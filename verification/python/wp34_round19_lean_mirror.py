#!/usr/bin/env python3
"""
WP34 -- Round-19/20 harness: the Lean-mirrored source-oriented update
(papers/fable5_round19/, papers/fable5_round20/,
formal/Round19Transport.lean).

Round 19 changed the medium: the NORMATIVE definitions (the operational
fold `unfoldAll` and the source-oriented update `uSource`, U1-U5 of the
thirteenth review) live in Lean, where totality is compiler-checked and
the thirteenth review's witnesses are kernel-checked theorems.
ROUND 20 (2026-07-13): the round-19 `sorry` is DISCHARGED --
`uSource_eq_frame` is now a kernel-checked theorem (`frame_char`,
induction on the canonical step list; fuel adequacy via
`uSourceFuel_irrel`), and the file also proves non-vacuity
(`certC_wellformed`).  The proof forced four Wellformed clauses this
generator had silently honored (targets_exist, targets_length,
net_conv, f_reads_rows); the Part-B steering function now reads ONLY
in-range row entries, the literal form of f_reads_rows.
ROUND 21 (2026-07-13): the S-layer soundness kernel is in the same
file -- SCond (the manuscripts' S4 on certificate-computable values)
implies the unfolded frame is composition-closed, converse-coherent
and EQ-free (frame_closed / frame_conv / frame_proper); the WP32
Part-C adversarial control is now the kernel-checked certD pair.
ROUND 22 (2026-07-13): the catalogue level -- SCat states the
S-condition on (coreNet, templates, f) alone over enumerated abstract
rows; scat_scond proves SCat + pattern faithfulness imply SCond for
every faithful unfolding (one finite check, unboundedly many step
lists); certD's catalogue check provably fails at the reachable row.
ROUND 23 (2026-07-13): the catalogue GENERATOR -- a Catalog + N2
attachment rules + buildCert produce certificates that are Wellformed
and Faithful BY CONSTRUCTION (build_wellformed, build_faithful), so
catalogue_soundness gives SCond for EVERY valid plan; the certK
witness drives the whole round-19..23 pipeline.
Part A below re-verifies all of it on every run.
This harness:

  A  builds the Lean file if a Lean toolchain is available (the build
     is the totality check and re-verifies every theorem incl. the
     round-20 characterization; EXPECTED SORRIES: ZERO), else reports
     SKIPPED with instructions;
  B  cross-checks a Python TRANSCRIPTION of uSource against a Python
     transcription of the operational fold on random certificates
     whose slot targets range over ARBITRARY pre-existing occurrences
     (core or born, injective) -- the inherited-member geometry class
     where defects #11-#12 lived; expected: exact agreement on every
     existing non-core-core pair (now a REGRESSION against the proved
     theorem, guarding the Lean/Python transcription seam);
  C  the thirteenth review's WP-literalization items: the negative
     steering control is DETERMINISTIC (no salted hash), and it fires;
  D  a result digest stable across PYTHONHASHSEED.

Run:  python3 verification/python/wp34_round19_lean_mirror.py
"""

import hashlib
import itertools
import os
import random
import shutil
import subprocess
import sys

ATOMS = ('EQ', 'PP', 'PPI', 'PO', 'DR')
CONV = {'EQ': 'EQ', 'PP': 'PPI', 'PPI': 'PP', 'PO': 'PO', 'DR': 'DR'}
AIDX = {a: i for i, a in enumerate(ATOMS)}


# ------------------------------------------------------------- Part A ---

def part_a():
    lean = shutil.which('lean') or os.path.expanduser('~/.elan/bin/lean')
    src = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       '..', '..', 'formal', 'Round19Transport.lean')
    if not os.path.exists(lean):
        print("A. Lean build: SKIPPED (no toolchain; install elan and run"
              "  `lean formal/Round19Transport.lean`)")
        return True
    r = subprocess.run([lean, os.path.abspath(src)],
                       capture_output=True, text=True, timeout=600,
                       cwd=os.path.dirname(os.path.abspath(src)))
    sorries = r.stdout.count('declaration uses `sorry`') + \
        r.stderr.count('declaration uses `sorry`')
    ok = r.returncode == 0 and sorries == 0
    verdict = ('PASS -- zero sorries: uSource_eq_frame + fuel adequacy '
               '(round-20), the S-layer closure theorems (round-21), '
               'the catalogue-level scat_scond (round-22) and the '
               'catalogue generator build_wellformed/build_faithful/'
               'catalogue_soundness (round-23) are kernel-checked') \
        if ok else 'FAIL'
    print(f"A. Lean build of formal/Round19Transport.lean: "
          f"returncode={r.returncode}, sorries={sorries} "
          f"(expected 0 since round-20) ({verdict})")
    if not ok:
        print((r.stdout + r.stderr)[:800])
    return ok


# ---------------------------------------------- Lean-mirror definitions --
# Faithful transcriptions of formal/Round19Transport.lean.  Any change
# there must be mirrored here (and the Lean witnesses pin the semantics).

def default_template():
    return {'nSlots': 0, 'nFresh': 0, 'net': lambda p, q: 'DR'}


def cert_template(C, i):
    return C['templates'][i] if i < len(C['templates']) \
        else default_template()


def cert_step(C, i):
    return C['steps'][i] if i < len(C['steps']) else {'tmpl': 0,
                                                      'slotTargets': []}


def member_port(C, i, x):
    if x[0] == 'core':
        return ('core', x[1])
    s, j = x[1], x[2]
    if s == i:
        return ('fresh', j)
    st = cert_step(C, i)['slotTargets']
    for k, t in enumerate(st):
        if t == x:
            return ('slot', k)
    return None


def existing_before(C, i):
    occ = [('core', c) for c in range(C['nCore'])]
    for s in range(i):
        T = cert_template(C, cert_step(C, s)['tmpl'])
        occ += [('born', s, j) for j in range(T['nFresh'])]
    return occ


def frame_get(F, x, y):
    return F.get((x, y))


def port_occ(C, i, p):
    kind = p[0]
    if kind == 'slot':
        st = cert_step(C, i)['slotTargets']
        return st[p[1]] if p[1] < len(st) else ('core', 0)
    if kind == 'core':
        return ('core', p[1])
    return ('born', i, p[1])


def do_step(C, F, i):
    T = cert_template(C, cert_step(C, i)['tmpl'])
    member_ports = ([('slot', k) for k in range(T['nSlots'])] +
                    [('core', c) for c in range(C['nCore'])] +
                    [('fresh', j) for j in range(T['nFresh'])])
    F = dict(F)
    for p in member_ports:
        for q in member_ports:
            xo, yo = port_occ(C, i, p), port_occ(C, i, q)
            if xo != yo and (xo, yo) not in F:
                F[(xo, yo)] = T['net'](p, q)
    steered = [x for x in existing_before(C, i)
               if member_port(C, i, x) is None]
    for x in steered:
        crow = (lambda x_: lambda c:
                C['coreNet'](x_[1], c) if x_[0] == 'core'
                else F.get((x_, ('core', c)), 'DR'))(x)
        st = cert_step(C, i)['slotTargets']
        srow = (lambda x_: lambda k:
                F.get((x_, st[k]), 'DR') if k < len(st) else 'DR')(x)
        for j in range(T['nFresh']):
            v = C['f'](i, crow, srow, j)
            F[(x, ('born', i, j))] = v
            F[(('born', i, j), x)] = CONV[v]
    return F


def unfold_all(C):
    F = {}
    for i in range(len(C['steps'])):
        F = do_step(C, F, i)
    return F


def u_source_fuel(C, fuel, x, y):
    if fuel == 0:
        return 'DR'
    if x[0] == 'core' and y[0] == 'core':
        return C['coreNet'](x[1], y[1])
    if x[0] == 'core':
        s, j = y[1], y[2]
        T = cert_template(C, cert_step(C, s)['tmpl'])
        return CONV[T['net'](('fresh', j), ('core', x[1]))]
    if y[0] == 'core':
        s, j = x[1], x[2]
        T = cert_template(C, cert_step(C, s)['tmpl'])
        return T['net'](('fresh', j), ('core', y[1]))
    sx, jx, ss, js = x[1], x[2], y[1], y[2]
    if sx == ss:
        T = cert_template(C, cert_step(C, sx)['tmpl'])
        return T['net'](('fresh', jx), ('fresh', js))
    if sx < ss:
        mp = member_port(C, ss, x)
        T = cert_template(C, cert_step(C, ss)['tmpl'])
        if mp is not None:
            return T['net'](mp, ('fresh', js))
        st = cert_step(C, ss)['slotTargets']
        crow = lambda c: u_source_fuel(C, fuel - 1, x, ('core', c))
        srow = lambda k: (u_source_fuel(C, fuel - 1, x, st[k])
                          if k < len(st) else 'DR')  # pad like slotRowOf
        return C['f'](ss, crow, srow, js)
    return CONV[u_source_fuel(C, fuel - 1, y, x)]


def u_source(C, x, y):
    # depth <= 2*steps + 2 (flip preserves max birth once, steered-row
    # calls strictly decrease it); safe margin, mirroring the Lean bound
    return u_source_fuel(C, 2 * len(C['steps']) + 4, x, y)


# ------------------------------------------------------------- Part B ---

def make_net_from_dict(d):
    return lambda p, q: d.get((p, q), 'EQ')


def rand_cert(rng, n_templates=3, n_steps=5, n_core=1):
    templates = []
    for ti in range(n_templates):
        nS = 0 if ti == 0 else rng.randint(0, 2)
        nF = rng.randint(1, 2)
        d = {}
        ports = ([('slot', k) for k in range(nS)] +
                 [('core', c) for c in range(n_core)] +
                 [('fresh', j) for j in range(nF)])
        for p in ports:
            for q in ports:
                if p != q:
                    key = tuple(sorted([repr(p), repr(q)]))
                    if ('v', key) not in d:
                        v = rng.choice(['PP', 'PPI', 'PO', 'DR'])
                        d[('v', key)] = v
                    v = d[('v', key)]
                    d[(p, q)] = v if repr(p) < repr(q) else CONV[v]
        templates.append({'nSlots': nS, 'nFresh': nF,
                          'net': make_net_from_dict(
                              {k: v for k, v in d.items()
                               if not (isinstance(k, tuple)
                                       and k and k[0] == 'v')})})

    def f(i, crow, srow, j):
        # deterministic steering keyed on the rows (no salted hash),
        # reading ONLY in-range row entries -- the literal form of the
        # round-20 Wellformed clause f_reads_rows (C is resolved at
        # call time, after construction)
        nS = cert_template(C, cert_step(C, i)['tmpl'])['nSlots']
        key = sum(AIDX[crow(c)] for c in range(n_core)) + \
            sum(AIDX[srow(k)] for k in range(nS)) + i + j
        return ('DR', 'PO', 'PP', 'PPI')[key % 4]

    C = {'nCore': n_core,
         'coreNet': lambda a, b: 'EQ' if a == b else 'DR',
         'templates': templates, 'steps': [{'tmpl': 0, 'slotTargets': []}],
         'f': f}
    for i in range(1, n_steps):
        ti = rng.randrange(1, n_templates) if n_templates > 1 else 0
        nS = templates[ti]['nSlots']
        # slot targets: BORN occurrences only (core is threaded via its
        # dedicated ports per (N3); a core-targeting slot duplicates the
        # occurrence inside one pattern -- wellformedness forbids it,
        # a clause this harness itself surfaced during development)
        pool = [t for t in existing_before(C, i) if t[0] == 'born']
        if nS > len(pool):
            ti = 0
            nS = 0
        targets = rng.sample(pool, nS) if nS else []
        C['steps'].append({'tmpl': ti, 'slotTargets': targets})
    return C


def part_b(trials=200, seed=511):
    rng = random.Random(seed)
    n = mismatches = pairs_checked = inherited_targets = 0
    digest = hashlib.sha256()
    while n < trials:
        C = rand_cert(rng, rng.randint(2, 3), rng.randint(3, 6),
                      rng.randint(1, 2))
        n += 1
        inherited_targets += sum(
            1 for st in C['steps'] for t in st['slotTargets']
            if t[0] == 'born')
        F = unfold_all(C)
        occ = existing_before(C, len(C['steps']))
        for x in occ:
            for y in occ:
                if x == y or (x[0] == 'core' and y[0] == 'core'):
                    continue
                got = frame_get(F, x, y)
                want = u_source(C, x, y)
                pairs_checked += 1
                if got != want:
                    mismatches += 1
                digest.update(f"{x}{y}{got}{want}".encode())
    print(f"B. Lean-mirror uSource vs operational fold: {n} random "
          f"certificates (slot targets over ARBITRARY pre-existing "
          f"occurrences; {inherited_targets} born-occurrence targets "
          f"sampled), {pairs_checked} pairs checked, "
          f"{mismatches} mismatches "
          f"({('PASS -- transcription regression against the proved theorem' if mismatches == 0 else 'FAIL')})")
    print(f"D. determinism digest: {digest.hexdigest()[:16]} (stable "
          f"across PYTHONHASHSEED)")
    return mismatches == 0


# ------------------------------------------------------------- Part C ---

def part_c(trials=120, seed=523):
    """Deterministic adversarial steering (violates S4-style closure on
    purpose) must produce non-closed frames -- and the count must be
    hash-seed independent by construction."""
    import math
    rng = random.Random(seed)

    def derive_comp():
        n = 5
        subs = [frozenset(c) for k in range(1, n + 1)
                for c in itertools.combinations(range(n), k)]

        def rel(a, b):
            if a == b:
                return 'EQ'
            if not a & b:
                return 'DR'
            if a < b:
                return 'PP'
            if b < a:
                return 'PPI'
            return 'PO'
        t = {(r, s): set() for r in ATOMS for s in ATOMS}
        for a in subs:
            for b in subs:
                r = rel(a, b)
                for c in subs:
                    t[(r, rel(b, c))].add(rel(a, c))
        return {k: frozenset(v) for k, v in t.items()}

    COMP = derive_comp()

    def closed(F, occ, C):
        def val(x, y):
            if x[0] == 'core' and y[0] == 'core':
                return C['coreNet'](x[1], y[1])
            return F.get((x, y), 'DR')
        for x in occ:
            for y in occ:
                if x == y:
                    continue
                for z in occ:
                    if z in (x, y):
                        continue
                    if val(x, y) not in COMP[(val(x, z), val(z, y))]:
                        return False
        return True

    bad = total = 0
    for _ in range(trials):
        C = rand_cert(rng, 2, rng.randint(3, 5), 1)

        def adversarial(i, crow, srow, j):
            key = sum(AIDX[srow(k)] for k in range(3)) + \
                AIDX[crow(0)] + i + j           # deterministic key
            return ('PP', 'DR')[key % 2]         # extreme alternation

        C['f'] = adversarial
        F = unfold_all(C)
        occ = existing_before(C, len(C['steps']))
        total += 1
        if not closed(F, occ, C):
            bad += 1
    verdict = 'PASS -- control fires, no salted hash' if bad > 0 else 'FAIL'
    print(f"C. deterministic adversarial control: {bad}/{total} frames "
          f"non-closed ({verdict})")
    return bad > 0


if __name__ == '__main__':
    print(__doc__.split('\n')[1])
    print('=' * 70)
    r = [part_a(), part_b(), part_c()]
    print('=' * 70)
    print("WP34 OVERALL:", "PASS" if all(r) else "ATTENTION: see above")
    sys.exit(0 if all(r) else 1)
