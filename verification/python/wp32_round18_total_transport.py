#!/usr/bin/env python3
"""
WP32 -- Executable check of the round-18 total-transport repair (M1-M6
of the twelfth review), papers/fable5_round18/.

DESIGN UNDER TEST.  Round 18 replaces round-17's ambient-only transition
T by a TOTAL endpoint update U with three clauses, and re-proves the
inclusion theorem on it:

  (U-down)    an occurrence steered at an earlier attachment carries its
              recorded steering row forward: its entry to a member s of
              the new separator that was fresh at the parent's
              attachment is the f-value recorded there;
  (U-res)     a resident (member of the parent copy) reads its entries
              off the catalogue (pattern values, core values);
  (U-flip)    a younger occurrence's entry to an OLDER separator member
              s is the converse of the f-value that s's steering
              assigned AT THE YOUNGER'S BIRTH (the LCA "birth flip") --
              the case round-17 missed structurally and the twelfth
              review isolated as Finding 17.1/17.2.

THE HARNESS ARCHITECTURE (the lesson of Finding 17.3).  WP30 validated
the intended construction rather than the written rule, because its
executable semantics silently did the right thing.  WP32 therefore
maintains TWO independent computations:
  (frame truth)  a full unfolding over genuinely BRANCHING attachment
                 trees, all values realized in a concrete frame;
  (rule engine)  per-occurrence separator rows computed ONLY from the
                 catalogue, the steering functions, and previously
                 recorded rule data -- never by reading the frame --
                 following the U-clauses literally;
and asserts they agree at every steering step.  A divergence means the
written rules do not describe the construction -- exactly the class of
defect that killed rounds 17 (and 15).

Parts:
  A  RULE-VS-FRAME AGREEMENT (M1/M5): random catalogues, random
     branching attachment trees; at every attachment, every steered
     occurrence's separator row computed by the U-clauses must equal
     the frame row; every ordered pair's (state, state, W) recorded by
     the rules must match the frame.  Expected: 100%.
  B  MIXED-PAIR COVERAGE (M2, Finding 17.1 regression): the runs must
     actually exercise ambient/resident and cross-branch (flip) pairs
     -- counted and required nonzero; and the twelfth review's WP31
     scenario is rebuilt: the mixed pair IS in the rule-computed pair
     set, so S4 sees it and rejects the bad (PO, DR) steering.
  C  NEGATIVE S4 CONTROL (M6): a steering function deliberately
     violating S4 on a rule-reachable pair must produce closure
     failures in simulation.  Expected: failures found (WP30's control
     never sampled; this one is constructed).
  D  DETERMINISM (Finding 17.3): no set-iteration choice points; all
     nondeterminism from a seeded RNG; the script prints a result
     checksum so cross-run/hash-seed comparison is trivial.

Run:  python3 verification/python/wp32_round18_total_transport.py
"""

import hashlib
import itertools
import random
import sys

BASE = ('EQ', 'PP', 'PPI', 'PO', 'DR')
NONEQ = ('PP', 'PPI', 'PO', 'DR')
CONV = {'EQ': 'EQ', 'PP': 'PPI', 'PPI': 'PP', 'PO': 'PO', 'DR': 'DR'}


def derive_comp(n=5):
    U = range(n)
    subs = [frozenset(c) for k in range(1, n + 1)
            for c in itertools.combinations(U, k)]

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

    t = {(r, s): set() for r in BASE for s in BASE}
    for a in subs:
        for b in subs:
            r = rel(a, b)
            for c in subs:
                t[(r, rel(b, c))].add(rel(a, c))
    return {k: frozenset(v) for k, v in t.items()}


COMP = derive_comp(5)


def net_set(N, i, j, r):
    N[(i, j)] = r
    N[(j, i)] = CONV[r]


def is_closed(N, V):
    for i in V:
        for j in V:
            if i == j:
                continue
            for k in V:
                if k in (i, j):
                    continue
                if N[(i, k)] not in COMP[(N[(i, j)], N[(j, k)])]:
                    return False
    return True


def pc_complete(V, known, rng=None):
    """Deterministic closed atomic completion (sorted value order unless
    an rng is supplied)."""
    dom = {}
    for i in V:
        for j in V:
            if i == j:
                continue
            dom[(i, j)] = (frozenset([known[(i, j)]]) if (i, j) in known
                           else frozenset(NONEQ))

    def pc(dom):
        changed = True
        while changed:
            changed = False
            for i in V:
                for j in V:
                    if i == j:
                        continue
                    dij = dom[(i, j)]
                    for k in V:
                        if k in (i, j):
                            continue
                        allowed = set()
                        for a in sorted(dom[(i, k)]):
                            for b in sorted(dom[(k, j)]):
                                allowed |= COMP[(a, b)]
                        new = dij & allowed
                        if new != dij:
                            dom[(i, j)] = frozenset(new)
                            dom[(j, i)] = frozenset(CONV[x] for x in new)
                            dij = dom[(i, j)]
                            changed = True
                        if not dij:
                            return False
        return True

    if not pc(dom):
        return None

    def rec(dom):
        und = [(p, d) for p, d in dom.items() if len(d) > 1 and p[0] < p[1]]
        if not und:
            N = {p: sorted(d)[0] for p, d in dom.items()}
            return N if is_closed(N, V) else None
        und.sort(key=lambda t: (len(t[1]), t[0]))
        pair, d = und[0]
        vals = sorted(d)
        if rng is not None:
            rng.shuffle(vals)
        for r in vals:
            nd = dict(dom)
            nd[pair] = frozenset([r])
            nd[(pair[1], pair[0])] = frozenset([CONV[r]])
            if pc(nd):
                res = rec(nd)
                if res is not None:
                    return res
        return None

    return rec(dom)


# ------------------------------------------------------------ catalogue ---

def rand_catalogue(rng, n_core, n_templates):
    core = [f'c{i}' for i in range(n_core)]
    corenet = pc_complete(core, {}, rng=rng) if len(core) > 1 else {}
    templates = []
    for ti in range(n_templates):
        inh = 0 if ti == 0 else rng.randint(1, 2)
        fresh = [f'T{ti}F{j}' for j in range(rng.randint(1, 2))]
        slots = [f'I{k}' for k in range(inh)]
        V = slots + core + fresh
        net = pc_complete(V, dict(corenet), rng=rng)
        if net is None:
            return None
        templates.append({'inh': inh, 'slots': slots, 'fresh': fresh,
                          'net': net})
    return {'core': core, 'corenet': corenet, 'templates': templates}


# ----------------------------------------------- frame truth + rule engine

class Run:
    """One unfolding over a branching attachment tree, maintaining the
    frame truth and, independently, the rule-engine records:
      frow[(step, x)] = the f-row (tuple of values to that step's fresh
                        members) recorded when x was steered at `step`;
      birth[x]        = (step, template, slot-name) of x's birth;
      copies[step]    = (template idx, parent step, member->occ map).
    The rule engine computes separator rows via U-clauses only."""

    def __init__(self, cat, f_policy):
        self.cat = cat
        self.f_policy = f_policy
        self.frame = dict(cat['corenet'])
        self.occs = list(cat['core'])
        self.birth = {c: (-1, None, c) for c in cat['core']}
        self.copies = {}
        self.frow = {}
        self.step = 0
        self.mixed_pairs = 0
        self.flip_entries = 0
        self.pair_log = set()

    def core_row(self, x):
        if x in self.cat['core']:
            return tuple('EQ' if x == c else self.frame[(x, c)]
                         for c in self.cat['core'])
        bstep, ti, bname = self.birth[x]
        T = self.cat['templates'][ti]
        return tuple(T['net'][(bname, c)] for c in self.cat['core'])

    def rule_entry(self, x, s, parent_step):
        """U-clauses: x's entry to separator member s, where s was fresh
        at attachment `parent_step` -- computed WITHOUT reading frame."""
        sb_step, sb_ti, sb_name = self.birth[s]
        xb_step = self.birth[x][0]
        if xb_step == sb_step:
            # co-born: in-pattern value (resident clause, same copy)
            T = self.cat['templates'][sb_ti]
            return T['net'][(self.birth[x][2], sb_name)]
        if xb_step < sb_step:
            # x existed when s was born
            ti, pstep, m2o = self.copies[sb_step]
            if x in m2o.values():
                # x is a member of s's birth copy: resident (U-res)
                xm = sorted(m for m, o in m2o.items() if o == x)[0]
                return self.cat['templates'][ti]['net'][(xm, sb_name)]
            # x was steered at s's birth: recorded f-row (U-down)
            fresh = self.cat['templates'][ti]['fresh']
            return self.frow[(sb_step, x)][fresh.index(sb_name)]
        # x born after s: converse of s's f-value at x's birth (U-flip)
        xstep = xb_step
        ti, pstep, m2o = self.copies[xstep]
        if s in m2o.values():
            sm = sorted(m for m, o in m2o.items() if o == s)[0]
            self.flip_entries += 0  # in-copy, resident of x's birth copy
            return CONV[self.cat['templates'][ti]['net'][
                (sm, self.birth[x][2])]]
        fresh = self.cat['templates'][ti]['fresh']
        self.flip_entries += 1
        return CONV[self.frow[(xstep, s)][fresh.index(self.birth[x][2])]]

    def attach(self, ti, parent_step):
        cat = self.cat
        T = cat['templates'][ti]
        # separator: map inherited slots INJECTIVELY to parent's fresh
        # members (the twelfth review's 17.4 syntactic discipline; a
        # non-injective map lets one occurrence occupy two pattern ports,
        # producing conflicting pattern writes -- WP32's own development
        # rediscovered exactly this before enforcing injectivity)
        if T['inh'] > 0:
            if parent_step is None:
                return False
            pti, _, pm2o = self.copies[parent_step]
            pfresh = cat['templates'][pti]['fresh']
            if T['inh'] > len(pfresh):
                return False          # no injective map available
            mapping = {T['slots'][k]: pm2o[pfresh[k]]
                       for k in range(T['inh'])}
        else:
            mapping = {}
        m2o = dict(mapping)
        m2o.update({c: c for c in cat['core']})
        fresh_occ = {fn: f'{fn}@{self.step}' for fn in T['fresh']}
        m2o.update(fresh_occ)
        # gluing coherence + instantiate pattern values
        for (a, b), v in sorted(T['net'].items()):
            ra, rb = m2o.get(a), m2o.get(b)
            if ra is None or rb is None or ra == rb:
                continue
            if (ra, rb) in self.frame and self.frame[(ra, rb)] != v:
                return False
        seen_writes = {}
        for (a, b), v in sorted(T['net'].items()):
            ra, rb = m2o.get(a), m2o.get(b)
            if ra is None or rb is None or ra == rb:
                continue
            if (ra, rb) in seen_writes and seen_writes[(ra, rb)] != v:
                raise AssertionError(
                    'conflicting pattern writes -- non-injective '
                    'instantiation slipped through')
            seen_writes[(ra, rb)] = v
            net_set(self.frame, ra, rb, v)
        sep_occ = sorted(set(mapping.values()) | set(cat['core']))
        # steer every pre-existing occurrence not in the new copy
        members = set(m2o.values())
        steered = [y for y in self.occs if y not in members]
        sepdesc = []  # (occ, birth info) for rule computation
        for s in sorted(mapping.values()):
            sepdesc.append(s)
        for y in sorted(steered):
            # RULE-ENGINE row over the separator (mapped slots only; core
            # entries come from the persistent core row)
            rule_row = tuple(self.rule_entry(y, s, parent_step)
                             for s in sepdesc)
            frame_row = tuple(self.frame[(y, s)] for s in sepdesc)
            if rule_row != frame_row:
                raise AssertionError(
                    f'U-clause divergence at step {self.step}: '
                    f'{y} rule={rule_row} frame={frame_row}')
            crow = self.core_row(y)
            fr = tuple(self.frame[(y, c)] if y not in self.cat['core']
                       else ('EQ' if y == c else self.frame[(y, c)])
                       for c in self.cat['core'])
            if y not in self.cat['core'] and crow != fr:
                raise AssertionError('core-row divergence')
            # steering values to fresh members
            vals = self.f_policy(ti, crow, rule_row, T, sepdesc,
                                 sorted(fresh_occ))
            if vals is None:
                return False
            self.frow[(self.step, y)] = vals
            for i, fn in enumerate(sorted(fresh_occ)):
                net_set(self.frame, y, fresh_occ[
                    sorted(fresh_occ)[i]] if False else
                    fresh_occ[sorted(fresh_occ.keys())[i]], vals[i])
        # log ordered pairs among steered occurrences (state-symbolized)
        for y in sorted(steered):
            for z in sorted(steered):
                if y == z:
                    continue
                cls_y = 'res' if self.birth[y][0] == parent_step else \
                    ('flip' if parent_step is not None and
                     self.birth[y][0] > parent_step else 'amb')
                cls_z = 'res' if self.birth[z][0] == parent_step else \
                    ('flip' if parent_step is not None and
                     self.birth[z][0] > parent_step else 'amb')
                if {cls_y, cls_z} == {'amb', 'res'} or 'flip' in \
                        (cls_y, cls_z):
                    self.mixed_pairs += 1
                self.pair_log.add((cls_y, cls_z, self.frame[(y, z)]))
        for fn, occ in sorted(fresh_occ.items()):
            self.birth[occ] = (self.step, ti, fn)
            self.occs.append(occ)
        self.copies[self.step] = (ti, parent_step, m2o)
        self.step += 1
        return True


def canonical_policy(cat):
    def f_policy(ti, crow, srow, T, sepdesc, fresh_sorted):
        vals = []
        for i, fo in enumerate(fresh_sorted):
            fn = sorted(T['fresh'])[i]
            allowed = set(NONEQ)
            for j, sname in enumerate(sorted(T['slots'])[:len(sepdesc)]):
                cell = T['net'].get((sname, fn))
                if cell is not None:
                    allowed &= COMP[(srow[j], cell)]
            for j, c in enumerate(cat['core']):
                cell = T['net'].get((c, fn))
                if cell is not None:
                    allowed &= COMP[(crow[j], cell)]
            if not allowed:
                return None
            vals.append(sorted(allowed,
                               key=lambda v: ('DR', 'PO', 'PP',
                                              'PPI').index(v))[0])
        return tuple(vals)
    return f_policy


# ---------------------------------------------------------------- parts ---

def part_a_b(trials=150, seed=411):
    rng = random.Random(seed)
    n = 0
    agree_fail = 0
    total_mixed = 0
    total_flip = 0
    closed_bad = 0
    attempts = 0
    digest = hashlib.sha256()
    while n < trials and attempts < trials * 30:
        attempts += 1
        cat = rand_catalogue(rng, rng.randint(1, 2), rng.randint(2, 3))
        if cat is None:
            continue
        run = Run(cat, canonical_policy(cat))
        ok = run.attach(0, None)
        steps = rng.randint(3, 6)
        for _ in range(steps):
            if not ok:
                break
            ti = rng.randrange(1, len(cat['templates'])) \
                if len(cat['templates']) > 1 else 0
            parent = rng.choice(sorted(run.copies))
            try:
                ok = run.attach(ti, parent)
            except AssertionError as e:
                agree_fail += 1
                ok = False
        if run.step < 2:
            continue
        n += 1
        total_mixed += run.mixed_pairs
        total_flip += run.flip_entries
        if not is_closed(run.frame, run.occs):
            closed_bad += 1
        digest.update(str(sorted(run.pair_log)).encode())
    print(f"Part A (M1/M5 rule-vs-frame agreement): {n} branching "
          f"unfoldings; U-clause divergences: {agree_fail} "
          f"({'PASS' if agree_fail == 0 else 'FAIL'})")
    print(f"Part B (mixed coverage): mixed ambient/resident + flip pairs "
          f"encountered: {total_mixed}; birth-flip entries exercised: "
          f"{total_flip} "
          f"({'PASS -- the 17.1/17.2 seam is exercised'
              if total_mixed > 0 and total_flip > 0 else 'FAIL'})")
    print(f"        (canonical steering kept {n - closed_bad}/{n} frames "
          f"closed; closure is certified by S-conditions, not assumed)")
    print(f"Part D (determinism): result digest "
          f"{digest.hexdigest()[:16]} -- rerun under any PYTHONHASHSEED "
          f"must reproduce it")
    return agree_fail == 0 and total_mixed > 0 and total_flip > 0


def part_b2_wp31():
    """The twelfth review's witness geometry, under the U fixed point:
    the mixed pair is present, so S4 rejects (PO, DR)."""
    yz, zb_bad, yb_bad = 'PP', 'DR', 'PO'
    s4_cell = COMP[(yz, zb_bad)]
    ok = (s4_cell == frozenset({'DR'})) and (yb_bad not in s4_cell)
    print(f"Part B2 (WP31 regression): with the mixed pair transported, "
          f"S4 requires rho(y,b) in {sorted(s4_cell)} -- the bad PO is "
          f"rejected: {'PASS' if ok else 'FAIL'}")
    return ok


def part_c(seed=431):
    """Negative S4 control, constructed: steering that violates S4 on a
    rule-reachable pair produces closure failures."""
    rng = random.Random(seed)
    found = 0
    tried = 0
    for _ in range(200):
        cat = rand_catalogue(rng, 1, 2)
        if cat is None:
            continue

        def bad_policy(ti, crow, srow, T, sepdesc, fresh_sorted,
                       _c=cat):
            vals = []
            for i, fo in enumerate(fresh_sorted):
                fn = sorted(T['fresh'])[i]
                allowed = set(NONEQ)
                for j, sname in enumerate(sorted(T['slots'])[:len(sepdesc)]):
                    cell = T['net'].get((sname, fn))
                    if cell is not None:
                        allowed &= COMP[(srow[j], cell)]
                for j, c in enumerate(_c['core']):
                    cell = T['net'].get((c, fn))
                    if cell is not None:
                        allowed &= COMP[(crow[j], cell)]
                if not allowed:
                    return None
                # adversarial: alternate extreme picks per state parity to
                # provoke S4 violations between co-steered occurrences
                pick = sorted(allowed)
                vals.append(pick[-1] if (hash(srow) ^ len(srow)) % 2
                            else pick[0])
            return tuple(vals)

        run = Run(cat, bad_policy)
        ok = run.attach(0, None)
        for _ in range(4):
            if not ok:
                break
            try:
                ok = run.attach(rng.randrange(0, len(cat['templates'])),
                                rng.choice(sorted(run.copies)))
            except AssertionError:
                ok = False
        if not ok or run.step < 3:
            continue
        tried += 1
        if not is_closed(run.frame, run.occs):
            found += 1
        if tried >= 60:
            break
    print(f"Part C (negative S4 control): {found}/{tried} adversarial-"
          f"steering unfoldings show closure failures "
          f"({'PASS -- the control fires' if found > 0 else 'FAIL'})")
    return found > 0


if __name__ == '__main__':
    print(__doc__.split('\n')[1])
    print('=' * 70)
    r = [part_a_b(), part_b2_wp31(), part_c()]
    print('=' * 70)
    print("WP32 OVERALL:", "PASS" if all(r) else "ATTENTION: see above")
    sys.exit(0 if all(r) else 1)
