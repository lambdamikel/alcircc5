#!/usr/bin/env python3
"""
WP15 -- Shadow-row joint realizability: a machine check of the round-12
Truth Lemma's critical step (split_forest_automata_with_appendices.tex,
Appendix E "Truth lemma" / Appendix M "Truth lemma: universal cases").

THE STEP UNDER TEST.  Round-12 builds the global relation rho_T by applying
patchwork + compactness to "the tree-shaped family of finite BAG networks"
(App E, Global realization) -- bag networks ONLY.  The truth lemma for
universals then asserts:

    "When y is introduced, the exact relation vector from x to the live
     ports includes rho_T(x,y) = R; validity therefore forces D into the
     type of y."

i.e. it assumes the DECLARED relation-vector shadow entries agree with the
patchwork completion rho_T.  Nothing in the paper's local legality tests
(App H "two-way shadow movement": boundary agreement on shared ports +
compatibility with the current bag network; App Q tests) constrains two
DIFFERENT shadows against each other, or a shadow entry declared while a
port was live against entries declared after that port is forgotten.  So
the implicit lemma is:

    (Shadow Amalgamation)  bag networks + all declared shadow rows are
    JOINTLY realizable by one abstract RCC5 frame.

This script shows that lemma is FALSE for the tests as written, and maps
out which strengthened disciplines restore it.

Model of the round-12 checks ("V0", the charitable literal reading):
  - a path of bags, each a complete atomic composition-closed network;
  - adjacent bags agree on continued ports (overlap tests O1-O5);
  - each shadow x has, at every bag in its scope, a row P_t -> Rel\\{EQ}
    (charitably excluding EQ entries, which Def 3.3 does not even do);
  - RIGIDITY: rows agree across adjacent bags on continued ports
    (App H: "the old and new vectors agree on shared ports");
  - ONE-POINT CLOSURE: the extended network on P_t + {x} is composition-
    closed (the strong reading of "compatible with the bag network");
  - NOTHING relates two shadows to each other, and a row entry to a port
    is dropped when that port is forgotten (rows are over CURRENT ports).

Parts:
  P1  Handcrafted minimal counterexample (3 bags, 3 occurrences): passes
      every V0 test; no abstract RCC5 frame realizes bags + all rows.
      Also a variant with a nonempty all-DR separator chain.
  P2  Exhaustive mini-search over the 3-bag pattern: counts how many
      V0-passing row assignments are jointly unrealizable.
  P3  SINGLE-shadow sweep: with only one shadow, V0-passing configurations
      are ALWAYS realizable (the extended family {bag + row} is itself a
      tree-shaped agreeing family of complete atomic networks, so the
      patchwork theorem applies to it).  Empirical confirmation.
  P4  Restricted-discipline sweep (the repair direction): all shadow
      entries in {DR, PO} (i.e. vertical PP/PPI/EQ relations must be
      co-bagged, exactly the saturation/residual-frontier discipline V7
      applied to the shadow layer): search for jointly unrealizable
      configurations.  Expected: none found.
  P5  Extended-bag discipline (alternative repair): shadows are treated as
      virtual ports -- every bag carries a complete network on ports +
      in-scope shadows INCLUDING shadow-shadow entries, with boundary
      agreement on continued shadows.  Then the family is again a
      tree-shaped agreeing family and patchwork applies; empirical
      confirmation that realizability always holds.

Interpretation.  P1/P2 demonstrate a configuration-level defect in the
Truth Lemma AS WRITTEN (its quoted sentence is false for every choice of
rho_T on these inputs).  They do NOT by themselves produce an
accepted-but-unsatisfiable CONCEPT; see the accompanying report.  P3-P5
support two concrete repair routes.

Run:  python3 verification/python/wp15_shadow_row_realizability.py
"""

import itertools
import random
import sys

BASE = ('EQ', 'PP', 'PPI', 'PO', 'DR')
NONEQ = ('PP', 'PPI', 'PO', 'DR')
CONV = {'EQ': 'EQ', 'PP': 'PPI', 'PPI': 'PP', 'PO': 'PO', 'DR': 'DR'}

COMP = {
    ('EQ', 'EQ'): {'EQ'}, ('EQ', 'PP'): {'PP'}, ('EQ', 'PPI'): {'PPI'},
    ('EQ', 'PO'): {'PO'}, ('EQ', 'DR'): {'DR'},
    ('PP', 'EQ'): {'PP'}, ('PP', 'PP'): {'PP'},
    ('PP', 'PPI'): set(BASE), ('PP', 'PO'): {'PP', 'PO', 'DR'},
    ('PP', 'DR'): {'DR'},
    ('PPI', 'EQ'): {'PPI'}, ('PPI', 'PP'): {'EQ', 'PP', 'PPI', 'PO'},
    ('PPI', 'PPI'): {'PPI'}, ('PPI', 'PO'): {'PPI', 'PO'},
    ('PPI', 'DR'): {'PPI', 'PO', 'DR'},
    ('PO', 'EQ'): {'PO'}, ('PO', 'PP'): {'PP', 'PO'},
    ('PO', 'PPI'): {'PPI', 'PO', 'DR'}, ('PO', 'PO'): set(BASE),
    ('PO', 'DR'): {'PPI', 'PO', 'DR'},
    ('DR', 'EQ'): {'DR'}, ('DR', 'PP'): {'PP', 'PO', 'DR'},
    ('DR', 'PPI'): {'DR'}, ('DR', 'PO'): {'PP', 'PO', 'DR'},
    ('DR', 'DR'): set(BASE),
}

COMP_F = {(r, s): frozenset(v) for (r, s), v in COMP.items()}


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


# ------------------------- fast completion: domains + path consistency ---

def _pc(dom, V):
    """Path-consistency refinement of pair domains; False if wiped out."""
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
                    for r in dom[(i, k)]:
                        for s in dom[(k, j)]:
                            allowed |= COMP_F[(r, s)]
                    new = dij & allowed
                    if new != dij:
                        dij = new
                        dom[(i, j)] = new
                        dom[(j, i)] = frozenset(CONV[r] for r in new)
                        changed = True
                    if not dij:
                        return False
        # keep converse coherence
    return True


def complete_network(V, known, rng=None):
    """Closed atomic completion of partial `known` on V, or None.
    Domains + path consistency + smallest-domain-first backtracking."""
    dom = {}
    for i in V:
        for j in V:
            if i == j:
                continue
            if (i, j) in known:
                dom[(i, j)] = frozenset([known[(i, j)]])
            else:
                dom[(i, j)] = frozenset(NONEQ)
    dom = dict(dom)
    if not _pc(dom, V):
        return None

    def rec(dom):
        undecided = [(p, d) for p, d in dom.items()
                     if len(d) > 1 and p[0] < p[1]]
        if not undecided:
            N = {p: next(iter(d)) for p, d in dom.items()}
            return N if is_closed(N, V) else None
        undecided.sort(key=lambda t: len(t[1]))
        pair, d = undecided[0]
        vals = list(d)
        if rng is not None:
            rng.shuffle(vals)
        for r in vals:
            nd = dict(dom)
            nd[pair] = frozenset([r])
            nd[(pair[1], pair[0])] = frozenset([CONV[r]])
            if _pc(nd, V):
                res = rec(nd)
                if res is not None:
                    return res
        return None

    return rec(dom)


# ------------------------------------------------------- configurations ---
# A configuration:
#   bags:    list of (ports, N) along a path t_0 - t_1 - ... (ports: tuple)
#   shadows: dict name -> {bag_index: row dict {port: rel}}
# Ports carried between adjacent bags are "continued" (same name).


def v0_legal(bags, shadows, entries_alphabet=NONEQ):
    """The round-12 local legality tests, charitable literal reading."""
    for ports, N in bags:
        for i in ports:
            for j in ports:
                if i != j and ((i, j) not in N or N[(i, j)] == 'EQ'):
                    return False, "bag not complete atomic"
        if not is_closed(N, list(ports)):
            return False, "bag not closed"
    for t in range(len(bags) - 1):
        p0, n0 = bags[t]
        p1, n1 = bags[t + 1]
        common = set(p0) & set(p1)
        for i in common:
            for j in common:
                if i != j and n0[(i, j)] != n1[(i, j)]:
                    return False, "overlap disagreement"
    for x, rows in shadows.items():
        scope = sorted(rows)
        if scope != list(range(scope[0], scope[-1] + 1)):
            return False, "non-contiguous scope"
        for t in scope:
            ports, N = bags[t]
            row = rows[t]
            if set(row) != set(ports):
                return False, "row does not cover current ports"
            for p, r in row.items():
                if r not in entries_alphabet:
                    return False, f"entry {r} outside alphabet"
            ext = dict(N)
            for p, r in row.items():
                net_set(ext, x, p, r)
            if not is_closed(ext, list(ports) + [x]):
                return False, "row not one-point closed with bag"
        for t in scope[:-1]:
            if t + 1 in rows:
                common = set(bags[t][0]) & set(bags[t + 1][0])
                for p in common:
                    if rows[t][p] != rows[t + 1][p]:
                        return False, "rigidity violated"
    return True, "ok"


def occurrences(bags, shadows):
    occ = []
    for ports, _ in bags:
        for p in ports:
            if p not in occ:
                occ.append(p)
    for x in shadows:
        if x not in occ:
            occ.append(x)
    return occ


def jointly_realizable(bags, shadows, extra=None):
    """One abstract RCC5 frame extending all bag networks and all declared
    shadow rows?  (Never-cobagged port pairs and shadow-shadow pairs are
    completed freely -- exactly the freedom patchwork has.)"""
    V = occurrences(bags, shadows)
    known = {}
    for ports, N in bags:
        for k, v in N.items():
            if k in known and known[k] != v:
                return False
            known[k] = v
    for x, rows in shadows.items():
        for t, row in rows.items():
            for p, r in row.items():
                if (x, p) in known and known[(x, p)] != r:
                    return False
                net_set(known, x, p, r)
    if extra:
        for (a, b), r in extra.items():
            net_set(known, a, b, r)
    return complete_network(V, known) is not None


# ---------------------------------------------------------------- parts ---

def p1_handcrafted():
    """Bags t0={x1}, t1={x2}, t2={p}; x1 forgotten after t0, x2 after t1.
    Declared rows:
        x1 @ t1: x2 -> DR     (a residual-frontier-respecting DR entry)
        x1 @ t2: p  -> PP
        x2 @ t2: p  -> PPI
    Composition forces lambda(x1,x2) in Comp(PP, PP) = {PP} via p
    (x1 PP p and p PP x2), contradicting the declared DR."""
    bags = [(('x1',), {}), (('x2',), {}), (('p',), {})]
    shadows = {
        'x1': {1: {'x2': 'DR'}, 2: {'p': 'PP'}},
        'x2': {2: {'p': 'PPI'}},
    }
    legal, why = v0_legal(bags, shadows)
    real = jointly_realizable(bags, shadows)
    print("P1a minimal counterexample (empty separators):")
    print(f"    passes all V0 legality tests: {legal} ({why})")
    print(f"    jointly realizable:           {real}")
    ok_a = legal and not real

    N0, N1, N2 = {}, {}, {}
    net_set(N0, 's', 'x1', 'DR')
    net_set(N1, 's', 'x2', 'DR')
    net_set(N2, 's', 'p', 'DR')
    bags = [(('s', 'x1'), N0), (('s', 'x2'), N1), (('s', 'p'), N2)]
    shadows = {
        'x1': {1: {'s': 'DR', 'x2': 'DR'}, 2: {'s': 'DR', 'p': 'PP'}},
        'x2': {2: {'s': 'DR', 'p': 'PPI'}},
    }
    legal, why = v0_legal(bags, shadows)
    real = jointly_realizable(bags, shadows)
    print("P1b same defect with a continued all-DR separator port s:")
    print(f"    passes all V0 legality tests: {legal} ({why})")
    print(f"    jointly realizable:           {real}")
    ok_b = legal and not real
    print(f"P1 {'PASS (defect demonstrated)' if ok_a and ok_b else 'FAIL'}")
    return ok_a and ok_b


def p2_exhaustive_mini():
    """All row assignments on the 3-bag single-port pattern of P1a."""
    n_legal = 0
    n_bad = 0
    examples = []
    for v1 in NONEQ:          # x1 @ t1 : x2
        for v2 in NONEQ:      # x1 @ t2 : p
            for v3 in NONEQ:  # x2 @ t2 : p
                bags = [(('x1',), {}), (('x2',), {}), (('p',), {})]
                shadows = {'x1': {1: {'x2': v1}, 2: {'p': v2}},
                           'x2': {2: {'p': v3}}}
                legal, _ = v0_legal(bags, shadows)
                if not legal:
                    continue
                n_legal += 1
                if not jointly_realizable(bags, shadows):
                    n_bad += 1
                    examples.append((v1, v2, v3))
    print(f"P2 exhaustive 3-bag pattern: {n_legal} V0-legal row assignments,"
          f" {n_bad} jointly UNREALIZABLE")
    for v1, v2, v3 in examples[:6]:
        print(f"    e.g. x1-x2:{v1}  x1-p:{v2}  x2-p:{v3}")
    if len(examples) > 6:
        print(f"    ... and {len(examples) - 6} more")
    ok = n_bad > 0
    print(f"P2 {'PASS (defect is generic, not a knife-edge)' if ok else 'FAIL'}")
    return ok


def rand_config(rng, n_shadows, entry_alphabet):
    """Random V0-legal path configuration built constructively."""
    n_bags = rng.randint(2, 3)
    fresh = itertools.count()
    ports0 = tuple(f'p{next(fresh)}' for _ in range(rng.randint(1, 2)))
    N0 = complete_network(list(ports0), {}, rng=rng)
    bags = [(ports0, N0)]
    for _ in range(n_bags - 1):
        pv, pn = bags[-1]
        smax = min(2, len(pv))
        ssize = rng.randint(0, smax)
        sep = tuple(rng.sample(list(pv), ssize))
        sepn = {(i, j): pn[(i, j)] for i in sep for j in sep if i != j}
        new = tuple(f'p{next(fresh)}' for _ in range(rng.randint(1, 2)))
        Nn = complete_network(list(sep + new), dict(sepn), rng=rng)
        bags.append((sep + new, Nn))

    shadows = {}
    for s in range(n_shadows):
        x = f'x{s}'
        start = rng.randint(0, len(bags) - 1)
        rows = {}
        prev_row = None
        okso = True
        for t in range(start, len(bags)):
            ports, N = bags[t]
            row = {}
            if prev_row is not None:
                for p in set(ports) & set(bags[t - 1][0]):
                    row[p] = prev_row[p]
            todo = [p for p in ports if p not in row]
            found = False
            for _ in range(80):
                trial = dict(row)
                for p in todo:
                    trial[p] = rng.choice(entry_alphabet)
                ext = dict(N)
                for p, r in trial.items():
                    net_set(ext, x, p, r)
                if is_closed(ext, list(ports) + [x]):
                    row = trial
                    found = True
                    break
            if not found:
                okso = False
                break
            rows[t] = row
            prev_row = row
        if okso and rows:
            shadows[x] = rows
    return bags, shadows


def p3_single_shadow(trials=250, seed=23):
    rng = random.Random(seed)
    bad = 0
    n = 0
    attempts = 0
    while n < trials and attempts < trials * 40:
        attempts += 1
        bags, shadows = rand_config(rng, 1, NONEQ)
        legal, _ = v0_legal(bags, shadows)
        if not legal or not shadows:
            continue
        n += 1
        if not jointly_realizable(bags, shadows):
            bad += 1
            print(f"    UNEXPECTED single-shadow failure: {bags} {shadows}")
    print(f"P3 single shadow, unrestricted entries, {n} random V0-legal "
          f"configs: {bad} unrealizable " +
          ("(PASS -- single-shadow extended family always patches)"
           if bad == 0 else "(FAIL)"))
    return bad == 0


def p4_restricted(trials=350, seed=29):
    """Repair discipline: shadow entries restricted to {DR, PO} (verticals
    must be co-bagged: the saturation/residual-frontier rule (V7) applied
    to the shadow layer)."""
    rng = random.Random(seed)
    bad = 0
    n = 0
    attempts = 0
    while n < trials and attempts < trials * 40:
        attempts += 1
        bags, shadows = rand_config(rng, rng.randint(2, 3), ('DR', 'PO'))
        legal, _ = v0_legal(bags, shadows, entries_alphabet=('DR', 'PO'))
        if not legal or len(shadows) < 2:
            continue
        n += 1
        if not jointly_realizable(bags, shadows):
            bad += 1
            print(f"    counterexample under DR/PO discipline: "
                  f"{bags} {shadows}")
    n_bad_mini = 0
    for v1 in ('DR', 'PO'):
        for v2 in ('DR', 'PO'):
            for v3 in ('DR', 'PO'):
                bags = [(('x1',), {}), (('x2',), {}), (('p',), {})]
                shadows = {'x1': {1: {'x2': v1}, 2: {'p': v2}},
                           'x2': {2: {'p': v3}}}
                if v0_legal(bags, shadows, ('DR', 'PO'))[0] and \
                   not jointly_realizable(bags, shadows):
                    n_bad_mini += 1
    print(f"P4 multi-shadow, entries restricted to DR/PO: {n} random configs"
          f" + 8 exhaustive mini-patterns: {bad + n_bad_mini} unrealizable " +
          ("(PASS -- no counterexample under the repair discipline)"
           if bad + n_bad_mini == 0 else "(FAIL)"))
    return bad + n_bad_mini == 0


def p5_extended_bags(trials=200, seed=31):
    """Alternative repair: shadows as virtual ports.  Each bag's network is
    extended by all in-scope shadows INCLUDING shadow-shadow entries; the
    extended bags must be closed and agree across boundaries.  Then the
    extended family is a tree-shaped agreeing family of complete atomic
    networks, so patchwork applies and realizability must always hold."""
    rng = random.Random(seed)
    bad = 0
    n = 0
    attempts = 0
    while n < trials and attempts < trials * 60:
        attempts += 1
        bags, shadows = rand_config(rng, 2, NONEQ)
        if len(shadows) < 2:
            continue
        names = sorted(shadows)
        pair_vals = {}
        ok = True
        for a, b in itertools.combinations(names, 2):
            common = sorted(set(shadows[a]) & set(shadows[b]))
            if not common:
                continue
            found = None
            for r in NONEQ:
                good = True
                for t in common:
                    ports, N = bags[t]
                    ext = dict(N)
                    for p, v in shadows[a][t].items():
                        net_set(ext, a, p, v)
                    for p, v in shadows[b][t].items():
                        net_set(ext, b, p, v)
                    net_set(ext, a, b, r)
                    if not is_closed(ext, list(ports) + [a, b]):
                        good = False
                        break
                if good:
                    found = r
                    break
            if found is None:
                ok = False
                break
            pair_vals[(a, b)] = found
        if not ok:
            continue  # the extended-bag discipline REJECTS this input
        n += 1
        if not jointly_realizable(bags, shadows, extra=pair_vals):
            bad += 1
            print(f"    extended-bag discipline failure: {bags} {shadows} "
                  f"{pair_vals}")
    print(f"P5 extended-bag discipline (shadow-shadow entries checked "
          f"per-bag): {n} accepted configs, {bad} unrealizable " +
          ("(PASS -- discipline restores patchwork)" if bad == 0
           else "(FAIL)"))
    return bad == 0


if __name__ == '__main__':
    print(__doc__.split('\n')[1])
    print('=' * 74)
    r = [p1_handcrafted(), p2_exhaustive_mini(), p3_single_shadow(),
         p4_restricted(), p5_extended_bags()]
    print('=' * 74)
    print("WP15 OVERALL:", "PASS (defect demonstrated; repair disciplines "
          "corroborated)" if all(r) else "ATTENTION: see failures above")
    sys.exit(0 if all(r) else 1)
