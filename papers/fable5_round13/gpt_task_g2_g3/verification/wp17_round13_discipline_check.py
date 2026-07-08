#!/usr/bin/env python3
"""
WP17 -- Machine checks for the round-13 repair ("Shadow Amalgamation via
the horizontal-shadow discipline"), papers/fable5_round13/.

Round-13 repairs the 7th review's critical finding F1 (the round-12 Truth
Lemma assumes, without proof, that declared relation-vector shadows agree
with the patchwork completion rho_T) by tightening the abstraction
language -- the D-discipline:

  (D1) shadow vector entries range over {DR, PO} only (no EQ, no PP/PPI);
       vertically related pairs are co-bagged instead (saturation (S2)/(S3)
       /(S4), residual-frontier (V7) extended to the shadow layer);
  (D2) obligation-carrying shadows propagate omni-directionally; a crossing
       that would force a vertical rigid entry is replaced by (S3)
       verticalization (the pair becomes co-bagged);
  (D3) transitive vertical universals propagate through TYPES along
       vertical edges (forall PP.D at p and N(p,q)=PP pushes {D, forall
       PP.D} into tau(q); dually for PPI) -- so vertical obligations never
       need long-range shadows;
  (D4) vertical-request sources stay live along their support branch.

and then proves the SHADOW AMALGAMATION LEMMA: bag networks + all declared
(horizontal) rows + [fixed values for previously co-bagged pairs, DR for
all remaining shadow-shadow pairs] are jointly realizable, by finite
patchwork + compactness on the shadow-extended family.

This script verifies:

  A  The FINITE COMPOSITION FACTS the lemma's closure argument cites,
     exhaustively over the (independently re-derived) composition table:
       A1  {DR,PO} subseteq Comp(a,b) for all a,b in {DR,PO}
           (horizontal values never constrain each other: every triangle
           with two horizontal sides admits every horizontal third side --
           this single fact closes the (shadow,shadow,port),
           (shadow,shadow,shadow) and rotation triangles under D1);
       A2  Comp(PP,PP)={PP} and Comp(PPI,PPI)={PPI}
           (soundness of the D3 type-propagation rule);
       A3  Comp(h,r) cap {DR,PO} != emptyset for all h in {DR,PO},
           r in {PP,PPI} (a shadow entering a vertical region from a
           horizontal anchor is never forced vertical-only: either a
           horizontal entry exists, or the true relation is vertical and
           (D2) verticalizes -- no dead ends);
       A4  the EQ-cell fact from WP14 (every nontrivial cell containing EQ
           also contains PP, PPI, PO), reused by strong equality.

  B  CONSTRUCTIVE LEMMA CHECK on random TREE-shaped configurations (the
     7th review's WP15 used paths; the round-13 proof's running-
     intersection/median argument is about trees): random trees of closed
     bags; 2-4 shadow sources that are real occurrences (live in a root
     bag, then forgotten) whose scopes spread over the whole remaining
     tree; rows sampled under D1 (entries in {DR,PO}, one-point closure,
     rigidity); then the lemma's ASSIGNMENT is built explicitly --
     previously co-bagged pairs keep their bag value, all remaining
     shadow-shadow pairs get DR -- and the script asserts:
       B1  every shadow-extended bag is a complete atomic composition-
           closed network (the finite-facts step of the proof);
       B2  the whole extended constraint set is jointly realizable
           (independent global CSP check = what patchwork + compactness
           guarantee).
     Expected: 100% of configurations pass both.

  C  NEGATIVE CONTROL: the same generator with a single vertical entry
     admitted (D1 violated) must produce configurations where B fails
     (this is the WP15 defect reappearing), confirming the harness can
     see the failure the discipline excludes.

Run:  python3 verification/python/wp17_round13_discipline_check.py
"""

import itertools
import random
import sys

BASE = ('EQ', 'PP', 'PPI', 'PO', 'DR')
NONEQ = ('PP', 'PPI', 'PO', 'DR')
HOR = ('DR', 'PO')
VERT = ('PP', 'PPI')
CONV = {'EQ': 'EQ', 'PP': 'PPI', 'PPI': 'PP', 'PO': 'PO', 'DR': 'DR'}


def derive_comp(n=5):
    universe = range(n)
    subsets = []
    for k in range(1, n + 1):
        subsets += [frozenset(c) for c in itertools.combinations(universe, k)]

    def rel(a, b):
        if a == b:
            return 'EQ'
        if not (a & b):
            return 'DR'
        if a < b:
            return 'PP'
        if b < a:
            return 'PPI'
        return 'PO'

    t = {(r, s): set() for r in BASE for s in BASE}
    for a in subsets:
        for b in subsets:
            r = rel(a, b)
            for c in subsets:
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


def _pc(dom, V):
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
                            allowed |= COMP[(r, s)]
                    new = dij & allowed
                    if new != dij:
                        dom[(i, j)] = frozenset(new)
                        dom[(j, i)] = frozenset(CONV[r] for r in new)
                        dij = dom[(i, j)]
                        changed = True
                    if not dij:
                        return False
    return True


def complete_network(V, known, rng=None):
    dom = {}
    for i in V:
        for j in V:
            if i == j:
                continue
            dom[(i, j)] = (frozenset([known[(i, j)]]) if (i, j) in known
                           else frozenset(NONEQ))
    if not _pc(dom, V):
        return None

    def rec(dom):
        und = [(p, d) for p, d in dom.items() if len(d) > 1 and p[0] < p[1]]
        if not und:
            N = {p: next(iter(d)) for p, d in dom.items()}
            return N if is_closed(N, V) else None
        und.sort(key=lambda t: len(t[1]))
        pair, d = und[0]
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


# ------------------------------------------------------------ Part A -----

def part_a():
    ok = True
    # A1: horizontal absorption
    a1 = all(set(HOR) <= COMP[(a, b)] for a in HOR for b in HOR)
    print(f"A1 {{DR,PO}} subseteq Comp(a,b) for all a,b in {{DR,PO}}: "
          f"{'PASS' if a1 else 'FAIL'}")
    # A2: vertical transitivity (D3 soundness)
    a2 = COMP[('PP', 'PP')] == {'PP'} and COMP[('PPI', 'PPI')] == {'PPI'}
    print(f"A2 Comp(PP,PP)={{PP}}, Comp(PPI,PPI)={{PPI}}: "
          f"{'PASS' if a2 else 'FAIL'}")
    # A3: no dead ends entering vertical regions
    a3 = all(COMP[(h, r)] & set(HOR) for h in HOR for r in VERT)
    print(f"A3 Comp(h,r) cap {{DR,PO}} nonempty for h in {{DR,PO}}, "
          f"r in {{PP,PPI}}: {'PASS' if a3 else 'FAIL'}")
    # A4: EQ never forced (strong equality, reused from WP14)
    a4 = all({'PP', 'PPI', 'PO'} <= cell
             for (r, s), cell in COMP.items()
             if 'EQ' in cell and (r, s) != ('EQ', 'EQ'))
    print(f"A4 every nontrivial cell containing EQ contains PP,PPI,PO: "
          f"{'PASS' if a4 else 'FAIL'}")
    ok = a1 and a2 and a3 and a4
    print(f"Part A (finite facts): {'PASS' if ok else 'FAIL'}")
    return ok


# ------------------------------------------------------------ Part B -----
# Configurations on TREES of bags.  Shadows are real occurrences: each is
# live in exactly one bag (its root), then forgotten; its scope is every
# other bag, reached along tree edges (omni-directional propagation).

def rand_tree_config(rng, n_shadows, entry_alphabet):
    """Shadows are real occurrences: each is live in its own distinct home
    bag (there it relates to the home ports like a port, any relation),
    and casts a row over every other bag (omni-directional propagation).
    Rows cover the bag ports AND any shadow whose home is that bag (a live
    manifestation is a port); the entry to it is the unique pair value
    (D5 pair coherence), sampled once and reused from either side."""
    n_bags = rng.randint(3, 5)
    if n_shadows > n_bags:
        n_shadows = n_bags
    fresh = itertools.count()
    ports0 = tuple(f'p{next(fresh)}' for _ in range(rng.randint(1, 2)))
    N0 = complete_network(list(ports0), {}, rng=rng)
    bags = [(ports0, N0)]
    parent = {0: None}
    for b in range(1, n_bags):
        par = rng.randrange(len(bags))
        pv, pn = bags[par]
        smax = min(2, len(pv))
        ssize = rng.randint(0, smax)
        sep = tuple(rng.sample(list(pv), ssize))
        sepn = {(i, j): pn[(i, j)] for i in sep for j in sep if i != j}
        new = tuple(f'p{next(fresh)}' for _ in range(rng.randint(1, 2)))
        Nn = complete_network(list(sep + new), dict(sepn), rng=rng)
        bags.append((sep + new, Nn))
        parent[b] = par

    def neighbors(t):
        out = []
        if parent[t] is not None:
            out.append(parent[t])
        out += [c for c in parent if parent[c] == t]
        return out

    names = [f'x{s}' for s in range(n_shadows)]
    homes = dict(zip(names, rng.sample(range(n_bags), n_shadows)))
    home_of_bag = {t: x for x, t in homes.items()}

    # live rows: each shadow extends its own home bag (any relations)
    live_row = {}
    for x in names:
        hv, hn = bags[homes[x]]
        ext = complete_network(list(hv) + [x], dict(hn), rng=rng)
        if ext is None:
            return None
        live_row[x] = {p: ext[(x, p)] for p in hv}

    pairval = {}   # unique declared value per shadow pair (D5)
    shadows = {}
    for x in names:
        home = homes[x]
        rows = {home: ('LIVE', dict(live_row[x]))}
        order = [home]
        seen = {home}
        okso = True
        while order and okso:
            t = order.pop(0)
            for u in neighbors(t):
                if u in seen:
                    continue
                seen.add(u)
                pu, Nu = bags[u]
                # effective bag at u: ports + a live manifestation there
                eff_ports = list(pu)
                eff_net = dict(Nu)
                resident = home_of_bag.get(u)
                if resident is not None and resident != x:
                    eff_ports.append(resident)
                    for p, r in live_row[resident].items():
                        net_set(eff_net, resident, p, r)
                row = {}
                prev = rows[t][1]
                for p in set(pu) & set(bags[t][0]):
                    if p in prev:
                        row[p] = prev[p]
                if resident is not None and resident != x:
                    key = tuple(sorted((x, resident)))
                    if key in pairval:
                        v = pairval[key] if key[0] == x else CONV[pairval[key]]
                        row[resident] = v
                if any(v not in entry_alphabet for v in row.values()):
                    okso = False
                    break
                todo = [p for p in eff_ports if p not in row]
                found = False
                for _ in range(120):
                    trial = dict(row)
                    for p in todo:
                        trial[p] = rng.choice(entry_alphabet)
                    extn = dict(eff_net)
                    for p, r in trial.items():
                        net_set(extn, x, p, r)
                    if is_closed(extn, eff_ports + [x]):
                        row = trial
                        found = True
                        break
                if not found:
                    okso = False
                    break
                if resident is not None and resident != x:
                    key = tuple(sorted((x, resident)))
                    if key not in pairval:
                        pairval[key] = (row[resident] if key[0] == x
                                        else CONV[row[resident]])
                rows[u] = ('SH', row)
                order.append(u)
        if not okso:
            return None
        shadows[x] = (home, rows)
    return bags, shadows, parent, pairval, live_row, home_of_bag


def lemma_assignment(bags, shadows, pairval):
    """The round-13 constructive assignment: bag values; live rows; shadow
    rows (including declared entries to live manifestations = the unique
    pair values, D5); DR for shadow pairs never co-located."""
    known = {}
    for ports, N in bags:
        known.update(N)
    for x, (home, rows) in shadows.items():
        for t, (kind, row) in rows.items():
            for p, r in row.items():
                net_set(known, x, p, r)
    names = sorted(shadows)
    for a, b in itertools.combinations(names, 2):
        key = (a, b)
        if key in pairval and (a, b) not in known:
            net_set(known, a, b, pairval[key])
        if (a, b) not in known:
            net_set(known, a, b, 'DR')
    return known


def occurrences(bags, shadows):
    occ = []
    for ports, _ in bags:
        for p in ports:
            if p not in occ:
                occ.append(p)
    occ += sorted(shadows)
    return occ


def extended_bags_closed(bags, shadows, known):
    """B1: every bag extended by all in-scope shadows + the assignment is
    a closed complete atomic network."""
    names = sorted(shadows)
    for t, (ports, N) in enumerate(bags):
        Vt = list(ports) + names
        Nt = {}
        for i in Vt:
            for j in Vt:
                if i != j:
                    Nt[(i, j)] = known[(i, j)]
        if not is_closed(Nt, Vt):
            return False
    return True


def part_b(trials=400, seed=41):
    rng = random.Random(seed)
    n = 0
    bad_closed = 0
    bad_real = 0
    attempts = 0
    while n < trials and attempts < trials * 50:
        attempts += 1
        cfg = rand_tree_config(rng, rng.randint(2, 4), HOR)
        if cfg is None:
            continue
        bags, shadows, parent, pairval, live_row, home_of = cfg
        n += 1
        known = lemma_assignment(bags, shadows, pairval)
        if not extended_bags_closed(bags, shadows, known):
            bad_closed += 1
            continue
        V = occurrences(bags, shadows)
        if complete_network(V, known) is None:
            bad_real += 1
    print(f"Part B: {n} random tree configurations under the D-discipline")
    print(f"   B1 extended bags closed under the lemma assignment: "
          f"{n - bad_closed}/{n} "
          f"({'PASS' if bad_closed == 0 else 'FAIL'})")
    print(f"   B2 jointly realizable (global CSP): {n - bad_real}/{n} "
          f"({'PASS' if bad_real == 0 else 'FAIL'})")
    return bad_closed == 0 and bad_real == 0


def part_c(trials=300, seed=43):
    """Negative control: admit vertical entries (violating D1) and check
    that unrealizable configurations exist and are detected."""
    rng = random.Random(seed)
    n = 0
    bad = 0
    attempts = 0
    while n < trials and attempts < trials * 50:
        attempts += 1
        cfg = rand_tree_config(rng, rng.randint(2, 3), NONEQ)
        if cfg is None:
            continue
        bags, shadows, parent, pairval, live_row, home_of = cfg
        n += 1
        known = lemma_assignment(bags, shadows, pairval)
        # under vertical entries the DR-default may already clash in a bag
        if not extended_bags_closed(bags, shadows, known):
            bad += 1
            continue
        V = occurrences(bags, shadows)
        if complete_network(V, known) is None:
            bad += 1
    print(f"Part C (negative control, vertical entries admitted): "
          f"{bad}/{n} configurations fail the lemma assignment "
          f"({'PASS -- the harness sees the WP15 defect the discipline '
             'excludes' if bad > 0 else 'FAIL -- control did not trigger'})")
    return bad > 0


if __name__ == '__main__':
    print(__doc__.split('\n')[1])
    print('=' * 74)
    r = [part_a(), part_b(), part_c()]
    print('=' * 74)
    print("WP17 OVERALL:", "PASS" if all(r) else "ATTENTION: see above")
    sys.exit(0 if all(r) else 1)
