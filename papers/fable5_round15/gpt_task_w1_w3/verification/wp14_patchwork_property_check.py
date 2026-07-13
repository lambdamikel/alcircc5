#!/usr/bin/env python3
"""
WP14 -- Direct verification of the RCC5 patchwork theorem as stated in
round-12 (split_forest_automata_with_appendices.tex, Theorem 2.5 and
Appendix A), for the abstract composition-table semantics, at small widths.

Round-12's entire global-coherence layer rests on this single external
theorem (its "two external finite facts", Section 2.4):

    (two-bag patchwork)  Let N1, N2 be finite complete atomic RCC5 networks
    over V1, V2, each satisfiable as an abstract RCC5 network, agreeing on
    V1 cap V2.  Then their union has a satisfiable completion on V1 cup V2.

    (finite tree patching, App A)  ... hence every finite tree-shaped family
    of complete atomic bag networks agreeing on overlaps has a satisfiable
    completion, by leaf-by-leaf induction.

For the ABSTRACT semantics of the paper (Def 2.1: a frame is any (Delta,rho)
satisfying identity/converse/composition), a finite complete atomic network
is satisfiable iff it is composition-closed -- the network IS a frame.  So
both statements are purely combinatorial properties of the RCC5 composition
table and can be verified exhaustively at small widths.

Tests:
  T0  Re-derive the composition table from set semantics (5-element
      universe) and assert it equals the paper's table (independent of WP1).
  T1  Two-bag patchwork, exhaustive: one fresh variable on each side,
      shared part S with |S| in {0,1,2,3}: for ALL pairs of closed atomic
      networks agreeing on S, a closed atomic completion of the union
      exists.
  T2  Two-bag patchwork, exhaustive at |fresh|=2 per side, |S| in {1,2}
      (sampled for the largest class to keep runtime bounded).
  T3  Finite tree patching: random trees of 3..6 closed atomic bags
      (width <= 5, separators <= 3, running intersection by construction),
      amalgamated leaf-by-leaf exactly as in Appendix A's induction;
      assert success and closure of the final network.
  T4  EQ-forcing analysis: verify that every composition-table cell
      containing EQ also contains PP, PPI and PO, so a cross-pair value is
      never forced to be exactly EQ (supports Appendix G: strong equality
      is preservable -- completions never need EQ between distinct
      occurrences).  All completions in T1-T3 are searched over non-EQ
      values only, so their success is itself the constructive check.

A FAILURE in T1-T3 would be a counterexample to round-12's Theorem 2.5 and
would invalidate the proof (its own Appendix U, failure point F1).

Result expected: all PASS (the property is standard for RCC5; this makes
the repo's reliance on it directly machine-checked in the exact form the
round-12 manuscript uses it, complementing WP6's mosaic closure search).

Run:  python3 verification/python/wp14_patchwork_property_check.py
"""

import itertools
import random
import sys

# ---------------------------------------------------------------- table ---

BASE = ('EQ', 'PP', 'PPI', 'PO', 'DR')
NONEQ = ('PP', 'PPI', 'PO', 'DR')
CONV = {'EQ': 'EQ', 'PP': 'PPI', 'PPI': 'PP', 'PO': 'PO', 'DR': 'DR'}

# The table as printed in split_forest_automata_with_appendices.tex, Sec 2.1
PAPER_COMP = {
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


def derive_comp_from_sets(n=5):
    """RCC5 composition table from nonempty subsets of an n-element set."""
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

    table = {(r, s): set() for r in BASE for s in BASE}
    for a in subsets:
        for b in subsets:
            r = rel(a, b)
            for c in subsets:
                table[(r, rel(b, c))].add(rel(a, c))
    return table


COMP = PAPER_COMP  # used everywhere below; T0 asserts it equals set-derived

# ------------------------------------------------------------- networks ---
# A network is a dict {(i, j): rel} storing BOTH directions for i != j,
# over a variable tuple V.  Atomic complete: every pair labelled, EQ iff
# equal.  Closed: composition table respected on every ordered triple.


def net_set(N, i, j, r):
    N[(i, j)] = r
    N[(j, i)] = CONV[r]


def is_closed(N, V):
    for i in V:
        for j in V:
            if i == j:
                continue
            for k in V:
                if k == i or k == j:
                    continue
                if N[(i, k)] not in COMP[(N[(i, j)], N[(j, k)])]:
                    return False
    return True


def enumerate_closed(V):
    """All closed atomic complete networks on tuple V (small |V| only)."""
    pairs = [(V[i], V[j]) for i in range(len(V)) for j in range(i + 1, len(V))]
    out = []

    def rec(idx, N):
        if idx == len(pairs):
            out.append(dict(N))
            return
        i, j = pairs[idx]
        for r in NONEQ:
            net_set(N, i, j, r)
            ok = True
            # check all triangles fully labelled so far that involve (i,j)
            for k in V:
                if k in (i, j):
                    continue
                if (i, k) in N and (j, k) in N:
                    if N[(i, k)] not in COMP[(N[(i, j)], N[(j, k)])] or \
                       N[(j, k)] not in COMP[(N[(j, i)], N[(i, k)])] or \
                       N[(i, j)] not in COMP[(N[(i, k)], N[(k, j)])]:
                        ok = False
                        break
            if ok:
                rec(idx + 1, N)
            del N[(i, j)], N[(j, i)]

    rec(0, {})
    return out


def complete_network(V, known, rng=None):
    """Backtracking search for a closed atomic completion of the partial
    network `known` (dict with both directions) on variable list V.
    Returns a completed dict or None.  Only non-EQ values are tried for
    distinct pairs (strong equality)."""
    unknown = [(V[i], V[j]) for i in range(len(V))
               for j in range(i + 1, len(V)) if (V[i], V[j]) not in known]
    N = dict(known)

    def consistent(i, j):
        for k in V:
            if k in (i, j):
                continue
            ik, kj = (i, k) in N, (k, j) in N
            if ik and kj and N[(i, j)] not in COMP[(N[(i, k)], N[(k, j)])]:
                return False
            if ik and (j, k) in N and \
               N[(i, k)] not in COMP[(N[(i, j)], N[(j, k)])]:
                return False
            if (k, i) in N and kj is False and (k, j) in N:
                pass
            if (k, i) in N and (k, j) in N and \
               N[(k, j)] not in COMP[(N[(k, i)], N[(i, j)])]:
                return False
        return True

    def rec(idx):
        if idx == len(unknown):
            return is_closed(N, V)
        i, j = unknown[idx]
        vals = list(NONEQ)
        if rng is not None:
            rng.shuffle(vals)
        for r in vals:
            net_set(N, i, j, r)
            if consistent(i, j) and rec(idx + 1):
                return True
            del N[(i, j)], N[(j, i)]
        return False

    if rec(0):
        return N
    return None


# ---------------------------------------------------------------- tests ---

def t0_table():
    derived = derive_comp_from_sets(5)
    bad = [(r, s) for (r, s) in PAPER_COMP if derived[(r, s)] != PAPER_COMP[(r, s)]]
    print(f"T0 composition table vs set semantics (5-cell universe): "
          f"{'PASS' if not bad else 'FAIL ' + str(bad)}")
    return not bad


def t1_two_bag_exhaustive():
    """One fresh variable per side, |S| in {0,1,2,3}, fully exhaustive."""
    ok = True
    total = 0
    for s_size in (0, 1, 2, 3):
        S = tuple(f's{i}' for i in range(s_size))
        V1 = S + ('a',)
        V2 = S + ('b',)
        nets1 = enumerate_closed(V1)
        # group by restriction to S for matching
        def key(N):
            return tuple(sorted((p, r) for p, r in N.items()
                                if p[0] in S and p[1] in S))
        nets2 = enumerate_closed(V2)
        by_key2 = {}
        for N in nets2:
            by_key2.setdefault(key(N), []).append(N)
        cnt = 0
        for N1 in nets1:
            for N2 in by_key2.get(key(N1), []):
                union = dict(N1)
                union.update(N2)
                V = S + ('a', 'b')
                if complete_network(list(V), union) is None:
                    print(f"    COUNTEREXAMPLE at |S|={s_size}: N1={N1} N2={N2}")
                    ok = False
                cnt += 1
        total += cnt
        print(f"    |S|={s_size}: {len(nets1)} x matching nets, "
              f"{cnt} agreeing pairs checked")
    print(f"T1 two-bag patchwork, 1+1 fresh, exhaustive ({total} pairs): "
          f"{'PASS' if ok else 'FAIL'}")
    return ok


def t2_two_bag_fresh2(sample_cap=40000, seed=7):
    """Two fresh variables per side, |S| in {1,2}; exhaustive where cheap,
    sampled otherwise."""
    rng = random.Random(seed)
    ok = True
    for s_size in (1, 2):
        S = tuple(f's{i}' for i in range(s_size))
        V1 = S + ('a1', 'a2')
        V2 = S + ('b1', 'b2')
        nets1 = enumerate_closed(V1)
        nets2 = enumerate_closed(V2)

        def key(N):
            return tuple(sorted((p, r) for p, r in N.items()
                                if p[0] in S and p[1] in S))
        by_key2 = {}
        for N in nets2:
            by_key2.setdefault(key(N), []).append(N)
        pairs = []
        for N1 in nets1:
            for N2 in by_key2.get(key(N1), []):
                pairs.append((N1, N2))
        if len(pairs) > sample_cap:
            pairs = rng.sample(pairs, sample_cap)
        fails = 0
        for N1, N2 in pairs:
            union = dict(N1)
            union.update(N2)
            V = list(S) + ['a1', 'a2', 'b1', 'b2']
            if complete_network(V, union) is None:
                fails += 1
                if fails <= 3:
                    print(f"    COUNTEREXAMPLE |S|={s_size}: N1={N1} N2={N2}")
        print(f"    |S|={s_size}: {len(pairs)} agreeing pairs checked, "
              f"{fails} failures")
        ok = ok and fails == 0
    print(f"T2 two-bag patchwork, 2+2 fresh: {'PASS' if ok else 'FAIL'}")
    return ok


def random_closed_extension(sep_vars, sep_net, fresh, rng):
    """A closed atomic bag on sep_vars+fresh extending sep_net, sampled by
    randomized backtracking (independent of any global model)."""
    V = list(sep_vars) + list(fresh)
    return complete_network(V, dict(sep_net), rng=rng)


def t3_tree_patching(trials=300, seed=11):
    rng = random.Random(seed)
    ok = True
    for t in range(trials):
        n_bags = rng.randint(3, 6)
        # bag 0
        fresh_id = itertools.count()
        v0 = [f'v{next(fresh_id)}' for _ in range(rng.randint(2, 4))]
        b0 = complete_network(v0, {}, rng=rng)
        bags = [(v0, b0)]
        parent = {0: None}
        for b in range(1, n_bags):
            par = rng.randrange(len(bags))
            pv, pn = bags[par]
            sep_size = rng.randint(1, min(3, len(pv)))
            sep = rng.sample(pv, sep_size)
            sep_net = {(i, j): pn[(i, j)] for i in sep for j in sep if i != j}
            fresh = [f'v{next(fresh_id)}' for _ in range(rng.randint(1, 3))]
            bn = random_closed_extension(sep, sep_net, fresh, rng)
            assert bn is not None
            bags.append((sep + fresh, bn))
            parent[b] = par
        # leaf-by-leaf amalgamation, exactly App A's induction
        alive = list(range(n_bags))
        acc_vars, acc_net = list(bags[0][0]), dict(bags[0][1])
        # fold in BFS order (any order with parent before child = leaf fold
        # of the reversed order)
        for b in range(1, n_bags):
            bv, bn = bags[b]
            union = dict(acc_net)
            union.update(bn)
            allv = list(dict.fromkeys(acc_vars + bv))
            merged = complete_network(allv, union, rng=rng)
            if merged is None:
                print(f"    COUNTEREXAMPLE trial {t}: fold of bag {b} failed")
                ok = False
                break
            acc_vars, acc_net = allv, merged
        if ok and not is_closed(acc_net, acc_vars):
            print(f"    trial {t}: final network not closed")
            ok = False
        if not ok:
            break
    print(f"T3 tree patching, {trials} random trees (3-6 bags, width<=7): "
          f"{'PASS' if ok else 'FAIL'}")
    return ok


def t4_eq_forcing():
    bad = []
    for (r, s), cell in COMP.items():
        if 'EQ' in cell and (r, s) != ('EQ', 'EQ'):
            if not {'PP', 'PPI', 'PO'} <= cell:
                bad.append((r, s))
    print("T4 every non-trivial comp cell containing EQ also contains "
          f"PP,PPI,PO: {'PASS' if not bad else 'FAIL ' + str(bad)}")
    print("    (hence a cross-pair is never composition-forced to be exactly"
          " EQ; with T1-T3 searching non-EQ values only, strong equality is"
          " preservable, as Appendix G claims)")
    return not bad


if __name__ == '__main__':
    print(__doc__.split('\n')[1])
    print('=' * 74)
    results = [t0_table(), t1_two_bag_exhaustive(), t2_two_bag_fresh2(),
               t3_tree_patching(), t4_eq_forcing()]
    print('=' * 74)
    print("WP14 OVERALL:", "PASS" if all(results) else "FAIL")
    sys.exit(0 if all(results) else 1)
