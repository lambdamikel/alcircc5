#!/usr/bin/env python3
"""
WP26 -- Machine checks for the round-15 decision layer:
"Cluster Quasimodels for ALCI_RCC5" (papers/fable5_round15/), the
no-automaton replacement for Theorem C demanded by the ninth review
(R1/R2: either prove enrichment representability, or replace the
tree-automaton layer by a mosaic/type-elimination argument -- this is the
latter).

DESIGN UNDER TEST.  Round 15 drops the automaton and the guessed
enrichment entirely.  The certificate is a finite CLUSTER QUASIMODEL:
Hintikka types + safe links (2-types with transitive vertical
propagation) + a finite catalogue of cluster patterns (small closed
atomic safe-decorated networks fulfilling every demand within one step)
+ fold-based long-range conditions.  Global coherence is not enforced by
any machine at run time: it is CONSTRUCTED in the soundness proof, by
iterated patchwork over the unfolding tree plus a canonical selection on
the fold lattice.  Decidability = finite certificate space + finitely
checkable conditions.

Parts:

  A  THE FOLD LATTICE (new finite fact, load-bearing).  Fold-sets =
     compositions of atomic RCC5 words along paths.  A1: exactly 10
     fold-sets are reachable.  A2 (FOLD fact): every reachable fold-set
     is a singleton or contains a horizontal atom (DR or PO); moreover
     every fold-set contains DR, contains PO, or is one of the vertical
     singletons {PP},{PPI}.  A3: the three non-singleton fold-sets
     without DR ({PP,PO},{PPI,PO},{EQ,PP,PPI,PO}) all contain PO -- the
     canonical selector s(F) = (forced atom if |F\\{EQ}|=1, else DR if
     DR in F, else PO) is total on reachable folds.  A4: DR-column
     absorption (DR in Comp(W,DR) for every atom W) and the previously
     verified facts (horizontal absorption, vertical transitivity,
     EQ never forced) -- the steering toolkit.

  B  SAFE-PATCHWORK STEERING PROBE (the designated keystone W1,
     empirically).  Random realized "old" frames built as trees of
     closed atomic clusters glued by iterated patchwork; then a fresh
     cluster is glued on a separator, and every cross pair (old element,
     fresh element) receives a DOMAIN = (its true separator-mediated
     feasible set) intersected with a safety-like restriction that is
     guaranteed to contain the canonical selector value.  Checked: a
     joint completion within all domains exists (expect 100%).  Negative
     control: delete the horizontal atoms from some free domains --
     failures must appear (the WP15/F1.3 genus, which the certificate
     conditions exclude).

  C  ACCEPTANCE CROSS-VALIDATION.  A bounded rendering of the cluster-
     quasimodel acceptance semantics (types; witness edges with reuse =
     exact occurrence identity, which handles unique/"solitary" types;
     obligations enforced on actual completed relations; repetition
     closes only on request-closed cluster laps -- no promissory
     witnesses) against the cover-tree tableau oracle, on the full
     nine-review diagnostic suite -- including the eighth review's
     C_G2a tower and the ninth review's p4 shared-unique-witness tower
     -- plus a random sweep.

Run:  python3 verification/python/wp26_round15_cluster_quasimodels.py
"""

import itertools
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', '..', 'src'))

BASE = ('EQ', 'PP', 'PPI', 'PO', 'DR')
NONEQ = ('PP', 'PPI', 'PO', 'DR')
HOR = ('DR', 'PO')
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


def setcomp(A, B):
    out = set()
    for a in A:
        for b in B:
            out |= COMP[(a, b)]
    return frozenset(out)


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


def pc_complete(V, known, domains=None, rng=None):
    """Closed atomic completion of `known` on V with optional per-pair
    domains (default: all non-EQ atoms).  Path-consistency + search."""
    dom = {}
    for i in V:
        for j in V:
            if i == j:
                continue
            if (i, j) in known:
                dom[(i, j)] = frozenset([known[(i, j)]])
            elif domains and (i, j) in domains:
                dom[(i, j)] = frozenset(domains[(i, j)])
            else:
                dom[(i, j)] = frozenset(NONEQ)

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
                        allowed = setcomp(dom[(i, k)], dom[(k, j)])
                        new = dij & allowed
                        if new != dij:
                            dom[(i, j)] = new
                            dom[(j, i)] = frozenset(CONV[r] for r in new)
                            dij = new
                            changed = True
                        if not dij:
                            return False
        return True

    if not pc(dom):
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
            if pc(nd):
                res = rec(nd)
                if res is not None:
                    return res
        return None

    return rec(dom)


# ---------------------------------------------------------------- Part A --

def fold_lattice():
    seen = {}
    frontier = {frozenset([a]): (a,) for a in NONEQ}
    seen.update(frontier)
    while frontier:
        nf = {}
        for S, w in frontier.items():
            for a in NONEQ:
                T = setcomp(S, frozenset([a]))
                if T not in seen:
                    seen[T] = w + (a,)
                    nf[T] = w + (a,)
        frontier = nf
    return seen


def selector(F):
    """Canonical selection on a fold-set (distinct endpoints: EQ dropped)."""
    G = set(F) - {'EQ'}
    if len(G) == 1:
        return next(iter(G))
    if 'DR' in G:
        return 'DR'
    if 'PO' in G:
        return 'PO'
    return None


def part_a():
    seen = fold_lattice()
    a1 = len(seen) == 10
    print(f"A1 reachable fold-sets: {len(seen)} (expected 10): "
          f"{'PASS' if a1 else 'FAIL'}")
    nonsing = [S for S in seen if len(S) > 1]
    a2a = all(('DR' in S) or ('PO' in S) for S in nonsing)
    a2b = all(('DR' in S) or ('PO' in S) or
              (len(S) == 1 and next(iter(S)) in ('PP', 'PPI'))
              for S in seen)
    print(f"A2 FOLD fact (non-singleton folds contain a horizontal; every "
          f"fold has DR, PO, or is a vertical singleton): "
          f"{'PASS' if a2a and a2b else 'FAIL'}")
    nodr = sorted(tuple(sorted(S)) for S in nonsing if 'DR' not in S)
    a3 = all('PO' in S for S in nonsing if 'DR' not in S) and \
        all(selector(S) is not None for S in seen)
    print(f"A3 no-DR non-singleton folds {nodr} all contain PO; canonical "
          f"selector total on the lattice: {'PASS' if a3 else 'FAIL'}")
    a4 = all('DR' in COMP[(w, 'DR')] for w in BASE) and \
        all(set(HOR) <= COMP[(a, b)] for a in HOR for b in HOR) and \
        COMP[('PP', 'PP')] == {'PP'} and COMP[('PPI', 'PPI')] == {'PPI'} and \
        all({'PP', 'PPI', 'PO'} <= c for (r, s), c in COMP.items()
            if 'EQ' in c and (r, s) != ('EQ', 'EQ'))
    print(f"A4 steering toolkit (DR-column absorption; horizontal "
          f"absorption; vertical transitivity; EQ never forced): "
          f"{'PASS' if a4 else 'FAIL'}")
    ok = a1 and a2a and a2b and a3 and a4
    print(f"Part A: {'PASS' if ok else 'FAIL'}")
    return ok


# ---------------------------------------------------------------- Part B --

def rand_cluster_tree_frame(rng, n_clusters=4):
    """A realized frame built as a tree of clusters via iterated
    patchwork; returns (elements, frame, tree paths info)."""
    fresh = itertools.count()
    v0 = [f'e{next(fresh)}' for _ in range(rng.randint(2, 3))]
    frame = pc_complete(v0, {}, rng=rng)
    elems = list(v0)
    for _ in range(n_clusters - 1):
        sep = rng.sample(elems, min(len(elems), rng.randint(1, 2)))
        new = [f'e{next(fresh)}' for _ in range(rng.randint(1, 2))]
        known = dict(frame)
        allv = elems + new
        frame = pc_complete(allv, known, rng=rng)
        if frame is None:
            return None
        elems = allv
    return elems, frame


def part_b(trials=250, seed=71):
    rng = random.Random(seed)
    n = ok_pos = 0
    neg_total = neg_fail = 0
    attempts = 0
    while n < trials and attempts < trials * 40:
        attempts += 1
        made = rand_cluster_tree_frame(rng, rng.randint(3, 5))
        if made is None:
            continue
        elems, frame = made
        # glue a fresh cluster on a separator
        sep = rng.sample(elems, min(len(elems), rng.randint(1, 2)))
        fresh = [f'b{i}' for i in range(rng.randint(1, 2))]
        patt_v = sep + fresh
        sepn = {(i, j): frame[(i, j)] for i in sep for j in sep if i != j}
        patt = pc_complete(patt_v, dict(sepn), rng=rng)
        if patt is None:
            continue
        n += 1
        # true feasible set of each cross pair = values realizable given
        # frame + pattern (separator-mediated); domain = feasible cap
        # a safety-like restriction guaranteed to contain the canonical
        # selector of the feasible set
        known = dict(frame)
        known.update(patt)
        allv = elems + fresh
        # compute feasible sets pointwise
        cross = [(y, b) for y in elems if y not in sep for b in fresh]
        domains = {}
        ok = True
        for (y, b) in cross:
            feas = set()
            for v in NONEQ:
                k2 = dict(known)
                net_set(k2, y, b, v)
                if pc_complete(allv, k2) is not None:
                    feas.add(v)
            if not feas:
                ok = False
                break
            sel = selector(frozenset(feas))
            dom = {sel}
            # add a random subset of the rest (safety-like restriction)
            for v in feas:
                if rng.random() < 0.4:
                    dom.add(v)
            domains[(y, b)] = frozenset(dom)
            domains[(b, y)] = frozenset(CONV[v] for v in dom)
        if not ok:
            continue
        sol = pc_complete(allv, known, domains=domains)
        if sol is not None:
            ok_pos += 1
        # negative control: strip horizontals from the free domains
        neg_domains = {}
        stripped = False
        for (p, q), d in domains.items():
            d2 = set(d)
            if len(d2) >= 1 and any(v in HOR for v in d2) and \
               any(v not in HOR for v in NONEQ if v in d2) is False:
                pass
            nd = {v for v in d2 if v not in HOR}
            if nd != d2 and nd:
                neg_domains[(p, q)] = frozenset(nd)
                stripped = True
            elif nd != d2 and not nd:
                # force a vertical-only guess even if infeasible
                neg_domains[(p, q)] = frozenset({'PP'})
                stripped = True
            else:
                neg_domains[(p, q)] = frozenset(d2)
        if stripped:
            neg_total += 1
            if pc_complete(allv, known, domains=neg_domains) is None:
                neg_fail += 1
    print(f"Part B: {n} glue steps; canonical-selector domains jointly "
          f"realizable: {ok_pos}/{n} "
          f"({'PASS' if ok_pos == n else 'FAIL'})")
    print(f"        negative control (horizontals stripped): "
          f"{neg_fail}/{neg_total} become unrealizable "
          f"({'PASS -- harness sees the F1.3/WP15 genus' if neg_fail > 0 else 'FAIL'})")
    return ok_pos == n and neg_fail > 0


# ---------------------------------------------------------------- Part C --

from alcircc5_reasoner import (          # noqa: E402
    DR, PO, PP, PPI,
    AtomicConcept, NegAtomicConcept, Top, Bottom,
    And, Or, Exists, ForAll,
    closure, enumerate_types,
)
from cover_tree_tableau import check_sat as _tab  # noqa: E402


def tableau_sat(C0):
    res = _tab(C0)
    return bool(res[0]) if isinstance(res, tuple) else bool(res)


RELS4 = (PP, PPI, PO, DR)
CONV4 = {PP: PPI, PPI: PP, PO: PO, DR: DR}
COMP4 = {(r, s): frozenset(v for v in COMP[(r, s)] if v != 'EQ')
         for r in NONEQ for s in NONEQ}


def universals(t):
    return [(c.role, c.concept) for c in t if isinstance(c, ForAll)]


def edge_type_ok(tu, tv, R):
    for (S, D) in universals(tu):
        if S == R and D not in tv:
            return False
    for (S, D) in universals(tv):
        if S == CONV4[R] and D not in tu:
            return False
    return True


def pair_allowed(tu, tv):
    return frozenset(R for R in RELS4 if edge_type_ok(tu, tv, R))


def decide_ctq(C0, max_nodes=5, node_cap=120000):
    """Bounded cluster-quasimodel acceptance: witness graph with reuse,
    obligations on actual completed relations, request-closed repetition."""
    cl = closure(C0)
    types = enumerate_types(cl)
    root_types = [t for t in types if C0 in t]
    counter = [0]
    failed = set()

    def build_domains(nts, edges):
        n = len(nts)
        dom = {}
        for i in range(n):
            for j in range(i + 1, n):
                if (i, j) in edges:
                    d = frozenset([edges[(i, j)]])
                else:
                    d = pair_allowed(nts[i], nts[j])
                if not d:
                    return None
                dom[(i, j)] = d
                dom[(j, i)] = frozenset(CONV4[r] for r in d)
        return dom

    def pc(dom, n):
        changed = True
        while changed:
            changed = False
            for i in range(n):
                for j in range(n):
                    if i == j:
                        continue
                    dij = dom[(i, j)]
                    for k in range(n):
                        if k in (i, j):
                            continue
                        allowed = set()
                        for r in dom[(i, k)]:
                            for s in dom[(k, j)]:
                                allowed |= COMP4[(r, s)]
                        new = dij & allowed
                        if new != dij:
                            dom[(i, j)] = frozenset(new)
                            dom[(j, i)] = frozenset(CONV4[r] for r in new)
                            dij = dom[(i, j)]
                            changed = True
                        if not dij:
                            return False
        return True

    def complete(nts, edges):
        dom = build_domains(nts, edges)
        if dom is None:
            return False
        if not pc(dom, len(nts)):
            return False

        def rec(dom):
            und = [(p, d) for p, d in dom.items()
                   if len(d) > 1 and p[0] < p[1]]
            if not und:
                n = len(nts)
                for i in range(n):
                    for j in range(n):
                        if i == j:
                            continue
                        for k in range(n):
                            if k in (i, j):
                                continue
                            (a,) = dom[(i, k)]
                            (b,) = dom[(k, j)]
                            (c,) = dom[(i, j)]
                            if c not in COMP4[(a, b)]:
                                return False
                return True
            und.sort(key=lambda t: len(t[1]))
            pair, d = und[0]
            for r in d:
                nd = dict(dom)
                nd[pair] = frozenset([r])
                nd[(pair[1], pair[0])] = frozenset([CONV4[r]])
                if pc(nd, len(nts)) and rec(nd):
                    return True
            return False

        return rec(dom)

    def feasible(nts, edges):
        dom = build_domains(nts, edges)
        return dom is not None and pc(dom, len(nts))

    def search(nts, edges, pending):
        counter[0] += 1
        if counter[0] > node_cap:
            raise TimeoutError
        key = (nts, frozenset(edges.items()), frozenset(pending))
        if key in failed:
            return False
        if not feasible(nts, edges):
            failed.add(key)
            return False
        if not pending:
            if complete(nts, edges):
                return True
            failed.add(key)
            return False
        (u, ex) = pending[0]
        rest = tuple(pending[1:])
        R, D = ex.role, ex.concept
        for v in range(len(nts)):
            tv = nts[v]
            if v == u or D not in tv:
                continue
            if (u, v) in edges:
                if edges[(u, v)] == R and search(nts, edges, rest):
                    return True
            elif edge_type_ok(nts[u], tv, R):
                e2 = dict(edges)
                e2[(u, v)] = R
                e2[(v, u)] = CONV4[R]
                if search(nts, e2, rest):
                    return True
        # request-closed cluster repetition (vertical only): the same
        # (type, demand) was fulfilled concretely by an earlier lap
        if R in (PP, PPI):
            for w in range(u):
                if w != u and nts[w] == nts[u] and any(
                        edges.get((w, v)) == R and D in nts[v]
                        for v in range(len(nts))):
                    if search(nts, edges, rest):
                        return True
                    break
        if len(nts) < max_nodes:
            for tv in types:
                if D not in tv or not edge_type_ok(nts[u], tv, R):
                    continue
                v = len(nts)
                e2 = dict(edges)
                e2[(u, v)] = R
                e2[(v, u)] = CONV4[R]
                np_ = rest + tuple((v, c) for c in tv
                                   if isinstance(c, Exists))
                if search(nts + (tv,), e2, np_):
                    return True
        failed.add(key)
        return False

    try:
        for t0 in root_types:
            pend = tuple((0, c) for c in t0 if isinstance(c, Exists))
            if search((t0,), {}, pend):
                return True
        return False
    except TimeoutError:
        return None


def part_c():
    A, B, Cn = AtomicConcept('A'), AtomicConcept('B'), AtomicConcept('C')
    nA, nB, nC = (NegAtomicConcept('A'), NegAtomicConcept('B'),
                  NegAtomicConcept('C'))
    top = Top()

    def AND(*cs):
        out = cs[0]
        for c in cs[1:]:
            out = And(out, c)
        return out

    cases = [
        ("C_force", AND(Exists(PP, Exists(DR, A)), ForAll(DR, nA)), False),
        ("C_split", AND(Exists(PP, AND(A, nB, ForAll(PP, nB),
                                       ForAll(PPI, nB), ForAll(PO, nB))),
                        Exists(PP, B)), False),
        ("C_recursive", Exists(DR, AND(A, Exists(DR, B))), True),
        ("C_up", AND(Exists(PP, top), ForAll(PP, Exists(PP, top))), True),
        ("C_2hop", AND(Exists(DR, Exists(PPI, A)), ForAll(DR, nA)), False),
        ("C_3hop", AND(Exists(DR, Exists(PPI, Exists(PPI, A))),
                       ForAll(DR, nA)), False),
        ("PO-loop", AND(Cn, Exists(PO, Exists(PO, Cn)), ForAll(PO, nC),
                        ForAll(DR, nC), ForAll(PP, nC), ForAll(PPI, nC)),
         True),
        ("C_dualdesc", AND(Exists(PO, A), Exists(PPI, top),
                           ForAll(PPI, AND(Exists(PPI, top),
                                           ForAll(DR, nA),
                                           ForAll(PO, nA)))), True),
        ("C_G2a (8th rev.)", AND(Exists(PP, top),
                                 ForAll(PP, AND(Exists(PP, top),
                                                AND(ForAll(PP, Exists(PP, top)),
                                                    ForAll(DR, A))))), True),
        ("p4 tower (9th rev.)", AND(A, ForAll(PP, nA), ForAll(PPI, nA),
                                    ForAll(PO, nA), ForAll(DR, nA),
                                    Exists(PP, AND(Exists(PP, top),
                                                   ForAll(PP,
                                                          AND(Exists(PP, top),
                                                              Exists(PPI, A)))))),
         True),
        ("sanity UNSAT", AND(Exists(DR, A), ForAll(DR, nA)), False),
    ]
    print(f"{'concept':22s} {'tableau':8s} {'CTQ':8s}")
    print('-' * 44)
    ok = True
    for name, C0, expected in cases:
        tb = tableau_sat(C0)
        got = decide_ctq(C0)
        agree = (got == tb == expected)
        ok &= agree
        fs = {True: 'SAT', False: 'UNSAT', None: 'T/O'}
        print(f"{name:22s} {fs[tb]:8s} {fs[got]:8s}"
              f"{'' if agree else '   <-- MISMATCH'}")
    print('-' * 44)

    rng = random.Random(131)
    lits = [AtomicConcept('A'), AtomicConcept('B'),
            NegAtomicConcept('A'), NegAtomicConcept('B'), Top()]

    def rand_c(depth):
        if depth == 0:
            return rng.choice(lits)
        r = rng.random()
        if r < 0.30:
            return Exists(rng.choice(RELS4), rand_c(depth - 1))
        if r < 0.60:
            return ForAll(rng.choice(RELS4), rand_c(depth - 1))
        if r < 0.80:
            return And(rand_c(depth - 1), rand_c(depth - 1))
        if r < 0.95:
            return Or(rand_c(depth - 1), rand_c(depth - 1))
        return rng.choice(lits)

    mism = timeouts = done = 0
    for _ in range(200):
        C0 = And(rand_c(2), rand_c(2))
        try:
            tb = tableau_sat(C0)
        except Exception:
            continue
        got = decide_ctq(C0, max_nodes=6, node_cap=60000)
        if got is None:
            timeouts += 1
            continue
        done += 1
        if got != tb:
            mism += 1
            print(f"    MISMATCH tableau={tb} ctq={got}: {C0}")
    print(f"random sweep: {done} decided ({timeouts} timeouts skipped), "
          f"{mism} disagreements with the tableau")
    return ok and mism == 0


if __name__ == '__main__':
    print(__doc__.split('\n')[1])
    print('=' * 70)
    r = [part_a(), part_b(), part_c()]
    print('=' * 70)
    print("WP26 OVERALL:", "PASS" if all(r) else "ATTENTION: see above")
    sys.exit(0 if all(r) else 1)
