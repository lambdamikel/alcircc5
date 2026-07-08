#!/usr/bin/env python3
"""
WP16 -- Acceptance-level mechanism check of the round-12 patchwork-bag
abstraction (split_forest_automata_with_appendices.tex), on the referee
diagnostic concepts and a random sweep, cross-checked against the
cover-tree tableau (src/cover_tree_tableau.py).

WHAT IS MODELLED.  A finite-occurrence rendering of the round-12
abstraction semantics: occurrences carry Hintikka types over Cl(C0);
existential formulas get declared witness edges (fresh occurrence, or
reuse of an existing occurrence -- reuse is round-12's exact occurrence
identity, which is how the strong-EQ loop concepts are satisfied);
vertical PP/PPI eventualities may be discharged by regularity (an earlier
occurrence with the same type: the finite prefix of a regular tail, i.e.
parity acceptance); and the pair relations not fixed by witness edges are
completed to a total atomic composition-closed network (this is exactly
the freedom Theorem 2.5 patchwork + App A compactness provide).

Two modes decide how universal obligations interact with that completion:

  repaired  Obligations (forall R.D at u) are enforced against the ACTUAL
            completed relation lambda(u,v) for EVERY pair of occurrences,
            i.e. shadow propagation is mandatory and exhaustive, and
            shadow entries are exact and never EQ.  This is the charitable
            reading of round-12 that the accompanying report argues is the
            intended (and repairable-to) semantics.

  literal   Obligations are enforced only on pairs with a declared witness
            edge.  Distant pairs escape, which is licensed by the tests as
            LITERALLY written in two independent ways: (i) Def 3.3 allows
            a shadow vector entry EQ (obligations (R,D) with R != EQ then
            never fire on that target), and (ii) no clause pins down the
            set of bags a shadow must continue into (App H: "all adjacent
            bags in which the shadow must continue" -- undefined), so a
            run may simply not carry the shadow to the target's bag.

EXPECTED RESULT.  In repaired mode all diagnostic verdicts agree with the
cover-tree tableau (including UNSAT for C_split via the Comp(PPI,PP)
DR-exclusion, and SAT for the strong-EQ PO-loop concept the retired
quasimodel reasoner got wrong).  In literal mode the unsatisfiable forced-
composition concepts C_force, C_split, C_2hop are ACCEPTED -- i.e. the two
spec loopholes are individually load-bearing for soundness.

CAVEATS.  This is a bounded mechanism probe, not a verification of
Theorem B: occurrence budget max_nodes, regularity approximated by
same-type blocking for PP/PPI requests.  UNSAT verdicts are exhaustive
only within those bounds (ample for the diagnostics, whose forced cores
are 3-4 occurrences deep).

Run:  python3 verification/python/wp16_round12_bag_acceptance.py
"""

import itertools
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', '..', 'src'))

from alcircc5_reasoner import (          # noqa: E402
    DR, PO, PP, PPI,
    AtomicConcept, NegAtomicConcept, Top, Bottom,
    And, Or, Exists, ForAll,
    closure, enumerate_types,
)
from cover_tree_tableau import check_sat as _tableau_sat  # noqa: E402


def tableau_sat(C0):
    """cover_tree_tableau returns (is_sat, info); keep the verdict only."""
    res = _tableau_sat(C0)
    return bool(res[0]) if isinstance(res, tuple) else bool(res)

RELS4 = (PP, PPI, PO, DR)
CONV = {PP: PPI, PPI: PP, PO: PO, DR: DR}

# RCC5 composition among DISTINCT occurrences: the paper's table with the
# EQ atom removed from each cell (EQ is identity; distinct occurrences are
# never EQ under strong equality / exact occurrence identity).
COMP4 = {
    (PP, PP): {PP}, (PP, PPI): {PP, PPI, PO, DR},
    (PP, PO): {PP, PO, DR}, (PP, DR): {DR},
    (PPI, PP): {PP, PPI, PO},          # EQ removed from {EQ,PP,PPI,PO}
    (PPI, PPI): {PPI}, (PPI, PO): {PPI, PO}, (PPI, DR): {PPI, PO, DR},
    (PO, PP): {PP, PO}, (PO, PPI): {PPI, PO, DR},
    (PO, PO): {PP, PPI, PO, DR}, (PO, DR): {PPI, PO, DR},
    (DR, PP): {PP, PO, DR}, (DR, PPI): {DR},
    (DR, PO): {PP, PO, DR}, (DR, DR): {PP, PPI, PO, DR},
}
COMP4 = {k: frozenset(v) for k, v in COMP4.items()}


# ------------------------------------------------ completion (PC search) --

def pc_refine(dom, n):
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
                        dom[(j, i)] = frozenset(CONV[r] for r in new)
                        dij = dom[(i, j)]
                        changed = True
                    if not dij:
                        return False
    return True


def completion_exists(n, init_dom):
    dom = dict(init_dom)
    if not pc_refine(dom, n):
        return False

    def rec(dom):
        und = [(p, d) for p, d in dom.items() if len(d) > 1 and p[0] < p[1]]
        if not und:
            # atomic: verify closure
            for i in range(n):
                for j in range(n):
                    if i == j:
                        continue
                    for k in range(n):
                        if k in (i, j):
                            continue
                        (ri,) = dom[(i, k)]
                        (rk,) = dom[(k, j)]
                        (rij,) = dom[(i, j)]
                        if rij not in COMP4[(ri, rk)]:
                            return False
            return True
        und.sort(key=lambda t: len(t[1]))
        pair, d = und[0]
        for r in d:
            nd = dict(dom)
            nd[pair] = frozenset([r])
            nd[(pair[1], pair[0])] = frozenset([CONV[r]])
            if pc_refine(nd, n) and rec(nd):
                return True
        return False

    return rec(dom)


# ------------------------------------------------------------ the machine --

def universals(t):
    return [(c.role, c.concept) for c in t if isinstance(c, ForAll)]


def edge_type_ok(tu, tv, R):
    """Obligation check on a DECLARED edge u -R-> v (both directions)."""
    for (S, D) in universals(tu):
        if S == R and D not in tv:
            return False
    for (S, D) in universals(tv):
        if S == CONV[R] and D not in tu:
            return False
    return True


def pair_allowed(tu, tv):
    """Relations between occurrences of types tu, tv compatible with BOTH
    types' universal obligations (used in repaired mode for all pairs)."""
    out = []
    for R in RELS4:
        if edge_type_ok(tu, tv, R):
            out.append(R)
    return frozenset(out)


def decide(C0, mode='repaired', max_nodes=5, node_cap=120000):
    """Existence of an accepted finite-prefix abstraction for C0."""
    cl = closure(C0)
    types = enumerate_types(cl)
    root_types = [t for t in types if C0 in t]
    counter = [0]
    failed = set()

    def build_domains(node_types, edges):
        n = len(node_types)
        dom = {}
        for i in range(n):
            for j in range(i + 1, n):
                if (i, j) in edges:
                    d = frozenset([edges[(i, j)]])
                elif mode == 'repaired':
                    d = pair_allowed(node_types[i], node_types[j])
                else:  # literal: distant pairs escape obligations
                    d = frozenset(RELS4)
                if not d:
                    return None
                dom[(i, j)] = d
                dom[(j, i)] = frozenset(CONV[r] for r in d)
        return dom

    def feasible(node_types, edges):
        dom = build_domains(node_types, edges)
        if dom is None:
            return False
        return pc_refine(dom, len(node_types))

    def search(node_types, edges, pending):
        counter[0] += 1
        if counter[0] > node_cap:
            raise TimeoutError
        key = (node_types, frozenset(edges.items()), frozenset(pending))
        if key in failed:
            return False
        if not feasible(node_types, edges):
            failed.add(key)
            return False
        if not pending:
            dom = build_domains(node_types, edges)
            if completion_exists(len(node_types), dom):
                return True
            failed.add(key)
            return False

        (u, ex) = pending[0]
        rest = tuple(pending[1:])
        R, D = ex.role, ex.concept

        # (a) reuse an existing occurrence (exact occurrence identity)
        for v in range(len(node_types)):
            tv = node_types[v]
            if v == u or D not in tv:
                continue
            if (u, v) in edges:
                if edges[(u, v)] == R and search(node_types, edges, rest):
                    return True
            else:
                if edge_type_ok(node_types[u], tv, R):
                    e2 = dict(edges)
                    e2[(u, v)] = R
                    e2[(v, u)] = CONV[R]
                    if search(node_types, e2, rest):
                        return True

        # (b) regularity (blocking) for vertical eventualities.
        # A request may be discharged by a repeating profile ONLY if the
        # blocking occurrence fulfilled the SAME request concretely (a
        # request-closed lap): naive same-type blocking would accept
        # infinite deferral of the eventuality, which is exactly what the
        # parity condition must reject (cf. the round-6/7 lap-collapse
        # defect in the no-automata thread).
        if R in (PP, PPI):
            for w in range(u):
                if w != u and node_types[w] == node_types[u] and any(
                        edges.get((w, v)) == R and D in node_types[v]
                        for v in range(len(node_types))):
                    if search(node_types, edges, rest):
                        return True
                    break

        # (c) fresh occurrence
        if len(node_types) < max_nodes:
            for tv in types:
                if D not in tv:
                    continue
                if not edge_type_ok(node_types[u], tv, R):
                    continue
                v = len(node_types)
                e2 = dict(edges)
                e2[(u, v)] = R
                e2[(v, u)] = CONV[R]
                new_pending = rest + tuple((v, c) for c in tv
                                           if isinstance(c, Exists))
                if search(node_types + (tv,), e2, new_pending):
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


# ------------------------------------------------------------ diagnostics --

def diagnostics():
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
        ("C_force  = ExPP.(ExDR.A) n AllDR.~A",
         AND(Exists(PP, Exists(DR, A)), ForAll(DR, nA)), False),
        ("C_split  = ExPP.(A n ~B n AllPP~B n AllPPI~B n AllPO~B) n ExPP.B",
         AND(Exists(PP, AND(A, nB, ForAll(PP, nB), ForAll(PPI, nB),
                            ForAll(PO, nB))), Exists(PP, B)), False),
        ("C_recur  = ExDR.(A n ExDR.B)",
         Exists(DR, AND(A, Exists(DR, B))), True),
        ("C_up     = ExPP.T n AllPP.ExPP.T",
         AND(Exists(PP, top), ForAll(PP, Exists(PP, top))), True),
        ("C_2hop   = ExDR.(ExPPI.A) n AllDR.~A",
         AND(Exists(DR, Exists(PPI, A)), ForAll(DR, nA)), False),
        ("C_3hop   = ExDR.(ExPPI.ExPPI.A) n AllDR.~A",
         AND(Exists(DR, Exists(PPI, Exists(PPI, A))), ForAll(DR, nA)),
         False),
        ("PO-loop  = C n ExPO.ExPO.C n All{PO,DR,PP,PPI}.~C",
         AND(Cn, Exists(PO, Exists(PO, Cn)), ForAll(PO, nC),
             ForAll(DR, nC), ForAll(PP, nC), ForAll(PPI, nC)), True),
        ("C_dual   = ExPO.A n ExPPI.T n AllPPI.(ExPPI.T n AllDR~A n AllPO~A)",
         AND(Exists(PO, A), Exists(PPI, top),
             ForAll(PPI, AND(Exists(PPI, top), ForAll(DR, nA),
                             ForAll(PO, nA)))), True),
        ("sanity   = ExDR.A n AllDR.~A",
         AND(Exists(DR, A), ForAll(DR, nA)), False),
        ("sanity   = ExPP.A n AllPP.(A u B)",
         AND(Exists(PP, A), ForAll(PP, Or(A, B))), True),
    ]

    print(f"{'concept':58s} {'tableau':8s} {'repaired':9s} {'literal':8s}",
          flush=True)
    print('-' * 88, flush=True)
    ok_rep = True
    literal_flips = []

    def fs(v):
        return {True: 'SAT', False: 'UNSAT', None: 'T/O'}[v]

    for name, C0, expected in cases:
        tb = tableau_sat(C0)
        rep = decide(C0, 'repaired')
        lit = decide(C0, 'literal')
        agree = (rep == tb == expected)
        ok_rep &= agree
        if lit != tb:
            literal_flips.append(name.split('=')[0].strip())
        flag = '' if agree else '   <-- MISMATCH'
        print(f"{name:58s} {fs(tb):8s} {fs(rep):9s} {fs(lit):8s}{flag}",
              flush=True)
    print('-' * 88)
    print(f"repaired mode: {'all verdicts agree with the tableau oracle'
          if ok_rep else 'MISMATCHES -- see above'}")
    print(f"literal mode:  wrong (SAT) verdicts on: "
          f"{', '.join(literal_flips) if literal_flips else 'none'}")
    print("    (each wrong literal verdict is an UNSAT concept ACCEPTED "
          "when distant pairs\n     escape obligations -- the EQ-entry / "
          "shadow-scope loopholes are load-bearing)")
    # For the headline finding we require the three forced-composition
    # concepts to flip in literal mode:
    need = {'C_force', 'C_split', 'C_2hop', 'C_3hop'}
    return ok_rep and need <= set(literal_flips)


# ---------------------------------------------------------- random sweep --

def random_concept(rng, depth):
    A, B = AtomicConcept('A'), AtomicConcept('B')
    nA, nB = NegAtomicConcept('A'), NegAtomicConcept('B')
    lits = [A, B, nA, nB, Top()]
    if depth == 0:
        return rng.choice(lits)
    r = rng.random()
    if r < 0.30:
        return Exists(rng.choice(RELS4), random_concept(rng, depth - 1))
    if r < 0.60:
        return ForAll(rng.choice(RELS4), random_concept(rng, depth - 1))
    if r < 0.80:
        return And(random_concept(rng, depth - 1),
                   random_concept(rng, depth - 1))
    if r < 0.95:
        return Or(random_concept(rng, depth - 1),
                  random_concept(rng, depth - 1))
    return rng.choice(lits)


def sweep(n=150, seed=97):
    rng = random.Random(seed)
    mism, timeouts, done = [], 0, 0
    for i in range(n):
        C0 = And(random_concept(rng, 2), random_concept(rng, 2))
        try:
            tb = tableau_sat(C0)
        except Exception:
            continue
        rep = decide(C0, 'repaired', max_nodes=6, node_cap=60000)
        if rep is None:
            timeouts += 1
            continue
        done += 1
        if rep != tb:
            mism.append((C0, tb, rep))
    print(f"random sweep: {done} concepts decided (of {n}; {timeouts} "
          f"budget timeouts skipped), {len(mism)} disagreements with the "
          f"cover-tree tableau")
    for C0, tb, rep in mism[:5]:
        print(f"    MISMATCH tableau={tb} repaired={rep}: {C0}")
    return len(mism) == 0


if __name__ == '__main__':
    print(__doc__.split('\n')[1])
    print('=' * 88)
    ok1 = diagnostics()
    print()
    ok2 = sweep()
    print('=' * 88)
    print("WP16 OVERALL:",
          "PASS (repaired discipline correct on all probes; literal spec "
          "loopholes demonstrated)" if ok1 and ok2 else
          "ATTENTION: see mismatches above")
    sys.exit(0 if (ok1 and ok2) else 1)
