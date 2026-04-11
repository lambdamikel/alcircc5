#!/usr/bin/env python3
"""
Check whether Q3 (existential) implies Q3s (strong) for the RCC5 composition table.

Q3:  For all R12 ∈ DN(τ1,τ2), there EXIST R13 ∈ DN(τ1,τ3) and R23 ∈ DN(τ2,τ3)
     with R13 ∈ comp(R12, R23).

Q3s: For all R12 ∈ DN(τ1,τ2) and all R13 ∈ DN(τ1,τ3), there EXISTS R23 ∈ DN(τ2,τ3)
     with R13 ∈ comp(R12, R23).

If Q3 → Q3s for all possible DN sets over the RCC5 composition table,
then the existing proof already works.

Also check: does the model-derived DN network always satisfy Q3s?
A model-derived DN network is satisfiable (there exists a consistent atomic
refinement). If satisfiable → Q3s, then Q3s is extractable.
"""

import itertools
from extension_gap_checker import RELS, INV, COMP

def check_q3(dn, types):
    """Check if Q3 (existential) holds for the DN sets.

    Only checks triples of pairwise-distinct types. When t3 = t1 or t3 = t2,
    DN(t,t) contains EQ and the condition is automatically satisfied by
    converse closure.
    """
    for t1 in types:
        for t2 in types:
            if t1 == t2:
                continue
            for r12 in dn.get((t1,t2), set()):
                for t3 in types:
                    if t3 == t1 or t3 == t2:
                        continue
                    # Need: exist r13 ∈ DN(t1,t3), r23 ∈ DN(t2,t3) with r13 ∈ comp(r12, r23)
                    found = False
                    for r23 in dn.get((t2,t3), set()):
                        for r13_cand in COMP.get((r12, r23), frozenset()):
                            if r13_cand in dn.get((t1,t3), set()):
                                found = True
                                break
                        if found:
                            break
                    if not found:
                        return False
    return True

def check_q3s(dn, types):
    """Check if Q3s (strong) holds for the DN sets.

    Only checks triples of pairwise-distinct types (same reasoning as check_q3).
    """
    for t1 in types:
        for t2 in types:
            if t1 == t2:
                continue
            for r12 in dn.get((t1,t2), set()):
                for t3 in types:
                    if t3 == t1 or t3 == t2:
                        continue
                    for r13 in dn.get((t1,t3), set()):
                        # Need: exist r23 ∈ DN(t2,t3) with r13 ∈ comp(r12, r23)
                        found = False
                        for r23 in dn.get((t2,t3), set()):
                            if r13 in COMP.get((r12, r23), frozenset()):
                                found = True
                                break
                        if not found:
                            return False
    return True

def is_dn_satisfiable(dn, types):
    """Check if the DN network has a satisfying atomic assignment.

    A satisfying assignment picks one value per edge such that all
    triples are composition-consistent.

    For small type sets, brute-force enumerate.
    """
    edges = [(t1,t2) for t1 in types for t2 in types if t1 != t2]
    if not edges:
        return True

    def backtrack(idx, assignment):
        if idx == len(edges):
            return True
        t1, t2 = edges[idx]
        domain = dn.get((t1,t2), set())
        if not domain:
            return False  # no possible relation → unsatisfiable
        for r in domain:
            assignment[(t1,t2)] = r
            # Check all triples involving this new edge
            # For each third type t3 (distinct from t1, t2), check:
            #   assignment[(t1,t2)] ∈ comp(assignment[(t1,t3)], assignment[(t3,t2)])
            consistent = True
            for t3 in types:
                if t3 == t1 or t3 == t2:
                    continue
                if (t1,t3) in assignment and (t3,t2) in assignment:
                    r13 = assignment[(t1,t3)]
                    r32 = assignment[(t3,t2)]
                    if r not in COMP.get((r13, r32), frozenset()):
                        consistent = False
                        break
                if (t1,t3) in assignment and (t3, t2) not in assignment and (t2,t3) in assignment:
                    # We have (t1,t3) and (t2,t3), check triple via:
                    # r12 ∈ comp(r13, inv(r23)) = comp(r13, r32)
                    r13 = assignment[(t1,t3)]
                    r23 = assignment[(t2,t3)]
                    r32 = INV[r23]
                    if r not in COMP.get((r13, r32), frozenset()):
                        consistent = False
                        break
            if consistent:
                if backtrack(idx+1, assignment):
                    return True
        if (t1,t2) in assignment:
            del assignment[(t1,t2)]
        return False

    return backtrack(0, {})

def main():
    print("="*60)
    print("TEST 1: Does Q3 imply Q3s for all DN sets over RCC5?")
    print("="*60)

    # Enumerate DN networks on small type sets
    # For 2 types: DN has 2 edges (t1→t2, t2→t1), each a subset of {DR,PO,PP,PPI}
    # For each edge, 15 non-empty subsets. But must be converse-closed.

    types2 = ['a', 'b']

    all_subsets = [frozenset()]
    for size in range(1, 5):
        for combo in itertools.combinations(RELS, size):
            all_subsets.append(frozenset(combo))
    nonempty_subsets = [s for s in all_subsets if s]

    # For 2 types with converse closure:
    # DN(a,b) and DN(b,a) must be converse-related: R ∈ DN(a,b) iff inv(R) ∈ DN(b,a)
    q3_count = 0
    q3s_count = 0
    q3_not_q3s = 0

    for d_ab in nonempty_subsets:
        d_ba = frozenset(INV[r] for r in d_ab)
        dn = {('a','b'): d_ab, ('b','a'): d_ba}

        if check_q3(dn, types2):
            q3_count += 1
            if check_q3s(dn, types2):
                q3s_count += 1
            else:
                q3_not_q3s += 1
                if q3_not_q3s <= 5:
                    print(f"  Q3 but NOT Q3s: DN(a,b)={set(d_ab)}, DN(b,a)={set(d_ba)}")

    print(f"\n  2 types: Q3 satisfied: {q3_count}, Q3s satisfied: {q3s_count}, Q3∧¬Q3s: {q3_not_q3s}")
    print(f"  (Note: with 2 types, no triple of distinct types exists → Q3/Q3s vacuously true)")

    # For 3 types (more interesting)
    types3 = ['a', 'b', 'c']
    q3_count = 0
    q3s_count = 0
    q3_not_q3s = 0
    examples = []

    # DN has 6 directed edges. With converse closure, we choose 3 undirected edges.
    for d_ab in nonempty_subsets:
        d_ba = frozenset(INV[r] for r in d_ab)
        for d_ac in nonempty_subsets:
            d_ca = frozenset(INV[r] for r in d_ac)
            for d_bc in nonempty_subsets:
                d_cb = frozenset(INV[r] for r in d_bc)
                dn = {
                    ('a','b'): d_ab, ('b','a'): d_ba,
                    ('a','c'): d_ac, ('c','a'): d_ca,
                    ('b','c'): d_bc, ('c','b'): d_cb,
                }
                if check_q3(dn, types3):
                    q3_count += 1
                    if check_q3s(dn, types3):
                        q3s_count += 1
                    else:
                        q3_not_q3s += 1
                        if q3_not_q3s <= 3:
                            examples.append(dict(dn))

    print(f"  3 types: Q3 satisfied: {q3_count}, Q3s satisfied: {q3s_count}, Q3∧¬Q3s: {q3_not_q3s}")
    if examples:
        for ex in examples[:3]:
            print(f"\n  Example (Q3 but NOT Q3s):")
            for (t1,t2), rels in sorted(ex.items()):
                if t1 < t2:
                    print(f"    DN({t1},{t2}) = {set(rels)}")

    print()
    print("="*60)
    print("TEST 2: Does SATISFIABLE DN network imply Q3s?")
    print("="*60)
    print("(A satisfiable DN has a consistent atomic assignment)")
    print()

    # For 3 types: check all DN networks that are satisfiable
    sat_count = 0
    sat_q3s = 0
    sat_not_q3s = 0
    sat_examples = []

    for d_ab in nonempty_subsets:
        d_ba = frozenset(INV[r] for r in d_ab)
        for d_ac in nonempty_subsets:
            d_ca = frozenset(INV[r] for r in d_ac)
            for d_bc in nonempty_subsets:
                d_cb = frozenset(INV[r] for r in d_bc)
                dn = {
                    ('a','b'): d_ab, ('b','a'): d_ba,
                    ('a','c'): d_ac, ('c','a'): d_ca,
                    ('b','c'): d_bc, ('c','b'): d_cb,
                }
                if is_dn_satisfiable(dn, types3):
                    sat_count += 1
                    if check_q3s(dn, types3):
                        sat_q3s += 1
                    else:
                        sat_not_q3s += 1
                        if sat_not_q3s <= 3:
                            sat_examples.append(dict(dn))

    print(f"  3 types: Satisfiable: {sat_count}, Q3s: {sat_q3s}, Sat∧¬Q3s: {sat_not_q3s}")
    if sat_examples:
        for ex in sat_examples[:3]:
            print(f"\n  Example (satisfiable but NOT Q3s):")
            for (t1,t2), rels in sorted(ex.items()):
                if t1 < t2:
                    print(f"    DN({t1},{t2}) = {set(rels)}")
    else:
        print("\n  *** ALL satisfiable DN networks satisfy Q3s! ***")
        print("  This would mean: model-derived DN always satisfies Q3s")
        print("  → Q3s is extractable from models → extension gap is closed!")


if __name__ == '__main__':
    main()
