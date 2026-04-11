#!/usr/bin/env python3
"""
Fast check: does model-derived DN always satisfy Q3s?

Tests the hand-constructed counterexample and does a systematic
check on small models (3-4 elements, 2-3 types).
"""

import itertools
from extension_gap_checker import RELS, INV, COMP, is_triple_consistent


def check_q3s_dn(dn, type_set):
    """Check Q3s for DN on pairwise-distinct types. Returns list of failures."""
    failures = []
    for t1 in type_set:
        for t2 in type_set:
            if t1 == t2:
                continue
            for r12 in dn.get((t1,t2), set()):
                for t3 in type_set:
                    if t3 == t1 or t3 == t2:
                        continue
                    for r13 in dn.get((t1,t3), set()):
                        found = False
                        for r23 in dn.get((t2,t3), set()):
                            if r13 in COMP.get((r12, r23), frozenset()):
                                found = True
                                break
                        if not found:
                            failures.append((t1,t2,t3,r12,r13))
    return failures


def main():
    # -------------------------------------------------------
    # PART 1: Hand-constructed counterexample
    # -------------------------------------------------------
    print("="*60)
    print("PART 1: Hand-constructed counterexample")
    print("="*60)

    # Model: d1(A), d1'(A), d2(B), d3(C)
    # d1-d1': DR, d1-d2: PP, d1-d3: PP, d1'-d2: DR, d1'-d3: DR, d2-d3: PP
    elements = [0, 1, 2, 3]  # d1, d1', d2, d3
    tp = {0: 'A', 1: 'A', 2: 'B', 3: 'C'}
    net = {(0,1): 'DR', (0,2): 'PP', (0,3): 'PP',
           (1,2): 'DR', (1,3): 'DR', (2,3): 'PP'}

    # Verify consistency
    def get_rel(net, i, j):
        if i == j: return 'EQ'
        key = (min(i,j), max(i,j))
        r = net[key]
        return r if i < j else INV[r]

    print("Verifying model consistency...")
    ok = True
    for i in range(4):
        for j in range(i+1, 4):
            for k in range(j+1, 4):
                rij = get_rel(net, i, j)
                rik = get_rel(net, i, k)
                rjk = get_rel(net, j, k)
                if rij == 'EQ' or rik == 'EQ' or rjk == 'EQ':
                    continue
                if not is_triple_consistent(rij, rjk, rik):
                    print(f"  FAIL: ({i},{j},{k}) R={rij},{rjk},{rik}")
                    ok = False
    print(f"  {'✓ Consistent' if ok else '✗ INCONSISTENT'}")

    # Extract DN
    dn = {}
    type_set = ['A', 'B', 'C']
    for t1 in type_set:
        for t2 in type_set:
            if t1 == t2: continue
            rels = set()
            for e1 in elements:
                if tp[e1] != t1: continue
                for e2 in elements:
                    if tp[e2] != t2 or e1 == e2: continue
                    rels.add(get_rel(net, e1, e2))
            if rels:
                dn[(t1,t2)] = rels

    print("\nDN sets:")
    for (t1,t2), rels in sorted(dn.items()):
        if t1 < t2:
            print(f"  DN({t1},{t2}) = {rels}")

    failures = check_q3s_dn(dn, type_set)
    if failures:
        print(f"\n*** Q3s FAILS! {len(failures)} violations ***")
        for t1,t2,t3,r12,r13 in failures[:5]:
            print(f"  ({t1},{t2},{t3}): R12={r12}, R13={r13}")
            print(f"    Need: {r13} ∈ comp({r12}, R23) for some R23 ∈ DN({t2},{t3})={dn.get((t2,t3),set())}")
            for r23 in dn.get((t2,t3), set()):
                print(f"    comp({r12},{r23}) = {set(COMP.get((r12,r23), frozenset()))}")
    else:
        print("\n  Q3s satisfied")

    # -------------------------------------------------------
    # PART 2: Systematic check on small models
    # -------------------------------------------------------
    print()
    print("="*60)
    print("PART 2: Systematic check (3-4 elements, 2-3 types)")
    print("="*60)

    total_models = 0
    q3s_violations = 0
    examples = []

    for n in [3, 4]:
        for k in range(2, min(n, 4) + 1):
            type_labels = [chr(ord('A') + i) for i in range(k)]
            edges = [(i,j) for i in range(n) for j in range(i+1, n)]

            # Enumerate type assignments (each type used at least once)
            for ta in itertools.product(range(k), repeat=n):
                if len(set(ta)) < k:
                    continue
                tp_map = {i: type_labels[ta[i]] for i in range(n)}

                # Enumerate consistent atomic networks via backtracking
                def enum_nets(idx, network):
                    nonlocal total_models, q3s_violations
                    if idx == len(edges):
                        total_models += 1
                        # Extract DN
                        dn_loc = {}
                        for t1 in type_labels:
                            for t2 in type_labels:
                                if t1 == t2: continue
                                rels = set()
                                for e1 in range(n):
                                    if tp_map[e1] != t1: continue
                                    for e2 in range(n):
                                        if tp_map[e2] != t2 or e1 == e2: continue
                                        key = (min(e1,e2), max(e1,e2))
                                        r = network[key]
                                        if e1 > e2: r = INV[r]
                                        rels.add(r)
                                if rels:
                                    dn_loc[(t1,t2)] = rels

                        fails = check_q3s_dn(dn_loc, type_labels)
                        if fails:
                            q3s_violations += 1
                            if len(examples) < 5:
                                examples.append({
                                    'n': n, 'k': k,
                                    'types': dict(tp_map),
                                    'network': dict(network),
                                    'dn': {kk: set(v) for kk,v in dn_loc.items()},
                                    'fails': fails[:2],
                                })
                        return

                    i, j = edges[idx]
                    for r in RELS:
                        network[(i,j)] = r
                        ok = True
                        for m in range(n):
                            if m == i or m == j: continue
                            ik = (min(i,m), max(i,m))
                            jk = (min(j,m), max(j,m))
                            if ik in network and jk in network:
                                rij = r if i < j else INV[r]
                                rim = network[ik] if i < m else INV[network[ik]]
                                rjm = network[jk] if j < m else INV[network[jk]]
                                if not is_triple_consistent(rij, rjm, rim):
                                    ok = False
                                    break
                        if ok:
                            enum_nets(idx + 1, network)
                    if edges[idx] in network:
                        del network[edges[idx]]

                enum_nets(0, {})

        print(f"  After n={n}: total={total_models:,}, Q3s violations={q3s_violations}")

    print(f"\n{'='*60}")
    print(f"TOTAL: {total_models:,} models, {q3s_violations} with Q3s violations")
    if q3s_violations > 0:
        print(f"\n*** MODEL-DERIVED DN CAN VIOLATE Q3s ***")
        print(f"*** Q3s is genuinely NOT extractable from models ***\n")
        for i, ex in enumerate(examples[:5]):
            print(f"Example {i+1} ({ex['n']} elements, {ex['k']} types):")
            for e in sorted(ex['types'].keys()):
                print(f"  e{e}: type {ex['types'][e]}")
            for (e1,e2), r in sorted(ex['network'].items()):
                print(f"  R(e{e1},e{e2}) = {r}")
            print(f"  DN:")
            for (t1,t2), rels in sorted(ex['dn'].items()):
                if t1 < t2:
                    print(f"    DN({t1},{t2}) = {rels}")
            for t1,t2,t3,r12,r13 in ex['fails']:
                print(f"  Q3s fail: ({t1},{t2},{t3}) R12={r12}, R13={r13}")
            print()
    else:
        print("\n*** ALL model-derived DNs satisfy Q3s! ***")


if __name__ == '__main__':
    main()
