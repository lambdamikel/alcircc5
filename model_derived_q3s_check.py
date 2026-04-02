#!/usr/bin/env python3
"""
Check whether MODEL-DERIVED DN networks always satisfy Q3s.

Model-derived DN: given a complete, composition-consistent RCC5 model
(set of elements with types and pairwise atomic relations), the DN sets
are DN(τ₁,τ₂) = {R(d₁,d₂) : tp(d₁)=τ₁, tp(d₂)=τ₂}.

This is STRONGER than "satisfiable DN" (which only requires one consistent
atomic assignment per type-pair).

Key question: does every model-derived DN satisfy Q3s?

Hand-constructed counterexample to test:
  4 elements: d1(τ₁), d1'(τ₁), d2(τ₂), d3(τ₃)
  d1-d2: PP,  d1-d3: PP,  d1-d1': DR
  d1'-d2: DR, d1'-d3: DR, d2-d3: PP

  DN(τ₁,τ₂) = {PP, DR}
  DN(τ₁,τ₃) = {PP, DR}
  DN(τ₂,τ₃) = {PP}

  Q3s check: R₁₂=PP, R₁₃=DR → need DR ∈ comp(PP, R₂₃) for R₂₃ ∈ {PP}
  comp(PP, PP) = {PP}. DR ∉ {PP}. FAIL!
"""

import itertools
from extension_gap_checker import RELS, INV, COMP, is_triple_consistent


def verify_model(elements, types, relations):
    """Verify that a model is composition-consistent.

    elements: list of element names
    types: dict mapping element -> type
    relations: dict mapping (e1,e2) -> atomic relation (for e1 < e2)
    """
    def get_rel(e1, e2):
        if e1 == e2:
            return 'EQ'
        key = (min(e1,e2), max(e1,e2))
        r = relations[key]
        return r if e1 < e2 else INV[r]

    # Check all triples
    for i, e1 in enumerate(elements):
        for j, e2 in enumerate(elements):
            if j <= i:
                continue
            for k, e3 in enumerate(elements):
                if k <= j:
                    continue
                r12 = get_rel(e1, e2)
                r13 = get_rel(e1, e3)
                r23 = get_rel(e2, e3)

                if r12 == 'EQ' or r13 == 'EQ' or r23 == 'EQ':
                    continue  # EQ triples are trivially consistent

                if not is_triple_consistent(r12, r23, r13):
                    print(f"  INCONSISTENT triple ({e1},{e2},{e3}): "
                          f"R({e1},{e2})={r12}, R({e2},{e3})={r23}, R({e1},{e3})={r13}")
                    return False
    return True


def extract_dn(elements, types, relations):
    """Extract DN sets from a model."""
    dn = {}
    type_set = set(types.values())

    def get_rel(e1, e2):
        if e1 == e2:
            return 'EQ'
        key = (min(e1,e2), max(e1,e2))
        r = relations[key]
        return r if e1 < e2 else INV[r]

    for t1 in type_set:
        for t2 in type_set:
            if t1 == t2:
                continue  # skip self-loops for this check
            rels = set()
            for e1 in elements:
                if types[e1] != t1:
                    continue
                for e2 in elements:
                    if types[e2] != t2:
                        continue
                    if e1 == e2:
                        continue
                    rels.add(get_rel(e1, e2))
            if rels:
                dn[(t1,t2)] = rels
    return dn


def check_q3s(dn, type_set):
    """Check if Q3s holds for the DN network (pairwise-distinct types only)."""
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
    print("="*60)
    print("TEST: Hand-constructed counterexample")
    print("="*60)

    elements = ['d1', 'd1p', 'd2', 'd3']
    types = {'d1': 'A', 'd1p': 'A', 'd2': 'B', 'd3': 'C'}
    relations = {
        ('d1', 'd1p'): 'DR',
        ('d1', 'd2'): 'PP',
        ('d1', 'd3'): 'PP',
        ('d1p', 'd2'): 'DR',
        ('d1p', 'd3'): 'DR',
        ('d2', 'd3'): 'PP',
    }

    print("Model:")
    for (e1,e2), r in sorted(relations.items()):
        print(f"  R({e1}[{types[e1]}], {e2}[{types[e2]}]) = {r}")

    print("\nVerifying composition consistency...")
    if verify_model(elements, types, relations):
        print("  ✓ Model is consistent!")
    else:
        print("  ✗ Model is INCONSISTENT!")
        return

    dn = extract_dn(elements, types, relations)
    print("\nDN sets:")
    for (t1,t2), rels in sorted(dn.items()):
        print(f"  DN({t1},{t2}) = {rels}")

    type_set = sorted(set(types.values()))
    failures = check_q3s(dn, type_set)
    if failures:
        print(f"\nQ3s FAILS! {len(failures)} failures:")
        for t1,t2,t3,r12,r13 in failures:
            print(f"  ({t1},{t2},{t3}): R12={r12}, R13={r13} — no witness R23 ∈ DN({t2},{t3})")
            print(f"    DN({t2},{t3}) = {dn.get((t2,t3), set())}")
            for r23 in dn.get((t2,t3), set()):
                print(f"    comp({r12}, {r23}) = {set(COMP.get((r12,r23), frozenset()))}")
    else:
        print("\n  Q3s satisfied!")

    print()
    print("="*60)
    print("SYSTEMATIC CHECK: All small model-derived DNs")
    print("="*60)
    print("Enumerate models with 2-4 elements, 2-3 types, check Q3s")
    print()

    # Enumerate all small models and check model-derived Q3s
    # Model: n elements with types from a set of k types, all pairwise relations
    total_models = 0
    q3s_violations = 0
    violation_examples = []

    for n_elements in range(3, 6):  # 3 to 5 elements
        for n_types in range(2, min(n_elements, 4) + 1):  # 2 to 3 types
            type_labels = [chr(ord('A') + i) for i in range(n_types)]

            # All type assignments (at least one element per type)
            for type_assign in itertools.product(range(n_types), repeat=n_elements):
                # Check: every type is used
                if len(set(type_assign)) < n_types:
                    continue

                elems = list(range(n_elements))
                tp = {i: type_labels[type_assign[i]] for i in elems}

                # All edges
                edges = [(i,j) for i in elems for j in elems if i < j]

                # Enumerate all consistent atomic networks
                def enum_networks(idx, network):
                    if idx == len(edges):
                        yield dict(network)
                        return
                    i, j = edges[idx]
                    for r in RELS:
                        network[(i,j)] = r
                        # Check triples with previously assigned edges
                        ok = True
                        for k in elems:
                            if k == i or k == j:
                                continue
                            ik = (min(i,k), max(i,k))
                            jk = (min(j,k), max(j,k))
                            if ik in network and jk in network:
                                r_ij = r if i < j else INV[r]
                                r_ik = network[ik] if i < k else INV[network[ik]]
                                r_jk = network[jk] if j < k else INV[network[jk]]
                                if not is_triple_consistent(r_ij, r_jk, r_ik):
                                    ok = False
                                    break
                        if ok:
                            yield from enum_networks(idx + 1, network)
                    if (i,j) in network:
                        del network[(i,j)]

                for network in enum_networks(0, {}):
                    total_models += 1

                    # Extract DN
                    dn = {}
                    for t1 in type_labels:
                        for t2 in type_labels:
                            if t1 == t2:
                                continue
                            rels = set()
                            for e1 in elems:
                                if tp[e1] != t1:
                                    continue
                                for e2 in elems:
                                    if tp[e2] != t2 or e1 == e2:
                                        continue
                                    key = (min(e1,e2), max(e1,e2))
                                    r = network[key]
                                    if e1 > e2:
                                        r = INV[r]
                                    rels.add(r)
                            if rels:
                                dn[(t1,t2)] = rels

                    failures = check_q3s(dn, type_labels)
                    if failures:
                        q3s_violations += 1
                        if len(violation_examples) < 5:
                            violation_examples.append({
                                'n': n_elements,
                                'types': dict(tp),
                                'network': dict(network),
                                'dn': {k: set(v) for k,v in dn.items()},
                                'failures': failures[:3],
                            })

        print(f"  After n_elements={n_elements}: "
              f"total models={total_models:,}, Q3s violations={q3s_violations}")

    print(f"\n{'='*60}")
    print(f"RESULT: {total_models:,} models checked, {q3s_violations} Q3s violations")

    if q3s_violations == 0:
        print("\n*** ALL model-derived DN networks satisfy Q3s! ***")
        print("This would mean Q3s IS extractable from models.")
    else:
        print(f"\n*** Model-derived DN can VIOLATE Q3s! ***")
        print(f"*** Q3s is genuinely NOT extractable! ***")
        for i, ex in enumerate(violation_examples):
            print(f"\nExample {i+1} ({ex['n']} elements):")
            for e, t in sorted(ex['types'].items()):
                print(f"  element {e}: type {t}")
            for (e1,e2), r in sorted(ex['network'].items()):
                print(f"  R({e1},{e2}) = {r}")
            print(f"  DN: {ex['dn']}")
            for t1,t2,t3,r12,r13 in ex['failures']:
                print(f"  Q3s fail: ({t1},{t2},{t3}) R12={r12}, R13={r13}")


if __name__ == '__main__':
    main()
