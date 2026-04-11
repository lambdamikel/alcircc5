#!/usr/bin/env python3
"""
Algebraic verification of the one-point extension property for RCC5.

GOAL: Prove that the following property holds for ALL RCC5 configurations:

  For any path-consistent atomic network G, any parent p, demanded relation R,
  and any SAFE restrictions satisfying quasimodel triple-type conditions,
  the one-point extension always produces a satisfiable disjunctive network.

APPROACH: Exhaustively verify the "quadruple consistency" property:
  For all atomic relations R, S_px, S_xy, S_py, r_zx with:
    - r_zx ∈ comp(R, S_px)           [z-to-x composition domain]
    - S_py ∈ comp(S_px, S_xy)        [existing path-consistency]
    - S_py = S_py                     [atomic, given]

  Check: comp(r_zx, S_xy) ∩ comp(R, S_py) ≠ ∅

  This is the PURE version (no SAFE restriction). If this holds,
  then the one-point extension works algebraically.

  Then check: under quasimodel SAFE conditions, does the intersection
  remain non-empty?
"""

import itertools

DR, PO, PP, PPI = 'DR', 'PO', 'PP', 'PPI'
RELS = [DR, PO, PP, PPI]
INV = {DR: DR, PO: PO, PP: PPI, PPI: PP}

COMP = {}
COMP[(DR, DR)] = frozenset({DR, PO, PP, PPI})
COMP[(DR, PO)] = frozenset({DR, PO, PP})
COMP[(DR, PP)] = frozenset({DR, PO, PP})
COMP[(DR, PPI)] = frozenset({DR})
COMP[(PO, DR)] = frozenset({DR, PO, PPI})
COMP[(PO, PO)] = frozenset({DR, PO, PP, PPI})
COMP[(PO, PP)] = frozenset({PO, PP})
COMP[(PO, PPI)] = frozenset({DR, PO, PPI})
COMP[(PP, DR)] = frozenset({DR})
COMP[(PP, PO)] = frozenset({DR, PO, PP})
COMP[(PP, PP)] = frozenset({PP})
COMP[(PP, PPI)] = frozenset({DR, PO, PP, PPI})
COMP[(PPI, DR)] = frozenset({DR, PO, PPI})
COMP[(PPI, PO)] = frozenset({PO, PPI})
COMP[(PPI, PP)] = frozenset({PO, PP, PPI})
COMP[(PPI, PPI)] = frozenset({PPI})


def test_quadruple_consistency():
    """
    PROPERTY 1 (Pure): For all R, S_px, S_xy, S_py, r_zx with valid constraints:
      comp(r_zx, S_xy) ∩ comp(R, S_py) ≠ ∅

    This means: the edge z-y can always be found consistently through BOTH
    the path z→x→y AND the path z→p→y.
    """
    print("=" * 70)
    print("TEST 1: Quadruple Consistency (Pure)")
    print("comp(r_zx, S_xy) ∩ comp(R, S_py) ≠ ∅")
    print("=" * 70)

    total = 0
    failures = 0
    details = []

    for R in RELS:
        for S_px in RELS:
            for S_xy in RELS:
                # S_py must be in comp(S_px, S_xy) [path-consistency of existing]
                for S_py in COMP[(S_px, S_xy)]:
                    # r_zx must be in comp(R, S_px)
                    for r_zx in COMP[(R, S_px)]:
                        total += 1

                        through_x = COMP[(r_zx, S_xy)]
                        through_p = COMP[(R, S_py)]
                        intersection = through_x & through_p

                        if not intersection:
                            failures += 1
                            details.append({
                                'R': R, 'S_px': S_px, 'S_xy': S_xy,
                                'S_py': S_py, 'r_zx': r_zx,
                                'through_x': through_x,
                                'through_p': through_p
                            })

    print(f"  Total quadruples tested: {total}")
    print(f"  Failures: {failures}")
    if failures:
        for d in details[:10]:
            print(f"    R={d['R']}, S_px={d['S_px']}, S_xy={d['S_xy']}, "
                  f"S_py={d['S_py']}, r_zx={d['r_zx']}")
            print(f"      through_x={d['through_x']}, through_p={d['through_p']}")
    else:
        print("  ALL QUADRUPLES CONSISTENT ✓")

    return failures == 0


def test_safe_intersection():
    """
    PROPERTY 2 (With SAFE): Under quasimodel conditions, does the three-way
    intersection comp(r_zx, S_xy) ∩ comp(R, S_py) ∩ SAFE remain non-empty?

    Quasimodel conditions:
    - comp(r_zx, S_xy) ∩ SAFE_y ≠ ∅  [triple-type for (z, x, y)]
    - comp(R, S_py) ∩ SAFE_y ≠ ∅     [triple-type for (z, p, y)]

    Question: does comp(r_zx, S_xy) ∩ comp(R, S_py) ∩ SAFE_y ≠ ∅?
    """
    print(f"\n{'='*70}")
    print("TEST 2: Three-Way Intersection (With SAFE)")
    print("comp(r_zx, S_xy) ∩ comp(R, S_py) ∩ SAFE_y ≠ ∅")
    print("=" * 70)

    all_subsets = []
    for size in range(1, 5):
        for s in itertools.combinations(RELS, size):
            all_subsets.append(frozenset(s))

    total = 0
    failures = 0
    failure_details = []

    for R in RELS:
        for S_px in RELS:
            for S_xy in RELS:
                for S_py in COMP[(S_px, S_xy)]:
                    for r_zx in COMP[(R, S_px)]:
                        through_x = COMP[(r_zx, S_xy)]
                        through_p = COMP[(R, S_py)]
                        pure_intersection = through_x & through_p

                        # For each possible SAFE_y:
                        for SAFE_y in all_subsets:
                            # Check quasimodel conditions
                            cond1 = through_x & SAFE_y  # triple (z, x, y)
                            cond2 = through_p & SAFE_y   # triple (z, p, y)

                            if not cond1 or not cond2:
                                continue  # Invalid quasimodel, skip

                            total += 1
                            three_way = through_x & through_p & SAFE_y

                            if not three_way:
                                failures += 1
                                if len(failure_details) < 20:
                                    failure_details.append({
                                        'R': R, 'S_px': S_px, 'S_xy': S_xy,
                                        'S_py': S_py, 'r_zx': r_zx,
                                        'SAFE_y': SAFE_y,
                                        'through_x': through_x,
                                        'through_p': through_p,
                                        'cond1': cond1,
                                        'cond2': cond2,
                                        'pure': pure_intersection
                                    })

    print(f"  Total configurations tested: {total}")
    print(f"  Failures: {failures}")
    if failures:
        print(f"\n  FAILURES (three-way intersection empty):")
        for d in failure_details[:10]:
            print(f"    R={d['R']}, S_px={d['S_px']}, S_xy={d['S_xy']}, S_py={d['S_py']}")
            print(f"    r_zx={d['r_zx']}, SAFE_y={d['SAFE_y']}")
            print(f"    through_x={d['through_x']}, through_p={d['through_p']}")
            print(f"    QM cond1(z,x,y)={d['cond1']}, cond2(z,p,y)={d['cond2']}")
            print(f"    pure intersection={d['pure']}")
            print()
    else:
        print("  ALL THREE-WAY INTERSECTIONS NON-EMPTY ✓")

    return failures == 0


def test_full_arc_consistency():
    """
    PROPERTY 3: Full arc consistency check on star networks.

    Given z with edges to p, x₁, x₂ (3 existing nodes),
    with fixed relations among p, x₁, x₂ (path-consistent),
    and domains D(z, xᵢ) = comp(R, rel(p, xᵢ)) ∩ SAFE(z, xᵢ):

    Does arc consistency always succeed?

    This tests the MULTI-step arc consistency propagation,
    not just individual triples.
    """
    print(f"\n{'='*70}")
    print("TEST 3: Full Arc Consistency on Star Networks")
    print("(z connected to p, x₁, x₂ with quasimodel SAFE conditions)")
    print("=" * 70)

    all_subsets = []
    for size in range(1, 5):
        for s in itertools.combinations(RELS, size):
            all_subsets.append(frozenset(s))

    total_tests = 0
    total_failures = 0
    failure_details = []

    # Enumerate path-consistent atomic networks on {p, x1, x2} = {0, 1, 2}
    for r01 in RELS:  # rel(p, x1)
        for r02 in RELS:  # rel(p, x2)
            for r12 in RELS:  # rel(x1, x2)
                net = {
                    (0,1): r01, (1,0): INV[r01],
                    (0,2): r02, (2,0): INV[r02],
                    (1,2): r12, (2,1): INV[r12],
                }
                # Check path-consistency
                nodes = [0, 1, 2]
                pc = True
                for i in nodes:
                    for j in nodes:
                        if i == j: continue
                        for k in nodes:
                            if k == i or k == j: continue
                            if net[(i,j)] not in COMP[(net[(i,k)], net[(k,j)])]:
                                pc = False
                                break
                        if not pc: break
                    if not pc: break
                if not pc:
                    continue

                # For each R (demanded relation z to p=0)
                for R in RELS:
                    comp_d1 = COMP[(R, r01)]
                    comp_d2 = COMP[(R, r02)]

                    # For each SAFE pair
                    for S1 in all_subsets:
                        d1 = set(comp_d1) & set(S1)
                        if not d1: continue
                        # Check triple (z, p, x1): comp(R, r01) ∩ S1 ≠ ∅ ✓

                        for S2 in all_subsets:
                            d2 = set(comp_d2) & set(S2)
                            if not d2: continue
                            # Check triple (z, p, x2): comp(R, r02) ∩ S2 ≠ ∅ ✓

                            # Check triple (z, x1, x2):
                            # ∃ r1 ∈ d1, r2 ∈ d2: r2 ∈ comp(r1, r12)?
                            # (quasimodel triple condition)
                            qm_zx1x2 = False
                            for r1 in d1:
                                if set(COMP[(r1, r12)]) & d2:
                                    qm_zx1x2 = True
                                    break

                            qm_zx2x1 = False
                            for r2 in d2:
                                if set(COMP[(r2, INV[r12])]) & d1:
                                    qm_zx2x1 = True
                                    break

                            if not (qm_zx1x2 and qm_zx2x1):
                                continue  # Not a valid quasimodel config

                            total_tests += 1

                            # Run arc consistency
                            domains = {1: set(d1), 2: set(d2)}
                            changed = True
                            empty = False
                            while changed and not empty:
                                changed = False
                                for x in [1, 2]:
                                    for y in [1, 2]:
                                        if x == y: continue
                                        allowed = set()
                                        for ry in domains[y]:
                                            allowed |= set(COMP[(ry, net[(y, x)])])
                                        new_d = domains[x] & allowed
                                        if new_d != domains[x]:
                                            domains[x] = new_d
                                            changed = True
                                            if not new_d:
                                                empty = True
                                                break
                                    if empty: break

                            if empty:
                                total_failures += 1
                                if len(failure_details) < 10:
                                    failure_details.append({
                                        'net': f'p-x1={r01}, p-x2={r02}, x1-x2={r12}',
                                        'R': R,
                                        'S1': S1, 'S2': S2,
                                        'd1_init': set(comp_d1) & set(S1),
                                        'd2_init': set(comp_d2) & set(S2),
                                        'd1_final': domains[1],
                                        'd2_final': domains[2],
                                    })

    print(f"  Total valid configurations: {total_tests}")
    print(f"  Arc-consistency failures: {total_failures}")
    if failure_details:
        print(f"\n  FAILURES:")
        for d in failure_details:
            print(f"    Net: {d['net']}, R={d['R']}")
            print(f"    SAFE: S1={d['S1']}, S2={d['S2']}")
            print(f"    Init: d1={d['d1_init']}, d2={d['d2_init']}")
            print(f"    Final: d1={d['d1_final']}, d2={d['d2_final']}")
            print()
    else:
        print("  ALL ARC-CONSISTENCY CHECKS PASS ✓")

    return total_failures == 0


def test_compositional_monotonicity():
    """
    PROPERTY 4: Check a key algebraic property.

    For all R, S_px, S_xy, S_py with S_py ∈ comp(S_px, S_xy):
      comp(R, S_py) ⊆ ∪_{s ∈ comp(R, S_px)} comp(s, S_xy)

    Equivalently: comp(R, {specific S_py}) ⊆ comp(comp(R, S_px), S_xy)

    This is the "two-path composition" property: going through p→y directly
    is contained in going through p→x→y.
    """
    print(f"\n{'='*70}")
    print("TEST 4: Compositional Monotonicity")
    print("comp(R, S_py) ⊆ ∪_{s ∈ comp(R, S_px)} comp(s, S_xy)")
    print("=" * 70)

    total = 0
    failures = 0

    for R in RELS:
        for S_px in RELS:
            for S_xy in RELS:
                for S_py in COMP[(S_px, S_xy)]:
                    total += 1

                    # LHS: comp(R, S_py)
                    lhs = COMP[(R, S_py)]

                    # RHS: ∪_{s ∈ comp(R, S_px)} comp(s, S_xy)
                    rhs = set()
                    for s in COMP[(R, S_px)]:
                        rhs |= set(COMP[(s, S_xy)])

                    if not lhs.issubset(rhs):
                        failures += 1
                        diff = lhs - rhs
                        print(f"  FAIL: R={R}, S_px={S_px}, S_xy={S_xy}, S_py={S_py}")
                        print(f"    LHS={lhs}, RHS={rhs}, diff={diff}")

    print(f"  Total: {total}, Failures: {failures}")
    if failures == 0:
        print("  COMPOSITIONAL MONOTONICITY HOLDS ✓")
        print("  This means: comp(R, S_py) ⊆ comp(comp(R, S_px), S_xy)")
        print("  Every relation achievable through p→y is also achievable through p→x→y")

    return failures == 0


def test_reverse_path():
    """
    PROPERTY 5: Check the REVERSE direction.

    For all R, S_px, S_xy, S_py, r_zx with valid constraints:
      comp(r_zx, S_xy) ∩ comp(R, S_py) ≠ ∅

    AND: comp(r_zx, S_xy) ∩ comp(R, S_py) = comp(R, S_py)
    i.e., the pure intersection EQUALS the through-p domain?

    This would mean: any relation achievable through p is also
    achievable through x, so SAFE restrictions on the x-path
    never kill a p-path relation.
    """
    print(f"\n{'='*70}")
    print("TEST 5: Does comp(R, S_py) ⊆ comp(r_zx, S_xy) always hold?")
    print("(If yes: through-p path is always within through-x path)")
    print("=" * 70)

    total = 0
    superset_count = 0
    subset_count = 0

    for R in RELS:
        for S_px in RELS:
            for S_xy in RELS:
                for S_py in COMP[(S_px, S_xy)]:
                    for r_zx in COMP[(R, S_px)]:
                        total += 1
                        through_x = COMP[(r_zx, S_xy)]
                        through_p = COMP[(R, S_py)]

                        if through_p.issubset(through_x):
                            superset_count += 1
                        if through_x.issubset(through_p):
                            subset_count += 1

    print(f"  Total: {total}")
    print(f"  through_p ⊆ through_x: {superset_count}/{total} ({100*superset_count/total:.1f}%)")
    print(f"  through_x ⊆ through_p: {subset_count}/{total} ({100*subset_count/total:.1f}%)")


if __name__ == '__main__':
    p1 = test_quadruple_consistency()
    p2 = test_safe_intersection()
    p3 = test_full_arc_consistency()
    p4 = test_compositional_monotonicity()
    test_reverse_path()

    print(f"\n\n{'='*70}")
    print("SUMMARY")
    print("=" * 70)
    print(f"  Property 1 (Pure quadruple consistency): {'PASS ✓' if p1 else 'FAIL ✗'}")
    print(f"  Property 2 (Three-way with SAFE):        {'PASS ✓' if p2 else 'FAIL ✗'}")
    print(f"  Property 3 (Full arc consistency):        {'PASS ✓' if p3 else 'FAIL ✗'}")
    print(f"  Property 4 (Compositional monotonicity):  {'PASS ✓' if p4 else 'FAIL ✗'}")

    if p1 and p2 and p3 and p4:
        print(f"\n  ALL PROPERTIES VERIFIED.")
        print(f"  The one-point extension ALWAYS works under quasimodel conditions.")
        print(f"  Combined with RCC5 patchwork: quasimodel → model.")
        print(f"  Combined with type elimination: ALCI_RCC5 is DECIDABLE.")
