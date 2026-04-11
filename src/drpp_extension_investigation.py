#!/usr/bin/env python3
"""
Deep investigation of the DR+PP case for ALCI_RCC5 decidability.

Three questions:
1. Is ONE-STEP EXTENSION always solvable for concrete consistent networks?
   (Given a consistent network + node x, can we always add a DR-witness y
   with SOME consistent edge assignment — not necessarily profile-copy?)

2. Can we always find an extension that AVOIDS PP edges to the new node?
   (This would prevent cascading of the DR+PP problem.)

3. What does the constraint propagation look like? When z has R(z,x) = PP,
   forcing R(z,y) = DR, what constraints does this impose on other new edges?
"""

import itertools
from extension_gap_checker import (
    RELS, INV, COMP, is_triple_consistent, enumerate_consistent_networks
)


def solve_extension_csp(base_net, n_existing, parent, witness_rel,
                        exclude_pp=False):
    """Try to add a witness node y to a consistent base network.

    parent: index of the node that y is a witness of
    witness_rel: the relation R(parent, y) = S

    Returns: list of all valid assignments for edges to y,
             or None if only checking satisfiability (returns True/False).

    If exclude_pp: exclude PP from domains (test avoidability).
    """
    y = n_existing  # new node index

    # Build domains
    other_nodes = [i for i in range(n_existing) if i != parent]
    if not other_nodes:
        return [{}]  # No other nodes, trivially solvable

    # Get relation from each other node to parent
    def get_rel_directed(net, a, b):
        """Get R(a,b) from stored network where (min,max) -> R."""
        if a < b:
            return net[(a, b)]
        else:
            return INV[net[(b, a)]]

    # Domains for R(z, y) for each z in other_nodes
    domains = {}
    for z in other_nodes:
        r_zp = get_rel_directed(base_net, z, parent)
        dom = set(COMP[(r_zp, witness_rel)])
        if exclude_pp:
            dom.discard('PP')
            if not dom:
                return []  # Empty domain after excluding PP
        domains[z] = dom

    # Solve CSP via backtracking
    # Variables: R(z, y) for z in other_nodes
    # Constraints: for each pair z1, z2:
    #   R(z1,y) ∈ comp(R(z1,z2), R(z2,y))  AND  R(z2,y) ∈ comp(R(z2,z1), R(z1,y))
    # Also: R(parent,y) = witness_rel must be consistent with all
    #   R(z,y) via the triple (parent, z, y)

    assignment = {}
    solutions = []

    def is_consistent_with_assigned(z, r_zy):
        """Check if assigning R(z,y) = r_zy is consistent with all
        previously assigned edges and the parent edge."""
        # Check triple (parent, z, y)
        r_pz = get_rel_directed(base_net, parent, z)
        r_py = witness_rel
        # Need: is_triple_consistent(R(parent,z), R(z,y), R(parent,y))
        if not is_triple_consistent(r_pz, r_zy, r_py):
            return False

        # Check triples with all previously assigned z' nodes
        for z2, r_z2y in assignment.items():
            r_zz2 = get_rel_directed(base_net, z, z2)
            if not is_triple_consistent(r_zz2, r_z2y, r_zy):
                return False
        return True

    def backtrack(idx):
        if idx == len(other_nodes):
            solutions.append(dict(assignment))
            return True  # Found at least one

        z = other_nodes[idx]
        for r in domains[z]:
            if is_consistent_with_assigned(z, r):
                assignment[z] = r
                backtrack(idx + 1)
                del assignment[z]
                # Don't stop at first solution — enumerate all
        return len(solutions) > 0

    backtrack(0)
    return solutions


def question1_one_step_extension():
    """Q1: Is one-step extension always solvable?

    For each consistent network and each node x and each witness relation S,
    check if we can always add a witness y with R(x,y) = S.
    """
    print("=" * 70)
    print("Q1: Is one-step extension ALWAYS solvable for concrete networks?")
    print("=" * 70)
    print()

    for witness_rel in RELS:
        total = 0
        failures = 0
        failure_examples = []

        for n in range(2, 6):  # 2 to 5 existing nodes
            for net in enumerate_consistent_networks(n):
                for parent in range(n):
                    total += 1
                    solutions = solve_extension_csp(net, n, parent, witness_rel)
                    if not solutions:
                        failures += 1
                        if len(failure_examples) < 3:
                            failure_examples.append((n, dict(net), parent))

        if failures == 0:
            print(f"  S = {witness_rel}: ALWAYS solvable ({total:,} cases checked)")
        else:
            print(f"  S = {witness_rel}: {failures} FAILURES out of {total:,} cases!")
            for n, net, p in failure_examples:
                print(f"    n={n}, parent={p}, net={net}")
    print()


def question2_avoid_pp():
    """Q2: Can we always avoid PP edges to the new DR-witness?

    When adding a DR-witness y, can we find an assignment where
    R(z,y) ≠ PP for all z?
    """
    print("=" * 70)
    print("Q2: Can we always AVOID PP edges to DR-witnesses?")
    print("=" * 70)
    print()

    total = 0
    must_use_pp = 0
    pp_examples = []

    for n in range(2, 6):
        n_total = 0
        n_pp = 0
        for net in enumerate_consistent_networks(n):
            for parent in range(n):
                total += 1
                n_total += 1

                # All solutions
                all_sols = solve_extension_csp(net, n, parent, 'DR')
                # Solutions without PP
                no_pp_sols = solve_extension_csp(net, n, parent, 'DR',
                                                 exclude_pp=True)

                if all_sols and not no_pp_sols:
                    must_use_pp += 1
                    n_pp += 1
                    if len(pp_examples) < 5:
                        # Find which edges MUST be PP
                        pp_examples.append({
                            'n': n,
                            'net': dict(net),
                            'parent': parent,
                            'n_solutions': len(all_sols),
                            'sample_sol': all_sols[0],
                        })

        print(f"  n={n}: {n_pp} cases require PP out of {n_total}")

    print(f"\n  TOTAL: {must_use_pp} cases require PP out of {total:,}")

    if must_use_pp > 0:
        print(f"\n  *** Cannot always avoid PP — cascading possible! ***")
        for i, ex in enumerate(pp_examples[:5]):
            print(f"\n  Example {i+1} (n={ex['n']}, parent={ex['parent']}):")
            for (a, b), r in sorted(ex['net'].items()):
                print(f"    R({a},{b}) = {r}")
            print(f"    Solutions (all use PP): {ex['n_solutions']}")
            sol = ex['sample_sol']
            for z, r in sorted(sol.items()):
                r_zp = ex['net'].get((min(z, ex['parent']), max(z, ex['parent'])))
                if z > ex['parent']:
                    r_zp_dir = INV.get(r_zp, r_zp)
                else:
                    r_zp_dir = r_zp
                print(f"    R({z},y) = {r}  (R({z},parent) = {r_zp_dir})")
    else:
        print(f"\n  *** PP edges are ALWAYS avoidable! ***")
        print(f"  This means the DR+PP cascading problem does NOT arise.")
    print()


def question3_constraint_propagation():
    """Q3: Detailed constraint propagation for DR+PP case.

    When R(z,x) = PP forces R(z,y) = DR for the DR-witness y,
    what does this imply for other nodes' edges to y?
    """
    print("=" * 70)
    print("Q3: Constraint propagation from forced DR edges")
    print("=" * 70)
    print()

    # For a concrete analysis: enumerate 3-node networks with
    # parent=0, z1=1, z2=2 where R(z1,0)=PP, and see what
    # constraints R(z1,y)=DR imposes on R(z2,y).

    print("Setup: parent=0, z1 has R(z1,parent)=PP → R(z1,y)=DR forced")
    print("For each R(z2,parent) and R(z1,z2), what is dom(R(z2,y))?")
    print()

    # Enumerate all consistent 3-node networks with R(1,0) = PP
    # (stored as R(0,1) = PPI since 0 < 1)
    for r_z2_p in RELS:  # R(z2, parent) = R(2, 0)
        for r_z1_z2 in RELS:  # R(z1, z2) = R(1, 2)
            # Stored: (0,1) -> PPI (since R(1,0)=PP means R(0,1)=PPI)
            # (0,2) -> INV[r_z2_p] (since R(2,0)=r_z2_p means R(0,2)=INV[r_z2_p])
            # (1,2) -> r_z1_z2

            # Check base network consistency
            # Triple (0,1,2): R(0,1)=PPI, R(1,2)=r_z1_z2, R(0,2)=INV[r_z2_p]
            r_01 = 'PPI'  # R(0,1) = PPI since R(1,0)=PP
            r_02 = INV[r_z2_p]  # R(0,2) = INV[R(2,0)]
            r_12 = r_z1_z2

            if not is_triple_consistent(r_01, r_12, r_02):
                continue

            # Now compute domain for R(z2,y)
            # Constraints:
            # 1. R(z2,y) ∈ comp(R(z2,parent), R(parent,y)) = comp(r_z2_p, DR)
            dom1 = set(COMP[(r_z2_p, 'DR')])

            # 2. R(z2,y) ∈ comp(R(z2,z1), R(z1,y)) = comp(INV[r_z1_z2], DR)
            r_z2_z1 = INV[r_z1_z2]
            dom2 = set(COMP[(r_z2_z1, 'DR')])

            # 3. R(z1,y) ∈ comp(R(z1,z2), R(z2,y)) — constrains R(z2,y)
            #    R(z1,y) = DR, so DR ∈ comp(r_z1_z2, R(z2,y))
            dom3 = set()
            for r in RELS:
                if 'DR' in COMP.get((r_z1_z2, r), frozenset()):
                    dom3.add(r)

            final_dom = dom1 & dom2 & dom3

            if final_dom != dom1:  # forced-DR node adds extra constraints
                print(f"  R(z1,z2)={r_z1_z2}, R(z2,p)={r_z2_p}: "
                      f"dom1={sorted(dom1)}, dom2={sorted(dom2)}, "
                      f"dom3={sorted(dom3)}, final={sorted(final_dom)}"
                      f"{'  *** EMPTY ***' if not final_dom else ''}")
    print()


def question4_model_theoretic_argument():
    """Q4: Does the model-theoretic argument prove one-step extension?

    The argument: any consistent atomic RCC5 network is realizable (Renz 1999).
    In the realization, we can always find a new region with any desired
    base relation to the parent. The resulting extension is consistent.

    Verify: the extension CSP is always solvable for ALL witness relations.
    """
    print("=" * 70)
    print("Q4: Comprehensive extension solvability check")
    print("=" * 70)
    print()

    for n in range(2, 6):
        for s in RELS:
            total = 0
            failures = 0
            for net in enumerate_consistent_networks(n):
                for parent in range(n):
                    total += 1
                    sols = solve_extension_csp(net, n, parent, s)
                    if not sols:
                        failures += 1
            print(f"  n={n}, S={s}: {failures} failures / {total} cases")
    print()


def question5_pp_avoidability_detailed():
    """Q5: When PP IS required, what's the structure?

    Detailed analysis of cases where R(z,y) = PP is forced.
    """
    print("=" * 70)
    print("Q5: Detailed PP-forcing analysis")
    print("=" * 70)
    print()

    print("For each z, R(z,y) = PP requires PP ∈ comp(R(z,x), DR).")
    print("comp(R, DR) contains PP only for R = DR:")
    for r in RELS:
        dom = COMP[(r, 'DR')]
        has_pp = 'PP' in dom
        print(f"  comp({r}, DR) = {set(dom)} — {'PP possible' if has_pp else 'no PP'}")
    print()
    print("So R(z,y) = PP can only happen when R(z,x) = DR.")
    print("And it's NEVER forced — comp(DR, DR) = {DR,PO,PP,PPI},")
    print("so we can always choose DR, PO, or PPI instead.")
    print()
    print("BUT: the choice must be consistent with OTHER edges to y.")
    print("Can the inter-node constraints force PP?")
    print()

    # Find cases where PP is the ONLY option for some node
    pp_forced_cases = []
    for n in range(3, 6):
        for net in enumerate_consistent_networks(n):
            for parent in range(n):
                others = [i for i in range(n) if i != parent]
                # Check each solution: is there always some z with R(z,y)=PP?
                sols = solve_extension_csp(net, n, parent, 'DR')
                no_pp_sols = solve_extension_csp(net, n, parent, 'DR',
                                                 exclude_pp=True)
                if sols and not no_pp_sols:
                    # ALL solutions require PP somewhere
                    # Find which z is forced to PP in every solution
                    for z in others:
                        always_pp = all(s[z] == 'PP' for s in sols)
                        if always_pp:
                            pp_forced_cases.append({
                                'n': n,
                                'net': dict(net),
                                'parent': parent,
                                'z': z,
                                'n_sols': len(sols),
                            })

    if pp_forced_cases:
        print(f"Found {len(pp_forced_cases)} cases where some z is FORCED to PP:")
        for i, case in enumerate(pp_forced_cases[:10]):
            print(f"\n  Case {i+1} (n={case['n']}, parent={case['parent']}, "
                  f"forced z={case['z']}):")
            for (a,b), r in sorted(case['net'].items()):
                print(f"    R({a},{b}) = {r}")

            def get_r(net, a, b):
                if a < b: return net[(a,b)]
                return INV[net[(b,a)]]

            p = case['parent']
            z = case['z']
            r_zp = get_r(case['net'], z, p)
            print(f"    R(z={z}, parent={p}) = {r_zp}")
            print(f"    comp({r_zp}, DR) = {set(COMP[(r_zp, 'DR')])}")
            # Show constraints from other nodes
            for z2 in range(case['n']):
                if z2 == p or z2 == z:
                    continue
                r_z2p = get_r(case['net'], z2, p)
                r_zz2 = get_r(case['net'], z, z2)
                print(f"    R(z2={z2}, parent) = {r_z2p}, R(z={z}, z2={z2}) = {r_zz2}")
    else:
        print("No z is ever FORCED to PP in any network!")
        print("PP is always avoidable by choosing alternative edges.")
    print()


def question6_no_pp_extension_universal():
    """Q6: Can we ALWAYS extend with a DR-witness using NO PP edges,
    for ALL base networks up to size 5?"""
    print("=" * 70)
    print("Q6: Universal PP-free DR-extension check (up to n=5)")
    print("=" * 70)
    print()

    for n in range(2, 6):
        total = 0
        need_pp = 0
        no_sol = 0
        for net in enumerate_consistent_networks(n):
            for parent in range(n):
                total += 1
                all_sols = solve_extension_csp(net, n, parent, 'DR')
                no_pp_sols = solve_extension_csp(net, n, parent, 'DR',
                                                exclude_pp=True)
                if not all_sols:
                    no_sol += 1
                elif not no_pp_sols:
                    need_pp += 1

        print(f"  n={n}: total={total}, no solution={no_sol}, "
              f"need PP={need_pp}, PP-free OK={total - no_sol - need_pp}")
    print()


if __name__ == '__main__':
    question1_one_step_extension()
    question2_avoid_pp()
    question3_constraint_propagation()
    question5_pp_avoidability_detailed()
    question6_no_pp_extension_universal()
