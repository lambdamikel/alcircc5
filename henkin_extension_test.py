#!/usr/bin/env python3
"""
Henkin tree extension test for ALCI_RCC5.

Tests whether the quasimodel's type set can be unfolded into
an actual tree model with consistent RCC5 relations. Builds
Henkin trees and checks if cross-edges can always be
consistently assigned.

Key question: when adding node e (child of d, role R), can we
always find a witness type AND atomic ρ(e, x) for all existing
x such that the star network is path-consistent?
"""

import itertools
import sys

from alcircc5_reasoner import (
    DR, PO, PP, PPI, BASE_RELS, INV, COMP,
    AtomicConcept, NegAtomicConcept, Top, Bottom,
    And, Or, Exists, ForAll,
    closure, enumerate_types, compute_safe,
    check_satisfiability
)


def star_path_consistent(center_doms, existing_rels):
    """Run arc-consistency on the star for a new node.

    center_doms: {existing_node_idx: domain_set}
    existing_rels: {(i,j): atomic_relation}

    Returns (feasible, reduced_doms)
    """
    nodes = list(center_doms.keys())
    doms = {i: set(center_doms[i]) for i in nodes}

    changed = True
    while changed:
        changed = False
        for i in nodes:
            for j in nodes:
                if i == j:
                    continue
                R_ij = existing_rels[(i, j)]
                new_dom = set()
                for r in doms[i]:
                    if COMP[(r, R_ij)] & doms[j]:
                        new_dom.add(r)
                if new_dom != doms[i]:
                    doms[i] = new_dom
                    changed = True
                    if not new_dom:
                        return False, doms
    return True, doms


# Future-flexibility ordering: prefer relations whose compositions with
# all roles give the widest domains.  PO averages 3.0 elements per
# composition, DR 2.75, PP/PPI 2.25.  Using this order makes cross-level
# constraints less likely to produce empty domains at deeper tree levels.
_RELATION_PREFERENCE = [PO, DR, PP, PPI]


def _sorted_rels(rel_set):
    """Sort a set of relations by future-flexibility preference."""
    return sorted(rel_set, key=lambda r: _RELATION_PREFERENCE.index(r))


def find_assignment(doms, existing_rels):
    """Backtracking atomic assignment from feasible star domains.
    Tries relations in future-flexibility order (PO > DR > PP > PPI)."""
    nodes = list(doms.keys())

    def bt(idx, assignment):
        if idx == len(nodes):
            return dict(assignment)
        node = nodes[idx]
        for r in _sorted_rels(doms[node]):
            ok = True
            for prev_node, prev_r in assignment:
                R_ij = existing_rels.get((node, prev_node))
                R_ji = existing_rels.get((prev_node, node))
                if R_ij is not None:
                    if prev_r not in COMP[(r, R_ij)]:
                        ok = False
                        break
                if R_ji is not None:
                    if r not in COMP[(prev_r, R_ji)]:
                        ok = False
                        break
            if ok:
                assignment.append((node, r))
                result = bt(idx + 1, assignment)
                if result is not None:
                    return result
                assignment.pop()
        return None

    result = bt(0, [])
    if result is None:
        return None
    return {node: r for node, r in result.items()}


def try_extend_node(nodes, rels, node_idx, R, witness, existing):
    """Try to extend the tree by adding a child with the given witness type.

    Returns (success, center_doms_or_None, failure_info_or_None).
    If success, center_doms contains the domain for each existing node.
    """
    safe = try_extend_node._safe  # set by caller
    type_list = try_extend_node._type_list

    # Compute domains for the star network
    center_doms = {}
    for x in existing:
        R_parent_x = rels[(node_idx, x)]
        dom = set(COMP[(INV[R], R_parent_x)]) & set(safe[(witness, nodes[x][0])])
        if not dom:
            return False, None, {
                'stage': 'domain_empty',
                'new_type': witness,
                'parent_type': nodes[node_idx][0],
                'existing_type': nodes[x][0],
                'R': R,
                'R_parent_x': R_parent_x,
                'comp': set(COMP[(INV[R], R_parent_x)]),
                'safe': set(safe[(witness, nodes[x][0])]),
            }
        center_doms[x] = dom

    # Get existing pairwise rels
    existing_rels = {}
    for i in existing:
        for j in existing:
            if i != j:
                existing_rels[(i, j)] = rels[(i, j)]

    # Star arc-consistency
    feasible, reduced = star_path_consistent(center_doms, existing_rels)
    if not feasible:
        return False, None, {
            'stage': 'star_ac',
            'new_type': witness,
            'parent_type': nodes[node_idx][0],
            'num_existing': len(existing),
        }

    # Find consistent assignment
    assignment = find_assignment(reduced, existing_rels)
    if assignment is None:
        return False, None, {
            'stage': 'assignment',
            'new_type': witness,
            'parent_type': nodes[node_idx][0],
            'num_existing': len(existing),
        }

    return True, assignment, None


def compute_witness_plan(type_list, safe, demands, type_set):
    """Precompute a sibling-compatible witness assignment for each type.

    For each type i in T with demands (R_1,D_1),...,(R_k,D_k),
    find witnesses j_1,...,j_k in T such that:
      - D_m ∈ type_list[j_m] and R_m ∈ safe(i, j_m)
      - For all pairs: comp(INV[R_m], R_m') ∩ safe(j_m, j_m') ≠ ∅

    Returns: {type_i: [(R, D, witness_j), ...]} for each type
    """
    T = type_set
    T_sorted = sorted(T)  # deterministic iteration order
    plan = {}

    for i in T_sorted:
        dems = demands[i]
        if not dems:
            plan[i] = []
            continue

        # For each demand, candidate witnesses (deterministic order)
        candidates = []
        for R, D in dems:
            cands = sorted([j for j in T
                            if D in type_list[j] and R in safe[(i, j)]])
            candidates.append(cands)

        k = len(dems)

        # Backtracking search for compatible assignment
        def bt(slot, assignment):
            if slot == k:
                return list(assignment)
            Rm = dems[slot][0]
            for jm in candidates[slot]:
                ok = True
                for prev_slot in range(len(assignment)):
                    jmp = assignment[prev_slot]
                    if jm == jmp:
                        continue  # same witness, always compatible
                    Rmp = dems[prev_slot][0]
                    if not (COMP[(INV[Rm], Rmp)] & safe[(jm, jmp)]):
                        ok = False
                        break
                    if not (COMP[(INV[Rmp], Rm)] & safe[(jmp, jm)]):
                        ok = False
                        break
                if ok:
                    assignment.append(jm)
                    result = bt(slot + 1, assignment)
                    if result is not None:
                        return result
                    assignment.pop()
            return None

        assignment = bt(0, [])
        if assignment is None:
            # Fallback: use first available witness per demand
            plan[i] = [(R, D, candidates[m][0] if candidates[m] else None)
                        for m, (R, D) in enumerate(dems)]
        else:
            plan[i] = [(dems[m][0], dems[m][1], assignment[m])
                        for m in range(k)]

    return plan


def build_henkin_tree(type_list, safe, demands, type_set, root_type, max_depth=5):
    """Build a Henkin tree using ONLY types from the quasimodel's type_set.

    Uses precomputed witness plan for sibling-compatible witness selection,
    then tries alternative witnesses with backtracking if cross-level
    constraints cause failures.
    """
    T = type_set
    try_extend_node._safe = safe
    try_extend_node._type_list = type_list

    # Precompute witness plan
    plan = compute_witness_plan(type_list, safe, demands, type_set)

    nodes = [(root_type, None, None)]  # (type, parent_idx, role)
    rels = {}
    depth_of = {0: 0}

    stats = {
        'tests': 0,
        'failures': 0,
        'domain_empty': 0,
        'star_ac': 0,
        'assignment': 0,
        'details': [],
    }

    frontier = [0]

    while frontier:
        next_frontier = []
        for node_idx in frontier:
            node_type = nodes[node_idx][0]
            node_depth = depth_of[node_idx]

            if node_depth >= max_depth:
                continue

            for R, D, planned_witness in plan.get(node_type, []):
                if planned_witness is None:
                    continue

                new_idx = len(nodes)
                existing = [i for i in range(new_idx) if i != node_idx]

                if not existing:
                    nodes.append((planned_witness, node_idx, R))
                    depth_of[new_idx] = node_depth + 1
                    next_frontier.append(new_idx)
                    rels[(node_idx, new_idx)] = R
                    rels[(new_idx, node_idx)] = INV[R]
                    continue

                stats['tests'] += 1

                # Try planned witness first, then alternatives
                all_candidates = [planned_witness]
                for j in T:
                    if j != planned_witness and D in type_list[j] and R in safe[(node_type, j)]:
                        all_candidates.append(j)

                # Try all candidates (sorted for determinism)
                all_candidates = sorted(set(all_candidates))

                best_witness = None
                best_assignment = None
                last_failure = None

                for witness in all_candidates:
                    success, assignment, failure = try_extend_node(
                        nodes, rels, node_idx, R, witness, existing)
                    if success:
                        best_witness = witness
                        best_assignment = assignment
                        break
                    last_failure = failure

                if best_witness is not None:
                    nodes.append((best_witness, node_idx, R))
                    depth_of[new_idx] = node_depth + 1
                    next_frontier.append(new_idx)
                    rels[(node_idx, new_idx)] = R
                    rels[(new_idx, node_idx)] = INV[R]
                    for x, r in best_assignment.items():
                        rels[(new_idx, x)] = r
                        rels[(x, new_idx)] = INV[r]
                else:
                    stats['failures'] += 1
                    if last_failure:
                        stage = last_failure['stage']
                        if stage == 'domain_empty':
                            stats['domain_empty'] += 1
                        elif stage == 'star_ac':
                            stats['star_ac'] += 1
                        elif stage == 'assignment':
                            stats['assignment'] += 1
                        last_failure['depth'] = node_depth + 1
                        if len(stats['details']) < 5:
                            stats['details'].append(last_failure)

                    witness = all_candidates[0]
                    nodes.append((witness, node_idx, R))
                    depth_of[new_idx] = node_depth + 1
                    next_frontier.append(new_idx)
                    rels[(node_idx, new_idx)] = R
                    rels[(new_idx, node_idx)] = INV[R]
                    for x in existing:
                        rels[(new_idx, x)] = DR
                        rels[(x, new_idx)] = DR

        frontier = next_frontier

    stats['tree_size'] = len(nodes)
    return stats


def test_concept(name, concept):
    """Test: reasoner says SAT → can we build a Henkin tree?"""
    result, info = check_satisfiability(concept)
    if not result:
        return 'UNSAT', None

    T = info.get('type_set')
    if T is None:
        return 'NO_TYPE_SET', None

    type_list = info['type_list']
    safe = info['safe']
    demands = info['demands']

    # Find root type in T
    roots = [i for i in T if concept in type_list[i]]
    if not roots:
        return 'NO_ROOT', None

    best = None
    for root in roots:
        r = build_henkin_tree(type_list, safe, demands, T, root, max_depth=5)
        if best is None or r['failures'] < best['failures']:
            best = r
            best['root'] = root
            best['type_set_size'] = len(T)

    return 'SAT', best


def main():
    A = AtomicConcept('A')
    B = AtomicConcept('B')
    C = AtomicConcept('C')
    D = AtomicConcept('D')
    nA = NegAtomicConcept('A')
    nB = NegAtomicConcept('B')
    nD = NegAtomicConcept('D')
    top = Top()

    tests = [
        ("A", A),
        ("∃DR.A", Exists(DR, A)),
        ("∃PP.A", Exists(PP, A)),
        ("∃PP.⊤ ⊓ ∃DR.⊤", And(Exists(PP, top), Exists(DR, top))),
        ("∃PP.⊤ ⊓ ∀PP.∃PP.⊤",
         And(Exists(PP, top), ForAll(PP, Exists(PP, top)))),
        ("∃PP.∃PPI.⊤", Exists(PP, Exists(PPI, top))),
        ("∃PP.(A ⊓ ∃PPI.B) ⊓ B",
         And(Exists(PP, And(A, Exists(PPI, B))), B)),
        ("∃DR.A ⊓ ∀DR.A",
         And(Exists(DR, A), ForAll(DR, A))),
        ("∃DR.(A ⊓ B) ⊓ ∀DR.(A ⊔ ¬B)",
         And(Exists(DR, And(A, B)), ForAll(DR, Or(A, nB)))),
        ("∃PP.(∀DR.A) ⊓ ∃DR.¬A",
         And(Exists(PP, ForAll(DR, A)), Exists(DR, nA))),
        ("∃PP.A ⊓ ∃PPI.B ⊓ ∃DR.C",
         And(And(Exists(PP, A), Exists(PPI, B)), Exists(DR, C))),
        ("∃PP.(A ⊓ ∃PP.A)",
         Exists(PP, And(A, Exists(PP, A)))),
        ("∃PP.∀PP.⊥", Exists(PP, ForAll(PP, Bottom()))),
        # Cross-role demands with universals
        ("∃PP.(∀DR.A) ⊓ ∃DR.(∀PP.B) ⊓ ∃PO.⊤",
         And(And(Exists(PP, ForAll(DR, A)),
                 Exists(DR, ForAll(PP, B))),
             Exists(PO, top))),
        # PP-chain with DR witnesses
        ("∃PP.(A ⊓ ∃DR.B) ⊓ ∀PP.(A ⊓ ∃PP.⊤ ⊓ ∃DR.B)",
         And(Exists(PP, And(A, Exists(DR, B))),
             ForAll(PP, And(And(A, Exists(PP, top)), Exists(DR, B))))),
        # PO-incoherent counterexample
        ("∃PO.D ⊓ ∃DR.(B ⊓ ∀PO.¬D) ⊓ ∀DR.¬D ⊓ ∀PP.¬D ⊓ ∀PPI.¬D",
         And(And(And(And(
             Exists(PO, D),
             Exists(DR, And(B, ForAll(PO, nD)))),
             ForAll(DR, nD)),
             ForAll(PP, nD)),
             ForAll(PPI, nD))),
    ]

    print("=" * 70)
    print("HENKIN TREE EXTENSION TEST (backtracking witness selection)")
    print("Does the quasimodel unfold into a consistent tree model?")
    print("=" * 70)

    total_concepts = 0
    total_ext_tests = 0
    total_ext_failures = 0
    failed_concepts = []

    for name, concept in tests:
        status, result = test_concept(name, concept)
        if status != 'SAT':
            print(f"  [{status}] {name}")
            continue

        total_concepts += 1
        total_ext_tests += result['tests']
        total_ext_failures += result['failures']

        ok = "✓" if result['failures'] == 0 else "✗"
        print(f"  {ok} {name}: |T|={result['type_set_size']}, "
              f"tree={result['tree_size']}, "
              f"ext={result['tests']}, fail={result['failures']} "
              f"(empty={result['domain_empty']}, "
              f"ac={result['star_ac']}, "
              f"assign={result['assignment']})")

        if result['failures'] > 0:
            failed_concepts.append(name)
            for d in result['details']:
                print(f"      {d['stage']}: depth={d.get('depth','?')}, "
                      f"new=τ{d['new_type']}, parent=τ{d['parent_type']}")
                if 'R' in d:
                    print(f"        R={d['R']}, R_parent_x={d['R_parent_x']}")
                    print(f"        comp∩safe: {d['comp']} ∩ {d['safe']}")

    print(f"\n{'='*60}")
    print(f"RESULTS")
    print(f"{'='*60}")
    print(f"  SAT concepts tested: {total_concepts}")
    print(f"  Total extension tests: {total_ext_tests}")
    print(f"  Total extension failures: {total_ext_failures}")

    if total_ext_failures == 0:
        print(f"\n  ✓ ALL EXTENSIONS SUCCEED")
        print(f"  Evidence that the quasimodel correctly unfolds to a model")
    else:
        print(f"\n  ✗ {len(failed_concepts)} concepts have failures:")
        for name in failed_concepts:
            print(f"      - {name}")

    return total_ext_failures == 0


if __name__ == '__main__':
    main()
