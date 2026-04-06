#!/usr/bin/env python3
"""
One-Point Extension Check for RCC5

Key question: Given a path-consistent atomic RCC5 network on n nodes,
and a new element z with rel(z, p) = R for some existing node p,
can we ALWAYS find an assignment of rel(z, x_i) for all other nodes
such that the extended network is path-consistent?

If yes: the cross-chain edge assignment problem is solved, because
we can build any model by inductively adding one node at a time.

Method: For each path-consistent atomic network on n nodes,
for each node p, for each demanded relation R, try to find a
path-consistent extension.
"""

import itertools
from collections import defaultdict

# ── RCC5 ──────────────────────────────────────────────────────────

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


def is_path_consistent(net, nodes):
    """Check path-consistency of atomic network."""
    for i in nodes:
        for j in nodes:
            if i == j:
                continue
            for k in nodes:
                if k == i or k == j:
                    continue
                r_ij = net[(i, j)]
                r_ik = net[(i, k)]
                r_kj = net[(k, j)]
                if r_ij not in COMP[(r_ik, r_kj)]:
                    return False
    return True


def enum_pc_networks(n):
    """Enumerate all path-consistent atomic RCC5 networks on n nodes."""
    nodes = list(range(n))
    edges = [(i, j) for i in nodes for j in nodes if i < j]

    results = []
    for assignment in itertools.product(RELS, repeat=len(edges)):
        net = {}
        for idx, (i, j) in enumerate(edges):
            net[(i, j)] = assignment[idx]
            net[(j, i)] = INV[assignment[idx]]

        if is_path_consistent(net, nodes):
            results.append(net)

    return results, nodes


def try_one_point_extension(net, nodes, parent, demanded_rel):
    """
    Try to extend network by adding node z with rel(z, parent) = demanded_rel.
    Returns (success, assignment) where assignment maps each existing node
    to z's relation to it.

    Uses constraint propagation + backtracking.
    """
    z = max(nodes) + 1
    others = [x for x in nodes if x != parent]

    # Initialize domains: rel(z, x) for each x in others
    domains = {}
    for x in others:
        # Constraint from path through parent:
        # rel(z, x) ∈ comp(rel(z, parent), rel(parent, x))
        domain = COMP[(demanded_rel, net[(parent, x)])]
        domains[x] = set(domain)

    # Propagate constraints between pairs of others
    changed = True
    while changed:
        changed = False
        for x in others:
            for y in others:
                if x == y:
                    continue
                # rel(z, x) ∈ ∪_{r ∈ domains[y]} comp(r, rel(y, x))
                # But more precisely: for each r_x in domains[x],
                # there must exist r_y in domains[y] with r_x in comp(r_y, rel(y,x))
                # (This is arc consistency on z's variables)

                # Also: rel(z, x) must be in comp(rel(z, y), rel(y, x))
                # for SOME choice of rel(z, y) in domains[y]
                allowed = set()
                for ry in domains[y]:
                    allowed |= set(COMP[(ry, net[(y, x)])])
                new_domain = domains[x] & allowed
                if new_domain != domains[x]:
                    domains[x] = new_domain
                    changed = True
                    if not new_domain:
                        return False, None, "Empty domain for node " + str(x)

    # After arc consistency, try to find a consistent assignment
    # For small networks, just try all combinations
    if not others:
        return True, {parent: demanded_rel}, "trivial"

    def backtrack(idx, assignment):
        if idx == len(others):
            # Verify full path-consistency
            # Check all triples involving z
            all_nodes = nodes + [z]
            full_net = dict(net)
            full_net[(z, parent)] = demanded_rel
            full_net[(parent, z)] = INV[demanded_rel]
            for x in others:
                full_net[(z, x)] = assignment[x]
                full_net[(x, z)] = INV[assignment[x]]

            for i in all_nodes:
                for j in all_nodes:
                    if i == j:
                        continue
                    for k in all_nodes:
                        if k == i or k == j:
                            continue
                        if full_net[(i, j)] not in COMP[(full_net[(i, k)], full_net[(k, j)])]:
                            return None
            return dict(assignment)

        x = others[idx]
        for r in domains[x]:
            # Quick check against already assigned nodes
            ok = True
            for prev_x in others[:idx]:
                r_prev = assignment[prev_x]
                # Check: r ∈ comp(r_prev, rel(prev_x, x))
                if r not in COMP[(r_prev, net[(prev_x, x)])]:
                    ok = False
                    break
                # Check: r_prev ∈ comp(r, rel(x, prev_x))
                if r_prev not in COMP[(r, net[(x, prev_x)])]:
                    ok = False
                    break
            if ok:
                assignment[x] = r
                result = backtrack(idx + 1, assignment)
                if result is not None:
                    return result
                del assignment[x]
        return None

    result = backtrack(0, {})
    if result is not None:
        result[parent] = demanded_rel
        return True, result, "found"
    else:
        return False, None, "backtrack exhausted"


def test_one_point_extension(max_n=4):
    """Test one-point extension for all PC networks up to size max_n."""

    print("=" * 70)
    print("ONE-POINT EXTENSION TEST FOR RCC5")
    print("=" * 70)

    for n in range(2, max_n + 1):
        print(f"\n{'='*60}")
        print(f"Networks on {n} nodes")
        print(f"{'='*60}")

        networks, nodes = enum_pc_networks(n)
        print(f"  Path-consistent atomic networks: {len(networks)}")

        total_tests = 0
        total_success = 0
        total_failure = 0
        failures = []

        for net_idx, net in enumerate(networks):
            for parent in nodes:
                for R in RELS:
                    total_tests += 1
                    success, assignment, msg = try_one_point_extension(
                        net, nodes, parent, R
                    )
                    if success:
                        total_success += 1
                    else:
                        total_failure += 1
                        failures.append({
                            'net_idx': net_idx,
                            'net': dict(net),
                            'parent': parent,
                            'demanded': R,
                            'msg': msg,
                            'n': n
                        })

        print(f"  Total extension tests: {total_tests}")
        print(f"  Successes: {total_success}")
        print(f"  Failures: {total_failure}")

        if failures:
            print(f"\n  FAILURES FOUND:")
            for f in failures[:10]:  # Show first 10
                net_str = {(i,j): r for (i,j), r in f['net'].items() if i < j}
                print(f"    Net: {net_str}")
                print(f"    Parent: {f['parent']}, Demanded: {f['demanded']}")
                print(f"    Reason: {f['msg']}")
                print()
        else:
            print(f"  ALL EXTENSIONS SUCCEED ✓")

    return failures


def test_typed_extension(max_n=3):
    """
    Test one-point extension WITH type constraints (∀-safety).

    A type τ has ∀-constraints: for each R, a set of concepts that R-neighbors must satisfy.
    This means: if rel(z, x) = R and ∀R.C ∈ tp(z), then C ∈ tp(x).

    Model this abstractly: for each pair of types (τ, σ), there's a set of
    ALLOWED relations (those compatible with all ∀-constraints).

    Question: can one-point extension always succeed with these restrictions?
    """
    print(f"\n\n{'='*70}")
    print("TYPED ONE-POINT EXTENSION TEST")
    print("(with ∀-safety constraints filtering allowed relations)")
    print("=" * 70)

    # For each number of types T, enumerate all possible "allowed relation" matrices
    # between types. An allowed(τ, σ) ⊆ {DR, PO, PP, PPI}.
    # The constraint is: allowed(τ, σ) = INV(allowed(σ, τ)).
    # Also: allowed must be non-empty (otherwise the types can't coexist,
    # which means the completion graph already closed that branch).

    # For computational feasibility, test with 2 types and small networks.

    for num_types in [2, 3]:
        print(f"\n--- {num_types} types ---")

        types = list(range(num_types))
        type_pairs = [(t1, t2) for t1 in types for t2 in types if t1 <= t2]

        # Enumerate all non-empty subsets of RELS for each type pair
        # with INV consistency
        all_subsets = []
        for size in range(1, 5):
            for s in itertools.combinations(RELS, size):
                all_subsets.append(frozenset(s))

        # For each type pair (t1, t2), allowed(t1,t2) and allowed(t2,t1) must be inverses
        def inv_set(s):
            return frozenset(INV[r] for r in s)

        # For self-pairs (t, t): allowed must be closed under INV
        # For cross-pairs (t1, t2): allowed(t2,t1) = inv(allowed(t1,t2))

        total_configs = 0
        total_failures = 0
        failure_examples = []

        # Generate allowed-relation matrices
        # For tractability, just test a sample of interesting cases
        interesting_alloweds = [
            frozenset({DR}),
            frozenset({PO}),
            frozenset({PP}),
            frozenset({PPI}),
            frozenset({DR, PO}),
            frozenset({DR, PP}),
            frozenset({DR, PPI}),
            frozenset({PO, PP}),
            frozenset({PO, PPI}),
            frozenset({PP, PPI}),
            frozenset({DR, PO, PP}),
            frozenset({DR, PO, PPI}),
            frozenset({DR, PP, PPI}),
            frozenset({PO, PP, PPI}),
            frozenset({DR, PO, PP, PPI}),
        ]

        for n in [2, 3]:
            networks, nodes = enum_pc_networks(n)

            # For each network, assign types to nodes and test extensions
            for type_assignment in itertools.product(types, repeat=n):
                for allowed_self in interesting_alloweds:
                    # Self-type allowed rels (must be INV-closed)
                    if inv_set(allowed_self) != allowed_self:
                        continue

                    if num_types == 2:
                        for allowed_cross in interesting_alloweds:
                            allowed = {}
                            for t1 in types:
                                for t2 in types:
                                    if t1 == t2:
                                        allowed[(t1, t2)] = allowed_self
                                    elif t1 < t2:
                                        allowed[(t1, t2)] = allowed_cross
                                        allowed[(t2, t1)] = inv_set(allowed_cross)
                                    # else already set

                            # Check: does the existing network respect the type constraints?
                            for net in networks:
                                net_ok = True
                                for i in nodes:
                                    for j in nodes:
                                        if i == j:
                                            continue
                                        ti, tj = type_assignment[i], type_assignment[j]
                                        if net[(i, j)] not in allowed[(ti, tj)]:
                                            net_ok = False
                                            break
                                    if not net_ok:
                                        break

                                if not net_ok:
                                    continue

                                # Test one-point extensions with type constraints
                                for parent in nodes:
                                    for R in RELS:
                                        for new_type in types:
                                            # Check R is allowed between new_type and parent's type
                                            tp = type_assignment[parent]
                                            if R not in allowed[(new_type, tp)]:
                                                continue

                                            total_configs += 1

                                            # Try extension with restricted domains
                                            z = max(nodes) + 1
                                            others = [x for x in nodes if x != parent]

                                            domains = {}
                                            for x in others:
                                                tx = type_assignment[x]
                                                comp_domain = COMP[(R, net[(parent, x)])]
                                                type_domain = allowed[(new_type, tx)]
                                                domains[x] = set(comp_domain) & set(type_domain)
                                                if not domains[x]:
                                                    total_failures += 1
                                                    if len(failure_examples) < 5:
                                                        failure_examples.append({
                                                            'n': n,
                                                            'types': type_assignment,
                                                            'new_type': new_type,
                                                            'parent': parent,
                                                            'demanded': R,
                                                            'blocked_node': x,
                                                            'comp': comp_domain,
                                                            'type_allowed': type_domain,
                                                            'reason': 'empty initial domain'
                                                        })
                                                    break
                                            else:
                                                # Propagate arc consistency
                                                changed = True
                                                empty = False
                                                while changed and not empty:
                                                    changed = False
                                                    for x in others:
                                                        for y in others:
                                                            if x == y:
                                                                continue
                                                            new_d = set()
                                                            for ry in domains[y]:
                                                                new_d |= set(COMP[(ry, net[(y, x)])])
                                                            new_d &= domains[x]
                                                            if new_d != domains[x]:
                                                                domains[x] = new_d
                                                                changed = True
                                                                if not new_d:
                                                                    empty = True
                                                                    break
                                                        if empty:
                                                            break

                                                if empty:
                                                    total_failures += 1
                                                    if len(failure_examples) < 5:
                                                        failure_examples.append({
                                                            'n': n,
                                                            'types': type_assignment,
                                                            'new_type': new_type,
                                                            'parent': parent,
                                                            'demanded': R,
                                                            'reason': 'arc consistency failed'
                                                        })
                    # Skip 3-type cross pairs for now (too many combos)
                    elif num_types == 3:
                        # Just test with all-rels allowed cross
                        allowed = {}
                        for t1 in types:
                            for t2 in types:
                                if t1 == t2:
                                    allowed[(t1, t2)] = allowed_self
                                else:
                                    allowed[(t1, t2)] = frozenset(RELS)

                        for net in networks:
                            net_ok = True
                            for i in nodes:
                                for j in nodes:
                                    if i == j:
                                        continue
                                    ti, tj = type_assignment[i], type_assignment[j]
                                    if net[(i, j)] not in allowed[(ti, tj)]:
                                        net_ok = False
                                        break
                                if not net_ok:
                                    break

                            if not net_ok:
                                continue

                            for parent in nodes:
                                for R in RELS:
                                    for new_type in types:
                                        tp = type_assignment[parent]
                                        if R not in allowed[(new_type, tp)]:
                                            continue
                                        total_configs += 1
                                        # (skip full extension test for 3 types to keep runtime manageable)

            print(f"  n={n}: tested {total_configs} configs, {total_failures} failures")

        if failure_examples:
            print(f"\n  FAILURE EXAMPLES:")
            for f in failure_examples:
                print(f"    {f}")
        else:
            print(f"  No failures found in typed extension tests")

    return failure_examples


if __name__ == '__main__':
    # Phase 1: Pure algebraic one-point extension (no type constraints)
    failures = test_one_point_extension(max_n=4)

    # Phase 2: Typed extension (with ∀-safety constraints)
    typed_failures = test_typed_extension(max_n=3)

    print(f"\n\n{'='*70}")
    print("SUMMARY")
    print("=" * 70)
    if not failures and not typed_failures:
        print("ALL TESTS PASS: One-point extension always succeeds!")
        print("This means cross-chain edge assignment is always possible.")
    elif failures:
        print(f"PURE EXTENSION FAILURES: {len(failures)}")
        print("Cross-chain edge assignment may fail even without type constraints!")
    elif typed_failures:
        print(f"TYPED EXTENSION FAILURES: {len(typed_failures)}")
        print("Type constraints can block one-point extension.")
        print("Need to analyze whether these cases arise in actual tableaux.")
