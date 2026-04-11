#!/usr/bin/env python3
"""
Direct demand satisfaction check for ALCI_RCC5 open completion graphs.

The Henkin-free approach: instead of extracting a quasimodel and building
a model via tree unraveling (which has the extension gap), check whether
the open completion graph ALREADY satisfies all existential demands.

Setup:
  - Nodes 0..n-1, each with a Hintikka type tp[i] from {0..k-1}
  - Complete RCC5 graph: E(i,j) ∈ {DR, PO, PP, PPI} for distinct i,j
  - Composition-consistent: all triples satisfy the RCC5 composition table
  - Each type τ has existential demands: {(R, τ') | ∃R.C ∈ τ, C realized by τ'}
  - ∀-constraints: if E(i,j) = R and ∀R.C ∈ tp[i], then C ∈ tp[j]

Key question (demand satisfaction):
  For every node i and every demand (R, τ') of tp[i],
  does there exist j ≠ i with E(i,j) = R and tp[j] = τ'?

If this holds for all open completion graphs, the graph IS a model
(no Henkin construction needed), proving soundness of the Section 7 tableau.

We enumerate:
  - All composition-consistent RCC5 graphs on n nodes
  - All type assignments with k types
  - All "demand structures" (which types demand which relations to which types)
  - Filter for ∀-safety (edges respect universal constraints)
  - Test demand satisfaction
"""

import itertools
import sys
import time
from collections import defaultdict

# ── RCC5 infrastructure ──────────────────────────────────────────────

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


def is_triple_consistent(r_ab, r_bc, r_ac):
    """Check if (a,b,c) with given relations is composition-consistent."""
    if r_ac not in COMP[(r_ab, r_bc)]:
        return False
    r_cb = INV[r_bc]
    if r_ab not in COMP[(r_ac, r_cb)]:
        return False
    r_ba = INV[r_ab]
    if r_bc not in COMP[(r_ba, r_ac)]:
        return False
    return True


def get_rel(network, i, j):
    """Get relation from i to j."""
    if i < j:
        return network[(i, j)]
    else:
        return INV[network[(j, i)]]


# ── Network enumeration ──────────────────────────────────────────────

def enumerate_consistent_networks(n):
    """Enumerate all composition-consistent atomic RCC5 networks on n nodes."""
    if n <= 1:
        return [{}]

    edges = [(i, j) for i in range(n) for j in range(i+1, n)]
    results = []

    def backtrack(idx, network):
        if idx == len(edges):
            results.append(dict(network))
            return
        i, j = edges[idx]
        for r in RELS:
            network[(i, j)] = r
            consistent = True
            for k in range(n):
                if k == i or k == j:
                    continue
                edge_ik = (min(i, k), max(i, k))
                edge_jk = (min(j, k), max(j, k))
                if edge_ik in network and edge_jk in network:
                    r_ij = r if i < j else INV[r]
                    r_ik = get_rel(network, i, k)
                    r_jk = get_rel(network, j, k)
                    if not is_triple_consistent(r_ij, r_jk, r_ik):
                        consistent = False
                        break
            if consistent:
                backtrack(idx + 1, network)
        if (i, j) in network:
            del network[(i, j)]

    backtrack(0, {})
    return results


# ── Demand structures ────────────────────────────────────────────────

def generate_demand_structures(k, max_demands_per_type=None):
    """Generate all possible demand structures for k types.

    A demand structure maps each type τ to a set of (R, τ') pairs,
    meaning "type τ requires an R-neighbor of type τ'."

    We also generate ∀-constraints: for each type τ and relation R,
    a set of types that R-neighbors of τ must have.

    For tractability, we parametrize:
    - max_demands_per_type: max number of demands per type (None = all)

    Returns list of (demands, forall_constraints) where:
    - demands[τ] = set of (R, τ') — existential demands
    - forall_constraints[(τ, R)] = set of τ' — allowed types for R-neighbors of τ
    """
    # For now, generate demands directly.
    # Each type can demand any subset of {(R, τ') : R ∈ RELS, τ' ∈ {0..k-1}}
    # This is 4k possible demands per type, 2^(4k) subsets — too many.
    #
    # Instead: we'll parametrize by a smaller set of "interesting" demands.
    # Each type has at most max_demands demands.

    if max_demands_per_type is None:
        max_demands_per_type = 2  # reasonable default

    all_demands = [(R, t) for R in RELS for t in range(k)]

    # Generate demand sets for a single type
    def type_demand_sets():
        result = [frozenset()]  # empty demand set
        for size in range(1, max_demands_per_type + 1):
            for combo in itertools.combinations(all_demands, size):
                result.append(frozenset(combo))
        return result

    single_type_sets = type_demand_sets()

    # All combinations for k types
    for combo in itertools.product(single_type_sets, repeat=k):
        demands = {t: set(combo[t]) for t in range(k)}
        yield demands


def derive_forall_constraints(k, demands):
    """Derive ∀-constraints that are consistent with the demands.

    For ALCI, if type τ has ∃R.C and ∀R.D, then any R-witness for C
    must also satisfy D. We model this as: for each (τ, R), the set of
    allowed target types.

    For simplicity: ∀R.D constrains R-neighbors. We compute the
    allowed target types as those that are compatible with all demands.

    In the simplest model: ∀-constraints are just "any type is allowed"
    (no universal restrictions). This is the pure existential case.

    For a more interesting test, we can add: if type τ demands (R, τ'),
    then τ also has ∀R constraints that are satisfied by τ'.

    For now, return None (= no ∀-constraints, any type allowed via any relation).
    """
    return None


# ── Core check ───────────────────────────────────────────────────────

def check_demand_satisfaction(n, network, tp, demands):
    """Check if every node's every demand is satisfied by some other node.

    Returns (satisfied, failures) where failures is a list of
    (node, demand_R, demand_type) triples that are not satisfied.
    """
    failures = []
    for i in range(n):
        for (R, target_type) in demands.get(tp[i], set()):
            found = False
            for j in range(n):
                if j == i:
                    continue
                if tp[j] == target_type and get_rel(network, i, j) == R:
                    found = True
                    break
            if not found:
                failures.append((i, R, target_type))
    return (len(failures) == 0, failures)


def check_forall_safety(n, network, tp, forall_constraints):
    """Check if all edges respect ∀-constraints.

    forall_constraints[(τ, R)] = set of allowed target types.
    If missing, any type is allowed.
    """
    if forall_constraints is None:
        return True
    for i in range(n):
        for j in range(n):
            if j == i:
                continue
            R = get_rel(network, i, j)
            key = (tp[i], R)
            if key in forall_constraints:
                if tp[j] not in forall_constraints[key]:
                    return False
    return True


# ── Main experiment ──────────────────────────────────────────────────

def run_experiment(n, k, max_demands=2, verbose=True):
    """Run the demand satisfaction experiment.

    For each composition-consistent network on n nodes,
    for each type assignment with k types,
    for each demand structure,
    check if demand satisfaction holds.

    Focus on cases where demands are NOT trivially satisfied
    (i.e., there exist unsatisfied demands to begin with).
    """
    print(f"\n{'='*70}")
    print(f"DEMAND SATISFACTION CHECK: n={n} nodes, k={k} types, "
          f"max {max_demands} demands/type")
    print(f"{'='*70}")

    t0 = time.time()

    # Step 1: enumerate networks
    print(f"\nEnumerating composition-consistent networks on {n} nodes...")
    networks = enumerate_consistent_networks(n)
    print(f"  Found {len(networks)} networks")

    # Step 2: enumerate type assignments (k types, all nodes must be covered)
    # We want surjective assignments (all k types used) for interesting cases
    type_assignments = []
    for assignment in itertools.product(range(k), repeat=n):
        if len(set(assignment)) == k:  # surjective
            type_assignments.append(assignment)
    print(f"  Surjective type assignments: {len(type_assignments)}")

    # Step 3: for each (network, type_assignment), check demands
    # Rather than enumerating all demand structures (too many),
    # we extract the "natural" demands from the graph and check
    # whether EVERY possible demand is already satisfied.

    total_configs = 0
    demand_tested = 0
    failures_found = 0
    failure_examples = []

    # Approach: for each (network, tp), compute what demands CAN be satisfied
    # and what demands CANNOT. A demand (R, τ') for type τ is satisfied at
    # node i (of type τ) if ∃ j≠i with tp[j]=τ' and E(i,j)=R.
    #
    # A demand is "globally unsatisfiable" if there exists a node of type τ
    # where it's not satisfied. This is the interesting case.
    #
    # For the tableau: if the graph is an open completion graph, every
    # non-blocked node has all demands satisfied. A blocked node has the
    # same type as its blocker, so the question is whether the blocked node
    # (which might be in a different relational context) also has the demand
    # satisfied.
    #
    # The STRONG test: for every type τ, every demand (R, τ') of τ,
    # and EVERY node i of type τ, the demand is satisfied at i.
    # (This means the demand holds regardless of where in the graph
    # a node of type τ appears.)

    # For each (network, tp), compute per-type demand satisfaction profiles
    satisfied_count = 0
    partial_count = 0
    unsatisfied_count = 0

    for network in networks:
        for tp in type_assignments:
            total_configs += 1

            # For each type, for each possible demand (R, τ'),
            # check satisfaction at ALL nodes of that type
            type_nodes = defaultdict(list)
            for i in range(n):
                type_nodes[tp[i]].append(i)

            has_interesting_failure = False

            for tau in range(k):
                nodes_of_tau = type_nodes[tau]
                for R in RELS:
                    for tau_prime in range(k):
                        # Can this demand be satisfied at all?
                        # Check each node of type tau
                        sat_nodes = []
                        unsat_nodes = []
                        for i in nodes_of_tau:
                            found = any(
                                tp[j] == tau_prime and get_rel(network, i, j) == R
                                for j in range(n) if j != i
                            )
                            if found:
                                sat_nodes.append(i)
                            else:
                                unsat_nodes.append(i)

                        if sat_nodes and unsat_nodes:
                            # INTERESTING: same demand, same type, but
                            # different nodes have different satisfaction!
                            # This is exactly the problematic case for blocking.
                            has_interesting_failure = True
                            demand_tested += 1
                            failures_found += 1
                            if len(failure_examples) < 20:
                                failure_examples.append({
                                    'network': dict(network),
                                    'tp': tp,
                                    'type': tau,
                                    'demand': (R, tau_prime),
                                    'sat_nodes': sat_nodes,
                                    'unsat_nodes': unsat_nodes,
                                })

            if has_interesting_failure:
                unsatisfied_count += 1
            else:
                satisfied_count += 1

    elapsed = time.time() - t0

    print(f"\nResults (elapsed: {elapsed:.1f}s):")
    print(f"  Total (network, type) configurations: {total_configs}")
    print(f"  All demands uniformly satisfied: {satisfied_count}")
    print(f"  Has non-uniform demand satisfaction: {unsatisfied_count}")
    print(f"  Individual demand failures: {failures_found}")

    if failure_examples:
        print(f"\n  First failure examples (up to 20):")
        for idx, ex in enumerate(failure_examples[:10]):
            print(f"\n  --- Example {idx+1} ---")
            print(f"  Types: {ex['tp']}")
            print(f"  Demand: type {ex['type']} needs "
                  f"{ex['demand'][0]}-neighbor of type {ex['demand'][1]}")
            print(f"  Satisfied at nodes: {ex['sat_nodes']}")
            print(f"  NOT satisfied at nodes: {ex['unsat_nodes']}")
            # Show edges from unsatisfied node
            for i in ex['unsat_nodes'][:1]:
                edges = []
                for j in range(n):
                    if j != i:
                        edges.append(f"  E({i},{j})={get_rel(ex['network'], i, j)}"
                                     f" [type={ex['tp'][j]}]")
                print(f"  Edges from unsat node {i}: " + ", ".join(edges))
            # Show edges from satisfied node for comparison
            for i in ex['sat_nodes'][:1]:
                edges = []
                for j in range(n):
                    if j != i:
                        edges.append(f"  E({i},{j})={get_rel(ex['network'], i, j)}"
                                     f" [type={ex['tp'][j]}]")
                print(f"  Edges from sat node {i}: " + ", ".join(edges))

    return failures_found


def run_focused_experiment(n, k, verbose=True):
    """Focused experiment: only test demands that ARE satisfied somewhere.

    A demand (R, τ') for type τ is "graph-present" if there exist nodes
    a, b with tp[a]=τ, tp[b]=τ', E(a,b)=R in the graph.

    The question: for graph-present demands, is the demand satisfied at
    ALL nodes of type τ, or only at SOME?

    This models the actual tableau scenario: the demand exists because
    some node of type τ was expanded and got an R-successor of type τ'.
    The question is whether a DIFFERENT node of type τ (a blocked node)
    also has this demand satisfied.
    """
    print(f"\n{'='*70}")
    print(f"FOCUSED DEMAND SATISFACTION: n={n} nodes, k={k} types")
    print(f"Only testing demands that are witnessed somewhere in the graph")
    print(f"{'='*70}")

    t0 = time.time()
    networks = enumerate_consistent_networks(n)
    print(f"  Networks: {len(networks)}")

    type_assignments = [
        a for a in itertools.product(range(k), repeat=n)
        if len(set(a)) == k
    ]
    print(f"  Type assignments: {len(type_assignments)}")

    total_configs = 0
    configs_with_failure = 0
    total_demands_tested = 0
    total_demand_failures = 0
    failure_examples = []

    for network in networks:
        for tp in type_assignments:
            total_configs += 1

            type_nodes = defaultdict(list)
            for i in range(n):
                type_nodes[tp[i]].append(i)

            # Extract graph-present demands
            present_demands = set()
            for i in range(n):
                for j in range(n):
                    if j == i:
                        continue
                    R = get_rel(network, i, j)
                    present_demands.add((tp[i], R, tp[j]))

            # For each present demand, check ALL nodes of that type
            config_has_failure = False
            for (tau, R, tau_prime) in present_demands:
                nodes_of_tau = type_nodes[tau]
                if len(nodes_of_tau) <= 1:
                    continue  # only one node of this type, no blocking issue

                total_demands_tested += 1
                all_satisfied = True
                unsat = []
                sat = []
                for i in nodes_of_tau:
                    found = any(
                        tp[j] == tau_prime and get_rel(network, i, j) == R
                        for j in range(n) if j != i
                    )
                    if found:
                        sat.append(i)
                    else:
                        unsat.append(i)
                        all_satisfied = False

                if not all_satisfied and sat:
                    # Some nodes satisfy, some don't — the blocking problem!
                    total_demand_failures += 1
                    config_has_failure = True
                    if len(failure_examples) < 30:
                        failure_examples.append({
                            'network': dict(network),
                            'tp': tp,
                            'n': n,
                            'demand': (tau, R, tau_prime),
                            'sat': sat,
                            'unsat': unsat,
                        })

            if config_has_failure:
                configs_with_failure += 1

    elapsed = time.time() - t0

    print(f"\nResults (elapsed: {elapsed:.1f}s):")
    print(f"  Total configurations: {total_configs}")
    print(f"  Configurations with non-uniform satisfaction: "
          f"{configs_with_failure} "
          f"({100*configs_with_failure/max(total_configs,1):.1f}%)")
    print(f"  Total present demands tested (multi-node types): "
          f"{total_demands_tested}")
    print(f"  Demand failures (sat at some, not all): "
          f"{total_demand_failures} "
          f"({100*total_demand_failures/max(total_demands_tested,1):.1f}%)")

    if failure_examples:
        print(f"\n  === FAILURE ANALYSIS ===")
        # Analyze failure patterns
        fail_rels = defaultdict(int)
        for ex in failure_examples:
            fail_rels[ex['demand'][1]] += 1
        print(f"  Failures by demand relation: {dict(fail_rels)}")

        print(f"\n  First failures:")
        for idx, ex in enumerate(failure_examples[:5]):
            tau, R, tau_prime = ex['demand']
            print(f"\n  --- Failure {idx+1} ---")
            print(f"  n={ex['n']}, types={ex['tp']}")
            print(f"  Demand: type {tau} needs {R}-neighbor of type {tau_prime}")
            print(f"  Satisfied at: {ex['sat']}, NOT at: {ex['unsat']}")

            # Show full edge structure for one sat and one unsat node
            nn = ex['n']
            for label, node in [("UNSAT", ex['unsat'][0]),
                                ("SAT", ex['sat'][0])]:
                edges = []
                for j in range(nn):
                    if j != node:
                        r = get_rel(ex['network'], node, j)
                        edges.append(f"{r}→{j}(t{ex['tp'][j]})")
                print(f"    {label} node {node} (type {ex['tp'][node]}): "
                      f"{', '.join(edges)}")
    else:
        print(f"\n  *** NO FAILURES: all graph-present demands are uniformly "
              f"satisfied! ***")

    return total_demand_failures, failure_examples


def analyze_failure_structure(failure_examples):
    """Analyze whether failures can be resolved by the tableau's structure.

    In the actual tableau:
    1. The ∃-rule creates successors for unsatisfied demands
    2. The CF rule assigns composition-consistent edges to ALL nodes
    3. Blocking only fires when a node has the same TYPE as an ancestor

    Question: can the failures be "repaired" by noting that in a real
    tableau, the graph would have been expanded further?
    """
    if not failure_examples:
        print("\n  No failures to analyze.")
        return

    print(f"\n{'='*70}")
    print(f"FAILURE STRUCTURE ANALYSIS")
    print(f"{'='*70}")

    for idx, ex in enumerate(failure_examples[:10]):
        tau, R, tau_prime = ex['demand']
        n = ex['n']
        tp = ex['tp']
        network = ex['network']

        print(f"\n--- Failure {idx+1}: type {tau} needs {R}→type {tau_prime} ---")

        # For the unsatisfied node, what relations does it have to
        # nodes of type tau_prime?
        for i in ex['unsat']:
            rels_to_target = []
            for j in range(n):
                if j != i and tp[j] == tau_prime:
                    r = get_rel(network, i, j)
                    rels_to_target.append((j, r))

            if not rels_to_target:
                print(f"  Node {i}: no neighbors of type {tau_prime} at all!")
            else:
                print(f"  Node {i}: has type-{tau_prime} neighbors with "
                      f"relations {[(j, r) for j, r in rels_to_target]} "
                      f"(needs {R})")

        # Check: could adding a new node of type tau_prime with
        # edge R to the unsatisfied node be composition-consistent?
        for i in ex['unsat'][:1]:
            print(f"  Can we add new node of type {tau_prime} with "
                  f"E({i},new)={R}?")
            # For each existing node j, what relations are possible
            # for (new, j)?
            possible = True
            for j in range(n):
                if j == i:
                    continue
                r_ij = get_rel(network, i, j)
                # Need: E(new,j) ∈ comp(inv(R), r_ij)
                allowed = COMP.get((INV[R], r_ij), frozenset())
                if not allowed:
                    print(f"    E(new,{j}): IMPOSSIBLE (comp({INV[R]},{r_ij})=∅)")
                    possible = False
                else:
                    print(f"    E(new,{j}): must be in {set(allowed)}")
            if possible:
                print(f"    → Extension IS possible (composition allows it)")
            else:
                print(f"    → Extension IMPOSSIBLE")


if __name__ == '__main__':
    # Start small and scale up
    print("DEMAND SATISFACTION IN RCC5 COMPLETION GRAPHS")
    print("Testing whether blocked nodes' demands are already satisfied")
    print("by existing nodes in the graph.\n")

    # n=3, k=2: smallest interesting case
    run_focused_experiment(3, 2)

    # n=4, k=2
    run_focused_experiment(4, 2)

    # n=4, k=3
    run_focused_experiment(4, 3)

    # n=5, k=2
    f5, ex5 = run_focused_experiment(5, 2)

    # n=5, k=3
    f53, ex53 = run_focused_experiment(5, 3)

    # Analyze failures from the most interesting case
    if ex53:
        analyze_failure_structure(ex53)
    elif ex5:
        analyze_failure_structure(ex5)
    else:
        print("\n\n*** REMARKABLE: NO FAILURES FOUND IN ANY CONFIGURATION! ***")
        print("This would mean the direct demand satisfaction approach works.")
