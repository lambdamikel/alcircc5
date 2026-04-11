#!/usr/bin/env python3
"""
Tableau simulation for ALCI_RCC5 demand satisfaction.

Instead of testing arbitrary composition-consistent graphs (which trivially
fail), simulate the actual Section 7 tableau expansion and test whether
BLOCKED nodes' existential demands are satisfied by existing nodes.

The tableau structure:
  1. Start with a root node of some type
  2. For each unsatisfied ∃R.C demand at an expanded node, create a
     successor with that relation and type
  3. Assign composition-consistent edges between the new node and ALL
     existing nodes (CF rule — nondeterministic)
  4. Block a node if another node with the same type exists
  5. Check: are blocked nodes' demands satisfied?

Key insight: in the tableau, edge assignment (CF) is NONDETERMINISTIC.
We test both:
  (a) Whether SOME edge assignment satisfies all blocked nodes' demands
  (b) Whether ALL edge assignments do (or whether it depends on choices)
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
    if r_ac not in COMP[(r_ab, r_bc)]:
        return False
    if r_ab not in COMP[(r_ac, INV[r_bc])]:
        return False
    if r_bc not in COMP[(INV[r_ab], r_ac)]:
        return False
    return True


# ── Tableau simulation ───────────────────────────────────────────────

class TableauGraph:
    """Simulates a Section 7 tableau completion graph."""

    def __init__(self):
        self.nodes = []        # list of node ids
        self.types = {}        # node -> type
        self.edges = {}        # (i,j) with i<j -> relation
        self.parent = {}       # node -> parent node (None for root)
        self.parent_rel = {}   # node -> relation from parent to this node
        self.expanded = set()  # nodes that have been expanded
        self.blocked = set()   # nodes that are blocked

    def add_node(self, node_type, parent=None, rel=None):
        nid = len(self.nodes)
        self.nodes.append(nid)
        self.types[nid] = node_type
        self.parent[nid] = parent
        self.parent_rel[nid] = rel
        return nid

    def get_rel(self, i, j):
        if i == j:
            return 'EQ'
        key = (min(i, j), max(i, j))
        if key not in self.edges:
            return None
        r = self.edges[key]
        return r if i < j else INV[r]

    def set_rel(self, i, j, r):
        if i == j:
            return
        if i > j:
            r = INV[r]
            i, j = j, i
        self.edges[(i, j)] = r

    def get_possible_rels(self, new_node, existing_node):
        """Get composition-consistent relations for (new_node, existing_node)
        given all other assigned edges."""
        possible = set(RELS)
        for k in self.nodes:
            if k == new_node or k == existing_node:
                continue
            r_nk = self.get_rel(new_node, k)
            r_ek = self.get_rel(existing_node, k)
            if r_nk is not None and r_ek is not None:
                # Triple (new, existing, k): need r_ne ∈ comp(r_nk, inv(r_ek))
                allowed_ne = COMP.get((r_nk, INV[r_ek]), frozenset())
                possible &= allowed_ne
                # Triple (existing, new, k): need r_en ∈ comp(r_ek, inv(r_nk))
                # But r_en = inv(r_ne), so inv(r_ne) ∈ comp(r_ek, inv(r_nk))
                allowed_en = COMP.get((r_ek, INV[r_nk]), frozenset())
                possible &= {r for r in possible if INV[r] in allowed_en}
            elif r_nk is not None:
                pass  # can't constrain without both
            elif r_ek is not None:
                pass
        return possible


def compute_cf_domains(graph, new_node):
    """Compute allowed relations from new_node to each existing node,
    given the parent edge is already set.

    Returns dict: existing_node -> set of allowed relations.
    Uses arc-consistency to prune.
    """
    existing = [n for n in graph.nodes if n != new_node]
    # Initial domains: composition with parent
    parent = graph.parent[new_node]
    parent_rel = graph.parent_rel[new_node]

    domains = {}
    for j in existing:
        if j == parent:
            # Edge to parent is fixed
            domains[j] = frozenset({INV[parent_rel]})
            continue
        # Initial domain from composition with parent
        r_pj = graph.get_rel(parent, j)
        if r_pj is not None:
            # new->j must be in comp(inv(parent_rel), r_pj)
            # because parent->new = parent_rel, parent->j = r_pj
            # Triple (new, parent, j): new->j ∈ comp(new->parent, parent->j)
            #   = comp(inv(parent_rel), r_pj)
            dom = set(COMP[(INV[parent_rel], r_pj)])
        else:
            dom = set(RELS)

        # Also constrain from all other assigned edges
        for k in existing:
            if k == j:
                continue
            r_nk = graph.get_rel(new_node, k)
            r_jk = graph.get_rel(j, k)
            if r_nk is not None and r_jk is not None:
                # Triple (new, j, k): new->j must satisfy composition
                allowed = set()
                for r in dom:
                    if is_triple_consistent(r, graph.get_rel(j, k), r_nk):
                        allowed.add(r)
                dom = allowed
            elif r_jk is not None and domains.get(k) is not None:
                # Can use arc-consistency with domain of k
                pass  # handled in AC loop

        domains[j] = frozenset(dom)

    # Arc-consistency enforcement
    changed = True
    while changed:
        changed = False
        for j in existing:
            if len(domains[j]) <= 1:
                continue
            new_dom = set()
            for rj in domains[j]:
                # Check: for each other node k, is there a consistent
                # assignment for (new, k)?
                ok = True
                for k in existing:
                    if k == j:
                        continue
                    r_jk = graph.get_rel(j, k)
                    if r_jk is None:
                        continue
                    # Triple (new, j, k): need r_nk ∈ comp(rj, r_jk) ∩ domains[k]
                    needed = COMP[(rj, r_jk)]
                    if k in domains and not (needed & domains[k]):
                        ok = False
                        break
                if ok:
                    new_dom.add(rj)
            new_dom = frozenset(new_dom)
            if new_dom != domains[j]:
                domains[j] = new_dom
                changed = True

    return domains


def enumerate_cf_assignments(domains, existing_nodes):
    """Enumerate all valid CF edge assignments from domains.

    Simple backtracking over the Cartesian product filtered by
    domains.  Returns a generator.
    """
    if not existing_nodes:
        yield {}
        return

    nodes = list(existing_nodes)

    def backtrack(idx, assignment):
        if idx == len(nodes):
            yield dict(assignment)
            return
        j = nodes[idx]
        for r in domains.get(j, RELS):
            assignment[j] = r
            yield from backtrack(idx + 1, assignment)
        if j in assignment:
            del assignment[j]

    yield from backtrack(0, {})


# ── Demand structures ────────────────────────────────────────────────

def enumerate_demand_structures(num_types, max_demands_per_type=2):
    """Generate interesting demand structures.

    Each type has demands (R, target_type).
    We limit to at most max_demands per type for tractability.
    """
    all_possible = [(R, t) for R in RELS for t in range(num_types)]

    single_sets = [frozenset()]
    for size in range(1, min(max_demands_per_type + 1, len(all_possible) + 1)):
        for combo in itertools.combinations(all_possible, size):
            single_sets.append(frozenset(combo))

    for combo in itertools.product(single_sets, repeat=num_types):
        # At least one type must have demands
        if any(combo):
            yield {t: set(combo[t]) for t in range(num_types)}


# ── The main experiment ──────────────────────────────────────────────

def simulate_tableau(num_types, demands, max_depth=3):
    """Simulate a minimal tableau expansion.

    Create one node per type (the "expanded" nodes), then for each
    demand, create a successor.  Assign edges via CF.  Then for each
    type τ, create a "blocked" test node and check if its demands
    are satisfied by existing nodes.

    Returns: (can_satisfy_all, details)
    """
    graph = TableauGraph()

    # Phase 1: Create one "seed" node per type
    seed_nodes = {}
    for t in range(num_types):
        nid = graph.add_node(t)
        seed_nodes[t] = nid

    # Assign edges between seed nodes — try all assignments
    # For small num_types, enumerate all composition-consistent assignments
    seed_list = list(range(num_types))
    seed_edges = [(i, j) for i in seed_list for j in seed_list if i < j]

    if not seed_edges:
        # Only 1 type — create seed edges between seed and first successor
        pass

    def enumerate_seed_networks():
        """Enumerate composition-consistent edge assignments for seed nodes."""
        if not seed_edges:
            yield {}
            return

        def backtrack(idx, assignment):
            if idx == len(seed_edges):
                yield dict(assignment)
                return
            i, j = seed_edges[idx]
            for r in RELS:
                assignment[(i, j)] = r
                ok = True
                for k in seed_list:
                    if k == i or k == j:
                        continue
                    ik = (min(i, k), max(i, k))
                    jk = (min(j, k), max(j, k))
                    if ik in assignment and jk in assignment:
                        r_ij = r if i < j else INV[r]
                        r_ik = assignment[ik] if i < k else INV[assignment[ik]]
                        r_jk = assignment[jk] if j < k else INV[assignment[jk]]
                        if not is_triple_consistent(r_ij, r_jk, r_ik):
                            ok = False
                            break
                if ok:
                    yield from backtrack(idx + 1, assignment)
                if (i, j) in assignment:
                    del assignment[(i, j)]

        yield from backtrack(0, {})

    results = {
        'total_networks': 0,
        'some_cf_works': 0,   # ∃ CF assignment where all blocked demands satisfied
        'all_cf_work': 0,     # ∀ CF assignments, all blocked demands satisfied
        'no_cf_works': 0,     # no CF assignment works
        'failure_details': [],
    }

    for seed_network in enumerate_seed_networks():
        results['total_networks'] += 1

        # Set seed edges
        for (i, j), r in seed_network.items():
            graph.edges[(i, j)] = r

        # Phase 2: For each demand, create successors
        # We create successors for ALL seed nodes' demands
        successors = {}  # (parent, R, target_type) -> successor node id
        successor_list = []

        for t in range(num_types):
            parent = seed_nodes[t]
            for (R, target_type) in demands.get(t, set()):
                # Create successor
                nid = graph.add_node(target_type, parent=parent, rel=R)
                # Set edge to parent
                graph.set_rel(parent, nid, R)
                successors[(parent, R, target_type)] = nid
                successor_list.append(nid)

        if not successor_list:
            # No demands — skip
            # Clean up
            graph.nodes = graph.nodes[:num_types]
            for key in list(graph.types.keys()):
                if key >= num_types:
                    del graph.types[key]
            for key in list(graph.parent.keys()):
                if key >= num_types:
                    del graph.parent[key]
                    del graph.parent_rel[key]
            for key in list(graph.edges.keys()):
                if key[0] >= num_types or key[1] >= num_types:
                    del graph.edges[key]
            continue

        # Phase 3: Assign CF edges for each successor to all other nodes
        # This is the nondeterministic part.
        # For tractability, compute domains and check if SOME assignment works.

        # Compute domains for each successor's edges to non-parent nodes
        all_domains = {}  # successor -> {node -> frozenset of rels}
        for s in successor_list:
            parent = graph.parent[s]
            parent_rel = graph.parent_rel[s]
            # Edges to seed nodes (other than parent)
            domains = {}
            for j in seed_list:
                if j == parent:
                    domains[j] = frozenset({INV[parent_rel]})
                    continue
                r_pj = graph.get_rel(parent, j)
                if r_pj is not None:
                    dom = set(COMP[(INV[parent_rel], r_pj)])
                else:
                    dom = set(RELS)
                domains[j] = frozenset(dom)

            # Edges to other successors
            for s2 in successor_list:
                if s2 == s:
                    continue
                if s2 < s:
                    # Already assigned in s2's iteration — skip for now
                    continue
                # Compute domain from known edges
                dom = set(RELS)
                for k in seed_list:
                    r_sk = graph.get_rel(s, k)
                    r_s2k = graph.get_rel(s2, k)
                    if r_sk is not None and r_s2k is not None:
                        allowed = set()
                        for r in dom:
                            if is_triple_consistent(r, graph.get_rel(s2, k) or 'X', r_sk or 'X'):
                                allowed.add(r)
                        dom = allowed
                domains[s2] = frozenset(dom) if dom else frozenset(RELS)

            all_domains[s] = domains

        # For simplicity (since full enumeration is combinatorial),
        # just check if there EXISTS an assignment where blocked demands work.
        # We do this by: for each blocked test scenario, check if the
        # demand relation appears in some domain.

        # Phase 4: Check demand satisfaction for "blocked" nodes
        # A blocked node of type τ would be a new node with the same type
        # as some seed node. It needs all of τ's demands satisfied.
        #
        # The blocked node b (type τ) has edges to all existing nodes.
        # The question: for each demand (R, τ'), is there some node j
        # of type τ' with E(b, j) = R?
        #
        # The blocked node's edges are constrained by its parent edge.
        # But we're testing the general case: can the edges work out?

        # Simpler approach: for each type τ, check if every node of
        # type τ in the (expanded) graph has all of τ's demands satisfied.
        # The seed node trivially does (it was expanded). The successors
        # that happen to have type τ might not.

        # Also: we need to handle the seed-to-successor edges.
        # For now, just check the SEED nodes and hypothetical blocked copies.

        # Check: for each type τ and demand (R, τ'), do all seed nodes
        # of type τ satisfy this? (Only relevant if multiple seeds share type,
        # which only happens if num_types < num_seeds, i.e., never in our setup.)

        # The REAL test: create a hypothetical "blocked" node of type τ,
        # connected to the seed node of type τ via some relation S.
        # Its edges to other nodes are constrained by composition.
        # Does it have its demands satisfied?

        # For each type τ, for each possible relation S to seed[τ]:
        blocked_ok_some = True  # some S works for all demands
        blocked_ok_all = True   # all S work for all demands
        failure_detail = None

        for tau in range(num_types):
            tau_demands = demands.get(tau, set())
            if not tau_demands:
                continue

            seed = seed_nodes[tau]

            # For each possible relation S between blocked node and its blocker
            some_s_works = False
            for S in RELS:
                # Blocked node b has: E(b, seed[τ]) = S
                # For each other seed node j (type τ_j):
                #   E(b, j) ∈ comp(S, E(seed[τ], j))
                # For each successor s (created by seed c with rel R_cs):
                #   E(b, s) depends on E(b, c) and E(c, s)

                # Compute domains for b's edges to all existing nodes
                b_domains = {}
                b_domains[seed] = frozenset({S})

                for j in seed_list:
                    if j == seed:
                        continue
                    r_seed_j = graph.get_rel(seed, j)
                    if r_seed_j is not None:
                        b_domains[j] = frozenset(COMP[(S, r_seed_j)])
                    else:
                        b_domains[j] = frozenset(RELS)

                # Domains for successor nodes
                for s in successor_list:
                    p = graph.parent[s]
                    p_rel = graph.parent_rel[s]
                    # E(b, s): need to be in comp(E(b,p), E(p,s))
                    #   = comp(E(b,p), p_rel)
                    b_to_p = b_domains.get(p)
                    if b_to_p is not None:
                        dom = set()
                        for bp in b_to_p:
                            dom |= COMP[(bp, p_rel)]
                        b_domains[s] = frozenset(dom)
                    else:
                        b_domains[s] = frozenset(RELS)

                # Arc-consistency with triangle constraints
                all_nodes_in_graph = seed_list + successor_list
                changed = True
                iterations = 0
                while changed and iterations < 20:
                    changed = False
                    iterations += 1
                    for j in all_nodes_in_graph:
                        if len(b_domains.get(j, frozenset())) <= 1:
                            continue
                        new_dom = set()
                        for rj in b_domains[j]:
                            ok = True
                            for k in all_nodes_in_graph:
                                if k == j:
                                    continue
                                r_jk = graph.get_rel(j, k)
                                if r_jk is None:
                                    continue
                                # Triple (b, j, k): b->k ∈ comp(rj, r_jk)
                                needed = COMP[(rj, r_jk)]
                                if k in b_domains and not (needed & b_domains[k]):
                                    ok = False
                                    break
                            if ok:
                                new_dom.add(rj)
                        new_dom = frozenset(new_dom)
                        if new_dom != b_domains.get(j, frozenset()):
                            b_domains[j] = new_dom
                            changed = True

                # Check: for each demand (R, τ'), is there some node j
                # with type[j] = τ' and R ∈ b_domains[j]?
                all_demands_sat = True
                for (R, target_type) in tau_demands:
                    found = False
                    for j in all_nodes_in_graph:
                        if graph.types[j] == target_type and R in b_domains.get(j, frozenset()):
                            found = True
                            break
                    if not found:
                        all_demands_sat = False
                        if failure_detail is None:
                            failure_detail = {
                                'type': tau,
                                'blocker_rel': S,
                                'demand': (R, target_type),
                                'b_domains': {j: set(b_domains.get(j, frozenset())) for j in all_nodes_in_graph},
                                'types': {j: graph.types[j] for j in all_nodes_in_graph},
                                'seed_edges': dict(seed_network),
                            }
                        break

                if all_demands_sat:
                    some_s_works = True
                else:
                    blocked_ok_all = False

            if not some_s_works:
                blocked_ok_some = False

        if blocked_ok_some:
            results['some_cf_works'] += 1
        else:
            results['no_cf_works'] += 1
            if failure_detail and len(results['failure_details']) < 10:
                results['failure_details'].append(failure_detail)

        if blocked_ok_all:
            results['all_cf_work'] += 1

        # Clean up: remove successors
        graph.nodes = graph.nodes[:num_types]
        for key in list(graph.types.keys()):
            if key >= num_types:
                del graph.types[key]
        for key in list(graph.parent.keys()):
            if key >= num_types:
                del graph.parent[key]
                del graph.parent_rel[key]
        for key in list(graph.edges.keys()):
            if key[0] >= num_types or key[1] >= num_types:
                del graph.edges[key]

    return results


def run_experiment(num_types, max_demands_per_type=2):
    """Run the tableau demand satisfaction experiment."""
    print(f"\n{'='*70}")
    print(f"TABLEAU DEMAND SATISFACTION: {num_types} types, "
          f"max {max_demands_per_type} demands/type")
    print(f"{'='*70}")

    t0 = time.time()

    total_structures = 0
    total_networks = 0
    any_genuine_failure = False
    all_failure_details = []

    for demands in enumerate_demand_structures(num_types, max_demands_per_type):
        total_structures += 1
        if total_structures % 500 == 0:
            print(f"  ... processed {total_structures} demand structures "
                  f"({time.time()-t0:.1f}s)")

        results = simulate_tableau(num_types, demands)
        total_networks += results['total_networks']

        if results['no_cf_works'] > 0:
            any_genuine_failure = True
            for fd in results['failure_details']:
                fd['demands'] = demands
            all_failure_details.extend(results['failure_details'])

    elapsed = time.time() - t0

    print(f"\nResults ({elapsed:.1f}s):")
    print(f"  Demand structures tested: {total_structures}")
    print(f"  Total (structure × network) configs: {total_networks}")

    if any_genuine_failure:
        print(f"\n  *** FAILURES FOUND: {len(all_failure_details)} examples ***")
        for idx, fd in enumerate(all_failure_details[:5]):
            print(f"\n  --- Failure {idx+1} ---")
            print(f"  Demands: {fd['demands']}")
            print(f"  Seed edges: {fd['seed_edges']}")
            print(f"  Failed type: {fd['type']}, "
                  f"blocker rel: {fd['blocker_rel']}")
            print(f"  Unsatisfied demand: {fd['demand']}")
            print(f"  Node types: {fd['types']}")
            print(f"  Blocked node domains:")
            for j, dom in sorted(fd['b_domains'].items()):
                print(f"    to node {j} (type {fd['types'].get(j,'?')}): {dom}")
    else:
        print(f"\n  *** NO FAILURES: for every demand structure and "
              f"every seed network,")
        print(f"      there exists a blocker-relation S such that "
              f"all blocked demands are satisfiable! ***")

    return any_genuine_failure, all_failure_details


def run_strict_experiment(num_types, max_demands_per_type=2):
    """Strict version: the blocked node's relation to its blocker is
    determined by the WITNESS RELATION (the edge from the blocker's
    parent to the blocker).

    In a real tableau, a blocked node b is a child of some node p
    via relation R. b is blocked by node a (same type). The edge
    E(a, b) was assigned by CF when b was created. We don't get to
    choose it — it's part of the graph.

    However, we CAN choose: which node blocks b. If there are multiple
    nodes of the same type, we pick one whose relation to b makes
    demands satisfiable.

    For this experiment: the blocked node is a child of seed[τ_parent]
    via relation R_parent, and has type τ. It's blocked by seed[τ].
    E(blocked, seed[τ]) is determined by composition:
    E(blocked, seed[τ]) ∈ comp(inv(R_parent), E(seed[τ_parent], seed[τ]))
    """
    print(f"\n{'='*70}")
    print(f"STRICT TABLEAU DEMAND SATISFACTION: {num_types} types, "
          f"max {max_demands_per_type} demands/type")
    print(f"Blocked node created as child, relation to blocker from CF")
    print(f"{'='*70}")

    t0 = time.time()

    total_scenarios = 0
    failure_scenarios = 0
    all_failures = []

    for demands in enumerate_demand_structures(num_types, max_demands_per_type):
        # For each seed network
        seed_list = list(range(num_types))
        seed_edges = [(i, j) for i in seed_list for j in seed_list if i < j]

        def enum_seed_nets():
            if not seed_edges:
                yield {}
                return
            def bt(idx, asgn):
                if idx == len(seed_edges):
                    yield dict(asgn)
                    return
                i, j = seed_edges[idx]
                for r in RELS:
                    asgn[(i, j)] = r
                    ok = True
                    for k in seed_list:
                        if k == i or k == j: continue
                        ik = (min(i,k), max(i,k))
                        jk = (min(j,k), max(j,k))
                        if ik in asgn and jk in asgn:
                            r_ij = r
                            r_ik = asgn[ik] if i < k else INV[asgn[(k,i) if (k,i) in asgn else (i,k)]]
                            r_jk = asgn[jk] if j < k else INV[asgn[(k,j) if (k,j) in asgn else (j,k)]]
                            if not is_triple_consistent(r_ij, r_jk, r_ik):
                                ok = False
                                break
                    if ok:
                        yield from bt(idx + 1, asgn)
                    if (i, j) in asgn:
                        del asgn[(i, j)]
            yield from bt(0, {})

        def get_seed_rel(network, i, j):
            if i == j: return 'EQ'
            key = (min(i,j), max(i,j))
            r = network[key]
            return r if i < j else INV[r]

        for seed_net in enum_seed_nets():
            # For each type τ with demands, simulate blocking
            for tau in range(num_types):
                tau_demands = demands.get(tau, set())
                if not tau_demands:
                    continue

                # The blocked node could be a child of any type via any demand
                # For each (parent_type, R_parent) that produces type τ
                for parent_type in range(num_types):
                    for R_parent in RELS:
                        # Only relevant if this is actually a demand
                        if (R_parent, tau) not in demands.get(parent_type, set()):
                            continue

                        total_scenarios += 1

                        parent_node = parent_type  # seed node index
                        blocker = tau  # seed node of type τ

                        if parent_node == blocker:
                            # Parent IS the blocker: E(blocked, blocker) = inv(R_parent)
                            possible_blocker_rels = frozenset({INV[R_parent]})
                        else:
                            # E(blocked, blocker) ∈ comp(inv(R_parent),
                            #                            E(parent, blocker))
                            r_parent_blocker = get_seed_rel(seed_net, parent_node, blocker)
                            possible_blocker_rels = COMP[(INV[R_parent], r_parent_blocker)]

                        # For each possible E(blocked, blocker):
                        any_works = False
                        for S in possible_blocker_rels:
                            # Compute b's domains to all nodes
                            b_domains = {}
                            b_domains[blocker] = frozenset({S})
                            b_domains[parent_node] = frozenset({INV[R_parent]})

                            for j in seed_list:
                                if j == blocker or j == parent_node:
                                    continue
                                # From blocker: E(b,j) ∈ comp(S, E(blocker,j))
                                r_bj = get_seed_rel(seed_net, blocker, j)
                                dom1 = COMP[(S, r_bj)]
                                # From parent: E(b,j) ∈ comp(inv(R_parent), E(parent,j))
                                r_pj = get_seed_rel(seed_net, parent_node, j)
                                dom2 = COMP[(INV[R_parent], r_pj)]
                                b_domains[j] = dom1 & dom2

                            # Also compute domains for successor nodes
                            # Seed node c's R_c-successor has type t_c
                            succ_info = []  # (parent_seed, R, target_type, succ_id)
                            sid = num_types
                            for c in seed_list:
                                for (Rc, tc) in demands.get(c, set()):
                                    succ_info.append((c, Rc, tc, sid))
                                    sid += 1

                            succ_types = {}
                            for (c, Rc, tc, sid_val) in succ_info:
                                succ_types[sid_val] = tc

                            for (c, Rc, tc, sid_val) in succ_info:
                                # E(b, succ) where succ is c's Rc-successor
                                # E(b, c) is in b_domains[c]
                                # E(c, succ) = Rc
                                if c in b_domains:
                                    dom = set()
                                    for bc in b_domains[c]:
                                        dom |= COMP[(bc, Rc)]
                                    b_domains[sid_val] = frozenset(dom)
                                else:
                                    b_domains[sid_val] = frozenset(RELS)

                            # Check demands
                            all_sat = True
                            for (R_dem, target_type) in tau_demands:
                                found = False
                                # Check seed nodes
                                for j in seed_list:
                                    if j == parent_node and tau == parent_type:
                                        continue  # b itself? no, b is different
                                    if j != blocker and get_seed_rel(seed_net, j, j) == 'EQ':
                                        pass  # seed nodes are distinct
                                    t_j = j  # type of seed node j = j
                                    if t_j == target_type and R_dem in b_domains.get(j, frozenset()):
                                        found = True
                                        break
                                # Check successor nodes
                                if not found:
                                    for (c, Rc, tc, sid_val) in succ_info:
                                        if tc == target_type and R_dem in b_domains.get(sid_val, frozenset()):
                                            found = True
                                            break
                                if not found:
                                    all_sat = False
                                    break

                            if all_sat:
                                any_works = True
                                break

                        if not any_works:
                            failure_scenarios += 1
                            if len(all_failures) < 10:
                                all_failures.append({
                                    'demands': {t: set(demands[t]) for t in demands},
                                    'seed_net': dict(seed_net),
                                    'blocked_type': tau,
                                    'parent_type': parent_type,
                                    'parent_rel': R_parent,
                                    'possible_blocker_rels': set(possible_blocker_rels),
                                    'unsat_demands': list(tau_demands),
                                })

    elapsed = time.time() - t0
    print(f"\nResults ({elapsed:.1f}s):")
    print(f"  Total blocking scenarios: {total_scenarios}")
    print(f"  Failure scenarios: {failure_scenarios} "
          f"({100*failure_scenarios/max(total_scenarios,1):.1f}%)")

    if all_failures:
        print(f"\n  === FAILURE EXAMPLES ===")
        for idx, f in enumerate(all_failures[:5]):
            print(f"\n  --- Failure {idx+1} ---")
            print(f"  Demands: {f['demands']}")
            print(f"  Seed network: {f['seed_net']}")
            print(f"  Blocked type {f['blocked_type']} "
                  f"(child of type {f['parent_type']} via {f['parent_rel']})")
            print(f"  Possible E(blocked, blocker): {f['possible_blocker_rels']}")
            print(f"  Unsatisfied demands: {f['unsat_demands']}")
    else:
        print(f"\n  *** NO FAILURES! All blocked demands can be satisfied. ***")

    return failure_scenarios, all_failures


if __name__ == '__main__':
    print("TABLEAU DEMAND SATISFACTION EXPERIMENT")
    print("Simulating actual tableau structure (expanded nodes + successors)")
    print()

    # Test with 2 types first
    print("\n" + "="*70)
    print("PHASE 1: Basic experiment (any blocker relation)")
    print("="*70)
    run_experiment(2, max_demands_per_type=2)

    # Strict experiment: blocker relation determined by CF
    print("\n" + "="*70)
    print("PHASE 2: Strict experiment (blocker relation from CF)")
    print("="*70)
    run_strict_experiment(2, max_demands_per_type=2)

    print("\n" + "="*70)
    print("PHASE 3: 3 types, strict (may be slow)")
    print("="*70)
    run_strict_experiment(3, max_demands_per_type=1)
