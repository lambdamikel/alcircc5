#!/usr/bin/env python3
"""
Depth-2 demand satisfaction check.

Key finding from tableau_demand_check.py:
  - Phase 1 (free blocker relation): ZERO failures
  - Phase 2 (CF-forced blocker relation): 1.7% failures, ALL involving
    DR parent → DR blocker → unsatisfied PPI demand

This script tests: if we DON'T block the stuck node and instead expand
it one more level, does the NEXT generation satisfy all demands?

The scenario:
  1. Seed nodes: one per type, with demands
  2. Level 1: successors of seeds (expand all demands)
  3. A level-1 node of type τ is "stuck" if its demands aren't satisfied
  4. Expand the stuck node: create level-2 successors
  5. Check: are level-2 nodes' demands satisfied? (by ANY node in the graph)

If yes → the tableau just needs one more level before blocking works.
"""

import itertools
import time
from collections import defaultdict

# ── RCC5 ─────────────────────────────────────────────────────────────

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


# ── Helpers ──────────────────────────────────────────────────────────

def enum_seed_networks(num_types):
    """Enumerate composition-consistent networks on seed nodes."""
    seeds = list(range(num_types))
    edges = [(i, j) for i in seeds for j in seeds if i < j]
    if not edges:
        yield {}
        return

    def get_rel(net, i, j):
        if i < j: return net[(i,j)]
        return INV[net[(j,i)]]

    def bt(idx, asgn):
        if idx == len(edges):
            yield dict(asgn)
            return
        i, j = edges[idx]
        for r in RELS:
            asgn[(i,j)] = r
            ok = True
            for k in seeds:
                if k == i or k == j: continue
                ik, jk = (min(i,k),max(i,k)), (min(j,k),max(j,k))
                if ik in asgn and jk in asgn:
                    r_ij = r
                    r_ik = get_rel(asgn, i, k)
                    r_jk = get_rel(asgn, j, k)
                    if not is_triple_consistent(r_ij, r_jk, r_ik):
                        ok = False; break
            if ok:
                yield from bt(idx+1, asgn)
            if (i,j) in asgn: del asgn[(i,j)]
    yield from bt(0, {})


def enum_demand_structures(num_types, max_per_type=2):
    all_demands = [(R, t) for R in RELS for t in range(num_types)]
    single = [frozenset()]
    for sz in range(1, min(max_per_type+1, len(all_demands)+1)):
        for c in itertools.combinations(all_demands, sz):
            single.append(frozenset(c))
    for combo in itertools.product(single, repeat=num_types):
        if any(combo):
            yield {t: set(combo[t]) for t in range(num_types)}


# ── Main check ───────────────────────────────────────────────────────

def check_depth2(num_types, max_demands=2):
    """For each (demands, seed_network), simulate 2-level expansion
    and check if all second-level blocked nodes have demands satisfied."""

    print(f"\n{'='*70}")
    print(f"DEPTH-2 DEMAND CHECK: {num_types} types, max {max_demands} demands/type")
    print(f"{'='*70}")

    t0 = time.time()
    total_scenarios = 0
    stuck_at_level1 = 0
    resolved_at_level2 = 0
    still_stuck_at_level2 = 0
    failure_details = []

    for demands in enum_demand_structures(num_types, max_demands):
        for seed_net in enum_seed_networks(num_types):

            def get_seed_rel(i, j):
                if i == j: return 'EQ'
                key = (min(i,j), max(i,j))
                r = seed_net[key]
                return r if i < j else INV[r]

            # Build the graph: seeds + level-1 successors
            # Each seed s (type s) has successors for demands[s]
            # Level-1 node: (parent_seed, R_demand, target_type)
            level1 = []
            for s in range(num_types):
                for (R, t) in demands.get(s, set()):
                    level1.append((s, R, t))

            if not level1:
                continue

            # For each type τ, check if a level-1 node of type τ
            # (created as R-child of some seed) has its demands satisfied.

            for l1_idx, (parent, R_parent, l1_type) in enumerate(level1):
                l1_demands = demands.get(l1_type, set())
                if not l1_demands:
                    continue

                total_scenarios += 1

                # The level-1 node b: E(b, parent) = inv(R_parent)
                # E(b, blocker=seed[l1_type]):
                if parent == l1_type:
                    # parent IS the blocker
                    S_blocker = INV[R_parent]
                else:
                    r_parent_blocker = get_seed_rel(parent, l1_type)
                    # E(b, blocker) ∈ comp(inv(R_parent), r_parent_blocker)
                    possible_S = COMP[(INV[R_parent], r_parent_blocker)]
                    # For each possible S, check demands. Take the BEST case.
                    S_blocker = None  # will try all

                # Compute b's domains to all graph nodes, for each S
                def check_with_blocker_rel(S):
                    """Check if b's demands are satisfied given E(b,blocker)=S."""
                    blocker = l1_type

                    # b's domains to seeds
                    b_to_seed = {}
                    b_to_seed[parent] = frozenset({INV[R_parent]})
                    if blocker != parent:
                        b_to_seed[blocker] = frozenset({S})

                    for j in range(num_types):
                        if j in b_to_seed:
                            continue
                        # From parent: comp(inv(R_parent), E(parent, j))
                        dom1 = COMP[(INV[R_parent], get_seed_rel(parent, j))]
                        # From blocker: comp(S, E(blocker, j))
                        dom2 = COMP[(S, get_seed_rel(blocker, j))]
                        b_to_seed[j] = dom1 & dom2

                    # b's domains to level-1 successors
                    b_to_l1 = {}
                    for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                        if l1j_idx == l1_idx:
                            continue  # skip self
                        # E(b, l1j): l1j is Rj-child of seed pj
                        # E(b, pj) known, E(pj, l1j) = Rj
                        if pj in b_to_seed:
                            dom = set()
                            for bp in b_to_seed[pj]:
                                dom |= COMP[(bp, Rj)]
                            b_to_l1[l1j_idx] = frozenset(dom)
                        else:
                            b_to_l1[l1j_idx] = frozenset(RELS)

                    # Check each demand
                    unsat = []
                    for (R_dem, target_type) in l1_demands:
                        found = False
                        # Check seeds
                        for j in range(num_types):
                            if j == target_type and R_dem in b_to_seed.get(j, frozenset()):
                                found = True; break
                        # Check level-1 nodes
                        if not found:
                            for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                                if l1j_idx == l1_idx: continue
                                if tj == target_type and R_dem in b_to_l1.get(l1j_idx, frozenset()):
                                    found = True; break
                        if not found:
                            unsat.append((R_dem, target_type))
                    return unsat

                # Try all possible blocker relations
                if S_blocker is not None:
                    possible_S_set = [S_blocker]
                else:
                    possible_S_set = list(possible_S)

                best_unsat = None
                for S in possible_S_set:
                    unsat = check_with_blocker_rel(S)
                    if not unsat:
                        best_unsat = []
                        break
                    if best_unsat is None or len(unsat) < len(best_unsat):
                        best_unsat = unsat
                        best_S = S

                if best_unsat:
                    # Level 1 is stuck! Now expand b and check level 2.
                    stuck_at_level1 += 1

                    # Expand b: for each demand of l1_type, create level-2 successor
                    # Level-2 node: b's R_dem-child of type target_type
                    # Then check: do level-2 nodes of the SAME type as b have
                    # THEIR demands satisfied?

                    # Actually, the key question: when we expand b and create
                    # b's successors, do those successors (when they share a
                    # type with some seed) have their demands satisfied?

                    # b creates successors for its own demands.
                    # b's DR-successor d2 has type l1_type (same as b!).
                    # d2 is blocked by seed[l1_type].
                    # E(d2, b) = inv(R_for_that_demand).
                    # E(d2, blocker) depends on E(d2, b) and E(b, blocker).

                    # For each demand of l1_type that produces type l1_type
                    # (self-referential demands like DR→self):
                    level2_resolved = False

                    for (R_l2, t_l2) in l1_demands:
                        # d2 is R_l2-child of b, type t_l2
                        t2_demands = demands.get(t_l2, set())
                        if not t2_demands:
                            continue

                        # E(d2, b) = inv(R_l2)
                        # E(d2, seed[j]) depends on E(d2, b) and E(b, seed[j])

                        # Try all blocker rels for b (from the stuck scenario)
                        for S in possible_S_set:
                            b_to_seed_local = {}
                            b_to_seed_local[parent] = frozenset({INV[R_parent]})
                            blocker = l1_type
                            if blocker != parent:
                                b_to_seed_local[blocker] = frozenset({S})
                            for j in range(num_types):
                                if j in b_to_seed_local: continue
                                dom1 = COMP[(INV[R_parent], get_seed_rel(parent, j))]
                                dom2 = COMP[(S, get_seed_rel(blocker, j))]
                                b_to_seed_local[j] = dom1 & dom2

                            # d2's domains to seeds
                            d2_to_seed = {}
                            for j in range(num_types):
                                # E(d2, j) via b: comp(inv(R_l2), E(b,j))
                                dom = set()
                                for bj in b_to_seed_local.get(j, frozenset(RELS)):
                                    dom |= COMP[(INV[R_l2], bj)]
                                d2_to_seed[j] = frozenset(dom)

                            # d2's domains to level-1 nodes
                            d2_to_l1 = {}
                            for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                                # E(d2, l1j) via seed pj: comp(E(d2,pj), Rj)
                                dom = set()
                                for dp in d2_to_seed.get(pj, frozenset(RELS)):
                                    dom |= COMP[(dp, Rj)]
                                d2_to_l1[l1j_idx] = frozenset(dom)

                            # d2's domain to b itself
                            d2_to_b = frozenset({INV[R_l2]})

                            # d2's domains to OTHER level-2 nodes (b's other successors)
                            # For simplicity, compute domain to b's successors via b
                            d2_to_b_succs = {}
                            for (R_other, t_other) in l1_demands:
                                if (R_other, t_other) == (R_l2, t_l2):
                                    continue
                                # b's R_other-successor s: E(d2,s) via b
                                # E(d2,b) = inv(R_l2), E(b,s) = R_other
                                dom = COMP[(INV[R_l2], R_other)]
                                d2_to_b_succs[(R_other, t_other)] = dom

                            # Check d2's demands
                            all_d2_sat = True
                            for (R_dem, target_type) in t2_demands:
                                found = False
                                # Seeds
                                for j in range(num_types):
                                    if j == target_type and R_dem in d2_to_seed.get(j, frozenset()):
                                        found = True; break
                                # Level-1 nodes
                                if not found:
                                    for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                                        if tj == target_type and R_dem in d2_to_l1.get(l1j_idx, frozenset()):
                                            found = True; break
                                # b itself
                                if not found:
                                    if l1_type == target_type and R_dem in d2_to_b:
                                        found = True
                                # b's other successors
                                if not found:
                                    for (R_other, t_other), dom in d2_to_b_succs.items():
                                        if t_other == target_type and R_dem in dom:
                                            found = True; break
                                if not found:
                                    all_d2_sat = False
                                    break

                            if all_d2_sat:
                                level2_resolved = True
                                break
                        if level2_resolved:
                            break

                    if level2_resolved:
                        resolved_at_level2 += 1
                    else:
                        still_stuck_at_level2 += 1
                        if len(failure_details) < 10:
                            failure_details.append({
                                'demands': {t: set(demands[t]) for t in demands},
                                'seed_net': dict(seed_net),
                                'l1_type': l1_type,
                                'l1_parent': parent,
                                'l1_parent_rel': R_parent,
                                'unsat_demands': best_unsat,
                            })

    elapsed = time.time() - t0
    print(f"\nResults ({elapsed:.1f}s):")
    print(f"  Total level-1 blocking scenarios: {total_scenarios}")
    print(f"  Stuck at level 1: {stuck_at_level1} "
          f"({100*stuck_at_level1/max(total_scenarios,1):.1f}%)")
    print(f"  Resolved by level-2 expansion: {resolved_at_level2} "
          f"({100*resolved_at_level2/max(stuck_at_level1,1):.1f}% of stuck)")
    print(f"  STILL STUCK at level 2: {still_stuck_at_level2} "
          f"({100*still_stuck_at_level2/max(total_scenarios,1):.1f}%)")

    if failure_details:
        print(f"\n  === LEVEL-2 FAILURE EXAMPLES ===")
        for idx, f in enumerate(failure_details[:5]):
            print(f"\n  --- Failure {idx+1} ---")
            print(f"  Demands: {f['demands']}")
            print(f"  Seed net: {f['seed_net']}")
            print(f"  L1 node: type {f['l1_type']}, child of type {f['l1_parent']} "
                  f"via {f['l1_parent_rel']}")
            print(f"  Unsatisfied: {f['unsat_demands']}")
    elif stuck_at_level1 > 0:
        print(f"\n  *** ALL level-1 stuck cases RESOLVED at level 2! ***")
    else:
        print(f"\n  *** No stuck cases at level 1 either! ***")

    return still_stuck_at_level2, failure_details


# ── Also check: what if we just expand the stuck demand? ─────────────

def check_targeted_expansion(num_types, max_demands=2):
    """Instead of expanding ALL of b's demands at level 2, just expand
    the STUCK demand (PPI).

    The stuck node b needs PPI→τ'. b creates PPI-successor e (type τ').
    e has edges to all existing nodes. Question: does EVERYTHING work now?

    Key: E(e, seed[j]) via b. E(e,b) = PP (inv of PPI), E(b,seed[j]) = ...
    So E(e,j) ∈ comp(PP, E(b,j)).

    For the BLOCKER (b blocked by seed[τ]):
    E(e, blocker) ∈ comp(PP, S_blocker).

    If S_blocker = DR: comp(PP, DR) = {DR}. So E(e, blocker) = DR.
    The blocker has type τ (same as b). So e's edge to blocker is DR.

    Now e (type τ') needs its own demands satisfied. If τ' also needs
    PPI→some_type, and e is DR to seed[some_type]... could cascade.

    But usually τ' ≠ τ, so different demands.
    """
    print(f"\n{'='*70}")
    print(f"TARGETED PPI EXPANSION CHECK: {num_types} types, "
          f"max {max_demands} demands/type")
    print(f"When b is stuck on PPI demand, expand just that demand.")
    print(f"Check: does the PPI-successor satisfy ITS demands?")
    print(f"{'='*70}")

    t0 = time.time()
    total = 0
    stuck = 0
    resolved = 0
    still_stuck = 0

    for demands in enum_demand_structures(num_types, max_demands):
        for seed_net in enum_seed_networks(num_types):
            def get_seed_rel(i, j):
                if i == j: return 'EQ'
                key = (min(i,j), max(i,j))
                r = seed_net[key]
                return r if i < j else INV[r]

            # Level-1 successors
            level1 = []
            for s in range(num_types):
                for (R, t) in demands.get(s, set()):
                    level1.append((s, R, t))

            if not level1:
                continue

            for l1_idx, (par, R_par, l1_type) in enumerate(level1):
                l1_demands = demands.get(l1_type, set())
                ppi_demands = [(R, t) for R, t in l1_demands if R == PPI]
                if not ppi_demands:
                    continue

                total += 1

                # Blocker relation
                blocker = l1_type
                if par == blocker:
                    S = INV[R_par]
                else:
                    r_pb = get_seed_rel(par, blocker)
                    possible_S = list(COMP[(INV[R_par], r_pb)])
                    # Check each S
                    S = None
                    for s_try in possible_S:
                        if s_try != DR:
                            S = s_try; break
                    if S is None:
                        S = DR

                if S != DR:
                    continue  # non-DR blocker — PPI demand likely satisfied
                              # (only DR causes the self-absorption failure)

                stuck += 1

                # b is stuck: E(b, blocker) = DR, PPI demand unsatisfied.
                # Expand b's PPI demand: create e (type t_ppi) as PPI-child of b.
                # E(e, b) = PP.
                # E(e, seed[j]) ∈ comp(PP, E(b, seed[j]))

                # First compute E(b, seed[j])
                b_to_seed = {}
                b_to_seed[par] = frozenset({INV[R_par]})
                if blocker != par:
                    b_to_seed[blocker] = frozenset({DR})
                for j in range(num_types):
                    if j in b_to_seed: continue
                    dom1 = COMP[(INV[R_par], get_seed_rel(par, j))]
                    dom2 = COMP[(DR, get_seed_rel(blocker, j))]
                    b_to_seed[j] = dom1 & dom2

                for (_, t_ppi) in ppi_demands:
                    # e is PPI-child of b, type t_ppi
                    # E(e, b) = PP
                    e_demands = demands.get(t_ppi, set())
                    if not e_demands:
                        resolved += 1
                        continue

                    # e's domains to seeds
                    e_to_seed = {}
                    for j in range(num_types):
                        dom = set()
                        for bj in b_to_seed.get(j, frozenset(RELS)):
                            dom |= COMP[(PP, bj)]
                        e_to_seed[j] = frozenset(dom)

                    # e's domains to level-1 nodes (via their parent seeds)
                    e_to_l1 = {}
                    for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                        if l1j_idx == l1_idx: continue
                        dom = set()
                        for ep in e_to_seed.get(pj, frozenset(RELS)):
                            dom |= COMP[(ep, Rj)]
                        e_to_l1[l1j_idx] = frozenset(dom)

                    # Check e's demands
                    all_sat = True
                    unsat_list = []
                    for (R_dem, target_type) in e_demands:
                        found = False
                        for j in range(num_types):
                            if j == target_type and R_dem in e_to_seed.get(j, frozenset()):
                                found = True; break
                        if not found:
                            for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                                if l1j_idx == l1_idx: continue
                                if tj == target_type and R_dem in e_to_l1.get(l1j_idx, frozenset()):
                                    found = True; break
                        if not found:
                            # Also check: b itself as a neighbor of e
                            if l1_type == target_type and R_dem == PP:
                                found = True  # E(e,b) = PP
                        if not found:
                            all_sat = False
                            unsat_list.append((R_dem, target_type))

                    if all_sat:
                        resolved += 1
                    else:
                        still_stuck += 1
                        if still_stuck <= 5:
                            print(f"\n  Level-2 PPI-successor stuck!")
                            print(f"  Demands: {demands}")
                            print(f"  Seed net: {dict(seed_net)}")
                            print(f"  b: type {l1_type}, DR-child of type {par}")
                            print(f"  e: type {t_ppi}, PPI-child of b")
                            print(f"  e's unsat demands: {unsat_list}")
                            print(f"  e to seeds: {dict(e_to_seed)}")

    elapsed = time.time() - t0
    print(f"\nResults ({elapsed:.1f}s):")
    print(f"  Total PPI-demand scenarios: {total}")
    print(f"  Stuck (DR blocker, PPI demand): {stuck}")
    print(f"  Resolved by PPI-expansion: {resolved}")
    print(f"  Still stuck after expansion: {still_stuck}")

    if still_stuck == 0 and stuck > 0:
        print(f"\n  *** ALL PPI-stuck cases resolved by one expansion! ***")

    return still_stuck


if __name__ == '__main__':
    print("DEPTH-2 DEMAND SATISFACTION ANALYSIS")
    print("Testing whether one extra expansion resolves DR→PPI stuck cases")

    # 2 types
    check_depth2(2, max_demands=2)

    # Targeted PPI check
    check_targeted_expansion(2, max_demands=2)

    # 3 types
    print("\n\n--- 3 TYPES ---")
    check_depth2(3, max_demands=1)
    check_targeted_expansion(3, max_demands=1)
