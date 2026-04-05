#!/usr/bin/env python3
"""
Comprehensive demand satisfaction check — fixes bugs and classifies failures.

Key findings so far:
  - Phase 1 (free blocker rel): ZERO failures
  - Phase 2 (CF-forced): 1.7% failures, all DR→PPI self-absorption
  - Depth 2: 99.4-99.9% resolve, remaining are PPI cascades

This script:
  1. Fixes the depth-2 bug (empty-demand successors should count as resolved)
  2. Classifies ALL remaining failures: self-referential PPI or other?
  3. Tests the key claim: the ONLY irreducible obstruction is ∃PPI.self-type
  4. Tests larger structures (multiple nodes per type) for completeness
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
    seeds = list(range(num_types))
    edges = [(i, j) for i in seeds for j in seeds if i < j]
    if not edges:
        yield {}
        return

    def get_rel(net, i, j):
        if i < j: return net[(i, j)]
        return INV[net[(j, i)]]

    def bt(idx, asgn):
        if idx == len(edges):
            yield dict(asgn)
            return
        i, j = edges[idx]
        for r in RELS:
            asgn[(i, j)] = r
            ok = True
            for k in seeds:
                if k == i or k == j: continue
                ik, jk = (min(i, k), max(i, k)), (min(j, k), max(j, k))
                if ik in asgn and jk in asgn:
                    r_ij = r
                    r_ik = get_rel(asgn, i, k)
                    r_jk = get_rel(asgn, j, k)
                    if not is_triple_consistent(r_ij, r_jk, r_ik):
                        ok = False; break
            if ok:
                yield from bt(idx + 1, asgn)
            if (i, j) in asgn: del asgn[(i, j)]
    yield from bt(0, {})


def enum_demand_structures(num_types, max_per_type=2):
    all_demands = [(R, t) for R in RELS for t in range(num_types)]
    single = [frozenset()]
    for sz in range(1, min(max_per_type + 1, len(all_demands) + 1)):
        for c in itertools.combinations(all_demands, sz):
            single.append(frozenset(c))
    for combo in itertools.product(single, repeat=num_types):
        if any(combo):
            yield {t: set(combo[t]) for t in range(num_types)}


# ── PPI reachability check ──────────────────────────────────────────

def has_ppi_cycle(demands, num_types):
    """Check if the demand structure has a PPI-reachable cycle.

    A type τ is "PPI-reachable" from τ' if τ' has demand PPI→τ,
    or τ' has demand PPI→τ'' and τ is PPI-reachable from τ''.

    A PPI cycle means some type can reach itself via PPI demands.
    Self-referential PPI (∃PPI.τ in type τ) is the simplest cycle.
    """
    # Build PPI demand graph
    ppi_targets = defaultdict(set)
    for t in range(num_types):
        for (R, target) in demands.get(t, set()):
            if R == PPI:
                ppi_targets[t].add(target)

    # Check for cycles using DFS
    def has_cycle_from(start):
        visited = set()
        stack = [start]
        while stack:
            node = stack.pop()
            if node in visited:
                if node == start and len(visited) > 0:
                    return True
                continue
            visited.add(node)
            for target in ppi_targets.get(node, set()):
                if target == start:
                    return True
                stack.append(target)
        return False

    for t in range(num_types):
        if has_cycle_from(t):
            return True
    return False


def classify_ppi_chain(demands, num_types, stuck_type):
    """Check if the stuck type is part of a PPI chain/cycle.

    Returns 'self' if stuck_type has PPI→self,
    'cycle' if it's part of a PPI cycle,
    'chain' if it PPI-reaches a PPI cycle,
    'none' if no PPI cycle involvement.
    """
    # Direct self-reference
    for (R, target) in demands.get(stuck_type, set()):
        if R == PPI and target == stuck_type:
            return 'self'

    # Build PPI target graph and check for cycles
    ppi_targets = defaultdict(set)
    for t in range(num_types):
        for (R, target) in demands.get(t, set()):
            if R == PPI:
                ppi_targets[t].add(target)

    # BFS from stuck_type's PPI successors
    visited = set()
    queue = list(ppi_targets.get(stuck_type, set()))
    while queue:
        t = queue.pop(0)
        if t == stuck_type:
            return 'cycle'
        if t in visited:
            continue
        visited.add(t)
        # Check if t is part of a self-referential PPI
        if t in ppi_targets.get(t, set()):
            return 'chain'  # stuck_type PPI-reaches a self-referential type
        for target in ppi_targets.get(t, set()):
            queue.append(target)

    return 'none'


# ── Fixed depth-2 check ─────────────────────────────────────────────

def check_depth2_fixed(num_types, max_demands=2, verbose=True):
    """Fixed depth-2 check with proper classification of all failures."""

    print(f"\n{'='*70}")
    print(f"FIXED DEPTH-2 CHECK: {num_types} types, max {max_demands} demands/type")
    print(f"{'='*70}")

    t0 = time.time()
    total = 0
    stuck_l1 = 0
    resolved_l2 = 0
    still_stuck_l2 = 0
    failure_classes = defaultdict(int)
    failure_details = []

    for demands in enum_demand_structures(num_types, max_demands):
        for seed_net in enum_seed_networks(num_types):

            def get_seed_rel(i, j):
                if i == j: return 'EQ'
                key = (min(i, j), max(i, j))
                r = seed_net[key]
                return r if i < j else INV[r]

            level1 = []
            for s in range(num_types):
                for (R, t) in demands.get(s, set()):
                    level1.append((s, R, t))

            if not level1:
                continue

            for l1_idx, (par, R_par, l1_type) in enumerate(level1):
                l1_demands = demands.get(l1_type, set())
                if not l1_demands:
                    continue

                total += 1

                blocker = l1_type
                if par == blocker:
                    possible_S = [INV[R_par]]
                else:
                    r_pb = get_seed_rel(par, blocker)
                    possible_S = list(COMP[(INV[R_par], r_pb)])

                # Check level-1 demand satisfaction
                def check_l1_demands(S):
                    b_to_seed = {}
                    b_to_seed[par] = frozenset({INV[R_par]})
                    if blocker != par:
                        b_to_seed[blocker] = frozenset({S})
                    for j in range(num_types):
                        if j in b_to_seed: continue
                        dom1 = COMP[(INV[R_par], get_seed_rel(par, j))]
                        dom2 = COMP[(S, get_seed_rel(blocker, j))]
                        b_to_seed[j] = dom1 & dom2

                    b_to_l1 = {}
                    for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                        if l1j_idx == l1_idx: continue
                        dom = set()
                        for bp in b_to_seed.get(pj, frozenset(RELS)):
                            dom |= COMP[(bp, Rj)]
                        b_to_l1[l1j_idx] = frozenset(dom)

                    unsat = []
                    for (R_dem, tgt) in l1_demands:
                        found = False
                        for j in range(num_types):
                            if j == tgt and R_dem in b_to_seed.get(j, frozenset()):
                                found = True; break
                        if not found:
                            for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                                if l1j_idx == l1_idx: continue
                                if tj == tgt and R_dem in b_to_l1.get(l1j_idx, frozenset()):
                                    found = True; break
                        if not found:
                            unsat.append((R_dem, tgt))
                    return unsat, b_to_seed

                best_unsat = None
                best_S = None
                best_b_to_seed = None
                for S in possible_S:
                    unsat, bts = check_l1_demands(S)
                    if not unsat:
                        best_unsat = []; break
                    if best_unsat is None or len(unsat) < len(best_unsat):
                        best_unsat = unsat
                        best_S = S
                        best_b_to_seed = bts

                if not best_unsat:
                    continue  # L1 satisfied

                stuck_l1 += 1

                # Depth-2 check: expand b, check if successors' demands are OK
                # FIXED: empty demands = resolved
                level2_ok = True
                level2_fail_demand = None

                for (R_l2, t_l2) in l1_demands:
                    t2_demands = demands.get(t_l2, set())
                    if not t2_demands:
                        continue  # successor has no demands = OK

                    # d2 is R_l2-child of b, type t_l2
                    # E(d2, b) = inv(R_l2)
                    # For each S (blocker rel of b):
                    any_s_works = False
                    for S in possible_S:
                        _, b_to_seed = check_l1_demands(S)

                        # d2's domains to seeds
                        d2_to_seed = {}
                        for j in range(num_types):
                            dom = set()
                            for bj in b_to_seed.get(j, frozenset(RELS)):
                                dom |= COMP[(INV[R_l2], bj)]
                            d2_to_seed[j] = frozenset(dom)

                        # d2's domains to level-1 nodes
                        d2_to_l1 = {}
                        for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                            if l1j_idx == l1_idx: continue
                            dom = set()
                            for dp in d2_to_seed.get(pj, frozenset(RELS)):
                                dom |= COMP[(dp, Rj)]
                            d2_to_l1[l1j_idx] = frozenset(dom)

                        # d2's edge to b
                        d2_to_b = INV[R_l2]

                        # d2's edges to b's OTHER successors
                        d2_to_bsucc = {}
                        for (R_other, t_other) in l1_demands:
                            if (R_other, t_other) == (R_l2, t_l2): continue
                            d2_to_bsucc[(R_other, t_other)] = COMP[(INV[R_l2], R_other)]

                        # Check d2's demands
                        all_sat = True
                        for (R_dem, tgt) in t2_demands:
                            found = False
                            for j in range(num_types):
                                if j == tgt and R_dem in d2_to_seed.get(j, frozenset()):
                                    found = True; break
                            if not found:
                                for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                                    if l1j_idx == l1_idx: continue
                                    if tj == tgt and R_dem in d2_to_l1.get(l1j_idx, frozenset()):
                                        found = True; break
                            if not found:
                                if l1_type == tgt and R_dem == d2_to_b:
                                    found = True
                            if not found:
                                for (R_other, t_other), dom in d2_to_bsucc.items():
                                    if t_other == tgt and R_dem in dom:
                                        found = True; break
                            if not found:
                                all_sat = False
                                level2_fail_demand = (t_l2, R_dem, tgt)
                                break

                        if all_sat:
                            any_s_works = True
                            break

                    if not any_s_works and t2_demands:
                        level2_ok = False
                        break

                if level2_ok:
                    resolved_l2 += 1
                else:
                    still_stuck_l2 += 1
                    # Classify the failure
                    cls = classify_ppi_chain(demands, num_types, l1_type)
                    # Also check the failing successor's type
                    if level2_fail_demand:
                        fail_type, fail_R, fail_tgt = level2_fail_demand
                        cls2 = classify_ppi_chain(demands, num_types, fail_type)
                        if cls2 in ('self', 'cycle', 'chain'):
                            cls = cls2
                        elif fail_R == PPI:
                            cls = f'ppi_demand_{cls}'
                    failure_classes[cls] += 1
                    if len(failure_details) < 5:
                        failure_details.append({
                            'demands': {t: set(demands[t]) for t in demands},
                            'seed_net': dict(seed_net),
                            'l1_type': l1_type,
                            'parent': par,
                            'R_parent': R_par,
                            'unsat': best_unsat,
                            'l2_fail': level2_fail_demand,
                            'class': cls,
                        })

    elapsed = time.time() - t0
    print(f"\nResults ({elapsed:.1f}s):")
    print(f"  Total level-1 scenarios: {total}")
    print(f"  Stuck at level 1: {stuck_l1} ({100*stuck_l1/max(total,1):.1f}%)")
    print(f"  Resolved at level 2: {resolved_l2} "
          f"({100*resolved_l2/max(stuck_l1,1):.1f}% of stuck)")
    print(f"  Still stuck at level 2: {still_stuck_l2} "
          f"({100*still_stuck_l2/max(total,1):.2f}%)")

    if failure_classes:
        print(f"\n  Failure classification:")
        for cls, cnt in sorted(failure_classes.items()):
            print(f"    {cls}: {cnt}")

    if failure_details:
        print(f"\n  Failure examples:")
        for idx, f in enumerate(failure_details):
            print(f"\n  --- {idx+1} [{f['class']}] ---")
            print(f"  Demands: {f['demands']}")
            print(f"  Seed: {f['seed_net']}")
            print(f"  Stuck type {f['l1_type']} (child of {f['parent']} via {f['R_parent']})")
            print(f"  L1 unsat: {f['unsat']}")
            if f['l2_fail']:
                ft, fr, ftgt = f['l2_fail']
                print(f"  L2 fail: type {ft} can't satisfy {fr}→{ftgt}")
    elif stuck_l1 > 0:
        print(f"\n  *** ALL stuck cases RESOLVED at depth 2! ***")
    else:
        print(f"\n  *** No stuck cases at all! ***")

    return still_stuck_l2


# ── Self-absorption analysis ────────────────────────────────────────

def self_absorption_analysis():
    """Exhaustively check which (R, S) pairs have R ∈ comp(S, R)."""
    print(f"\n{'='*70}")
    print(f"SELF-ABSORPTION ANALYSIS")
    print(f"For each R, S: is R ∈ comp(S, R)?")
    print(f"{'='*70}\n")

    failures = []
    for R in RELS:
        for S in RELS:
            sa = R in COMP[(S, R)]
            status = "✓" if sa else "✗ FAIL"
            if not sa:
                failures.append((R, S))
            print(f"  {R} self-absorbing under {S}: "
                  f"{R} ∈ comp({S}, {R}) = {set(COMP[(S,R)])}  {status}")

    print(f"\n  Total failures: {len(failures)}")
    for R, S in failures:
        print(f"  → {R} ∉ comp({S}, {R}) = {set(COMP[(S,R)])}")

    return failures


# ── Test: demands WITHOUT any PPI-cycle ─────────────────────────────

def check_no_ppi_cycle(num_types, max_demands=2):
    """Test ONLY demand structures that have NO PPI cycles.

    If all failures disappear, it confirms: the ONLY irreducible
    obstruction is PPI cycles (self-referential PPI demands).
    """
    print(f"\n{'='*70}")
    print(f"NO-PPI-CYCLE CHECK: {num_types} types, max {max_demands} demands/type")
    print(f"Testing only demand structures without PPI reachability cycles")
    print(f"{'='*70}")

    t0 = time.time()
    total = 0
    stuck = 0
    total_structures = 0
    skipped_structures = 0

    for demands in enum_demand_structures(num_types, max_demands):
        total_structures += 1
        if has_ppi_cycle(demands, num_types):
            skipped_structures += 1
            continue

        for seed_net in enum_seed_networks(num_types):
            def get_seed_rel(i, j):
                if i == j: return 'EQ'
                key = (min(i, j), max(i, j))
                r = seed_net[key]
                return r if i < j else INV[r]

            level1 = []
            for s in range(num_types):
                for (R, t) in demands.get(s, set()):
                    level1.append((s, R, t))

            if not level1:
                continue

            for l1_idx, (par, R_par, l1_type) in enumerate(level1):
                l1_demands = demands.get(l1_type, set())
                if not l1_demands:
                    continue

                total += 1

                blocker = l1_type
                if par == blocker:
                    possible_S = [INV[R_par]]
                else:
                    r_pb = get_seed_rel(par, blocker)
                    possible_S = list(COMP[(INV[R_par], r_pb)])

                # Check level-1 demand satisfaction
                any_works = False
                for S in possible_S:
                    b_to_seed = {}
                    b_to_seed[par] = frozenset({INV[R_par]})
                    if blocker != par:
                        b_to_seed[blocker] = frozenset({S})
                    for j in range(num_types):
                        if j in b_to_seed: continue
                        dom1 = COMP[(INV[R_par], get_seed_rel(par, j))]
                        dom2 = COMP[(S, get_seed_rel(blocker, j))]
                        b_to_seed[j] = dom1 & dom2

                    b_to_l1 = {}
                    for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                        if l1j_idx == l1_idx: continue
                        dom = set()
                        for bp in b_to_seed.get(pj, frozenset(RELS)):
                            dom |= COMP[(bp, Rj)]
                        b_to_l1[l1j_idx] = frozenset(dom)

                    all_sat = True
                    for (R_dem, tgt) in l1_demands:
                        found = False
                        for j in range(num_types):
                            if j == tgt and R_dem in b_to_seed.get(j, frozenset()):
                                found = True; break
                        if not found:
                            for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                                if l1j_idx == l1_idx: continue
                                if tj == tgt and R_dem in b_to_l1.get(l1j_idx, frozenset()):
                                    found = True; break
                        if not found:
                            all_sat = False; break

                    if all_sat:
                        any_works = True; break

                if not any_works:
                    stuck += 1
                    if stuck <= 3:
                        print(f"\n  STUCK (no PPI cycle): demands={demands}")
                        print(f"  Seed: {dict(seed_net)}")
                        print(f"  L1 type {l1_type}, child of {par} via {R_par}")

    elapsed = time.time() - t0
    print(f"\nResults ({elapsed:.1f}s):")
    print(f"  Demand structures: {total_structures} total, "
          f"{skipped_structures} with PPI cycles, "
          f"{total_structures - skipped_structures} without")
    print(f"  Scenarios tested (no PPI cycle): {total}")
    print(f"  Stuck at level 1: {stuck}")

    if stuck == 0:
        print(f"\n  *** ZERO FAILURES when PPI cycles are excluded! ***")
        print(f"  This confirms: the ONLY irreducible obstruction is PPI cycles.")
    else:
        print(f"\n  *** {stuck} FAILURES even without PPI cycles! ***")
        print(f"  The PPI-cycle classification is incomplete.")

    return stuck


# ── Test with depth-2 for non-PPI-cycle demands ────────────────────

def check_depth2_no_ppi_cycle(num_types, max_demands=2):
    """Depth-2 check restricted to demand structures WITHOUT PPI cycles.

    Expected: ALL stuck cases resolve at depth 2 (zero remaining).
    """
    print(f"\n{'='*70}")
    print(f"DEPTH-2, NO PPI CYCLE: {num_types} types, max {max_demands} demands/type")
    print(f"{'='*70}")

    t0 = time.time()
    total = 0
    stuck_l1 = 0
    resolved_l2 = 0
    still_stuck = 0

    for demands in enum_demand_structures(num_types, max_demands):
        if has_ppi_cycle(demands, num_types):
            continue

        for seed_net in enum_seed_networks(num_types):
            def get_seed_rel(i, j):
                if i == j: return 'EQ'
                key = (min(i, j), max(i, j))
                r = seed_net[key]
                return r if i < j else INV[r]

            level1 = []
            for s in range(num_types):
                for (R, t) in demands.get(s, set()):
                    level1.append((s, R, t))
            if not level1:
                continue

            for l1_idx, (par, R_par, l1_type) in enumerate(level1):
                l1_demands = demands.get(l1_type, set())
                if not l1_demands: continue
                total += 1

                blocker = l1_type
                if par == blocker:
                    possible_S = [INV[R_par]]
                else:
                    possible_S = list(COMP[(INV[R_par], get_seed_rel(par, blocker))])

                # L1 check
                l1_ok = False
                for S in possible_S:
                    b_to_seed = {}
                    b_to_seed[par] = frozenset({INV[R_par]})
                    if blocker != par:
                        b_to_seed[blocker] = frozenset({S})
                    for j in range(num_types):
                        if j in b_to_seed: continue
                        dom1 = COMP[(INV[R_par], get_seed_rel(par, j))]
                        dom2 = COMP[(S, get_seed_rel(blocker, j))]
                        b_to_seed[j] = dom1 & dom2

                    b_to_l1 = {}
                    for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                        if l1j_idx == l1_idx: continue
                        dom = set()
                        for bp in b_to_seed.get(pj, frozenset(RELS)):
                            dom |= COMP[(bp, Rj)]
                        b_to_l1[l1j_idx] = frozenset(dom)

                    ok = True
                    for (R_dem, tgt) in l1_demands:
                        found = False
                        for j in range(num_types):
                            if j == tgt and R_dem in b_to_seed.get(j, frozenset()):
                                found = True; break
                        if not found:
                            for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                                if l1j_idx == l1_idx: continue
                                if tj == tgt and R_dem in b_to_l1.get(l1j_idx, frozenset()):
                                    found = True; break
                        if not found:
                            ok = False; break
                    if ok:
                        l1_ok = True; break

                if l1_ok: continue
                stuck_l1 += 1

                # Depth-2: expand b
                l2_ok = True
                for (R_l2, t_l2) in l1_demands:
                    t2_demands = demands.get(t_l2, set())
                    if not t2_demands: continue  # empty = OK

                    any_s_ok = False
                    for S in possible_S:
                        b_to_seed = {}
                        b_to_seed[par] = frozenset({INV[R_par]})
                        if blocker != par:
                            b_to_seed[blocker] = frozenset({S})
                        for j in range(num_types):
                            if j in b_to_seed: continue
                            dom1 = COMP[(INV[R_par], get_seed_rel(par, j))]
                            dom2 = COMP[(S, get_seed_rel(blocker, j))]
                            b_to_seed[j] = dom1 & dom2

                        d2_to_seed = {}
                        for j in range(num_types):
                            dom = set()
                            for bj in b_to_seed.get(j, frozenset(RELS)):
                                dom |= COMP[(INV[R_l2], bj)]
                            d2_to_seed[j] = frozenset(dom)

                        d2_to_l1 = {}
                        for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                            if l1j_idx == l1_idx: continue
                            dom = set()
                            for dp in d2_to_seed.get(pj, frozenset(RELS)):
                                dom |= COMP[(dp, Rj)]
                            d2_to_l1[l1j_idx] = frozenset(dom)

                        d2_to_b = INV[R_l2]
                        d2_to_bsucc = {}
                        for (Ro, to) in l1_demands:
                            if (Ro, to) == (R_l2, t_l2): continue
                            d2_to_bsucc[(Ro, to)] = COMP[(INV[R_l2], Ro)]

                        ok = True
                        for (Rd, tgt) in t2_demands:
                            found = False
                            for j in range(num_types):
                                if j == tgt and Rd in d2_to_seed.get(j, frozenset()):
                                    found = True; break
                            if not found:
                                for l1j_idx, (pj, Rj, tj) in enumerate(level1):
                                    if l1j_idx == l1_idx: continue
                                    if tj == tgt and Rd in d2_to_l1.get(l1j_idx, frozenset()):
                                        found = True; break
                            if not found:
                                if l1_type == tgt and Rd == d2_to_b:
                                    found = True
                            if not found:
                                for (Ro, to), dom in d2_to_bsucc.items():
                                    if to == tgt and Rd in dom:
                                        found = True; break
                            if not found:
                                ok = False; break
                        if ok:
                            any_s_ok = True; break

                    if not any_s_ok and t2_demands:
                        l2_ok = False; break

                if l2_ok:
                    resolved_l2 += 1
                else:
                    still_stuck += 1
                    if still_stuck <= 3:
                        print(f"  DEPTH-2 STUCK (no PPI cycle!)")
                        print(f"  demands={demands}, seed={dict(seed_net)}")
                        print(f"  type {l1_type}, child of {par} via {R_par}")

    elapsed = time.time() - t0
    print(f"\nResults ({elapsed:.1f}s):")
    print(f"  Scenarios (no PPI cycle): {total}")
    print(f"  Stuck at L1: {stuck_l1}")
    print(f"  Resolved at L2: {resolved_l2}")
    print(f"  Still stuck at L2: {still_stuck}")

    if still_stuck == 0 and stuck_l1 > 0:
        print(f"\n  *** ALL non-PPI-cycle stuck cases resolve at depth 2! ***")

    return still_stuck


if __name__ == '__main__':
    print("COMPREHENSIVE DEMAND SATISFACTION ANALYSIS")
    print("Classifying all failures and testing key claims")

    # Self-absorption analysis
    self_absorption_analysis()

    # 2 types: fixed depth-2 with classification
    check_depth2_fixed(2, max_demands=2)

    # 2 types: no-PPI-cycle check (level 1)
    check_no_ppi_cycle(2, max_demands=2)

    # 2 types: depth-2 without PPI cycles
    check_depth2_no_ppi_cycle(2, max_demands=2)

    # 3 types: fixed depth-2
    check_depth2_fixed(3, max_demands=1)

    # 3 types: no-PPI-cycle
    check_no_ppi_cycle(3, max_demands=1)

    # 3 types: depth-2 without PPI cycles
    check_depth2_no_ppi_cycle(3, max_demands=1)

    print("\n\n" + "="*70)
    print("FINAL SUMMARY")
    print("="*70)
    print("""
Key claims to verify:
  1. The ONLY self-absorption failure is PPI ∉ comp(DR, PPI) = {DR}
  2. ALL level-1 failures involve DR→PPI (blocked node DR to blocker, PPI demand)
  3. When PPI cycles are excluded, level-1 failures still exist (DR→PPI)
     but ALL resolve at depth 2
  4. The irreducible failures are EXACTLY the PPI cycle cases
     (self-referential ∃PPI.τ or mutual ∃PPI chains)
  5. PP-chain demands (∃PPI.τ) require infinite chains — handled separately

Proof strategy:
  A) For non-PPI-chain demands: one extra expansion level suffices
  B) For PPI-chain demands: explicit infinite chain construction
  C) Cross-edges: triangle-type filtering + patchwork property
""")
