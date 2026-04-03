#!/usr/bin/env python3
"""
Strong triangle closure check for the triangle-type blocking approach.

Tests whether composition-consistent RCC5 models with type assignments
satisfy "strong triangle closure" (STC) — the condition needed for the
triangle-type blocking approach to ALCI_RCC5 decidability.

Definitions:
  P = {(τ₁, R, τ₂) | ∃ distinct nodes x,y: L(x)=τ₁, L(y)=τ₂, E(x,y)=R}
  T = {(τ₁,R₁₂,τ₂,R₂₃,τ₃,R₁₃) | ∃ distinct x,y,z forming this triangle}
  STC: ∀(τ₁,R,τ₂)∈P, (τ₂,S,τ₃)∈P: ∃R' with (τ₁,R,τ₂,S,τ₃,R')∈T

Also tests:
  - T-filtered extension CSP solvability (the actual requirement)
  - Comparison of STC vs Q3s failures
"""

import itertools
import time
from extension_gap_checker import RELS, INV, COMP, is_triple_consistent


def get_rel(network, i, j):
    if i == j:
        return 'EQ'
    key = (min(i, j), max(i, j))
    r = network[key]
    return r if i < j else INV[r]


def extract_PT(n, tp, network):
    """Extract pair-types P and triangle types T."""
    P = set()
    T = set()
    for i in range(n):
        for j in range(n):
            if j == i:
                continue
            rij = get_rel(network, i, j)
            P.add((tp[i], rij, tp[j]))
            for k in range(n):
                if k == i or k == j:
                    continue
                rjk = get_rel(network, j, k)
                rik = get_rel(network, i, k)
                T.add((tp[i], rij, tp[j], rjk, tp[k], rik))
    return P, T


def check_stc(P, T):
    """Check strong triangle closure. Returns list of failures."""
    failures = []
    for (t1, r12, t2) in P:
        for (t2b, r23, t3) in P:
            if t2b != t2:
                continue
            found = any((t1, r12, t2, r23, t3, r13) in T for r13 in RELS)
            if not found:
                failures.append((t1, r12, t2, r23, t3))
    return failures


def check_extension_csp(n, tp, network, T, P, only_unsatisfied=False):
    """Check if the T-filtered extension CSP is solvable for all scenarios.

    For each (new_type, demand_node, demand_rel), try to assign edges from
    a new node to all existing nodes such that all triangles are in T.
    Uses arc-consistency enforcement.

    If only_unsatisfied=True, skip demands that are already globally satisfied
    (i.e., there exists a node w with tp[w]=new_type and E(demand_node,w)=dem_rel).

    Returns number of failures and first few examples.
    """
    type_set = sorted(set(tp.values()))
    fails = 0
    examples = []

    for new_type in type_set:
        for dem_node in range(n):
            for dem_rel in RELS:
                # E(dem_node, new) = dem_rel, so E(new, dem_node) = inv(dem_rel)
                inv_dem = INV[dem_rel]
                if (new_type, inv_dem, tp[dem_node]) not in P:
                    continue

                # Skip if demand already globally satisfied
                if only_unsatisfied:
                    satisfied = False
                    for w in range(n):
                        if w == dem_node:
                            continue
                        if tp[w] == new_type and get_rel(network, dem_node, w) == dem_rel:
                            satisfied = True
                            break
                    if satisfied:
                        continue

                # Initial domains
                domains = {}
                skip = False
                for i in range(n):
                    if i == dem_node:
                        domains[i] = frozenset({inv_dem})
                    else:
                        d = frozenset(r for r in RELS
                                      if (new_type, r, tp[i]) in P)
                        if not d:
                            skip = True
                            break
                        domains[i] = d
                if skip:
                    continue

                # Arc-consistency with triangle-type filtering
                changed = True
                empty = False
                while changed and not empty:
                    changed = False
                    for i in range(n):
                        if empty:
                            break
                        for j in range(n):
                            if i == j:
                                continue
                            rij = get_rel(network, i, j)
                            new_di = frozenset(
                                ri for ri in domains[i]
                                if any((new_type, ri, tp[i], rij, tp[j], rj) in T
                                       for rj in domains[j])
                            )
                            if new_di != domains[i]:
                                domains[i] = new_di
                                changed = True
                                if not new_di:
                                    empty = True
                                    break

                if empty:
                    fails += 1
                    if len(examples) < 3:
                        examples.append((new_type, dem_node, dem_rel,
                                         {i: set(d) for i, d in domains.items()}))

    return fails, examples


def would_create_new_triangles(n, tp, network, T, P, new_type, dem_node, dem_rel):
    """Check if a composition-consistent extension would create new triangle types.

    Tries to extend the graph with a new node (new_type) connected via dem_rel
    to dem_node. Finds the unique composition-forced assignment (if edges are
    fully determined) or tries all possibilities. Returns True if EVERY
    consistent extension creates at least one new triangle type.
    """
    inv_dem = INV[dem_rel]

    # Compute forced edges via composition
    # For each existing node i != dem_node:
    #   E(new, i) must be in comp(inv_dem, E(dem_node, i)) ∩ comp(R_j, E(j,i)) for all j
    # Start with just the demand constraint
    domains = {}
    for i in range(n):
        if i == dem_node:
            domains[i] = frozenset({inv_dem})
        else:
            # Must be in comp(E(new,dem), E(dem,i))
            r_dem_i = get_rel(network, dem_node, i)
            d = frozenset(COMP.get((inv_dem, r_dem_i), frozenset())) & frozenset(RELS)
            domains[i] = d

    # Arc-consistency with composition only (no T constraint)
    changed = True
    while changed:
        changed = False
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                rij = get_rel(network, i, j)
                new_di = frozenset(
                    ri for ri in domains[i]
                    if any(rj in COMP.get((ri, rij), frozenset())
                           for rj in domains[j])
                )
                if new_di != domains[i]:
                    domains[i] = new_di
                    changed = True
                    if not new_di:
                        return True  # No consistent extension at all

    # Check if any consistent extension is T-closed
    # Try all combinations (for small models this is feasible)
    node_list = [i for i in range(n) if i != dem_node]
    domain_lists = [list(domains[i]) for i in node_list]

    for combo in itertools.product(*domain_lists):
        assignment = {dem_node: inv_dem}
        for idx, i in enumerate(node_list):
            assignment[i] = combo[idx]

        # Check all triples for composition consistency
        ok = True
        for i in range(n):
            for j in range(i + 1, n):
                ri = assignment[i]
                rj = assignment[j]
                rij = get_rel(network, i, j)
                # Check (new, i, j): ri, rij, rj
                if rj not in COMP.get((ri, rij), frozenset()):
                    ok = False
                    break
                if ri not in COMP.get((rj, INV[rij]), frozenset()):
                    ok = False
                    break
            if not ok:
                break

        if not ok:
            continue

        # Check if all triangles are in T
        all_in_T = True
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                rij = get_rel(network, i, j)
                ri = assignment[i]
                rj = assignment[j]
                # Triangle (new, i, j)
                if (new_type, ri, tp[i], rij, tp[j], rj) not in T:
                    all_in_T = False
                    break
            if not all_in_T:
                break

        if all_in_T:
            return False  # Found a T-closed extension → no new triangles

    return True  # Every consistent extension creates new triangles


def check_q3s(dn, type_set):
    """Check Q3s for DN. Returns number of failures."""
    count = 0
    for t1 in type_set:
        for t2 in type_set:
            if t1 == t2:
                continue
            for r12 in dn.get((t1, t2), set()):
                for t3 in type_set:
                    if t3 == t1 or t3 == t2:
                        continue
                    for r13 in dn.get((t1, t3), set()):
                        if not any(r13 in COMP.get((r12, r23), frozenset())
                                   for r23 in dn.get((t2, t3), set())):
                            count += 1
    return count


def extract_dn(n, tp, network, type_labels):
    dn = {}
    for t1 in type_labels:
        for t2 in type_labels:
            if t1 == t2:
                continue
            rels = set()
            for e1 in range(n):
                if tp[e1] != t1:
                    continue
                for e2 in range(n):
                    if tp[e2] != t2 or e1 == e2:
                        continue
                    rels.add(get_rel(network, e1, e2))
            if rels:
                dn[(t1, t2)] = rels
    return dn


def main():
    print("=" * 70)
    print("STRONG TRIANGLE CLOSURE (STC) CHECK")
    print("=" * 70)

    # -------------------------------------------------------
    # PART 1: GPT's counterexample
    # -------------------------------------------------------
    print("\nPART 1: GPT's counterexample")
    print("-" * 50)

    n = 6
    tp = {0: 'C0', 1: 'A', 2: 'B', 3: 'B', 4: 'p', 5: 'q'}
    net = {
        (0, 1): 'DR', (0, 2): 'DR', (0, 3): 'PO',
        (0, 4): 'PP', (0, 5): 'DR', (1, 2): 'DR',
        (1, 3): 'PO', (1, 4): 'DR', (1, 5): 'DR',
        (2, 3): 'DR', (2, 4): 'DR', (2, 5): 'DR',
        (3, 4): 'PO', (3, 5): 'DR', (4, 5): 'DR',
    }
    type_set = sorted(set(tp.values()))
    P, T = extract_PT(n, tp, net)
    stc = check_stc(P, T)
    print(f"|P|={len(P)}, |T|={len(T)}, STC failures={len(stc)}")

    # The key check: does the problematic (C0,PO,B,DR,p) fail STC?
    key_fail = ('C0', 'PO', 'B', 'DR', 'p')
    print(f"Key failure (C0,PO,B,DR,p) in STC violations: {key_fail in stc}")

    # Check T-filtered extension — all scenarios
    ext_f, ext_ex = check_extension_csp(n, tp, net, T, P, only_unsatisfied=False)
    print(f"T-filtered extension CSP failures (all demands): {ext_f}")

    # Check T-filtered extension — only unsatisfied demands
    ext_f2, ext_ex2 = check_extension_csp(n, tp, net, T, P, only_unsatisfied=True)
    print(f"T-filtered extension CSP failures (unsatisfied only): {ext_f2}")
    if ext_ex2:
        for new_t, dn, dr, doms in ext_ex2[:3]:
            print(f"  new={new_t}, demand: e{dn}({tp[dn]}) via {dr}")
            empty = [i for i, d in doms.items() if not d]
            print(f"  empty domains at: {['e' + str(i) + '(' + tp[i] + ')' for i in empty]}")

    # -------------------------------------------------------
    # PART 2: Systematic check (n=3,4; 2-3 types)
    # -------------------------------------------------------
    print(f"\nPART 2: Systematic check")
    print("-" * 50)

    total = 0
    stc_fail_count = 0
    ext_fail_count = 0
    ext_unsat_fail_count = 0  # only unsatisfied demands
    q3s_fail_count = 0
    both_stc_ext = 0  # STC fails AND ext fails
    stc_not_ext = 0   # STC fails but ext passes
    q3s_not_stc = 0   # Q3s fails but STC passes
    stc_not_q3s = 0   # STC fails but Q3s passes

    stc_examples = []
    ext_examples = []
    ext_unsat_examples = []

    t0 = time.time()

    for n_el in [3, 4]:
        for n_tp in range(2, min(n_el, 4) + 1):
            type_labels = [chr(ord('A') + i) for i in range(n_tp)]
            edges = [(i, j) for i in range(n_el) for j in range(i + 1, n_el)]

            for ta in itertools.product(range(n_tp), repeat=n_el):
                if len(set(ta)) < n_tp:
                    continue
                tp_map = {i: type_labels[ta[i]] for i in range(n_el)}

                def enum_nets(idx, network):
                    nonlocal total, stc_fail_count, ext_fail_count
                    nonlocal ext_unsat_fail_count
                    nonlocal q3s_fail_count, both_stc_ext, stc_not_ext
                    nonlocal q3s_not_stc, stc_not_q3s

                    if idx == len(edges):
                        total += 1
                        P_loc, T_loc = extract_PT(n_el, tp_map, network)
                        stc_f = check_stc(P_loc, T_loc)
                        dn_loc = extract_dn(n_el, tp_map, network, type_labels)
                        q3s_f = check_q3s(dn_loc, type_labels)

                        has_stc = len(stc_f) > 0
                        has_q3s = q3s_f > 0

                        if has_stc:
                            stc_fail_count += 1
                        if has_q3s:
                            q3s_fail_count += 1
                        if has_stc and not has_q3s:
                            stc_not_q3s += 1
                        if has_q3s and not has_stc:
                            q3s_not_stc += 1

                        # Check extension CSP — all demands
                        ef, eex = check_extension_csp(
                            n_el, tp_map, dict(network), T_loc, P_loc,
                            only_unsatisfied=False)
                        if ef > 0:
                            ext_fail_count += 1
                            if has_stc:
                                both_stc_ext += 1

                        # Check extension CSP — unsatisfied demands only
                        ef2, eex2 = check_extension_csp(
                            n_el, tp_map, dict(network), T_loc, P_loc,
                            only_unsatisfied=True)
                        if ef2 > 0:
                            ext_unsat_fail_count += 1
                            if len(ext_unsat_examples) < 5:
                                ext_unsat_examples.append({
                                    'n': n_el, 'k': n_tp,
                                    'types': dict(tp_map),
                                    'network': dict(network),
                                    'ext': eex2,
                                })

                        if has_stc and ef == 0:
                            stc_not_ext += 1
                            if len(stc_examples) < 3:
                                stc_examples.append({
                                    'n': n_el, 'k': n_tp,
                                    'types': dict(tp_map),
                                    'network': dict(network),
                                    'stc_fails': stc_f[:3],
                                })
                        if ef > 0 and len(ext_examples) < 5:
                            ext_examples.append({
                                'n': n_el, 'k': n_tp,
                                'types': dict(tp_map),
                                'network': dict(network),
                                'ext': eex,
                            })
                        return

                    i, j = edges[idx]
                    for r in RELS:
                        network[(i, j)] = r
                        ok = True
                        for m in range(n_el):
                            if m == i or m == j:
                                continue
                            ik = (min(i, m), max(i, m))
                            jk = (min(j, m), max(j, m))
                            if ik in network and jk in network:
                                rij = r if i < j else INV[r]
                                rim = (network[ik] if i < m
                                       else INV[network[ik]])
                                rjm = (network[jk] if j < m
                                       else INV[network[jk]])
                                if not is_triple_consistent(rij, rjm, rim):
                                    ok = False
                                    break
                        if ok:
                            enum_nets(idx + 1, network)
                        if edges[idx] in network:
                            del network[edges[idx]]

                enum_nets(0, {})

        elapsed = time.time() - t0
        print(f"  After n={n_el}: total={total:,}, "
              f"STC fail={stc_fail_count}, "
              f"ext(all)={ext_fail_count}, "
              f"ext(unsat)={ext_unsat_fail_count} "
              f"[{elapsed:.1f}s]")

    # -------------------------------------------------------
    # PART 3: Summary
    # -------------------------------------------------------
    print(f"\n{'=' * 70}")
    print("SUMMARY")
    print(f"{'=' * 70}")

    print(f"\nTotal models: {total:,}")
    print(f"STC violations:             {stc_fail_count} "
          f"({100 * stc_fail_count / max(total, 1):.1f}%)")
    print(f"Q3s violations:             {q3s_fail_count} "
          f"({100 * q3s_fail_count / max(total, 1):.1f}%)")
    print(f"Ext CSP failures (all):     {ext_fail_count} "
          f"({100 * ext_fail_count / max(total, 1):.1f}%)")
    print(f"Ext CSP failures (unsat):   {ext_unsat_fail_count} "
          f"({100 * ext_unsat_fail_count / max(total, 1):.1f}%)")

    print(f"\nRelationship between STC and Q3s:")
    print(f"  STC fails, Q3s passes: {stc_not_q3s}")
    print(f"  Q3s fails, STC passes: {q3s_not_stc}")

    print(f"\nRelationship between STC and ext CSP (all):")
    print(f"  STC fails, ext passes: {stc_not_ext}")
    print(f"  STC fails, ext fails:  {both_stc_ext}")

    if ext_unsat_fail_count == 0:
        print(f"\n*** KEY FINDING: T-filtered ext CSP always solvable for ***")
        print(f"*** unsatisfied demands! Global blocking handles the rest. ***")
        print(f"*** Triangle approach may work with global blocking! ***")
    elif ext_unsat_fail_count < ext_fail_count:
        print(f"\n*** Global blocking reduces failures from {ext_fail_count} "
              f"to {ext_unsat_fail_count} ***")
        print(f"*** But {ext_unsat_fail_count} genuine failures remain ***")
    else:
        print(f"\n*** T-filtered extension CSP FAILS even for unsatisfied demands ***")

    # -------------------------------------------------------
    # PART 3: Classify ext(unsat) failures
    # -------------------------------------------------------
    print(f"\n{'=' * 70}")
    print("PART 3: Are ext(unsat) failures real or would-be-expanded?")
    print(f"{'=' * 70}")
    print("Check if every consistent extension creates new triangle types")
    print("(meaning node would NOT be blocked under condition b).\n")

    real_failures = 0
    would_expand = 0

    t1_start = time.time()
    models_with_unsat = 0

    for n_el in [3, 4]:
        for n_tp in range(2, min(n_el, 4) + 1):
            type_labels = [chr(ord('A') + i) for i in range(n_tp)]
            edges_list = [(i, j) for i in range(n_el)
                          for j in range(i + 1, n_el)]

            for ta in itertools.product(range(n_tp), repeat=n_el):
                if len(set(ta)) < n_tp:
                    continue
                tp_map = {i: type_labels[ta[i]] for i in range(n_el)}

                def enum_nets3(idx, network):
                    nonlocal real_failures, would_expand, models_with_unsat
                    if idx == len(edges_list):
                        P_loc, T_loc = extract_PT(n_el, tp_map, network)
                        ef, eex = check_extension_csp(
                            n_el, tp_map, dict(network), T_loc, P_loc,
                            only_unsatisfied=True)
                        if ef == 0:
                            return
                        models_with_unsat += 1
                        for new_t, dn, dr, doms in eex:
                            creates_new = would_create_new_triangles(
                                n_el, tp_map, dict(network), T_loc, P_loc,
                                new_t, dn, dr)
                            if creates_new:
                                would_expand += 1
                            else:
                                real_failures += 1
                        return

                    i, j = edges_list[idx]
                    for r in RELS:
                        network[(i, j)] = r
                        ok = True
                        for m in range(n_el):
                            if m == i or m == j:
                                continue
                            ik = (min(i, m), max(i, m))
                            jk = (min(j, m), max(j, m))
                            if ik in network and jk in network:
                                rij_v = r if i < j else INV[r]
                                rim = (network[ik] if i < m
                                       else INV[network[ik]])
                                rjm = (network[jk] if j < m
                                       else INV[network[jk]])
                                if not is_triple_consistent(rij_v, rjm, rim):
                                    ok = False
                                    break
                        if ok:
                            enum_nets3(idx + 1, network)
                        if edges_list[idx] in network:
                            del network[edges_list[idx]]

                enum_nets3(0, {})

        elapsed = time.time() - t1_start
        print(f"  After n={n_el}: models_with_failures={models_with_unsat}, "
              f"would_expand={would_expand}, "
              f"REAL={real_failures} [{elapsed:.1f}s]")

    print(f"\n  Scenarios where extension creates new triangles "
          f"(node not blocked): {would_expand}")
    print(f"  GENUINE failures (T-closed extension exists but "
          f"CSP fails): {real_failures}")

    if real_failures == 0:
        print(f"\n  *** ALL ext(unsat) failures are would-be-expanded! ***")
        print(f"  *** When a T-closed extension exists, the T-filtered ***")
        print(f"  *** CSP always finds it. The approach is CONSISTENT. ***")
    else:
        print(f"\n  *** {real_failures} GENUINE failures found ***")

    # Print examples
    if ext_unsat_examples:
        print(f"\nUnsatisfied-demand extension CSP failure examples:")
        for i, ex in enumerate(ext_unsat_examples[:5]):
            print(f"\n  Example {i + 1} ({ex['n']} elements, {ex['k']} types):")
            for e in sorted(ex['types'].keys()):
                print(f"    e{e}: type {ex['types'][e]}")
            for (e1, e2), r in sorted(ex['network'].items()):
                print(f"    E(e{e1},e{e2}) = {r}")
            for new_t, dn, dr, doms in ex['ext'][:2]:
                print(f"    Fail: new_type={new_t}, demand at "
                      f"e{dn}({ex['types'][dn]}) via {dr}")
                empty = [j for j, d in doms.items() if not d]
                print(f"    Empty domains: "
                      f"{['e' + str(j) + '(' + ex['types'][j] + ')' for j in empty]}")
    elif ext_unsat_fail_count == 0 and ext_fail_count > 0:
        print(f"\nAll extension failures are for already-satisfied demands!")
        print(f"Global blocking (condition a) eliminates all failures.")


def part4_cross_context():
    """PART 4: Cross-context test.

    Simulate what happens in the model: take a graph G, extract T.
    Then build a DIFFERENT graph G' on the same types (all pair-types in P,
    all triangle types in T) and try extensions in G'. This tests whether
    T-filtered extensions are solvable in a "foreign" context.
    """
    print(f"\n{'=' * 70}")
    print("PART 4: Cross-context extension test")
    print(f"{'=' * 70}")
    print("For each pair of models (G, G') on the same types with G's T")
    print("covering G's triangles, test if G' extensions are T-solvable.\n")

    cross_failures = 0
    cross_total = 0

    for n_el in [3, 4]:
        for n_tp in range(2, min(n_el, 4) + 1):
            type_labels = [chr(ord('A') + i) for i in range(n_tp)]
            edges_list = [(i, j) for i in range(n_el)
                          for j in range(i + 1, n_el)]

            # Collect all models grouped by type assignment
            models_by_ta = {}
            for ta in itertools.product(range(n_tp), repeat=n_el):
                if len(set(ta)) < n_tp:
                    continue
                tp_map = {i: type_labels[ta[i]] for i in range(n_el)}
                ta_key = tuple(ta)
                models_by_ta[ta_key] = []

                def collect(idx, network):
                    if idx == len(edges_list):
                        models_by_ta[ta_key].append(dict(network))
                        return
                    i, j = edges_list[idx]
                    for r in RELS:
                        network[(i, j)] = r
                        ok = True
                        for m in range(n_el):
                            if m == i or m == j:
                                continue
                            ik = (min(i, m), max(i, m))
                            jk = (min(j, m), max(j, m))
                            if ik in network and jk in network:
                                rij_v = r if i < j else INV[r]
                                rim = (network[ik] if i < m
                                       else INV[network[ik]])
                                rjm = (network[jk] if j < m
                                       else INV[network[jk]])
                                if not is_triple_consistent(rij_v, rjm, rim):
                                    ok = False
                                    break
                        if ok:
                            collect(idx + 1, network)
                        if edges_list[idx] in network:
                            del network[edges_list[idx]]

                collect(0, {})

            # For each type assignment, take pairs of models
            for ta_key, models in models_by_ta.items():
                if len(models) < 2:
                    continue
                tp_map = {i: type_labels[ta_key[i]] for i in range(n_el)}

                # Use the UNION of triangle types from ALL models
                # (simulating a saturated T)
                T_union = set()
                P_union = set()
                for net in models:
                    P_loc, T_loc = extract_PT(n_el, tp_map, net)
                    T_union |= T_loc
                    P_union |= P_loc

                # Now test extensions in each model using T_union
                for net in models:
                    P_loc, T_loc = extract_PT(n_el, tp_map, net)
                    # Only test if T_loc ⊆ T_union (always true)
                    ef, _ = check_extension_csp(
                        n_el, tp_map, net, T_union, P_union,
                        only_unsatisfied=True)
                    cross_total += 1
                    if ef > 0:
                        # Check if these are real failures
                        for new_t, dn, dr, doms in _:
                            creates_new = would_create_new_triangles(
                                n_el, tp_map, net, T_union, P_union,
                                new_t, dn, dr)
                            if not creates_new:
                                cross_failures += 1

        print(f"  After n={n_el}: tested={cross_total}, "
              f"real cross-context failures={cross_failures}")

    if cross_failures == 0:
        print(f"\n  *** No cross-context failures with union T! ***")
        print(f"  *** Triangle approach appears robust across contexts ***")
    else:
        print(f"\n  *** {cross_failures} cross-context failures found ***")
        print(f"  *** Triangle types from one model don't transfer ***")


if __name__ == '__main__':
    main()
    part4_cross_context()
