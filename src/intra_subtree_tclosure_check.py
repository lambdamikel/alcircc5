#!/usr/bin/env python3
"""
Investigate the intra-subtree T-closure issue for ALCI_RCC5 tableau
soundness (scrutiny point 1 in the tableau paper).

When the tree unraveling copies a blocked subtree, two distinct elements
can both map to the SAME completion-graph node. The paper's proof uses
a "map-based" relation assignment ρ(a,b) = E(map(a), map(b)) for pairs
with distinct maps, and claims a T-closed solution exists.

This script checks whether the map-based assignment is actually T-closed,
and if not, whether arc-consistency on the constraint network can still
yield non-empty domains (which would still give decidability via full
RCC5 tractability).

Key finding: the map-based assignment creates "mirror triangles" of the
form (τ_A, R, τ_A, PO, σ, PO) — two τ_A copies both PO to the same σ
witness — that NEVER appear in T(G) because in the completion graph, each
σ witness is PO to exactly one τ_A node. The script investigates whether
arc-consistency resolves this by restricting the problematic domains.
"""

from extension_gap_checker import RELS, INV, COMP

DR, PO, PP, PPI = 'DR', 'PO', 'PP', 'PPI'
ALL_RELS = [DR, PO, PP, PPI]


def comp(r, s):
    return COMP[(r, s)]


def inv(r):
    return INV[r]


def build_completion_graph(chain_len):
    """
    Build the completion graph: a prefix of the PO-incoherent model.
    Uses the all-DR-backward branch.

    Returns (nodes, ntype, rel) for the active portion.
    """
    num_w = (chain_len + 1) // 2
    chain = [f'd{i}' for i in range(chain_len)]
    witnesses = [f'w{k}' for k in range(num_w)]
    nodes = chain + witnesses

    ntype = {}
    for i in range(chain_len):
        ntype[chain[i]] = 'tA' if i % 2 == 0 else 'tB'
    for w in witnesses:
        ntype[w] = 'sigma'

    rel = {}
    for i in range(chain_len):
        for j in range(i + 1, chain_len):
            rel[(chain[i], chain[j])] = PP
            rel[(chain[j], chain[i])] = PPI

    for k in range(num_w):
        for i in range(chain_len):
            if i == 2 * k:
                rel[(chain[i], witnesses[k])] = PO
                rel[(witnesses[k], chain[i])] = PO
            elif i < 2 * k:
                rel[(chain[i], witnesses[k])] = DR
                rel[(witnesses[k], chain[i])] = DR
            else:
                rel[(chain[i], witnesses[k])] = PPI
                rel[(witnesses[k], chain[i])] = PP

    for i in range(num_w):
        for j in range(i + 1, num_w):
            rel[(witnesses[i], witnesses[j])] = DR
            rel[(witnesses[j], witnesses[i])] = DR

    return nodes, ntype, rel


def compute_T(nodes, ntype, rel):
    """Compute T(G) = set of all triangle types in the completion graph."""
    T = set()
    for i, a in enumerate(nodes):
        for j in range(i + 1, len(nodes)):
            b = nodes[j]
            for k in range(j + 1, len(nodes)):
                c = nodes[k]
                for x, y, z in [(a, b, c), (a, c, b), (b, a, c),
                                 (b, c, a), (c, a, b), (c, b, a)]:
                    t = (ntype[x], rel[(x, y)], ntype[y],
                         rel[(y, z)], ntype[z], rel[(x, z)])
                    T.add(t)
    return T


def compute_P(nodes, ntype, rel):
    """Compute P(G) = set of all pair-types in the completion graph."""
    P = set()
    for a in nodes:
        for b in nodes:
            if a != b:
                P.add((ntype[a], rel[(a, b)], ntype[b]))
    return P


def format_tri(t):
    return f"({t[0]}, {t[1]}, {t[2]}, {t[3]}, {t[4]}, {t[5]})"


# =====================================================================
# PART 1: Mirror triangle analysis
# =====================================================================

def analyze_mirror_triangles(T, ntype_set):
    """
    A "mirror triangle" arises when two elements both map to the same
    CG node n, and both have the same relation S to a third element
    mapping to some node m. The triangle type is:
        (ntype[n], R, ntype[n], S, ntype[m], S)
    where R is the (unknown) relation between the two copies.

    Check which of these mirror types are in T(G) and which are not.
    """
    print("=" * 72)
    print("MIRROR TRIANGLE ANALYSIS")
    print("=" * 72)
    print()
    print("When two elements both map to node n, and both have")
    print("relation S to a third element mapping to m, the triangle is:")
    print("  (type(n), R, type(n), S, type(m), S)")
    print("where R is the unknown same-node relation.")
    print()

    results = {}
    for tau1 in ntype_set:
        for S in ALL_RELS:
            for tau2 in ntype_set:
                feasible = []
                for R in ALL_RELS:
                    t = (tau1, R, tau1, S, tau2, S)
                    if t in T:
                        feasible.append(R)
                key = (tau1, S, tau2)
                results[key] = feasible

    # Report problematic cases (no R works)
    problems = []
    partial = []
    for (tau1, S, tau2), feasible in sorted(results.items()):
        if not feasible:
            problems.append((tau1, S, tau2))
        elif len(feasible) < 4:
            partial.append((tau1, S, tau2, feasible))

    if problems:
        print(f"IMPOSSIBLE mirror triangles ({len(problems)}):")
        print("  These triangle types are NOT in T(G) for ANY R:")
        for tau1, S, tau2 in problems:
            print(f"    ({tau1}, ?, {tau1}, {S}, {tau2}, {S})"
                  f"  — no R makes this work")
        print()
    else:
        print("  No impossible mirror triangles found.\n")

    if partial:
        print(f"Restricted mirror triangles ({len(partial)}):")
        print("  Only some R values work:")
        for tau1, S, tau2, feasible in partial:
            print(f"    ({tau1}, ?, {tau1}, {S}, {tau2}, {S})"
                  f"  — feasible R: {feasible}")
        print()

    return problems, results


# =====================================================================
# PART 2: Why mirror triangles are impossible
# =====================================================================

def explain_po_exclusivity(nodes, ntype, rel):
    """
    Explain WHY (τ_A, R, τ_A, PO, σ, PO) is never in T(G):
    each σ node is PO to exactly one τ_A node.
    """
    print("=" * 72)
    print("WHY PO MIRROR TRIANGLES ARE IMPOSSIBLE")
    print("=" * 72)
    print()
    print("In the PO-incoherent model, each witness w_k is PO to exactly")
    print("one chain element d_{2k}. No two distinct τ_A nodes share a")
    print("PO-related σ witness. This is structural, not accidental:")
    print()
    print("  - w_k is PO to d_{2k} (by construction)")
    print("  - w_k is PP to d_i for i > 2k (forced by composition)")
    print("  - w_k is DR to d_i for i < 2k (backward branch choice)")
    print()

    # Show the PO connections
    ta_nodes = [n for n in nodes if ntype[n] == 'tA']
    sigma_nodes = [n for n in nodes if ntype[n] == 'sigma']

    print("PO connections (σ ↔ τ_A):")
    for w in sigma_nodes:
        po_partners = [d for d in ta_nodes if rel.get((w, d)) == PO]
        print(f"  {w}: PO to {po_partners}")

    print()
    print("Each σ node has EXACTLY ONE PO-connected τ_A node.")
    print("Therefore (τ_A, R, τ_A, PO, σ, PO) requires two distinct")
    print("τ_A nodes both PO to the same σ — impossible.")
    print()
    print("Similarly (σ, R, σ, PO, τ_A, PO) requires two distinct")
    print("σ nodes both PO to the same τ_A — also impossible.")
    print()


# =====================================================================
# PART 3: Unraveling simulation
# =====================================================================

def build_unraveling(cg_nodes, ntype, rel, blocked_node, blocker,
                     num_copies=2):
    """
    Build a tree unraveling with blocked copies.

    The blocked subtree is the set of nodes reachable from the blocker
    via existential witnesses. For simplicity, we identify the blocked
    subtree as [blocker, blocker's PP-child, blocker's PO-witness].

    Returns (elements, emap, etype, fixed_edges, cross_edges)
    where fixed_edges are parent-child, cross_edges need assignment.
    """
    # Identify blocker's subtree (nodes it generates witnesses for)
    # In our model: blocker = d6, subtree = {d6, d7, w3}
    blocker_idx = int(blocker[1:])
    subtree = [blocker]
    if f'd{blocker_idx + 1}' in cg_nodes:
        subtree.append(f'd{blocker_idx + 1}')
    witness_idx = blocker_idx // 2
    if f'w{witness_idx}' in cg_nodes:
        subtree.append(f'w{witness_idx}')

    print(f"  Blocked node: {blocked_node}, blocker: {blocker}")
    print(f"  Blocked subtree: {subtree}")

    # Build elements
    elements = list(cg_nodes)  # original nodes
    emap = {n: n for n in cg_nodes}
    etype = dict(ntype)

    for c in range(1, num_copies + 1):
        for n in subtree:
            name = f'{n}_c{c}'
            elements.append(name)
            emap[name] = n
            etype[name] = ntype[n]

    return elements, emap, etype, subtree


def check_map_based_assignment(elements, emap, etype, rel, T, cg_nodes):
    """
    Check if the map-based assignment ρ(a,b) = E(map(a), map(b))
    is T-closed. Report all triples whose triangle type is NOT in T.
    """
    print()
    print("=" * 72)
    print("MAP-BASED ASSIGNMENT T-CLOSURE CHECK")
    print("=" * 72)
    print()
    print("Assignment rule: ρ(a,b) = E(map(a), map(b)) when maps differ")
    print("For same-map pairs: relation is UNDEFINED (the gap)")
    print()

    violations = []
    same_map_triples = []

    for i, a in enumerate(elements):
        for j in range(i + 1, len(elements)):
            b = elements[j]
            for k in range(j + 1, len(elements)):
                c = elements[k]

                na, nb, nc = emap[a], emap[b], emap[c]

                # Skip if any pair has same map (can't assign)
                if na == nb or nb == nc or na == nc:
                    same_map_triples.append((a, b, c))
                    continue

                # All maps distinct: use E(map, map)
                r_ab = rel[(na, nb)]
                r_bc = rel[(nb, nc)]
                r_ac = rel[(na, nc)]

                for x, y, z, rxy, ryz, rxz in [
                    (a, b, c, r_ab, r_bc, r_ac),
                    (a, c, b, r_ac, rel[(nc, nb)], r_ab),
                    (b, a, c, rel[(nb, na)], r_ac, r_bc),
                    (b, c, a, r_bc, rel[(nc, na)], rel[(nb, na)]),
                    (c, a, b, rel[(nc, na)], r_ab, rel[(nc, nb)]),
                    (c, b, a, rel[(nc, nb)], rel[(nb, na)], rel[(nc, na)]),
                ]:
                    t = (etype[x], rxy, etype[y], ryz, etype[z], rxz)
                    if t not in T:
                        violations.append((x, y, z, t))

    if violations:
        print(f"VIOLATIONS: {len(violations)} triples with non-T triangle types")
        seen = set()
        for x, y, z, t in violations:
            if t not in seen:
                seen.add(t)
                print(f"  {format_tri(t)}")
                print(f"    e.g., ({x}, {y}, {z})")
    else:
        print("No violations for all-distinct-map triples. ✓")

    print(f"\n  Triples involving same-map pairs: {len(same_map_triples)}"
          f" (need separate analysis)")

    return violations, same_map_triples


def analyze_same_node_pairs(elements, emap, etype, rel, T, P, cg_nodes):
    """
    For each same-node pair, compute:
    1. Composition-feasible relations (from third elements with known rels)
    2. T-consistent relations (all triples have type in T)
    3. The intersection
    """
    print()
    print("=" * 72)
    print("SAME-NODE PAIR ANALYSIS")
    print("=" * 72)

    same_pairs = []
    for i, a in enumerate(elements):
        for j in range(i + 1, len(elements)):
            b = elements[j]
            if emap[a] == emap[b]:
                same_pairs.append((a, b))

    print(f"\nSame-node pairs: {len(same_pairs)}")

    all_resolvable = True
    pair_results = {}

    for a, b in same_pairs:
        n = emap[a]  # = emap[b]
        tau = etype[a]

        print(f"\n  ({a}, {b}) — both map to {n} (type {tau})")

        # Initial domain from P(G)
        initial_domain = set()
        for R in ALL_RELS:
            if (tau, R, tau) in P:
                initial_domain.add(R)
        print(f"    Initial domain (from P): {initial_domain}")

        # Composition constraints from all third elements
        comp_feasible = set(initial_domain)
        comp_details = {}

        for c in elements:
            if c == a or c == b:
                continue
            nc = emap[c]
            na, nb = emap[a], emap[b]

            if na == nc or nb == nc:
                # Third element also same-map with a or b — skip
                continue

            r_ac = rel[(na, nc)]
            r_cb = rel[(nc, nb)]

            allowed = comp(r_ac, r_cb)
            before = set(comp_feasible)
            comp_feasible &= allowed
            removed = before - comp_feasible
            if removed:
                comp_details[c] = (r_ac, r_cb, allowed, removed)

        print(f"    After composition: {comp_feasible}")
        if comp_details:
            for c, (r_ac, r_cb, allowed, removed) in sorted(
                    comp_details.items(), key=lambda x: x[0]):
                print(f"      via {c}: comp({r_ac}, {r_cb}) = "
                      f"{set(allowed)}, removed {removed}")

        # T-consistency check for each feasible R
        t_feasible = set()

        for R in comp_feasible:
            R_inv = inv(R)
            ok = True
            blocking_triples = []

            for c in elements:
                if c == a or c == b:
                    continue
                nc = emap[c]
                na, nb = emap[a], emap[b]

                if na == nc or nb == nc:
                    continue

                r_ac = rel[(na, nc)]
                r_bc = rel[(nb, nc)]
                r_ca = rel[(nc, na)]
                r_cb = rel[(nc, nb)]

                # Check all 6 orientations of (a, b, c)
                triangles = [
                    (etype[a], R, etype[b], r_bc, etype[c], r_ac),
                    (etype[a], r_ac, etype[c], r_cb, etype[b], R),
                    (etype[b], R_inv, etype[a], r_ac, etype[c], r_bc),
                    (etype[b], r_bc, etype[c], r_ca, etype[a], R_inv),
                    (etype[c], r_ca, etype[a], R, etype[b], r_cb),
                    (etype[c], r_cb, etype[b], R_inv, etype[a], r_ca),
                ]

                for t in triangles:
                    if t not in T:
                        ok = False
                        blocking_triples.append((c, t))

            if ok:
                t_feasible.add(R)
            else:
                print(f"    R={R} BLOCKED by T-closure:")
                seen_types = set()
                for c, t in blocking_triples:
                    if t not in seen_types:
                        seen_types.add(t)
                        print(f"      {format_tri(t)} via {c} "
                              f"(maps to {emap[c]})")

        print(f"    T-consistent: {t_feasible}")

        final = comp_feasible & t_feasible
        print(f"    FINAL (comp ∩ T-consistent): {final}")

        if not final:
            print(f"    *** NO VALID RELATION — GAP CONFIRMED ***")
            all_resolvable = False
        else:
            print(f"    ✓ Resolvable")

        pair_results[(a, b)] = final

    return all_resolvable, pair_results


# =====================================================================
# PART 4: Constraint network with arc-consistency
# =====================================================================

def run_arc_consistency(elements, emap, etype, rel, T, P, cg_nodes):
    """
    Build the full constraint network for the unraveling and run
    arc-consistency. Unlike the same-node analysis above (which uses
    the map-based assignment for distinct-map pairs), this treats
    ALL pairs as having disjunctive domains and checks whether
    arc-consistency preserves non-empty domains.
    """
    print()
    print("=" * 72)
    print("FULL CONSTRAINT NETWORK WITH ARC-CONSISTENCY")
    print("=" * 72)
    print()
    print("Instead of using the map-based assignment, treat ALL non-")
    print("parent-child pairs as having disjunctive domains from P(G).")
    print("Apply T-filtering then arc-consistency.")
    print()

    # Build initial domains
    domain = {}
    fixed = {}

    for i, a in enumerate(elements):
        for j in range(i + 1, len(elements)):
            b = elements[j]
            ta, tb = etype[a], etype[b]
            # Initial domain from P(G)
            d = set()
            for R in ALL_RELS:
                if (ta, R, tb) in P:
                    d.add(R)
            domain[(a, b)] = d
            # Inverse domain
            d_inv = set()
            for R in d:
                d_inv.add(inv(R))
            domain[(b, a)] = d_inv

    n_pairs = len(elements) * (len(elements) - 1) // 2
    print(f"  {len(elements)} elements, {n_pairs} pairs")

    # For distinct-map pairs that are parent-child, fix the edge
    # (We don't track tree structure here, so skip fixing for now
    #  and just use disjunctive domains throughout)

    # T-filtering: remove R from D(a,b) if some third element c
    # has no compatible (S, S') in D(b,c) x D(a,c) with triangle in T
    print("\n  Running T-filtering + arc-consistency...")

    changed = True
    iteration = 0
    while changed:
        changed = False
        iteration += 1
        for i, a in enumerate(elements):
            for j in range(i + 1, len(elements)):
                b = elements[j]
                to_remove_ab = set()
                to_remove_ba = set()

                for R in list(domain[(a, b)]):
                    R_inv = inv(R)
                    # For each third element c, check if SOME
                    # assignment to (b,c) and (a,c) puts the
                    # triangle type in T
                    for c in elements:
                        if c == a or c == b:
                            continue
                        # Need: exists S in D(b,c), S' in D(a,c)
                        # such that (tp(a), R, tp(b), S, tp(c), S') in T
                        found = False
                        for S in domain[(b, c)]:
                            for Sp in domain[(a, c)]:
                                t = (etype[a], R, etype[b], S,
                                     etype[c], Sp)
                                if t in T:
                                    found = True
                                    break
                            if found:
                                break
                        if not found:
                            to_remove_ab.add(R)
                            to_remove_ba.add(R_inv)
                            break

                if to_remove_ab:
                    domain[(a, b)] -= to_remove_ab
                    domain[(b, a)] -= to_remove_ba
                    changed = True

    print(f"  Converged after {iteration} iterations")

    # Check for empty domains
    empty = []
    narrowed = []
    for i, a in enumerate(elements):
        for j in range(i + 1, len(elements)):
            b = elements[j]
            d = domain[(a, b)]
            if not d:
                empty.append((a, b))
            elif len(d) < len([R for R in ALL_RELS
                               if (etype[a], R, etype[b]) in P]):
                narrowed.append((a, b, d))

    if empty:
        print(f"\n  EMPTY DOMAINS: {len(empty)}")
        for a, b in empty:
            print(f"    ({a}, {b}) [{emap[a]}→{emap[b]}]")
    else:
        print(f"\n  All domains non-empty after arc-consistency ✓")

    # Report same-node pair domains
    print(f"\n  Same-node pair domains after arc-consistency:")
    for i, a in enumerate(elements):
        for j in range(i + 1, len(elements)):
            b = elements[j]
            if emap[a] == emap[b]:
                print(f"    ({a}, {b}) [both → {emap[a]}]: "
                      f"{domain[(a, b)]}")

    # Report key cross-subtree domains (copy ↔ original witness)
    print(f"\n  Key cross-subtree domains (copy ↔ original witness):")
    for i, a in enumerate(elements):
        for j in range(i + 1, len(elements)):
            b = elements[j]
            na, nb = emap[a], emap[b]
            if na != nb and ('_c' in a or '_c' in b):
                # Is this a copy-to-witness edge?
                if (na.startswith('d') and nb.startswith('w')) or \
                   (nb.startswith('d') and na.startswith('w')):
                    orig_rel = rel.get((na, nb), '?')
                    d = domain[(a, b)]
                    marker = ""
                    if orig_rel not in d:
                        marker = f"  ← map-based {orig_rel} REMOVED"
                    print(f"    ({a}, {b}) [{na}→{nb}, "
                          f"map={orig_rel}]: {d}{marker}")

    return empty, domain


# =====================================================================
# PART 5: Composition consistency of the arc-consistent network
# =====================================================================

def check_composition_consistency(elements, emap, etype, domain):
    """
    After arc-consistency, check if the remaining domains are
    composition-consistent: for each triple (a,b,c) and each
    R in D(a,c), there exist S in D(a,b), T in D(b,c) with
    R in comp(S, T).
    """
    print()
    print("=" * 72)
    print("COMPOSITION CONSISTENCY CHECK")
    print("=" * 72)

    violations = 0
    for i, a in enumerate(elements):
        for j in range(i + 1, len(elements)):
            b = elements[j]
            for k in range(j + 1, len(elements)):
                c = elements[k]

                # Check: for each R in D(a,c), exists S in D(a,b),
                # T in D(b,c) with R in comp(S, T)
                for R in list(domain.get((a, c), set())):
                    found = False
                    for S in domain.get((a, b), set()):
                        for T in domain.get((b, c), set()):
                            if R in comp(S, T):
                                found = True
                                break
                        if found:
                            break
                    if not found:
                        violations += 1

    if violations == 0:
        print("  All triples composition-consistent ✓")
    else:
        print(f"  {violations} composition violations found")

    return violations


# =====================================================================
# MAIN
# =====================================================================

def main():
    print("=" * 72)
    print("INTRA-SUBTREE T-CLOSURE INVESTIGATION")
    print("PO-incoherent counterexample: ∃PO.A ∈ τ_A, ∀PO.¬A ∈ τ_B")
    print("=" * 72)

    # Build completion graph (d0..d7, w0..w3)
    # With TNbr blocking: d8 blocked by d6
    CG_CHAIN = 8
    cg_nodes, ntype, rel = build_completion_graph(CG_CHAIN)
    print(f"\nCompletion graph: {len(cg_nodes)} nodes "
          f"(chain d0..d{CG_CHAIN-1}, witnesses w0..w{(CG_CHAIN+1)//2-1})")

    # Compute T(G) and P(G)
    T = compute_T(cg_nodes, ntype, rel)
    P = compute_P(cg_nodes, ntype, rel)
    print(f"|T(G)| = {len(T)} triangle types")
    print(f"|P(G)| = {len(P)} pair-types")

    ntype_set = set(ntype.values())

    # Part 1: Mirror triangle analysis
    problems, mirror_results = analyze_mirror_triangles(T, ntype_set)

    # Part 2: Explain PO exclusivity
    explain_po_exclusivity(cg_nodes, ntype, rel)

    # Part 3: Build unraveling
    print("=" * 72)
    print("TREE UNRAVELING")
    print("=" * 72)

    blocked_node = 'd8'  # would be next τ_A node
    blocker = 'd6'       # TNbr-blocks d8
    elements, emap, etype, subtree = build_unraveling(
        cg_nodes, ntype, rel, blocked_node, blocker, num_copies=2
    )
    print(f"  Unraveling: {len(elements)} elements")

    # Part 3a: Check map-based T-closure
    violations, same_triples = check_map_based_assignment(
        elements, emap, etype, rel, T, cg_nodes
    )

    # Part 3b: Same-node pair analysis
    all_resolvable, pair_results = analyze_same_node_pairs(
        elements, emap, etype, rel, T, P, cg_nodes
    )

    # Part 4: Full constraint network
    empty, domain = run_arc_consistency(
        elements, emap, etype, rel, T, P, cg_nodes
    )

    # Part 5: Composition consistency
    comp_violations = check_composition_consistency(
        elements, emap, etype, domain
    )

    # =====================================================================
    # SUMMARY
    # =====================================================================
    print()
    print("=" * 72)
    print("SUMMARY")
    print("=" * 72)

    print(f"""
  1. MIRROR TRIANGLES: {len(problems)} impossible types found
     (τ_A, ?, τ_A, PO, σ, PO) and (σ, ?, σ, PO, τ_A, PO) are NEVER
     in T(G) because each σ witness is PO to exactly one τ_A node.

  2. MAP-BASED ASSIGNMENT: {"NOT T-closed" if not all_resolvable else "T-closed"}
     The assignment ρ(a,b) = E(map(a), map(b)) creates mirror triangles
     when two elements both map to a node that is PO to a witness.
     {"The same-node pairs have NO composition+T-consistent relation." if not all_resolvable else ""}

  3. CONSTRAINT NETWORK: {"All domains non-empty ✓" if not empty else f"{len(empty)} EMPTY domains"}
     After T-filtering + arc-consistency on the full disjunctive network,
     {"all domains remain non-empty." if not empty else "some domains are empty."}""")

    if not empty:
        print(f"""
  IMPLICATION: The map-based assignment in Lemma 5.5 is flawed (it is
  NOT T-closed for same-node pairs). However, the constraint network
  N_T with disjunctive domains DOES have non-empty domains after
  arc-consistency. The key mechanism: arc-consistency REMOVES the
  problematic PO relation from cross-subtree edges between copies
  and original witnesses, replacing it with DR or PPI.

  This suggests the proof can be REPAIRED: instead of constructing
  a specific T-closed solution, argue that the constraint network's
  domains are non-empty (via a model-existence argument or direct
  analysis), then appeal to full RCC5 tractability.

  The same-node pair issue is resolved by the network: it doesn't
  need a T-closed solution as an intermediate step — it only needs
  non-empty domains, which arc-consistency preserves because the
  domains contain relations consistent with the actual model.""")
    else:
        print("""
  IMPLICATION: The intra-subtree issue is a GENUINE GAP that cannot
  be resolved by arc-consistency alone. A fundamentally different
  approach to model construction may be needed.""")

    # Additional: verify with larger CG
    print()
    print("=" * 72)
    print("VERIFICATION WITH LARGER COMPLETION GRAPH")
    print("=" * 72)

    for cg_size in [10, 12]:
        cg_nodes2, ntype2, rel2 = build_completion_graph(cg_size)
        T2 = compute_T(cg_nodes2, ntype2, rel2)
        P2 = compute_P(cg_nodes2, ntype2, rel2)

        # Check if PO mirror triangle is ever in T
        found_po_mirror = False
        for R in ALL_RELS:
            if ('tA', R, 'tA', PO, 'sigma', PO) in T2:
                found_po_mirror = True
                break

        blocker2 = f'd{cg_size - 2}'
        elements2, emap2, etype2, _ = build_unraveling(
            cg_nodes2, ntype2, rel2,
            f'd{cg_size}', blocker2, num_copies=1
        )
        empty2, _ = run_arc_consistency(
            elements2, emap2, etype2, rel2, T2, P2, cg_nodes2
        )

        print(f"\n  CG size {cg_size}: PO mirror in T? {found_po_mirror}. "
              f"Empty domains after AC? {'YES' if empty2 else 'NO'}")


if __name__ == '__main__':
    main()
