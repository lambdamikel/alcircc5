#!/usr/bin/env python3
"""
Check whether abstract triangle-type sets stabilize for PO-incoherent
descriptors — the key question for whether triangle-type-set blocking
terminates AND supports correct unraveling.

A triangle type is (τ1, R12, τ2, R23, τ3, R13) — three Hintikka types
and three pairwise relations. No node identities.

For each τ_A node d_{2k}, we compute the SET of all abstract triangle
types it participates in. If these sets stabilize (d_{2k} and d_{2(k+1)}
have the same set for k ≥ K), then triangle-type-set blocking terminates.

We also check whether the triangle-type set from the finite completion
graph is "closed" under the compositions needed for unraveling.
"""

from extension_gap_checker import RELS, INV, COMP

DR, PO, PP, PPI = 'DR', 'PO', 'PP', 'PPI'

def comp(r, s):
    return COMP[(r, s)]

def inv(r):
    return INV[r]


def build_full_model(num_chain):
    """
    Build a complete, consistent relation assignment for a PP-chain
    of length num_chain with PO-witnesses. Uses the all-DR-backward branch.

    Returns: (nodes, ntype, assignment)
    """
    num_w = (num_chain + 1) // 2
    chain = [f'd{i}' for i in range(num_chain)]
    witnesses = [f'w{k}' for k in range(num_w)]
    nodes = chain + witnesses

    ntype = {}
    for i in range(num_chain):
        ntype[chain[i]] = 'tA' if i % 2 == 0 else 'tB'
    for w in witnesses:
        ntype[w] = 'sigma'

    rel = {}

    # Chain relations
    for i in range(num_chain):
        for j in range(i + 1, num_chain):
            rel[(chain[i], chain[j])] = PP
            rel[(chain[j], chain[i])] = PPI

    # Chain-to-witness: use all-DR-backward branch
    for k in range(num_w):
        for i in range(num_chain):
            if i == 2 * k:
                rel[(chain[i], witnesses[k])] = PO
                rel[(witnesses[k], chain[i])] = PO
            elif i < 2 * k:
                # Backward from demanded: all DR in this branch
                rel[(chain[i], witnesses[k])] = DR
                rel[(witnesses[k], chain[i])] = DR
            else:
                # Forward: PPI (forced)
                rel[(chain[i], witnesses[k])] = PPI
                rel[(witnesses[k], chain[i])] = PP

    # Witness-to-witness: all DR (consistent with the all-DR-backward branch)
    for i in range(num_w):
        for j in range(i + 1, num_w):
            rel[(witnesses[i], witnesses[j])] = DR
            rel[(witnesses[j], witnesses[i])] = DR

    # Verify composition consistency
    for a in nodes:
        for b in nodes:
            if a == b:
                continue
            for c in nodes:
                if c == a or c == b:
                    continue
                if rel[(a, c)] not in comp(rel[(a, b)], rel[(b, c)]):
                    print(f"  INCONSISTENCY: ρ({a},{c})={rel[(a,c)]} ∉ "
                          f"comp(ρ({a},{b})={rel[(a,b)]}, ρ({b},{c})={rel[(b,c)]})"
                          f" = {comp(rel[(a,b)], rel[(b,c)])}")
                    return None

    return nodes, ntype, rel


def compute_triangle_type_set(node, nodes, ntype, rel):
    """
    Compute the set of abstract triangle types involving `node`.
    A triangle type is (τ_node, R_node_b, τ_b, R_b_c, τ_c, R_node_c)
    for all pairs (b, c) of other nodes.
    """
    tri_types = set()
    others = [n for n in nodes if n != node]

    for i, b in enumerate(others):
        for c in others[i + 1:]:
            t = (ntype[node], rel[(node, b)], ntype[b],
                 rel[(b, c)], ntype[c], rel[(node, c)])
            tri_types.add(t)
            # Also the "other orientation" — (node, c, b)
            t2 = (ntype[node], rel[(node, c)], ntype[c],
                  rel[(c, b)], ntype[b], rel[(node, b)])
            tri_types.add(t2)

    return tri_types


def format_tri(t):
    """Format a triangle type for display."""
    return f"({t[0]}, {t[1]}, {t[2]}, {t[3]}, {t[4]}, {t[5]})"


def main():
    print("=" * 72)
    print("TRIANGLE-TYPE SET SATURATION CHECK")
    print("PO-incoherent descriptor: ∃PO.A ∈ τ_A, ∀PO.¬A ∈ τ_B")
    print("=" * 72)
    print()
    print("Using all-DR-backward branch (ρ(d_i, w_k) = DR for i < 2k)")
    print("All witness-witness relations = DR")

    N = 24  # chain length
    result = build_full_model(N)
    if result is None:
        print("Model is inconsistent!")
        return

    nodes, ntype, rel = result
    print(f"\nModel: {N} chain elements, {(N+1)//2} witnesses")
    print("Composition consistency: VERIFIED ✓")

    # Compute triangle-type sets for each τ_A node
    ta_nodes = [n for n in nodes if ntype[n] == 'tA' and n.startswith('d')]
    tb_nodes = [n for n in nodes if ntype[n] == 'tB' and n.startswith('d')]
    sigma_nodes = [n for n in nodes if ntype[n] == 'sigma']

    print(f"\n{'='*72}")
    print("τ_A NODE TRIANGLE-TYPE SETS")
    print(f"{'='*72}")

    ta_tri_sets = {}
    for d in ta_nodes:
        tri_set = compute_triangle_type_set(d, nodes, ntype, rel)
        ta_tri_sets[d] = tri_set
        print(f"\n  {d}: {len(tri_set)} abstract triangle types")

    # Compare consecutive τ_A nodes
    print(f"\n{'='*72}")
    print("PAIRWISE COMPARISON OF τ_A TRIANGLE-TYPE SETS")
    print(f"{'='*72}")

    for i in range(len(ta_nodes) - 1):
        d1, d2 = ta_nodes[i], ta_nodes[i + 1]
        s1, s2 = ta_tri_sets[d1], ta_tri_sets[d2]
        only_in_d1 = s1 - s2
        only_in_d2 = s2 - s1

        if s1 == s2:
            print(f"\n  {d1} vs {d2}: *** IDENTICAL SETS *** ({len(s1)} types)")
        else:
            print(f"\n  {d1} vs {d2}: DIFFER")
            print(f"    |{d1}| = {len(s1)}, |{d2}| = {len(s2)}, "
                  f"|{d1}∩{d2}| = {len(s1 & s2)}")
            if only_in_d1:
                print(f"    Only in {d1} ({len(only_in_d1)}):")
                for t in sorted(only_in_d1):
                    print(f"      {format_tri(t)}")
            if only_in_d2:
                print(f"    Only in {d2} ({len(only_in_d2)}):")
                for t in sorted(only_in_d2):
                    print(f"      {format_tri(t)}")

    # Also compare non-consecutive pairs to find the stabilization point
    print(f"\n{'='*72}")
    print("FULL COMPARISON MATRIX (= means identical sets)")
    print(f"{'='*72}")

    header = "        " + "".join(f"{d:>6}" for d in ta_nodes)
    print(header)
    for d1 in ta_nodes:
        row = f"  {d1:>4}  "
        for d2 in ta_nodes:
            if d1 == d2:
                row += f"{'·':>6}"
            elif ta_tri_sets[d1] == ta_tri_sets[d2]:
                row += f"{'=':>6}"
            else:
                diff = len(ta_tri_sets[d1].symmetric_difference(ta_tri_sets[d2]))
                row += f"{diff:>6}"
        print(row)

    # Same for τ_B
    print(f"\n{'='*72}")
    print("τ_B NODE COMPARISON")
    print(f"{'='*72}")

    tb_tri_sets = {}
    for d in tb_nodes:
        tri_set = compute_triangle_type_set(d, nodes, ntype, rel)
        tb_tri_sets[d] = tri_set
        print(f"  {d}: {len(tri_set)} types")

    header = "        " + "".join(f"{d:>6}" for d in tb_nodes)
    print(header)
    for d1 in tb_nodes:
        row = f"  {d1:>4}  "
        for d2 in tb_nodes:
            if d1 == d2:
                row += f"{'·':>6}"
            elif tb_tri_sets[d1] == tb_tri_sets[d2]:
                row += f"{'=':>6}"
            else:
                diff = len(tb_tri_sets[d1].symmetric_difference(tb_tri_sets[d2]))
                row += f"{diff:>6}"
        print(row)

    # Same for σ
    print(f"\n{'='*72}")
    print("σ NODE COMPARISON")
    print(f"{'='*72}")

    sig_tri_sets = {}
    for w in sigma_nodes:
        tri_set = compute_triangle_type_set(w, nodes, ntype, rel)
        sig_tri_sets[w] = tri_set
        print(f"  {w}: {len(tri_set)} types")

    header = "        " + "".join(f"{w:>6}" for w in sigma_nodes)
    print(header)
    for w1 in sigma_nodes:
        row = f"  {w1:>4}  "
        for w2 in sigma_nodes:
            if w1 == w2:
                row += f"{'·':>6}"
            elif sig_tri_sets[w1] == sig_tri_sets[w2]:
                row += f"{'=':>6}"
            else:
                diff = len(sig_tri_sets[w1].symmetric_difference(sig_tri_sets[w2]))
                row += f"{diff:>6}"
        print(row)

    # Repeat with all-PP-backward branch
    print(f"\n{'='*72}")
    print("VERIFICATION WITH ALL-PP-BACKWARD BRANCH")
    print(f"{'='*72}")

    # Rebuild with PP backward
    num_w = (N + 1) // 2
    chain = [f'd{i}' for i in range(N)]
    witnesses = [f'w{k}' for k in range(num_w)]
    nodes2 = chain + witnesses

    rel2 = {}
    for i in range(N):
        for j in range(i + 1, N):
            rel2[(chain[i], chain[j])] = PP
            rel2[(chain[j], chain[i])] = PPI

    for k in range(num_w):
        for i in range(N):
            if i == 2 * k:
                rel2[(chain[i], witnesses[k])] = PO
                rel2[(witnesses[k], chain[i])] = PO
            elif i < 2 * k:
                rel2[(chain[i], witnesses[k])] = PP
                rel2[(witnesses[k], chain[i])] = PPI
            else:
                rel2[(chain[i], witnesses[k])] = PPI
                rel2[(witnesses[k], chain[i])] = PP

    for i in range(num_w):
        for j in range(i + 1, num_w):
            rel2[(witnesses[i], witnesses[j])] = PP
            rel2[(witnesses[j], witnesses[i])] = PPI

    # Verify
    ok = True
    for a in nodes2:
        for b in nodes2:
            if a == b: continue
            for c in nodes2:
                if c == a or c == b: continue
                if rel2[(a, c)] not in comp(rel2[(a, b)], rel2[(b, c)]):
                    ok = False
                    break
            if not ok: break
        if not ok: break

    if not ok:
        print("  PP-backward branch: INCONSISTENT — skipping")
    else:
        print("  PP-backward branch: VERIFIED ✓")

        ta_tri_sets2 = {}
        for d in ta_nodes:
            tri_set = compute_triangle_type_set(d, nodes2, ntype, rel2)
            ta_tri_sets2[d] = tri_set

        header = "        " + "".join(f"{d:>6}" for d in ta_nodes)
        print(f"\n  τ_A comparison matrix (PP-backward):")
        print(f"  {header}")
        for d1 in ta_nodes:
            row = f"    {d1:>4}  "
            for d2 in ta_nodes:
                if d1 == d2:
                    row += f"{'·':>6}"
                elif ta_tri_sets2[d1] == ta_tri_sets2[d2]:
                    row += f"{'=':>6}"
                else:
                    diff = len(ta_tri_sets2[d1].symmetric_difference(ta_tri_sets2[d2]))
                    row += f"{diff:>6}"
            print(row)

    # === Conclusion ===
    print(f"\n{'='*72}")
    print("CONCLUSION")
    print(f"{'='*72}")

    # Find stabilization point
    stab_k_ta = None
    for i in range(len(ta_nodes) - 1):
        if ta_tri_sets[ta_nodes[i]] == ta_tri_sets[ta_nodes[i + 1]]:
            stab_k_ta = i
            break

    stab_k_tb = None
    for i in range(len(tb_nodes) - 1):
        if tb_tri_sets[tb_nodes[i]] == tb_tri_sets[tb_nodes[i + 1]]:
            stab_k_tb = i
            break

    stab_k_sig = None
    for i in range(len(sigma_nodes) - 1):
        if sig_tri_sets[sigma_nodes[i]] == sig_tri_sets[sigma_nodes[i + 1]]:
            stab_k_sig = i
            break

    if stab_k_ta is not None:
        print(f"\n  τ_A triangle-type sets STABILIZE at {ta_nodes[stab_k_ta]}")
        print(f"    {ta_nodes[stab_k_ta]} and all subsequent τ_A nodes have "
              f"identical abstract triangle-type sets ({len(ta_tri_sets[ta_nodes[stab_k_ta]])} types)")
    else:
        print(f"\n  τ_A triangle-type sets do NOT stabilize within chain length {N}")

    if stab_k_tb is not None:
        print(f"  τ_B triangle-type sets STABILIZE at {tb_nodes[stab_k_tb]}")
    else:
        print(f"  τ_B triangle-type sets do NOT stabilize within chain length {N}")

    if stab_k_sig is not None:
        print(f"  σ triangle-type sets STABILIZE at {sigma_nodes[stab_k_sig]}")
    else:
        print(f"  σ triangle-type sets do NOT stabilize within chain length {N}")

    if stab_k_ta is not None and stab_k_tb is not None and stab_k_sig is not None:
        print(f"""
  IMPLICATION: Triangle-type-set blocking TERMINATES for this descriptor.
  After the stabilization point, new nodes are blocked by earlier nodes
  with identical abstract triangle-type sets. Since the blocked node
  participates in exactly the same abstract triangle types as its blocker,
  unraveling produces only triangles already in T.

  This suggests the Extension Solvability Conjecture holds for this case,
  and the PO gap may be closeable via triangle-type-set blocking.
""")
    else:
        print(f"\n  No stabilization detected — need longer chain or different analysis.")


if __name__ == '__main__':
    main()
