#!/usr/bin/env python3
"""
Verify Tri-neighborhood equivalence for the PO-incoherent counterexample.

For each pair of interior τ_A nodes (d4, d6, d8, ...), check that not only
Tri(x) = Tri(y), but also that for each (relation, type) pair, the set of
Tri-values among neighbors matches.

This verifies that the strengthened blocking condition (Michael Wessel's
suggestion) is also satisfied by the stabilized interior nodes.
"""

from extension_gap_checker import RELS, INV, COMP
from triangle_type_saturation_check import (
    build_full_model, compute_triangle_type_set
)

DR, PO, PP, PPI = 'DR', 'PO', 'PP', 'PPI'


def compute_tri_neighborhood_signature(node, nodes, ntype, rel, tri_sets):
    """
    Compute the Tri-neighborhood signature of a node:
    For each (relation R, type τ) pair, collect the SET of Tri-values
    among R-neighbors of type τ.

    Returns a frozenset of ((R, τ), frozenset_of_Tri_values) pairs.
    """
    from collections import defaultdict
    neighbor_tri = defaultdict(set)

    for b in nodes:
        if b == node:
            continue
        key = (rel[(node, b)], ntype[b])
        neighbor_tri[key].add(tri_sets[b])

    # Convert to a hashable signature
    sig = frozenset(
        (k, frozenset(v)) for k, v in neighbor_tri.items()
    )
    return sig


def main():
    print("=" * 72)
    print("TRI-NEIGHBORHOOD EQUIVALENCE CHECK")
    print("Strengthened blocking: Tri(x)=Tri(y) AND matching neighbor Tri sets")
    print("=" * 72)

    N = 24
    result = build_full_model(N)
    if result is None:
        print("Model inconsistent!")
        return

    nodes, ntype, rel = result
    print(f"\nModel: {N} chain elements, {(N+1)//2} witnesses")

    # Compute Tri sets for ALL nodes
    tri_sets = {}
    for n in nodes:
        tri_set = compute_triangle_type_set(n, nodes, ntype, rel)
        tri_sets[n] = frozenset(tri_set)

    # Compute Tri-neighborhood signatures for ALL nodes
    tri_nbr_sigs = {}
    for n in nodes:
        tri_nbr_sigs[n] = compute_tri_neighborhood_signature(
            n, nodes, ntype, rel, tri_sets
        )

    # Check τ_A nodes
    ta_nodes = [n for n in nodes if ntype[n] == 'tA' and n.startswith('d')]
    tb_nodes = [n for n in nodes if ntype[n] == 'tB' and n.startswith('d')]
    sigma_nodes = [n for n in nodes if ntype[n] == 'sigma']

    print(f"\n{'='*72}")
    print("τ_A NODES: Tri-neighborhood equivalence")
    print(f"{'='*72}")

    for i in range(len(ta_nodes)):
        d = ta_nodes[i]
        print(f"\n  {d}: Tri size = {len(tri_sets[d])}")

    print(f"\n  Pairwise comparison (= means Tri-nbr equivalent):")
    header = "        " + "".join(f"{d:>6}" for d in ta_nodes)
    print(header)
    for d1 in ta_nodes:
        row = f"  {d1:>4}  "
        for d2 in ta_nodes:
            if d1 == d2:
                row += f"{'·':>6}"
            elif (tri_sets[d1] == tri_sets[d2] and
                  tri_nbr_sigs[d1] == tri_nbr_sigs[d2]):
                row += f"{'=':>6}"
            elif tri_sets[d1] == tri_sets[d2]:
                row += f"{'T':>6}"  # Tri matches but nbr doesn't
            else:
                row += f"{'X':>6}"  # Tri doesn't match
        print(row)

    print(f"\n  Legend: = Tri-nbr equivalent, T = Tri match only, X = Tri differs")

    # Count how many pairs are Tri-equivalent but NOT Tri-nbr-equivalent
    tri_only = 0
    tri_nbr = 0
    for i in range(len(ta_nodes)):
        for j in range(i+1, len(ta_nodes)):
            d1, d2 = ta_nodes[i], ta_nodes[j]
            if tri_sets[d1] == tri_sets[d2]:
                if tri_nbr_sigs[d1] == tri_nbr_sigs[d2]:
                    tri_nbr += 1
                else:
                    tri_only += 1

    print(f"\n  τ_A pairs with Tri match only: {tri_only}")
    print(f"  τ_A pairs with full Tri-nbr equivalence: {tri_nbr}")

    # Same for τ_B
    print(f"\n{'='*72}")
    print("τ_B NODES: Tri-neighborhood equivalence")
    print(f"{'='*72}")

    header = "        " + "".join(f"{d:>6}" for d in tb_nodes)
    print(header)
    for d1 in tb_nodes:
        row = f"  {d1:>4}  "
        for d2 in tb_nodes:
            if d1 == d2:
                row += f"{'·':>6}"
            elif (tri_sets[d1] == tri_sets[d2] and
                  tri_nbr_sigs[d1] == tri_nbr_sigs[d2]):
                row += f"{'=':>6}"
            elif tri_sets[d1] == tri_sets[d2]:
                row += f"{'T':>6}"
            else:
                row += f"{'X':>6}"
        print(row)

    # Same for σ
    print(f"\n{'='*72}")
    print("σ NODES: Tri-neighborhood equivalence")
    print(f"{'='*72}")

    header = "        " + "".join(f"{w:>6}" for w in sigma_nodes)
    print(header)
    for w1 in sigma_nodes:
        row = f"  {w1:>4}  "
        for w2 in sigma_nodes:
            if w1 == w2:
                row += f"{'·':>6}"
            elif (tri_sets[w1] == tri_sets[w2] and
                  tri_nbr_sigs[w1] == tri_nbr_sigs[w2]):
                row += f"{'=':>6}"
            elif tri_sets[w1] == tri_sets[w2]:
                row += f"{'T':>6}"
            else:
                row += f"{'X':>6}"
        print(row)

    # Detailed analysis: for a Tri-matching pair that ISN'T Tri-nbr equivalent,
    # show what differs
    print(f"\n{'='*72}")
    print("DETAILED ANALYSIS: any Tri-matching pairs that fail Tri-nbr?")
    print(f"{'='*72}")

    found_gap = False
    for node_list, label in [(ta_nodes, "τ_A"), (tb_nodes, "τ_B"),
                              (sigma_nodes, "σ")]:
        for i in range(len(node_list)):
            for j in range(i+1, len(node_list)):
                d1, d2 = node_list[i], node_list[j]
                if (tri_sets[d1] == tri_sets[d2] and
                    tri_nbr_sigs[d1] != tri_nbr_sigs[d2]):
                    found_gap = True
                    print(f"\n  {label} pair ({d1}, {d2}): Tri matches but "
                          f"Tri-nbr DIFFERS")

                    # Find what differs
                    sig1 = dict(tri_nbr_sigs[d1])
                    sig2 = dict(tri_nbr_sigs[d2])
                    all_keys = set(sig1.keys()) | set(sig2.keys())
                    for k in sorted(all_keys):
                        v1 = sig1.get(k, frozenset())
                        v2 = sig2.get(k, frozenset())
                        if v1 != v2:
                            print(f"    Key {k}: {len(v1)} vs {len(v2)} "
                                  f"distinct Tri sets among neighbors")

    if not found_gap:
        print("\n  *** NO GAPS: every Tri-matching pair is also "
              "Tri-nbr equivalent ***")

    # Final summary
    print(f"\n{'='*72}")
    print("CONCLUSION")
    print(f"{'='*72}")

    # Check stabilization with the stronger condition
    stab_ta = None
    for i in range(len(ta_nodes) - 1):
        d1, d2 = ta_nodes[i], ta_nodes[i+1]
        if (tri_sets[d1] == tri_sets[d2] and
            tri_nbr_sigs[d1] == tri_nbr_sigs[d2]):
            stab_ta = ta_nodes[i]
            break

    stab_tb = None
    for i in range(len(tb_nodes) - 1):
        d1, d2 = tb_nodes[i], tb_nodes[i+1]
        if (tri_sets[d1] == tri_sets[d2] and
            tri_nbr_sigs[d1] == tri_nbr_sigs[d2]):
            stab_tb = tb_nodes[i]
            break

    stab_sig = None
    for i in range(len(sigma_nodes) - 1):
        d1, d2 = sigma_nodes[i], sigma_nodes[i+1]
        if (tri_sets[d1] == tri_sets[d2] and
            tri_nbr_sigs[d1] == tri_nbr_sigs[d2]):
            stab_sig = sigma_nodes[i]
            break

    if stab_ta:
        print(f"\n  τ_A Tri-nbr stabilizes at {stab_ta}")
    else:
        print(f"\n  τ_A Tri-nbr does NOT stabilize")

    if stab_tb:
        print(f"  τ_B Tri-nbr stabilizes at {stab_tb}")
    else:
        print(f"  τ_B Tri-nbr does NOT stabilize")

    if stab_sig:
        print(f"  σ Tri-nbr stabilizes at {stab_sig}")
    else:
        print(f"  σ Tri-nbr does NOT stabilize")

    if stab_ta and stab_tb and stab_sig:
        print(f"""
  The STRENGTHENED blocking condition (Tri-neighborhood equivalence)
  also stabilizes. This means:
  - Termination is preserved (stronger condition still matches)
  - Soundness is strengthened (copied neighbors also have matching
    Tri sets, so the T-closure argument works from every node's
    perspective, not just the blocked/blocker pair)
""")
    else:
        print(f"\n  The strengthened condition does NOT stabilize — "
              f"the weaker Tri(x)=Tri(y) condition is needed.")


if __name__ == '__main__':
    main()
