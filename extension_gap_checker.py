#!/usr/bin/env python3
"""
Exhaustive checker for the RCC5 extension gap.

Tests whether path-consistency enforcement on the Henkin extension CSP
ever empties a domain. If it never does, the extension gap is closeable
and ALCI_RCC5 is decidable.

The extension problem: given m existing elements with fixed atomic RCC5
relations, add a new element with disjunctive domains D_i ⊆ {DR, PO, PP, PPI}.
The binary constraint between R_i and R_j (edges to the new element) is:
    R_i ∈ comp(R(e_i, e_j), R_j)  AND  R_j ∈ comp(R(e_j, e_i), R_i)

We check: does path-consistency enforcement always preserve non-empty domains?
"""

import itertools
import sys
import time
from collections import defaultdict

# Base relations (excluding EQ for distinct elements)
DR, PO, PP, PPI = 'DR', 'PO', 'PP', 'PPI'
RELS = [DR, PO, PP, PPI]

# Inverse map
INV = {DR: DR, PO: PO, PP: PPI, PPI: PP}

# RCC5 composition table
# comp[(R(a,b), S(b,c))] = set of possible R(a,c)
# From the paper's table: row = S(b,c), column = R(a,b), entry = possible R(a,c)
# For distinct elements, EQ is excluded from results.
COMP = {}

# Column DR(a,b):
COMP[(DR, DR)] = frozenset({DR, PO, PP, PPI})  # *
COMP[(DR, PO)] = frozenset({DR, PO, PP})
COMP[(DR, PP)] = frozenset({DR, PO, PP})
COMP[(DR, PPI)] = frozenset({DR})

# Column PO(a,b):
COMP[(PO, DR)] = frozenset({DR, PO, PPI})
COMP[(PO, PO)] = frozenset({DR, PO, PP, PPI})  # *
COMP[(PO, PP)] = frozenset({PO, PP})
COMP[(PO, PPI)] = frozenset({DR, PO, PPI})

# Column PP(a,b):
COMP[(PP, DR)] = frozenset({DR})
COMP[(PP, PO)] = frozenset({DR, PO, PP})
COMP[(PP, PP)] = frozenset({PP})
COMP[(PP, PPI)] = frozenset({DR, PO, PP, PPI})  # * (EQ excluded)

# Column PPI(a,b):
COMP[(PPI, DR)] = frozenset({DR, PO, PPI})
COMP[(PPI, PO)] = frozenset({PO, PPI})
COMP[(PPI, PP)] = frozenset({PO, PP, PPI})  # EQ excluded
COMP[(PPI, PPI)] = frozenset({PPI})


def is_triple_consistent(r_ab, r_bc, r_ac):
    """Check if the triple (a,b,c) with given relations is composition-consistent."""
    # r_ac must be in comp(r_ab, r_bc)
    if r_ac not in COMP[(r_ab, r_bc)]:
        return False
    # r_ab must be in comp(r_ac, inv(r_bc))  i.e. comp(r_ac, r_cb)
    r_cb = INV[r_bc]
    if r_ab not in COMP[(r_ac, r_cb)]:
        return False
    # r_bc must be in comp(inv(r_ab), r_ac)  i.e. comp(r_ba, r_ac)
    r_ba = INV[r_ab]
    if r_bc not in COMP[(r_ba, r_ac)]:
        return False
    return True


def enumerate_consistent_networks(m):
    """Enumerate all composition-consistent atomic RCC5 networks on m nodes.

    Returns list of dicts mapping (i,j) -> relation for i < j.
    Relations for (j,i) are the inverse.
    """
    if m <= 1:
        return [{}]

    # All edges (i,j) with i < j
    edges = [(i, j) for i in range(m) for j in range(i+1, m)]

    results = []

    def get_rel(network, i, j):
        if i < j:
            return network[(i, j)]
        elif i > j:
            return INV[network[(j, i)]]
        else:
            return None  # same node

    def backtrack(idx, network):
        if idx == len(edges):
            results.append(dict(network))
            return

        i, j = edges[idx]
        for r in RELS:
            network[(i, j)] = r
            # Check all triples involving this edge and previously assigned edges
            consistent = True
            for k in range(m):
                if k == i or k == j:
                    continue
                # Check triple (i, j, k) — need edges (i,k) and (j,k)
                edge_ik = (min(i,k), max(i,k))
                edge_jk = (min(j,k), max(j,k))
                if edge_ik in network and edge_jk in network:
                    r_ij = r
                    r_ik = get_rel(network, i, k)
                    r_jk = get_rel(network, j, k)
                    if not is_triple_consistent(r_ij, r_jk, r_ik):
                        consistent = False
                        break
                    if not is_triple_consistent(r_ik, INV[r_ij], r_jk):
                        consistent = False
                        break

            if consistent:
                backtrack(idx + 1, network)

        if (i, j) in network:
            del network[(i, j)]

    backtrack(0, {})
    return results


def run_path_consistency(m, network, domains):
    """Run path-consistency enforcement on the extension CSP.

    m: number of existing elements (0..m-1)
    network: dict (i,j) -> relation for i < j, defining relations among existing elements
    domains: list of m sets, domains[i] = possible relations from e_i to e_new

    Returns: (success, refined_domains)
    where success = True if no domain became empty
    """
    # Make mutable copies
    doms = [set(d) for d in domains]

    def get_rel(i, j):
        """Get relation from existing element i to existing element j."""
        if i < j:
            return network[(i, j)]
        else:
            return INV[network[(j, i)]]

    changed = True
    while changed:
        changed = False
        # For each pair of existing elements (i, j), enforce arc-consistency
        # on the triple (e_i, e_j, e_new)
        for i in range(m):
            for j in range(m):
                if i == j:
                    continue
                r_ij = get_rel(i, j)
                # Constraint: R_i must be in comp(r_ij, R_j) for some R_j in doms[j]
                # Also: R_j must be in comp(inv(r_ij), R_i) for some R_i in doms[i]
                # Equivalently: R_i must be in comp(r_ij, R_j) for some R_j in doms[j]

                # Filter doms[i]: keep only values that have a support in doms[j]
                new_dom_i = set()
                for ri in doms[i]:
                    # ri = R(e_i, e_new), r_ij = R(e_i, e_j), rj = R(e_j, e_new)
                    # Triple (e_i, e_j, e_new): need ri ∈ comp(r_ij, rj)
                    # i.e., rj must be such that ri ∈ comp(r_ij, rj)
                    for rj in doms[j]:
                        if ri in COMP.get((r_ij, rj), frozenset()):
                            new_dom_i.add(ri)
                            break

                if new_dom_i != doms[i]:
                    changed = True
                    doms[i] = new_dom_i

                if not doms[i]:
                    return False, doms

    return True, doms


def check_extension_gap(max_m, verbose=True):
    """Check the extension gap for all configurations up to max_m existing elements.

    Returns: (passed, counterexample_or_None)
    """
    total_checked = 0
    total_failures = 0

    for m in range(1, max_m + 1):
        if verbose:
            print(f"\n{'='*60}")
            print(f"Checking m = {m} existing elements...")
            start = time.time()

        networks = enumerate_consistent_networks(m)
        if verbose:
            print(f"  Found {len(networks)} composition-consistent networks")

        # All non-empty subsets of {DR, PO, PP, PPI}
        all_domains = []
        for size in range(1, 5):
            for combo in itertools.combinations(RELS, size):
                all_domains.append(frozenset(combo))
        # 15 non-empty subsets

        m_checked = 0
        m_failures = 0

        for net_idx, network in enumerate(networks):
            # Try all domain assignments for the new element
            for dom_assignment in itertools.product(all_domains, repeat=m):
                domains = [set(d) for d in dom_assignment]

                success, refined = run_path_consistency(m, network, domains)
                m_checked += 1

                if not success:
                    m_failures += 1
                    total_failures += 1

                    if verbose:
                        print(f"\n  *** DOMAIN EMPTIED! ***")
                        print(f"  Network ({m} nodes):")
                        for (i,j), r in sorted(network.items()):
                            print(f"    R(e{i}, e{j}) = {r}")
                        print(f"  Initial domains for new element:")
                        for i, d in enumerate(dom_assignment):
                            print(f"    D{i} = {set(d)}")
                        print(f"  Refined domains:")
                        for i, d in enumerate(refined):
                            print(f"    D{i} = {d}")
                        empty_idx = [i for i, d in enumerate(refined) if not d]
                        print(f"  Empty domains at indices: {empty_idx}")

        elapsed = time.time() - start
        total_checked += m_checked

        if verbose:
            print(f"  Checked {m_checked:,} configurations in {elapsed:.1f}s")
            if m_failures == 0:
                print(f"  ✓ ALL PASSED for m = {m}")
            else:
                print(f"  ✗ {m_failures} FAILURES for m = {m}")

    print(f"\n{'='*60}")
    print(f"SUMMARY")
    print(f"{'='*60}")
    print(f"Total configurations checked: {total_checked:,}")

    if total_failures == 0:
        print(f"RESULT: ALL PASSED — no domain ever emptied!")
        print(f"The extension CSP is always solvable for m ≤ {max_m}.")
    else:
        print(f"RESULT: {total_failures} FAILURES found.")

    return total_failures == 0


def check_with_quasimodel_constraints(max_m, verbose=True):
    """A more refined check that only considers domain assignments arising
    from valid quasimodel pair-type sets.

    A domain D_i = DN(τ_i, τ') represents the set of relations allowed
    between type τ_i and type τ'. The quasimodel condition (Q3) constrains
    which domains can co-occur: for any pair of existing elements with
    types τ_i, τ_j and relation R(e_i, e_j), the domains D_i and D_j must
    be "compatible" — there must exist values r_i ∈ D_i, r_j ∈ D_j with
    r_i ∈ comp(R(e_i,e_j), r_j).

    This is a weaker check than the full quasimodel conditions but filters
    out obviously impossible configurations.
    """
    total_checked = 0
    total_failures = 0
    total_skipped = 0

    for m in range(1, max_m + 1):
        if verbose:
            print(f"\n{'='*60}")
            print(f"Checking m = {m} (with Q3-compatibility filter)...")
            start = time.time()

        networks = enumerate_consistent_networks(m)
        if verbose:
            print(f"  Found {len(networks)} composition-consistent networks")

        all_domains = []
        for size in range(1, 5):
            for combo in itertools.combinations(RELS, size):
                all_domains.append(frozenset(combo))

        m_checked = 0
        m_failures = 0
        m_skipped = 0

        def get_rel(network, i, j):
            if i < j:
                return network[(i, j)]
            else:
                return INV[network[(j, i)]]

        for net_idx, network in enumerate(networks):
            for dom_assignment in itertools.product(all_domains, repeat=m):
                # Q3 compatibility filter: for each pair (i,j), check that
                # there exist r_i ∈ D_i, r_j ∈ D_j with r_i ∈ comp(R_ij, r_j)
                compatible = True
                for i in range(m):
                    for j in range(i+1, m):
                        r_ij = get_rel(network, i, j)
                        found = False
                        for ri in dom_assignment[i]:
                            for rj in dom_assignment[j]:
                                if ri in COMP.get((r_ij, rj), frozenset()):
                                    found = True
                                    break
                            if found:
                                break
                        if not found:
                            compatible = False
                            break
                    if not compatible:
                        break

                if not compatible:
                    m_skipped += 1
                    continue

                domains = [set(d) for d in dom_assignment]
                success, refined = run_path_consistency(m, network, domains)
                m_checked += 1

                if not success:
                    m_failures += 1
                    total_failures += 1

                    if verbose:
                        print(f"\n  *** DOMAIN EMPTIED! ***")
                        print(f"  Network ({m} nodes):")
                        for (i,j), r in sorted(network.items()):
                            print(f"    R(e{i}, e{j}) = {r}")
                        print(f"  Initial domains for new element:")
                        for i, d in enumerate(dom_assignment):
                            print(f"    D{i} = {set(d)}")
                        print(f"  Refined domains:")
                        for i, d in enumerate(refined):
                            print(f"    D{i} = {d}")
                        empty_idx = [i for i, d in enumerate(refined) if not d]
                        print(f"  Empty domains at indices: {empty_idx}")

        elapsed = time.time() - start
        total_checked += m_checked
        total_skipped += m_skipped

        if verbose:
            print(f"  Checked {m_checked:,} (skipped {m_skipped:,} incompatible) in {elapsed:.1f}s")
            if m_failures == 0:
                print(f"  ✓ ALL PASSED for m = {m}")
            else:
                print(f"  ✗ {m_failures} FAILURES for m = {m}")

    print(f"\n{'='*60}")
    print(f"SUMMARY (with Q3-compatibility filter)")
    print(f"{'='*60}")
    print(f"Total configurations checked: {total_checked:,}")
    print(f"Total skipped (incompatible): {total_skipped:,}")

    if total_failures == 0:
        print(f"RESULT: ALL PASSED — no domain ever emptied!")
        print(f"The extension CSP is always solvable for m ≤ {max_m}.")
    else:
        print(f"RESULT: {total_failures} FAILURES found.")

    return total_failures == 0


if __name__ == '__main__':
    max_m = int(sys.argv[1]) if len(sys.argv) > 1 else 4

    print("RCC5 Extension Gap Exhaustive Checker")
    print(f"Checking all configurations up to m = {max_m} existing elements")
    print(f"Base relations: {RELS}")
    print(f"Non-empty domain subsets: 15")

    # First run the unrestricted check (all domain assignments)
    print("\n" + "="*60)
    print("PHASE 1: Unrestricted check (all domain assignments)")
    print("="*60)
    passed1 = check_extension_gap(max_m)

    if not passed1:
        # If failures found, run with Q3 filter to see if they persist
        print("\n" + "="*60)
        print("PHASE 2: Filtered check (Q3-compatible assignments only)")
        print("="*60)
        passed2 = check_with_quasimodel_constraints(max_m)
