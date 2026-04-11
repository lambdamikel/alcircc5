#!/usr/bin/env python3
"""
Extension gap checker v2: tests whether the UNIVERSAL Q3 (algebraic closure)
eliminates all failures.

Key theoretical insight:
- Existential Q3: for R_ij, SOME r_j has comp(R_ij, r_j) ∩ D_i ≠ ∅
- Universal Q3: for R_ij, ALL r_j have comp(R_ij, r_j) ∩ D_i ≠ ∅
  (= arc-consistency of the extension CSP)

If the universal Q3 eliminates all failures, then:
  Universal Q3 → arc-consistent extension CSP → path-consistent (for RCC5) → satisfiable

The remaining question: does model-derived quasimodel satisfy universal Q3?
"""

import itertools
import sys
import time
from extension_gap_checker import (
    RELS, INV, COMP, is_triple_consistent,
    enumerate_consistent_networks, run_path_consistency
)


def check_universal_q3(m, network, domains):
    """Check if the universal Q3 (algebraic closure) holds for all pairs.

    For each pair (i,j) with relation R_ij:
      For ALL r_j in D_j: comp(R_ij, r_j) ∩ D_i ≠ ∅
      For ALL r_i in D_i: comp(inv(R_ij), r_i) ∩ D_j ≠ ∅
    """
    def get_rel(i, j):
        if i < j:
            return network[(i, j)]
        else:
            return INV[network[(j, i)]]

    for i in range(m):
        for j in range(i+1, m):
            r_ij = get_rel(i, j)
            r_ji = INV[r_ij]

            # Check: for all r_j in D_j, comp(R_ij, r_j) ∩ D_i ≠ ∅
            for rj in domains[j]:
                if not (COMP.get((r_ij, rj), frozenset()) & domains[i]):
                    return False

            # Check: for all r_i in D_i, comp(R_ji, r_i) ∩ D_j ≠ ∅
            for ri in domains[i]:
                if not (COMP.get((r_ji, ri), frozenset()) & domains[j]):
                    return False

    return True


def check_existential_q3(m, network, domains):
    """Check the existential Q3 (weaker): for each pair, SOME compatible values exist."""
    def get_rel(i, j):
        if i < j:
            return network[(i, j)]
        else:
            return INV[network[(j, i)]]

    for i in range(m):
        for j in range(i+1, m):
            r_ij = get_rel(i, j)
            found = False
            for ri in domains[i]:
                for rj in domains[j]:
                    if ri in COMP.get((r_ij, rj), frozenset()):
                        found = True
                        break
                if found:
                    break
            if not found:
                return False
    return True


def main(max_m):
    print("RCC5 Extension Gap Checker v2")
    print(f"Testing existential vs universal Q3 up to m = {max_m}")
    print()

    all_domains = []
    for size in range(1, 5):
        for combo in itertools.combinations(RELS, size):
            all_domains.append(frozenset(combo))

    for m in range(2, max_m + 1):
        print(f"{'='*60}")
        print(f"m = {m} existing elements")
        start = time.time()

        networks = enumerate_consistent_networks(m)
        print(f"  {len(networks)} composition-consistent networks")

        # Counters
        total = 0
        fail_no_filter = 0
        fail_exist_q3 = 0  # fails AC but passes existential Q3
        fail_univ_q3 = 0   # fails AC but passes universal Q3
        pass_all = 0

        for network in networks:
            for dom_tuple in itertools.product(all_domains, repeat=m):
                domains_frozen = [frozenset(d) for d in dom_tuple]
                total += 1

                # Run path-consistency (actually arc-consistency)
                success, _ = run_path_consistency(m, network, [set(d) for d in dom_tuple])

                if success:
                    pass_all += 1
                    continue

                # It failed. Check which Q3 it satisfies:
                fail_no_filter += 1

                exist_ok = check_existential_q3(m, network, domains_frozen)
                univ_ok = check_universal_q3(m, network, domains_frozen)

                if exist_ok:
                    fail_exist_q3 += 1
                if univ_ok:
                    fail_univ_q3 += 1

                    # This would be a critical finding: universal Q3 passed but AC failed
                    print(f"\n  *** UNIVERSAL Q3 PASSED BUT AC FAILED ***")
                    print(f"  Network:")
                    for (i,j), r in sorted(network.items()):
                        print(f"    R(e{i}, e{j}) = {r}")
                    print(f"  Domains: {[set(d) for d in dom_tuple]}")

        elapsed = time.time() - start
        print(f"  Total: {total:,} | Pass: {pass_all:,} | Fail: {fail_no_filter:,}")
        print(f"  Failures passing existential Q3: {fail_exist_q3:,}")
        print(f"  Failures passing universal Q3:   {fail_univ_q3}")
        if fail_univ_q3 == 0:
            print(f"  ✓ Universal Q3 eliminates ALL failures at m={m}")
        else:
            print(f"  ✗ Universal Q3 does NOT eliminate all failures at m={m}")
        print(f"  Time: {elapsed:.1f}s")
        print()

    print("="*60)
    print("CONCLUSION")
    print("="*60)


if __name__ == '__main__':
    max_m = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    main(max_m)
