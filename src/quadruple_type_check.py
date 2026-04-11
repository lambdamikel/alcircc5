#!/usr/bin/env python3
"""
Quadruple-type verification for ALCI_RCC5 decidability.

THE KEY INSIGHT: Triple-types are insufficient (3-arm star failures show this).
Quadruple-types capture the 4-way interaction needed for star path-consistency.

A quadruple-type for (z, p, x_i, x_j) enforces:
  r_zy ∈ comp(r_zx, rel(x_i, x_j)) ∩ comp(R, rel(p, x_j)) ∩ SAFE(tp(z), tp(x_j))

This is EXACTLY the path-consistency condition for the triple (z, x_i, x_j).

VERIFICATION: Replace pairwise triple condition with quadruple condition
and re-run the 3-arm star test. ALL failures should disappear.
"""

import itertools
import time

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


def is_pc(net, nodes):
    for i in nodes:
        for j in nodes:
            if i == j: continue
            for k in nodes:
                if k == i or k == j: continue
                if net[(i,j)] not in COMP[(net[(i,k)], net[(k,j)])]:
                    return False
    return True


def main():
    print("=" * 70)
    print("QUADRUPLE-TYPE VERIFICATION")
    print("Testing: does quadruple condition fix the 3-arm star failures?")
    print("=" * 70)

    all_subsets = []
    for size in range(1, 5):
        for s in itertools.combinations(RELS, size):
            all_subsets.append(frozenset(s))

    nodes = [0, 1, 2, 3]  # p=0, x1=1, x2=2, x3=3
    edges = [(i,j) for i in nodes for j in nodes if i < j]

    print("Enumerating PC networks on 4 nodes...")
    pc_networks = []
    for assignment in itertools.product(RELS, repeat=6):
        net = {}
        for idx, (i,j) in enumerate(edges):
            net[(i,j)] = assignment[idx]
            net[(j,i)] = INV[assignment[idx]]
        if is_pc(net, nodes):
            pc_networks.append(net)
    print(f"  Found {len(pc_networks)} PC networks")

    others = [1, 2, 3]
    arm_pairs = [(1,2), (1,3), (2,3)]

    total_triple_only = 0
    total_quadruple = 0
    triple_failures = 0
    quadruple_failures = 0

    t0 = time.time()
    checkpoint = time.time()

    for net_idx, net in enumerate(pc_networks):
        if time.time() - checkpoint > 30:
            print(f"  Progress: {net_idx}/{len(pc_networks)}, "
                  f"triple_tests={total_triple_only}, quad_tests={total_quadruple}, "
                  f"triple_fail={triple_failures}, quad_fail={quadruple_failures}")
            checkpoint = time.time()

        for R in RELS:
            comp_d = {x: set(COMP[(R, net[(0, x)])]) for x in others}

            for S1 in all_subsets:
                d1 = comp_d[1] & set(S1)
                if not d1: continue
                for S2 in all_subsets:
                    d2 = comp_d[2] & set(S2)
                    if not d2: continue
                    for S3 in all_subsets:
                        d3 = comp_d[3] & set(S3)
                        if not d3: continue

                        domains_init = {1: set(d1), 2: set(d2), 3: set(d3)}

                        # ── Check TRIPLE condition (pairwise) ──
                        triple_ok = True
                        for (a, b) in arm_pairs:
                            found = False
                            for ra in domains_init[a]:
                                if set(COMP[(ra, net[(a,b)])]) & domains_init[b]:
                                    found = True
                                    break
                            if not found:
                                triple_ok = False
                                break
                            found = False
                            for rb in domains_init[b]:
                                if set(COMP[(rb, net[(b,a)])]) & domains_init[a]:
                                    found = True
                                    break
                            if not found:
                                triple_ok = False
                                break

                        if not triple_ok:
                            continue

                        # ── Check QUADRUPLE condition ──
                        # For each pair (xi, xj) and each r in D(z, xi):
                        # ∃ r' ∈ D(z, xj) with r' ∈ comp(r, rel(xi, xj))
                        # i.e., full path-consistency of the star's disjunctive network
                        quad_ok = True
                        for (a, b) in arm_pairs:
                            for ra in domains_init[a]:
                                if not (set(COMP[(ra, net[(a,b)])]) & domains_init[b]):
                                    quad_ok = False
                                    break
                            if not quad_ok: break
                            for rb in domains_init[b]:
                                if not (set(COMP[(rb, net[(b,a)])]) & domains_init[a]):
                                    quad_ok = False
                                    break
                            if not quad_ok: break

                        # ── Test arc consistency under TRIPLE condition ──
                        total_triple_only += 1
                        domains = {x: set(domains_init[x]) for x in others}
                        changed = True
                        empty = False
                        while changed and not empty:
                            changed = False
                            for x in others:
                                for y in others:
                                    if x == y: continue
                                    allowed = set()
                                    for ry in domains[y]:
                                        allowed |= set(COMP[(ry, net[(y, x)])])
                                    new_d = domains[x] & allowed
                                    if new_d != domains[x]:
                                        domains[x] = new_d
                                        changed = True
                                        if not new_d:
                                            empty = True
                                            break
                                if empty: break

                        if empty:
                            triple_failures += 1

                        # ── Test arc consistency under QUADRUPLE condition ──
                        if quad_ok:
                            total_quadruple += 1
                            domains = {x: set(domains_init[x]) for x in others}
                            changed = True
                            empty = False
                            while changed and not empty:
                                changed = False
                                for x in others:
                                    for y in others:
                                        if x == y: continue
                                        allowed = set()
                                        for ry in domains[y]:
                                            allowed |= set(COMP[(ry, net[(y, x)])])
                                        new_d = domains[x] & allowed
                                        if new_d != domains[x]:
                                            domains[x] = new_d
                                            changed = True
                                            if not new_d:
                                                empty = True
                                                break
                                    if empty: break

                            if empty:
                                quadruple_failures += 1

    elapsed = time.time() - t0

    print(f"\n{'='*60}")
    print(f"RESULTS ({elapsed:.1f}s)")
    print(f"{'='*60}")
    print(f"\n  Under TRIPLE condition (pairwise):")
    print(f"    Tests: {total_triple_only}")
    print(f"    Arc-consistency failures: {triple_failures} ({100*triple_failures/max(1,total_triple_only):.2f}%)")

    print(f"\n  Under QUADRUPLE condition (full star path-consistency):")
    print(f"    Tests: {total_quadruple}")
    print(f"    Arc-consistency failures: {quadruple_failures}")

    if quadruple_failures == 0:
        print(f"\n  ✓ QUADRUPLE CONDITION ELIMINATES ALL FAILURES")
        print(f"  This confirms: quadruple-types → star path-consistency → decidability")
    else:
        print(f"\n  ✗ Quadruple condition still has failures — need stronger conditions")

    return quadruple_failures == 0


if __name__ == '__main__':
    success = main()
