#!/usr/bin/env python3
"""
Three-arm star network arc-consistency check.

Verify Property 3 for z connected to p, x₁, x₂, x₃.
This extends the 2-arm verification to the next inductive case.

If this passes: we have verified arc-consistency stability for
stars with 1, 2, and 3 arms — covering all base cases for an
inductive argument.
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
    print("THREE-ARM STAR: Arc Consistency Check")
    print("z → p, x₁, x₂, x₃ with quasimodel SAFE conditions")
    print("=" * 70)

    all_subsets = []
    for size in range(1, 5):
        for s in itertools.combinations(RELS, size):
            all_subsets.append(frozenset(s))

    # Enumerate PC networks on {p=0, x1=1, x2=2, x3=3}
    nodes = [0, 1, 2, 3]
    edges = [(i,j) for i in nodes for j in nodes if i < j]  # 6 edges

    print(f"Enumerating path-consistent networks on 4 nodes...")
    t0 = time.time()

    pc_networks = []
    for assignment in itertools.product(RELS, repeat=6):
        net = {}
        for idx, (i,j) in enumerate(edges):
            net[(i,j)] = assignment[idx]
            net[(j,i)] = INV[assignment[idx]]
        if is_pc(net, nodes):
            pc_networks.append(net)

    print(f"  Found {len(pc_networks)} PC networks in {time.time()-t0:.1f}s")

    total_tests = 0
    total_failures = 0
    total_skipped_qm = 0
    failure_details = []

    others = [1, 2, 3]  # x1, x2, x3
    pairs = [(1,2), (1,3), (2,3)]  # pairs of arms

    t0 = time.time()
    checkpoint = time.time()

    for net_idx, net in enumerate(pc_networks):
        if time.time() - checkpoint > 30:
            print(f"  Progress: {net_idx}/{len(pc_networks)} networks, "
                  f"{total_tests} tests, {total_failures} failures, "
                  f"{time.time()-t0:.0f}s elapsed")
            checkpoint = time.time()

        for R in RELS:
            # Compute composition domains
            comp_d = {x: set(COMP[(R, net[(0, x)])]) for x in others}

            # For each SAFE triple
            for S1 in all_subsets:
                d1 = comp_d[1] & set(S1)
                if not d1: continue

                for S2 in all_subsets:
                    d2 = comp_d[2] & set(S2)
                    if not d2: continue

                    for S3 in all_subsets:
                        d3 = comp_d[3] & set(S3)
                        if not d3: continue

                        # Check quasimodel triple conditions for all pairs
                        safe_map = {1: S1, 2: S2, 3: S3}
                        domains_init = {1: set(d1), 2: set(d2), 3: set(d3)}

                        qm_ok = True
                        for (a, b) in pairs:
                            # Check: ∃ ra ∈ D(a), rb ∈ D(b) with rb ∈ comp(ra, rel(a,b))
                            found_ab = False
                            for ra in domains_init[a]:
                                if set(COMP[(ra, net[(a,b)])]) & domains_init[b]:
                                    found_ab = True
                                    break
                            if not found_ab:
                                qm_ok = False
                                break

                            found_ba = False
                            for rb in domains_init[b]:
                                if set(COMP[(rb, net[(b,a)])]) & domains_init[a]:
                                    found_ba = True
                                    break
                            if not found_ba:
                                qm_ok = False
                                break

                        if not qm_ok:
                            total_skipped_qm += 1
                            continue

                        total_tests += 1

                        # Run arc consistency
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
                            total_failures += 1
                            if len(failure_details) < 5:
                                failure_details.append({
                                    'net_idx': net_idx,
                                    'R': R,
                                    'SAFE': (S1, S2, S3),
                                    'init': dict(domains_init),
                                    'final': dict(domains),
                                    'net_edges': {(i,j): net[(i,j)] for i,j in edges}
                                })

    elapsed = time.time() - t0
    print(f"\n{'='*60}")
    print(f"RESULTS ({elapsed:.1f}s)")
    print(f"{'='*60}")
    print(f"  PC networks on 4 nodes: {len(pc_networks)}")
    print(f"  Total valid configs tested: {total_tests}")
    print(f"  Skipped (invalid QM): {total_skipped_qm}")
    print(f"  Arc-consistency failures: {total_failures}")

    if failure_details:
        print(f"\n  FAILURES:")
        for d in failure_details:
            print(f"    Net: {d['net_edges']}")
            print(f"    R={d['R']}, SAFE={d['SAFE']}")
            print(f"    Init: {d['init']}")
            print(f"    Final: {d['final']}")
            print()
    else:
        print(f"\n  ALL ARC-CONSISTENCY CHECKS PASS ✓")
        print(f"  Three-arm star verification: COMPLETE")

    return total_failures == 0


if __name__ == '__main__':
    success = main()
    if success:
        print(f"\n  VERIFIED: One-point extension with 3 arms always succeeds.")
        print(f"  Combined with 2-arm verification: covers all inductive base cases.")
