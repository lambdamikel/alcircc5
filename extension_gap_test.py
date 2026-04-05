#!/usr/bin/env python3
"""
Test whether the extension step in the quasimodel Henkin construction
can fail for abstract quasimodels of ALCI_RCC5.

THE QUESTION:
Given m existing elements with a globally consistent atomic RCC5 network,
and m non-empty domains D_1,...,D_m ⊆ {DR,PO,PP,PPI} for edges to a new
element, if every triple (e_i, e_j, e_new) is individually satisfiable
(the (Q3) condition), does a GLOBAL assignment always exist?

If YES for all m: the extension gap in the decidability proof is closed.
If NO: the gap is real, and we exhibit a concrete counterexample.
"""

import sys
from itertools import product

# RCC5 base relations (between distinct elements)
DR, PO, PP, PPI = 'DR', 'PO', 'PP', 'PPI'
RELS = [DR, PO, PP, PPI]
INV = {DR: DR, PO: PO, PP: PPI, PPI: PP}

# RCC5 composition table (excluding EQ)
COMP = {
    (DR, DR): frozenset({DR, PO, PP, PPI}),
    (DR, PO): frozenset({DR, PO, PP}),
    (DR, PP): frozenset({DR, PO, PP}),
    (DR, PPI): frozenset({DR}),
    (PO, DR): frozenset({DR, PO, PPI}),
    (PO, PO): frozenset({DR, PO, PP, PPI}),
    (PO, PP): frozenset({PO, PP}),
    (PO, PPI): frozenset({DR, PO, PPI}),
    (PP, DR): frozenset({DR}),
    (PP, PO): frozenset({DR, PO, PP}),
    (PP, PP): frozenset({PP}),
    (PP, PPI): frozenset({DR, PO, PP, PPI}),
    (PPI, DR): frozenset({DR, PO, PPI}),
    (PPI, PO): frozenset({PO, PPI}),
    (PPI, PP): frozenset({PO, PP, PPI}),
    (PPI, PPI): frozenset({PPI}),
}


def comp(r, s):
    return COMP[(r, s)]


def is_consistent_triple(r12, r13, r23):
    """Check if atomic triple (r12, r13, r23) is composition-consistent."""
    return r13 in comp(r12, r23)


def enum_consistent_networks(m):
    """Enumerate all globally consistent atomic RCC5 networks on m nodes.

    Returns list of dicts {(i,j): relation} for 0 <= i < j < m.
    """
    pairs = [(i, j) for i in range(m) for j in range(i+1, m)]
    n_pairs = len(pairs)

    networks = []
    for assignment in product(RELS, repeat=n_pairs):
        edge = {}
        for idx, (i, j) in enumerate(pairs):
            edge[(i, j)] = assignment[idx]
            edge[(j, i)] = INV[assignment[idx]]

        # Check all triples
        ok = True
        for i in range(m):
            for j in range(i+1, m):
                for k in range(j+1, m):
                    rij = edge[(i, j)]
                    rik = edge[(i, k)]
                    rjk = edge[(j, k)]
                    if not (rik in comp(rij, rjk) and
                            rjk in comp(INV[rij], rik) and
                            rij in comp(rik, INV[rjk])):
                        ok = False
                        break
                if not ok:
                    break
            if not ok:
                break
        if ok:
            networks.append(edge)

    return networks


def check_pairwise_satisfiability(edge, domains, m):
    """Check (Q3) pairwise satisfiability.

    For each pair (i,j) among the m existing nodes, check that
    there exist S_i ∈ D_i, S_j ∈ D_j with S_i ∈ comp(R(i,j), S_j).
    """
    for i in range(m):
        for j in range(i+1, m):
            rij = edge[(i, j)]
            found = False
            for si in domains[i]:
                for sj in domains[j]:
                    if si in comp(rij, sj):
                        found = True
                        break
                if found:
                    break
            if not found:
                return False
    return True


def check_global_satisfiability(edge, domains, m):
    """Check if a global assignment S_1,...,S_m exists with
    S_i ∈ D_i and S_i ∈ comp(R(i,j), S_j) for all i ≠ j.
    """
    for assignment in product(*[list(d) for d in domains]):
        ok = True
        for i in range(m):
            for j in range(i+1, m):
                rij = edge[(i, j)]
                si, sj = assignment[i], assignment[j]
                if si not in comp(rij, sj):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True, assignment
    return False, None


def run_star_extension_test(m, verbose=False):
    """Test whether pairwise satisfiability implies global satisfiability
    for star extensions with m existing nodes.

    Returns list of counterexamples.
    """
    print(f"\n{'='*70}")
    print(f"Star Extension Test: m = {m} existing nodes")
    print(f"{'='*70}")

    # Enumerate consistent base networks
    networks = enum_consistent_networks(m)
    print(f"Consistent atomic networks on {m} nodes: {len(networks)}")

    # Non-empty subsets of RELS
    all_domains = []
    for mask in range(1, 16):  # 1..15
        d = frozenset(r for idx, r in enumerate(RELS) if mask & (1 << idx))
        all_domains.append(d)
    print(f"Non-empty domain options: {len(all_domains)}")
    print(f"Total cases: {len(networks)} × {len(all_domains)}^{m} = "
          f"{len(networks) * len(all_domains)**m:,}")

    counterexamples = []
    total_pairwise_sat = 0
    total_global_sat = 0
    total_checked = 0

    for net_idx, edge in enumerate(networks):
        for domain_combo in product(all_domains, repeat=m):
            domains = list(domain_combo)
            total_checked += 1

            if check_pairwise_satisfiability(edge, domains, m):
                total_pairwise_sat += 1
                glob_sat, assignment = check_global_satisfiability(edge, domains, m)
                if glob_sat:
                    total_global_sat += 1
                else:
                    # COUNTEREXAMPLE FOUND!
                    ce = {
                        'edge': dict(edge),
                        'domains': domains,
                        'm': m
                    }
                    counterexamples.append(ce)
                    if verbose or len(counterexamples) <= 5:
                        print(f"\n*** COUNTEREXAMPLE #{len(counterexamples)} ***")
                        print(f"  Base network:")
                        for i in range(m):
                            for j in range(i+1, m):
                                print(f"    R({i},{j}) = {edge[(i,j)]}")
                        print(f"  Domains:")
                        for i in range(m):
                            print(f"    D_{i} = {{{', '.join(sorted(domains[i]))}}}")
                        print(f"  Pairwise satisfiable: YES")
                        print(f"  Globally satisfiable: NO")
                        # Show which pairwise solutions exist
                        for i in range(m):
                            for j in range(i+1, m):
                                rij = edge[(i, j)]
                                sols = [(si, sj) for si in domains[i]
                                        for sj in domains[j]
                                        if si in comp(rij, sj)]
                                print(f"    Triple ({i},{j},new): "
                                      f"R={rij}, solutions: {sols}")

        if (net_idx + 1) % 50 == 0:
            print(f"  ... processed {net_idx+1}/{len(networks)} networks, "
                  f"{len(counterexamples)} counterexamples so far")

    print(f"\nResults for m={m}:")
    print(f"  Total cases checked:        {total_checked:>10,}")
    print(f"  Pairwise satisfiable:       {total_pairwise_sat:>10,}")
    print(f"  Globally satisfiable:       {total_global_sat:>10,}")
    print(f"  Pairwise but NOT global:    {len(counterexamples):>10,}")

    if counterexamples:
        print(f"\n  *** GAP IS REAL: {len(counterexamples)} counterexamples found ***")
    else:
        print(f"\n  *** NO COUNTEREXAMPLES: pairwise ⟹ global for m={m} ***")

    return counterexamples


def analyze_counterexample(ce):
    """Deep analysis of a counterexample."""
    edge = ce['edge']
    domains = ce['domains']
    m = ce['m']

    print(f"\n{'─'*70}")
    print(f"Detailed analysis of counterexample (m={m}):")
    print(f"{'─'*70}")

    print(f"\nBase network (existing elements):")
    for i in range(m):
        for j in range(i+1, m):
            print(f"  R({i},{j}) = {edge[(i,j)]}")

    print(f"\nDomains for edges to new element:")
    for i in range(m):
        print(f"  D_{i} = {{{', '.join(sorted(domains[i]))}}}")

    print(f"\nPairwise satisfiability (Q3 check):")
    for i in range(m):
        for j in range(i+1, m):
            rij = edge[(i, j)]
            sols = []
            for si in domains[i]:
                for sj in domains[j]:
                    if si in comp(rij, sj):
                        sols.append((si, sj))
            print(f"  ({i},{j}): R={rij}, "
                  f"solutions in D_{i}×D_{j}: {sols}")

    print(f"\nGlobal search (exhaustive):")
    for assignment in product(*[list(d) for d in domains]):
        violations = []
        for i in range(m):
            for j in range(i+1, m):
                rij = edge[(i, j)]
                si, sj = assignment[i], assignment[j]
                if si not in comp(rij, sj):
                    violations.append((i, j, si, sj, rij))
        status = "✓ CONSISTENT" if not violations else f"✗ {len(violations)} violations"
        print(f"  S = {assignment}: {status}")
        if violations:
            for (i, j, si, sj, rij) in violations[:2]:
                print(f"      {si} ∉ comp({rij}, {sj}) = {comp(rij, sj)}")

    # Path-consistency enforcement simulation
    print(f"\nPath-consistency enforcement simulation:")
    D = [set(d) for d in domains]
    changed = True
    iteration = 0
    while changed:
        changed = False
        iteration += 1
        for i in range(m):
            for j in range(m):
                if i == j:
                    continue
                rij = edge.get((i, j))
                if rij is None:
                    rij = INV[edge[(j, i)]]
                # Enforce: D_i ← D_i ∩ {si | ∃ sj ∈ D_j : si ∈ comp(rij, sj)}
                new_di = set()
                for si in D[i]:
                    for sj in D[j]:
                        if si in comp(rij, sj):
                            new_di.add(si)
                            break
                if new_di != D[i]:
                    removed = D[i] - new_di
                    print(f"  Iter {iteration}: D_{i} loses {removed} "
                          f"(via node {j}, R={rij})")
                    D[i] = new_di
                    changed = True
                    if not D[i]:
                        print(f"  *** D_{i} is EMPTY — enforcement failed! ***")
                        return

    print(f"  Fixed point after {iteration} iterations:")
    for i in range(m):
        print(f"    D_{i} = {{{', '.join(sorted(D[i]))}}}")
    if all(D[i] for i in range(m)):
        print(f"  All domains non-empty after enforcement.")
        # Re-check global satisfiability with refined domains
        glob, asgn = check_global_satisfiability(edge, D, m)
        if glob:
            print(f"  Globally satisfiable after enforcement: {asgn}")
        else:
            print(f"  STILL globally unsatisfiable after enforcement!")
            print(f"  *** This is a genuine counterexample to the extension claim ***")


def test_with_witness_constraint(m, verbose=False):
    """Like run_star_extension_test but with one edge fixed to a singleton
    (modeling the witness constraint D_k = {R} from the ∃-rule).
    """
    print(f"\n{'='*70}")
    print(f"Star Extension Test WITH Witness Constraint: m = {m}")
    print(f"  (one domain forced to be a singleton)")
    print(f"{'='*70}")

    networks = enum_consistent_networks(m)
    all_domains = []
    for mask in range(1, 16):
        d = frozenset(r for idx, r in enumerate(RELS) if mask & (1 << idx))
        all_domains.append(d)

    singleton_domains = [frozenset({r}) for r in RELS]

    counterexamples = []
    total_pairwise = 0
    total_global = 0

    for edge in networks:
        for witness_node in range(m):
            for witness_rel in RELS:
                for domain_combo in product(all_domains, repeat=m):
                    domains = list(domain_combo)
                    # Override witness node's domain
                    if witness_rel not in domains[witness_node]:
                        continue  # witness rel must be in original domain
                    domains[witness_node] = frozenset({witness_rel})

                    if check_pairwise_satisfiability(edge, domains, m):
                        total_pairwise += 1
                        glob_sat, _ = check_global_satisfiability(edge, domains, m)
                        if glob_sat:
                            total_global += 1
                        else:
                            counterexamples.append({
                                'edge': dict(edge),
                                'domains': domains,
                                'm': m,
                                'witness_node': witness_node,
                                'witness_rel': witness_rel
                            })
                            if len(counterexamples) <= 3:
                                print(f"\n*** COUNTEREXAMPLE #{len(counterexamples)} ***")
                                for i in range(m):
                                    for j in range(i+1, m):
                                        print(f"  R({i},{j})={edge[(i,j)]}", end="  ")
                                print()
                                for i in range(m):
                                    wm = " (WITNESS)" if i == witness_node else ""
                                    print(f"  D_{i}={set(domains[i])}{wm}")

    print(f"\nResults (m={m}, with witness constraint):")
    print(f"  Pairwise satisfiable: {total_pairwise}")
    print(f"  Globally satisfiable: {total_global}")
    print(f"  Counterexamples:      {len(counterexamples)}")
    return counterexamples


if __name__ == '__main__':
    # Start with smallest interesting case
    ce3 = run_star_extension_test(3)

    if ce3:
        # Analyze first few counterexamples
        for ce in ce3[:3]:
            analyze_counterexample(ce)
    else:
        print("\nm=3 clean. Trying m=4...")
        ce4 = run_star_extension_test(4)
        if ce4:
            for ce in ce4[:3]:
                analyze_counterexample(ce)
        else:
            print("\nm=4 clean. Trying m=5...")
            ce5 = run_star_extension_test(5)
            if ce5:
                for ce in ce5[:3]:
                    analyze_counterexample(ce)
            else:
                print("\n" + "="*70)
                print("ALL CLEAN through m=5!")
                print("Strong evidence that pairwise ⟹ global for RCC5.")
                print("The extension gap may be closable.")
                print("="*70)
