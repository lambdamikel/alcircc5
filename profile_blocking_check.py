#!/usr/bin/env python3
"""
Verify non-termination of profile blocking for PO-incoherent descriptors.

Setup:
  τ_A = {∃PP.⊤, ∃PO.A, A}     (chain positions 0, 2, 4, ...)
  τ_B = {∃PP.⊤, ∀PO.¬A}       (chain positions 1, 3, 5, ...)
  σ   = {A}                     (witness type)

Chain: d0(τA) PP d1(τB) PP d2(τA) PP d3(τB) PP d4(τA) PP ...
Each d_{2k} has PO-witness w_k with ρ(d_{2k}, w_k) = PO.

Type safety constraint: ∀PO.¬A ∈ τ_B and A ∈ σ imply ρ(d_i, w_k) ≠ PO
for every odd i (τ_B position) and every witness w_k.

The script:
1. Builds the constraint network for N chain elements + witnesses
2. Propagates composition + type safety via arc consistency
3. Enumerates ALL valid complete relation assignments
4. Verifies composition consistency of each solution
5. Checks whether any two same-type nodes share identical profiles
6. Simulates the step-by-step tableau with profile blocking
"""

import itertools
from extension_gap_checker import RELS, INV, COMP

DR, PO, PP, PPI = 'DR', 'PO', 'PP', 'PPI'

def comp(r, s):
    """Possible ρ(a,c) given ρ(a,b)=r, ρ(b,c)=s, for distinct elements."""
    return COMP[(r, s)]

def inv(r):
    return INV[r]


def build_network(num_chain):
    """
    Build and solve the full constraint network for a PP-chain of length
    num_chain with one PO-witness per τ_A node.

    Returns: (nodes, node_type, solutions)
      where each solution is a dict (node_i, node_j) → relation
    """
    num_witnesses = (num_chain + 1) // 2  # one per even position

    chain = [f'd{i}' for i in range(num_chain)]
    witnesses = [f'w{k}' for k in range(num_witnesses)]
    nodes = chain + witnesses

    # Node types
    ntype = {}
    for i in range(num_chain):
        ntype[chain[i]] = 'tA' if i % 2 == 0 else 'tB'
    for w in witnesses:
        ntype[w] = 'sigma'

    # Initialize domains: every directed pair gets full domain
    domains = {}
    for a in nodes:
        for b in nodes:
            if a != b:
                domains[(a, b)] = set(RELS)

    # --- Fixed constraints ---

    # Chain: d_i PP d_{i+1} for consecutive, and PP/PPI for all pairs by transitivity
    for i in range(num_chain):
        for j in range(i + 1, num_chain):
            domains[(chain[i], chain[j])] = {PP}
            domains[(chain[j], chain[i])] = {PPI}

    # Demanded: ρ(d_{2k}, w_k) = PO
    for k in range(num_witnesses):
        domains[(chain[2 * k], witnesses[k])] = {PO}
        domains[(witnesses[k], chain[2 * k])] = {PO}  # PO is self-inverse

    # Type safety: ∀PO.¬A ∈ τ_B, A ∈ σ → ρ(τ_B, σ) ≠ PO and ρ(σ, τ_B) ≠ PO
    for i in range(num_chain):
        if i % 2 == 1:  # τ_B
            for w in witnesses:
                domains[(chain[i], w)] -= {PO}
                domains[(w, chain[i])] -= {PO}

    # --- Arc consistency propagation ---
    def propagate():
        changed = True
        iterations = 0
        while changed:
            changed = False
            iterations += 1
            # Inverse consistency
            for a in nodes:
                for b in nodes:
                    if a == b:
                        continue
                    inv_dom = {inv(r) for r in domains[(b, a)]}
                    new_dom = domains[(a, b)] & inv_dom
                    if new_dom != domains[(a, b)]:
                        domains[(a, b)] = new_dom
                        changed = True

            # Composition consistency: for all triples (a, b, c),
            # ρ(a,c) must be in ∪_{r∈ρ(a,b), s∈ρ(b,c)} comp(r, s)
            for a in nodes:
                for c in nodes:
                    if a == c:
                        continue
                    for b in nodes:
                        if b == a or b == c:
                            continue
                        allowed = set()
                        for r in domains[(a, b)]:
                            for s in domains[(b, c)]:
                                allowed |= comp(r, s)
                        new_dom = domains[(a, c)] & allowed
                        if new_dom != domains[(a, c)]:
                            domains[(a, c)] = new_dom
                            changed = True
        return iterations

    iters = propagate()

    # Check for empty domains
    for (a, b), dom in domains.items():
        if not dom:
            print(f"  INCONSISTENT: ρ({a},{b}) has empty domain!")
            return nodes, ntype, []

    # --- Report domains ---
    print(f"\n  Domains after {iters} iterations of arc consistency:")
    print(f"\n  Chain-to-witness relations:")
    header = "        " + "".join(f"{w:>10}" for w in witnesses)
    print(header)
    for d in chain:
        row = f"    {d:>4}"
        for w in witnesses:
            dom = domains[(d, w)]
            if len(dom) == 1:
                row += f"{'[' + list(dom)[0] + ']':>10}"
            else:
                row += f"{'{' + ','.join(sorted(dom)) + '}':>10}"
        print(row)

    if num_witnesses > 1:
        print(f"\n  Witness-to-witness relations:")
        for i in range(num_witnesses):
            for j in range(i + 1, num_witnesses):
                dom = domains[(witnesses[i], witnesses[j])]
                if len(dom) == 1:
                    s = f"[{list(dom)[0]}]"
                else:
                    s = "{" + ",".join(sorted(dom)) + "}"
                print(f"    ρ({witnesses[i]},{witnesses[j]}) = {s}")

    # --- Enumerate all valid complete assignments ---
    # Collect free variables (domain size > 1), only one direction per pair
    free_pairs = []
    for a in nodes:
        for b in nodes:
            if a < b and len(domains[(a, b)]) > 1:
                free_pairs.append((a, b))

    print(f"\n  Free variables: {len(free_pairs)}")
    for a, b in free_pairs:
        print(f"    ρ({a},{b}) ∈ {domains[(a,b)]}")

    free_doms = [sorted(domains[(a, b)]) for a, b in free_pairs]
    total_combos = 1
    for d in free_doms:
        total_combos *= len(d)
    print(f"  Combinations to check: {total_combos}")

    solutions = []
    for combo in itertools.product(*free_doms):
        # Build full assignment
        assign = {}
        for (a, b), val in zip(free_pairs, combo):
            assign[(a, b)] = val
            assign[(b, a)] = inv(val)
        # Fill in determined values
        for (a, b), dom in domains.items():
            if (a, b) not in assign:
                assert len(dom) == 1, f"ρ({a},{b}) not assigned but domain={dom}"
                assign[(a, b)] = list(dom)[0]

        # Verify full composition consistency
        valid = True
        for a in nodes:
            for b in nodes:
                if a == b:
                    continue
                for c in nodes:
                    if c == a or c == b:
                        continue
                    if assign[(a, c)] not in comp(assign[(a, b)], assign[(b, c)]):
                        valid = False
                        break
                if not valid:
                    break
            if not valid:
                break

        if valid:
            solutions.append(assign)

    print(f"  Valid solutions: {len(solutions)}")
    return nodes, ntype, solutions


def check_profiles(nodes, ntype, solutions):
    """Check whether any two same-type nodes have matching profiles."""
    any_match = False

    for type_name, type_code in [('τ_A', 'tA'), ('τ_B', 'tB'), ('σ', 'sigma')]:
        typed = [n for n in nodes if ntype[n] == type_code]
        if len(typed) < 2:
            continue

        print(f"\n  {type_name} nodes: {typed}")

        for sol_idx, sol in enumerate(solutions):
            for i, n1 in enumerate(typed):
                for n2 in typed[i + 1:]:
                    # Profile = relations to all nodes except n1 and n2
                    common = [e for e in nodes if e != n1 and e != n2]
                    p1 = tuple(sol[(n1, e)] for e in common)
                    p2 = tuple(sol[(n2, e)] for e in common)
                    if p1 == p2:
                        any_match = True
                        print(f"    *** MATCH: {n1} ≡ {n2} in solution {sol_idx + 1} ***")
                        for e, r1, r2 in zip(common, p1, p2):
                            print(f"      {e}: {n1}→{r1}  {n2}→{r2}")
                    else:
                        diffs = [(e, r1, r2) for e, r1, r2 in zip(common, p1, p2) if r1 != r2]
                        diff_str = ", ".join(f"{e}:{r1}≠{r2}" for e, r1, r2 in diffs)
                        tag = f"  (sol {sol_idx+1})" if len(solutions) > 1 else ""
                        print(f"    {n1} vs {n2}: DIFFER at {diff_str}{tag}")

    return any_match


def simulate_tableau(nodes, ntype, solutions):
    """
    Simulate the step-by-step tableau construction with profile blocking.
    Shows which nodes exist at each blocking check and why blocking fails.
    """
    print(f"\n  Simulating tableau construction (model-guided, profile blocking):")

    # Construction order: d0, w0, d1, d2, w1, d3, d4, w2, d5, ...
    chain_nodes = sorted([n for n in nodes if n.startswith('d')],
                         key=lambda x: int(x[1:]))
    witness_nodes = sorted([n for n in nodes if n.startswith('w')],
                           key=lambda x: int(x[1:]))

    # Build the creation order
    order = []
    num_chain = len(chain_nodes)
    num_w = len(witness_nodes)

    # d0 first, then w0, d1, then for each subsequent pair: d_{2k}, w_k, d_{2k+1}
    order.append('d0')
    if num_w > 0:
        order.append('w0')
    if num_chain > 1:
        order.append('d1')
    for k in range(1, num_w):
        if 2 * k < num_chain:
            order.append(f'd{2*k}')
        order.append(f'w{k}')
        if 2 * k + 1 < num_chain:
            order.append(f'd{2*k+1}')

    # Add any remaining chain nodes
    for d in chain_nodes:
        if d not in order:
            order.append(d)

    existing = []
    blocked_in_all = {}  # node → True if blocked in all solutions

    for node in order:
        existing_before = list(existing)
        existing.append(node)

        if not existing_before:
            print(f"\n    Create {node} ({ntype[node]}): root node")
            continue

        # Show relations to existing nodes
        print(f"\n    Create {node} ({ntype[node]})")

        # Check for same-type predecessors
        same_type = [e for e in existing_before if ntype[e] == ntype[node]]
        if not same_type:
            print(f"      No earlier {ntype[node]} node → not blockable")
            # Show key relations
            for sol in solutions[:1]:
                rels = {e: sol[(node, e)] for e in existing_before}
                print(f"      Relations: {rels}")
            continue

        # Check blocking in each solution
        print(f"      Profile blocking check vs {same_type}:")
        all_unblocked = True
        for sol_idx, sol in enumerate(solutions):
            for blocker in same_type:
                # Common nodes: all existing_before except the blocker
                common = [e for e in existing_before if e != blocker]
                p_new = tuple(sol[(node, e)] for e in common)
                p_blk = tuple(sol[(blocker, e)] for e in common)

                if p_new == p_blk:
                    all_unblocked = False
                    print(f"        *** BLOCKED by {blocker} in solution {sol_idx+1} ***")
                else:
                    diffs = [(e, sol[(node, e)], sol[(blocker, e)])
                             for e in common if sol[(node, e)] != sol[(blocker, e)]]
                    if sol_idx == 0 or len(solutions) <= 4:
                        diff_str = ", ".join(
                            f"{e}:{node}→{r1} vs {blocker}→{r2}"
                            for e, r1, r2 in diffs[:3])
                        print(f"        vs {blocker} (sol {sol_idx+1}): "
                              f"NOT blocked — {diff_str}")

        if all_unblocked:
            print(f"      → NOT BLOCKED in any of {len(solutions)} solution(s)")


def print_relation_table(nodes, ntype, sol, title=""):
    """Print a full relation table for one solution."""
    if title:
        print(f"\n  {title}")

    chain = sorted([n for n in nodes if n.startswith('d')],
                   key=lambda x: int(x[1:]))
    wits = sorted([n for n in nodes if n.startswith('w')],
                  key=lambda x: int(x[1:]))
    ordered = chain + wits

    w = 5
    print(f"    {'':>{w}}", end="")
    for n in ordered:
        print(f" {n:>{w}}", end="")
    print()

    for a in ordered:
        print(f"    {a:>{w}}", end="")
        for b in ordered:
            if a == b:
                print(f" {'·':>{w}}", end="")
            else:
                print(f" {sol[(a,b)]:>{w}}", end="")
        print(f"   ({ntype[a]})")


def main():
    print("=" * 72)
    print("PROFILE BLOCKING NON-TERMINATION VERIFICATION")
    print("PO-incoherent descriptor: ∃PO.A ∈ τ_A, ∀PO.¬A ∈ τ_B")
    print("=" * 72)
    print()
    print("Types:  τ_A = {∃PP.⊤, ∃PO.A, A}  (even chain positions)")
    print("        τ_B = {∃PP.⊤, ∀PO.¬A}    (odd chain positions)")
    print("        σ   = {A}                  (PO-witness type)")
    print()
    print("Constraint: ∀PO.¬A at τ_B + A at σ ⟹ ρ(τ_B-node, σ-node) ≠ PO")

    any_match_global = False

    for N in [4, 6, 8]:
        print(f"\n{'='*72}")
        print(f"CHAIN LENGTH {N}: d0..d{N-1} with {(N+1)//2} witnesses")
        print(f"{'='*72}")

        nodes, ntype, solutions = build_network(N)

        if not solutions:
            print("  No valid models found!")
            continue

        # Print first solution's relation table
        print_relation_table(nodes, ntype, solutions[0],
                             f"Relation table (solution 1 of {len(solutions)}):")

        # If multiple solutions, show how they differ
        if len(solutions) > 1:
            print(f"\n  All {len(solutions)} solutions differ only in:")
            for i, sol in enumerate(solutions):
                diffs = {}
                for (a, b), r in sol.items():
                    if a < b and r != solutions[0][(a, b)]:
                        diffs[(a, b)] = r
                if diffs:
                    print(f"    Solution {i+1}: " +
                          ", ".join(f"ρ({a},{b})={r}" for (a,b), r in sorted(diffs.items())))
                else:
                    print(f"    Solution {i+1}: (reference)")

        # Profile check
        print(f"\n  --- Profile comparison (all {len(solutions)} solutions) ---")
        match = check_profiles(nodes, ntype, solutions)
        if match:
            any_match_global = True

        # Tableau simulation
        print(f"\n  --- Tableau simulation ---")
        simulate_tableau(nodes, ntype, solutions)

    # === Conclusion ===
    print(f"\n{'='*72}")
    print("CONCLUSION")
    print(f"{'='*72}")
    if any_match_global:
        print("""
RESULT: Some same-type nodes have matching profiles in some valid models.
Profile blocking MIGHT terminate for these cases.
""")
    else:
        print("""
RESULT: In every valid model, no two same-type nodes share a profile.

The distinguishing mechanism:
  - d_{2k} is PO to w_k (demanded), but all other d_{2j} are forced to
    DR, PP, or PPI to w_k (never PO) by composition + type safety.
  - Forward: ρ(d_{2k+1}, w_k) ∈ comp(PPI, PO) = {PO, PPI};
    PO excluded by ∀PO.¬A → PPI. Then comp(PPI, PPI) = {PPI} forever.
  - Backward: ρ(d_{2k-1}, w_k) ∈ comp(PP, PO) = {DR, PO, PP};
    PO excluded by ∀PO.¬A → {DR, PP}. Then comp(PP, DR)={DR} or
    comp(PP, PP)={PP}: stays DR or PP backward, never PO.

Therefore, with profile blocking:
  → No τ_A node is ever blocked (each has PO to its own unique witness)
  → No τ_B node is ever blocked (different PP/PPI patterns to later nodes)
  → No σ node is ever blocked (different PO targets)
  → The completion graph grows without bound on a SATISFIABLE input
  → Profile blocking fails to terminate (completeness violation)
""")


if __name__ == '__main__':
    main()
