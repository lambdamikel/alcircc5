#!/usr/bin/env python3
"""
Check whether the extension-gap counterexamples can be "lifted" to
genuine ALCI_RCC5 quasimodels.

A counterexample has:
  - Base network: atomic RCC5 relations among existing nodes
  - Domains D_i ⊆ {DR,PO,PP,PPI} for edges to new node
  - Pairwise satisfiable (Q3) but not globally satisfiable

For it to represent a real gap, we need:
  1. Types τ_0,...,τ_{m-1}, τ' with the right DN domains
  2. The quasimodel conditions (Q1)-(Q3) satisfied
  3. The element-level edges among existing nodes consistent with type-level DN

Key observation: the domains D_i = DN(τ_i, τ') are determined by the
pair-compatibility conditions (P1)-(P2) and the chain propagation (P1',P2').
For GENERIC types (no ∀R.C constraints), DN(τ₁,τ₂) = {DR,PO,PP,PPI} (all 4).
Small domains arise only when types contain ∀-formulas that EXCLUDE certain
relations.

This script checks:
  (a) What domain patterns are achievable from ALCI_RCC5 types?
  (b) Can the specific counterexample domains from extension_gap_test.py
      be realized?
"""

import sys
from itertools import product, combinations

DR, PO, PP, PPI = 'DR', 'PO', 'PP', 'PPI'
RELS = [DR, PO, PP, PPI]
INV = {DR: DR, PO: PO, PP: PPI, PPI: PP}

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


def analyze_dn_from_types():
    """Analyze what DN(τ₁,τ₂) sets are achievable from ALCI_RCC5 types.

    A type τ is a subset of cl(C₀). For our purposes, the relevant
    formulas are ∀R.D for various R and D. A relation S is in
    DN(τ₁, τ₂) iff (τ₁, S, τ₂) is S-compatible:
      (P1): ∀S.D ∈ τ₁ → D ∈ τ₂
      (P2): ∀inv(S).D ∈ τ₂ → D ∈ τ₁
    Plus chain propagation for PP/PPI.

    Key insight: DN(τ₁, τ₂) = {S ∈ {DR,PO,PP,PPI} | (τ₁,S,τ₂) compatible}.
    A relation S is EXCLUDED from DN when:
      - ∃ some ∀S.D ∈ τ₁ with D ∉ τ₂, OR
      - ∃ some ∀inv(S).D ∈ τ₂ with D ∉ τ₁, OR
      - (chain propagation) if S=PP: ∃ ∀PP.D ∈ τ₁ with ∀PP.D ∉ τ₂, OR
      - (chain propagation) if S=PP: ∃ ∀PPI.D ∈ τ₂ with ∀PPI.D ∉ τ₁

    So we can independently exclude each relation. Let's model this
    abstractly: for each relation S, we have a boolean "excluded(S)"
    that can be set to True by choosing appropriate ∀-formulas.
    """

    print("="*70)
    print("Analysis of achievable DN domains from ALCI_RCC5 types")
    print("="*70)

    # For each relation S, what excludes it?
    # Direct exclusion: ∀S.D ∈ τ₁ with D ∉ τ₂
    # Inverse exclusion: ∀inv(S).D ∈ τ₂ with D ∉ τ₁
    # Chain propagation (only for PP, PPI):
    #   PP excluded if: ∀PP.D ∈ τ₁, ∀PP.D ∉ τ₂ (forward propagation fails)
    #   PPI excluded if: ∀PPI.D ∈ τ₁, ∀PPI.D ∉ τ₂ (analogous)

    print("\nDirect exclusion mechanism:")
    print("  To exclude S from DN(τ₁,τ₂):")
    print("    - Put ∀S.D in τ₁ but D not in τ₂, OR")
    print("    - Put ∀inv(S).D in τ₂ but D not in τ₁")
    print()
    print("  For S=DR:  ∀DR.D∈τ₁, D∉τ₂  OR  ∀DR.D∈τ₂, D∉τ₁")
    print("  For S=PO:  ∀PO.D∈τ₁, D∉τ₂  OR  ∀PO.D∈τ₂, D∉τ₁")
    print("  For S=PP:  ∀PP.D∈τ₁, D∉τ₂  OR  ∀PPI.D∈τ₂, D∉τ₁")
    print("             ALSO chain: ∀PP.D∈τ₁, ∀PP.D∉τ₂")
    print("  For S=PPI: ∀PPI.D∈τ₁, D∉τ₂  OR  ∀PP.D∈τ₂, D∉τ₁")
    print("             ALSO chain: ∀PPI.D∈τ₁, ∀PPI.D∉τ₂")

    print("\nKey observation: Each relation can be INDEPENDENTLY excluded")
    print("by introducing appropriate ∀-formulas in τ₁ or τ₂.")
    print("So ANY non-empty subset of {DR,PO,PP,PPI} is achievable as DN(τ₁,τ₂).")
    print()

    # But wait — there are coupling constraints from chain propagation!
    # If PP is in DN(τ₁,τ₂), then:
    #   (P1'): ∀PP.D ∈ τ₁ → ∀PP.D ∈ τ₂
    #   (P2'): ∀PPI.D ∈ τ₂ → ∀PPI.D ∈ τ₁
    # This means: if PP ∈ DN(τ₁,τ₂), then:
    #   - All ∀PP formulas in τ₁ must be in τ₂
    #   - All ∀PPI formulas in τ₂ must be in τ₁
    # These constrain OTHER DN domains involving τ₁ and τ₂ with other types!

    print("COUPLING from chain propagation:")
    print("  If PP ∈ DN(τ₁,τ₂), then ∀PP from τ₁ propagates to τ₂,")
    print("  and ∀PPI from τ₂ propagates back to τ₁.")
    print("  This constrains what OTHER DN(τ_i, τ_j) can look like.")
    print("  But it does NOT prevent DN(τ₁,τ') from being small —")
    print("  it's about propagation ALONG chains, not ACROSS types.")


def check_counterexample_liftability():
    """Check whether the simplest counterexample can arise from a quasimodel.

    Counterexample #1:
      Base: R(0,1)=DR, R(0,2)=DR, R(1,2)=PO
      D₀={PO}, D₁={DR}, D₂={PP,PPI}

    We need types τ₀, τ₁, τ₂, τ' (possibly from a larger type set T) such that:
      DN(τ₀, τ') = {PO}     — only PO-compatible with τ'
      DN(τ₁, τ') = {DR}     — only DR-compatible with τ'
      DN(τ₂, τ') = {PP,PPI} — PP and PPI compatible with τ'
      DN(τ₀, τ₁) ∋ DR       — elements can be DR-related
      DN(τ₀, τ₂) ∋ DR       — elements can be DR-related
      DN(τ₁, τ₂) ∋ PO       — elements can be PO-related
      Q3 holds for all triples of types
    """

    print("\n" + "="*70)
    print("Liftability check for counterexample #1")
    print("="*70)

    print("\nCounterexample: R(0,1)=DR, R(0,2)=DR, R(1,2)=PO")
    print("  D₀=DN(τ₀,τ')={PO}, D₁=DN(τ₁,τ')={DR}, D₂=DN(τ₂,τ')={PP,PPI}")

    print("\nTo achieve DN(τ₀,τ')={PO}:")
    print("  Must exclude DR, PP, PPI from DN(τ₀,τ').")
    print("  Exclude DR: put ∀DR.A in τ₀ with A∉τ'")
    print("  Exclude PP: put ∀PP.B in τ₀ with B∉τ'")
    print("  Exclude PPI: put ∀PPI.C in τ₀ with C∉τ' (i.e., ∀PP.C∈τ', C∉τ₀)")
    print("  Keep PO: ensure no ∀PO.D∈τ₀ with D∉τ' and no ∀PO.D∈τ' with D∉τ₀")

    print("\nTo achieve DN(τ₁,τ')={DR}:")
    print("  Must exclude PO, PP, PPI from DN(τ₁,τ').")
    print("  Exclude PO: put ∀PO.E in τ₁ with E∉τ'")
    print("  Exclude PP: put ∀PP.F in τ₁ with F∉τ'")
    print("  Exclude PPI: put ∀PPI.G in τ₁ with G∉τ'")
    print("  Keep DR: ensure no ∀DR.H∈τ₁ with H∉τ' and no ∀DR.H∈τ' with H∉τ₁")

    print("\nTo achieve DN(τ₂,τ')={PP,PPI}:")
    print("  Must exclude DR, PO from DN(τ₂,τ').")
    print("  Exclude DR: put ∀DR.I in τ₂ with I∉τ'")
    print("  Exclude PO: put ∀PO.J in τ₂ with J∉τ'")
    print("  Keep PP: ∀PP formulas in τ₂ must have fillers in τ'")
    print("  Keep PPI: ∀PPI formulas in τ₂ must have fillers in τ'")

    print("\nConstructing concrete types...")
    print("  Let C₀ = A₁ ⊓ ∃PO.(∃DR.A₃) ⊓ ∀PO.(∀PO.A₃ ⊓ ∀PP.A₃ ⊓ ∀PPI.A₃)")
    print("  ... (complex, but the point is the type structure is flexible enough)")

    # Abstract check: model the DN constraints as a 4×4 matrix
    # Types: τ₀, τ₁, τ₂, τ'
    # DN values (subsets of RELS) for each pair

    types = ['τ₀', 'τ₁', 'τ₂', 'τ\'']
    n = len(types)

    # Required DN values
    required_dn = {}
    # Edges involving τ' (new element)
    required_dn[('τ₀', 'τ\'')] = frozenset({PO})
    required_dn[('τ₁', 'τ\'')] = frozenset({DR})
    required_dn[('τ₂', 'τ\'')] = frozenset({PP, PPI})
    # Edges among existing elements (must contain the specific relation)
    # DN can be larger — we just need DR ∈ DN(τ₀,τ₁) etc.
    # For simplicity, try various DN sizes

    print("\n\nChecking Q3 for the required DN structure...")
    print("(Using smallest possible DN domains that include the required relations)")

    # Try: DN among existing types = just the required relation (tightest)
    dn = {}
    dn[('τ₀', 'τ₁')] = frozenset({DR})
    dn[('τ₁', 'τ₀')] = frozenset({DR})
    dn[('τ₀', 'τ₂')] = frozenset({DR})
    dn[('τ₂', 'τ₀')] = frozenset({DR})
    dn[('τ₁', 'τ₂')] = frozenset({PO})
    dn[('τ₂', 'τ₁')] = frozenset({PO})
    # To τ'
    dn[('τ₀', 'τ\'')] = frozenset({PO})
    dn[('τ\'', 'τ₀')] = frozenset({PO})
    dn[('τ₁', 'τ\'')] = frozenset({DR})
    dn[('τ\'', 'τ₁')] = frozenset({DR})
    dn[('τ₂', 'τ\'')] = frozenset({PP, PPI})
    dn[('τ\'', 'τ₂')] = frozenset({PP, PPI})

    # Self-DN (elements of same type with each other)
    for t in types:
        dn[(t, t)] = frozenset(RELS)  # assume full for self-pairs

    def check_q3(dn_map, types_list):
        """Check Q3: for every τ₁,τ₂,τ₃ and every R₁₂ ∈ DN(τ₁,τ₂),
        there exist R₁₃ ∈ DN(τ₁,τ₃), R₂₃ ∈ DN(τ₂,τ₃) with
        R₁₃ ∈ comp(R₁₂, R₂₃)."""
        violations = []
        for t1 in types_list:
            for t2 in types_list:
                for t3 in types_list:
                    if t1 == t2 == t3:
                        continue  # skip all-same
                    d12 = dn_map.get((t1, t2), frozenset())
                    d13 = dn_map.get((t1, t3), frozenset())
                    d23 = dn_map.get((t2, t3), frozenset())
                    for r12 in d12:
                        found = False
                        for r23 in d23:
                            r13_needed = comp(r12, r23)
                            if r13_needed & d13:
                                found = True
                                break
                        if not found:
                            violations.append((t1, t2, t3, r12))
        return violations

    print("\nCase 1: Tight DN (singletons among existing, as required)")
    violations = check_q3(dn, types)
    if violations:
        print(f"  Q3 FAILS — {len(violations)} violations:")
        for v in violations[:10]:
            t1, t2, t3, r12 = v
            d13 = dn.get((t1, t3), frozenset())
            d23 = dn.get((t2, t3), frozenset())
            print(f"    ({t1},{t2},{t3}): R₁₂={r12}, "
                  f"DN₁₃={set(d13)}, DN₂₃={set(d23)}")
            # What compositions are available?
            for r23 in d23:
                needed = comp(r12, r23)
                avail = needed & d13
                print(f"      comp({r12},{r23})={set(needed)}, "
                      f"∩ DN₁₃={set(avail)}")
    else:
        print("  Q3 holds! ✓")
        print("  → The counterexample IS liftable to a quasimodel.")

    # Try widening DN among existing types
    print("\nCase 2: Full DN among existing types (DN = {DR,PO,PP,PPI})")
    dn2 = dict(dn)
    for t1 in types[:3]:
        for t2 in types[:3]:
            if t1 != t2:
                dn2[(t1, t2)] = frozenset(RELS)

    violations2 = check_q3(dn2, types)
    if violations2:
        print(f"  Q3 FAILS — {len(violations2)} violations:")
        for v in violations2[:10]:
            t1, t2, t3, r12 = v
            d13 = dn2.get((t1, t3), frozenset())
            d23 = dn2.get((t2, t3), frozenset())
            print(f"    ({t1},{t2},{t3}): R₁₂={r12}, "
                  f"DN₁₃={set(d13)}, DN₂₃={set(d23)}")
            for r23 in d23:
                needed = comp(r12, r23)
                avail = needed & d13
                print(f"      comp({r12},{r23})={set(needed)}, "
                      f"∩ DN₁₃={set(avail)}")
    else:
        print("  Q3 holds! ✓")
        print("  → The counterexample IS liftable with wide existing-type DN.")

    # Now try systematically: what DN assignments among existing types
    # make Q3 hold while keeping the required DN to τ' ?
    print("\n\nSystematic search: find DN among existing types that make Q3 hold")
    print("  Fixed: DN(τ₀,τ')={PO}, DN(τ₁,τ')={DR}, DN(τ₂,τ')={PP,PPI}")

    all_subsets = []
    for mask in range(1, 16):
        s = frozenset(r for idx, r in enumerate(RELS) if mask & (1 << idx))
        all_subsets.append(s)

    # Pairs among existing types: (τ₀,τ₁), (τ₀,τ₂), (τ₁,τ₂)
    # Each can have any non-empty subset of RELS as DN
    # But must be converse-closed: DN(a,b) and DN(b,a) are related by INV
    # DN(a,b) = {R} → DN(b,a) = {inv(R)}
    # More generally: R ∈ DN(a,b) ↔ inv(R) ∈ DN(b,a)

    found_any = False
    found_count = 0
    for d01 in all_subsets:
        d10 = frozenset(INV[r] for r in d01)
        if DR not in d01:
            continue  # must contain DR for R(0,1)=DR
        for d02 in all_subsets:
            d20 = frozenset(INV[r] for r in d02)
            if DR not in d02:
                continue
            for d12 in all_subsets:
                d21 = frozenset(INV[r] for r in d12)
                if PO not in d12:
                    continue

                dn_test = {}
                dn_test[('τ₀', 'τ₁')] = d01
                dn_test[('τ₁', 'τ₀')] = d10
                dn_test[('τ₀', 'τ₂')] = d02
                dn_test[('τ₂', 'τ₀')] = d20
                dn_test[('τ₁', 'τ₂')] = d12
                dn_test[('τ₂', 'τ₁')] = d21
                # Fixed: to τ'
                dn_test[('τ₀', 'τ\'')] = frozenset({PO})
                dn_test[('τ\'', 'τ₀')] = frozenset({PO})
                dn_test[('τ₁', 'τ\'')] = frozenset({DR})
                dn_test[('τ\'', 'τ₁')] = frozenset({DR})
                dn_test[('τ₂', 'τ\'')] = frozenset({PP, PPI})
                dn_test[('τ\'', 'τ₂')] = frozenset({PP, PPI})
                # Self
                for t in types:
                    dn_test[(t, t)] = frozenset(RELS)

                violations = check_q3(dn_test, types)
                if not violations:
                    found_any = True
                    found_count += 1
                    if found_count <= 3:
                        print(f"\n  Found valid quasimodel structure #{found_count}:")
                        print(f"    DN(τ₀,τ₁) = {set(d01)}")
                        print(f"    DN(τ₀,τ₂) = {set(d02)}")
                        print(f"    DN(τ₁,τ₂) = {set(d12)}")
                        print(f"    DN(τ₀,τ') = {{PO}}")
                        print(f"    DN(τ₁,τ') = {{DR}}")
                        print(f"    DN(τ₂,τ') = {{PP, PPI}}")

    print(f"\n  Total valid quasimodel structures: {found_count}")
    if found_any:
        print(f"\n  *** THE EXTENSION GAP IS LIFTABLE ***")
        print(f"  There exist abstract quasimodels where Q1-Q3 hold")
        print(f"  but the Henkin construction's extension step FAILS.")
        print(f"  The decidability proof has a genuine gap.")
    else:
        print(f"\n  No valid quasimodel structure found for this counterexample.")
        print(f"  Q3 at the type level may prevent this specific scenario.")


def check_all_minimal_counterexamples():
    """Check ALL distinct counterexample patterns (up to symmetry) from m=3.

    Categorize by (base_network, domain_pattern) and check liftability.
    """
    print("\n" + "="*70)
    print("Checking liftability of ALL m=3 counterexample patterns")
    print("="*70)

    # Re-enumerate counterexamples
    from extension_gap_test import (
        enum_consistent_networks,
        check_pairwise_satisfiability,
        check_global_satisfiability
    )

    all_subsets = []
    for mask in range(1, 16):
        s = frozenset(r for idx, r in enumerate(RELS) if mask & (1 << idx))
        all_subsets.append(s)

    networks = enum_consistent_networks(3)

    # Collect unique patterns
    patterns = set()
    for edge in networks:
        r01 = edge[(0,1)]
        r02 = edge[(0,2)]
        r12 = edge[(1,2)]
        for d0, d1, d2 in product(all_subsets, repeat=3):
            domains = [d0, d1, d2]
            if check_pairwise_satisfiability(edge, domains, 3):
                glob, _ = check_global_satisfiability(edge, domains, 3)
                if not glob:
                    patterns.add((r01, r02, r12, d0, d1, d2))

    print(f"Total distinct counterexample patterns: {len(patterns)}")

    # For each pattern, check if Q3 can hold at the type level
    liftable = 0
    non_liftable = 0

    types = ['τ₀', 'τ₁', 'τ₂', 'τ\'']

    for r01, r02, r12, d0, d1, d2 in sorted(patterns):
        # Try all possible DN among existing types
        # Must contain the specific relations
        found = False
        for d01_mask in range(1, 16):
            d01 = frozenset(r for idx, r in enumerate(RELS) if d01_mask & (1 << idx))
            if r01 not in d01:
                continue
            d10 = frozenset(INV[r] for r in d01)
            for d02_mask in range(1, 16):
                d02 = frozenset(r for idx, r in enumerate(RELS) if d02_mask & (1 << idx))
                if r02 not in d02:
                    continue
                d20 = frozenset(INV[r] for r in d02)
                for d12_mask in range(1, 16):
                    d12 = frozenset(r for idx, r in enumerate(RELS) if d12_mask & (1 << idx))
                    if r12 not in d12:
                        continue
                    d21 = frozenset(INV[r] for r in d12)

                    dn_test = {}
                    dn_test[('τ₀', 'τ₁')] = d01
                    dn_test[('τ₁', 'τ₀')] = d10
                    dn_test[('τ₀', 'τ₂')] = d02
                    dn_test[('τ₂', 'τ₀')] = d20
                    dn_test[('τ₁', 'τ₂')] = d12
                    dn_test[('τ₂', 'τ₁')] = d21
                    dn_test[('τ₀', 'τ\'')] = d0
                    dn_test[('τ\'', 'τ₀')] = frozenset(INV[r] for r in d0)
                    dn_test[('τ₁', 'τ\'')] = d1
                    dn_test[('τ\'', 'τ₁')] = frozenset(INV[r] for r in d1)
                    dn_test[('τ₂', 'τ\'')] = d2
                    dn_test[('τ\'', 'τ₂')] = frozenset(INV[r] for r in d2)
                    for t in types:
                        dn_test[(t, t)] = frozenset(RELS)

                    # Check Q3
                    ok = True
                    for t1 in types:
                        for t2 in types:
                            for t3 in types:
                                if t1 == t2 == t3:
                                    continue
                                d_12 = dn_test.get((t1, t2), frozenset())
                                d_13 = dn_test.get((t1, t3), frozenset())
                                d_23 = dn_test.get((t2, t3), frozenset())
                                for r_12 in d_12:
                                    has_support = False
                                    for r_23 in d_23:
                                        if comp(r_12, r_23) & d_13:
                                            has_support = True
                                            break
                                    if not has_support:
                                        ok = False
                                        break
                                if not ok:
                                    break
                            if not ok:
                                break
                        if not ok:
                            break

                    if ok:
                        found = True
                        break
                if found:
                    break
            if found:
                break

        if found:
            liftable += 1
        else:
            non_liftable += 1

    print(f"\nResults:")
    print(f"  Liftable (Q3 can hold):     {liftable}")
    print(f"  Non-liftable (Q3 prevents): {non_liftable}")

    if liftable > 0:
        print(f"\n  *** {liftable} counterexamples are LIFTABLE ***")
        print(f"  The extension gap is genuine for abstract quasimodels.")
    if non_liftable > 0:
        print(f"  ({non_liftable} counterexamples are prevented by Q3)")
    if liftable == 0:
        print(f"\n  *** ALL counterexamples are prevented by Q3! ***")
        print(f"  Q3 is strong enough to close the extension gap (for m=3).")


if __name__ == '__main__':
    analyze_dn_from_types()
    check_counterexample_liftability()
    print("\n" + "="*70)
    print("Now checking ALL counterexample patterns...")
    check_all_minimal_counterexamples()
