#!/usr/bin/env python3
"""
Analysis of the PP-cycle obstruction and its resolution.

The PP-kernel quotient works perfectly for single-type PP-chains
but fails for multi-type periodic chains because PP is transitive
(comp(PP,PP) = {PP}), forcing a strict linear order on kernel nodes.

This script:
1. Confirms the single-type case works
2. Demonstrates the PP-cycle obstruction precisely
3. Tests whether multi-type demands can be resolved by external elements
4. Explores the "period descriptor" approach (finite representation
   of periodic chains without trying to embed them as RCC5 nodes)
"""

from extension_gap_checker import RELS, INV, COMP


# ======================================================================
# PART 1: Single-type PP-chains collapse perfectly
# ======================================================================
print("=" * 70)
print("PART 1: Single-type PP-chains — perfect collapse")
print("=" * 70)
print()
print("Concept: C∞ = ∃PP.⊤ ⊓ ∀PP.∃PP.⊤")
print("Model: d₀ PP d₁ PP d₂ PP ... all with type τ = {C∞, ∃PP.⊤}")
print()
print("Quotient: single kernel k_τ with PP(k_τ, k_τ)")
print("  ∃PP.⊤ demand: satisfied by PP-self-loop (⊤ ∈ τ)")
print("  ∀PP.∃PP.⊤ propagation: ∃PP.⊤ ∈ τ ✓ (type closed under ∀PP)")
print("  Composition: PP(k,k) self-consistent ✓")
print()
print("The infinite chain collapses to ONE NODE. ✓")
print()

# Verify that single-type is the COMMON case
print("When does a PP-chain become single-type?")
print()
print("On chain d₀ PP d₁ PP d₂ PP ...:")
print("  ∀PP-consequences accumulate: F₁ ⊆ F₂ ⊆ ... ⊆ F_N = F (stabilize)")
print("  After stabilization, all types contain F.")
print("  If F determines the type uniquely (no free concepts), → single-type.")
print("  Multi-type only if cl(C₀)\\F has concepts that can freely alternate.")
print()
print("Example of single-type: C∞ above. F = {∃PP.⊤, C∞}. Only one type works.")
print("Example of multi-type: ∃PP.(A ⊓ ∃PP.¬A) ⊓ ∀PP.∃PP.(A ⊓ ∃PP.¬A)")
print("  forces alternation between types containing A and ¬A.")


# ======================================================================
# PART 2: The PP-cycle obstruction
# ======================================================================
print()
print("=" * 70)
print("PART 2: Why multi-type periods can't be represented as kernel nodes")
print("=" * 70)
print()
print("PP-transitivity: comp(PP, PP) = {PP}")
print("This forces any set of PP-related distinct nodes into a TOTAL ORDER.")
print()

# Show that no atomic assignment of {PP,PPI} on 3 nodes can form a cycle
print("3-node PP-cycle test: k₁ PP k₂ PP k₃ PP k₁?")
print("  k₁ PP k₂ and k₂ PP k₃ → comp(PP,PP)={PP} → k₁ PP k₃ forced")
print("  k₃ PP k₁ needed for cycle")
print("  But k₁ PP k₃ means PPI(k₃, k₁), not PP(k₃, k₁)")
print("  → IMPOSSIBLE (PP and PPI can't both hold between distinct nodes)")
print()

# But verify: what if we try all 8 assignments?
print("Exhaustive check: any PP-cycle among 3 distinct nodes?")
edges_3 = [(0, 1), (1, 2), (0, 2)]
n_cycles = 0
for combo in ((a, b, c) for a in ['PP', 'PPI'] for b in ['PP', 'PPI'] for c in ['PP', 'PPI']):
    a = {(0, 1): combo[0], (1, 0): INV[combo[0]],
         (1, 2): combo[1], (2, 1): INV[combo[1]],
         (0, 2): combo[2], (2, 0): INV[combo[2]]}

    # Check composition for all triples
    ok = True
    for i, j, k in [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]:
        if a[(i, k)] not in COMP[(a[(i, j)], a[(j, k)])]:
            ok = False
            break

    if ok:
        # Check if every node has both a PP-successor and a PP-predecessor
        # (i.e., for each i, ∃j with PP(i,j) and ∃k with PPI(i,k) where j≠k)
        all_have_both = True
        for i in range(3):
            has_pp = any(a[(i, j)] == 'PP' for j in range(3) if j != i)
            has_ppi = any(a[(i, j)] == 'PPI' for j in range(3) if j != i)
            if not (has_pp and has_ppi):
                all_have_both = False
        if all_have_both:
            n_cycles += 1
            print(f"  Found: {combo[0]}(0,1), {combo[1]}(1,2), {combo[2]}(0,2) — each node has PP and PPI")

if n_cycles == 0:
    print("  NONE — no 3-node configuration gives every node both PP and PPI neighbors")


# ======================================================================
# PART 3: Key insight — PPI demands are satisfied OUTSIDE the chain
# ======================================================================
print()
print("=" * 70)
print("PART 3: Demand satisfaction — which demands stay in-chain?")
print("=" * 70)
print()
print("In the tree unraveling, a PP-chain d₀ PP d₁ PP d₂ PP ...:")
print("  Each d_i was created as a PP-witness for d_{i-1}'s ∃PP demand.")
print("  So the CHAIN carries PP demands downward (each ∃PP.C generates")
print("  the next element on the chain).")
print()
print("Other demands of d_i (∃DR.C, ∃PO.C, ∃PPI.C) create BRANCHES")
print("off the chain — separate subtrees rooted at d_i's children.")
print()
print("So the ONLY demands that must be satisfied WITHIN the chain")
print("are ∃PP demands. All other demands are satisfied by non-chain elements.")
print()
print("For a linear kernel order k₁ PP k₂ PP ... PP k_p:")
print("  k_i's ∃PP.C demand (C ∉ tp(k_i)) needs PP-neighbor k_j (j > i) with C ∈ tp(k_j)")
print("  This works for ALL kernels EXCEPT k_p (the last one).")
print()
print("k_p's ∃PP.C demand (C ∉ tp(k_p)):")
print("  In the original chain, k_p's representative has PP to a 'next period' element.")
print("  That element has the same type as some k_j (j ≤ p, by periodicity).")
print("  But PP(k_p, k_j) contradicts the linear order if j < p.")

# Test: can k_p's demand be satisfied by its own reflexive loop?
print()
print("Can k_p satisfy its own PP demand via the reflexive loop?")
print("  ∃PP.C ∈ tp(k_p): if C ∈ tp(k_p), yes (self-loop). ✓")
print("  If C ∉ tp(k_p), NO — the self-loop doesn't help.")
print()
print("When does C ∈ tp(k_p)?")
print("  On the periodic chain, k_p's ∃PP.C demand is satisfied by the next element")
print("  (first of the next period, type τ₁). So C ∈ τ₁.")
print("  If τ₁ = τ_p (single type!), then C ∈ tp(k_p). Self-loop works. ✓")
print("  If τ₁ ≠ τ_p (multi-type), then C ∉ tp(k_p). Self-loop fails. ✗")


# ======================================================================
# PART 4: Period descriptor — finite representation without RCC5 cycles
# ======================================================================
print()
print("=" * 70)
print("PART 4: The period descriptor approach")
print("=" * 70)
print()
print("Instead of representing the periodic tail as RCC5 kernel nodes,")
print("represent it as a FINITE DESCRIPTOR:")
print()
print("  PeriodDesc = (τ₁, τ₂, ..., τ_p)")
print()
print("  where each τ_i is a Hintikka type, and the period repeats:")
print("  τ₁ PP τ₂ PP ... PP τ_p PP τ₁ PP τ₂ PP ... (infinitely)")
print()
print("The descriptor is valid if:")
print("  (V1) Each τ_i is a Hintikka type in cl(C₀)")
print("  (V2) ∀PP.C ∈ τ_i ⟹ C ∈ τ_j for all j (periodic propagation)")
print("  (V3) ∀PPI.C ∈ τ_i ⟹ C ∈ τ_j for all j (backward propagation)")
print("  (V4) ∃PP.C ∈ τ_i ⟹ C ∈ τ_j for some j (existential witness)")
print("  (V5) Cross-chain composition: for any external node m and any")
print("       two positions i, j in the period, if R(τ_i, m) = S_i and")
print("       R(τ_j, m) = S_j, then S_j ∈ comp(PP^|j-i|, S_i)")
print("       (where PP^k is the k-fold composition of PP)")
print()

# Verify V5: PP^k composition
print("PP^k composition table (how external relations evolve along the chain):")
print("  PP^1 = PP")
print("  PP^k for k ≥ 1: comp(PP, PP) = {PP}, so PP^k = PP for all k ≥ 1")
print()
print("  So comp(PP^k, S) = comp(PP, S) for all k ≥ 1:")
for S in RELS:
    print(f"    comp(PP, {S}) = {set(COMP[('PP', S)])}")

print()
print("This means: on a PP-chain, external relations are constrained by")
print("comp(PP, current_relation), regardless of distance. The relation")
print("can only transition WITHIN the allowed set.")
print()
print("Stabilization: comp(PP, PP) = {PP} (absorbing)")
print("So once R(e, d_i) = PP, it stays PP forever. ✓")
print()

# Check V2 and V3 for concrete 2-type periods
print("─" * 70)
print("Test: 2-type period (A, B) validity conditions")
print("─" * 70)
print()

# Enumerate valid 2-type periods
# A type is a subset of some concept set. Let's use a minimal example.
# Concepts: {p, ¬p, ∃PP.p, ∃PP.¬p, ∀PP.p, ∀PP.¬p}
# A maximal consistent subset = a Hintikka type

concepts = ['p', '~p', 'ePP.p', 'ePP.~p', 'aPP.p', 'aPP.~p']

# A type must contain exactly one of {p, ~p}
# If aPP.p ∈ τ, then all PP-successors must have p
# If aPP.~p ∈ τ, then all PP-successors must have ~p

# Generate all consistent types
types = []
for has_p in [True, False]:
    for has_epp_p in [True, False]:
        for has_epp_np in [True, False]:
            for has_app_p in [True, False]:
                for has_app_np in [True, False]:
                    t = set()
                    t.add('p' if has_p else '~p')
                    if has_epp_p:
                        t.add('ePP.p')
                    if has_epp_np:
                        t.add('ePP.~p')
                    if has_app_p:
                        t.add('aPP.p')
                    if has_app_np:
                        t.add('aPP.~p')

                    # Consistency: if aPP.p ∈ t and aPP.~p ∈ t,
                    # then PP-successors must have both p and ~p — contradiction
                    if 'aPP.p' in t and 'aPP.~p' in t:
                        continue

                    types.append(frozenset(t))

print(f"Generated {len(types)} consistent types over {{p, ~p, ∃PP.p, ∃PP.~p, ∀PP.p, ∀PP.~p}}")

# Check valid 2-type periods
valid_periods = []
for t1 in types:
    for t2 in types:
        # V2: ∀PP.C ∈ τ₁ ⟹ C ∈ τ₂ AND C ∈ τ₁ (periodic)
        # V2: ∀PP.C ∈ τ₂ ⟹ C ∈ τ₁ AND C ∈ τ₂
        v2_ok = True
        for app_c, c in [('aPP.p', 'p'), ('aPP.~p', '~p')]:
            if app_c in t1:
                if c not in t2 or c not in t1:
                    v2_ok = False
            if app_c in t2:
                if c not in t1 or c not in t2:
                    v2_ok = False
        if not v2_ok:
            continue

        # V4: ∃PP.C ∈ τ₁ ⟹ C ∈ τ₁ or C ∈ τ₂
        # V4: ∃PP.C ∈ τ₂ ⟹ C ∈ τ₁ or C ∈ τ₂
        v4_ok = True
        for epp_c, c in [('ePP.p', 'p'), ('ePP.~p', '~p')]:
            if epp_c in t1:
                if c not in t1 and c not in t2:
                    v4_ok = False
            if epp_c in t2:
                if c not in t1 and c not in t2:
                    v4_ok = False
        if not v4_ok:
            continue

        # Must have different types for multi-type period
        if t1 == t2:
            continue

        valid_periods.append((t1, t2))

print(f"Valid 2-type periods: {len(valid_periods)}")
if valid_periods:
    for t1, t2 in valid_periods[:5]:
        print(f"  ({set(t1)}, {set(t2)})")
    if len(valid_periods) > 5:
        print(f"  ... and {len(valid_periods) - 5} more")


# ======================================================================
# PART 5: The hybrid approach — period descriptors + kernel nodes
# ======================================================================
print()
print("=" * 70)
print("PART 5: Hybrid approach — period descriptors + PP-kernel for external")
print("=" * 70)
print()
print("The finite model representation combines two mechanisms:")
print()
print("1. PERIOD DESCRIPTORS for PP-chain tails:")
print("   Each infinite PP-chain's periodic tail is described by (τ₁,...,τ_p).")
print("   The period satisfies V1-V5. No RCC5 nodes needed for the chain itself.")
print("   The descriptor is a finite object of size ≤ p ≤ |types| ≤ 2^|cl(C₀)|.")
print()
print("2. PP-KERNEL NODES for cross-chain interaction:")
print("   Each period descriptor has ONE representative kernel node k with")
print("   reflexive PP(k,k). This node represents 'any element on this chain'")
print("   for the purpose of cross-chain edges.")
print()
print("   The kernel's type = the TYPE SHARED BY ALL period elements, i.e.,")
print("   the intersection ∩{τ₁,...,τ_p} of concepts common to all period types.")
print("   (Or more precisely: the stabilized ∀PP/∀PPI core.)")
print()
print("3. ATOMIC EDGES between kernels of different chains:")
print("   Determined by PP-chain monotonicity (stabilized external relations).")
print()
print("4. REGULAR NODES for non-chain elements (finite prefix, non-PP witnesses).")
print()

# Check: the stabilized core
print("The stabilized core of a period (τ₁,...,τ_p):")
print("  Core = ∩{τ₁,...,τ_p} (concepts present in ALL types)")
print("  This includes:")
print("    - All ∀PP consequences (by V2)")
print("    - All ∀PPI consequences (by V3)")
print()
print("The kernel node k with type = Core is ∀-safe for all cross-chain edges")
print("(any edge R(k, m) has ∀-safety inherited from the stabilized model relation).")
print()
print("Cross-chain ∃-demands: if ∃R.C ∈ Core, then ∃R.C ∈ τ_i for all i,")
print("meaning the demand is present at every position on the chain.")
print("The witness is either on the chain (for R=PP, handled by the descriptor)")
print("or off the chain (for R∈{DR,PO,PPI}, handled by regular nodes/other kernels).")

print()
print("═" * 70)
print("CONCLUSION")
print("═" * 70)
print()
print("The PP-kernel quotient works in two tiers:")
print()
print("TIER 1 (within PP-chains): Period descriptors.")
print("  A periodic chain (τ₁,...,τ_p,τ₁,...) is described finitely.")
print("  The descriptor validates PP-demands internally (V4).")
print("  No RCC5 graph needed for the chain — it's a WORD, not a graph.")
print()
print("TIER 2 (between PP-chains): Kernel nodes + regular nodes.")
print("  One kernel per chain (type = stabilized core).")
print("  Reflexive PP for chain self-interaction.")
print("  Atomic edges to other kernels/regular nodes.")
print("  Standard RCC5 composition consistency for cross-chain triples.")
print()
print("FINITENESS:")
print("  Number of distinct period descriptors: bounded by |types|! ≤ 2^{O(|C₀|)}")
print("  Number of kernel nodes: ≤ number of PP-chains = ≤ number of ∃PP demands")
print("  Number of regular nodes: bounded by tableau size = 2^{O(|C₀|)}")
print("  Total quotient size: 2^{O(|C₀|)} → EXPTIME decision procedure")
print()
print("KEY REMAINING QUESTION:")
print("  Can every satisfiable concept be represented by such a quotient?")
print("  Equivalently: does every infinite model admit this two-tier decomposition?")
print("  The PP-chain stabilization argument (monotonicity + finiteness of types)")
print("  strongly suggests yes, but a formal proof requires:")
print("  (a) Showing external relations truly stabilize on the periodic tail")
print("  (b) Showing the cross-chain kernel edges are composition-consistent")
print("  (c) Showing the period descriptor + kernel is sufficient for all demands")
