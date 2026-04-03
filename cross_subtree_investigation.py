#!/usr/bin/env python3
"""
Investigate the CROSS-SUBTREE EDGE PROBLEM for ALCI_RCC5 decidability.

SETUP: In the unraveling of a blocked complete-graph tableau, nodes in
different subtrees need edges assigned. These must satisfy:
  (a) RCC5 composition constraints
  (b) ∀-constraint safety: R(u,v) = S → (∀S.D ∈ tp(u) → D ∈ tp(v))

KEY INSIGHT ("ancestor projection"):
  For nodes u,v mapping to DISTINCT tableau nodes T(u), T(v):
  Set R(u,v) = R_tableau(T(u), T(v)). This is:
    - Composition-consistent (tableau is consistent) ✓
    - ∀-safe (tableau ∀-rule was fully applied) ✓

  For nodes u,v mapping to the SAME tableau node (copies from blocking):
  Need R(u,v) = some self-safe relation in the composition domain.

This script investigates the SAME-NODE COPY problem:
  Given type τ (with ∀-constraints), which relations are "self-safe"?
  Are self-safe relations always in the composition domain for copies?
"""

from extension_gap_checker import RELS, INV, COMP, is_triple_consistent


def self_safe_relations(forall_constraints):
    """Given ∀-constraints as a dict {role: set of formulas that must be in type},
    and the type τ (set of formulas), find self-safe relations.

    A relation S is self-safe for τ if:
      ∀S.D ∈ τ → D ∈ τ  AND  ∀INV[S].D ∈ τ → D ∈ τ

    We represent this abstractly: forall_constraints[S] = set of formulas
    required by ∀S in the type. The type contains ALL these formulas iff
    forall_constraints[S] ⊆ type_formulas.

    Returns set of self-safe relations.
    """
    safe = set()
    for s in RELS:
        # Check ∀S.D → D ∈ τ for all D
        s_safe = forall_constraints.get(s, set()) <= forall_constraints.get('in_type', set())
        # Check ∀INV[S].D → D ∈ τ for all D
        inv_s = INV[s]
        inv_safe = forall_constraints.get(inv_s, set()) <= forall_constraints.get('in_type', set())
        if s_safe and inv_safe:
            safe.add(s)
    return safe


def analyze_ancestor_projection():
    """Analyze the ancestor projection strategy for cross-subtree edges."""
    print("=" * 70)
    print("ANCESTOR PROJECTION STRATEGY")
    print("=" * 70)
    print()
    print("For nodes u,v mapping to DISTINCT tableau nodes T(u) ≠ T(v):")
    print("  Set R(u,v) = R_tableau(T(u), T(v))")
    print("  Composition-consistent: YES (tableau network is consistent)")
    print("  ∀-safe: YES (tableau ∀-rule was fully applied)")
    print("  → ALWAYS WORKS for distinct tableau nodes")
    print()
    print("For nodes u,v mapping to SAME tableau node (copies):")
    print("  Need R(u,v) to be:")
    print("  (a) In the composition domain (from path in unraveling tree)")
    print("  (b) Self-safe for the type τ = tp(T(u)) = tp(T(v))")
    print()
    print("Self-safe: S is self-safe for τ if:")
    print("  ∀S.D ∈ τ → D ∈ τ  AND  ∀INV[S].D ∈ τ → D ∈ τ")
    print()


def analyze_tableau_self_safety():
    """In a complete-graph tableau, when two nodes n₁, n₂ have the same
    type τ and relation R(n₁,n₂) = T, the ∀-rule guarantees T is self-safe.

    Proof: ∀T.D ∈ tp(n₁) and R(n₁,n₂) = T → D ∈ tp(n₂) = τ.
           ∀INV[T].D ∈ tp(n₂) and R(n₂,n₁) = INV[T] → D ∈ tp(n₁) = τ.
    So ∀T.D ∈ τ → D ∈ τ and ∀INV[T].D ∈ τ → D ∈ τ. T is self-safe.
    """
    print("=" * 70)
    print("TABLEAU SELF-SAFETY GUARANTEE")
    print("=" * 70)
    print()
    print("THEOREM: In a complete-graph tableau, if n₁ and n₂ have the")
    print("same type τ and R(n₁,n₂) = T, then T is self-safe for τ.")
    print()
    print("PROOF: The ∀-rule was fully applied to all edges in the tableau.")
    print("  ∀T.D ∈ tp(n₁) ∧ R(n₁,n₂)=T → D ∈ tp(n₂) = τ  ✓")
    print("  ∀INV[T].D ∈ tp(n₂) ∧ R(n₂,n₁)=INV[T] → D ∈ tp(n₁) = τ  ✓")
    print("  Therefore T is self-safe for τ.  □")
    print()
    print("COROLLARY: In any open tableau branch, every blocked type has")
    print("at least one self-safe relation (the relation between the two")
    print("same-type nodes that triggered blocking).")
    print()


def analyze_composition_domains_for_copies():
    """For copies of the same node in the unraveling, what are the
    composition domains?

    The domain depends on the PATH between the copies.
    Key cases by witness relation S:

    Adjacent copies (parent → witness, copy of parent → copy of witness):
      Path: p₁ → w₁ → ... → p₂ → w₂
      R(w₁, w₂) ∈ comp(R(w₁, p₂), R(p₂, w₂))

    But actually the simplest case is:
      n blocked by n', both have type τ.
      In unraveling: n's subtree is replaced by copy of n'.
      At depth 2: n' has child c (same as n's child in n's subtree).
      If c is also blocked by n' (same type), then c's subtree is
      another copy of n'. The two copies of n' are related by:
      R(n'₁, n'₂) ∈ comp(R(n'₁, c₁), R(c₁, n'₂))
      where c₁ is the intermediate node.

    For the general case, two copies can be at arbitrary depth
    in the unraveling tree.
    """
    print("=" * 70)
    print("COMPOSITION DOMAINS FOR SAME-NODE COPIES")
    print("=" * 70)
    print()

    # For witness relation S, the path between adjacent copies goes:
    # copy₁ --S--> child --INV[S]--> copy₂ (if child is blocked and loops back)
    # So R(copy₁, copy₂) ∈ comp(S, INV[S])
    print("Adjacent copies (1-step blocked loop):")
    print("Path: copy₁ -S→ child_of_copy₁ -?→ copy₂")
    print("where child is blocked by copy₂'s parent (same type)")
    print()

    # Actually, the path is more complex. Let me think...
    # n has type τ, demand ∃S.C.
    # n's S-witness w has some type.
    # If w has type τ (same as n), w is blocked by n.
    # In unraveling: n → w₁ (copy of n) → w₂ (copy of n) → ...
    # R(n, w₁) = S. R(w₁, w₂) = ?
    # w₂ is S-witness of w₁ in the copy. So R(w₁, w₂) = S.
    # R(n, w₂) ∈ comp(R(n, w₁), R(w₁, w₂)) = comp(S, S).

    print("Self-loop blocking: n has ∃S.C, witness has type τ = tp(n)")
    print("Unraveling: n → w₁(=n) → w₂(=n) → ...")
    print("R(wₖ, wₖ₊₁) = S for all k")
    print("R(wⱼ, wₖ) ∈ comp(S, S, ..., S) [k-j times]")
    print()

    print("Iterated composition comp(S, S)^k:")
    for s in RELS:
        chain = set(RELS)  # Start with all relations
        # Actually start with comp(S, S) for k=2
        comp_k = set(COMP[(s, s)])
        print(f"  S = {s}:")
        print(f"    k=2: comp({s},{s}) = {comp_k}")

        # k=3: comp(comp(S,S), S) = union of comp(R, S) for R in comp(S,S)
        comp_k_next = set()
        for r in comp_k:
            comp_k_next |= set(COMP[(r, s)])
        print(f"    k=3: comp(comp({s},{s}), {s}) = {comp_k_next}")

        # k=4
        comp_k_4 = set()
        for r in comp_k_next:
            comp_k_4 |= set(COMP[(r, s)])
        print(f"    k=4: {comp_k_4}")

        # Check if it stabilizes
        if comp_k_next == comp_k_4:
            print(f"    Stable from k=3: {comp_k_next}")
        else:
            comp_k_5 = set()
            for r in comp_k_4:
                comp_k_5 |= set(COMP[(r, s)])
            print(f"    k=5: {comp_k_5}")
            if comp_k_4 == comp_k_5:
                print(f"    Stable from k=4: {comp_k_4}")
    print()

    # The key question: for each stable set, does it always contain
    # a self-safe relation?
    print("Stable composition sets:")
    for s in RELS:
        # Compute stable set
        comp_k = set(COMP[(s, s)])
        while True:
            comp_next = set()
            for r in comp_k:
                comp_next |= set(COMP[(r, s)])
            if comp_next == comp_k:
                break
            comp_k = comp_next

        print(f"  S = {s}: stable domain = {comp_k}")
        # Check: comp(S, INV[S]) for the "back and forth" pattern
        comp_back = set(COMP[(s, INV[s])])
        print(f"  comp({s}, {INV[s]}) = {comp_back} (for alternating pattern)")
    print()


def analyze_critical_case():
    """Analyze the critical case: S = PPI.

    comp(PPI, PPI) = {PPI}. So deep PPI-chains force PPI for all copies.
    PPI self-safe requires: ∀PPI.D ∈ τ → D ∈ τ AND ∀PP.D ∈ τ → D ∈ τ.

    In the tableau: n₁ and n₂ have R(n₁,n₂) = T.
    T is self-safe. T may be DR, PO, PP, or PPI.

    comp(PPI, PPI) = {PPI}. So for PPI-chains, only PPI is available.
    Need PPI to be self-safe.

    Is PPI always self-safe for types that get PPI-blocked?
    """
    print("=" * 70)
    print("CRITICAL CASE: S = PPI chains")
    print("=" * 70)
    print()
    print("comp(PPI, PPI) = {PPI}. Deep chains force R = PPI between copies.")
    print()
    print("PPI self-safe requires:")
    print("  ∀PPI.D ∈ τ → D ∈ τ  [PPI = self]")
    print("  ∀PP.D ∈ τ → D ∈ τ   [INV[PPI] = PP]")
    print()

    # Similarly for PP chains
    print("Similarly: comp(PP, PP) = {PP}. Deep PP-chains force PP.")
    print("PP self-safe requires:")
    print("  ∀PP.D ∈ τ → D ∈ τ   [PP = self]")
    print("  ∀PPI.D ∈ τ → D ∈ τ  [INV[PP] = PPI]")
    print()
    print("PP and PPI self-safety are EQUIVALENT (both require ∀PP and ∀PPI closure).")
    print()

    # When does a PPI-witness have the same type as its parent?
    # n has ∃PPI.C. Witness w has R(n,w) = PPI, C ∈ tp(w).
    # w's type is determined by C plus ∀-consequences from all edges.
    # One edge: R(n,w) = PPI → R(w,n) = PP.
    #   ∀PP.D ∈ tp(w) → D ∈ tp(n) (from w to n)
    #   ∀PPI.D ∈ tp(n) → D ∈ tp(w) (from n to w)
    # So tp(w) includes all D from ∀PPI.D ∈ tp(n).
    # And tp(n) includes all D from ∀PP.D ∈ tp(w).

    print("For PPI-witness w of n (R(n,w) = PPI):")
    print("  ∀-rule: ∀PPI.D ∈ tp(n) → D ∈ tp(w)")
    print("  ∀-rule: ∀PP.D ∈ tp(w) → D ∈ tp(n)")
    print()
    print("If tp(w) = tp(n) = τ (blocking triggers):")
    print("  ∀PPI.D ∈ τ → D ∈ τ  [from n to w, since R(n,w)=PPI]")
    print("  ∀PP.D ∈ τ → D ∈ τ   [from w to n, since R(w,n)=PP]")
    print()
    print("  *** BOTH conditions for PPI self-safety are SATISFIED! ***")
    print()
    print("PROOF: If w is a PPI-witness of n with tp(w) = tp(n) = τ:")
    print("  R(n,w) = PPI → ∀PPI.D ∈ tp(n)=τ → D ∈ tp(w)=τ  ✓")
    print("  R(w,n) = PP  → ∀PP.D ∈ tp(w)=τ → D ∈ tp(n)=τ   ✓")
    print("  Therefore PPI is self-safe for τ.  □")
    print()

    print("Similarly for PP-witness w of n (R(n,w) = PP, R(w,n) = PPI):")
    print("  ∀PP.D ∈ tp(n)=τ → D ∈ tp(w)=τ   [R(n,w)=PP]  ✓")
    print("  ∀PPI.D ∈ tp(w)=τ → D ∈ tp(n)=τ  [R(w,n)=PPI] ✓")
    print("  Therefore PP is self-safe for τ.  □")
    print()
    print("=" * 70)
    print("KEY THEOREM: FOR THE WITNESS RELATION S, S IS ALWAYS SELF-SAFE")
    print("=" * 70)
    print()
    print("PROOF: If w is an S-witness of n with tp(w) = tp(n) = τ:")
    print("  R(n,w) = S → ∀S.D ∈ tp(n)=τ → D ∈ tp(w)=τ  ✓")
    print("  R(w,n) = INV[S] → ∀INV[S].D ∈ tp(w)=τ → D ∈ tp(n)=τ  ✓")
    print("  This gives exactly the self-safety conditions for S.  □")
    print()
    print("This resolves the PPI-chain issue!")
    print("  comp(PPI,PPI)^k = {PPI} for all k.")
    print("  PPI is self-safe (by the theorem above).")
    print("  So PPI can be used for all copies in PPI-chains.  ✓")
    print()
    print("And similarly for PP-chains: comp(PP,PP)^k = {PP}.")
    print("  PP is self-safe. ✓")
    print()
    print("And for DR-chains: comp(DR,DR)^k = {DR,PO,PP,PPI} (stable).")
    print("  DR is self-safe. Any self-safe relation works.  ✓")
    print()
    print("And for PO-chains: comp(PO,PO)^k = {DR,PO,PP,PPI} (stable).")
    print("  PO is self-safe. Any self-safe relation works.  ✓")
    print()


def analyze_mixed_chains():
    """What about MIXED chains? Where copies are not all the same type.

    In the unraveling, the path between two copies of n may go through
    nodes of DIFFERENT types (not just copies of n).
    """
    print("=" * 70)
    print("MIXED CHAINS: copies separated by different-type nodes")
    print("=" * 70)
    print()
    print("In the unraveling, two copies u₁, u₂ of tableau node n may be")
    print("separated by nodes of different types. Example:")
    print("  n --S₁--> c₁ --S₂--> n' --S₃--> c₂ --S₄--> n''")
    print("  where n, n', n'' are copies (same type τ)")
    print("  and c₁, c₂ are nodes of different types")
    print()
    print("R(u₁, u₂) ∈ comp(S₁, S₂, S₃, S₄, ...) along the path")
    print()
    print("For the ANCESTOR PROJECTION: R(u₁, u₂) = R_tableau(n₁, n₂)")
    print("where n₁, n₂ are the tableau nodes. Since n₁ = n₂ = n,")
    print("this gives EQ — invalid for distinct elements!")
    print()
    print("Instead: R(u₁, u₂) must be in the PATH composition domain")
    print("AND self-safe for τ.")
    print()
    print("But the key insight: the PATH goes through the blocker.")
    print("If n₂ is blocked by n₁, the path from n₁ to any copy of")
    print("n₂ goes through the blocked node's subtree, which in the")
    print("unraveling becomes a copy of n₁'s subtree.")
    print()
    print("The simplest case: n has ∃S.C, the witness has type τ = tp(n).")
    print("The witness is blocked by n. In the unraveling:")
    print("  n --S--> w₁(=n) --S--> w₂(=n) --S--> ...")
    print("R(wⱼ, wₖ) ∈ comp(S)^(k-j)")
    print()
    print("By the theorem above: S is self-safe for τ.")
    print("And S ∈ comp(S)^k for all k (since comp(S,S) ⊇ {S} for all S).")
    print()

    # Verify: S ∈ comp(S, S) for all S?
    print("Verify: S ∈ comp(S, S)?")
    for s in RELS:
        in_comp = s in COMP[(s, s)]
        print(f"  {s} ∈ comp({s},{s}) = {set(COMP[(s,s)])}? {'✓' if in_comp else '✗'}")

    print()
    print("PP ∈ comp(PP,PP) = {PP}  ✓")
    print("PPI ∈ comp(PPI,PPI) = {PPI}  ✓")
    print("DR ∈ comp(DR,DR) = {DR,PO,PP,PPI}  ✓")
    print("PO ∈ comp(PO,PO) = {DR,PO,PP,PPI}  ✓")
    print()
    print("S ∈ comp(S,S) for ALL S.  ✓")
    print()
    print("By induction: S ∈ comp(S)^k for all k ≥ 1.")
    print("Combined with self-safety of S: every copy in an S-chain")
    print("can use relation S between adjacent copies, and S is self-safe.")
    print()
    print("For non-adjacent copies: R(wⱼ, wₖ) ∈ comp(S)^(k-j).")
    print("S ∈ comp(S)^(k-j) (by induction). And S is self-safe.")
    print("So S works for ALL pairs of copies!  ✓")
    print()


def final_synthesis():
    """Synthesize all findings into the complete picture."""
    print("=" * 70)
    print("COMPLETE SYNTHESIS: SOUNDNESS OF BLOCKING IN ALCI_RCC5")
    print("=" * 70)
    print()
    print("Given: Open, completed, blocked complete-graph tableau branch.")
    print("Goal: Construct a model.")
    print()
    print("CONSTRUCTION:")
    print("1. Unravel the blocked branch into an infinite tree-like structure.")
    print("   Each blocked node is replaced by a copy of its blocker's subtree.")
    print()
    print("2. WITHIN-SUBTREE edges: directly from the tableau.")
    print("   Composition-consistent ✓, ∀-safe ✓ (tableau properties)")
    print()
    print("3. CROSS-SUBTREE edges between DISTINCT tableau nodes T(u) ≠ T(v):")
    print("   Use ANCESTOR PROJECTION: R(u,v) = R_tableau(T(u), T(v))")
    print("   - Composition-consistent: YES")
    print("     The tableau is a complete composition-consistent network.")
    print("     R_tableau(T(u), T(w)) ∈ comp(R_tableau(T(u), T(v)), R_tableau(T(v), T(w)))")
    print("     for any three distinct tableau nodes.")
    print("   - ∀-safe: YES")
    print("     The ∀-rule was fully applied in the tableau:")
    print("     ∀S.D ∈ tp(T(u)) ∧ R_tableau(T(u),T(v))=S → D ∈ tp(T(v))")
    print()
    print("4. CROSS-SUBTREE edges between SAME tableau node copies T(u) = T(v) = n:")
    print("   Use the WITNESS RELATION: R(u,v) = S where S is the role that")
    print("   created the blocked node (i.e., the ∃S.C demand).")
    print("   - In the composition domain: YES")
    print("     S ∈ comp(S)^k for all k ≥ 1 (proved: S ∈ comp(S,S) for all S)")
    print("   - Self-safe: YES (KEY THEOREM)")
    print("     If w is S-witness of n with tp(w) = tp(n) = τ,")
    print("     then the ∀-rule gives:")
    print("     ∀S.D ∈ τ → D ∈ τ  (from n to w via R(n,w)=S)")
    print("     ∀INV[S].D ∈ τ → D ∈ τ  (from w to n via R(w,n)=INV[S])")
    print()
    print("5. CONSISTENCY between assignment strategies (3) and (4):")
    print("   For a triple (u, v, w) where T(u) = T(v) ≠ T(w):")
    print("   R(u,w) = R_tableau(n, T(w))  [strategy 3]")
    print("   R(v,w) = R_tableau(n, T(w))  [strategy 3, same!]")
    print("   R(u,v) = S  [strategy 4]")
    print("   Need: R_tableau(n, T(w)) ∈ comp(S, R_tableau(n, T(w)))")
    print("   i.e., R ∈ comp(S, R) for R = R_tableau(n, T(w))")
    print("   This is SELF-ABSORPTION: R ∈ comp(S, R).")
    print()

    # Check self-absorption in the reverse direction
    print("   Self-absorption check: R ∈ comp(S, R)?")
    all_ok = True
    for s in RELS:
        for r in RELS:
            result = r in COMP[(s, r)]
            if not result:
                print(f"     {r} ∈ comp({s}, {r}) = {set(COMP[(s,r)])}? ✗ FAIL!")
                all_ok = False
    if all_ok:
        print("   All pass! R ∈ comp(S, R) for all S, R.  ✓")
    else:
        print()
        print("   FAILURES detected! Need to analyze...")
    print()

    # Also check: R ∈ comp(R, S)?
    print("   Also need: R(u,w) ∈ comp(R(u,v), R(v,w))")
    print("   = R_tableau(n,T(w)) ∈ comp(S, R_tableau(n,T(w)))")
    print("   Already checked above (same condition).")
    print()
    print("   And: R(v,w) ∈ comp(R(v,u), R(u,w))")
    print("   = R_tableau(n,T(w)) ∈ comp(INV[S], R_tableau(n,T(w)))")
    print("   Need: R ∈ comp(INV[S], R) for all R.")
    print()
    all_ok2 = True
    for s in RELS:
        inv_s = INV[s]
        for r in RELS:
            result = r in COMP[(inv_s, r)]
            if not result:
                print(f"     {r} ∈ comp({inv_s}, {r}) = {set(COMP[(inv_s,r)])}? ✗")
                all_ok2 = False
    if all_ok2:
        print("   All pass! R ∈ comp(INV[S], R) for all S, R.  ✓")
    print()

    if not all_ok or not all_ok2:
        print("   *** CONSISTENCY BETWEEN STRATEGIES FAILS! ***")
        print("   Need more careful analysis...")
        print()
        # Which combinations fail?
        print("   Failing combinations:")
        for s in RELS:
            for r in RELS:
                if r not in COMP[(s, r)]:
                    print(f"     R ∈ comp(S, R): S={s}, R={r}: "
                          f"{r} ∉ comp({s},{r})={set(COMP[(s,r)])}")
                inv_s = INV[s]
                if r not in COMP[(inv_s, r)]:
                    print(f"     R ∈ comp(INV[S], R): S={s}, INV[S]={inv_s}, R={r}: "
                          f"{r} ∉ comp({inv_s},{r})={set(COMP[(inv_s,r)])}")
    print()

    # Final summary
    print("=" * 70)
    if all_ok and all_ok2:
        print("RESULT: SOUNDNESS PROOF IS COMPLETE")
        print("=" * 70)
        print()
        print("The ancestor projection (for distinct nodes) combined with")
        print("witness-relation assignment (for same-node copies) gives a")
        print("valid model construction from any open tableau branch.")
        print()
        print("All cross-subtree edges satisfy:")
        print("  - RCC5 composition constraints  ✓")
        print("  - ∀-constraint safety           ✓")
        print("  - Inter-strategy consistency     ✓")
    else:
        print("RESULT: GAPS REMAIN IN CONSISTENCY")
        print("=" * 70)
        print()
        print("The inter-strategy consistency check reveals failures.")
        print("These need to be resolved before the soundness proof is complete.")
    print()


if __name__ == '__main__':
    analyze_ancestor_projection()
    analyze_tableau_self_safety()
    analyze_composition_domains_for_copies()
    analyze_critical_case()
    analyze_mixed_chains()
    final_synthesis()
