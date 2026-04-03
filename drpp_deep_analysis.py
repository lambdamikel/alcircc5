#!/usr/bin/env python3
"""
Deep analysis of the DR+PP case: modified profile and type enrichment.

Key findings from drpp_extension_investigation.py:
  Q1: One-step extension is ALWAYS solvable (45,528 / 45,528)
  Q2: PP edges are ALWAYS avoidable for DR-witnesses (0 forced PP)

This script investigates:
  Q7: Can we ALWAYS use "modified profile-copy" for DR-witnesses?
      (profile-copy for non-PP-parents, DR for PP-parents)
  Q8: What is the structure of the ∀-constraint mismatch?
  Q9: Does the type enrichment cascade or stabilize?
  Q10: Can we bound the number of distinct "enriched types"?
"""

from extension_gap_checker import (
    RELS, INV, COMP, is_triple_consistent, enumerate_consistent_networks
)


def question7_modified_profile():
    """Q7: Does "modified profile-copy" always work?

    Modified profile: for DR-witness y of x:
      R(z,y) = R(z,x) if R(z,x) ≠ PP  (profile copy)
      R(z,y) = DR     if R(z,x) = PP   (forced by composition)

    Check: is this assignment ALWAYS composition-consistent
    (including inter-node constraints between z-nodes)?
    """
    print("=" * 70)
    print("Q7: Is modified profile-copy always composition-consistent?")
    print("=" * 70)
    print()

    total = 0
    failures = 0
    failure_examples = []

    for n in range(2, 6):
        n_total = 0
        n_fail = 0
        for net in enumerate_consistent_networks(n):
            for parent in range(n):
                total += 1
                n_total += 1

                others = [i for i in range(n) if i != parent]

                def get_r(a, b):
                    if a < b: return net[(a,b)]
                    return INV[net[(b,a)]]

                # Build modified profile assignment
                assignment = {}
                for z in others:
                    r_zx = get_r(z, parent)
                    if r_zx == 'PP':
                        assignment[z] = 'DR'  # forced
                    else:
                        assignment[z] = r_zx  # profile copy

                # Check: is this assignment consistent?
                # Check all triples (z1, z2, y) and (parent, z, y)
                ok = True

                # Triple (parent, z, y) for each z
                for z in others:
                    r_pz = get_r(parent, z)
                    r_py = 'DR'  # witness relation
                    r_zy = assignment[z]
                    if not is_triple_consistent(r_pz, r_zy, r_py):
                        ok = False
                        break

                # Triples (z1, z2, y) for each pair z1, z2
                if ok:
                    for i, z1 in enumerate(others):
                        for z2 in others[i+1:]:
                            r_z1z2 = get_r(z1, z2)
                            r_z1y = assignment[z1]
                            r_z2y = assignment[z2]
                            if not is_triple_consistent(r_z1z2, r_z2y, r_z1y):
                                ok = False
                                if len(failure_examples) < 5:
                                    failure_examples.append({
                                        'n': n, 'net': dict(net),
                                        'parent': parent,
                                        'z1': z1, 'z2': z2,
                                        'r_z1z2': r_z1z2,
                                        'r_z1y': r_z1y,
                                        'r_z2y': r_z2y,
                                        'assignment': dict(assignment),
                                    })
                                break
                        if not ok:
                            break

                if not ok:
                    failures += 1
                    n_fail += 1

        print(f"  n={n}: {n_fail} failures / {n_total} cases")

    print(f"\n  TOTAL: {failures} failures / {total:,} cases")
    if failures == 0:
        print("  *** Modified profile-copy ALWAYS works! ***")
    else:
        print(f"  *** Modified profile-copy has {failures} failures ***")
        for i, ex in enumerate(failure_examples[:5]):
            print(f"\n  Failure {i+1} (n={ex['n']}, parent={ex['parent']}):")
            for (a,b), r in sorted(ex['net'].items()):
                print(f"    R({a},{b}) = {r}")
            print(f"    Assignment: {ex['assignment']}")
            print(f"    Failing triple: z1={ex['z1']}, z2={ex['z2']}")
            print(f"    R(z1,z2)={ex['r_z1z2']}, R(z1,y)={ex['r_z1y']}, "
                  f"R(z2,y)={ex['r_z2y']}")
    print()
    return failures == 0


def theoretical_proof_q7():
    """Theoretical proof that modified profile-copy always works.

    For non-PP-parent z and PP-parent z':
    We need: R(z,x) ∈ comp(R(z,z'), R(z',y)) = comp(R(z,z'), DR)

    Since z' has R(z',x) = PP, the existing network has:
    R(z,x) ∈ comp(R(z,z'), R(z',x)) = comp(R(z,z'), PP)

    Check: comp(R, PP) ⊆ comp(R, DR) for the non-PP values?
    """
    print("=" * 70)
    print("Q7 THEORETICAL: comp(R, PP) \\ {PP} ⊆ comp(R, DR)?")
    print("=" * 70)
    print()
    print("For non-PP-parent z with R(z,z') = R (any relation) and")
    print("PP-parent z' (R(z',x) = PP → R(z',y) = DR):")
    print()
    print("Need: R(z,x) ∈ comp(R, DR) [for the modified profile]")
    print("Know: R(z,x) ∈ comp(R, PP) [from existing network]")
    print("Since R(z,x) ≠ PP: need comp(R, PP) \\ {PP} ⊆ comp(R, DR)")
    print()

    all_ok = True
    for r in RELS:
        comp_pp = set(COMP[(r, 'PP')])
        comp_dr = set(COMP[(r, 'DR')])
        non_pp = comp_pp - {'PP'}
        subset = non_pp <= comp_dr
        print(f"  R={r}: comp({r},PP)={comp_pp}, comp({r},DR)={comp_dr}")
        print(f"         comp({r},PP)\\{{PP}} = {non_pp} ⊆ comp({r},DR)? {'✓' if subset else '✗'}")
        if not subset:
            all_ok = False
            print(f"         MISSING: {non_pp - comp_dr}")
    print()
    if all_ok:
        print("  *** PROVED: comp(R,PP) \\ {PP} ⊆ comp(R,DR) for ALL R ***")
        print("  This means: any non-PP relation achievable via comp(R,PP)")
        print("  is also achievable via comp(R,DR). Modified profile is valid")
        print("  for the (z, z', y) triples.")
    else:
        print("  Some relations fail the inclusion.")
    print()

    # Also check: for two non-PP-parent z1, z2, profile-copy works
    print("For two non-PP-parents z1, z2 with R(z1,x) ≠ PP and R(z2,x) ≠ PP:")
    print("Need: R(z1,x) ∈ comp(R(z1,z2), R(z2,x)) — same as existing network")
    print("This is the SELF-ABSORPTION case, already verified ✓")
    print()


def question8_forall_mismatch_structure():
    """Q8: Structure of the ∀-constraint mismatch.

    For each PP-parent z of x, the mismatch is:
    - x receives: {D : ∀PP.D ∈ tp(z)} via R(z,x) = PP
    - y receives: {D : ∀DR.D ∈ tp(z)} via R(z,y) = DR

    Also from x/y's perspective (outgoing edges):
    - x sends: {D : ∀PPI.D ∈ tp(x)} to z via R(x,z) = PPI
    - y sends: {D : ∀DR.D ∈ tp(y)} to z via R(y,z) = DR

    Analyze: how large is the mismatch in typical cases?
    """
    print("=" * 70)
    print("Q8: ∀-constraint mismatch structure")
    print("=" * 70)
    print()
    print("When R(z,x) = PP changes to R(z,y) = DR:")
    print()
    print("INCOMING constraints (z → node):")
    print("  Role ∀PP.D:  triggers for x (PP=PP ✓) but NOT for y (DR≠PP)")
    print("  Role ∀DR.D:  triggers for y (DR=DR ✓) but NOT for x (PP≠DR)")
    print("  Role ∀PO.D:  neither (PP≠PO, DR≠PO)")
    print("  Role ∀PPI.D: neither (PP≠PPI, DR≠PPI)")
    print()
    print("OUTGOING constraints (node → z):")
    print("  R(x,z) = PPI, R(y,z) = DR")
    print("  Role ∀PPI.D: triggers from x (PPI=PPI ✓) but NOT from y (DR≠PPI)")
    print("  Role ∀DR.D:  triggers from y (DR=DR ✓) but NOT from x (PPI≠DR)")
    print("  Role ∀PO.D:  neither")
    print("  Role ∀PP.D:  neither")
    print()
    print("SUMMARY OF TYPE DIFFERENCES:")
    print("  tp(y) has EXTRA:  {D : ∀DR.D ∈ tp(z)} \\ tp(x)")
    print("  tp(y) is MISSING: {D : ∀PP.D ∈ tp(z)} if they were only from z")
    print("     (but x might have D from other sources)")
    print()
    print("  z's type constraints from y: {D : ∀DR.D ∈ tp(y)} (must be in tp(z))")
    print("  z's type constraints from x: {D : ∀PPI.D ∈ tp(x)} (already in tp(z))")
    print()
    print("CRITICAL SCENARIO for clash:")
    print("  z has ∀DR.D, D ∉ tp(x)")
    print("  → y must have D (from z's ∀DR.D via R(z,y)=DR)")
    print("  → but tp(y) is supposed to equal tp(x)")
    print("  → TYPE MISMATCH: y needs enriched type")
    print()
    print("CRITICAL SCENARIO for outgoing clash:")
    print("  y has ∀DR.D (either from tp(x) or enriched), D ∉ tp(z)")
    print("  → z must have D (from y's ∀DR.D via R(y,z)=DR)")
    print("  → but tp(z) is fixed (z is already expanded)")
    print("  → if D ∉ tp(z): BACKFLOW CLASH!")
    print()

    # Analyze: when does ∀DR.D at y (= x) NOT match tp(z)?
    # y has ∀DR.D ∈ tp(y). R(y,z) = DR. So z must have D.
    # In x's world: ∀DR.D ∈ tp(x), R(x,z) = PPI. ∀DR.D doesn't trigger (PPI≠DR).
    # So z was never required to have D from x's perspective.
    # z has D iff some OTHER node constrained it, or it was in z's initial type.
    print("BACKFLOW ANALYSIS:")
    print("  y has ∀DR.D ∈ tp(y). R(y,z) = DR → z needs D.")
    print("  x had ∀DR.D ∈ tp(x). R(x,z) = PPI → z didn't need D from x.")
    print("  So D ∈ tp(z) iff some OTHER source provided it.")
    print()
    print("  This means: the backflow clash is possible.")
    print("  y = tp(x) has ∀DR.D, and z (PP-parent) may lack D.")
    print()
    print("  In a MODEL: y is the actual DR-witness. tp(y) includes D")
    print("  from z's ∀DR.D. y also has ∀DR.D (if tp(x) has it).")
    print("  R(y,z) = DR → z needs D from y's ∀DR.D. But z may not have D!")
    print()
    print("  Wait — does z have D in the model?")
    print("  y's ∀DR.D at z: requires D ∈ tp(z) since R(y,z) = DR.")
    print("  But ∀DR.D ∈ tp(y), and tp(y) may NOT equal tp(x)!")
    print("  In the model, tp(y) is whatever the model assigns.")
    print("  ∀DR.D ∈ tp(y) iff the model satisfies it at y.")
    print()
    print("  KEY POINT: In the model, ∀DR.D ∈ tp(y) is determined by the")
    print("  model, not by copying from x. If ∀DR.D ∉ tp(y) in the model,")
    print("  there's no backflow problem. The model is self-consistent.")
    print()
    print("  The backflow issue arises ONLY in the profile-blocking approach")
    print("  where we force tp(y) = tp(x). It's an artifact of the blocking")
    print("  strategy, not of the model theory.")
    print()


def question9_enrichment_cascade():
    """Q9: Type enrichment cascade analysis.

    If y (DR-witness of x with PP-parent z) gets enriched type:
      tp(y) = tp(x) ∪ {D : ∀DR.D ∈ tp(z), R(z,x)=PP}

    Does tp(y) have new ∃-demands that create further enrichment?

    The new formulas D come from z's ∀DR.D. Each D is in cl(C).
    If D = ∃S.C' for some S, then y has a new ∃-demand.
    The witness for this demand gets edges to all existing nodes.
    By Q2 (PP-avoidable), the witness has no PP-parents.
    So the witness's type is determined by standard profile-copy.
    → NO FURTHER ENRICHMENT at level 2+.
    """
    print("=" * 70)
    print("Q9: Type enrichment cascade")
    print("=" * 70)
    print()
    print("Level 0: x has type tp(x), demand ∃DR.C")
    print("Level 1: y (DR-witness of x)")
    print("  - R(z,y) = DR for PP-parents z of x (forced)")
    print("  - R(z,y) = R(z,x) for non-PP-parents z (profile copy)")
    print("  - tp(y) = tp(x) ∪ Δ where Δ = {D : ∀DR.D ∈ tp(z), R(z,x)=PP}")
    print("  - y MAY have new ∃-demands from Δ")
    print()
    print("Level 2: w (any witness of y)")
    print("  - y has NO PP-parents (by Q2: PP always avoidable)")
    print("  - So w uses exact profile-copy: R(z,w) = R(z,y) for all z")
    print("  - tp(w) is determined by standard ∀-rule application")
    print("  - NO enrichment needed at this level")
    print()
    print("Level 3+: descendants of w")
    print("  - w also has no PP-parents (its profile was copied from y)")
    print("  - Wait — can w have PP-parents from OTHER nodes?")
    print()

    # Check: if y has no PP-parents, can y's witness w have PP-parents?
    # w is a witness of y with R(y,w) = S for some S.
    # For z (another node), R(z,w) is determined by the extension.
    # R(z,w) = PP requires PP ∈ comp(R(z,y), S).
    # y has no PP-parents: R(z,y) ≠ PP for all z.
    print("Can w (witness of y) have PP-parents?")
    print("R(z,w) = PP requires PP ∈ comp(R(z,y), S) where S = R(y,w)")
    print()
    for s in RELS:
        print(f"  Witness rel S = {s}:")
        for r_zy in RELS:
            dom = COMP[(r_zy, s)]
            has_pp = 'PP' in dom
            if has_pp:
                print(f"    R(z,y) = {r_zy}: PP ∈ comp({r_zy},{s}) = {set(dom)} — PP possible!")

    print()
    print("PP is possible when R(z,y) = DR and S ∈ {DR, PO, PP}.")
    print()
    print("So even though y has no PP-parents, y's witness w CAN have")
    print("PP-parents (from nodes z with R(z,y) = DR).")
    print()
    print("BUT: by Q2, we can ALWAYS avoid PP edges to w.")
    print("So we CHOOSE not to give w any PP-parents.")
    print()
    print("Wait — Q2 only proved PP-avoidability for DR-witnesses.")
    print("What about PO/PP/PPI witnesses?")
    print()

    # Check PP-avoidability for ALL witness relations
    print("PP-avoidability by witness relation:")
    for s in RELS:
        print(f"\n  Witness relation S = {s}:")
        print(f"  R(z,y) = R requires PP ∈ comp(R, {s}):")
        for r in RELS:
            if 'PP' in COMP[(r, s)]:
                print(f"    R(z,y) = {r}: PP ∈ comp({r},{s}) — PP possible")
        # For profile-copy: R(z,w) = R(z,y). PP appears only if R(z,y) = PP.
        # Since y has no PP-parents, R(z,y) ≠ PP. But R(z,y) could be DR,
        # and comp(DR, S) may contain PP.
        # For profile-copy: R(z,w) = R(z,y), not from comp(R(z,y), S).
        # Wait, the profile-copy gives R(z,w) = R(z,y), which satisfies
        # R(z,w) ∈ comp(R(z,y), S) by self-absorption.
        # Since R(z,y) ≠ PP (no PP-parents for y), R(z,w) ≠ PP.
        # So w has no PP-parents either!

    print()
    print("BUT for profile-copy: R(z,w) = R(z,y). Since y has no PP-parents,")
    print("R(z,y) ≠ PP for all z. So R(z,w) ≠ PP for all z.")
    print("→ w has no PP-parents either!")
    print()
    print("For non-profile-copy (DR-witness w of y with PP-parent z):")
    print("  z would need R(z,y) = PP, but y has no PP-parents. Contradiction!")
    print("  So DR-witnesses of y ALSO never face the DR+PP problem.")
    print()
    print("=" * 70)
    print("CONCLUSION: Enrichment cascade is DEPTH-1 ONLY")
    print("=" * 70)
    print()
    print("1. At depth 0: x may have PP-parents → DR-witness y gets enriched type")
    print("2. y has NO PP-parents (by PP-avoidable extension)")
    print("3. ALL descendants of y can use exact profile-copy")
    print("4. Profile-copy preserves 'no PP-parents' property")
    print("5. Therefore: enrichment happens only at depth 1, never cascades")
    print()


def question10_decidability_implications():
    """Q10: What does this mean for decidability?"""
    print("=" * 70)
    print("Q10: Implications for ALCI_RCC5 decidability")
    print("=" * 70)
    print()
    print("THEOREM (proposed): ALCI_RCC5 concept satisfiability is decidable.")
    print()
    print("PROOF SKETCH using 'enriched profile-blocking':")
    print()
    print("1. TABLEAU PROCEDURE:")
    print("   - Standard complete-graph tableau with blocking")
    print("   - When creating witness y for ∃S.C at x:")
    print("     * If S ∈ {PO, PP, PPI}: use profile-copy for all edges")
    print("     * If S = DR: use modified profile (PP-parents get DR)")
    print("   - Blocking condition: y is blocked by earlier x' if:")
    print("     * tp(y) = tp(x') [standard type match]")
    print("     * The 'enriched edge profile' matches")
    print()
    print("2. TERMINATION:")
    print("   - Finitely many types (bounded by 2^|cl(C)|)")
    print("   - Finitely many edge profiles (bounded by (|RELS|+1)^n for n nodes)")
    print("   - The tableau must terminate")
    print()
    print("3. COMPLETENESS (satisfiable → open branch):")
    print("   - Standard: model guides nondeterministic choices")
    print("   - Q1 guarantees edge assignments always exist")
    print()
    print("4. SOUNDNESS (open branch → model):")
    print("   - Key insight: unraveling uses modified profile-copy")
    print("   - For PO/PP/PPI witnesses: exact profile-copy → same ∀-constraints")
    print("   - For DR witnesses: modified profile → enriched type")
    print("     * Enrichment is depth-1 only (Q9)")
    print("     * The enriched type is clash-free (guaranteed by model existence)")
    print("     * All descendants use exact profile-copy (no further enrichment)")
    print()
    print("   HOWEVER — there's a gap in step 4:")
    print("   The 'enriched type is clash-free' claim relies on model existence,")
    print("   which is what we're trying to prove. This is circular.")
    print()
    print("   The correct argument needs:")
    print("   (a) The tableau's open branch certifies that the enriched type")
    print("       is clash-free (the tableau computed it and found no clash)")
    print("   (b) The modified profile is composition-consistent (Q7)")
    print("   (c) The unraveling produces a valid model")
    print()
    print("   For (a): YES — the tableau's ∀-rule fires for all edges,")
    print("   including the modified edges. If the enriched type had a clash,")
    print("   the branch would close.")
    print()
    print("   For (c): Q1 + Q7 + depth-1 enrichment guarantee this.")
    print()
    print("=" * 70)
    print("REMAINING CONCERN: outgoing ∀-constraint backflow")
    print("=" * 70)
    print()
    print("When y (enriched type) has ∀DR.D ∈ tp(y) and R(y,z) = DR,")
    print("z must have D ∈ tp(z). But x had ∀DR.D and R(x,z) = PPI,")
    print("so z was NOT required to have D from x's perspective.")
    print()
    print("In the TABLEAU: the ∀-rule at y adds D to z's type if R(y,z)=DR")
    print("and ∀DR.D ∈ tp(y). This is computed during tableau expansion.")
    print("If D ∉ tp(z) causes a clash in z, the branch closes.")
    print("If D is compatible with tp(z), z's type grows.")
    print()
    print("The issue: z is an EXISTING node whose type was already established.")
    print("Adding D to tp(z) may trigger further ∀-propagation from z,")
    print("causing a cascade of type growth in the existing network.")
    print()
    print("BUT: types are bounded by cl(C), and type growth is monotonic.")
    print("So the cascade terminates. The question is whether it introduces")
    print("clashes. In a satisfiable concept, the model shows no clash occurs.")
    print()
    print("WAIT — in the UNRAVELING (model construction from open tableau),")
    print("we're not running the tableau. We're building the model directly.")
    print("The types are FIXED by the tableau. We need to choose edges such")
    print("that the fixed types satisfy all ∀-constraints.")
    print()
    print("For the modified profile: R(y,z) = DR (since R(z,y)=DR → R(y,z)=DR).")
    print("If ∀DR.D ∈ tp(y) and D ∉ tp(z): this is a VALID constraint violation.")
    print("The model construction FAILS for this edge assignment.")
    print()
    print("Can we choose a DIFFERENT assignment? R(z,y) is forced to DR")
    print("(since R(z,x)=PP and comp(PP,DR)={DR}). So R(y,z)=DR is forced.")
    print("There's no flexibility.")
    print()
    print("So: if ∀DR.D ∈ tp(y) and D ∉ tp(z) and R(z,x)=PP, the model")
    print("construction genuinely fails. This is a REAL obstacle.")
    print()
    print("But: does this situation arise in a SATISFIABLE concept?")
    print("In a model M |= C:")
    print("  - x, y, z are elements with R(z,x)=PP, R(x,y)=DR")
    print("  - R(z,y)=DR is forced (comp(PP,DR)={DR})")
    print("  - R(y,z)=DR")
    print("  - If ∀DR.D ∈ tp_M(y): D ∈ tp_M(z) (model satisfies constraint)")
    print("  - So in the model, D IS in tp(z)")
    print()
    print("The issue is: tp(y) in the unraveling is the ENRICHED type")
    print("(not the model's type for y). The enriched type may include")
    print("∀DR.D that the model's y doesn't have.")
    print()
    print("But the enriched type is tp(x) ∪ Δ, which may have EXTRA formulas")
    print("compared to the model's tp(y). These extra formulas include")
    print("∀DR.D from tp(x), which applies to z via R(y,z)=DR.")
    print()
    print("In the model: ∀DR.D ∈ tp_M(x) → for all e with R(x,e)=DR: D ∈ tp_M(e)")
    print("z has R(x,z) = PPI ≠ DR, so ∀DR.D at x doesn't constrain z.")
    print("But R(y,z) = DR, and ∀DR.D ∈ tp(y) (copied from x), so D must be in tp(z).")
    print()
    print("In the MODEL: ∀DR.D ∈ tp_M(y)? Only if the model assigns ∀DR.D to y.")
    print("The model's y may NOT have ∀DR.D (y may have a different type from x).")
    print()
    print("So the backflow clash is an artifact of FORCING tp(y) to contain")
    print("tp(x)'s formulas. The model's y has a DIFFERENT type that avoids")
    print("the backflow.")
    print()
    print("=" * 70)
    print("REFINED CONCLUSION")
    print("=" * 70)
    print()
    print("Profile-blocking (even modified) forces tp(y) ⊇ tp(x).")
    print("But the model's DR-witness y may have tp(y) ≠ tp(x).")
    print("The backflow from tp(x)'s ∀DR.D is an artifact of profile-blocking.")
    print()
    print("CORRECT APPROACH: Don't force tp(y) = tp(x) for DR-witnesses.")
    print("Instead, let the tableau COMPUTE y's type from the ∀-rule")
    print("applications (which account for the modified edges).")
    print("Then block y by any earlier node with the SAME COMPUTED TYPE")
    print("and SAME MODIFIED PROFILE.")
    print()
    print("This is essentially standard type-blocking — but the type is")
    print("DETERMINED by the edge assignment, not copied from the blocker.")
    print()
    print("The soundness question then becomes:")
    print("  If y has the same computed type AND same profile as x',")
    print("  can y's subtree be replaced by x''s subtree?")
    print()
    print("For PO/PP/PPI witnesses: profile-copy → YES (identical context)")
    print("For DR witnesses: modified profile → same computed type AND")
    print("  same modified profile → YES (identical context up to PP→DR change)")
    print()
    print("And since y has no PP-parents, y's subtree develops identically")
    print("to x''s subtree. The unraveling is sound.")
    print()
    print("THE KEY INSIGHT: y's type is NOT tp(x). It's the type COMPUTED")
    print("by the ∀-rule for y's actual edges. This type accounts for")
    print("the DR edges from PP-parents. The backflow problem doesn't")
    print("arise because the computed type is self-consistent.")
    print()


def verify_backflow_resolution():
    """Verify that the 'computed type' approach resolves backflow.

    In the computed-type approach:
    - y's type is determined by: C (from ∃DR.C) + ∀-consequences from edges
    - y's edges: R(z,y) = DR for PP-parents, R(z,y) = R(z,x) for others
    - ∀-consequences: for each z, {D : ∀R(z,y).D ∈ tp(z)} flows into y
    - y's type = close(C ∪ ∪_z {D : ∀R(z,y).D ∈ tp(z)})

    For backflow: ∀S.D ∈ tp(y) and R(y,z) = S → D must be in tp(z)
    Question: is this always satisfied?

    In a model: yes (by consistency). But we're constructing from tableau.
    The tableau's ∀-rule propagates: when y is created with edges,
    for each ∀S.D ∈ tp(y) and each z with R(y,z) = S, D is added to tp(z).
    If D causes a clash in z, the branch closes.
    If no clash, the types are consistent.

    In the unraveling: types are fixed from the tableau. The edges are
    the same as in the tableau. So the ∀-constraints are satisfied.
    """
    print("=" * 70)
    print("BACKFLOW RESOLUTION VERIFICATION")
    print("=" * 70)
    print()
    print("In the TABLEAU (not unraveling):")
    print("  1. Create y as DR-witness of x")
    print("  2. Assign edges: R(z,y) = DR for PP-parents, copy for others")
    print("  3. ∀-rule: for each z, flow ∀-constraints over R(z,y) into y")
    print("     → determines tp(y) [may differ from tp(x)]")
    print("  4. ∀-rule: for each z, flow ∀-constraints over R(y,z) into z")
    print("     → may add formulas to tp(z)")
    print("  5. If any clash → branch closes")
    print("  6. If no clash → continue expanding y's demands")
    print()
    print("Step 4 is the backflow. It's handled by the TABLEAU itself.")
    print("The tableau adds D to tp(z) and checks for clashes.")
    print("If satisfiable, no clash occurs (model guides choices).")
    print()
    print("In the UNRAVELING from a completed tableau:")
    print("  - All types are final (∀-rules fully applied)")
    print("  - All edges are fixed")
    print("  - For blocked nodes: redirect to blocker")
    print("  - The redirected node has the SAME type and edges as the blocker")
    print("  - So all ∀-constraints are already satisfied")
    print()
    print("The only issue: CROSS-SUBTREE edges in the unraveling")
    print("(edges between nodes in different subtrees that didn't exist")
    print("in the original tableau).")
    print()
    print("In TREE-shaped unraveling: no cross-subtree edges")
    print("In COMPLETE-GRAPH unraveling: cross-subtree edges exist")
    print()
    print("For COMPLETE-GRAPH: each unraveled node needs edges to ALL")
    print("other unraveled nodes. These edges are new (not in tableau).")
    print("They must satisfy both RCC5-consistency and ∀-constraints.")
    print()
    print("Q1 guarantees RCC5-consistency. The ∀-constraint issue is:")
    print("  For nodes u,v in different subtrees:")
    print("  R(u,v) is chosen from composition constraints")
    print("  ∀S.D ∈ tp(u) and R(u,v) = S → D must be in tp(v)")
    print()
    print("Can we ALWAYS choose R(u,v) to avoid ∀-constraint violations?")
    print()

    # This is the fundamental question. Let me analyze it.
    # For two nodes u, v with known types, what edges are "safe"?
    # An edge R(u,v) = S is safe if:
    #   for all ∀S.D ∈ tp(u): D ∈ tp(v)
    #   for all ∀INV[S].D ∈ tp(v): D ∈ tp(u)

    # The question is: is there always a safe edge?

    # Consider: R(u,v) = DR is safe if:
    #   for all ∀DR.D ∈ tp(u): D ∈ tp(v)
    #   for all ∀DR.D ∈ tp(v): D ∈ tp(u)
    #   (since INV[DR] = DR)

    # This fails if u has ∀DR.D and D ∉ tp(v), or vice versa.
    # But DR is the "most universal" relation — it triggers ∀DR constraints.

    # What about EQ? R(u,v) = EQ requires u = v. Not useful.

    # What if u has ∀S.D for ALL S? Then no edge is safe unless D ∈ tp(v).
    # This happens when u has ∀DR.D ∧ ∀PO.D ∧ ∀PP.D ∧ ∀PPI.D = ∀⊤.D.
    # In this case, ALL elements must have D (except u itself with EQ).
    # So D IS in tp(v) in any model.

    # The tableau propagates this: when u is created, ∀-rules fire for
    # all edges, adding D to all neighbors. In the unraveling, the new
    # cross-subtree edge triggers the same addition. But types are FIXED
    # in the unraveling — we can't add D to tp(v) post-hoc.

    print("Analysis: when is edge R(u,v) = S 'safe'?")
    print("  Safe if: ∀S.D ∈ tp(u) → D ∈ tp(v)")
    print("       and ∀INV[S].D ∈ tp(v) → D ∈ tp(u)")
    print()
    print("If u has ∀S.D for some S with D ∉ tp(v):")
    print("  S is 'unsafe' for the u→v direction")
    print("  We need R(u,v) ≠ S")
    print()
    print("If ALL relations S are unsafe (u has ∀S.D for all S, D ∉ tp(v)):")
    print("  This means u has '∀⊤.D': universal value restriction")
    print("  In any model, ALL elements must have D")
    print("  So D ∈ tp(v) in any valid model")
    print("  The tableau would have propagated D to all nodes")
    print("  → This case doesn't arise in a completed open branch")
    print()
    print("For SPECIFIC relations: if u has ∀DR.D with D ∉ tp(v):")
    print("  Just avoid R(u,v) = DR. Use PO, PP, or PPI instead.")
    print("  These don't trigger ∀DR.D.")
    print()
    print("The question: can we find R(u,v) that's safe AND in the")
    print("composition domain AND consistent with all other edges?")
    print()
    print("This is a CSP with both RCC5 constraints and ∀-safety constraints.")
    print("The ∀-safety constraints REDUCE the domain for each edge.")
    print("If the reduced domain is non-empty, the CSP may be solvable.")
    print()
    print("CONJECTURE: The reduced CSP is always solvable for open tableau branches.")
    print("REASON: The model provides a solution (all edges in the model are safe).")
    print()
    print("But this is circular — the model is what we're trying to construct.")
    print()
    print("=" * 70)
    print("FUNDAMENTAL STATUS")
    print("=" * 70)
    print()
    print("The core obstacle is the CROSS-SUBTREE EDGE assignment problem.")
    print("This is EQUIVALENT to the extension gap, viewed differently:")
    print()
    print("  Extension gap (quasimodel): abstract types → concrete model")
    print("  Cross-subtree edges (tableau): finite graph → infinite model")
    print()
    print("Both reduce to: can we always assign edges between elements of")
    print("known types such that RCC5 + ∀-constraints are satisfied?")
    print()
    print("What our investigation HAS established:")
    print("  1. RCC5 assignment is ALWAYS possible (Q1)")
    print("  2. PP edges are avoidable for DR (Q2)")
    print("  3. Modified profile-copy is RCC5-consistent (Q7)")
    print("  4. Type enrichment doesn't cascade (Q9)")
    print("  5. The obstacle is SOLELY about ∀-constraint satisfaction")
    print("     in cross-subtree edge assignments")
    print()
    print("What WOULD close the gap:")
    print("  A proof that cross-subtree edges can always be chosen")
    print("  to satisfy ∀-constraints. This is a pure DL+RCC5 problem.")
    print()


if __name__ == '__main__':
    q7_ok = question7_modified_profile()
    if q7_ok:
        theoretical_proof_q7()
    question8_forall_mismatch_structure()
    question9_enrichment_cascade()
    question10_decidability_implications()
    verify_backflow_resolution()
