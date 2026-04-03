#!/usr/bin/env python3
"""
Investigate the DR+PP case for profile-blocking in ALCI_RCC5.

Profile-blocking: when creating witness y for ∃S.C at node x, we want y to
copy x's "profile" — i.e., for every existing node z, establish R(z,y) such
that the ∀-constraints flowing into y from z match those flowing into x from z.

For ∀-constraints to match, we need: for every ∀R.D constraint, if z has some
relation to x that triggers ∀R.D (meaning R(z,x) ∈ domain of R), then z must
have the SAME triggering relation to y. The simplest condition: R(z,y) = R(z,x)
for all z (exact profile copy).

Profile-copy requires: R(z,y) = R(z,x) must be composition-consistent with
R(x,y) = S. That means R(z,x) ∈ comp(R(z,x_parent)·...·R(x,y)) — but more
directly, the triple (z,x,y) requires:
    R(z,y) ∈ comp(R(z,x), R(x,y))
So we need R(z,x) ∈ comp(R(z,x), S).

This is the SELF-ABSORPTION property: R ∈ comp(R, S).

Self-absorption holds for S ∈ {PO, PP, PPI} for ALL R.
For S = DR: R ∈ comp(R, DR) fails when R = PP.
  comp(PP, DR) = {DR}, but we need PP ∈ {DR}. FAILS.

So profile-copy fails only for ∃DR.C when some z has R(z,x) = PP.

This script investigates whether a MODIFIED profile strategy can work:
instead of exact copy, allow R(z,y) ≠ R(z,x) for the problematic z-nodes,
while still ensuring (a) composition-consistency and (b) the ∀-constraints
flowing into y still match those for x.

KEY INSIGHT: If R(z,x) = PP and R(x,y) = DR, then R(z,y) must be in
comp(PP, DR) = {DR}. So R(z,y) = DR is forced. The question is: does this
cause a type mismatch? The ∀-constraints from z to x flow over PP, but from
z to y they flow over DR. These may differ.

We analyze:
1. When does ∀R.D trigger over PP vs DR? Answer: ∀PP.D triggers over PP (yes)
   and over DR (no). ∀DR.D triggers over DR (yes) and over PP (no). So the
   ∀-constraint sets are DIFFERENT — profile-blocking genuinely fails here.

2. Can we rescue this by choosing a different witness relation S ≠ DR?
   For ∃DR.C, the witness relation MUST be DR (since DR is an atomic role).

3. Can we rescue this by expanding the witness's type to include extra formulas?
   This would mean y's type is not a copy of x's type — different approach.

4. Systematic check: enumerate all configurations and verify the analysis.
"""

from extension_gap_checker import RELS, INV, COMP, is_triple_consistent

def check_self_absorption():
    """Check R ∈ comp(R, S) for all R, S."""
    print("Self-absorption check: R ∈ comp(R, S)?")
    print(f"{'R\\S':<6}", end="")
    for s in RELS:
        print(f"{s:<6}", end="")
    print()
    for r in RELS:
        print(f"{r:<6}", end="")
        for s in RELS:
            result = r in COMP[(r, s)]
            print(f"{'✓' if result else '✗':<6}", end="")
        print()
    print()


def check_profile_copy_feasibility():
    """For each witness relation S and each possible R(z,x), check if
    profile copy R(z,y) = R(z,x) is composition-consistent."""
    print("Profile-copy feasibility: R(z,x) ∈ comp(R(z,x), S)?")
    print("(Same as self-absorption, shown as domains)")
    print()
    for s in RELS:
        print(f"Witness relation S = {s}:")
        for r in RELS:
            domain = COMP[(r, s)]
            copy_ok = r in domain
            print(f"  R(z,x) = {r}: comp({r},{s}) = {set(domain)}, "
                  f"copy {'OK' if copy_ok else 'FAILS'}"
                  f"{'' if copy_ok else f' → forced to {set(domain)}'}")
        print()


def analyze_forall_mismatch():
    """Analyze ∀-constraint mismatch when R(z,x) = PP but R(z,y) = DR.

    The key question: what ∀-constraints flow over PP vs DR?

    In ALCI_RCC5:
    - ∀DR.D flows when the relation is DR (the role DR is an atomic role)
    - ∀PP.D flows when the relation is PP
    - ∀PO.D flows when the relation is PO
    - ∀PPI.D flows when the relation is PPI

    But also consider INVERSE roles:
    - If R(z,x) = PP, then R(x,z) = PPI. So from x's perspective, z is
      reached via PPI. Constraints ∀PPI.D at x apply to z.
    - If R(z,y) = DR, then R(y,z) = DR. So from y's perspective, z is
      reached via DR. Constraints ∀DR.D at y apply to z.

    For profile-blocking to work, we need y to have the same type as x.
    If x has ∀PPI.D in its type, then z must satisfy D (since R(x,z) = PPI).
    If y has ∀PPI.D in its type (same as x), then z must satisfy D only if
    R(y,z) = PPI. But R(y,z) = DR ≠ PPI, so this constraint is NOT triggered.
    → This is fine (fewer constraints on z from y's perspective).

    BUT: if x has ∀DR.D in its type, then z doesn't need to satisfy D
    (since R(x,z) = PPI ≠ DR). But y has ∀DR.D too, and R(y,z) = DR,
    so z MUST satisfy D from y's perspective.
    → This is problematic! z may not have D in its type.
    """
    print("∀-constraint flow analysis for PP→DR mismatch:")
    print()
    print("Given: R(z,x) = PP, so R(x,z) = PPI")
    print("Forced: R(z,y) = DR, so R(y,z) = DR")
    print()
    print("Constraints at x that TRIGGER on z (via R(x,z) = PPI):")
    print("  ∀PPI.D  → z must satisfy D   [TRIGGERS]")
    print("  ∀DR.D   → z need not satisfy D [does not trigger]")
    print("  ∀PO.D   → z need not satisfy D [does not trigger]")
    print("  ∀PP.D   → z need not satisfy D [does not trigger]")
    print()
    print("Constraints at y that TRIGGER on z (via R(y,z) = DR):")
    print("  ∀DR.D   → z must satisfy D   [TRIGGERS]")
    print("  ∀PPI.D  → z need not satisfy D [does not trigger]")
    print("  ∀PO.D   → z need not satisfy D [does not trigger]")
    print("  ∀PP.D   → z need not satisfy D [does not trigger]")
    print()
    print("MISMATCH: y has ∀DR.D → z must satisfy D")
    print("  But x has ∀DR.D and R(x,z) = PPI, so z was never required to satisfy D.")
    print("  If D ∉ tp(z), then y's constraint ∀DR.D is violated.")
    print()
    print("ALSO: x has ∀PPI.D → z must satisfy D")
    print("  But y has ∀PPI.D and R(y,z) = DR ≠ PPI, so this doesn't trigger.")
    print("  This direction is SAFE (fewer constraints).")
    print()
    print("CONCLUSION: The PP→DR change causes ∀DR.D constraints at y to")
    print("  apply to z, but z may not satisfy D. Profile-blocking FAILS")
    print("  when x (= y's type donor) has any ∀DR.D in its type AND")
    print("  some existing z has R(z,x) = PP.")
    print()


def analyze_incoming_perspective():
    """Analyze from z's perspective (incoming edges into x vs y).

    Also need to check: constraints at z that apply to x vs y.
    If z has ∀R.D for some R, then:
    - x must satisfy D if R(z,x) = PP matches R → only ∀PP.D
    - y must satisfy D if R(z,y) = DR matches R → only ∀DR.D

    Since x and y have the same type, x satisfies D iff y satisfies D.
    But the TRIGGERING is different:
    - ∀PP.D at z triggers for x (R(z,x) = PP) but NOT for y (R(z,y) = DR)
      → SAFE (fewer constraints on y)
    - ∀DR.D at z triggers for y (R(z,y) = DR) but NOT for x (R(z,x) = PP)
      → PROBLEMATIC! y must satisfy D but x wasn't required to.
      However, y has the same type as x. So y satisfies D iff x satisfies D.
      If D ∉ tp(x) = tp(y), this is a type violation.
    """
    print("Incoming constraint analysis (z → x vs z → y):")
    print()
    print("z has ∀PP.D: triggers for x (R(z,x)=PP ✓) but not y (R(z,y)=DR ✗)")
    print("  → Safe: fewer constraints on y")
    print()
    print("z has ∀DR.D: triggers for y (R(z,y)=DR ✓) but not x (R(z,x)=PP ✗)")
    print("  → PROBLEM: y = tp(x) may not have D")
    print()
    print("z has ∀PO.D: neither triggers (PP ≠ PO, DR ≠ PO)")
    print("  → Safe: no change")
    print()
    print("z has ∀PPI.D: neither triggers (PP ≠ PPI, DR ≠ PPI)")
    print("  → Safe: no change")
    print()


def analyze_rescue_strategies():
    """Analyze possible rescue strategies for the DR+PP case."""
    print("="*60)
    print("RESCUE STRATEGIES")
    print("="*60)
    print()

    # Strategy 1: Different witness relation
    print("Strategy 1: Use S ≠ DR for the witness relation")
    print("-" * 40)
    print("For ∃DR.C, we need R(x,y) = DR. The role name IS the relation.")
    print("There is no flexibility here. RULED OUT.")
    print()

    # Strategy 2: Non-profile blocking — block if TYPES match
    print("Strategy 2: Type-only blocking (ignore profile)")
    print("-" * 40)
    print("Block y by x if tp(y) = tp(x), regardless of edges.")
    print("This is standard anywhere-blocking. But we lose the guarantee")
    print("that the blocked node can be unraveled — precisely the quasimodel")
    print("extension gap problem. INSUFFICIENT on its own.")
    print()

    # Strategy 3: Conditional profile-blocking
    print("Strategy 3: Conditional profile-blocking")
    print("-" * 40)
    print("Profile-blocking works UNLESS:")
    print("  (a) The demand is ∃DR.C, AND")
    print("  (b) Some existing z has R(z,x) = PP")
    print("In all other cases, profile-blocking works perfectly.")
    print()
    print("For case (a)+(b), fall back to standard type-blocking.")
    print("Question: is this special case actually problematic in practice?")
    print()
    print("Key observation: R(z,x) = PP means x is a proper part of z.")
    print("In the tableau, this happens when z was created as a PPI-witness")
    print("of some ancestor, and x ended up inside z. The ∃DR.C demand at x")
    print("needs a witness y disjoint from x. The issue: y is forced to be")
    print("disjoint from z too (since comp(PP, DR) = {DR}), but x's profile")
    print("has PP from z, not DR.")
    print()

    # Strategy 4: Enriched blocking condition
    print("Strategy 4: Enriched blocking — allow modified profile")
    print("-" * 40)
    print("Instead of requiring R(z,y) = R(z,x) for all z, require:")
    print("  R(z,y) = R(z,x) for z where R(z,x) ≠ PP")
    print("  R(z,y) = DR     for z where R(z,x) = PP (forced by composition)")
    print()
    print("Then check: can we guarantee that y's type is satisfiable?")
    print("y has the same type as x. The difference in ∀-constraints:")
    print("  - ∀DR.D at y triggers on z (where it didn't for x) — potential clash")
    print("  - ∀PP.D at y doesn't trigger on z (where it did for x) — safe")
    print("  - ∀PPI.D at x triggered on z; at y it doesn't — safe")
    print()
    print("The ONLY problematic scenario:")
    print("  x has ∀DR.D in type, z has R(z,x) = PP, and D ∉ tp(z)")
    print()
    print("But wait — if x has ∀DR.D, then for x's OWN ∀-constraints,")
    print("any element e with R(x,e) = DR must have D ∈ tp(e).")
    print("Now R(x,z) = PPI (since R(z,x) = PP), so ∀DR.D at x does NOT")
    print("constrain z. So D may indeed be absent from tp(z).")
    print()
    print("HOWEVER — from z's perspective: z has ∀DR.D means all elements")
    print("at DR from z must have D. R(z,y) = DR, so z's ∀DR.D requires")
    print("D ∈ tp(y). Since tp(y) = tp(x), this requires D ∈ tp(x).")
    print("But D may not be in tp(x)!")
    print()
    print("Concrete example of the problem:")
    print("  x: type has {∃DR.C} but not {D}")
    print("  z: type has {∀DR.D}, R(z,x) = PP")
    print("  Create y as DR-witness of x, R(z,y) = DR forced")
    print("  z's ∀DR.D requires D ∈ tp(y) = tp(x), but D ∉ tp(x)")
    print("  → CLASH")
    print()

    # Strategy 5: Check if PP from z to x implies z's ∀DR constraints are vacuous
    print("Strategy 5: Structural argument — PP excludes DR-constraints")
    print("-" * 40)
    print("Claim: if R(z,x) = PP, can z have ∀DR.D in its type with D ∉ tp(x)?")
    print()
    print("Consider: z has ∀DR.D. R(z,x) = PP, so ∀DR.D does NOT apply to x")
    print("(since PP ≠ DR). So D ∉ tp(x) is perfectly possible.")
    print()
    print("The question becomes: in a VALID model, if R(z,x) = PP and we add")
    print("y with R(x,y) = DR and R(z,y) = DR, does z's ∀DR.D force D ∈ tp(y)?")
    print("YES. And tp(y) = tp(x), so D must be in tp(x). But it isn't.")
    print()
    print("This is NOT just a profile-blocking failure — it's a GENUINE")
    print("constraint incompatibility. The new element y inherits constraints")
    print("from z (via the forced DR edge) that x didn't have.")
    print()
    print("KEY QUESTION: Does this mean ∃DR.C at x CANNOT have a witness y")
    print("that copies x's type? Or only that such a witness can't be")
    print("disjoint from z?")
    print()
    print("In the actual MODEL (not tableau), the witness for ∃DR.C at x")
    print("is some element y with R(x,y) = DR and C ∈ tp(y). The relation")
    print("R(z,y) in the model can be ANYTHING in comp(PP, DR) = {DR}.")
    print("So R(z,y) = DR is forced in the MODEL too!")
    print()
    print("This means: in any model where R(z,x) = PP, z has ∀DR.D, and")
    print("x has a DR-witness y, we MUST have D ∈ tp(y). The witness y")
    print("cannot have the same type as x unless D ∈ tp(x).")
    print()
    print("CONCLUSION: This is not a flaw of profile-blocking — it's a")
    print("genuine model-theoretic constraint. The DR-witness of x CANNOT")
    print("generally have the same type as x when PP-parents constrain it.")
    print("Profile-blocking (with any variation) cannot work for this case.")
    print()


def analyze_frequency():
    """How often does the DR+PP case arise in practice?"""
    print("="*60)
    print("FREQUENCY ANALYSIS: When does R(z,x) = PP arise?")
    print("="*60)
    print()
    print("In the complete-graph tableau, R(z,x) = PP means x is a proper")
    print("part of z. This happens when:")
    print("  1. z was created as a PPI-witness: ∃PPI.C at some ancestor w,")
    print("     so R(w,z) = PPI, meaning R(z,w) = PP. Then x = w has PP from z.")
    print("  2. Transitivity chains: if R(z,w) = PP and R(w,x) = PP,")
    print("     then R(z,x) ∈ comp(PP,PP) = {PP}. So PP propagates down.")
    print()
    print("In the EXISTING tableau approach, every new node gets edges to ALL")
    print("existing nodes. The relation R(z,y) is chosen from the composition")
    print("table. But in the profile-blocking approach, R(z,y) is determined")
    print("by the blocking condition.")
    print()
    print("Observation: if the TBox has NO role 'DR' in existential restrictions")
    print("(i.e., no ∃DR.C), then the DR+PP case never arises — profile-blocking")
    print("works perfectly for ∃PO.C, ∃PP.C, ∃PPI.C.")
    print()
    print("Observation: if the TBox has no ∃PPI.C (so no PP edges are created"),
    print("from children to parents), and the initial network has no PP edges,")
    print("then R(z,x) = PP never occurs — profile-blocking works for ∃DR.C too.")
    print()
    print("The problematic combination: ∃DR.C AND ∃PPI.C' both in the TBox.")
    print()


def profile_blocking_summary():
    """Summary of profile-blocking analysis."""
    print("="*60)
    print("SUMMARY: Profile-Blocking for ALCI_RCC5")
    print("="*60)
    print()
    print("DEFINITION: Node y is profile-blocked by x if:")
    print("  (B1) tp(y) = tp(x)")
    print("  (B2) For every existing z, R(z,y) = R(z,x)  [profile copy]")
    print("  (B3) The edge assignment is composition-consistent")
    print()
    print("THEOREM: Profile-blocking is sound (blocked nodes can be unraveled)")
    print("whenever it is applicable.")
    print()
    print("APPLICABILITY:")
    print("  ∃PO.C  — ALWAYS works (PO self-absorbs for all R)")
    print("  ∃PP.C  — ALWAYS works (PP self-absorbs for all R)")
    print("  ∃PPI.C — ALWAYS works (PPI self-absorbs for all R)")
    print("  ∃DR.C  — works UNLESS some z has R(z,x) = PP")
    print()
    print("FAILURE CASE: ∃DR.C at x when ∃z: R(z,x) = PP")
    print("  - Composition forces R(z,y) = DR ≠ PP = R(z,x)")
    print("  - Different ∀-constraints flow: z's ∀DR.D hits y but not x")
    print("  - This is a genuine model-theoretic constraint, not an artifact")
    print("  - The DR-witness MUST have different type constraints than x")
    print()
    print("PRACTICAL IMPACT:")
    print("  - Affects only TBoxes with BOTH ∃DR.C and ∃PPI.C'")
    print("  - For ∃PPI.C-free TBoxes, profile-blocking is complete")
    print("  - For ∃DR.C-free TBoxes, profile-blocking is complete")
    print()
    print("RESIDUAL QUESTION:")
    print("  For the DR+PP case, standard anywhere-blocking must be used.")
    print("  The soundness of standard blocking requires the quasimodel")
    print("  extraction argument, which has the extension gap.")
    print("  So profile-blocking NARROWS the gap but does not close it:")
    print("  the gap only matters for TBoxes with both ∃DR and ∃PPI roles.")
    print()


def verify_self_absorption_computationally():
    """Verify self-absorption with full triple-consistency check."""
    print("="*60)
    print("COMPUTATIONAL VERIFICATION")
    print("="*60)
    print()
    print("For each witness relation S and each existing relation R(z,x),")
    print("enumerate all possible networks and check if profile-copy")
    print("R(z,y) = R(z,x) is always achievable.")
    print()

    # For each S (witness relation x→y):
    for s in RELS:
        print(f"--- Witness relation S = {s} (R(x,y) = {s}) ---")
        failures = []
        for n_existing in [2, 3, 4]:  # number of existing nodes (including x)
            # Enumerate consistent base networks on n_existing nodes
            # Node 0 = x, nodes 1..n-1 = existing z-nodes
            from extension_gap_checker import enumerate_consistent_networks
            for base_net in enumerate_consistent_networks(n_existing):
                # Try to add node y with R(x,y) = s and R(z,y) = R(z,x) for z ≠ x
                # Check if this extended network is consistent
                y = n_existing  # new node index

                # Build extended network
                ext = dict(base_net)
                # R(x,y) = R(0,y)
                if 0 < y:
                    ext[(0, y)] = s
                else:
                    ext[(y, 0)] = INV[s]

                # For each z ≠ x, R(z,y) = R(z,x) = R(z,0)
                ok = True
                for z in range(1, n_existing):
                    r_zx = base_net.get((min(z,0), max(z,0)))
                    if z > 0:
                        r_zx_directed = r_zx  # z > 0, so (0,z) is stored, R(0,z)
                        # We need R(z,x) = R(z,0) = INV[R(0,z)]
                        r_zx_directed = INV[r_zx]
                    else:
                        r_zx_directed = r_zx

                    # R(z,y): since z < y, we store (z,y) = R(z,y) = r_zx_directed
                    # But we need to check it's in comp(R(z,x), R(x,y)) = comp(r_zx_directed, s)
                    domain = COMP.get((r_zx_directed, s), frozenset())
                    if r_zx_directed not in domain:
                        failures.append((n_existing, dict(base_net), z, r_zx_directed, s))
                        ok = False
                        break

                if ok:
                    # Also verify all triples involving y are consistent
                    for z1 in range(n_existing):
                        for z2 in range(z1+1, n_existing):
                            if not ok:
                                break
                            # Triple (z1, z2, y)
                            r_z1z2_key = (z1, z2)
                            r_z1z2 = base_net[r_z1z2_key]

                            # R(z1, y)
                            if z1 == 0:
                                r_z1y = s  # R(x,y) = s = R(0,y)
                            else:
                                # R(z1,x) = INV[R(0,z1)] since (0,z1) stored
                                r_z1x = INV[base_net[(0, z1)]]
                                r_z1y = r_z1x  # profile copy

                            # R(z2, y)
                            # R(z2,x) = INV[R(0,z2)]
                            r_z2x = INV[base_net[(0, z2)]]
                            r_z2y = r_z2x  # profile copy

                            if not is_triple_consistent(r_z1z2, r_z2y, r_z1y):
                                # Profile copy causes triple inconsistency!
                                failures.append((n_existing, dict(base_net),
                                               (z1,z2), r_z1z2, r_z1y, r_z2y,
                                               'triple'))
                                ok = False

        if failures:
            # Filter to unique self-absorption failures
            sa_fails = [f for f in failures if len(f) == 5]
            triple_fails = [f for f in failures if len(f) == 7]
            if sa_fails:
                print(f"  Self-absorption failures: {len(sa_fails)}")
                for f in sa_fails[:3]:
                    n, net, z, r, s2 = f
                    print(f"    n={n}, R(z,x)={r}, S={s2}: {r} ∉ comp({r},{s2})={set(COMP[(r,s2)])}")
            if triple_fails:
                print(f"  Triple-consistency failures after profile-copy: {len(triple_fails)}")
                for f in triple_fails[:3]:
                    n, net, pair, r12, r1y, r2y, _ = f
                    print(f"    n={n}, (z1,z2)={pair}: R(z1,z2)={r12}, R(z1,y)={r1y}, R(z2,y)={r2y}")
                    print(f"      is_triple_consistent({r12}, {r2y}, {r1y}) = False")
        else:
            print(f"  Profile-copy ALWAYS works for S = {s}")
        print()


if __name__ == '__main__':
    check_self_absorption()
    check_profile_copy_feasibility()
    print()
    analyze_forall_mismatch()
    print()
    analyze_incoming_perspective()
    print()
    analyze_rescue_strategies()
    print()
    analyze_frequency()
    print()
    profile_blocking_summary()
    print()
    verify_self_absorption_computationally()
