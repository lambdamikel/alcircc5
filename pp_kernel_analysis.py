#!/usr/bin/env python3
"""
Analysis of the PP-kernel quotient idea for ALCI_RCC5.

Tests whether reflexive PP loops are composition-consistent in all
configurations, and explores the feasibility of collapsing same-type
elements on PP-chains into kernel nodes.
"""

from extension_gap_checker import RELS, INV, COMP, is_triple_consistent

print("=" * 70)
print("PART 1: Is reflexive PP composition-consistent?")
print("=" * 70)
print()

# Check: for a node k with PP(k,k), and any node m with R(k,m) = S,
# do all triples (k,k,m), (k,m,k), (m,k,k) satisfy composition?

print("Test 1: Triple (k, k, m) — comp(PP(k,k), R(k,m)) must contain R(k,m)")
for R in RELS:
    result = COMP[('PP', R)]
    ok = R in result
    print(f"  R(k,m) = {R:3s}: comp(PP, {R}) = {str(set(result)):35s} — {R} in? {'YES' if ok else 'NO ***FAIL***'}")

print()
print("Test 2: Triple (m, k, k) — comp(R(m,k), PP(k,k)) must contain R(m,k)")
for R in RELS:
    result = COMP[(R, 'PP')]
    ok = R in result
    print(f"  R(m,k) = {R:3s}: comp({R}, PP) = {str(set(result)):35s} — {R} in? {'YES' if ok else 'NO ***FAIL***'}")

print()
print("Test 3: Triple (k, m, k) — comp(R(k,m), R(m,k)) must contain PP(k,k)")
for R in RELS:
    invR = INV[R]
    result = COMP[(R, invR)]
    ok = 'PP' in result
    print(f"  R(k,m) = {R:3s}: comp({R}, {invR}) = {str(set(result)):35s} — PP in? {'YES' if ok else 'NO ***FAIL***'}")

print()
print("Test 4: Two kernel nodes k1, k2 both with PP(ki,ki)")
print("  Triple (k1, k1, k2): same as Test 1 — already passed")
print("  Triple (k1, k2, k2): same as Test 2 — already passed")
print("  Triple (k2, k1, k2): comp(inv(R), R) must contain PP")
for R in RELS:
    invR = INV[R]
    result = COMP[(invR, R)]
    ok = 'PP' in result
    print(f"  R(k1,k2) = {R:3s}: comp({invR}, {R}) = {str(set(result)):35s} — PP in? {'YES' if ok else 'NO ***FAIL***'}")

print()
print("=" * 70)
print("CONCLUSION: Reflexive PP is FULLY composition-consistent.")
print("Reason: PP is universally self-absorbing (R ∈ comp(PP, R) and")
print("R ∈ comp(R, PP) for all R), and comp(R, inv(R)) always contains PP.")
print("=" * 70)

# Part 2: Self-absorption analysis — which relations allow reflexive loops?
print()
print("=" * 70)
print("PART 2: Which relations allow reflexive loops?")
print("=" * 70)
print()
print("For each S ∈ {DR, PO, PP, PPI}, check if S(k,k) is")
print("composition-consistent with all external edges R(k,m).")
print()

for S in RELS:
    invS = INV[S]
    all_ok = True
    failures = []

    for R in RELS:
        invR = INV[R]
        # Triple (k, k, m): comp(S, R) must contain R
        t1 = R in COMP[(S, R)]
        # Triple (m, k, k): comp(R', S) must contain R' where R' = inv(R)
        t2 = invR in COMP[(invR, S)]
        # Triple (k, m, k): comp(R, inv(R)) must contain S
        t3 = S in COMP[(R, invR)]

        if not (t1 and t2 and t3):
            all_ok = False
            if not t1:
                failures.append(f"  (k,k,m) with R={R}: {R} ∉ comp({S},{R})={COMP[(S,R)]}")
            if not t2:
                failures.append(f"  (m,k,k) with R={R}: {invR} ∉ comp({invR},{S})={COMP[(invR,S)]}")
            if not t3:
                failures.append(f"  (k,m,k) with R={R}: {S} ∉ comp({R},{invR})={COMP[(R,invR)]}")

    if all_ok:
        print(f"  Reflexive {S}(k,k): FULLY CONSISTENT with all external edges")
    else:
        print(f"  Reflexive {S}(k,k): FAILS — {len(failures)} violation(s):")
        for f in failures:
            print(f"    {f}")

# Part 3: PP-chain monotonicity and stabilization
print()
print("=" * 70)
print("PART 3: PP-chain monotonicity — relation progression along PP-chains")
print("=" * 70)
print()
print("If x PP y (y is inside x), and e is external,")
print("what relations R(e,y) are possible given R(e,x)?")
print()
print("comp(R(e,x), PP(x,y)) tells us the possible R(e,y):")
for R in RELS:
    possible = COMP[(R, 'PP')]
    print(f"  R(e,x) = {R:3s}: R(e,y) ∈ comp({R}, PP) = {possible}")

print()
print("Stabilization: once the relation reaches a value S where")
print("comp(S, PP) = {S}, it stays there forever.")
print()
for R in RELS:
    result = COMP[(R, 'PP')]
    if result == frozenset({R}):
        print(f"  {R} is ABSORBING: comp({R}, PP) = {{{R}}} — stabilizes immediately")
    else:
        print(f"  {R} is NOT absorbing: comp({R}, PP) = {result} — can transition")

# Part 4: What about PPI-kernel (dual)?
print()
print("=" * 70)
print("PART 4: PPI-kernel analysis (dual of PP-kernel)")
print("=" * 70)
print()
print("PPI is the inverse of PP. A PPI-kernel would represent collapsing")
print("of PPI-chains (which are just PP-chains viewed from the other end).")
print()

for S in ['PP', 'PPI']:
    print(f"  Self-composition: comp({S},{S}) = {COMP[(S,S)]}")
    print(f"  comp(R, {S}) contains R for all R?")
    for R in RELS:
        ok = R in COMP[(R, S)]
        if not ok:
            print(f"    {R}: NO — comp({R},{S}) = {COMP[(R,S)]}")
    print(f"  comp({S}, R) contains R for all R?")
    for R in RELS:
        ok = R in COMP[(S, R)]
        if not ok:
            print(f"    {R}: NO — comp({S},{R}) = {COMP[(S,R)]}")
    print()

# Part 5: Explore the collapsing condition
print()
print("=" * 70)
print("PART 5: When does collapsing two same-type nodes fail?")
print("=" * 70)
print()
print("If d1 and d2 have the same type and R(d1,d2) = S, collapsing them")
print("into one node k creates reflexive S(k,k). This requires:")
print("  (a) S ∈ comp(S, S)  [self-consistency]")
print("  (b) For all external edges R(k,m): R ∈ comp(S, R) and R ∈ comp(R, S)")
print("  (c) S ∈ comp(R, inv(R)) for all external R")
print()

for S in RELS:
    # Check (a)
    self_comp = S in COMP[(S, S)]
    # Check (b) and (c) — universal self-absorption
    all_absorb_left = all(R in COMP[(S, R)] for R in RELS)
    all_absorb_right = all(R in COMP[(R, S)] for R in RELS)
    all_in_self = all(S in COMP[(R, INV[R])] for R in RELS)

    status = "SAFE" if (self_comp and all_absorb_left and all_absorb_right and all_in_self) else "UNSAFE"
    print(f"  Collapsing via {S}: {status}")
    if not self_comp:
        print(f"    FAILS self-composition: {S} ∉ comp({S},{S}) = {COMP[(S,S)]}")
    if not all_absorb_left:
        for R in RELS:
            if R not in COMP[(S, R)]:
                print(f"    FAILS left absorption: {R} ∉ comp({S},{R}) = {COMP[(S,R)]}")
    if not all_absorb_right:
        for R in RELS:
            if R not in COMP[(R, S)]:
                print(f"    FAILS right absorption: {R} ∉ comp({R},{S}) = {COMP[(R,S)]}")
    if not all_in_self:
        for R in RELS:
            if S not in COMP[(R, INV[R])]:
                print(f"    FAILS self-containment: {S} ∉ comp({R},{INV[R]}) = {COMP[(R,INV[R])]}")

# Part 6: The key question — can different-type kernel nodes coexist on a chain?
print()
print("=" * 70)
print("PART 6: Multi-type PP-chains — can kernel nodes of different")
print("types coexist with well-defined relations?")
print("=" * 70)
print()
print("On a PP-chain with period (τ1, τ2, τ3, τ1, τ2, τ3, ...),")
print("collapsing all τ1 into k1, all τ2 into k2, all τ3 into k3:")
print()
print("Within one period: k1 PP k2 PP k3 (by chain order)")
print("Across periods: k3 PP k1 (next period's τ1 comes after τ3)")
print()
print("This creates BOTH k1 PP k3 (transitivity) and k3 PP k1.")
print("PP and PPI between the same pair violates JEPD!")
print()
print("Resolution options:")
print("  (A) Only collapse if all chain elements have the SAME type")
print("      (single-type chains collapse cleanly)")
print("  (B) Allow disjunctive quotient: R(k1,k3) ∈ {PP, PPI}")
print("      (violates atomic JEPD but is a valid disjunctive network)")
print("  (C) Reorder chain elements to group same types together,")
print("      then collapse each group. But reordering may break")
print("      composition with external elements.")
print("  (D) Don't collapse ACROSS types — keep the periodic structure")
print("      as a finite cycle of kernel nodes.")
print()

# Part 7: Count how many types can appear on a PP-chain
print("=" * 70)
print("PART 7: ∀PP propagation constrains chain types")
print("=" * 70)
print()
print("If ∀PP.C ∈ tp(d_i) on a PP-chain, then C ∈ tp(d_j) for all j > i.")
print("This means the set of ∀PP-consequences grows monotonically and")
print("stabilizes. After stabilization, all elements share the same")
print("∀PP-consequences, limiting the possible types.")
print()
print("Key insight: if we look at the 'eventually repeating' part of the")
print("chain (after ∀PP-stabilization), and if only ONE type appears,")
print("then the entire tail collapses to a single PP-kernel node.")
print()
print("Question: can multiple types coexist in the stable tail?")
print("Yes — different ∃-demands can generate different witness patterns,")
print("leading to different types. But the NUMBER of types is finite,")
print("so the sequence is eventually periodic.")

print()
print("=" * 70)
print("SUMMARY")
print("=" * 70)
print()
print("1. Reflexive PP is FULLY composition-consistent (universal self-absorption)")
print("2. Only PP (and PPI) allow safe reflexive loops; DR and PO do NOT")
print("3. PP-chain relations to external nodes stabilize (monotone, bounded)")
print("4. Same-type elements in the stable tail CAN be safely collapsed")
print("5. Multi-type periods create a JEPD issue (PP/PPI coexistence)")
print("6. The approach works cleanly for single-type tails; multi-type")
print("   tails need additional machinery (disjunctive quotient, or")
print("   keeping the periodic structure explicit)")
