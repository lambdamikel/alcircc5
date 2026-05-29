"""
RCC5 composition table and verification utilities for review3.

Cross-checks the round-8 manuscripts in
  alcircc5/papers/claude_latest_review_gpt5.5_fix/

The table is transcribed verbatim from the round-8 expanded companion,
Section 2.1 (expanded_split_forest_full_details_round8_full.tex, lines 120-133).
Reading convention (as stated there): the entry in row R, column S is the set
Comp(R,S) such that whenever  x R y  and  y S z, the label of (x,z) lies in it.

  PP(x,y)  means x is a proper part of y
  PPI      is the converse of PP
  EQ,DR,PO are self-converse
"""

from itertools import product

EQ, DR, PO, PP, PPI = "EQ", "DR", "PO", "PP", "PPI"
BASE = (EQ, DR, PO, PP, PPI)

INV = {EQ: EQ, DR: DR, PO: PO, PP: PPI, PPI: PP}

# Round-8 composition table, row R, column S  ->  Comp(R,S)
COMP = {
    (EQ, EQ): {EQ}, (EQ, DR): {DR}, (EQ, PO): {PO}, (EQ, PP): {PP}, (EQ, PPI): {PPI},

    (DR, EQ): {DR}, (DR, DR): set(BASE), (DR, PO): {DR, PO, PP},
    (DR, PP): {DR, PO, PP}, (DR, PPI): {DR},

    (PO, EQ): {PO}, (PO, DR): {DR, PO, PPI}, (PO, PO): set(BASE),
    (PO, PP): {PO, PP}, (PO, PPI): {DR, PO, PPI},

    (PP, EQ): {PP}, (PP, DR): {DR}, (PP, PO): {DR, PO, PP},
    (PP, PP): {PP}, (PP, PPI): set(BASE),

    (PPI, EQ): {PPI}, (PPI, DR): {DR, PO, PPI}, (PPI, PO): {PO, PPI},
    (PPI, PP): {EQ, PO, PP, PPI}, (PPI, PPI): {PPI},
}


def compose(R, S):
    return COMP[(R, S)]


def check_inverses():
    bad = []
    for R, S in product(BASE, repeat=2):
        lhs = {INV[X] for X in COMP[(R, S)]}
        rhs = COMP[(INV[S], INV[R])]
        if lhs != rhs:
            bad.append((R, S, lhs, rhs))
    return bad


def sec(title):
    print("\n" + "-" * 72 + "\n" + title + "\n" + "-" * 72)


def main():
    print("=" * 72)
    print("review3: composition checks for the round-8 saturated-side-context proof")
    print("=" * 72)

    bad = check_inverses()
    print(f"Inverse-symmetry violations in transcribed round-8 table: {len(bad)}")
    assert not bad
    triples = [(a, b, c) for a, b in product(BASE, repeat=2) for c in compose(a, b)]
    print(f"RCC5-legal ordered triples: {len(triples)}")

    # ------------------------------------------------------------------ #
    sec("Core fact 1: comp(PPI, PO) = {PO, PPI}  (note: DR is NOT in it)")
    print(f"  comp(PPI, PO) = {sorted(compose(PPI, PO))}")
    print("  Read: if  a PPI u  (i.e. u PP a, u a proper part of a) and  u PO w,")
    print("  then rho(a,w) in {PO, PPI}.  A universal forall PO.X at a, with w in ~X,")
    print("  EXCLUDES PO, FORCING rho(a,w) = PPI, i.e. w PP a.  DR is impossible.")

    sec("Core fact 2: comp(PPI, PPI) = {PPI}  (PP/PPI transitivity up the tower)")
    print(f"  comp(PPI, PPI) = {sorted(compose(PPI, PPI))}")
    print("  Read: once w PP a_1 and a_1 PP a_2, then rho(a_2,w) in comp(PPI,PPI)={PPI}.")
    print("  So w PP a_m is FORCED for EVERY tower node a_m, m >= 1.")

    sec("Core fact 3: comp(PP, PP) = {PP}  (the side witness is a part of the whole tower)")
    print(f"  comp(PP, PP) = {sorted(compose(PP, PP))}")

    # ------------------------------------------------------------------ #
    sec("Forced-label propagation in the witness configuration C0'")
    print("Configuration (all relations FORCED, none chosen):")
    print("   u            : source, has  exists PO.(~X)  ->  side witness w")
    print("   w            : the PO-witness of u,  w in ~X")
    print("   a_1,a_2,...  : infinite ascending PP-tower, each a_m in (forall PO.X)")
    print("   u PP a_1 PP a_2 PP ...   (u is a proper part of every tower node)")
    print()
    # rho(u,w) = PO ; rho(a_m, u) = PPI for all m (u proper part of a_m)
    # Propagate the forced label rho(a_m, w):
    rho_a_u = PPI          # a_1 PPI u  since u PP a_1
    rho_u_w = PO           # u PO w
    cand = compose(rho_a_u, rho_u_w)
    print(f"  Step m=1: rho(a_1,w) in comp(PPI,PO) = {sorted(cand)}")
    forced = {r for r in cand if r != PO}   # forall PO.X at a_1 + w in ~X kills PO
    print(f"            forall PO.X at a_1 + w in ~X  removes PO  ->  rho(a_1,w) = {sorted(forced)}")
    assert forced == {PPI}, forced
    label = PPI
    for m in range(2, 7):
        cand = compose(PPI, label)   # rho(a_m, a_{m-1}) = PPI, then to w
        assert cand == {PPI}, cand
        label = PPI
        print(f"  Step m={m}: rho(a_{m},w) in comp(PPI, PPI) = {{PPI}}  ->  w PP a_{m}")
    print()
    print("  CONCLUSION: w PP a_m is forced for ALL m >= 1.  The side witness w is a")
    print("  proper part of every node of the infinite tower.")

    # ------------------------------------------------------------------ #
    sec("Why the round-8 pair-shape catalogue cannot label the deep pairs")
    print("A saturated side context S_k(u) has <= m_*(C0) positions (Lemma 'side-width'),")
    print("so it contains only FINITELY many tower nodes a_1..a_K.  For m > K the pair")
    print("(a_m, w) must still carry the FORCED label PPI, yet:")
    print()
    print("  * tag 'side_PPI' (Def. incidence-tags) needs a_m and w in ONE finite side")
    print("    context  -> unavailable for m > K (a_m not in S_k(u)).")
    print("  * tag 'down'    needs a_m Reach_PPI w, i.e. an E_up path w -> ... -> a_m")
    print("    (Def. eq-aware-vertical).  The DR/PO side-witness w is attached to u's")
    print("    side context; the construction adds NO E_up edge from w into the tree,")
    print("    so Reach_PP(w, a_m) fails.")
    print("  * tag 'front_R' (residual frontier) is restricted to R in {DR,PO}")
    print("    (mosaic axiom M7 / clause V13 / Lemma residual-frontier).")
    print()
    print("So the only catalogue shapes that COULD apply to (a_m, w), m>K, are DR/PO")
    print("residual-frontier shapes.  Check those against the constraints:")
    print(f"  - DR : excluded by composition, since comp(PPI,PO) = {sorted(compose(PPI,PO))}"
          " has no DR.")
    print( "  - PO : composition-legal, BUT then a_m sees w as a PO-successor, and")
    print( "         clause V12 (DR/PO universal safety) + forall PO.X at a_m force")
    print( "         X in tp(w).  Since w in ~X, V12 FAILS.")
    print()
    print("  => No catalogue pair shape can carry the forced PPI label for m>K.")
    print("     The certificate produced by the stated construction (Lemma split-cover,")
    print("     which attaches w as a saturated side context of u) is INVALID.")
    print("     Hence the completeness construction does not go through for C0'.")


if __name__ == "__main__":
    main()
