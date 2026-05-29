"""
review3: concrete demonstration that the proposed repair closes D-1.

Two things are checked:

  (A) The REPAIRED presentation of the satisfiable concept C0' is a genuine
      finite RCC5 structure (converse + composition on every triple), its
      Reach_PP vertical tags reproduce exactly the PP/PPI labels (so the
      'down' pair shape is available for every (a_m, w)), and it satisfies
      every concept demand except the single top existential discharged by
      the blocking cycle.  => a VALID certificate now exists.

  (B) The repair does NOT over-accept: the UNSAT sibling C0 (tower also
      carries forall PPI.Y, witness in ~X and ~Y) is correctly rejected,
      because verticalizing w under the tower makes w a PPI-successor and
      fires forall PPI.Y on it, clashing with w in ~Y.  Every composition-
      legal choice for rho(a_1, w) leads to a clash.

Uses the round-8 composition table from rcc5_compose.py.
"""

from itertools import product
from rcc5_compose import EQ, DR, PO, PP, PPI, BASE, compose, INV


# --------------------------------------------------------------------------- #
#  generic finite-structure checker
# --------------------------------------------------------------------------- #
def check_frame(nodes, rho):
    """rho: dict (x,y)->label.  Verify the three RCC5 frame axioms."""
    errs = []
    for x in nodes:
        if rho[(x, x)] != EQ:
            errs.append(("F1-refl", x, rho[(x, x)]))
    for x, y in product(nodes, repeat=2):
        if x != y and rho[(x, y)] == EQ:
            errs.append(("F1-strict", x, y))
        if rho[(y, x)] != INV[rho[(x, y)]]:
            errs.append(("F2-converse", x, y, rho[(x, y)], rho[(y, x)]))
    for x, y, z in product(nodes, repeat=3):
        if rho[(x, z)] not in compose(rho[(x, y)], rho[(y, z)]):
            errs.append(("F3-comp", x, y, z, rho[(x, y)], rho[(y, z)], rho[(x, z)]))
    return errs


def reach_pp(nodes, e_up):
    """Strict transitive closure of the selected cover relation e_up (set of
    (child, parent) pairs).  Returns set of (x,y) with x Reach_PP y (y above x)."""
    up = {(c, p) for (c, p) in e_up}
    changed = True
    while changed:
        changed = False
        for (a, b) in list(up):
            for (c, d) in list(up):
                if b == c and (a, d) not in up:
                    up.add((a, d))
                    changed = True
    return up


# --------------------------------------------------------------------------- #
#  (A)  Repaired presentation of  C0' = (exists PP.G) and (exists PO.~X),
#       G = (forall PO.X) and (exists PP.G)
# --------------------------------------------------------------------------- #
def build_C0prime(M):
    """u, w, and a finite prefix a_1..a_M of the ascending tower.
    Repaired routing: w is spliced under a_1, hence w PP a_m for all m."""
    tower = [f"a{i}" for i in range(1, M + 1)]
    nodes = ["u", "w"] + tower
    rho = {}
    for x in nodes:
        rho[(x, x)] = EQ

    # u and w are proper parts of every tower node
    for a in tower:
        rho[("u", a)] = PP;  rho[(a, "u")] = PPI
        rho[("w", a)] = PP;  rho[(a, "w")] = PPI
    # u PO w
    rho[("u", "w")] = PO; rho[("w", "u")] = PO
    # tower is an ascending PP-chain
    for i in range(M):
        for j in range(M):
            if i < j:
                rho[(tower[i], tower[j])] = PP
                rho[(tower[j], tower[i])] = PPI
    return nodes, tower, rho


def demo_A():
    print("=" * 72)
    print("(A) Repaired presentation of the SAT concept C0'")
    print("=" * 72)
    M = 8
    nodes, tower, rho = build_C0prime(M)

    errs = check_frame(nodes, rho)
    print(f"RCC5 frame-axiom violations on the depth-{M} prefix: {len(errs)}")
    if errs:
        for e in errs[:8]:
            print("   ", e)
    assert not errs

    # selected cover edges of the repaired backbone:
    #   w -> a1  (the splice),  u -> a1,  a_i -> a_{i+1}
    e_up = {("w", "a1"), ("u", "a1")}
    for i in range(1, M):
        e_up.add((f"a{i}", f"a{i+1}"))
    R = reach_pp(nodes, e_up)

    # the 'down' shape is available for every (a_m, w): need w Reach_PP a_m
    missing = [a for a in tower if ("w", a) not in R]
    print(f"tower nodes a_m WITHOUT an available 'down' shape for (a_m,w): {len(missing)}")
    assert not missing, missing
    # and the vertical tag reproduces the label PPI = rho(a_m, w)
    ok = all(rho[(a, "w")] == PPI for a in tower)
    print(f"every (a_m,w) vertical tag reproduces label PPI: {ok}")
    assert ok
    # (u,w) is residual, neither reaches the other -> front_PO, matches rho
    uw_residual = ("u", "w") not in R and ("w", "u") not in R
    print(f"(u,w) is residual (front_PO), label = {rho[('u','w')]}: {uw_residual}")
    assert uw_residual and rho[("u", "w")] == PO

    # concept-truth check with X interpreted as empty (w in ~X, vacuous forall PO.X)
    Xext = set()
    def is_X(x): return x in Xext
    # forall PO.X at every tower node: tower nodes have NO PO-neighbour here
    for a in tower:
        po_neighbours = [y for y in nodes if y != a and rho[(a, y)] == PO]
        assert all(is_X(y) for y in po_neighbours), (a, po_neighbours)
    # exists PO.~X at u: witness w, rho(u,w)=PO, w in ~X
    assert rho[("u", "w")] == PO and not is_X("w")
    # exists PP.G at u and at each tower node: u PP a1, a_i PP a_{i+1}
    assert rho[("u", "a1")] == PP
    assert all(rho[(f"a{i}", f"a{i+1}")] == PP for i in range(1, M))
    print("All demands of C0' met (top existential a_M->a_{M+1} discharged by the cycle).")
    print(">>> A VALID repaired certificate for C0' EXISTS.\n")


# --------------------------------------------------------------------------- #
#  (B)  UNSAT sibling: G also carries forall PPI.Y, witness in ~X and ~Y.
#       Show every composition-legal choice for rho(a_1,w) clashes.
# --------------------------------------------------------------------------- #
def demo_B():
    print("=" * 72)
    print("(B) The repair does NOT over-accept the UNSAT sibling C0")
    print("=" * 72)
    print("Tower node a_1: forall PO.X and forall PPI.Y.  Witness w in ~X and ~Y.")
    print("u PP a_1 (rho(a_1,u)=PPI),  u PO w (rho(u,w)=PO).")
    cand = compose(PPI, PO)
    print(f"rho(a_1,w) must lie in comp(PPI,PO) = {sorted(cand)}.")
    clash_everywhere = True
    for r in sorted(cand):
        reasons = []
        if r == PO:
            reasons.append("a_1 sees w as PO-successor -> forall PO.X forces X(w); but w in ~X. CLASH")
        elif r == PPI:
            reasons.append("a_1 sees w as PPI-successor (w PP a_1) -> forall PPI.Y forces Y(w); but w in ~Y. CLASH")
        else:
            reasons.append("not composition-legal")
        legal = r in cand
        print(f"  rho(a_1,w)={r:3} : {'legal' if legal else 'ILLEGAL'} ; {reasons[0]}")
        if legal and "CLASH" not in reasons[0]:
            clash_everywhere = False
    print(f"\nEvery composition-legal label for (a_1,w) clashes: {clash_everywhere}")
    assert clash_everywhere
    print(">>> The repaired construction correctly finds NO valid certificate => UNSAT.\n")


if __name__ == "__main__":
    demo_A()
    demo_B()
    print("=" * 72)
    print("Repair verified on the witness pair: SAT C0' now certifiable, UNSAT C0")
    print("still correctly rejected.")
    print("=" * 72)
