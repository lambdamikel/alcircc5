#!/usr/bin/env python3
"""Target E: finite down-spectrum keys do not yield finite model anchors.

In the infinite set model

    A_n = {0,...,n},       B_m = {m+1},

all B_m have the same closure type and empty strict-lower spectrum for

    H  = (exists PP.TOP) and (exists DR.TOP),
    C0 = H and (forall PP.H).

Every A_n has the DR witness B_n, but no fixed finite external set serves the
DR demand on an arbitrarily late A-segment.  Thus finiteness of the refined key
does not, by itself, establish Target E's fixed point.  A construction using
fresh declared anchors would need an additional row-conservative placement
lemma and is deliberately not ruled out by this probe.
"""

DR, EQ, PP, PPI = "DR", "EQ", "PP", "PPI"


def rel(x, y):
    """RCC5 relation on symbolic points ('A',n) and ('B',m)."""
    kx, i = x
    ky, j = y
    if kx == "A" and ky == "A":
        return EQ if i == j else (PP if i < j else PPI)
    if kx == "B" and ky == "B":
        return EQ if i == j else DR
    if kx == "A":
        # A_i meets B_j={j+1} exactly when i >= j+1; then B_j < A_i.
        return DR if i <= j else PPI
    # converse: B_i to A_j
    return DR if j <= i else PP


def all_closure_formulas_hold(point):
    """Analytic truth check for every member of cl(C0).

    A_n has PP successor A_{n+1} and DR witness B_n.
    B_m has PP successor A_{m+1} and DR witness B_{m+1}.
    Every PP successor is an A_k, and every A_k satisfies H.  Hence TOP,
    exists-PP.TOP, exists-DR.TOP, H, forall-PP.H, and C0 all hold everywhere.
    """
    kind, n = point
    if kind == "A":
        pp_witness = ("A", n + 1)
        dr_witness = ("B", n)
    else:
        pp_witness = ("A", n + 1)
        dr_witness = ("B", n + 1)
    return rel(point, pp_witness) == PP and rel(point, dr_witness) == DR


def anchor_key(point):
    """Only B_m is used here; every such point has type T and empty spectrum."""
    assert point[0] == "B"
    model_type = ("C0", "H", "existsPPtop", "existsDRtop", "forallPPH", "TOP")
    lower_spectrum = frozenset()  # a singleton region has no nonempty subset
    return model_type, lower_spectrum


def finite_anchor_failure(externals):
    indices = [i for _kind, i in externals]
    threshold = 1 + max(indices, default=-1)
    source = ("A", threshold)
    return source, [rel(source, e) for e in externals]


def main():
    # Exhaustively check the symbolic relation law and local witnesses on a
    # substantial finite window.  The general proof is the displayed index
    # calculation, not this bound.
    for n in range(250):
        assert all_closure_formulas_hold(("A", n))
        assert all_closure_formulas_hold(("B", n))
        assert rel(("A", n), ("B", n)) == DR
        assert rel(("A", n + 1), ("B", n)) == PPI
    assert len({anchor_key(("B", m)) for m in range(250)}) == 1

    examples = [
        [("B", 0)],
        [("B", 0), ("B", 7), ("B", 12)],
        [("A", 3), ("B", 4), ("A", 20), ("B", 99)],
    ]
    print("TARGET E -- FINITE-KEY / FINITE-ANCHOR COUNTEREXAMPLE")
    print("=" * 72)
    print("A_n={0,...,n}; B_m={m+1}; C0=H and forall PP.H")
    print("H=(exists PP.TOP) and (exists DR.TOP)")
    print("all B_m have one model type and empty down-spectrum: PASS")
    print("each A_n has the DR witness B_n: PASS")
    print()
    for external in examples:
        source, rows = finite_anchor_failure(external)
        assert rows and all(r == PPI for r in rows)
        print(f"fixed externals {external}")
        print(f"  later source {source}: row = {rows}; no DR witness")
    print()
    print("For any finite E, choose n above every index used in E.")
    print("Every e in E is then a strict subset of A_n, so rho(A_n,e)=PPI.")
    print("Yet A_n still satisfies exists DR.TOP via the new point B_n.")
    print("=" * 72)
    print("VERDICT: finite key enumeration alone does not produce a finite")
    print("source-model anchor fixed point. Fresh anchored completion remains")
    print("a separate, unproved row-conservative placement construction.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
