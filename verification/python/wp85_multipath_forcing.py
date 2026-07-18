#!/usr/bin/env python3
"""
wp85_multipath_forcing.py  (2026-07-18)

Backs the overview paper's Remark on single-step vs. joint forcing, and the
sharp (dichotomy) form of the coincidence obstruction. Prompted by the 16th
review, which correctly found that "PO is never forced" was overstated.

Self-contained: derives the RCC5 composition table from finite set semantics
(the same derivation every wp probe uses), then establishes:

  A. Proposition 1 (single-cell): NO single length-two composition of proper
     relations returns the singleton {PO}; the only singleton cells are the
     four vertical ones ({DR,PP,PPI}).  [reviewer confirmed this is correct]

  B. Joint forcing: the INTERSECTION of two proper-relation cells CAN narrow
     to a singleton for EVERY proper relation {DR, PO, PP, PPI} -- including
     PO.  So "PO is never forced" is false; PO is not special among the
     proper relations under multi-path forcing.  (This is the p.16 fact:
     comp(DR,PO) ∩ comp(PPI,PO) = {PO}.)

  C. THE FOUNDATION (coincidence obstruction, half 1): EQ can NEVER be forced
     between distinct occurrences by ANY intersection of proper-relation
     composition constraints.  Composition alone never compels a merge --
     which is why a grid is never forced "for free" by the relational
     structure.  (Half 2 -- that concept-level isolation CAN force a merge but
     only self-defeatingly, collapsing to UNSAT at level 2 -- is the domino
     analysis in the paper, not a pure-algebra fact, so it is not checked
     here.)

Exit 0 and prints ALL PASS iff A, B, C all hold.
"""
from itertools import combinations

ATOMS = ["EQ", "PP", "PPI", "PO", "DR"]
PROPER = ["PP", "PPI", "PO", "DR"]


def rel(X, Y):
    X, Y = frozenset(X), frozenset(Y)
    if X == Y:
        return "EQ"
    if not (X & Y):
        return "DR"
    if X < Y:
        return "PP"
    if Y < X:
        return "PPI"
    return "PO"


def derive_comp(n=6):
    U = range(n)
    regs = [frozenset(s) for k in range(1, n + 1) for s in combinations(U, k)]
    comp = {(a, b): set() for a in ATOMS for b in ATOMS}
    for X in regs:
        for Y in regs:
            for Z in regs:
                comp[(rel(X, Y), rel(Y, Z))].add(rel(X, Z))
    return comp


COMP = derive_comp()


def part_a():
    singles = {(r, s): next(iter(COMP[(r, s)]))
               for r in PROPER for s in PROPER if len(COMP[(r, s)]) == 1}
    vals = sorted(set(singles.values()))
    assert "PO" not in vals, "PO appears as a single-cell value (Prop 1 false!)"
    assert "EQ" not in vals, "EQ appears as a single-cell value!"
    assert vals == ["DR", "PP", "PPI"], f"unexpected single-cell values {vals}"
    print(f"A. single-cell singletons: {len(singles)} cells, values {vals} "
          f"(PO and EQ never single-cell) -- PASS")


def part_b():
    forceable = {}
    for r1 in PROPER:
        for s1 in PROPER:
            for r2 in PROPER:
                for s2 in PROPER:
                    inter = COMP[(r1, s1)] & COMP[(r2, s2)]
                    if len(inter) == 1:
                        v = next(iter(inter))
                        forceable.setdefault(v, ((r1, s1), (r2, s2)))
    got = sorted(forceable)
    assert got == ["DR", "PO", "PP", "PPI"], f"two-path forceable = {got}"
    (a, b) = forceable["PO"]
    assert COMP[a] & COMP[b] == {"PO"}
    print(f"B. two-path forceable singletons: {got} (ALL four proper relations, "
          f"incl. PO)")
    print(f"   witness PO: comp{a} ∩ comp{b} = {{PO}} -- PASS")


def part_c():
    # any intersection of up to 4 proper-relation cells: can it be {EQ}?
    cells = [COMP[(r, s)] for r in PROPER for s in PROPER]
    from itertools import combinations as C
    for k in range(1, 5):
        for combo in C(range(len(cells)), k):
            inter = set(ATOMS)
            for i in combo:
                inter &= cells[i]
            assert inter != {"EQ"}, f"EQ forced by {k} proper cells -- FOUNDATION BROKEN"
    eq_cells = [(r, s) for r in PROPER for s in PROPER if "EQ" in COMP[(r, s)]]
    sizes = {(r, s): len(COMP[(r, s)]) for (r, s) in eq_cells}
    assert all(v >= 4 for v in sizes.values())
    print("C. EQ is never forced by any intersection of proper-relation cells "
          "(checked to 4 simultaneous)")
    print(f"   proper cells containing EQ: {eq_cells} -- all size >= 4 -- PASS")


if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    print()
    print("ALL PASS -- single-step forcing is only vertical (PO never single-cell),")
    print("but joint forcing reaches every proper relation incl. PO; EQ is never")
    print("forced by composition (the coincidence obstruction, algebra half).")
