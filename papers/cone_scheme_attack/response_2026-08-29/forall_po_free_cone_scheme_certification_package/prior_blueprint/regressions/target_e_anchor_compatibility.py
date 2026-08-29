#!/usr/bin/env python3
"""Target E: a finite dkey does not imply anchor-compatible borrowing.

This is a counterexample to the *current selection policy*:

    a blocked node borrows the chosen witness of its same-dkey gate mate.

It is not an impossibility result for every bounded repair.  In particular, an
existing-witness-first policy can avoid this tiny example, but would need a new
global boundedness proof.

The source is a finite ordered-disjoint model with two symmetric components.
For i in {0,1},

    p_i0 PP p_i1 PP p_i2 PP v_i,       p_i2 PP u_i,

where v_i PO u_i and all cross-component pairs are DR.  X labels v_0,v_1 and
Y labels u_0,u_1.  Put

    T  = exists PP.Z and exists PP.(X and exists DR.Y) and exists PP.Y
    C0 = T and exists DR.T.

The first two p-points in both components satisfy C0 and have the same full
model type; `exists PP.Z` is served along their p-chain.  The component swap is an
automorphism, so dkey(v_0)=dkey(v_1).  The unique DR-Y witness of v_0 is u_1,
and the unique DR-Y witness of v_1 is u_0.

The two p-chains can therefore be selected as equal-type PP recurrence
segments, whose postselected PP anchors include v_i and u_i.  If v_0 is the
gate representative, blocked v_1 borrows u_1 and the external construction
declares v_1 DR u_1.  This external declaration is locally compatible with an
ordered-disjoint external frame, but it cannot coexist with a kernel point
p_1 below both v_1 and u_1.  Equivalently,

    DR not in comp(PPI, PP).

Choosing v_1 as representative fails symmetrically in component 0.
"""

from itertools import combinations


DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
ATOMS = (DR, PO, EQ, PP, PPI)
CONV = {DR: DR, PO: PO, EQ: EQ, PP: PPI, PPI: PP}


def rel_sets(a, b):
    if a == b:
        return EQ
    if a < b:
        return PP
    if b < a:
        return PPI
    return DR if not (a & b) else PO


def composition_table(universe_size=4):
    """Derive the standard RCC5 table from nonempty finite regions."""
    regions = [
        frozenset(c)
        for size in range(1, universe_size + 1)
        for c in combinations(range(universe_size), size)
    ]
    table = {}
    for a in regions:
        for b in regions:
            first = rel_sets(a, b)
            for c in regions:
                table.setdefault((first, rel_sets(b, c)), set()).add(rel_sets(a, c))
    return table


CT = composition_table()


PTS = (
    "p00", "p01", "p02", "v0", "u0",
    "p10", "p11", "p12", "v1", "u1",
)
COMPONENT = {point: int(point[1]) for point in PTS}

LT = set()
for i in (0, 1):
    p0, p1, p2, v, u = f"p{i}0", f"p{i}1", f"p{i}2", f"v{i}", f"u{i}"
    chain = (p0, p1, p2)
    for left_index, left in enumerate(chain):
        for right in chain[left_index + 1:]:
            LT.add((left, right))
        LT.update({(left, v), (left, u)})

DISJ = {
    (x, y)
    for x in PTS
    for y in PTS
    if x != y and COMPONENT[x] != COMPONENT[y]
}


def relation(x, y):
    if x == y:
        return EQ
    if (x, y) in LT:
        return PP
    if (y, x) in LT:
        return PPI
    if (x, y) in DISJ:
        return DR
    return PO


X = ("atom", "X")
Y = ("atom", "Y")
Z = ("atom", "Z")


def conj(left, right):
    return ("and", left, right)


def exists(role, body):
    return ("exists", role, body)


T = conj(
    exists(PP, Z),
    conj(exists(PP, conj(X, exists(DR, Y))), exists(PP, Y)),
)
C0 = conj(T, exists(DR, T))

VALUATION = {point: set() for point in PTS}
for i in (0, 1):
    VALUATION[f"v{i}"].add("X")
    VALUATION[f"u{i}"].add("Y")
    for j in (0, 1, 2):
        VALUATION[f"p{i}{j}"].add("Z")


def satisfies(point, concept):
    kind = concept[0]
    if kind == "atom":
        return concept[1] in VALUATION[point]
    if kind == "and":
        return satisfies(point, concept[1]) and satisfies(point, concept[2])
    if kind == "exists":
        return any(
            relation(point, target) == concept[1] and satisfies(target, concept[2])
            for target in PTS
        )
    raise ValueError(f"unknown concept constructor: {kind}")


def closure(concept, result=None):
    result = [] if result is None else result
    if concept not in result:
        result.append(concept)
    if concept[0] == "and":
        closure(concept[1], result)
        closure(concept[2], result)
    elif concept[0] == "exists":
        closure(concept[2], result)
    return result


CL = closure(C0)


def model_type(point):
    return tuple(concept for concept in CL if satisfies(point, concept))


def down_spectrum(point):
    return frozenset(model_type(lower) for lower in PTS if relation(lower, point) == PP)


def dkey(point):
    return model_type(point), down_spectrum(point)


def check_source_ordered_disjoint():
    assert all((point, point) not in LT for point in PTS)
    assert all(
        (x, z) in LT
        for x, y in LT
        for y2, z in LT
        if y == y2
    )
    assert all((y, x) in DISJ for x, y in DISJ)
    assert all((point, point) not in DISJ for point in PTS)
    assert all((x, y) not in DISJ for x, y in LT)
    assert all(
        (x1, y1) in DISJ
        for x, y in DISJ
        for x1 in PTS
        for y1 in PTS
        if (x1 == x or (x1, x) in LT) and (y1 == y or (y1, y) in LT)
    )

    # Directly check that the induced atomic network obeys converse and every
    # RCC5 composition constraint used by the certificate.
    for x in PTS:
        for y in PTS:
            assert relation(y, x) == CONV[relation(x, y)]
            for z in PTS:
                assert relation(x, z) in CT[(relation(x, y), relation(y, z))]


def external_frame_with_borrowed_dr(blocked, witness):
    """The anchor-only external frame after overriding one PO pair by DR."""
    externals = ("v0", "u0", "v1", "u1")
    disj = {
        (x, y)
        for x in externals
        for y in externals
        if x != y and relation(x, y) == DR
    }
    disj.update({(blocked, witness), (witness, blocked)})
    assert all((x, x) not in disj for x in externals)
    assert all((y, x) in disj for x, y in disj)
    # There are no order edges among these four anchors, so downward closure
    # and lt-not-disjoint are vacuous.  The local external frame is valid.
    return disj


def main():
    check_source_ordered_disjoint()

    phases = ("p00", "p01", "p10", "p11")
    assert all(satisfies(point, C0) for point in phases)
    assert relation("p00", "p01") == PP
    assert relation("p10", "p11") == PP
    assert model_type("p00") == model_type("p01")
    assert model_type("p10") == model_type("p11")

    assert dkey("v0") == dkey("v1")

    witnesses = {}
    demand = exists(DR, Y)
    for v in ("v0", "v1"):
        witnesses[v] = [
            target
            for target in PTS
            if relation(v, target) == DR and satisfies(target, Y)
        ]
    assert witnesses == {"v0": ["u1"], "v1": ["u0"]}

    # Gate representative v0: blocked v1 borrows u1.
    external_frame_with_borrowed_dr("v1", "u1")
    assert relation("v1", "u1") == PO
    assert relation("p11", "v1") == PP
    assert relation("p11", "u1") == PP
    assert DR not in CT[(PPI, PP)]

    # Gate representative v1: the symmetric failure occurs at kernel 0.
    external_frame_with_borrowed_dr("v0", "u0")
    assert relation("v0", "u0") == PO
    assert relation("p01", "v0") == PP
    assert relation("p01", "u0") == PP

    print("PASS: source is an RCC5 composition-closed ordered-disjoint model")
    print("PASS: C0 is forall-PO-free and holds at all four selected phase points")
    print("PASS: each component has an equal-type PP recurrence segment with a")
    print("      same-type-chain demand exists PP.Z")
    print("PASS: dkey(v0) = dkey(v1)")
    print("PASS: unique DR-Y witnesses are crossed: v0->u1, v1->u0")
    print("PASS: either gate order declares DR between two anchors above one kernel")
    print("VERDICT: finite dkey closure terminates, but current borrowing is not")
    print("         anchor-compatible and need not extend to a valid kernel frame")


if __name__ == "__main__":
    main()
