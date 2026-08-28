#!/usr/bin/env python3
"""Executable Target-A counterexample to the shared class-top repair.

The artifact is deliberately self-contained and uses only the Python standard
library.  It does five things:

1. derives the RCC5 composition table from nonempty finite-set regions;
2. builds the eight-point ordered-disjoint frame from the report;
3. checks the ordered-disjoint axioms and RCC5 network closure;
4. evaluates the 22 subformulas of C0 and checks that v1 and v2 have the same
   full closure type and the advertised unique demand witnesses; and
5. mechanically checks the finite proof skeleton showing that no fresh D-top
   can be shared by v1 and v2 while preserving their fixed lower valuations.

The last check is not merely a search of the displayed eight-point model.  It
uses the singleton RCC5 cells PP;PP={PP} and DR;PPI={DR}; consequently it also
rules out a common D-top in an arbitrary composition-closed extension of the
frame (with arbitrarily many fresh supporting nodes).
"""

from itertools import combinations


# ------------------------------------------------------------------ RCC5 table

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
ATOMS = (DR, PO, EQ, PP, PPI)
CONVERSE = {DR: DR, PO: PO, EQ: EQ, PP: PPI, PPI: PP}


def set_relation(left, right):
    """RCC5 base relation between two nonempty finite-set regions."""
    if left == right:
        return EQ
    if left < right:
        return PP
    if right < left:
        return PPI
    if left.isdisjoint(right):
        return DR
    return PO


def nonempty_subsets(size):
    universe = range(size)
    return [
        frozenset(choice)
        for width in range(1, size + 1)
        for choice in combinations(universe, width)
    ]


def derive_composition_table(size):
    """Collect every r;s outcome realized by finite-set triples."""
    regions = nonempty_subsets(size)
    table = {}
    for left in regions:
        for middle in regions:
            first = set_relation(left, middle)
            for right in regions:
                second = set_relation(middle, right)
                outcome = set_relation(left, right)
                table.setdefault((first, second), set()).add(outcome)
    return table


# Four set-points suffice for all standard RCC5 composition outcomes.  The
# independent five-point derivation guards against stopping before saturation.
CT = derive_composition_table(4)
CT_FIVE = derive_composition_table(5)
assert CT == CT_FIVE
assert len(CT) == 25
assert sum(len(outcomes) for outcomes in CT.values()) == 54


def forced(first, second):
    """Return the uniquely forced composition result."""
    outcomes = CT[(first, second)]
    assert len(outcomes) == 1, (first, second, outcomes)
    return next(iter(outcomes))


# ------------------------------------------------------ formula representation

TOP = ("top",)
BOTTOM = ("bottom",)


def Atom(name):
    return ("atom", name)


def NotAtom(name):
    return ("not_atom", name)


def And(left, right):
    return ("and", left, right)


def Or(left, right):
    return ("or", left, right)


def Exists(role, body):
    return ("exists", role, body)


def Forall(role, body):
    return ("forall", role, body)


def conjunction(parts):
    assert parts
    result = parts[0]
    for part in parts[1:]:
        result = And(result, part)
    return result


def subformulas(concept):
    kind = concept[0]
    result = {concept}
    if kind in {"and", "or"}:
        result |= subformulas(concept[1])
        result |= subformulas(concept[2])
    elif kind in {"exists", "forall"}:
        result |= subformulas(concept[2])
    return result


def show(concept):
    kind = concept[0]
    if kind == "top":
        return "TOP"
    if kind == "bottom":
        return "BOTTOM"
    if kind == "atom":
        return concept[1]
    if kind == "not_atom":
        return "not " + concept[1]
    if kind == "and":
        return f"({show(concept[1])} and {show(concept[2])})"
    if kind == "or":
        return f"({show(concept[1])} or {show(concept[2])})"
    if kind == "exists":
        return f"exists {concept[1]}.{show(concept[2])}"
    if kind == "forall":
        return f"forall {concept[1]}.{show(concept[2])}"
    raise ValueError(concept)


P, Q, R_ATOM, S = map(Atom, ("P", "Q", "R", "S"))
NOT_P, NOT_Q = NotAtom("P"), NotAtom("Q")

U_P = Forall(DR, P)
U_Q = Forall(DR, Q)
A = Or(U_P, U_Q)
D = Exists(DR, A)

DEMAND_PP_D = Exists(PP, D)
DEMAND_PO_R = Exists(PO, R_ATOM)
DEMAND_PO_S = Exists(PO, S)
DEMAND_PPI_TOP = Exists(PPI, TOP)
DEMANDS = (DEMAND_PP_D, DEMAND_PO_R, DEMAND_PO_S, DEMAND_PPI_TOP)

C0 = conjunction(
    [
        DEMAND_PP_D,
        DEMAND_PO_R,
        DEMAND_PO_S,
        DEMAND_PPI_TOP,
        Or(P, NOT_P),
        Or(Q, NOT_Q),
    ]
)
CLOSURE = subformulas(C0)

# This exact count is useful: the equality below is equality on the full input
# subformula closure, not just on the four top-level modal demands.
assert len(CLOSURE) == 22
assert DEMAND_PP_D in CLOSURE and DEMAND_PO_R in CLOSURE
assert not any(c[0] == "forall" and c[1] == PO for c in CLOSURE)


# ----------------------------------------------------- ordered-disjoint frame

NODES = ("x1", "v1", "y1", "z1", "x2", "v2", "y2", "z2")

# Two three-point chains x_i < v_i < y_i, written transitively.
LT = {
    ("x1", "v1"),
    ("v1", "y1"),
    ("x1", "y1"),
    ("x2", "v2"),
    ("v2", "y2"),
    ("x2", "y2"),
}

# z_i is disjoint from exactly its own chain.  Every other incomparable pair
# is therefore PO under the ordered-disjoint normal form.
DISJ = set()
for z, chain in (
    ("z1", ("x1", "v1", "y1")),
    ("z2", ("x2", "v2", "y2")),
):
    for point in chain:
        DISJ.add((z, point))
        DISJ.add((point, z))


def le(left, right):
    return left == right or (left, right) in LT


def od_relation(left, right):
    if left == right:
        return EQ
    if (left, right) in LT:
        return PP
    if (right, left) in LT:
        return PPI
    if (left, right) in DISJ:
        return DR
    return PO


def check_ordered_disjoint_axioms():
    errors = []

    # Strict order: irreflexivity and transitivity.
    for x in NODES:
        if (x, x) in LT:
            errors.append(("lt_irreflexive", x))
    for x in NODES:
        for y in NODES:
            for z in NODES:
                if (x, y) in LT and (y, z) in LT and (x, z) not in LT:
                    errors.append(("lt_transitive", x, y, z))

    # disj is irreflexive, symmetric, incomparable, and downward closed.
    for x in NODES:
        if (x, x) in DISJ:
            errors.append(("disj_irreflexive", x))
        for y in NODES:
            if ((x, y) in DISJ) != ((y, x) in DISJ):
                errors.append(("disj_symmetric", x, y))
            if (x, y) in DISJ and ((x, y) in LT or (y, x) in LT):
                errors.append(("disj_comparable", x, y))

    for upper_x in NODES:
        for upper_y in NODES:
            if (upper_x, upper_y) not in DISJ:
                continue
            for lower_x in NODES:
                for lower_y in NODES:
                    if (
                        le(lower_x, upper_x)
                        and le(lower_y, upper_y)
                        and (lower_x, lower_y) not in DISJ
                    ):
                        errors.append(
                            (
                                "disj_downward_closed",
                                lower_x,
                                upper_x,
                                lower_y,
                                upper_y,
                            )
                        )
    return errors


def check_rcc5_network():
    errors = []
    for x in NODES:
        for y in NODES:
            actual = od_relation(x, y)
            if od_relation(y, x) != CONVERSE[actual]:
                errors.append(("converse", x, y))
            if x == y and actual != EQ:
                errors.append(("diagonal", x, actual))
            if x != y and actual == EQ:
                errors.append(("strong_EQ", x, y))
            for z in NODES:
                first = actual
                second = od_relation(y, z)
                outcome = od_relation(x, z)
                if outcome not in CT[(first, second)]:
                    errors.append(
                        ("composition", x, y, z, first, second, outcome)
                    )
    return errors


# ------------------------------------------------------------ model valuation

VALUATION = {
    "x1": {"P"},
    "v1": {"P", "Q", "R"},
    "y1": {"P", "Q"},
    "z1": {"S"},
    "x2": {"Q", "S"},
    "v2": {"P", "Q", "R"},
    "y2": {"P", "Q"},
    "z2": set(),
}


def holds(node, concept):
    kind = concept[0]
    if kind == "top":
        return True
    if kind == "bottom":
        return False
    if kind == "atom":
        return concept[1] in VALUATION[node]
    if kind == "not_atom":
        return concept[1] not in VALUATION[node]
    if kind == "and":
        return holds(node, concept[1]) and holds(node, concept[2])
    if kind == "or":
        return holds(node, concept[1]) or holds(node, concept[2])
    if kind == "exists":
        role, body = concept[1], concept[2]
        return any(
            od_relation(node, target) == role and holds(target, body)
            for target in NODES
        )
    if kind == "forall":
        role, body = concept[1], concept[2]
        return all(
            od_relation(node, target) != role or holds(target, body)
            for target in NODES
        )
    raise ValueError(concept)


def model_type(node):
    return frozenset(concept for concept in CLOSURE if holds(node, concept))


def demand_witnesses(node, demand):
    assert demand[0] == "exists"
    role, body = demand[1], demand[2]
    return tuple(
        target
        for target in NODES
        if od_relation(node, target) == role and holds(target, body)
    )


EXPECTED_WITNESSES = {
    "v1": {
        DEMAND_PP_D: ("y1",),
        DEMAND_PO_R: ("v2",),
        DEMAND_PO_S: ("x2",),
        DEMAND_PPI_TOP: ("x1",),
    },
    "v2": {
        DEMAND_PP_D: ("y2",),
        DEMAND_PO_R: ("v1",),
        DEMAND_PO_S: ("z1",),
        DEMAND_PPI_TOP: ("x2",),
    },
}


def check_types_and_witnesses():
    assert holds("v1", C0) and holds("v2", C0)
    type_v1 = model_type("v1")
    type_v2 = model_type("v2")
    assert type_v1 == type_v2

    # The gates are distinct, incomparable, and PO-related.
    assert od_relation("v1", "v2") == PO

    for gate, expected_by_demand in EXPECTED_WITNESSES.items():
        for demand, expected in expected_by_demand.items():
            actual = demand_witnesses(gate, demand)
            assert actual == expected, (gate, show(demand), actual, expected)

    # The proposed local syntactic label is realizable separately: each actual
    # PP witness realizes D and every forall-PP body present in the gate type.
    pp_universal_bodies = tuple(
        c[2] for c in type_v1 if c[0] == "forall" and c[1] == PP
    )
    class_top_label = (D,) + pp_universal_bodies
    assert all(holds("y1", c) for c in class_top_label)
    assert all(holds("y2", c) for c in class_top_label)
    return type_v1, pp_universal_bodies


# ------------------------------------------- common-class-top contradiction

def check_forced_common_top_contradiction():
    """Check the generic contradiction in every composition-closed extension.

    Hypotheses on fresh points t and z:

      v1 PP t, v2 PP t, z DR t, and z |= A.

    The first two express a shared top, while the latter two are exactly what
    t |= D supplies.  No relation involving a hypothetical point is guessed:
    all relations used below are forced singleton composition outcomes.
    """
    assert D == Exists(DR, A)
    assert A == Or(U_P, U_Q)

    # x_i PP v_i PP t forces x_i PP t.
    assert od_relation("x1", "v1") == PP
    assert od_relation("x2", "v2") == PP
    x_to_t = forced(PP, PP)
    assert x_to_t == PP
    t_to_x = CONVERSE[x_to_t]
    assert t_to_x == PPI

    # z DR t PPI x_i forces z DR x_i, for both i.
    z_to_x = forced(DR, t_to_x)
    assert z_to_x == DR

    # If z |= U_P, propagation along z DR x2 requires P(x2), false.
    # If z |= U_Q, propagation along z DR x1 requires Q(x1), false.
    obstructions = []
    for branch, lower_point in ((U_P, "x2"), (U_Q, "x1")):
        assert branch[0] == "forall" and branch[1] == DR
        required_atom = branch[2]
        assert required_atom[0] == "atom"
        atom_name = required_atom[1]
        assert z_to_x == DR
        assert atom_name not in VALUATION[lower_point]
        obstructions.append(
            f"{show(branch)} forces {atom_name}({lower_point}), "
            f"but {lower_point} satisfies not {atom_name}"
        )

    # Any witness of the disjunction A satisfies at least one of its branches,
    # and both branches have just been refuted.
    assert len(obstructions) == 2
    return obstructions


# --------------------------------------------------------------------- driver

def main():
    print("TARGET A -- EIGHT-POINT SHARED CLASS-TOP COUNTEREXAMPLE")
    print("=" * 72)

    print("[1] RCC5 table from finite-set semantics")
    print(f"    nonempty regions at size 4: {len(nonempty_subsets(4))}")
    print(f"    cells/outcomes: {len(CT)}/{sum(map(len, CT.values()))}")
    print("    size-4 and size-5 derivations agree: PASS")
    print(f"    PP;PP   = {sorted(CT[(PP, PP)])}")
    print(f"    DR;PPI  = {sorted(CT[(DR, PPI)])}")

    od_errors = check_ordered_disjoint_axioms()
    assert not od_errors, od_errors
    print("[2] Ordered-disjoint axioms: PASS")
    print("    strict order; symmetric irreflexive incomparable disjointness;")
    print("    downward closure of disjointness")

    network_errors = check_rcc5_network()
    assert not network_errors, network_errors
    print("[3] RCC5 converse, strong-EQ, and CT closure: PASS")
    print(f"    checked all {len(NODES) ** 3} ordered triples")

    closure_type, pp_bodies = check_types_and_witnesses()
    print("[4] Formula/model checks: PASS")
    print(f"    |sub(C0)| = {len(CLOSURE)}; forall-PO-free = True")
    print(
        "    v1 and v2 satisfy C0 and agree on all closure formulas "
        f"({len(closure_type)} true)"
    )
    for gate in ("v1", "v2"):
        rendered = ", ".join(
            f"{show(d)} -> {EXPECTED_WITNESSES[gate][d][0]}" for d in DEMANDS
        )
        print(f"    unique witnesses at {gate}: {rendered}")
    print(
        "    individual class-top label D + forall-PP bodies "
        f"({len(pp_bodies)} bodies) is realized at y1 and y2"
    )

    obstructions = check_forced_common_top_contradiction()
    print("[5] Fresh common D-top in any CT-closed extension: IMPOSSIBLE")
    print("    x_i PP v_i PP t forces x_i PP t")
    print("    z DR t PPI x_i forces z DR x_i")
    for obstruction in obstructions:
        print(f"    - {obstruction}")

    print("=" * 72)
    print("VERDICT: ALL CHECKS PASS; the T-only shared class-top repair is false.")


if __name__ == "__main__":
    main()
