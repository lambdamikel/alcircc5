#!/usr/bin/env python3
"""Full-logic boundary probe for the certified ConeScheme.

Purpose
=======

The Lean theorem ``decidableSat_cone`` assumes that ``forall PO`` does not
occur.  This probe demonstrates, deterministically, why that hypothesis cannot
be erased and why changing only the direct ``PO`` transition is insufficient.

It transcribes the finite control layer used by ``POFreeLift.lean`` and checks
two formulas outside the certified fragment:

DIRECT
    ``(forall PO.A) and (exists PO.not A)``

    This is unsatisfiable, but the current control graph has a two-signature
    post-fixed set carrying it because ``compatB PO`` imposes no universal
    transfer.

JOINT
    ``(exists PP.((forall PPI.A) and (forall PO.A)))
       and (exists PO.not A)``

    Let the two witnesses be ``y`` and ``z``.  From ``y PPI x`` and ``x PO z``,
    RCC5 composition gives ``y {PPI,PO} z``.  Either universal at ``y`` forces
    ``A`` at ``z``, contradicting ``not A``.  Nevertheless, the current control
    graph has a three-signature post-fixed set: the two demands are checked
    independently.  Thus strengthening only the *direct* PO-demand transition
    cannot repair the full logic.

The capped GFP runs are corroboration.  The explicit post-fixed sets are the
cap-independent argument: by monotonicity/greatest-post-fixed-point reasoning,
their root signatures survive in the full static space as well.

Expected result
===============

Both unsatisfiable, non-PO-free formulas are ACCEPTED by the hpo-erased control
test.  That is the expected boundary behavior, not a defect in the certified
forall-PO-free theorem.  The script exits 0 exactly when all algebraic,
post-fixed-set, and bounded-GFP checks reproduce that result.

Self-contained; Python 3 standard library only.
"""

from itertools import combinations


DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"


# ---------------------------------------------------------------- RCC5 table

def relation(a, b):
    """RCC5 relation of two nonempty finite sets."""
    if a == b:
        return EQ
    if a < b:
        return PP
    if b < a:
        return PPI
    return DR if not (a & b) else PO


def composition_table(universe_size=4):
    """Derive all 25 RCC5 composition cells from finite set semantics."""
    regions = [
        frozenset(xs)
        for size in range(1, universe_size + 1)
        for xs in combinations(range(universe_size), size)
    ]
    table = {}
    for a in regions:
        for b in regions:
            left = relation(a, b)
            for c in regions:
                table.setdefault((left, relation(b, c)), set()).add(
                    relation(a, c)
                )
    return table


COMP = composition_table()
assert len(COMP) == 25
assert COMP[(PPI, PO)] == {PPI, PO}


# ------------------------------------------------------------- concept syntax
#
# ('at', name), ('nat', name), ('top',), ('bot',)
# ('and', c, d), ('or', c, d), ('ex', r, c), ('all', r, c)

def closure(concept, result=None):
    result = [] if result is None else result
    if concept not in result:
        result.append(concept)
    if concept[0] in {"and", "or"}:
        closure(concept[1], result)
        closure(concept[2], result)
    elif concept[0] in {"ex", "all"}:
        closure(concept[2], result)
    return result


def po_free(concept):
    tag = concept[0]
    if tag in {"at", "nat", "top", "bot"}:
        return True
    if tag in {"and", "or"}:
        return po_free(concept[1]) and po_free(concept[2])
    if tag == "all" and concept[1] == PO:
        return False
    return po_free(concept[2])


# ------------------------------------------ exact ConeScheme control layer

def support_ok(concepts):
    """The Lean ``supportB`` conditions."""
    for concept in concepts:
        tag = concept[0]
        if tag == "bot":
            return False
        if tag == "at" and ("nat", concept[1]) in concepts:
            return False
        if tag == "and" and not (
            concept[1] in concepts and concept[2] in concepts
        ):
            return False
        if tag == "or" and not (
            concept[1] in concepts or concept[2] in concepts
        ):
            return False
        if tag in {"all", "ex"} and concept[1] == EQ:
            if concept[2] not in concepts:
                return False
    return True


def all_bodies(role, concepts):
    return frozenset(
        concept[2]
        for concept in concepts
        if concept[0] == "all" and concept[1] == role
    )


def cone(signature):
    typ, lowers = signature
    return (typ,) + tuple(lowers)


def signature_ok(signature):
    typ, lowers = signature
    if not support_ok(typ):
        return False
    for lower in lowers:
        if not support_ok(lower):
            return False
        if not all_bodies(PP, lower) <= typ:
            return False
        if not all_bodies(PPI, typ) <= lower:
            return False
    return True


def compatible(role, body, source, target):
    """The Lean ``compatB`` relation, including its unconstrained PO case."""
    if body not in target[0]:
        return False
    if role == PP:
        return all(member in target[1] for member in cone(source))
    if role == PPI:
        return all(member in source[1] for member in cone(target))
    if role == DR:
        for left in cone(source):
            for right in cone(target):
                if not all_bodies(DR, left) <= right:
                    return False
                if not all_bodies(DR, right) <= left:
                    return False
        return True
    return True  # PO and EQ impose no structural condition in compatB.


def demands(signature):
    return [
        (concept[1], concept[2])
        for concept in signature[0]
        if concept[0] == "ex" and concept[1] != EQ
    ]


def is_postfixed(signatures, closed):
    """The set lies in ``sigStatic`` and survives its own elimination."""
    closed_set = frozenset(closed)

    def is_static(signature):
        typ, lowers = signature
        return (
            signature_ok(signature)
            and typ <= closed_set
            and all(lower <= closed_set for lower in lowers)
        )

    return all(
        is_static(source)
        and all(
            any(compatible(role, body, source, target) for target in signatures)
            for role, body in demands(source)
        )
        for source in signatures
    )


def support_types(closed):
    result = []
    for size in range(len(closed) + 1):
        for items in combinations(closed, size):
            typ = frozenset(items)
            if support_ok(typ):
                result.append(typ)
    return result


def static_signatures(closed, lower_spectrum_cap):
    types = support_types(closed)
    result = []
    for typ in types:
        for size in range(min(lower_spectrum_cap, len(types)) + 1):
            for lowers in combinations(types, size):
                signature = (typ, frozenset(lowers))
                if signature_ok(signature):
                    result.append(signature)
    return result


def prune(signatures):
    return [
        source
        for source in signatures
        if all(
            any(compatible(role, body, source, target) for target in signatures)
            for role, body in demands(source)
        )
    ]


def bounded_gfp(concept, lower_spectrum_cap):
    signatures = static_signatures(closure(concept), lower_spectrum_cap)
    initial_count = len(signatures)
    rounds = 0
    while True:
        next_signatures = prune(signatures)
        rounds += 1
        if len(next_signatures) == len(signatures):
            signatures = next_signatures
            break
        signatures = next_signatures
    accepted = any(concept in signature[0] for signature in signatures)
    return accepted, initial_count, len(signatures), rounds


# --------------------------------------------------------- boundary examples

A = ("at", "A")
NOT_A = ("nat", "A")

ALL_PO_A = ("all", PO, A)
EX_PO_NOT_A = ("ex", PO, NOT_A)
DIRECT = ("and", ALL_PO_A, EX_PO_NOT_A)

ALL_PPI_A = ("all", PPI, A)
JOINT_BODY = ("and", ALL_PPI_A, ALL_PO_A)
EX_PP_JOINT_BODY = ("ex", PP, JOINT_BODY)
JOINT = ("and", EX_PP_JOINT_BODY, EX_PO_NOT_A)


def direct_postfixed_set():
    root_type = frozenset({DIRECT, ALL_PO_A, EX_PO_NOT_A})
    target_type = frozenset({NOT_A})
    empty = frozenset()
    return [
        (root_type, empty),
        (target_type, empty),
    ]


def joint_postfixed_set():
    # A is forced into the root type by the target's forall-PPI obligation:
    # the root type is a strict-lower type in the PP-target's spectrum.
    root_type = frozenset({JOINT, EX_PP_JOINT_BODY, EX_PO_NOT_A, A})
    pp_target_type = frozenset({JOINT_BODY, ALL_PPI_A, ALL_PO_A})
    po_target_type = frozenset({NOT_A})
    empty = frozenset()
    return [
        (root_type, empty),
        (pp_target_type, frozenset({root_type})),
        (po_target_type, empty),
    ]


def semantic_boundary_checks():
    """Check the finite algebraic cores of both impossibility arguments."""
    # DIRECT: the same PO witness must satisfy A (by forall) and not A (by ex).
    direct_roles_match = ALL_PO_A[1] == EX_PO_NOT_A[1] == PO
    direct_literal_clash = ALL_PO_A[2] == A and EX_PO_NOT_A[2] == NOT_A

    # JOINT: y PPI x and x PO z imply y {PPI,PO} z.  The two universals
    # cover the entire cell, so z must satisfy A although its demand says not A.
    joint_cell = COMP[(PPI, PO)]
    guarded_roles = {ALL_PPI_A[1], ALL_PO_A[1]}
    joint_cell_covered = joint_cell == guarded_roles == {PPI, PO}
    joint_literal_clash = ALL_PPI_A[2] == ALL_PO_A[2] == A
    joint_literal_clash &= EX_PO_NOT_A[2] == NOT_A

    return (
        direct_roles_match and direct_literal_clash,
        joint_cell_covered and joint_literal_clash,
    )


def main():
    direct_unsat_core, joint_unsat_core = semantic_boundary_checks()
    direct_postfixed = is_postfixed(direct_postfixed_set(), closure(DIRECT))
    joint_postfixed = is_postfixed(joint_postfixed_set(), closure(JOINT))

    direct_run = bounded_gfp(DIRECT, lower_spectrum_cap=0)
    joint_run = bounded_gfp(JOINT, lower_spectrum_cap=1)

    direct_expected = (True, 15, 15, 1)
    joint_expected = (True, 3450, 1410, 2)

    print("FULL-LOGIC BOUNDARY PROBE")
    print("=" * 72)
    print("DIRECT: (forall PO.A) and (exists PO.not A)")
    print(f"  in certified fragment:       {po_free(DIRECT)}")
    print(f"  semantic contradiction core: {direct_unsat_core}")
    print(f"  explicit post-fixed set:      {direct_postfixed}")
    print(
        "  capped GFP (cap 0):          "
        f"static={direct_run[1]}, survive={direct_run[2]}, "
        f"rounds={direct_run[3]}, "
        f"{'ACCEPT' if direct_run[0] else 'REJECT'}"
    )
    print()
    print("JOINT: ex PP.(all PPI.A and all PO.A) and ex PO.not A")
    print(f"  in certified fragment:       {po_free(JOINT)}")
    print(f"  comp(PPI,PO):                {sorted(COMP[(PPI, PO)])}")
    print(f"  semantic contradiction core: {joint_unsat_core}")
    print(f"  explicit post-fixed set:      {joint_postfixed}")
    print(
        "  capped GFP (cap 1):          "
        f"static={joint_run[1]}, survive={joint_run[2]}, "
        f"rounds={joint_run[3]}, "
        f"{'ACCEPT' if joint_run[0] else 'REJECT'}"
    )
    print("=" * 72)

    ok = all(
        [
            not po_free(DIRECT),
            not po_free(JOINT),
            direct_unsat_core,
            joint_unsat_core,
            direct_postfixed,
            joint_postfixed,
            direct_run == direct_expected,
            joint_run == joint_expected,
        ]
    )
    if ok:
        print("VERDICT: EXPECTED BOUNDARY REPRODUCED.")
        print("  The hpo-erased control test accepts both UNSAT examples.")
        print("  This does not challenge the certified forall-PO-free theorem;")
        print("  it proves that full logic needs joint cross-branch machinery.")
        return 0

    print("VERDICT: MISMATCH -- the recorded boundary behavior changed.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
