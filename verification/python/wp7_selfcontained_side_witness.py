#!/usr/bin/env python3
"""
WP7 self-contained: side-witness comparability stress test.

Round-6 (G6) repair: GPT-5.5's round-6 review noted that
wp7_side_witness_stress.py imports project modules from src/ and
therefore does not run from the verification archive alone. This
script is the requested self-contained replacement.

We construct a concrete three-element abstract RCC5 frame:

    Delta = {x, y, z},
    A = {y},
    B = {z},
    rho(x, y) = DR,
    rho(x, z) = DR,
    rho(y, z) = PP,
    (inverses and reflexive EQ filled in automatically).

We then directly evaluate the satisfaction relation for the round-5
stress concept

    C_side := exists DR.(A and exists PP.B) and exists DR.B

at the root x, with no external imports. The script also explicitly
verifies the JEPD axioms, the RCC5 composition table, and the
inverse/reflexivity laws on this small frame.

Expected output: ALL CHECKS PASS, including SAT at x.

If this script passes, it is reproducible from the verification
archive alone, with no dependencies outside the Python standard
library.
"""

import sys
import itertools

# -----------------------------------------------------------------
# RCC5 base relations and basic operations
# -----------------------------------------------------------------

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
BASE = (DR, PO, EQ, PP, PPI)

INV = {DR: DR, PO: PO, EQ: EQ, PP: PPI, PPI: PP}


def _composition_table():
    """RCC5 composition table (Renz & Nebel 1999, equivalent form).

    Returns a dict mapping (r1, r2) to the set of permitted labels for the
    third pair under composition r1; r2.
    """
    # The complete RCC5 composition table.
    table = {
        (DR, DR): {DR, PO, EQ, PP, PPI},
        (DR, PO): {DR, PO, PP},
        (DR, EQ): {DR},
        (DR, PP): {DR, PO, PP},
        (DR, PPI): {DR},
        (PO, DR): {DR, PO, PPI},
        (PO, PO): {DR, PO, EQ, PP, PPI},
        (PO, EQ): {PO},
        (PO, PP): {PO, PP},
        (PO, PPI): {DR, PO, PPI},
        (EQ, DR): {DR},
        (EQ, PO): {PO},
        (EQ, EQ): {EQ},
        (EQ, PP): {PP},
        (EQ, PPI): {PPI},
        (PP, DR): {DR},
        (PP, PO): {DR, PO, PP},
        (PP, EQ): {PP},
        (PP, PP): {PP},
        (PP, PPI): {DR, PO, EQ, PP, PPI},
        (PPI, DR): {DR, PO, PPI},
        (PPI, PO): {PO, PPI},
        (PPI, EQ): {PPI},
        (PPI, PP): {DR, PO, EQ, PP, PPI},
        (PPI, PPI): {PPI},
    }
    return table


COMP = _composition_table()


# -----------------------------------------------------------------
# The concrete frame for the stress concept
# -----------------------------------------------------------------

Delta = ("x", "y", "z")
A = {"y"}
B = {"z"}

# rho(a, b) for a != b, and EQ on the diagonal.
rho_directed = {
    ("x", "y"): DR,
    ("x", "z"): DR,
    ("y", "z"): PP,
}


def rho(a, b):
    if a == b:
        return EQ
    if (a, b) in rho_directed:
        return rho_directed[(a, b)]
    # Symmetric / inverse fill-in.
    if (b, a) in rho_directed:
        return INV[rho_directed[(b, a)]]
    raise ValueError(f"undefined pair ({a}, {b})")


# -----------------------------------------------------------------
# Frame axiom checks
# -----------------------------------------------------------------


def check_jepd():
    """Every pair gets exactly one base relation."""
    for a, b in itertools.product(Delta, repeat=2):
        r = rho(a, b)
        if r not in BASE:
            return f"({a},{b}) -> {r!r} not in BASE"
    return None


def check_inverse():
    """rho(b, a) == inv(rho(a, b))."""
    for a, b in itertools.product(Delta, repeat=2):
        if rho(b, a) != INV[rho(a, b)]:
            return f"({a},{b}): inverse mismatch"
    return None


def check_eq_identity():
    """EQ holds iff a == b (strong-EQ semantics)."""
    for a, b in itertools.product(Delta, repeat=2):
        if rho(a, b) == EQ and a != b:
            return f"({a},{b}): EQ but not identity"
        if a == b and rho(a, b) != EQ:
            return f"({a},{a}): not EQ"
    return None


def check_composition_table():
    """For every triple (a,b,c), rho(a,c) is in comp(rho(a,b), rho(b,c))."""
    for a, b, c in itertools.product(Delta, repeat=3):
        ab, bc, ac = rho(a, b), rho(b, c), rho(a, c)
        if ac not in COMP[(ab, bc)]:
            return f"({a},{b},{c}): {ac} not in comp({ab},{bc}) = {sorted(COMP[(ab, bc)])}"
    return None


# -----------------------------------------------------------------
# Concept satisfaction (positive fragment, sufficient for C_side)
# -----------------------------------------------------------------


def sat_atom(a, X):
    """True iff a is in atomic concept set X."""
    return a in X


def sat_exists(a, R, body_fn):
    """True iff some witness w with rho(a, w) = R satisfies body_fn(w)."""
    for w in Delta:
        if rho(a, w) == R and body_fn(w):
            return True
    return False


def sat_and(predicates, a):
    """All predicates hold at a."""
    return all(p(a) for p in predicates)


def stress_concept(a):
    """C_side := exists DR.(A and exists PP.B) and exists DR.B."""

    def inner_left(y_):
        # A(y) and exists PP.B(y)
        return sat_atom(y_, A) and sat_exists(y_, PP, lambda z_: sat_atom(z_, B))

    left = sat_exists(a, DR, inner_left)
    right = sat_exists(a, DR, lambda z_: sat_atom(z_, B))
    return left and right


# -----------------------------------------------------------------
# Main
# -----------------------------------------------------------------


def main():
    print("WP7 self-contained: side-witness comparability stress test")
    print(f"  Domain: {Delta}, A = {sorted(A)}, B = {sorted(B)}")
    print(f"  rho: x DR y, x DR z, y PP z (+ inverses and reflexive EQ)")
    print()

    failed = []
    for name, fn in [
        ("JEPD (every pair labelled)", check_jepd),
        ("inverse (rho(b,a) = inv(rho(a,b)))", check_inverse),
        ("strong-EQ (EQ iff identity)", check_eq_identity),
        ("RCC5 composition table", check_composition_table),
    ]:
        err = fn()
        if err is None:
            print(f"  PASS: {name}")
        else:
            print(f"  FAIL: {name}: {err}")
            failed.append(name)

    sat_at_x = stress_concept("x")
    print()
    print(f"  C_side := exists DR.(A and exists PP.B) and exists DR.B")
    print(f"  Satisfied at x: {sat_at_x}")

    if not sat_at_x:
        failed.append("stress-concept SAT at x")
        print("  FAIL: stress concept should be SAT at x")
    else:
        print("  PASS: stress concept is SAT at x")

    print()
    if failed:
        print(f"  RESULT: FAILED ({len(failed)} check(s))")
        return 1
    print("  RESULT: ALL CHECKS PASS, self-contained")
    return 0


if __name__ == "__main__":
    sys.exit(main())
