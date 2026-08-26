#!/usr/bin/env python3
"""WP121 -- full applicable MultiTierOk check for the thin fence certificate.

This probe strengthens wp120's counting result.  For every fence length L it
constructs the same two-external, zero-kernel certificate and checks the literal
MultiTierOk obligations that remain non-vacuous:

  frame_q (identity, converse, and RCC5 composition closure),
  e_clash, e_nobot, e_and, e_or, ee_all, and e_ex.

All kernel fields are vacuous because kappa is empty.

CONTROLS, stated before the run:
  1. The root and witness are distinct and the read-off edge is PP.
  2. Every supported label formula is true at its assigned model point.
  3. Removing B0 from the witness label must produce exactly one e_ex failure.
  4. Restoring B0 must make every checked obligation hold.

The RCC5 relation and composition table are re-derived from finite set
semantics.  This is a finite-family acceptance result, not a completeness proof.
"""

from itertools import combinations

from wp120_support_label_fence import (
    B0, C0, F0, JUNK, R, make_fence, rel, sat,
)

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
CONV = {DR: DR, PO: PO, EQ: EQ, PP: PPI, PPI: PP}


def composition_table():
    regions = [frozenset(c) for k in range(1, 6)
               for c in combinations(range(5), k)]
    table = {}
    for a in regions:
        for b in regions:
            r1 = rel(a, b)
            for c in regions:
                table.setdefault((r1, rel(b, c)), set()).add(rel(a, c))
    return table


CT = composition_table()


def thin_certificate(nodes, X, Y, val, omit_witness_argument=False):
    root, witness = X[0], Y[0]
    labels = {
        root: {C0, F0, ("or", R, JUNK), R},
        witness: set() if omit_witness_argument else {B0},
    }
    ext = [root, witness]
    E = {(x, y): rel(x, y) for x in ext for y in ext}
    return ext, E, labels, root, witness


def check_certificate(nodes, val, ext, E, labels):
    bad = {}

    def note(name):
        bad[name] = bad.get(name, 0) + 1

    # qnet has only externals here: kappa is empty.
    for x in ext:
        if E[(x, x)] != EQ:
            note("frame_q_refl")
        for y in ext:
            if CONV[E[(x, y)]] != E[(y, x)]:
                note("frame_q_conv")
            for z in ext:
                if E[(x, z)] not in CT[(E[(x, y)], E[(y, z)])]:
                    note("frame_q_comp")

    for x in ext:
        lab = labels[x]
        for f in list(lab):
            kind = f[0]
            if kind == "at" and ("nat", f[1]) in lab:
                note("e_clash")
            elif kind == "nat" and ("at", f[1]) in lab:
                note("e_clash")
            elif kind == "bot":
                note("e_nobot")
            elif kind == "and":
                if f[1] not in lab or f[2] not in lab:
                    note("e_and")
            elif kind == "or":
                if f[1] not in lab and f[2] not in lab:
                    note("e_or")
            elif kind == "all":
                for y in ext:
                    if E[(x, y)] == f[1] and f[2] not in labels[y]:
                        note("ee_all")
            elif kind == "ex":
                if not any(E[(x, y)] == f[1] and f[2] in labels[y]
                           for y in ext):
                    note("e_ex")
    return bad


def main():
    print("WP121 -- thin-support MultiTierOk acceptance on the fence\n")
    print("    L    negative control                  treatment")
    for L in (1, 2, 4, 8, 12, 18, 26, 40):
        nodes, X, Y, val = make_fence(L)

        ext, E, labels, root, witness = thin_certificate(
            nodes, X, Y, val, omit_witness_argument=True)
        assert root != witness
        assert E[(root, witness)] == PP
        assert sat(nodes, val, root, C0)
        for x in ext:
            assert all(sat(nodes, val, x, f) for f in labels[x])
        control = check_certificate(nodes, val, ext, E, labels)
        assert control == {"e_ex": 1}, control

        ext, E, labels, root, witness = thin_certificate(
            nodes, X, Y, val, omit_witness_argument=False)
        assert all(sat(nodes, val, x, f) for x in ext for f in labels[x])
        treatment = check_certificate(nodes, val, ext, E, labels)
        assert treatment == {}, treatment

        print(f"   {L:2d}    e_ex=1 (as expected)             PASS")

    print("\n" + "=" * 76)
    print("  CONTROLS HELD.  The two-external, zero-kernel support certificate")
    print("  satisfies every non-vacuous MultiTierOk field checked here.")
    print("  This validates the fixed fence family only; it does not establish")
    print("  termination of support generation for arbitrary C0.")
    print("=" * 76)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
