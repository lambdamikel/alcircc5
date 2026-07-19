#!/usr/bin/env python3
"""Finite regression checks for the accompanying ALCI_RRCC5 F6 technical note.

The proofs in the note are arbitrary-domain arguments; this script is only a
sanity check against orientation and boundary mistakes.  It:
  1. derives the RCC5 weak-composition table from finite nonempty-set semantics;
  2. enumerates ordered-disjoint structures on at most four labelled points;
  3. checks composition closure and the canonical set representation; and
  4. checks the exact one-point extension criterion on every four-way assignment
     (below / above / disjoint / overlap) over those structures.

No third-party packages are required.
"""
from __future__ import annotations

from itertools import product
from typing import FrozenSet, Iterable

RELATIONS = ("EQ", "DR", "PO", "PP", "PPI")
Pair = FrozenSet[int]


def rcc5_set_relation(a: frozenset[int], b: frozenset[int]) -> str:
    if a == b:
        return "EQ"
    if a < b:
        return "PP"
    if b < a:
        return "PPI"
    if a.isdisjoint(b):
        return "DR"
    return "PO"


def derive_composition_table() -> dict[tuple[str, str], set[str]]:
    regions = [
        frozenset(i for i in range(5) if (mask >> i) & 1)
        for mask in range(1, 1 << 5)
    ]
    comp = {(r, s): set() for r in RELATIONS for s in RELATIONS}
    for a in regions:
        for b in regions:
            r = rcc5_set_relation(a, b)
            for c in regions:
                s = rcc5_set_relation(b, c)
                comp[(r, s)].add(rcc5_set_relation(a, c))
    return comp


def is_strict_partial_order(n: int, order: set[tuple[int, int]]) -> bool:
    if any(x == y for x, y in order):
        return False
    return all(
        (x, z) in order
        for x, y in order
        for y2, z in order
        if y == y2
    )


def leq(order: set[tuple[int, int]], x: int, y: int) -> bool:
    return x == y or (x, y) in order


def is_downward_closed_disjointness(
    n: int, order: set[tuple[int, int]], disjoint: set[Pair]
) -> bool:
    for edge in disjoint:
        x, y = tuple(edge)
        for xp in range(n):
            for yp in range(n):
                if leq(order, xp, x) and leq(order, yp, y):
                    if xp == yp or frozenset((xp, yp)) not in disjoint:
                        return False
                if leq(order, xp, y) and leq(order, yp, x):
                    if xp == yp or frozenset((xp, yp)) not in disjoint:
                        return False
    return True


def induced_relation(
    order: set[tuple[int, int]], disjoint: set[Pair], x: int, y: int
) -> str:
    if x == y:
        return "EQ"
    if (x, y) in order:
        return "PP"
    if (y, x) in order:
        return "PPI"
    if frozenset((x, y)) in disjoint:
        return "DR"
    return "PO"


def canonical_region(
    n: int, order: set[tuple[int, int]], disjoint: set[Pair], x: int
) -> frozenset[tuple[int, int]]:
    omega = {
        (u, v)
        for u in range(n)
        for v in range(n)
        if u == v or frozenset((u, v)) not in disjoint
    }
    return frozenset(
        (u, v) for (u, v) in omega if leq(order, u, x) or leq(order, v, x)
    )


def extension_conditions(
    n: int,
    order: set[tuple[int, int]],
    disjoint: set[Pair],
    lower: set[int],
    upper: set[int],
    new_disjoint: set[int],
) -> bool:
    if lower & upper or lower & new_disjoint or upper & new_disjoint:
        return False
    if any(y in lower and x not in lower for x, y in order):
        return False
    if any(x in upper and y not in upper for x, y in order):
        return False
    if any((l, u) not in order for l in lower for u in upper):
        return False
    if any(y in new_disjoint and x not in new_disjoint for x, y in order):
        return False
    if any(frozenset((l, d)) not in disjoint for l in lower for d in new_disjoint):
        return False
    for u in upper:
        for x in range(n):
            if x != u and frozenset((u, x)) in disjoint and x not in new_disjoint:
                return False
    return True


def direct_extension_is_valid(
    n: int,
    order: set[tuple[int, int]],
    disjoint: set[Pair],
    lower: set[int],
    upper: set[int],
    new_disjoint: set[int],
) -> bool:
    p = n
    extended_order = order | {(l, p) for l in lower} | {(p, u) for u in upper}
    extended_disjoint = disjoint | {frozenset((p, d)) for d in new_disjoint}
    return is_strict_partial_order(n + 1, extended_order) and is_downward_closed_disjointness(
        n + 1, extended_order, extended_disjoint
    )


def run(max_n: int = 4) -> None:
    comp = derive_composition_table()
    total_structures = 0
    total_extensions = 0

    for n in range(1, max_n + 1):
        oriented = [(i, j) for i in range(n) for j in range(n) if i != j]
        undirected = [frozenset((i, j)) for i in range(n) for j in range(i + 1, n)]
        structures_n = 0
        extensions_n = 0

        for mask in range(1 << len(oriented)):
            order = {oriented[k] for k in range(len(oriented)) if (mask >> k) & 1}
            if not is_strict_partial_order(n, order):
                continue

            for dmask in range(1 << len(undirected)):
                disjoint = {
                    undirected[k] for k in range(len(undirected)) if (dmask >> k) & 1
                }
                if not is_downward_closed_disjointness(n, order, disjoint):
                    continue

                structures_n += 1

                # Composition closure and exact canonical representation.
                regions = [canonical_region(n, order, disjoint, x) for x in range(n)]
                for x, y, z in product(range(n), repeat=3):
                    r = induced_relation(order, disjoint, x, y)
                    s = induced_relation(order, disjoint, y, z)
                    t = induced_relation(order, disjoint, x, z)
                    if t not in comp[(r, s)]:
                        raise AssertionError(("composition", n, x, y, z, r, s, t))
                for x, y in product(range(n), repeat=2):
                    expected = induced_relation(order, disjoint, x, y)
                    actual = rcc5_set_relation(regions[x], regions[y])
                    if actual != expected:
                        raise AssertionError(("representation", n, x, y, expected, actual))

                # All assignments of the new point: 0=below, 1=above,
                # 2=disjoint, 3=overlap.
                for assignment in product(range(4), repeat=n):
                    lower = {i for i, value in enumerate(assignment) if value == 0}
                    upper = {i for i, value in enumerate(assignment) if value == 1}
                    new_disjoint = {i for i, value in enumerate(assignment) if value == 2}
                    predicted = extension_conditions(
                        n, order, disjoint, lower, upper, new_disjoint
                    )
                    actual = direct_extension_is_valid(
                        n, order, disjoint, lower, upper, new_disjoint
                    )
                    if predicted != actual:
                        raise AssertionError(
                            ("extension", n, order, disjoint, assignment, predicted, actual)
                        )
                    extensions_n += 1

        total_structures += structures_n
        total_extensions += extensions_n
        print(
            f"n={n}: {structures_n} ordered-disjoint structures, "
            f"{extensions_n} one-point assignments - all checks passed"
        )

    print(
        f"TOTAL: {total_structures} structures and {total_extensions} "
        "one-point assignments checked"
    )


if __name__ == "__main__":
    run()
