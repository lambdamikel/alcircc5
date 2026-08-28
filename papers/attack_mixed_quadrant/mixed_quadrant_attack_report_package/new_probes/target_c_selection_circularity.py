#!/usr/bin/env python3
"""Executable checks for the Target-C selection-circularity example.

The regions are A_n={0,...,n} and B_m={m+1}.  The probe checks their RCC5
relation law, checks bounded instances of the incompatible fixed-point
conditions, and exhibits the unbounded witness/reselection chase.

Run with:  python target_c_selection_circularity.py
"""

from __future__ import annotations


def rcc5(left: frozenset[int], right: frozenset[int]) -> str:
    """Return the RCC5 base relation of two nonempty extensional regions."""

    assert left and right
    if left == right:
        return "EQ"
    if left.isdisjoint(right):
        return "DR"
    if left < right:
        return "PP"
    if left > right:
        return "PPI"
    return "PO"


def a_region(n: int) -> frozenset[int]:
    assert n >= 0
    return frozenset(range(n + 1))


def b_region(m: int) -> frozenset[int]:
    assert m >= 0
    return frozenset({m + 1})


def predicted_relation(n: int, m: int) -> str:
    """The claimed closed form for R(A_n,B_m)."""

    return "DR" if n <= m else "PPI"


def stabilization_threshold(m: int) -> int:
    """First A-index after which the row against B_m is constantly PPI."""

    return m + 1


def verify_relation_law(bound: int) -> None:
    for n in range(bound + 1):
        for m in range(bound + 1):
            actual = rcc5(a_region(n), b_region(m))
            assert actual == predicted_relation(n, m), (n, m, actual)


def verify_row_stabilization(bound: int) -> None:
    for m in range(bound + 1):
        threshold = stabilization_threshold(m)
        # Before the threshold, every available A_n is disjoint from B_m.
        assert all(rcc5(a_region(n), b_region(m)) == "DR" for n in range(threshold))
        # At and after it, the singleton B_m is a proper part of A_n.
        assert all(
            rcc5(a_region(n), b_region(m)) == "PPI"
            for n in range(threshold, bound + 2)
        )


def fixed_point_candidates(bound: int) -> list[tuple[int, int]]:
    """Pairs satisfying both DR-witnesshood and tail-stable selection."""

    return [
        (n, m)
        for n in range(bound + 1)
        for m in range(bound + 1)
        if rcc5(a_region(n), b_region(m)) == "DR"
        and n >= stabilization_threshold(m)
    ]


def verify_no_bounded_fixed_point() -> None:
    for bound in (1, 5, 10, 25, 100):
        candidates = fixed_point_candidates(bound)
        assert candidates == [], (bound, candidates)
        print(f"  indices 0..{bound:>3}: 0 fixed-point pairs")


def verify_chase(steps: int = 12) -> list[tuple[int, int, int]]:
    """Use least choices to instantiate the forced increasing chase.

    A selected A_n gets the least DR witness B_m, namely m=n.  Reselection
    beyond that witness's row threshold picks n'=m+1.  The returned triples
    are (selected n, witness m, next selected n').
    """

    n = 0
    trace: list[tuple[int, int, int]] = []
    for _ in range(steps):
        m = n
        assert rcc5(a_region(n), b_region(m)) == "DR"
        next_n = stabilization_threshold(m)
        assert next_n > m >= n
        # Moving beyond the threshold invalidates the witness just selected.
        assert rcc5(a_region(next_n), b_region(m)) == "PPI"
        trace.append((n, m, next_n))
        n = next_n
    return trace


def verify_arbitrary_choices(bound: int = 40) -> None:
    """Check the chase inequalities for all bounded non-minimal choices."""

    for n in range(bound + 1):
        for m in range(n, bound + 1):
            # m>=n is exactly the DR-witness condition.
            assert rcc5(a_region(n), b_region(m)) == "DR"
            for next_n in range(m + 1, bound + 2):
                # Any legal reselection is strictly later and loses that DR row.
                assert n <= m < next_n
                assert rcc5(a_region(next_n), b_region(m)) == "PPI"


def main() -> None:
    verify_relation_law(150)
    verify_row_stabilization(150)
    print("Verified relation law on 0<=n,m<=150:")
    print("  R(A_n,B_m) = DR when n<=m, and PPI when n>=m+1.")
    print("  For fixed B_m, the row is constantly PPI from threshold m+1 onward.")

    print("\nBounded search for a tail-stable DR-witness fixed point:")
    verify_no_bounded_fixed_point()
    verify_arbitrary_choices()

    print("\nSymbolic inequality argument:")
    print("  B_m is a DR witness for A_n       iff n <= m.")
    print("  A_n is in the stable tail of B_m  only if n >= m+1.")
    print("  Together they require m+1 <= n <= m, an impossibility.")

    print("\nLeast-choice witness/reselection chase:")
    print("  selected n | DR witness m | next n beyond threshold")
    for n, m, next_n in verify_chase():
        print(f"  {n:>10} | {m:>12} | {next_n:>23}")
    print("  In general: n <= m < n' <= m' < n'' <= ...; no finite stage closes.")

    print("\nPASS: all Target-C circularity checks succeeded.")


if __name__ == "__main__":
    main()
