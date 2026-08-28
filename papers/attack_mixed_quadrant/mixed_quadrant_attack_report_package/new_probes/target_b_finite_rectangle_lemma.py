#!/usr/bin/env python3
"""Executable checks supporting the finite cross-kernel rectangle lemma.

This is a finite, dependency-free probe rather than a formal proof.  It:

* rederives the RCC5 weak-composition table from nonempty finite sets and
  checks it against the standard table;
* derives the four one-coordinate transition systems (PP/PPI tower,
  left/right coordinate), checks the advertised rank certificates, and
  checks that their non-loop graphs are acyclic;
* instantiates the two interleaved towers which refute an infinite-tail
  constant-rectangle claim; and
* constructs arbitrarily late finite phase rectangles whose endpoints have
  recurrent model types.

Run with:  python target_b_finite_rectangle_lemma.py
"""

from __future__ import annotations

from itertools import product


RELATIONS = ("DR", "PO", "PP", "PPI", "EQ")
CONVERSE = {"DR": "DR", "PO": "PO", "PP": "PPI", "PPI": "PP", "EQ": "EQ"}


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


def regions(universe_size: int) -> tuple[frozenset[int], ...]:
    """All nonempty subsets of a finite universe."""

    return tuple(
        frozenset(i for i in range(universe_size) if mask & (1 << i))
        for mask in range(1, 1 << universe_size)
    )


def derive_composition(universe_size: int = 5) -> dict[tuple[str, str], frozenset[str]]:
    """Derive weak composition by enumerating triples of finite regions."""

    rs = regions(universe_size)
    table: dict[tuple[str, str], set[str]] = {
        (first, second): set() for first in RELATIONS for second in RELATIONS
    }
    for left, middle, right in product(rs, repeat=3):
        table[rcc5(left, middle), rcc5(middle, right)].add(rcc5(left, right))
    return {cell: frozenset(values) for cell, values in table.items()}


# Rows and columns are ordered DR, PO, PP, PPI, EQ.  This explicit table is
# deliberately independent of derive_composition, so the enumeration is a
# meaningful regression check rather than a comparison with itself.
EXPECTED_COMPOSITION_ROWS = {
    "DR": (
        {"DR", "PO", "PP", "PPI", "EQ"},
        {"DR", "PO", "PP"},
        {"DR", "PO", "PP"},
        {"DR"},
        {"DR"},
    ),
    "PO": (
        {"DR", "PO", "PPI"},
        {"DR", "PO", "PP", "PPI", "EQ"},
        {"PO", "PP"},
        {"DR", "PO", "PPI"},
        {"PO"},
    ),
    "PP": (
        {"DR"},
        {"DR", "PO", "PP"},
        {"PP"},
        {"DR", "PO", "PP", "PPI", "EQ"},
        {"PP"},
    ),
    "PPI": (
        {"DR", "PO", "PPI"},
        {"PO", "PPI"},
        {"PO", "PP", "PPI", "EQ"},
        {"PPI"},
        {"PPI"},
    ),
    "EQ": (
        {"DR"},
        {"PO"},
        {"PP"},
        {"PPI"},
        {"EQ"},
    ),
}


def expected_composition() -> dict[tuple[str, str], frozenset[str]]:
    return {
        (row, column): frozenset(EXPECTED_COMPOSITION_ROWS[row][column_index])
        for row in RELATIONS
        for column_index, column in enumerate(RELATIONS)
    }


def relation_set(values: frozenset[str] | set[str]) -> str:
    """Stable compact rendering of a relation set."""

    return "{" + ",".join(relation for relation in RELATIONS if relation in values) + "}"


def print_composition(table: dict[tuple[str, str], frozenset[str]]) -> None:
    print("RCC5 weak-composition table (row o column):")
    print("       " + "  ".join(f"{relation:>14}" for relation in RELATIONS))
    for row in RELATIONS:
        cells = "  ".join(f"{relation_set(table[row, column]):>14}" for column in RELATIONS)
        print(f"{row:>4}   {cells}")


def derive_transitions(
    axis: str, step_relation: str, universe_size: int = 5
) -> dict[str, frozenset[str]]:
    """Derive old-to-new row values for one moving coordinate.

    ``step_relation`` is the relation from the old tower point to the new
    tower point.  ``axis`` says whether that tower occupies the left or right
    coordinate of the observed RCC5 row.
    """

    assert axis in {"left", "right"}
    assert step_relation in {"PP", "PPI"}
    rs = regions(universe_size)
    result = {relation: set() for relation in RELATIONS}
    for old, new, fixed in product(rs, repeat=3):
        if rcc5(old, new) != step_relation:
            continue
        if axis == "left":
            before, after = rcc5(old, fixed), rcc5(new, fixed)
        else:
            before, after = rcc5(fixed, old), rcc5(fixed, new)
        result[before].add(after)
    return {before: frozenset(after) for before, after in result.items()}


# Each tuple lists equal-rank classes from low to high.  Every allowed
# non-loop transition must go strictly to the right in this ordering.
RANK_CERTIFICATES = {
    ("left", "PP"): (("PP", "DR"), ("PO", "EQ"), ("PPI",)),
    ("right", "PP"): (("PPI", "DR"), ("PO", "EQ"), ("PP",)),
    ("left", "PPI"): (("PPI",), ("PO", "EQ"), ("DR", "PP")),
    ("right", "PPI"): (("PP",), ("PO", "EQ"), ("DR", "PPI")),
}


def has_nonloop_cycle(transitions: dict[str, frozenset[str]]) -> bool:
    """Detect a directed cycle after deleting self-loops."""

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(node: str) -> bool:
        if node in visiting:
            return True
        if node in visited:
            return False
        visiting.add(node)
        for successor in transitions[node]:
            if successor != node and visit(successor):
                return True
        visiting.remove(node)
        visited.add(node)
        return False

    return any(visit(node) for node in RELATIONS if node not in visited)


def verify_transition_certificate(
    axis: str, step_relation: str, transitions: dict[str, frozenset[str]]
) -> None:
    classes = RANK_CERTIFICATES[axis, step_relation]
    rank = {
        relation: class_index
        for class_index, relation_class in enumerate(classes)
        for relation in relation_class
    }
    assert set(rank) == set(RELATIONS)
    for before, successors in transitions.items():
        for after in successors:
            if before != after:
                assert rank[before] < rank[after], (
                    axis,
                    step_relation,
                    before,
                    after,
                    rank,
                )
    assert not has_nonloop_cycle(transitions)

    rank_text = " < ".join("{" + ",".join(group) + "}" for group in classes)
    print(f"\n{axis:>5} coordinate, {step_relation} tower: {rank_text}")
    for before in RELATIONS:
        print(f"  {before:>3} -> {relation_set(transitions[before])}")
    print("  verified: every non-loop transition strictly raises rank; graph is acyclic")


Point = tuple[int, int]


def interleaved_relation(left: Point, right: Point) -> str:
    """RCC5 relation in the ordered, overlapping two-lane frame."""

    if left == right:
        return "EQ"
    left_index, _left_lane = left
    right_index, _right_lane = right
    if left_index < right_index:
        return "PP"
    if left_index > right_index:
        return "PPI"
    return "PO"


def tower(lane: int, index: int) -> Point:
    return (index, lane)


def verify_interleaved_frame(composition: dict[tuple[str, str], frozenset[str]]) -> None:
    """Check a bounded induced fragment against all RCC5 CT constraints."""

    points = tuple((index, lane) for index in range(-3, 4) for lane in (0, 1))
    for left, middle, right in product(points, repeat=3):
        first = interleaved_relation(left, middle)
        second = interleaved_relation(middle, right)
        result = interleaved_relation(left, right)
        assert result in composition[first, second], (left, middle, right, first, second, result)

    for first_index, second_index in product(range(-5, 6), repeat=2):
        expected = (
            "PP"
            if first_index < second_index
            else "PPI"
            if first_index > second_index
            else "PO"
        )
        assert interleaved_relation(tower(0, first_index), tower(1, second_index)) == expected


def verify_no_constant_cofinal_tail() -> None:
    """Instantiate, then print, the general no-constant-tail argument."""

    for left_start, right_start in product((0, 1, 4, 17), repeat=2):
        cap = max(left_start, right_start) + 3
        observed = {
            interleaved_relation(tower(0, i), tower(1, j))
            for i in range(left_start, cap + 1)
            for j in range(right_start, cap + 1)
        }
        assert observed == {"PP", "PO", "PPI"}, (left_start, right_start, observed)

    print("\nInfinite-tail counterexample:")
    print("  R(c0(i),c1(j)) = PP if i<j, PO if i=j, and PPI if i>j.")
    print("  Given tail bounds I,J, let k=max(I,J).  The tail contains")
    print("  (i,j)=(k,k+1), with relation PP, and (k+1,k), with relation PPI.")
    print("  Therefore no product of two cofinal tails is constant.")


def model_type(lane: int, index: int) -> tuple[int, int]:
    """A toy recurrent type sequence: period two on lane 0, three on lane 1."""

    period = 2 if lane == 0 else 3
    return lane, index % period


def finite_rectangle(lower_bound: int) -> tuple[range, range, str]:
    """Construct a constant rectangle later than ``lower_bound``."""

    left_start = lower_bound
    left_end = left_start + 2  # lane-0 endpoint repeats its period-2 type
    right_start = max(lower_bound, left_end)
    right_end = right_start + 3  # lane-1 endpoint repeats its period-3 type
    left_segment = range(left_start, left_end)
    right_segment = range(right_start, right_end)

    assert model_type(0, left_start) == model_type(0, left_end)
    assert model_type(1, right_start) == model_type(1, right_end)
    values = {
        interleaved_relation(tower(0, i), tower(1, j))
        for i in left_segment
        for j in right_segment
    }
    assert values == {"PP"}
    reverse_values = {
        interleaved_relation(tower(1, j), tower(0, i))
        for i in left_segment
        for j in right_segment
    }
    assert reverse_values == {"PPI"}
    return left_segment, right_segment, values.pop()


def main() -> None:
    composition = derive_composition(5)
    assert composition == expected_composition()
    # Saturation by five atoms is also checked against a larger universe.
    assert derive_composition(6) == composition
    print_composition(composition)
    print("verified: exhaustive nonempty-set derivation on 5 and 6 atoms agrees with the RCC5 CT")

    print("\nFour transition tables:")
    for axis, step_relation in RANK_CERTIFICATES:
        transitions = derive_transitions(axis, step_relation, 5)
        # A sixth atom must not add a transition omitted by the smaller probe.
        assert derive_transitions(axis, step_relation, 6) == transitions
        verify_transition_certificate(axis, step_relation, transitions)

    verify_interleaved_frame(composition)
    print("\nverified: the bounded interleaved frame respects every RCC5 CT cell")
    verify_no_constant_cofinal_tail()

    print("\nArbitrarily late finite rectangles with recurrent endpoint types:")
    for lower_bound in (0, 10, 100, 10_000):
        left, right, value = finite_rectangle(lower_bound)
        print(
            f"  lower bound {lower_bound:>5}: "
            f"c0[{left.start}:{left.stop}) x c1[{right.start}:{right.stop}) = {value}"
        )
    print("\nPASS: all Target-B finite checks succeeded.")


if __name__ == "__main__":
    main()
