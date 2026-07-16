#!/usr/bin/env python3
"""
WP39 -- Small coarse-state W2' counterexample / repair witness.

Self-contained: derives the RCC5 composition table from finite set semantics,
then builds a one-separator / one-fresh glue step with three old occurrences
outside the separator.  It checks:

  1. the old side is a closed strong-EQ atomic RCC5 network;
  2. the glue step is jointly realizable;
  3. two old occurrences y,z have identical coarse state
     (same type, same row over the separator, same safe set toward fresh b);
  4. every joint realization forces y-b = DR and z-b = PPI;
     hence no coarse state-uniform steering function exists;
  5. a bounded principal-row refinement separates the collision.
"""

from itertools import combinations, product, permutations

BASE = ("EQ", "PP", "PPI", "PO", "DR")
NONEQ = ("PP", "PPI", "PO", "DR")
CONV = {"EQ": "EQ", "PP": "PPI", "PPI": "PP", "PO": "PO", "DR": "DR"}


def derive_comp(n=5):
    U = range(n)
    subs = [frozenset(c) for k in range(1, n + 1) for c in combinations(U, k)]

    def rel(a, b):
        if a == b:
            return "EQ"
        if not (a & b):
            return "DR"
        if a < b:
            return "PP"
        if b < a:
            return "PPI"
        return "PO"

    table = {(r, s): set() for r in BASE for s in BASE}
    for a in subs:
        for b in subs:
            r = rel(a, b)
            for c in subs:
                table[(r, rel(b, c))].add(rel(a, c))
    return {k: frozenset(v) for k, v in table.items()}


COMP = derive_comp()


def net_set(net, i, j, r):
    net[(i, j)] = r
    net[(j, i)] = CONV[r]


def is_closed(net, vertices):
    for i, j, k in permutations(vertices, 3):
        if net[(i, k)] not in COMP[(net[(i, j)], net[(j, k)])]:
            return False, (i, j, k, net[(i, j)], net[(j, k)], net[(i, k)], COMP[(net[(i, j)], net[(j, k)])])
    return True, None


def main():
    # Old side O plus separator s.  y and z are deliberately assigned the same concept type T.
    old_plus_sep = ["y", "z", "a", "s"]
    sep = ["s"]
    old = ["y", "z", "a"]
    fresh = ["b"]
    typ = {v: "T" for v in old_plus_sep + fresh}

    # Old frame.  The common separator row is y PP s and z PP s.
    frame = {}
    for i, j, r in [
        ("y", "z", "PP"),
        ("y", "a", "PP"),
        ("y", "s", "PP"),
        ("z", "a", "PPI"),
        ("z", "s", "PP"),
        ("a", "s", "PP"),
    ]:
        net_set(frame, i, j, r)

    ok, why = is_closed(frame, old_plus_sep)
    assert ok, f"old frame not closed: {why}"

    # Child pattern: b is a proper part of the separator s, i.e. s PPI b.
    pattern = {}
    net_set(pattern, "s", "b", "PPI")

    # Safe domains for old/fresh cross-pairs.
    domains = {
        ("y", "b"): frozenset({"DR", "PPI"}),
        ("z", "b"): frozenset({"DR", "PPI"}),
        ("a", "b"): frozenset({"PO"}),
    }

    def coarse_state(v):
        return (typ[v], tuple(frame[(v, s)] for s in sep), tuple(tuple(sorted(domains[(v, b)])) for b in fresh))

    assert coarse_state("y") == coarse_state("z")

    full_vertices = old_plus_sep + fresh
    joint_solutions = []
    for yb, zb, ab in product(sorted(domains[("y", "b")]), sorted(domains[("z", "b")]), sorted(domains[("a", "b")])):
        net = dict(frame)
        net.update(pattern)
        net_set(net, "y", "b", yb)
        net_set(net, "z", "b", zb)
        net_set(net, "a", "b", ab)
        ok, _ = is_closed(net, full_vertices)
        if ok:
            joint_solutions.append((yb, zb, ab))

    assert joint_solutions == [("DR", "PPI", "PO")], joint_solutions

    # Reason for the forced split:
    # y PP a and a PO b give y-b in {DR,PO,PP}; intersect Safe(y,b)={DR,PPI} -> DR.
    # z PPI a and a PO b give z-b in {PO,PPI}; intersect Safe(z,b)={DR,PPI} -> PPI.
    assert COMP[("PP", "PO")] == frozenset({"DR", "PO", "PP"})
    assert COMP[("PPI", "PO")] == frozenset({"PO", "PPI"})

    # Principal-row refinement for this one-fresh step: admissible b-values per old occurrence.
    principal = {}
    for v in old:
        vals = []
        for rb in sorted(domains[(v, "b")]):
            for yb, zb, ab in product(sorted(domains[("y", "b")]), sorted(domains[("z", "b")]), sorted(domains[("a", "b")])):
                chosen = {"y": yb, "z": zb, "a": ab}
                chosen[v] = rb
                net = dict(frame)
                net.update(pattern)
                for u, val in chosen.items():
                    net_set(net, u, "b", val)
                ok, _ = is_closed(net, full_vertices)
                if ok:
                    vals.append(rb)
                    break
        principal[v] = tuple(sorted(set(vals)))

    assert principal["y"] == ("DR",)
    assert principal["z"] == ("PPI",)
    assert principal["a"] == ("PO",)

    print("PASS: small W2' coarse-state failure verified")
    print("coarse_state(y) = coarse_state(z) =", coarse_state("y"))
    print("unique joint row (y-b, z-b, a-b) =", joint_solutions[0])
    print("principal-row refinement:", principal)


if __name__ == "__main__":
    main()
