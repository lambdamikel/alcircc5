#!/usr/bin/env python3
"""Finite counterexample to global borrowed-edge acyclicity (Target D1).

The model is a genuine finite RCC5 set model.  Its strict PP relation is strict
set inclusion.  The gate key is exactly

    q(v) = (mty(v), {mty(x) : x PP v}).

There are two blocked-key groups.  The first has two borrowers sharing one
target.  No group has a model-agreeing witness, so the stipulated selector uses
its fallback.  Every fallback target is individually safe (it is PO, not below,
its borrower), but the union of model-PP and borrowed edges has a directed
cycle.  Thus per-edge safety is insufficient.
"""

from itertools import product


DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"


def rel(x, y):
    """RCC5 atom of two nonempty finite regions."""
    if x == y:
        return EQ
    if x < y:
        return PP
    if y < x:
        return PPI
    if x.isdisjoint(y):
        return DR
    return PO


# Four common minimal points, followed by two branches.  These sets are the
# principal ideals of the intended poset, so inclusion has exactly the listed
# order and no unintended cross-branch comparabilities.
R = {
    "b00": frozenset({0}),
    "b01": frozenset({1}),
    "b10": frozenset({2}),
    "b11": frozenset({3}),
    "a1": frozenset({0, 1, 2, 3, 4}),
    "a2": frozenset({0, 1, 2, 3, 5}),
    "z1": frozenset({0, 1, 2, 3, 4, 6}),
    "z2": frozenset({0, 1, 2, 3, 5, 7}),
    "v2": frozenset({0, 1, 2, 3, 4, 6, 8}),
    "v1": frozenset({0, 1, 2, 3, 5, 7, 9}),
    "v1b": frozenset({0, 1, 2, 3, 5, 7, 12}),
    "t2": frozenset({0, 1, 2, 3, 4, 6, 8, 10}),
    "t1": frozenset({0, 1, 2, 3, 5, 7, 9, 11}),
    "t1b": frozenset({0, 1, 2, 3, 5, 7, 12, 13}),
}

# Model enumeration used by the deterministic first-witness fallback.  The
# desired gate-mate witnesses occur before their other PP successors.
MODEL_ORDER = [
    "b00", "b01", "b10", "b11", "a1", "a2", "z1", "z2",
    "v1", "v1b", "v2", "t1", "t1b", "t2",
]

# The declared frame only uses extracted external nodes, not every point of the
# source model.  CORE already refutes D1.  SHARED adds a second borrower of z1
# to audit the multiple-borrower case without changing the source model.
CORE = ["b00", "b01", "b10", "b11", "a1", "a2", "z1", "z2", "v2", "v1"]
SHARED = CORE + ["v1b"]


# Concept syntax: at/nat, and/or, ex/all.  C0 has no universal modality at all,
# hence in particular no universal PO.  tau is a tautology whose two atoms
# expose four different model types.  d is the borrowed PP demand.
P_TOP = ("or", ("at", "P"), ("nat", "P"))
Q_TOP = ("or", ("at", "Q"), ("nat", "Q"))
TAU = ("and", P_TOP, Q_TOP)
D = ("ex", PP, TAU)
C0 = ("and", D, TAU)


def closure(c, out=None):
    if out is None:
        out = []
    if c in out:
        return out
    out.append(c)
    if c[0] in ("and", "or"):
        closure(c[1], out)
        closure(c[2], out)
    elif c[0] in ("ex", "all"):
        closure(c[2], out)
    return out


CL = tuple(closure(C0))


def po_free(c):
    op = c[0]
    if op in ("at", "nat"):
        return True
    if op in ("and", "or"):
        return po_free(c[1]) and po_free(c[2])
    if op == "all" and c[1] == PO:
        return False
    return po_free(c[2])

# Colour the nonmaximal points so the two desired repeated types differ, while
# z1 and z2 have keys different from their gate mates.  Top points have the same
# atomic colours as indicated, but lack D because they are maximal.
COLOUR = {
    "b00": (False, False), "a1": (False, False),
    "v1": (False, False), "v1b": (False, False),
    "b01": (False, True), "a2": (False, True), "v2": (False, True),
    "b10": (True, False), "z1": (True, False),
    "b11": (True, True), "z2": (True, True),
    "t1": (False, False), "t1b": (True, False), "t2": (False, True),
}


def atom(name, point):
    bit = 0 if name == "P" else 1
    return COLOUR[point][bit]


def sat(point, c):
    op = c[0]
    if op == "at":
        return atom(c[1], point)
    if op == "nat":
        return not atom(c[1], point)
    if op == "and":
        return sat(point, c[1]) and sat(point, c[2])
    if op == "or":
        return sat(point, c[1]) or sat(point, c[2])
    if op == "ex":
        return any(
            rel(R[point], R[y]) == c[1] and sat(y, c[2])
            for y in MODEL_ORDER
        )
    if op == "all":
        return all(
            rel(R[point], R[y]) != c[1] or sat(y, c[2])
            for y in MODEL_ORDER
        )
    raise AssertionError(op)


def mty(point):
    return frozenset(c for c in CL if sat(point, c))


def spectrum(point):
    # The down-spectrum is taken in the source model, not merely among extracted
    # externals.
    return frozenset(
        mty(x) for x in MODEL_ORDER if rel(R[x], R[point]) == PP
    )


def key(point):
    return mty(point), spectrum(point)


def gate_and_groups(nodes):
    first = {}
    gate = []
    blocked = []
    for x in nodes:
        k = key(x)
        if k not in first:
            first[k] = x
            gate.append(x)
        else:
            blocked.append(x)
    groups = {}
    for v in blocked:
        if D in mty(v):
            a = first[key(v)]
            groups.setdefault(a, []).append(v)
    return gate, blocked, groups


def phase1_core_from_duplicate_free_seed():
    """Reproduce CORE by the abstract gate expansion used in the packet.

    The six-point seed has pairwise different exact keys.  Each surviving gate
    point with the nonpersistent demand D contributes its first model witness.
    """
    nodes = ["b00", "b01", "b10", "b11", "a1", "a2"]
    assert len({key(x) for x in nodes}) == len(nodes)
    guard = ("all", PP, D)
    for _ in range(10):
        gate, _blocked, _groups = gate_and_groups(nodes)
        new = []
        for a in gate:
            if D not in mty(a) or sat(a, guard):
                continue
            w = fallback_first(a)
            if w not in nodes and w not in new:
                new.append(w)
        if not new:
            return nodes
        nodes.extend(new)
    raise AssertionError("phase-1 simulation did not close")


def agreeing_candidates(a, borrowers):
    return [
        y for y in MODEL_ORDER
        if rel(R[a], R[y]) == PP
        and sat(y, TAU)
        and all(rel(R[v], R[y]) == PP for v in borrowers)
    ]


def fallback_first(a):
    return next(
        y for y in MODEL_ORDER
        if rel(R[a], R[y]) == PP and sat(y, TAU)
    )


def transitive_closure(nodes, edges):
    reach = {(x, y): False for x, y in product(nodes, repeat=2)}
    for x, y in edges:
        reach[x, y] = True
    for k in nodes:
        for i in nodes:
            if reach[i, k]:
                for j in nodes:
                    if reach[k, j]:
                        reach[i, j] = True
    return reach


def run_case(nodes, shared):
    gate, blocked, groups = gate_and_groups(nodes)

    assert po_free(C0)
    assert sat("a1", C0) and sat("a2", C0)

    # Exact down-spectrum gate repeats, not merely model-type repeats.
    assert key("a1") == key("v1") == key("v1b")
    assert key("a2") == key("v2")
    expected_a1 = ["v1", "v1b"] if shared else ["v1"]
    assert groups == {"a1": expected_a1, "a2": ["v2"]}
    expected_blocked = {"v1", "v1b", "v2"} if shared else {"v1", "v2"}
    assert set(blocked) == expected_blocked

    # The PP demand is edge-served: its persistence guard fails at both mates.
    guard = ("all", PP, D)
    assert not sat("a1", guard)
    assert not sat("a2", guard)

    # Agreement is unavailable group-wise; the ordered fallback is forced to
    # the displayed first candidate.
    assert agreeing_candidates("a1", groups["a1"]) == []
    assert agreeing_candidates("a2", groups["a2"]) == []
    assert fallback_first("a1") == "z1"
    assert fallback_first("a2") == "z2"
    chosen = {"a1": "z1", "a2": "z2"}

    borrowed = []
    for a, vs in groups.items():
        z = chosen[a]
        for v in vs:
            # Per-edge safety, in its strongest relevant form: the pair is PO.
            assert rel(R[z], R[v]) != PP  # target is not below borrower
            assert rel(R[v], R[z]) == PO
            borrowed.append((v, z))

    pp_edges = [
        (x, y) for x, y in product(nodes, repeat=2)
        if rel(R[x], R[y]) == PP
    ]
    reach = transitive_closure(nodes, pp_edges + borrowed)

    # Two explicit alternating cycles; the first group's target is shared.
    cycle_1 = [("v1", "z1"), ("z1", "v2"),
               ("v2", "z2"), ("z2", "v1")]
    assert all(e in pp_edges + borrowed for e in cycle_1)
    expected_cyclic = {"v1", "v2", "z1", "z2"}
    if shared:
        cycle_2 = [("v1b", "z1"), ("z1", "v2"),
                   ("v2", "z2"), ("z2", "v1b")]
        assert all(e in pp_edges + borrowed for e in cycle_2)
        expected_cyclic.add("v1b")
    cyclic = sorted(x for x in nodes if reach[x, x])
    assert set(cyclic) == expected_cyclic

    return blocked, groups, chosen, borrowed, cyclic


def main():
    assert phase1_core_from_duplicate_free_seed() == CORE
    core = run_case(CORE, shared=False)
    shared = run_case(SHARED, shared=True)
    blocked, groups, chosen, borrowed, cyclic = shared

    print("PASS: finite D1 counterexample verified")
    print(f"  source-model points       : {len(MODEL_ORDER)}")
    print(f"  core external nodes       : {len(CORE)}")
    print(f"  core cyclic nodes         : {core[-1]}")
    print(f"  shared-target externals   : {len(SHARED)}")
    print(f"  blocked nodes             : {blocked}")
    print(f"  borrowed groups           : {groups}")
    print(f"  agreeing candidates       : a1=[], a2=[]")
    print(f"  fallback targets          : {chosen}")
    print(f"  borrowed edges            : {borrowed}")
    print(f"  cyclic closure nodes      : {cyclic}")
    print("  cycle                     : v1 -b-> z1 -PP-> v2 -b-> z2 -PP-> v1")
    print("  shared-target cycle       : v1b -b-> z1 -PP-> v2 -b-> z2 -PP-> v1b")
    print("VERDICT: per-edge safety does not imply global irreflexivity.")


if __name__ == "__main__":
    main()
