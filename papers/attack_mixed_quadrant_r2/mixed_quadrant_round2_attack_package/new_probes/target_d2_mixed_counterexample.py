#!/usr/bin/env python3
"""Five-point mixed-quadrant counterexample to Target D2.

The source model is induced by ordinary nonempty sets.  Starting phase 1 at
`a`, its DR.Q witness is `v`, its PP.P witness is `za`, and its PO.R witness is
`p`.  Thus C0 genuinely lies in the mixed (exists-PO plus exists-PP) quadrant.
The refined down-spectrum gate blocks `v` at `a`, but `za` is DR from `v`.
Moreover `za` is the only PP.P witness of `a`, so no alternative gate-mate
witness avoids both the ancestor and disjointness obstructions.

This probe is deterministic and exhaustive over all points/pairs/triples of
the displayed finite model.
"""

from itertools import combinations


DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
CONV = {DR: DR, PO: PO, EQ: EQ, PP: PPI, PPI: PP}

# The order is intentional: the deterministic witness selector encounters v
# before any other DR.Q witness, and za is the unique PP.P witness of a.
POINTS = ("a", "v", "za", "zv", "p")
REGION = {
    "a": frozenset({0, 1}),
    "v": frozenset({2, 3}),
    "za": frozenset({0, 1, 4}),
    "zv": frozenset({2, 3, 5}),
    "p": frozenset({0, 2}),
}
VAL = {
    "a": frozenset({"Q"}),
    "v": frozenset({"Q"}),
    "za": frozenset({"P"}),
    "zv": frozenset({"P"}),
    "p": frozenset({"R"}),
}


def rho(x, y):
    sx, sy = REGION[x], REGION[y]
    if sx == sy:
        return EQ
    if sx < sy:
        return PP
    if sy < sx:
        return PPI
    return DR if sx.isdisjoint(sy) else PO


def all_nonempty_subsets(n):
    return [frozenset(c) for k in range(1, n + 1)
            for c in combinations(range(n), k)]


def composition_table(n=4):
    regs = all_nonempty_subsets(n)
    table = {}
    for x in regs:
        for y in regs:
            rxy = relation_of_sets(x, y)
            for z in regs:
                table.setdefault((rxy, relation_of_sets(y, z)), set()).add(
                    relation_of_sets(x, z)
                )
    return table


def relation_of_sets(x, y):
    if x == y:
        return EQ
    if x < y:
        return PP
    if y < x:
        return PPI
    return DR if x.isdisjoint(y) else PO


# Concepts: C0 = (exists DR.Q) and (exists PP.P) and (exists PO.R).
Q = ("at", "Q")
P = ("at", "P")
R = ("at", "R")
EX_DR_Q = ("ex", DR, Q)
EX_PP_P = ("ex", PP, P)
EX_PO_R = ("ex", PO, R)
C0 = ("and", ("and", EX_DR_Q, EX_PP_P), EX_PO_R)
# `persistDs` uses this derived guard.  It is false at a and v, so PP.P is an
# edge-served demand and cannot disappear into the kernel route.
PP_PERSIST_GUARD = ("all", PP, EX_PP_P)


def sat(x, concept):
    tag = concept[0]
    if tag == "at":
        return concept[1] in VAL[x]
    if tag == "nat":
        return concept[1] not in VAL[x]
    if tag == "and":
        return sat(x, concept[1]) and sat(x, concept[2])
    if tag == "or":
        return sat(x, concept[1]) or sat(x, concept[2])
    if tag == "ex":
        return any(rho(x, y) == concept[1] and sat(y, concept[2])
                   for y in POINTS)
    if tag == "all":
        return all(rho(x, y) != concept[1] or sat(y, concept[2])
                   for y in POINTS)
    raise ValueError(concept)


def closure(concept, out=None):
    out = [] if out is None else out
    if concept not in out:
        out.append(concept)
    if concept[0] in {"and", "or"}:
        closure(concept[1], out)
        closure(concept[2], out)
    elif concept[0] in {"ex", "all"}:
        closure(concept[2], out)
    return out


CL = tuple(closure(C0))


def mty(x):
    # The construction's full closure type.  Equality below also follows from
    # the model automorphism a<->v, za<->zv, so it is not representation-sensitive.
    return tuple(c for c in CL if sat(x, c))


def down_spectrum(x):
    return frozenset(mty(y) for y in POINTS if rho(y, x) == PP)


def dkey(x):
    return mty(x), down_spectrum(x)


def po_free(concept):
    tag = concept[0]
    if tag in {"at", "nat"}:
        return True
    if tag in {"and", "or"}:
        return po_free(concept[1]) and po_free(concept[2])
    if tag == "all" and concept[1] == PO:
        return False
    return po_free(concept[2])


def witness(x, relation, body):
    return next((y for y in POINTS
                 if rho(x, y) == relation and sat(y, body)), None)


def gate(nodes):
    seen, kept = set(), []
    for x in nodes:
        k = dkey(x)
        if k not in seen:
            seen.add(k)
            kept.append(x)
    return kept


def phase1(max_rounds=20):
    nodes = ["a"]
    children = {}
    for _ in range(max_rounds):
        new = []
        for x in gate(nodes):
            for demand in mty(x):
                if demand[0] != "ex":
                    continue
                if demand[1] == PP:
                    guard = ("all", PP, ("ex", PP, demand[2]))
                    if sat(x, guard):
                        continue  # persistent PP demand: kernel-served
                y = witness(x, demand[1], demand[2])
                assert y is not None
                children.setdefault((x, demand), y)
                if y not in nodes and y not in new:
                    new.append(y)
        if not new:
            return nodes, children, gate(nodes)
        nodes.extend(new)
    raise AssertionError("phase 1 did not reach a fixed point")


def check_rcc5_model():
    ct = composition_table(6)
    for x in POINTS:
        for y in POINTS:
            assert rho(y, x) == CONV[rho(x, y)]
            for z in POINTS:
                assert rho(x, z) in ct[(rho(x, y), rho(y, z))]


def check_ordered_disjoint_reduct():
    lt = {(x, y) for x in POINTS for y in POINTS if rho(x, y) == PP}
    dj = {(x, y) for x in POINTS for y in POINTS if rho(x, y) == DR}
    assert all((x, x) not in lt for x in POINTS)
    assert all(not ((x, y) in lt and (y, x) in lt) for x in POINTS for y in POINTS)
    assert all((x, z) in lt
               for x in POINTS for y in POINTS for z in POINTS
               if (x, y) in lt and (y, z) in lt)
    assert all(((x, y) in dj) == ((y, x) in dj)
               for x in POINTS for y in POINTS)
    assert all((x, x) not in dj for x in POINTS)
    assert all((x, z) in dj
               for x in POINTS for y in POINTS for z in POINTS
               if (x, y) in lt and (y, z) in dj)
    assert lt.isdisjoint(dj)


def main():
    check_rcc5_model()
    check_ordered_disjoint_reduct()

    assert po_free(C0)
    assert sat("a", C0) and sat("v", C0)
    assert not sat("a", PP_PERSIST_GUARD)
    assert not sat("v", PP_PERSIST_GUARD)
    assert mty("a") == mty("v")
    assert down_spectrum("a") == down_spectrum("v") == frozenset()
    assert dkey("a") == dkey("v")

    nodes, children, gated = phase1()
    assert nodes == ["a", "v", "za", "p"]
    assert gated == ["a", "za", "p"]
    assert children[("a", EX_DR_Q)] == "v"
    assert children[("a", EX_PP_P)] == "za"
    assert children[("a", EX_PO_R)] == "p"
    assert "v" not in gated                       # actual blocked occurrence
    assert rho("v", "zv") == PP and sat("zv", P)  # v's source-model witness

    candidates = [z for z in POINTS
                  if rho("a", z) == PP and sat(z, P)]
    safe = [z for z in candidates
            if rho(z, "v") != PP and rho("v", z) != DR]
    assert candidates == ["za"]
    assert safe == []
    assert rho("v", "za") == rho("za", "v") == DR

    # The construction declares v < za although its inherited disjointness
    # relation contains (v,za), directly falsifying lt -> not disj.
    declared_lt = {(x, y) for x in nodes for y in nodes if rho(x, y) == PP}
    declared_lt.add(("v", "za"))
    inherited_disj = {(x, y) for x in nodes for y in nodes if rho(x, y) == DR}
    violations = sorted(declared_lt & inherited_disj)
    assert violations == [("v", "za")]

    print("MODEL")
    for x in POINTS:
        print(f"  {x:2s} = {sorted(REGION[x])}, atoms={sorted(VAL[x])}")
    print("C0 = (exists DR.Q) and (exists PP.P) and (exists PO.R)")
    print(f"forall-PO-free: {po_free(C0)}; C0(a): {sat('a', C0)}")
    print(f"mty(a) = mty(v): {mty('a') == mty('v')}")
    print(f"down spectra: a={down_spectrum('a')}, v={down_spectrum('v')}")
    print(f"phase-1 fixed-point nodes: {nodes}; refined gate: {gated}")
    print(f"v blocked at gate-mate a: {'v' not in gated}")
    print(f"a's PP.P candidates: {candidates}; safe candidates: {safe}")
    print(f"declared-lt/inherited-disj conflict: {violations}")
    print("VERDICT: D2 IS FALSE (all exhaustive checks pass).")


if __name__ == "__main__":
    main()
