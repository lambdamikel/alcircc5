#!/usr/bin/env python3
"""
Round-15 W1a counterexample: pointwise safe-horizontal steering is not
jointly closed.

This is a finite check of the old-detour case in Lemma 4.3 of
cluster_quasimodels_round15.tex.  The networks are closed atomic RCC5
networks.  The fold condition Q4 is satisfied pointwise for the two
old-to-fresh pairs.  The canonical/safe horizontal choices required by
Lemma 4.3 are nevertheless incompatible with the already realized old
edge y PP z.
"""

from itertools import combinations

BASE = ("EQ", "PP", "PPI", "PO", "DR")
NONEQ = ("PP", "PPI", "PO", "DR")
CONV = {"EQ": "EQ", "PP": "PPI", "PPI": "PP", "PO": "PO", "DR": "DR"}


def derive_comp(n=5):
    universe = range(n)
    regions = [frozenset(c) for k in range(1, n + 1) for c in combinations(universe, k)]

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
    for a in regions:
        for b in regions:
            rab = rel(a, b)
            for c in regions:
                table[(rab, rel(b, c))].add(rel(a, c))
    return {k: frozenset(v) for k, v in table.items()}


COMP = derive_comp()


def comp_set(A, B):
    return frozenset(x for a in A for b in B for x in COMP[(a, b)])


def selector(F):
    G = set(F) - {"EQ"}
    if len(G) == 1:
        return next(iter(G))
    if "DR" in G:
        return "DR"
    if "PO" in G:
        return "PO"
    raise ValueError("selector undefined on %r" % (F,))


def choose(F, safe):
    """The round-15 pointwise choice rule: forced singleton if forced;
    otherwise choose selector if safe, else the other horizontal member."""
    G = set(F) - {"EQ"}
    if len(G) == 1:
        v = next(iter(G))
        return v if v in safe else None
    sel = selector(F)
    if sel in safe:
        return sel
    for h in ("DR", "PO"):
        if h != sel and h in F and h in safe:
            return h
    return None


def close_atomic(net, vertices):
    for x in vertices:
        for y in vertices:
            if x == y:
                continue
            if (x, y) not in net:
                return False, "missing edge %s,%s" % (x, y)
            if net[(y, x)] != CONV[net[(x, y)]]:
                return False, "bad converse %s,%s" % (x, y)
    for x in vertices:
        for y in vertices:
            if x == y:
                continue
            for z in vertices:
                if z in (x, y):
                    continue
                if net[(x, z)] not in COMP[(net[(x, y)], net[(y, z)])]:
                    return False, "%s-%s-%s violates %s not in %s o %s" % (
                        x, y, z, net[(x, z)], net[(x, y)], net[(y, z)]
                    )
    return True, "closed"


def add_edge(net, x, y, r):
    net[(x, y)] = r
    net[(y, x)] = CONV[r]


# A syntactic safe-link witness.  A type is represented by the set of atoms
# it contains and by universal formulas U(role, atom).  This implements the
# manuscript's Definition 3.1 exactly: L1 plus PP/PPI vertical propagation.

def U(role, atom):
    return ("forall", role, atom)


def safe(t, s):
    out = set()
    for R in NONEQ:
        ok = True
        # L1 forward
        for f in t:
            if isinstance(f, tuple) and f[0] == "forall" and f[1] == R:
                if f[2] not in s:
                    ok = False
                    break
        if not ok:
            continue
        # L1 inverse
        inv = CONV[R]
        for f in s:
            if isinstance(f, tuple) and f[0] == "forall" and f[1] == inv:
                if f[2] not in t:
                    ok = False
                    break
        if not ok:
            continue
        # L2 vertical propagation, as stated in round 15.
        if R == "PP":
            for f in t:
                if isinstance(f, tuple) and f[0] == "forall" and f[1] == "PP":
                    if f not in s:
                        ok = False
                        break
        elif R == "PPI":
            for f in s:
                if isinstance(f, tuple) and f[0] == "forall" and f[1] == "PPI":
                    if f not in t:
                        ok = False
                        break
        if ok:
            out.add(R)
    return frozenset(out)


# Guards for Y and Z.  B is deliberately made a PO-only safe target from Y
# and a DR-only safe target from Z.
Y = {
    "py", "qy", "ry", "ty", "tz", "qz", "pz", "rz",
    U("DR", "qy"), U("PO", "py"), U("PP", "ry"), U("PPI", "ty"),
    # included so Y is a legal PP-predecessor of Z even when Z has this inverse universal
    U("PPI", "tz"),
}
Z = {
    "py", "qy", "ry", "ty", "tz", "qz", "pz", "rz",
    U("DR", "qz"), U("PO", "pz"), U("PP", "rz"), U("PPI", "tz"),
    # inherited from the Y -> Z PP edge by L2
    U("PP", "ry"),
}
S = {
    "ry", "rz",
    U("PP", "ry"), U("PP", "rz"),
}
B = {
    "py",  # makes Y --PO--> B safe
    "qz",  # makes Z --DR--> B safe
    # B omits qy, ry, ty, pz, rz, tz; hence all other Y/Z-to-B roles are unsafe.
}


def main():
    print("RCC5 cells used:")
    print("  PP o PPI =", sorted(COMP[("PP", "PPI")]))
    print("  PP o DR  =", sorted(COMP[("PP", "DR")]))
    print()

    old = {}
    add_edge(old, "y", "z", "PP")
    add_edge(old, "z", "s", "PP")
    add_edge(old, "y", "s", "PP")
    fresh = {}
    add_edge(fresh, "s", "b", "PPI")

    ok_old, msg_old = close_atomic(old, ("y", "z", "s"))
    ok_fresh, msg_fresh = close_atomic(fresh, ("s", "b"))
    print("old pattern O(y,z,s):", msg_old)
    print("fresh pattern K(s,b):", msg_fresh)
    assert ok_old and ok_fresh

    print("pattern-edge safety:")
    print("  Safe(Y,Z) contains PP:", "PP" in safe(Y, Z), sorted(safe(Y, Z)))
    print("  Safe(Z,S) contains PP:", "PP" in safe(Z, S), sorted(safe(Z, S)))
    print("  Safe(Y,S) contains PP:", "PP" in safe(Y, S), sorted(safe(Y, S)))
    print("  Safe(S,B) contains PPI:", "PPI" in safe(S, B), sorted(safe(S, B)))
    assert "PP" in safe(Y, Z)
    assert "PP" in safe(Z, S)
    assert "PP" in safe(Y, S)
    assert "PPI" in safe(S, B)

    F_yb = comp_set({"PP"}, {"PPI"})
    F_zb = comp_set({"PP"}, {"PPI"})
    syb = safe(Y, B)
    szb = safe(Z, B)
    print()
    print("cross folds through separator s:")
    print("  F(y,b)=PP o PPI =", sorted(F_yb), "selector", selector(F_yb), "Safe(Y,B)=", sorted(syb))
    print("  F(z,b)=PP o PPI =", sorted(F_zb), "selector", selector(F_zb), "Safe(Z,B)=", sorted(szb))
    assert F_yb == frozenset(BASE)
    assert F_zb == frozenset(BASE)
    assert syb == frozenset({"PO"})
    assert szb == frozenset({"DR"})

    v_yb = choose(F_yb, syb)
    v_zb = choose(F_zb, szb)
    print()
    print("round-15 pointwise choices:")
    print("  rho(y,b) =", v_yb)
    print("  rho(z,b) =", v_zb)
    assert v_yb == "PO"
    assert v_zb == "DR"

    needed = COMP[("PP", v_zb)]
    print()
    print("old-detour triangle y --PP--> z --%s--> b requires rho(y,b) in %s" % (v_zb, sorted(needed)))
    print("  actual chosen rho(y,b) =", v_yb)
    violated = v_yb not in needed
    print("  CLOSED?", not violated)
    assert violated

    print()
    print("RESULT: PASS - this is a W1a counterexample to Lemma 4.3's pointwise canonical completion.")


if __name__ == "__main__":
    main()
