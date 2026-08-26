#!/usr/bin/env python3
"""WP120 candidate -- full model types versus demand-supported labels.

A fixed PO-free concept is evaluated on an arbitrarily long RCC5 fence

    X0 < Y0 > X1 < Y1 > X2 < ... < Y(L-1) > XL.

All incomparable regions overlap.  The model is represented by finite sets, so
RCC5 relations are derived rather than stipulated.

The fixed concept requires only exists-PP.B0 at X0.  A disjunct that is NOT
chosen nevertheless places four further existential formulas in cl(C0).  Full
model types import whichever of those formulas happen to be true at every
selected point and therefore walk the entire fence.  A demand-supported
Hintikka label chooses the true root disjunct and labels the witness only with
B0; it uses two nodes for every L.

This is not a MultiTierOk checker.  It isolates the construction invariant
"tauE(e) = full mty(e)" and shows that it can create model-length residue even
when every selected carrier is extremal and no infinite chain exists.
"""

from collections import deque

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"


def rel(a, b):
    if a == b:
        return EQ
    if a < b:
        return PP
    if b < a:
        return PPI
    if not (a & b):
        return DR
    return PO


def closure(c, out=None):
    if out is None:
        out = []
    if c not in out:
        out.append(c)
    if c[0] in ("and", "or"):
        closure(c[1], out)
        closure(c[2], out)
    elif c[0] in ("ex", "all"):
        closure(c[2], out)
    return out


def sat(nodes, val, x, c):
    k = c[0]
    if k == "at":
        return val.get((c[1], x), False)
    if k == "nat":
        return not val.get((c[1], x), False)
    if k == "and":
        return sat(nodes, val, x, c[1]) and sat(nodes, val, x, c[2])
    if k == "or":
        return sat(nodes, val, x, c[1]) or sat(nodes, val, x, c[2])
    if k == "ex":
        return any(rel(x, y) == c[1] and sat(nodes, val, y, c[2])
                   for y in nodes)
    return all(rel(x, y) != c[1] or sat(nodes, val, y, c[2])
               for y in nodes)


def make_fence(L):
    common = "c"
    X = [frozenset((common, f"x{i}")) for i in range(L + 1)]
    Y = [frozenset((common, f"x{i}", f"x{i+1}", f"y{i}"))
         for i in range(L)]
    nodes = X + Y

    # Atom numbers: R=0, A0=1, A1=2, B0=3, B1=4.
    val = {}
    val[(0, X[0])] = True
    for i, x in enumerate(X):
        val[((1 if i % 2 == 0 else 2), x)] = True
    for i, y in enumerate(Y):
        val[((3 if i % 2 == 0 else 4), y)] = True
    return nodes, X, Y, val


R = ("at", 0)
A0, A1 = ("at", 1), ("at", 2)
B0, B1 = ("at", 3), ("at", 4)
F0, F1 = ("ex", PP, B0), ("ex", PP, B1)
G0, G1 = ("ex", PPI, A1), ("ex", PPI, A0)
JUNK = ("and", F1, ("and", G0, G1))
C0 = ("and", F0, ("or", R, JUNK))



def model_type(nodes, val, x):
    return frozenset(f for f in closure(C0) if sat(nodes, val, x, f))


def full_demands(nodes, val, x):
    return sorted([(f[1], f[2]) for f in model_type(nodes, val, x)
                   if f[0] == "ex" and f[1] in (PP, PPI)], key=str)


def cut_closure(nodes, val, root):
    selected = {root}
    cuts = []
    stack = [(root, frozenset((model_type(nodes, val, root),)))]
    while stack:
        x, seen = stack.pop()
        for r, D in full_demands(nodes, val, x):
            y = next(y for y in nodes if rel(x, y) == r
                     and sat(nodes, val, y, D))
            selected.add(y)
            ty = model_type(nodes, val, y)
            if ty in seen:
                cuts.append(y)
            else:
                stack.append((y, seen | {ty}))
    return selected, cuts


def unserved_full(nodes, val, selected, x):
    return [(r, D) for r, D in full_demands(nodes, val, x)
            if not any(y in selected and rel(x, y) == r
                       and sat(nodes, val, y, D) for y in nodes)]


def target_rounds(nodes, val, root, max_rounds=200):
    selected = set()
    frontier = [root]
    for rnd in range(max_rounds):
        cuts = []
        for start in frontier:
            new, cut = cut_closure(nodes, val, start)
            selected |= new
            cuts.extend(cut)
        leaves = [x for x in cuts if unserved_full(nodes, val, selected, x)]
        if not leaves:
            return rnd + 1, len(selected), False
        targets = set()
        for x in leaves:
            for r, D in unserved_full(nodes, val, selected, x):
                y = next(y for y in nodes if y not in selected
                         and rel(x, y) == r and sat(nodes, val, y, D))
                targets.add(y)
        frontier = sorted(targets, key=lambda z: (len(z), sorted(z)))
    return max_rounds, len(selected), True

def full_type_closure(nodes, val, root):
    cl = closure(C0)
    lab = lambda x: [f for f in cl if sat(nodes, val, x, f)]
    selected = {root}
    queue = deque([root])
    done = set()
    while queue:
        x = queue.popleft()
        if x in done:
            continue
        done.add(x)
        for f in lab(x):
            if f[0] != "ex" or f[1] not in (PP, PPI):
                continue
            # One witness per true existential, preferring an already selected
            # witness but adding a new one when the demand requires it.
            ws = [y for y in nodes if rel(x, y) == f[1]
                  and sat(nodes, val, y, f[2])]
            old = next((y for y in ws if y in selected), None)
            y = old if old is not None else ws[0]
            if y not in selected:
                selected.add(y)
                queue.append(y)
    return selected


def add_supported(nodes, val, labels, x, f):
    """Least Boolean support needed for f at x.  This example has no labelled
    universals, so the universal cross-node rule is vacuous."""
    if f in labels.setdefault(x, set()):
        return
    assert sat(nodes, val, x, f)
    labels[x].add(f)
    if f[0] == "and":
        add_supported(nodes, val, labels, x, f[1])
        add_supported(nodes, val, labels, x, f[2])
    elif f[0] == "or":
        pick = f[1] if sat(nodes, val, x, f[1]) else f[2]
        add_supported(nodes, val, labels, x, pick)


def support_closure(nodes, val, root):
    labels = {}
    add_supported(nodes, val, labels, root, C0)
    changed = True
    while changed:
        changed = False
        for x, fs in list(labels.items()):
            for f in list(fs):
                if f[0] != "ex" or f[1] not in (PP, PPI):
                    continue
                if any(rel(x, y) == f[1] and f[2] in labels.get(y, set())
                       for y in labels):
                    continue
                y = next(y for y in nodes if rel(x, y) == f[1]
                         and sat(nodes, val, y, f[2]))
                before = len(labels)
                add_supported(nodes, val, labels, y, f[2])
                changed = changed or len(labels) != before
    return labels


def controls(nodes, X, Y):
    # Expected fence order; every other distinct pair must be PO.
    for i, y in enumerate(Y):
        assert rel(X[i], y) == PP
        assert rel(X[i + 1], y) == PP
    for a in nodes:
        for b in nodes:
            if a == b:
                assert rel(a, b) == EQ
            elif rel(a, b) not in (PP, PPI):
                assert rel(a, b) == PO


def main():
    print("WP120 candidate -- support labels on an alternating fence\n")
    print("  fixed C0 = exists-PP.B0 AND (R OR junk)")
    print("  R is true at the root; junk is not selected, but its existential")
    print("  subformulas still enter every FULL model type when locally true.\n")
    print("    L    model nodes    target rounds    full-mty nodes    support nodes")
    for L in (4, 8, 12, 18, 26, 40):
        nodes, X, Y, val = make_fence(L)
        controls(nodes, X, Y)
        assert sat(nodes, val, X[0], C0)
        rounds, round_nodes, cap = target_rounds(nodes, val, X[0])
        assert not cap
        full = full_type_closure(nodes, val, X[0])
        thin = support_closure(nodes, val, X[0])
        assert round_nodes == len(full)
        print(f"   {L:2d}       {len(nodes):3d}             {rounds:3d}"
              f"              {len(full):3d}             {len(thin):3d}")
    print("\n" + "=" * 76)
    print("  The growth is caused by full-type overlabelling, not by C0.")
    print("  A thin witness remains a real, distinct external and serves its parent,")
    print("  but it owes only formulas in its supported Hintikka label.")
    print("=" * 76)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
