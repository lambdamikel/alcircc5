#!/usr/bin/env python3
"""WP117 -- do KERNEL PHASES cover the leaves the closure misses?

ASSEMBLY_DESIGN sec.131.4.  Step 2 died because expanding cut leaves spawns
rounds that grow with the model.  The remaining branches are (a) a kernel at the
leaf and (b) an existing set member -- but (b) is false by definition on an
UNSERVED demand, and wp112 measured (a) at only 33-56% for prefix leaves.

What neither measured: a kernel contributes its PHASES to the certificate as
servers, and a leaf may be served by SOMEONE ELSE'S kernel.  In the tower class
the kernel phases are exactly the tail residues, and every tail residue is above
every prefix node, so the question is sharp:

    for an unserved exists-PP.D at a prefix cut leaf,
    does SOME TAIL RESIDUE satisfy D?

If yes the demand is served by a kernel phase, no new node, no round.

CONTROL, stated before the run: for TAIL cut leaves the answer must be 100%.
A tail leaf's own demand exists-PP.D has a witness above it, everything above a
tail node is a tail residue, so some residue carries D by construction.  A tail
figure below 100% means the instrument is wrong and the prefix figure is
withheld (sec.117.3).

MEASUREMENT: the prefix figure, and whether it MOVES with tower shape.

The tower is imported from wp112 so the probes cannot drift apart.
"""

import random

from wp112_lap_continuation_closed_form import (
    PP, PPI, build, mdepth, persistent, po_free, rand_c)
from wp116_target_rounds import close_from, unserved, vdemands


def served_by_phase(T, c0, v, r, D):
    """Is the demand served by a KERNEL PHASE -- i.e. by a tail residue that is
    an r-successor of v and carries D?"""
    return any(w in T.succs(v, r) and T.sat(w, D) for w in T.tail)


def blocker_of(T, c0, v, cuts_paths):
    """The path ancestor sharing v's type."""
    return cuts_paths.get(v)


def served_by_edge(T, c0, v, blk, r, D, nodes):
    """sec.123's declared edge under sec.124.2's two-clause condition:
    the blocker's witness, neither an ancestor of v nor disjoint from it."""
    if blk is None:
        return False
    for w in T.succs(blk, r):
        if not T.sat(w, D):
            continue
        # not an ancestor of v: v must not be an r-successor-reachable... in the
        # tower the order is explicit, so test directly
        if v in T.succs(w, r):
            continue                       # w is on v's side -> would cycle
        if w in T.succs(v, "DR") or v in T.succs(w, "DR"):
            continue                       # disjoint -> would break ltNotDj
        return True
    return False


def sweep(seed, trials, L, p):
    rng = random.Random(seed)
    st = {"P": [0, 0], "R": [0, 0], "S": [0, 0]}
    models = 0
    for _ in range(trials):
        c0 = rand_c(rng, rng.randint(2, 4))
        if not po_free(c0):
            continue
        T = build(rng, L=L, p=p)
        root = next((n for n in T.nodes if T.sat(n, c0)), None)
        if root is None:
            continue
        models += 1
        nodes, cuts = close_from(T, c0, root)
        # blocker = any node of the same type already in the set
        blkmap = {}
        for v in cuts:
            tv = T.mty(c0, v)
            blkmap[v] = next((z for z in nodes
                              if z != v and T.mty(c0, z) == tv), None)
        for v in cuts:
            for (r, D) in unserved(T, c0, nodes, v):
                st[v[0]][0] += 1
                if (served_by_phase(T, c0, v, r, D)
                        or served_by_edge(T, c0, v, blkmap[v], r, D, nodes)):
                    st[v[0]][1] += 1
    return models, st


def report(label, res):
    models, st = res
    print(f"  {label}: models {models}")
    names = {"R": "tail   (CONTROL, must be 100%)", "P": "prefix (MEASUREMENT)",
             "S": "side"}
    ok = True
    for k in ("R", "P", "S"):
        n, y = st[k]
        if n:
            pct = 100.0 * y / n
            print(f"    {names[k]:32s} {n:5d} unserved, phase-served {y:5d}"
                  f" ({pct:5.1f}%)")
            if k == "R" and pct < 99.9:
                ok = False
        else:
            print(f"    {names[k]:32s}     0 unserved")
    return ok, st


def main():
    print("WP117 -- UNION coverage: kernel phases OR the declared edge\n")
    res = []
    for lbl, seed, L, p in (("L=4   p=3", 20260826, 4, 3),
                            ("L=8   p=3", 777, 8, 3),
                            ("L=18  p=3", 31337, 18, 3),
                            ("L=8   p=6", 5150, 8, 6),
                            ("L=26  p=2", 8675309, 26, 2)):
        ok, st = report(lbl, sweep(seed, 1200, L, p))
        res.append((lbl, ok, st))
        print()
    print("=" * 72)
    if not all(ok for _, ok, _ in res):
        print("  CONTROL MISSED -- instrument wrong, prefix figures WITHHELD.")
        return 1
    pn = sum(st["P"][0] for _, _, st in res)
    py = sum(st["P"][1] for _, _, st in res)
    rates = [100.0 * st["P"][1] / st["P"][0] for _, _, st in res if st["P"][0]]
    print("  CONTROL HELD (tail 100%).  Prefix coverage, phases OR edge:")
    for lbl, _, st in res:
        n, y = st["P"]
        if n:
            print(f"    {lbl} : {y}/{n} = {100.0*y/n:5.1f}%")
    print(f"    pooled : {py}/{pn} = {100.0*py/max(pn,1):.1f}%")
    print()
    if rates and min(rates) > 99.9:
        print("  100% everywhere -> the two together cover the residue with no")
        print("  new node and no round: sec.131.4's redesign has its answer.")
    else:
        print(f"  {min(rates):.1f}%..{max(rates):.1f}% -> still not covered;")
        print("  the remainder needs a treatment none of the three supplies.")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
