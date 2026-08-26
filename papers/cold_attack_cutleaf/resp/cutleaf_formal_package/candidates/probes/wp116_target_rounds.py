#!/usr/bin/env python3
"""WP116 -- are the TARGET ROUNDS bounded?  (ASSEMBLY_DESIGN sec.130, step 2.)

The plan's only open step.  `cutNodesR` adds and expands each cut leaf's
blocker-witness; that target is itself expanded and may produce cut leaves of its
own, generating another ROUND.  Termination needs the round count bounded by
something computed from C0 alone.

Probed BEFORE the Lean, per the standing rule, and over wp112's CLOSED-FORM
eventually periodic tower -- the class where laps genuinely continue, which is
where unbounded rounds would live.  Finite set models cannot exhibit them
(wp110's blind spot), so measuring there would be worthless.

CONTROL, stated before the run: with target expansion disabled there must be cut
leaves carrying unserved demands.  If that count is 0 the measurement is vacuous
-- there is nothing to expand -- and the round numbers mean nothing.

MEASUREMENT: rounds until no new target is generated, and whether the maximum
MOVES when the tower's shape (prefix length L, period p) changes.  A maximum that
grows with L or p is a property of the model, and step 2 fails as stated.

The tower class is imported from wp112 rather than re-derived, so the two probes
cannot drift apart.
"""

import random

from wp112_lap_continuation_closed_form import (
    PP, PPI, Tower, build, closure, mdepth, persistent, po_free, rand_c)


def lab(T, c0, n):
    b = mdepth(c0) + 1
    return [d for d in T.mty(c0, n) if mdepth(d) <= b]


def vdemands(T, c0, n):
    """Non-persistent vertical demands at n."""
    return [(d[1], d[2]) for d in lab(T, c0, n)
            if d[0] == "ex" and d[1] in (PP, PPI)
            and not persistent(T, c0, n, d[2], d[1])]


def close_from(T, c0, root, cap=400):
    """One cutNodes closure: expand a witness unless its type is on the path.
    Returns (nodes touched, cut leaves)."""
    nodes = {root}
    cuts = []
    stack = [(root, frozenset({T.mty(c0, root)}))]
    steps = 0
    while stack and steps < cap:
        steps += 1
        x, seen = stack.pop()
        for (r, D) in vdemands(T, c0, x):
            for y in T.succs(x, r):
                if T.sat(y, D):
                    nodes.add(y)
                    ty = T.mty(c0, y)
                    if ty in seen:
                        cuts.append(y)
                    else:
                        stack.append((y, seen | {ty}))
                    break
    return nodes, cuts


def unserved(T, c0, nodes, v):
    return [(r, D) for (r, D) in vdemands(T, c0, v)
            if not any(w in T.succs(v, r) and T.sat(w, D) for w in nodes)]


def rounds_to_close(T, c0, root, maxround=15):
    """Repeat: close, then expand every unserved cut leaf's witness.
    Returns (rounds used, unserved leaves seen in round 0, hit_max)."""
    nodes = set()
    frontier = [root]
    r0 = 0
    for rnd in range(maxround):
        cuts = []
        for st in frontier:
            n2, c2 = close_from(T, c0, st)
            nodes |= n2
            cuts.extend(c2)
        leaves = [v for v in cuts if unserved(T, c0, nodes, v)]
        if rnd == 0:
            r0 = len(leaves)
        if not leaves:
            return rnd + 1, r0, False
        tg = set()
        for v in leaves:
            for (r, D) in unserved(T, c0, nodes, v):
                for w in T.succs(v, r):
                    if T.sat(w, D) and w not in nodes:
                        tg.add(w)
                        break
        if not tg:
            return rnd + 1, r0, False
        frontier = sorted(tg, key=str)
    return maxround, r0, True


def sweep(seed, trials, L, p):
    rng = random.Random(seed)
    models = maxr = ctl = hitmax = 0
    hist = {}
    for _ in range(trials):
        c0 = rand_c(rng, rng.randint(2, 4))
        if not po_free(c0):
            continue
        T = build(rng, L=L, p=p)
        root = next((n for n in T.nodes if T.sat(n, c0)), None)
        if root is None:
            continue
        models += 1
        r, r0, hm = rounds_to_close(T, c0, root)
        ctl += 1 if r0 > 0 else 0
        hitmax += 1 if hm else 0
        maxr = max(maxr, r)
        hist[r] = hist.get(r, 0) + 1
    return models, maxr, ctl, hitmax, hist


def report(label, res):
    models, maxr, ctl, hitmax, hist = res
    print(f"  {label}: models {models}")
    print(f"    CONTROL  models with an unserved cut leaf in round 0 : {ctl}"
          f"    <- must be > 0")
    print(f"    hit the round ceiling ({15})                            : {hitmax}"
          f"    <- >0 means rounds exceed the ceiling here")
    print(f"    MAX ROUNDS to close : {maxr}")
    print(f"    distribution        : "
          + ", ".join(f"{k}:{hist[k]}" for k in sorted(hist)))
    return ctl > 0, maxr, hitmax


def main():
    print("WP116 -- target rounds over the closed-form tower\n")
    res = []
    # Rounds tracked L, not p, in the first run.  Does that GROW with L or
    # SATURATE?  Growth means the round count is a model parameter and step 2
    # fails; saturation means a C0-computable bound is plausible, since the
    # prefix's TYPES are drawn from typeEnum C0 however long the prefix is.
    for lbl, seed, L, p in (("L=4   p=3", 20260826, 4, 3),
                            ("L=8   p=3", 777, 8, 3),
                            ("L=12  p=3", 31337, 12, 3),
                            ("L=18  p=3", 5150, 18, 3),
                            ("L=26  p=3", 8675309, 26, 3),
                            ("L=40  p=3", 112358, 40, 3)):
        ok, mx, hm = report(lbl, sweep(seed, 1200, L, p))
        res.append((lbl, ok, mx, hm))
        print()
    print("=" * 72)
    if not all(ok for _, ok, _, _ in res):
        print("  CONTROL MISSED (nothing to expand) -- round counts WITHHELD.")
        return 1
    mx = [m for _, _, m, _ in res]
    print("  CONTROL HELD.  Max rounds by tower shape:")
    for lbl, _, m, hm in res:
        tag = f"   ({hm} runs hit the ceiling, so this is a LOWER bound)" if hm else ""
        print(f"    {lbl} : {m}{tag}")
    print()
    if max(mx) == min(mx):
        print(f"  CONSTANT at {max(mx)} across all shapes -> step 2 looks")
        print("  provable: the round count does not depend on the model.")
    else:
        print(f"  MOVES ({min(mx)}..{max(mx)}) with tower shape -> the round")
        print("  count may be a property of the model; step 2 needs the measure")
        print("  to come from C0, and this says look harder before formalising.")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
