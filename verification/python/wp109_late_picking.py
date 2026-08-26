#!/usr/bin/env python3
"""WP109 -- does LATE PICKING remove direction switches instead of bounding them?

ASSEMBLY_DESIGN sec. 105.3, route 3.  The mixed quadrant is certified down to
one number, `SwitchBounded C0 I S` (sec. 104.2): every mixed skip path
decomposes into at most S same-direction runs.  Routes 1 (prove the bound) and
2 (fold same-type nodes) both cost real work.  Route 3 is cheaper and untested:

  the extraction CHOOSES its witnesses (`Classical.choose` in `ppWitness` /
  `ppiWitness`).  If, when serving a one-shot demand, it PREFERS a witness
  already in the node set, then no new node is created and no switch happens.

This is the `pp_witness_all_below` / `dr_witness_all_below` "late picking"
discipline the campaign already used elsewhere, applied to the vertical steps.

Late picking is SOUND by construction here: the preferred witness is a genuine
model witness (the real relation, the real label), just a different choice than
`Classical.choose` would make.  So the only question is whether it HELPS.

MEASURED, greedy vs late:
  new-node chain DEPTH   -- the fuel the closure actually needs
  SWITCHES on that chain -- the quantity `SwitchBounded` is about
  node count            -- the size of the certificate
  service rate          -- how often an existing node already serves

Parts A/B/C mirror wp107/wp108 so the numbers are comparable: random concepts,
the alternation engine built on purpose, and a hill-climbed champion.

Self-contained: RCC5 relations re-derived from finite set semantics.
"""

import random
from itertools import combinations

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


def subsets(univ):
    out = []
    for k in range(1, len(univ) + 1):
        for c in combinations(sorted(univ), k):
            out.append(frozenset(c))
    return out


def mdepth(c):
    k = c[0]
    if k in ("at", "nat"):
        return 0
    if k in ("and", "or"):
        return max(mdepth(c[1]), mdepth(c[2]))
    return 1 + mdepth(c[2])


def closure(c, acc=None):
    if acc is None:
        acc = []
    if c not in acc:
        acc.append(c)
    k = c[0]
    if k in ("and", "or"):
        closure(c[1], acc)
        closure(c[2], acc)
    elif k in ("ex", "all"):
        closure(c[2], acc)
    return acc


def po_free(c):
    k = c[0]
    if k in ("at", "nat"):
        return True
    if k in ("and", "or"):
        return po_free(c[1]) and po_free(c[2])
    if k == "all" and c[1] == PO:
        return False
    return po_free(c[2])


def sat(model, val, x, c):
    k = c[0]
    if k == "at":
        return val.get((c[1], x), False)
    if k == "nat":
        return not val.get((c[1], x), False)
    if k == "and":
        return sat(model, val, x, c[1]) and sat(model, val, x, c[2])
    if k == "or":
        return sat(model, val, x, c[1]) or sat(model, val, x, c[2])
    if k == "ex":
        return any(rel(x, y) == c[1] and sat(model, val, y, c[2]) for y in model)
    return all(rel(x, y) != c[1] or sat(model, val, y, c[2]) for y in model)


def mty(model, val, c0, x):
    return frozenset(d for d in closure(c0) if sat(model, val, x, d))


def mtk(model, val, c0, x, k):
    return frozenset(d for d in mty(model, val, c0, x) if mdepth(d) <= k)


def persistent(model, val, c0, x, D, direction):
    ex = ("ex", direction, D)
    return ex in mty(model, val, c0, x) and sat(model, val, x, ("all", direction, ex))


# ------------------------------------------------------------ the two closures

def build(model, val, c0, root, late, cap=800):
    """Build the vertical closure.  `late` = prefer a witness already in the set.

    Returns (max creation-chain depth, max switches on a creation chain,
             node count, demands served from the existing set, demands total)."""
    budget = mdepth(c0) + 1
    # info[x] = (depth, last_direction, switches) for the edge that CREATED x
    info = {root: (0, None, 0)}
    order = [root]
    work = [root]
    served_existing = 0
    demands = 0
    steps = 0
    while work and steps < cap:
        steps += 1
        x = work.pop(0)
        dep, lastd, sw = info[x]
        for d in sorted(mtk(model, val, c0, x, budget)):
            if d[0] != "ex" or d[1] not in (PP, PPI):
                continue
            D = d[2]
            if persistent(model, val, c0, x, D, d[1]):
                continue                       # kernel-served
            demands += 1
            if late:
                hit = None
                for y in order:                # deterministic: creation order
                    if rel(x, y) == d[1] and sat(model, val, y, D):
                        hit = y
                        break
                if hit is not None:
                    served_existing += 1
                    continue                   # NO new node, NO switch
            for y in model:
                if rel(x, y) == d[1] and sat(model, val, y, D):
                    if y in info:
                        served_existing += 1
                        break
                    nsw = sw + (1 if lastd is not None and d[1] != lastd else 0)
                    info[y] = (dep + 1, d[1], nsw)
                    order.append(y)
                    work.append(y)
                    break
    mdep = max((v[0] for v in info.values()), default=0)
    msw = max((v[2] for v in info.values()), default=0)
    return mdep, msw, len(info), served_existing, demands


def sweep(rng, c0, usize, tries, acc):
    regs = subsets(set(range(usize)))
    for _ in range(tries):
        m = rng.sample(regs, min(len(regs), rng.randint(2, min(len(regs), 10))))
        val = {}
        for a in range(3):
            for x in m:
                val[(a, x)] = rng.random() < 0.5
        for x in m:
            if sat(m, val, x, c0):
                g = build(m, val, c0, x, False)
                l = build(m, val, c0, x, True)
                acc.append((g, l))
                break


def report(acc, label):
    if not acc:
        print(f"  {label}: no models")
        return None
    gd = max(g[0] for g, _ in acc); ld = max(l[0] for _, l in acc)
    gs = max(g[1] for g, _ in acc); ls = max(l[1] for _, l in acc)
    gn = max(g[2] for g, _ in acc); ln = max(l[2] for _, l in acc)
    tot = sum(l[4] for _, l in acc); srv = sum(l[3] for _, l in acc)
    print(f"  {label:26s} samples {len(acc):5d}")
    print(f"    {'':10s} {'depth':>7} {'switches':>9} {'nodes':>7}")
    print(f"    {'greedy':10s} {gd:7d} {gs:9d} {gn:7d}")
    print(f"    {'late':10s} {ld:7d} {ls:9d} {ln:7d}")
    print(f"    demands served from the existing set (late): "
          f"{srv}/{tot} = {100.0*srv/max(tot,1):.1f}%")
    return gd, ld, gs, ls


def rand_c(rng, depth):
    if depth == 0 or rng.random() < 0.2:
        i = rng.randrange(3)
        return ("at", i) if rng.random() < 0.6 else ("nat", i)
    r = rng.random()
    if r < 0.2:
        return ("and", rand_c(rng, depth - 1), rand_c(rng, depth - 1))
    if r < 0.32:
        return ("or", rand_c(rng, depth - 1), rand_c(rng, depth - 1))
    if r < 0.68:
        return ("ex", rng.choice([PP, PPI, PP, PPI, DR]), rand_c(rng, depth - 1))
    return ("all", rng.choice([PP, PPI, PP, PPI, DR, EQ]), rand_c(rng, depth - 1))


def engine():
    A = ("at", 0); B = ("at", 1)
    return ("and", ("and", A, ("all", PP, ("ex", PPI, B))),
            ("and", ("all", PPI, ("ex", PP, A)), ("ex", PP, ("at", 2))))


def part_a(seed=8080, trials=3000):
    print("PART A -- random forall-PO-free concepts, greedy vs late")
    rng = random.Random(seed)
    acc = []
    for _ in range(trials):
        c0 = rand_c(rng, rng.randint(2, 4))
        if not po_free(c0):
            continue
        sweep(rng, c0, 5, 3, acc)
    r = report(acc, "random concepts")
    return r is not None and r[3] <= r[2]


def part_b(seed=9090):
    print("\nPART B -- the alternation engine (wp108 part A), greedy vs late")
    c0 = engine()
    ok = True
    for u in (4, 5, 6):
        acc = []
        rng = random.Random(seed + u)
        sweep(rng, c0, u, 700, acc)
        r = report(acc, f"engine, universe {u}")
        if r:
            ok &= r[3] <= r[2]
    return ok


def part_c(seed=1010, pool=1500):
    print("\nPART C -- hill-climbed champion (wp108 part B), greedy vs late")
    rng = random.Random(seed)
    champ, best = None, -1
    for _ in range(pool):
        c0 = rand_c(rng, rng.randint(2, 4))
        if not po_free(c0):
            continue
        acc = []
        sweep(rng, c0, 4, 60, acc)
        if acc:
            s = max(g[1] for g, _ in acc)
            if s > best:
                champ, best = c0, s
    if champ is None:
        print("  no champion")
        return False
    print(f"  champion mdepth {mdepth(champ)}  |cl C0| {len(closure(champ))}  "
          f"greedy switches {best}")
    ok = True
    for u in (4, 5, 6):
        acc = []
        rng2 = random.Random(seed + 7 * u)
        sweep(rng2, champ, u, 700, acc)
        r = report(acc, f"champion, universe {u}")
        if r:
            ok &= r[3] <= r[2]
    return ok


def main():
    res = {"A random": part_a(), "B engine": part_b(), "C champion": part_c()}
    print("\n" + "=" * 72)
    for k, v in res.items():
        print(f"  {k:14s} : {'late no worse' if v else 'LATE WORSE'}")
    print("=" * 72)
    print()
    print("  READ: late picking is SOUND by construction (a real model witness,")
    print("  a different choice).  If it drives switches to 0, SwitchBounded")
    print("  becomes free and route 3 finishes the mixed quadrant.  If it only")
    print("  lowers them, it is a constant-factor win and routes 1/2 still")
    print("  decide.  Scope: finite set models, deterministic creation order.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
