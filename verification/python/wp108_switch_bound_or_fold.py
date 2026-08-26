#!/usr/bin/env python3
"""WP108 -- is `SwitchBounded` TRUE, or is a FOLD mandatory?

ASSEMBLY_DESIGN sec. 104.2.  The mixed quadrant's vertical closure is certified
down to ONE number: `SwitchBounded C0 I S` -- every mixed skip path decomposes
into at most S same-direction runs.  Two futures:

  S is a function of C0        -> a THEOREM finishes the composition
  S grows with the model       -> a FOLD is mandatory (identify same-type
                                  nodes), a construction, not a bound

wp107 measured random concepts and found switches bounded and small, but random
sampling cannot force the adversarial case.  This probe attacks it directly.

THE ENGINE (sec. 104.3).  A CROSS-DIRECTION universal regenerates a demand of
the opposite direction whose own guard can fail:

    forall PP.(exists PPI.E)   puts an exists-PPI demand at every superset
    forall PPI.(exists PP.F)   puts an exists-PP  demand at every subset

Each is regenerated (so modal depth is no measure) and each can be ONE-SHOT (so
no kernel serves it).  Alternating the two is the alternation engine.  Since
cl C0 is finite the engine must cycle -- the question is whether the certificate
can stop when it cycles, or must keep walking.

PART A  builds the engine explicitly and measures alternation as the universe
        grows, for a FIXED concept.  This is the falsification test: growth for
        a fixed C0 refutes SwitchBounded.
PART B  hill-climbs for the switchiest concept at each universe size and asks
        the same question of the winner.
PART C  checks whether a mixed type-repeat is even REACHABLE -- if every mixed
        path with a type repeat is already cut by the per-direction test, the
        fold is unnecessary regardless.

Self-contained: RCC5 relations and the composition table are re-derived from
finite set semantics.
"""

import random
from itertools import combinations

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
ATOMS = [DR, PO, EQ, PP, PPI]


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


def walk(model, val, c0, root, budget, cap=3000):
    """Return (max switches, max path length, saw a MIXED type repeat).

    Cuts, per direction, when a (type, direction) pair repeats on the path --
    which is exactly what kserU / kserD do.  A repeat of a type with the OTHER
    direction is NOT cut (that is sec. 103.1) and is recorded."""
    best_sw = best_len = 0
    mixed_repeat = False
    stack = [(root, None, 0, ((mty(model, val, c0, root), None),))]
    steps = 0
    while stack and steps < cap:
        steps += 1
        x, lastd, sw, seen = stack.pop()
        best_sw = max(best_sw, sw)
        best_len = max(best_len, len(seen) - 1)
        for d in mtk(model, val, c0, x, budget):
            if d[0] != "ex" or d[1] not in (PP, PPI):
                continue
            D = d[2]
            if persistent(model, val, c0, x, D, d[1]):
                continue
            for y in model:
                if rel(x, y) == d[1] and sat(model, val, y, D):
                    ty = mty(model, val, c0, y)
                    nd = d[1]
                    if (ty, nd) in seen:
                        break                       # the per-direction cut
                    if any(t == ty for t, _ in seen):
                        mixed_repeat = True         # sec. 103.1's bad case
                    nsw = sw + (1 if lastd is not None and nd != lastd else 0)
                    stack.append((y, nd, nsw, seen + ((ty, nd),)))
                    break
    return best_sw, best_len, mixed_repeat


def best_over_models(rng, c0, usize, tries=900, maxregs=None):
    """Search models of C0 at this universe size; return the worst-case walk."""
    regs = subsets(set(range(usize)))
    if maxregs is None:
        maxregs = min(len(regs), 10)
    bw = bl = 0
    mr = False
    found = 0
    for _ in range(tries):
        m = rng.sample(regs, min(len(regs), rng.randint(2, maxregs)))
        val = {}
        for a in range(3):
            for x in m:
                val[(a, x)] = rng.random() < 0.5
        for x in m:
            if sat(m, val, x, c0):
                found += 1
                sw, pl, rep = walk(m, val, c0, x, mdepth(c0) + 1)
                bw = max(bw, sw)
                bl = max(bl, pl)
                mr |= rep
                break
    return bw, bl, mr, found


# ------------------------------------------------------------------ the engine

def engine():
    """A ⊓ ∀PP.(∃PPI.B) ⊓ ∀PPI.(∃PP.A) ⊓ ∃PP.⊤ -- the cross-direction cycle."""
    A = ("at", 0)
    B = ("at", 1)
    return ("and",
            ("and", A, ("all", PP, ("ex", PPI, B))),
            ("and", ("all", PPI, ("ex", PP, A)), ("ex", PP, ("at", 2))))


def part_a(seed=20260825):
    print("PART A -- the ALTERNATION ENGINE at growing universe size")
    c0 = engine()
    print(f"  concept modal depth {mdepth(c0)}   |cl C0| {len(closure(c0))}   "
          f"forall-PO-free {po_free(c0)}")
    print(f"  {'universe':>9} {'models':>7} {'max switches':>13} "
          f"{'max path':>9} {'mixed repeat':>13}")
    rows = []
    for u in (3, 4, 5, 6):
        rng = random.Random(seed + u)
        sw, pl, mr, f = best_over_models(rng, c0, u)
        rows.append(sw)
        print(f"  {u:9d} {f:7d} {sw:13d} {pl:9d} {str(mr):>13}")
    grew = len(rows) > 1 and rows[-1] > rows[0]
    print(f"  => switches {'GROW' if grew else 'do NOT grow'} with the universe")
    return not grew


def part_b(seed=777001, pool=2500):
    print("\nPART B -- hill-climb for the switchiest concept, then grow the model")

    def rand_c(rng, depth):
        if depth == 0 or rng.random() < 0.2:
            i = rng.randrange(3)
            return ("at", i) if rng.random() < 0.6 else ("nat", i)
        r = rng.random()
        if r < 0.2:
            return ("and", rand_c(rng, depth - 1), rand_c(rng, depth - 1))
        if r < 0.3:
            return ("or", rand_c(rng, depth - 1), rand_c(rng, depth - 1))
        if r < 0.65:
            return ("ex", rng.choice([PP, PPI, PP, PPI, DR]), rand_c(rng, depth - 1))
        return ("all", rng.choice([PP, PPI, PP, PPI, DR, EQ]), rand_c(rng, depth - 1))

    rng = random.Random(seed)
    champ, champ_sw = None, -1
    for _ in range(pool):
        c0 = rand_c(rng, rng.randint(2, 4))
        if not po_free(c0):
            continue
        sw, _, _, f = best_over_models(rng, c0, 4, tries=120)
        if f and sw > champ_sw:
            champ, champ_sw = c0, sw
    if champ is None:
        print("  no champion found")
        return False
    print(f"  champion: mdepth {mdepth(champ)}  |cl C0| {len(closure(champ))}  "
          f"switches at u=4: {champ_sw}")
    print(f"  {'universe':>9} {'models':>7} {'max switches':>13} {'max path':>9}")
    rows = []
    for u in (4, 5, 6):
        rng2 = random.Random(seed + 31 * u)
        sw, pl, _, f = best_over_models(rng2, champ, u, tries=1400)
        rows.append(sw)
        print(f"  {u:9d} {f:7d} {sw:13d} {pl:9d}")
    grew = rows[-1] > rows[0]
    print(f"  => switches {'GROW' if grew else 'do NOT grow'} for the champion")
    return not grew


def part_c(seed=424242, trials=4000):
    print("\nPART C -- is a MIXED type repeat even reachable?")
    print("  (if no reachable mixed path ever repeats a type, sec.103.1's bad")
    print("   case is vacuous on these models and no fold is needed)")

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

    rng = random.Random(seed)
    n = reps = 0
    for _ in range(trials):
        c0 = rand_c(rng, rng.randint(2, 4))
        if not po_free(c0):
            continue
        _, _, mr, f = best_over_models(rng, c0, 5, tries=90)
        if f:
            n += 1
            reps += 1 if mr else 0
    pct = 100.0 * reps / max(n, 1)
    print(f"  concepts with a model : {n}")
    print(f"  showing a MIXED type repeat on a reachable path : {reps} ({pct:.1f}%)")
    print("  => the bad case is NOT vacuous" if reps else
          "  => the bad case never occurred here")
    return n > 0


def main():
    res = {"A engine": part_a(), "B champion": part_b(), "C reachability": part_c()}
    print("\n" + "=" * 72)
    for k, v in res.items():
        print(f"  {k:18s} : {'bounded' if v else 'GREW / see part'}")
    print("=" * 72)
    print()
    print("  READ: parts A and B are the falsification test for SwitchBounded.")
    print("  Growth for a FIXED concept as the model grows would refute it and")
    print("  make the fold mandatory.  No growth is evidence for the bound --")
    print("  evidence only: these are finite set models and a random search.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
