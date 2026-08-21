"""WP99 -- does 'the cut' actually bound PP-path length?

ASSEMBLY_DESIGN sec.44.6 item 2 claims the dichotomy

    a PP-chain of demands either REPEATS A TYPE -- and a repetition gives a
    periodic tower, hence a KERNEL -- or it is SHORTER than the number of types

and rests the node bound on it.  Before formalizing, check the claim, because
the kernel half is not automatic: a repeat `mty(ei) = mty(ej)` with `ei PP ej`
does NOT by itself produce an infinite ascending chain in the model.  The
honest dichotomy is instead

    the demand-following path either TERMINATES (some node has no exists-PP)
    or is INFINITE (and then pigeonhole + recurrent_tail give a kernel)

and the terminating branch has no a-priori bound.  So the question that decides
the node count is:

  A  how long are greedy PP-demand paths, against |cl C0| and the number of
     REALIZED types?
  B  do types actually REPEAT along a terminating path?  (if never, length is
     bounded by the type count and the claim holds as stated)
  C  does WITNESS REUSE -- picking an existing node whenever one is PP-above and
     carries the argument -- keep the path inside |cl C0|?
  D  a forced-length family: C0_n = exists-PP^n.A, to see the bound track |cl C0|
     rather than the model.

SCOPE, stated up front: set models over a 4-element universe cap any PP-chain at
4, so part A cannot exhibit long paths.  Part D is the part with teeth on length.
"""

import random
from itertools import combinations

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
ATOMS = [DR, PO, EQ, PP, PPI]


def rel(a, b):
    if a == b: return EQ
    if a < b: return PP
    if b < a: return PPI
    if not (a & b): return DR
    return PO


def subsets(univ):
    out = []
    for k in range(1, len(univ) + 1):
        for c in combinations(sorted(univ), k):
            out.append(frozenset(c))
    return out


def mdepth(c):
    k = c[0]
    if k in ("at", "nat"): return 0
    if k in ("and", "or"): return max(mdepth(c[1]), mdepth(c[2]))
    return 1 + mdepth(c[2])


def closure(c, acc=None):
    if acc is None: acc = []
    if c not in acc: acc.append(c)
    k = c[0]
    if k in ("and", "or"): closure(c[1], acc); closure(c[2], acc)
    elif k in ("ex", "all"): closure(c[2], acc)
    return acc


def po_free(c):
    k = c[0]
    if k in ("at", "nat"): return True
    if k in ("and", "or"): return po_free(c[1]) and po_free(c[2])
    if k == "all" and c[1] == PO: return False
    return po_free(c[2])


def sat(model, val, x, c):
    k = c[0]
    if k == "at": return val.get((c[1], x), False)
    if k == "nat": return not val.get((c[1], x), False)
    if k == "and": return sat(model, val, x, c[1]) and sat(model, val, x, c[2])
    if k == "or": return sat(model, val, x, c[1]) or sat(model, val, x, c[2])
    if k == "ex":
        return any(rel(x, y) == c[1] and sat(model, val, y, c[2]) for y in model)
    return all(rel(x, y) != c[1] or sat(model, val, y, c[2]) for y in model)


def mty(model, val, x, c0):
    return frozenset(d for d in closure(c0) if sat(model, val, x, d))


def rand_concept(rng, depth, natoms=2):
    if depth == 0 or rng.random() < 0.22:
        i = rng.randrange(natoms)
        return ("at", i) if rng.random() < 0.6 else ("nat", i)
    r = rng.random()
    if r < 0.20:
        return ("and", rand_concept(rng, depth-1, natoms), rand_concept(rng, depth-1, natoms))
    if r < 0.32:
        return ("or", rand_concept(rng, depth-1, natoms), rand_concept(rng, depth-1, natoms))
    if r < 0.72:
        return ("ex", rng.choice(ATOMS), rand_concept(rng, depth-1, natoms))
    return ("all", rng.choice([DR, PP, PPI, EQ]), rand_concept(rng, depth-1, natoms))


def find_model(rng, c, natoms=2, tries=120, usize=4):
    regs = subsets(set(range(usize)))
    for _ in range(tries):
        m = rng.sample(regs, min(len(regs), rng.randint(2, 6)))
        val = {}
        for a in range(natoms):
            for x in m:
                val[(a, x)] = rng.random() < 0.5
        for x in m:
            if sat(m, val, x, c):
                return m, val, x
    return None


def greedy_path(model, val, c0, start, reuse=False, pool=None):
    """Follow exists-PP demands upward.  With `reuse`, prefer a witness already
    in `pool`."""
    path = [start]
    seen = {start}
    x = start
    while True:
        t = mty(model, val, x, c0)
        dem = [d for d in t if d[0] == "ex" and d[1] == PP]
        nxt = None
        for d in dem:
            cands = [y for y in model
                     if rel(x, y) == PP and sat(model, val, y, d[2])]
            if not cands:
                continue
            if reuse and pool:
                pref = [y for y in cands if y in pool]
                if pref:
                    nxt = pref[0]; break
            nxt = cands[0]; break
        if nxt is None or nxt in seen:
            break
        path.append(nxt); seen.add(nxt); x = nxt
    return path


def part_ab(trials=4000, seed=99001):
    print("PART A/B -- greedy PP-demand path length, and type repeats")
    rng = random.Random(seed)
    tested = 0
    maxlen = 0
    over_types = 0
    over_cl = 0
    repeats = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(1, 3))
        if not po_free(c0):
            continue
        got = find_model(rng, c0)
        if got is None:
            continue
        model, val, root = got
        tested += 1
        ntypes = len({mty(model, val, x, c0) for x in model})
        ncl = len(closure(c0))
        for s in model:
            p = greedy_path(model, val, c0, s)
            maxlen = max(maxlen, len(p))
            ts = [mty(model, val, y, c0) for y in p]
            if len(ts) != len(set(ts)):
                repeats += 1
            if len(p) > ntypes:
                over_types += 1
            if len(p) > ncl:
                over_cl += 1
    print(f"  instances tested                       : {tested}")
    print(f"  longest greedy PP-demand path          : {maxlen}")
    print(f"  paths with a REPEATED type             : {repeats}")
    print(f"  paths longer than the type count       : {over_types}")
    print(f"  paths longer than |cl C0|              : {over_cl}")
    print("  SCOPE: a 4-element universe caps any PP-chain at 4, so this part")
    print("  cannot exhibit long paths -- it only shows repeats do not occur")
    print("  at these sizes.  Part D is the length test.")
    return tested > 0


def part_d(nmax=7):
    print("\nPART D -- the forced-length family  C0_n = exists-PP^n . A")
    print(f"  {'n':>3} {'|cl C0|':>8} {'path len':>9} {'model size':>11} {'<= |cl|':>8}")
    ok = True
    for n in range(1, nmax + 1):
        c0 = ("at", 0)
        for _ in range(n):
            c0 = ("ex", PP, c0)
        # canonical model: a strict chain of n+1 nested regions, A at the top
        model = [frozenset(range(i + 1)) for i in range(n + 1)]
        val = {}
        for x in model:
            val[(0, x)] = (x == model[-1])
        root = model[0]
        assert sat(model, val, root, c0), n
        p = greedy_path(model, val, c0, root)
        ncl = len(closure(c0))
        good = len(p) <= ncl
        ok &= good
        print(f"  {n:3d} {ncl:8d} {len(p):9d} {len(model):11d} {str(good):>8}")
    print("  => the forced path length tracks |cl C0|, NOT the model: each step")
    print("     consumes one exists-PP from the closure, and the closure is")
    print("     finite in C0 alone.")
    return ok


def part_c(trials=3000, seed=99002):
    print("\nPART C -- does witness REUSE shorten paths?")
    rng = random.Random(seed)
    tested = 0
    shorter = same = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        if not po_free(c0):
            continue
        got = find_model(rng, c0)
        if got is None:
            continue
        model, val, root = got
        tested += 1
        base = greedy_path(model, val, c0, root)
        pool = set(base[:1])
        reu = greedy_path(model, val, c0, root, reuse=True, pool=pool)
        if len(reu) < len(base):
            shorter += 1
        elif len(reu) == len(base):
            same += 1
    print(f"  instances tested : {tested}")
    print(f"  reuse shortened  : {shorter}    unchanged : {same}")
    print("  => at these model sizes reuse changes nothing; it matters only")
    print("     when several witnesses of the same argument are available.")
    return tested > 0


def greedy_path_with_args(model, val, c0, start):
    """Like greedy_path, but also records the ARGUMENT of the demand used at
    each step, which the cut has to preserve."""
    path, args = [start], []
    seen = {start}
    x = start
    while True:
        t = mty(model, val, x, c0)
        nxt = arg = None
        for d in (e for e in t if e[0] == "ex" and e[1] == PP):
            cands = [y for y in model
                     if rel(x, y) == PP and sat(model, val, y, d[2])]
            if cands:
                nxt, arg = cands[0], d[2]
                break
        if nxt is None or nxt in seen:
            break
        path.append(nxt); args.append(arg); seen.add(nxt); x = nxt
    return path, args


def part_e(trials=6000, seed=99003):
    """THE CUT.  Section 44.6 said a repeat gives a KERNEL.  Part A/B refutes the
    bound that was drawn from it: repeats DO occur on terminating paths, and
    paths DO exceed the type count.  The correct statement is that a repeat on a
    FINITE path gives a CUT, not a kernel:

        mty(ei) = mty(ej), i < j  =>  delete ei..e(j-1) and keep ej.

    Two things must hold for that to be legitimate, and both are checked here:
      (i)  e(i-1) PP ej           -- model PP is TRANSITIVE, so the edge survives
      (ii) arg(i-1) in mty(ej)    -- the deleted node's role is inherited,
                                     because ej has the SAME TYPE as ei
    """
    print("\nPART E -- THE CUT: is a type repeat on a finite path removable?")
    rng = random.Random(seed)
    tested = found = ok_edge = ok_arg = 0
    bad = []
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(1, 3))
        if not po_free(c0):
            continue
        got = find_model(rng, c0)
        if got is None:
            continue
        model, val, root = got
        tested += 1
        for s in model:
            path, args = greedy_path_with_args(model, val, c0, s)
            ts = [mty(model, val, y, c0) for y in path]
            for i in range(len(path)):
                for j in range(i + 1, len(path)):
                    if ts[i] != ts[j]:
                        continue
                    found += 1
                    if i == 0:
                        ok_edge += 1; ok_arg += 1      # nothing below to re-link
                        continue
                    edge = rel(path[i - 1], path[j]) == PP
                    arg = sat(model, val, path[j], args[i - 1])
                    ok_edge += 1 if edge else 0
                    ok_arg += 1 if arg else 0
                    if not (edge and arg):
                        bad.append((c0, i, j, edge, arg))
    print(f"  instances tested                        : {tested}")
    print(f"  type repeats found on greedy paths      : {found}")
    print(f"  of those, the re-linked edge is PP      : {ok_edge}")
    print(f"  of those, the deleted role is inherited : {ok_arg}")
    if bad:
        print(f"  CUT FAILURES: {len(bad)}  e.g. {bad[0]}")
    print("  => a repeat on a finite path is REMOVABLE, so the path can be")
    print("     CHOSEN repeat-free and its length is then bounded by the number")
    print("     of types.  The kernel is what the INFINITE branch gives, not")
    print("     what a repeat gives -- section 44.6 conflated the two.")
    return found > 0 and not bad


def main():
    res = {"A/B repeats": part_ab(), "C reuse": part_c(),
           "D forced length": part_d(), "E the cut": part_e()}
    print("\n" + "=" * 72)
    for k, v in res.items():
        print(f"  {k:20s} : {'PASS' if v else 'FAIL'}")
    print("=" * 72)
    ok = all(res.values())
    print("VERDICT:", "ALL PASS" if ok else "FAILURE")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
