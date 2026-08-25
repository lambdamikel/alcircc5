#!/usr/bin/env python3
"""
rev2_wp101_top_region.py -- referee probe against wp101 part D.

CLAIM UNDER TEST (wp101 docstring + ASSEMBLY_DESIGN 49.4):
  "Only the IN-KERNEL rate is stable across all four model-class variants
   (89.2 / 90.2 / 83.5 / 91.3%)."
and wp101 part D's headline: 91.3% of cofinally recurring ONE-SHOT vertical
demands are served in-kernel, free.

wp100 was retired because its models had a MAXIMAL element, which satisfies no
`exists-PP.X`, so every node below it failed `forall-PP.exists-PP.X` and 100% of
demands read as one-shot.

HYPOTHESIS: wp101 reintroduces exactly that.  `build_model`'s cofinite branch is
    Reg(True, rng.sample(range(6), rng.randint(0, 3)))
and `randint(0, 3)` returns 0 with probability 1/4, giving Reg(True, frozenset())
= N, the WHOLE universe.  N is PP-above every chain node a_i = {0..i} and above
every other region in the class, and NOTHING is above N, so

    N |=/= exists-PP.X   for every X,

hence every chain node below N fails forall-PP.exists-PP.X and EVERY demand in
such a model is classified one-shot -- wp100's artifact, relocated from the
chain's top to the domain's top.

This script uses wp101's own code unmodified (import), and only changes which
side regions are drawn.
"""
import random
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp101_periodic_oneshot_vertical as W

PP = W.PP
TOP = W.Reg(True, ())


def has_top(m):
    return any(s == TOP for s in m.sides)


# ---------------------------------------------------------------- 1. frequency
def freq(trials=4000, seed=1):
    rng = random.Random(seed)
    n = sum(1 for _ in range(trials) if has_top(W.build_model(rng)))
    print(f"1. P(the maximum region N is among the 6 sides) = "
          f"{n}/{trials} = {100*n/trials:.1f}%")


# --------------------------------------- 2. is a demand one-shot *because* of N
def why_oneshot(trials=400, seed=101101):
    """For every chain exists-PP demand that reads ONE-SHOT, ask whether the
    forall-PP guard fails ONLY at N -- i.e. whether it would read PERSISTENT in
    the same model with N removed."""
    rng = random.Random(seed)
    hi = 40
    oneshot = spurious = 0
    for _ in range(trials):
        c0 = W.rand_concept(rng, rng.randint(2, 3))
        m = W.build_model(rng)
        if not has_top(m):
            continue
        m2 = W.PerModel(m.p, m.chain_val,
                        [s for s in m.sides if s != TOP], m.side_val)
        m2._stab = m._stab
        # side_val keys are (atom, index); reindex for the pruned model
        keep = [j for j, s in enumerate(m.sides) if s != TOP]
        m2.side_val = {(a, new): m.side_val.get((a, old), False)
                       for a in range(2) for new, old in enumerate(keep)}
        for i in range(m._stab, m._stab + 2 * m.p):
            for d in W.closure(c0):
                if d[0] != "ex" or d[1] != PP:
                    continue
                if not m.sat_chain(i, d, hi):
                    continue
                if m.sat_chain(i, ("all", PP, d), hi):
                    continue                       # persistent already
                oneshot += 1
                # same node, same model, N deleted
                if m2.sat_chain(i, d, hi) and m2.sat_chain(i, ("all", PP, d), hi):
                    spurious += 1
    print(f"2. one-shot demands in models that contain N : {oneshot}")
    if oneshot:
        print(f"   of these, PERSISTENT once N is deleted   : {spurious}"
              f"  ({100*spurious/oneshot:.1f}%)")
        print("   -> that fraction is wp100's artifact, verbatim.")


# ------------------------------------------- 3. part D, split by presence of N
def part_d_split(trials=900, seed=404404, exclude_top=False, label=""):
    """wp101 part_d, verbatim, except: optionally refuse models containing N,
    and always report the split."""
    rng = random.Random(seed)
    hi = 60
    stats = {True: [0, 0], False: [0, 0]}      # has_top -> [inkernel, extonly]
    for _ in range(trials):
        c0 = W.rand_concept(rng, rng.randint(2, 3))
        m = W.build_model(rng)
        top = has_top(m)
        if exclude_top and top:
            continue
        for d in W.closure(c0):
            if d[0] != "ex" or d[1] != PP:
                continue
            X = d[2]
            WIN = 64 * m.p
            occ = [i for i in range(m._stab, m._stab + WIN)
                   if m.sat_chain(i, d, hi)
                   and not m.sat_chain(i, ("all", PP, d), hi)]
            if not occ or len([i for i in occ
                               if i > m._stab + 3 * WIN // 4]) < m.p:
                continue
            chain_hits = [k for k in range(m._stab, m._stab + 8 * m.p)
                          if m.sat_chain(k, X, hi)]
            if len(chain_hits) >= 3:
                stats[top][0] += 1
            else:
                stats[top][1] += 1
    print(f"3{label}. part D re-run"
          + (" (models containing N REFUSED)" if exclude_top else ""))
    for k in (True, False):
        ik, ex = stats[k]
        tot = ik + ex
        if tot:
            print(f"     models {'WITH' if k else 'WITHOUT'} N : "
                  f"n={tot:4d}   in-kernel {ik:4d} ({100*ik/tot:5.1f}%)   "
                  f"external {ex:4d} ({100*ex/tot:5.1f}%)")
        else:
            print(f"     models {'WITH' if k else 'WITHOUT'} N : n=0")
    ikA, exA = stats[True]
    ikB, exB = stats[False]
    tot = ikA + exA + ikB + exB
    if tot:
        print(f"     pooled          : n={tot:4d}   in-kernel "
              f"{100*(ikA+ikB)/tot:5.1f}%")


# ------------------------- 4. is `_stab` really a stabilisation index?
def stab_check(trials=300, seed=7):
    """wp101 sets m._stab = 11 and comments 'above this index every side's
    relation to the chain has stabilised'.  sat_chain_res evaluates the whole
    chain-facing quantifier at indices _stab.._stab+p-1 on that basis.  But the
    BOUNDED-SEGMENT generator draws M in [stab+1, stab+5p], and such a side is
    PP-above a_0..a_{M-1} and not above a_M.  So the relation changes ABOVE
    _stab, by construction."""
    rng = random.Random(seed)
    worst = 0
    bad = 0
    for _ in range(trials):
        m = W.build_model(rng)
        last = 0
        for j, s in enumerate(m.sides):
            for i in range(0, 260):
                if W.rel(m.a(i), s) != W.rel(m.a(i + 1), s):
                    last = max(last, i + 1)
        if last > m._stab:
            bad += 1
        worst = max(worst, last)
    print(f"4. models whose side/chain relations change ABOVE _stab={11} : "
          f"{bad}/{trials}")
    print(f"   highest index at which a side/chain relation still changes: "
          f"{worst}")
    print("   sat_chain_res evaluates at indices 11..11+p-1, i.e. inside the")
    print("   unstable zone; part D's in-kernel test scans [11, 11+8p) as well,")
    print("   while cofinality is tested out to 11+64p.")


if __name__ == "__main__":
    print("=" * 74)
    print("rev2 -- is wp101's in-kernel rate an artifact of a maximum region?")
    print("=" * 74)
    freq()
    print()
    why_oneshot()
    print()
    part_d_split(label="a")
    print()
    part_d_split(exclude_top=True, label="b")
    print()
    stab_check()
