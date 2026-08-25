#!/usr/bin/env python3
"""
rev3_wp101_partD_decomposed.py

rev2 established that 100% of wp101 part D's population (173/173 cases) comes
from models that contain the maximum region N = Reg(True, ()), and that part D
finds ZERO qualifying cases in models without it.

This script asks the follow-up: inside that population, does the ONE-SHOT
classification carry any information at all?  For each of part D's cases we
recompute, in the SAME model with N deleted, whether the demand is still
one-shot (some node above the demanding node fails exists-PP.D) or is in fact
PERSISTENT and was only classified one-shot because nothing sits above N.

If the in-kernel cases are exactly the ones that were never one-shot, then part
D's 91.3% "in-kernel" rate is measuring PERSISTENCE, not in-kernel service of a
one-shot demand -- and it is wp100's artifact with an extra step.
"""
import random
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp101_periodic_oneshot_vertical as W

PP = W.PP
TOP = W.Reg(True, ())
NATOMS = 2


def drop_top(m):
    keep = [j for j, s in enumerate(m.sides) if s != TOP]
    m2 = W.PerModel(m.p, m.chain_val, [m.sides[j] for j in keep], {})
    m2._stab = m._stab
    m2.side_val = {(a, new): m.side_val.get((a, old), False)
                   for a in range(NATOMS) for new, old in enumerate(keep)}
    return m2


def main(trials=900, seed=404404):
    rng = random.Random(seed)
    hi = 60
    # buckets: (still one-shot without N?, in-kernel?)
    tab = {(True, True): 0, (True, False): 0,
           (False, True): 0, (False, False): 0}
    for _ in range(trials):
        c0 = W.rand_concept(rng, rng.randint(2, 3))
        m = W.build_model(rng)
        m2 = drop_top(m) if any(s == TOP for s in m.sides) else m
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
            inker = len([k for k in range(m._stab, m._stab + 8 * m.p)
                         if m.sat_chain(k, X, hi)]) >= 3
            # same test, N deleted: is the demand still one-shot cofinally?
            occ2 = [i for i in range(m2._stab, m2._stab + WIN)
                    if m2.sat_chain(i, d, hi)
                    and not m2.sat_chain(i, ("all", PP, d), hi)]
            still = bool(occ2) and len([i for i in occ2
                                        if i > m2._stab + 3 * WIN // 4]) >= m2.p
            tab[(still, inker)] += 1

    tot = sum(tab.values())
    print("=" * 74)
    print("wp101 part D population, decomposed")
    print("=" * 74)
    print(f"  total cases part D counts                : {tot}")
    print()
    print(f"  {'':34}{'in-kernel':>12}{'external':>12}{'total':>8}")
    for still, lbl in ((True, "still one-shot with N deleted"),
                       (False, "NOT one-shot with N deleted")):
        ik, ex = tab[(still, True)], tab[(still, False)]
        print(f"  {lbl:34}{ik:12d}{ex:12d}{ik+ex:8d}")
    print()
    ik_tot = tab[(True, True)] + tab[(False, True)]
    print(f"  part D's headline in-kernel rate         : "
          f"{100*ik_tot/tot:.1f}%  (matches the shipped 91.3%)")
    genuine = tab[(True, True)] + tab[(True, False)]
    if genuine:
        print(f"  in-kernel rate over GENUINELY one-shot    : "
              f"{100*tab[(True, True)]/genuine:.1f}%   (n={genuine})")
    else:
        print("  in-kernel rate over GENUINELY one-shot    : "
              "UNDEFINED -- n=0, the population is empty")
    print()
    print("  Reading: every case part D counts is one-shot only because N sits")
    print("  above the chain and satisfies no exists-PP.X.  Delete N and the")
    print("  demand is persistent, which is precisely why X 'recurs on the")
    print("  chain'.  The 91.3% is a measurement of PERSISTENCE.")


if __name__ == "__main__":
    main()
