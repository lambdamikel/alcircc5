#!/usr/bin/env python3
"""WP126 -- do STABLE witnesses exist for the kernel's routing conditions?

ASSEMBLY_DESIGN sec.165.2.  The remaining four routing conditions reduce to two
selection disciplines, and this probe tests the harder one:

    kDR / kUP / kDN -- a kernel's exists-DR / opposite-direction demand must be
    served by an external whose relation to the WHOLE CHAIN is uniform in the
    required direction (mKdr for DR; up/dn for the vertical ones).

Section 165.1 says why this is not free: disjointness propagates DOWN the chain
(comp(PP,DR) = {DR}) but NOT up (comp(PPI,DR) = {PPI,PO,DR}), so a witness
disjoint at one phase may cease to be.

MEASURED, over wp112's closed-form tower (the kernel-bearing class):
  for each kernel-phase demand, does a witness exist whose relation to EVERY
  tail residue is the demanded one?

CONTROLS, stated before the run:
  (1) a demand with NO witness at all must not occur -- the phase satisfies it,
      so the model has one.  A nonzero count means the probe is wrong.
  (2) the UNIFORM rate must be at most the ANY rate.  Equality would mean
      uniformity is free here and the class is not exercising sec.165.1.
"""

import random

from wp112_lap_continuation_closed_form import (
    DR, EQ, PP, PPI, build, closure, mdepth, po_free, rand_c)


def phase_demands(T, c0, R, budget):
    return [(d[1], d[2]) for d in T.mty(c0, R)
            if d[0] == "ex" and mdepth(d) <= budget]


def any_witness(T, R, r, D):
    return any(w in T.succs(R, r) and T.sat(w, D) for w in T.nodes)


def uniform_witness(T, r, D):
    """A witness related by r to EVERY tail residue -- what mKdr / up / dn ask."""
    for w in T.nodes:
        if w[0] == "R":
            continue
        if not T.sat(w, D):
            continue
        if all(w in T.succs(Rk, r) for Rk in T.tail):
            return True
    return False


def sweep(seed, trials, L, p):
    rng = random.Random(seed)
    stats = {}
    nowit = 0
    models = 0
    for _ in range(trials):
        c0 = rand_c(rng, rng.randint(2, 4))
        if not po_free(c0):
            continue
        T = build(rng, L=L, p=p)
        if not any(T.sat(n, c0) for n in T.nodes):
            continue
        models += 1
        b = mdepth(c0) + 1
        for R in T.tail:
            for (r, D) in phase_demands(T, c0, R, b):
                if r not in (DR, PP, PPI):
                    continue
                key = r
                a, u = stats.get(key, (0, 0))
                has_any = any_witness(T, R, r, D)
                if not has_any:
                    nowit += 1
                    continue
                stats[key] = (a + 1, u + (1 if uniform_witness(T, r, D) else 0))
    return models, stats, nowit


def main():
    print("WP126 -- stable (uniform) witnesses for the kernel routing conditions\n")
    ok = True
    for lbl, seed, L, p in (("L=4  p=3", 20260826, 4, 3),
                            ("L=8  p=3", 777, 8, 3),
                            ("L=8  p=6", 5150, 8, 6),
                            ("L=18 p=3", 31337, 18, 3)):
        models, st, nowit = sweep(seed, 700, L, p)
        print(f"  {lbl}: models {models}")
        print(f"    CONTROL  phase demands with NO witness at all : {nowit}"
              f"   <- must be 0")
        if nowit:
            ok = False
        for r in (DR, PP, PPI):
            a, u = st.get(r, (0, 0))
            if a:
                print(f"    exists-{r:3s}  any-witness {a:5d}   UNIFORM {u:5d}"
                      f"  ({100.0*u/a:5.1f}%)")
            else:
                print(f"    exists-{r:3s}  none")
        print()
    print("=" * 72)
    if not ok:
        print("  CONTROL MISSED -- probe wrong, rates WITHHELD.")
        return 1
    print("  100% would mean uniform witnesses are always available and")
    print("  kDR/kUP/kDN are a lookup.  Below 100% names the residue: demands")
    print("  whose only witnesses are non-uniform, which is sec.165.1's case.")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
