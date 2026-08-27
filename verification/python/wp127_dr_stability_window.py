#!/usr/bin/env python3
"""WP127 -- does a DR witness STAY disjoint as the chain grows?

ASSEMBLY_DESIGN sec.166.4.  wp126 could not test kDR: wp112's tower gives
dr-sides disjoint from the WHOLE chain by construction, so it cannot exhibit
sec.165.1's failure mode -- a witness disjoint at one phase and not at a later
one.

This probe uses PLAIN FINITE SET MODELS, where the failure is natural:

    chain  a_i = {0..i}   (a genuine ascending PP-chain)
    sides  arbitrary subsets of the universe

If  a_i DR w  then  a_i and w are disjoint; but a_j for j > i is LARGER, so it
may meet w.  Disjointness propagates DOWN the chain, never up -- exactly
comp(PP,DR) = {DR} versus comp(PPI,DR) = {PPI,PO,DR}.

Cofinality cannot be tested in a finite model, so this measures the TREND: of the
DR witnesses available at position i, what fraction survive to position i+W as
the window W grows?  A rate that decays with W is sec.165.1's failure mode
quantified; a flat rate says the witnesses that exist tend to be robust.

CONTROL, stated before the run: at W = 0 the rate must be 100% -- the witness is
disjoint at its own position by definition.  Anything else means the probe is
wrong.

Self-contained: RCC5 relations from finite set semantics.
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


def chain(i):
    return frozenset(range(i + 1))


def sweep(seed, trials, U, W):
    """Of the DR witnesses at a chain position, how many survive W steps up?"""
    rng = random.Random(seed)
    tot = surv = 0
    havewit = 0
    for _ in range(trials):
        # a random side set
        w = frozenset(rng.sample(range(U), rng.randint(1, max(1, U // 2))))
        for i in range(U - W - 1):
            if rel(chain(i), w) != DR:
                continue
            havewit += 1
            tot += 1
            if all(rel(chain(j), w) == DR for j in range(i, i + W + 1)):
                surv += 1
    return tot, surv, havewit


def sweep_exists(seed, trials, U, W):
    """The ACTUAL kDR question: the extraction CHOOSES its witness, so ask
    whether SOME D-carrier stays disjoint over the window -- not whether an
    arbitrary one does."""
    rng = random.Random(seed)
    demands = served = 0
    for _ in range(trials):
        # D holds on a random set of "carrier" subsets
        carriers = [frozenset(rng.sample(range(U), rng.randint(1, max(1, U // 2))))
                    for _ in range(6)]
        for i in range(U - W - 1):
            ci = chain(i)
            here = [w for w in carriers if rel(ci, w) == DR]
            if not here:
                continue                       # demand not present at i
            demands += 1
            if any(all(rel(chain(j), w) == DR for j in range(i, i + W + 1))
                   for w in here):
                served += 1
    return demands, served


def main():
    print("WP127 -- does a DR witness stay disjoint as the chain grows?\n")
    print(f"  {'window W':>9} {'DR witnesses':>13} {'still DR at i+W':>17} {'rate':>8}")
    rates = []
    for W in (0, 1, 2, 4, 8, 16):
        tot = surv = 0
        for seed in (11, 22, 33, 44):
            t, s, _ = sweep(seed, 400, 40, W)
            tot += t
            surv += s
        r = 100.0 * surv / max(tot, 1)
        rates.append((W, r))
        print(f"  {W:9d} {tot:13d} {surv:17d} {r:7.1f}%")
    print()
    if abs(rates[0][1] - 100.0) > 1e-9:
        print("  CONTROL MISSED (W=0 not 100%) -- probe wrong, rates WITHHELD.")
        return 1
    print("  CONTROL HELD (W=0 gives 100%).")
    print()
    decay = rates[0][1] - rates[-1][1]
    if decay > 5.0:
        print(f"  The rate DECAYS by {decay:.1f} points from W=0 to W={rates[-1][0]}.")
        print("  sec.165.1's failure mode is REAL and quantified: a DR witness")
        print("  chosen at one position frequently stops being disjoint higher up,")
        print("  so kDR genuinely needs the witness chosen for STABILITY, not")
        print("  merely for disjointness-here.")
    else:
        print(f"  The rate is FLAT ({decay:.1f} points) -- DR witnesses that exist")
        print("  tend to stay disjoint, so kDR is closer to a lookup than")
        print("  sec.165.1 feared.")
    print()
    print()
    print("  PART B -- the ACTUAL kDR question: does SOME D-carrier stay")
    print("  disjoint?  The extraction CHOOSES, so existence is what matters.")
    print(f"  {'window W':>9} {'demands':>9} {'a stable carrier exists':>25} {'rate':>8}")
    brates = []
    for W in (0, 1, 2, 4, 8, 16):
        d = sv = 0
        for seed in (11, 22, 33, 44):
            a, b = sweep_exists(seed, 400, 40, W)
            d += a
            sv += b
        r = 100.0 * sv / max(d, 1)
        brates.append((W, r))
        print(f"  {W:9d} {d:9d} {sv:25d} {r:7.1f}%")
    print()
    bdecay = brates[0][1] - brates[-1][1]
    if bdecay > 5.0:
        print(f"  Existence ALSO decays ({bdecay:.1f} points) -- some demands have")
        print("  no stable carrier at all, so kDR is not merely a selection")
        print("  discipline but a genuine obligation that can FAIL.")
    else:
        print(f"  Existence is FLAT ({bdecay:.1f} points) while arbitrary choice")
        print("  decays sharply -- so kDR IS a selection discipline: stable")
        print("  carriers are there, but must be CHOSEN, not taken at random.")
    print()
    print("  SCOPE: finite models, so 'cofinal' is approximated by a window.")
    print("  The TREND is the measurement; the absolute rate is not.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
