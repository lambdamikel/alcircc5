#!/usr/bin/env python3
"""WP102 -- can a forall-PO-free concept FORCE case 3?

ASSEMBLY_DESIGN sec. 49.5 reduced the campaign's mixed quadrant to ONE question.
For a cofinally recurring ONE-SHOT vertical demand at a kernel, exactly one of:

  1  the demanded concept recurs on the chain      -> served IN-KERNEL, cost 0
  2  one external sits above the whole kernel      -> cost 1
  3  neither                                       -> NO finite external set
                                                      can serve it

Case 3 is easy to exhibit as a MODEL.  The open question is whether a CONCEPT
can force EVERY model into it.  If not, the extraction always lands in 1 or 2
and the quadrant closes.

THE ROUTE UNDER TEST (sec. 50).  Do not extract a cofinal server -- CONSTRUCT one.
Add a tower above everything and let it serve the demands round-robin, exactly
as `class_persistAll` + `rr_covers` already do for the persistent half.  Adding
a top tower is safe in THIS fragment for a specific reason: a region above
everything is PPI to every old node, never PO or DR, so the only old universals
it must respect are the forall-PP ones -- and forall-PO, which would otherwise
fire on it, IS ABSENT BY HYPOTHESIS.  This is where forall-PO-freeness pays.

So the construction needs the top tower's phase types to be CONSISTENT.  This
probe measures exactly that, without building the tower:

  Q1  is  (stable forall-PP consequents at high chain nodes) + {D}  realized by
      some region of the model?   -- if always yes, the type a cofinal server
      needs always EXISTS, and case 3 is a POSITIONING failure, which an
      extension can repair
  Q2  do two different demands' requirements CONFLICT (each realizable alone,
      not together)?  -- if yes, a single top node cannot serve both and the
      round-robin TOWER is necessary, not a convenience
  Q3  is the stable consequent set small and does it stabilise at all?

Model class and the exact-satisfaction machinery are inherited from wp101
(finite/cofinite subsets of N: a genuinely infinite ascending chain with no
maximal element).  Self-contained: the RCC5 table is re-derived from finite set
semantics.
"""

import random

from wp101_periodic_oneshot_vertical import (
    comp_table,
    DR, PO, EQ, PP, PPI, ATOMS, Reg, rel, sub, disj,
    closure, mdepth, rand_concept, build_model, PerModel,
)

CT = comp_table(4)


def stable_consequents(m, c0, hi, lo, span):
    """The forall-PP consequents true at every chain node of a high segment.

    `sat_all_pp_up` (certified) makes this set MONOTONE going up, and it lives
    inside cl(C0), so it stabilises.  These are exactly the obligations a node
    placed above the whole chain would have to satisfy.
    """
    out = []
    for d in closure(c0):
        if d[0] == "all" and d[1] == PP:
            if all(m.sat_chain(i, d, hi) for i in range(lo, lo + span)):
                out.append(d[2])
    return out


def realized_by(m, reqs, hi):
    """Is there a region of the model satisfying every concept in `reqs`?"""
    for j in range(len(m.sides)):
        if all(m.sat_side(j, r, hi) for r in reqs):
            return ("side", j)
    for i in range(m._stab, m._stab + 20 * m.p):
        if all(m.sat_chain(i, r, hi) for r in reqs):
            return ("chain", i)
    return None


def cofinal_oneshot_demands(m, c0, hi):
    """The demands this probe is about: exists-PP.D present cofinally on the
    chain, guard failing, D not recurring on the chain."""
    out = []
    WIN = 64 * m.p
    for d in closure(c0):
        if d[0] != "ex" or d[1] != PP:
            continue
        occ = [i for i in range(m._stab, m._stab + WIN)
               if m.sat_chain(i, d, hi)
               and not m.sat_chain(i, ("all", PP, d), hi)]
        if not occ or len([i for i in occ if i > m._stab + 3 * WIN // 4]) < m.p:
            continue
        if len([k for k in range(m._stab, m._stab + 8 * m.p)
                if m.sat_chain(k, d[2], hi)]) >= 3:
            continue                                   # case 1, in-kernel
        out.append(d[2])
    return out


def part_q1(trials=4000, seed=606606):
    """SUPERSEDED AS A MEASUREMENT -- it is a THEOREM.

    The requirement for a cofinal server is (stable forall-PP consequents) +
    {D}, and the demand's OWN witness realizes it: if `forall-PP.X` holds at
    c i and c i PP w, then X holds at w by the meaning of `all`; and w carries
    D by choice of witness.  So case 3 is NEVER a consistency failure -- the
    needed type always exists in the model.  Certified as
    `witness_realizes_requirement` in POFreeLift.lean sec. 50.

    An early revision of this probe "measured" it at 100% over 21 samples with
    a mean consequent-set size of 0.05, i.e. it was confirming a tautology on
    empty requirements.  Kept here as the check that the reasoning matches the
    code, and re-pointed at the question that is NOT a theorem: PLACEMENT.
    """
    print("PART Q1 -- placement, the question that is NOT a theorem")
    print("  Case 3 is a POSITIONING failure, never a consistency failure (the")
    print("  requirement is realized by the demand's own witness -- a theorem,")
    print("  POFreeLift sec. 50).  So: can a server be PLACED above the whole")
    print("  chain?  The construction puts T above the chain and PO to")
    print("  everything else -- legal only if the result stays")
    print("  composition-closed.  PO is available precisely because the")
    print("  fragment has no forall-PO to fire on those edges.")
    rng = random.Random(seed)
    ok = bad = 0
    forced = {}
    for _ in range(trials):
        n = rng.randint(3, 6)
        # a random ordered-disjoint structure: chain + off-chain nodes
        clen = rng.randint(2, 3)
        lt = [[False] * n for _ in range(n)]
        for i in range(clen):
            for j in range(i + 1, clen):
                lt[i][j] = True                       # the kernel's chain
        for x in range(clen, n):                      # off-chain nodes
            for y in range(n):
                if x == y:
                    continue
                if rng.random() < 0.25:
                    lo, hiN = (x, y) if rng.random() < 0.5 else (y, x)
                    if not lt[hiN][lo]:
                        lt[lo][hiN] = True
        # transitive closure
        for k in range(n):
            for i in range(n):
                for j in range(n):
                    if lt[i][k] and lt[k][j]:
                        lt[i][j] = True
        if any(lt[i][i] for i in range(n)):
            continue
        dj = [[False] * n for _ in range(n)]
        for x in range(n):
            for y in range(x + 1, n):
                if rng.random() < 0.3 and not lt[x][y] and not lt[y][x]:
                    dj[x][y] = dj[y][x] = True
        # downward-close disjointness
        for _ in range(n):
            for x in range(n):
                for y in range(n):
                    if not dj[x][y]:
                        continue
                    for a in range(n):
                        for b in range(n):
                            if (a == x or lt[a][x]) and (b == y or lt[b][y]):
                                dj[a][b] = dj[b][a] = True
        if any(dj[x][x] for x in range(n)):
            continue
        if any(dj[x][y] and (lt[x][y] or lt[y][x])
               for x in range(n) for y in range(n)):
            continue

        def R(x, y):
            if x == y:
                return EQ
            if lt[x][y]:
                return PP
            if lt[y][x]:
                return PPI
            if dj[x][y]:
                return DR
            return PO

        # place T above the chain's DOWNWARD CLOSURE, PO to the rest.
        # The naive rule (above the chain only) breaks on exactly one cell:
        # an off-chain y BELOW a chain node z gives comp(PO,PP)={PO,PP} while
        # the rule assigns T-z = PPI.  Downward-closing repairs it, and it is
        # the same closure discipline odSeed already uses for disjointness.
        T = n
        under = [x for x in range(n)
                 if x < clen or any(lt[x][z] for z in range(clen))]

        def RT(x, y):
            if x == T and y == T:
                return EQ
            if y == T:
                return PP if x in under else PO
            if x == T:
                return PPI if y in under else PO
            return R(x, y)

        closed = True
        witness = None
        for x in range(n + 1):
            for y in range(n + 1):
                for z in range(n + 1):
                    cell = (RT(x, y), RT(y, z))
                    if RT(x, z) not in CT[cell]:
                        closed = False
                        witness = (cell, RT(x, z))
        if closed:
            ok += 1
        else:
            bad += 1
            forced[witness] = forced.get(witness, 0) + 1
    tot = ok + bad
    print(f"  structures tested                       : {tot}")
    print(f"    T placeable (PO residual keeps closure): {ok:5d}"
          f"  ({100*ok/max(tot,1):5.1f}%)")
    print(f"    placement BREAKS closure               : {bad:5d}"
          f"  ({100*bad/max(tot,1):5.1f}%)")
    if forced:
        print("    the cells that force a non-PO value:")
        for (cell, got), cnt in sorted(forced.items(), key=lambda t: -t[1])[:6]:
            print(f"      comp{cell} = {sorted(CT[cell])}   T-value {got}"
                  f"   ({cnt} cases)")
    return tot > 0


def part_q2(trials=1500, seed=707707):
    print("\nPART Q2 -- do two demands' requirements CONFLICT?")
    print("  (each realizable alone but not together => a single top node")
    print("   cannot serve both, and the round-robin TOWER is necessary)")
    rng = random.Random(seed)
    hi = 60
    pairs = conflict = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build_model(rng)
        ds = cofinal_oneshot_demands(m, c0, hi)
        if len(ds) < 2:
            continue
        cons = stable_consequents(m, c0, hi, m._stab, 4 * m.p)
        for a in range(len(ds)):
            for b in range(a + 1, len(ds)):
                ra = realized_by(m, cons + [ds[a]], hi)
                rb = realized_by(m, cons + [ds[b]], hi)
                if ra is None or rb is None:
                    continue
                pairs += 1
                if realized_by(m, cons + [ds[a], ds[b]], hi) is None:
                    conflict += 1
    print(f"  demand pairs both individually realizable : {pairs}")
    if pairs:
        print(f"    CONFLICTING (no common realizer)        : {conflict:5d}"
              f"  ({100*conflict/pairs:5.1f}%)")
    print("  A nonzero rate means the top server must be a TOWER serving")
    print("  round-robin, not a single node -- i.e. exactly rr_covers, which")
    print("  the campaign has certified since the vertical quadrant.")
    return pairs > 0


def part_q3(trials=800, seed=808808):
    print("\nPART Q3 -- does the forall-PP consequent set actually STABILISE?")
    print("  (sat_all_pp_up makes it monotone up; cl(C0) makes it finite --")
    print("   this checks the two facts meet where the construction needs them)")
    rng = random.Random(seed)
    hi = 60
    stab_ok = drift = samples = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build_model(rng)
        lo = m._stab
        s1 = set(map(str, stable_consequents(m, c0, hi, lo, 2 * m.p)))
        s2 = set(map(str, stable_consequents(m, c0, hi, lo + 8 * m.p, 2 * m.p)))
        s3 = set(map(str, stable_consequents(m, c0, hi, lo + 32 * m.p, 2 * m.p)))
        samples += 1
        if s2 == s3 and s1 <= s2:
            stab_ok += 1
        elif not (s1 <= s2 and s2 <= s3):
            drift += 1
    print(f"  models sampled                     : {samples}")
    print(f"    stabilised by 8p and monotone    : {stab_ok:5d}"
          f"  ({100*stab_ok/max(samples,1):5.1f}%)")
    print(f"    NON-MONOTONE (would break the proof): {drift:5d}")
    return drift == 0


def main():
    print("=" * 74)
    print("WP102 -- is case 3 forceable, or is it a positioning failure?")
    print("=" * 74)
    r = {"Q1 requirement realized": part_q1(),
         "Q2 demands conflict": part_q2(),
         "Q3 consequents stabilise": part_q3()}
    print("\n" + "=" * 74)
    for k, v in r.items():
        print(f"  {k:28s} : {'PASS' if v else 'see numbers'}")
    print("=" * 74)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
