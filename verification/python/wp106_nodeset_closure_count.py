#!/usr/bin/env python3
"""WP106 -- items A and C: is the node set CLOSED at its frontier, and COUNTED?

ASSEMBLY_DESIGN sec. 82.  Everything downstream of a valid COUNTED certificate is
certified (secs. 74-76, 81).  What is not is the node set itself:

  A  CLOSED    -- every demand at a node of the set is served inside it
  C  COUNTED   -- its size stays inside a bound computed from C0 alone

These pull against each other: closing under demands GROWS the set, bounding it
TRUNCATES.  Sec. 49's trichotomy and sec. 52's cut exist to resolve that, and
this probe measures whether they do, on models that can express the question.

WHAT THE CONSTRUCTION ACTUALLY NEEDS.  By sec. 49's split, a node's demands
divide:

  * PERSISTENT vertical demands  -> served by the node's own KERNEL (rr_covers,
    certified).  These need NO node in the set.
  * ONE-SHOT vertical demands and all horizontal ones -> need a WITNESS NODE
    inside the set.

So closure = every one-shot/horizontal demand's witness lies in the closure at
the chosen fuel.  That is what part A measures, and part C measures the size.

MODEL CLASS: wp105's two-chain class, which passes its own audit -- no maximal
element above the chain (else 100% of demands read one-shot: wp100/101/104), a
cofinal server family, and bounded-reach regions above the chain.  Part R
re-runs that audit here rather than trusting it.
"""

import random

from wp104_topfree_case3 import DR, PO, EQ, PP, PPI, P, Reg, rel, closure, mdepth
from wp105_two_chain_case3 import a_reg, s_reg, b_reg, build, rand_concept


HI = 14


# ---------------------------------------------------------------- the domain
def domain(m, na=30, ns=25):
    """(kind, index) for every node the probe considers.

    ⚠ The chains are INFINITE and this truncates them.  With na=8, ns=6 a first
    run reported closure plateauing at 93% -- and 26 of the 28 apparently
    unserved demands had their witness just OUTSIDE the truncation.  Widened to
    na=30, ns=25 and re-measured; the truncation check is part of the probe
    (part T) rather than a note."""
    d = [("a", i) for i in range(na)] + [("s", j) for j in range(ns)]
    d += [("b", u) for u in range(len(m.bs))]
    d += [("l", t) for t in range(len(m.lows))]
    return d


def reg_of(m, nd):
    k, i = nd
    if k == "a":
        return a_reg(i)
    if k == "s":
        return s_reg(i)
    if k == "b":
        return b_reg(m.bs[i])
    return m.lows[i]


def sat_of(m, nd, c):
    k, i = nd
    if k == "a":
        return m.sat_a(i, c, HI)
    if k == "s":
        return m.sat_s(i, c, HI)
    if k == "b":
        return m.sat_b(i, c, HI)
    return m.sat_l(i, c, HI)


def mty(m, nd, c0):
    return [d for d in closure(c0) if sat_of(m, nd, d)]


def mtk(m, nd, c0, bud):
    return [d for d in mty(m, nd, c0) if mdepth(d) <= bud]


def persistent(m, nd, D):
    """A vertical demand is persistent iff its forall-PP guard holds."""
    return sat_of(m, nd, ("all", PP, ("ex", PP, D)))


def kernel_served(m, nd, r, D):
    """Does the node's OWN KERNEL serve this vertical demand?

    Section 49 gives TWO ways, and a first version of this probe implemented only
    the first -- which is why it reported a closure gap that was really the
    construction being modelled wrong:

      * PERSISTENT  -> round-robin (`rr_covers`), the guard holds;
      * ONE-SHOT but the demanded concept RECURS ON THE CHAIN
        (`oneshot_in_kernel`) -> a higher chain node carries it, and the chain
        IS the kernel, so no new node is needed.

    The second is section 49's branch 1, measured at ~90% of cofinally recurring
    one-shot demands in wp105.  Omitting it makes every ascending chain look
    like an unbounded closure."""
    if r not in (PP, PPI):
        return False
    if persistent(m, nd, D):
        return True
    k, i = nd
    if k not in ("a", "s"):
        return False
    # the demanded concept recurs further along the node's own chain
    rng = range(i + 1, i + 20)
    if k == "a":
        return any(m.sat_a(j, D, HI) for j in rng)
    return any(m.sat_s(j, D, HI) for j in rng)


# ------------------------------------------------------ the node-set closure
def node_closure(m, c0, root, fuel, dom):
    """mixNodes-style: follow every demand's witness, budget dropping on
    horizontal steps and held on vertical ones (ppWitness_bud)."""
    seen = {(root, mdepth(c0))}
    frontier = [(root, mdepth(c0))]
    steps = 0
    while frontier and steps < fuel:
        steps += 1
        nxt = []
        for nd, bud in frontier:
            for d in mtk(m, nd, c0, bud):
                if d[0] != "ex":
                    continue
                r, D = d[1], d[2]
                if kernel_served(m, nd, r, D):
                    continue                      # the kernel serves it
                for w in dom:
                    if rel(reg_of(m, nd), reg_of(m, w)) == r and sat_of(m, w, D):
                        nb = bud if r in (PP, PPI) else bud - 1
                        if nb >= 0 and (w, nb) not in seen:
                            seen.add((w, nb))
                            nxt.append((w, nb))
                        break
        frontier = nxt
    return seen


def unserved(m, c0, S, dom):
    """Demands at set members with no witness inside the set."""
    bad = 0
    tot = 0
    for nd, bud in S:
        for d in mtk(m, nd, c0, bud):
            if d[0] != "ex":
                continue
            r, D = d[1], d[2]
            if kernel_served(m, nd, r, D):
                continue
            tot += 1
            ok = any(rel(reg_of(m, nd), reg_of(m, w)) == r and sat_of(m, w, D)
                     for (w, _) in S)
            if not ok:
                bad += 1
    return bad, tot


# --------------------------------------------------------------------- parts
def part_r(trials=200):
    print("PART R -- re-run wp105's class audit here rather than trust it")
    nomax = cof = bnd = 0
    for i in range(trials):
        m = build(random.Random(9000 + i))
        if not any(not any(rel(s_reg(j), s_reg(j2)) == PP
                           for j2 in range(j + 1, HI)) for j in range(HI - 2)):
            nomax += 1
        if all(rel(a_reg(i2), s_reg(0)) == PP for i2 in range(HI)):
            cof += 1
        if any(rel(a_reg(0), b_reg(M)) == PP and
               any(rel(a_reg(i2), b_reg(M)) != PP for i2 in range(HI))
               for M in m.bs):
            bnd += 1
    print(f"  no maximal element above the chain : {nomax}/{trials}")
    print(f"  cofinal server present             : {cof}/{trials}")
    print(f"  bounded-reach region above chain   : {bnd}/{trials}")
    ok = nomax == trials and cof == trials and bnd == trials
    print(f"  audit {'PASSES' if ok else 'FAILS'}")
    return ok


def part_a(trials=250, seed=606):
    print("\nPART A -- is the closure CLOSED, and at what fuel?")
    rng = random.Random(seed)
    rows = {}
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build(rng)
        dom = domain(m)
        roots = [nd for nd in dom if sat_of(m, nd, c0)]
        if not roots:
            continue
        root = roots[0]
        for fuel in (1, 2, 3, 4, 6, 8):
            S = node_closure(m, c0, root, fuel, dom)
            bad, tot = unserved(m, c0, S, dom)
            key = fuel
            r = rows.setdefault(key, [0, 0, 0, 0])
            r[0] += 1
            r[1] += (1 if bad == 0 else 0)
            r[2] += bad
            r[3] += len(S)
    print(f"  {'fuel':>5} {'cases':>7} {'CLOSED':>8} {'unserved':>9} {'mean |S|':>9}")
    for f in sorted(rows):
        n, cl, bad, sz = rows[f]
        print(f"  {f:5d} {n:7d} {cl:8d} {bad:9d} {sz/max(n,1):9.1f}")
    print("  CLOSED = every one-shot/horizontal demand at every set member has")
    print("  its witness inside the set.  Persistent vertical demands are")
    print("  excluded: sec. 49 serves those from the node's own kernel.")
    return rows


def part_c(rows, trials=250, seed=707):
    print("\nPART C -- the count against a C0-computed bound")
    rng = random.Random(seed)
    over = tot = 0
    worst = (0, 0)
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build(rng)
        dom = domain(m)
        roots = [nd for nd in dom if sat_of(m, nd, c0)]
        if not roots:
            continue
        S = node_closure(m, c0, roots[0], 8, dom)
        cl = len(closure(c0))
        bound = (cl + 1) ** max(mdepth(c0), 1)
        tot += 1
        if len(S) > bound:
            over += 1
        if len(S) / max(bound, 1) > worst[0] / max(worst[1], 1):
            worst = (len(S), bound)
    print(f"  closures measured               : {tot}")
    print(f"  exceeding (|cl C0|+1)^mdepth    : {over}")
    print(f"  worst |S| vs bound              : {worst[0]} vs {worst[1]}")
    print("  The certificate's own bound is mixKT C0 = mixBound C0 |typeEnum| ")
    print("  mdepth, which is far larger; this is the tighter comparison.")
    return over == 0


def part_t(trials=250, seed=606):
    """Is any remaining unservedness a TRUNCATION artifact?"""
    print("\nPART T -- truncation check (the first run's 93% was 93% artifact)")
    rng = random.Random(seed)
    def wide(m, na=60, ns=50):
        d = [("a", i) for i in range(na)] + [("s", j) for j in range(ns)]
        d += [("b", u) for u in range(len(m.bs))]
        d += [("l", t) for t in range(len(m.lows))]
        return d
    art = realgap = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build(rng)
        dom = domain(m); W = wide(m)
        roots = [nd for nd in dom if sat_of(m, nd, c0)]
        if not roots:
            continue
        S = node_closure(m, c0, roots[0], 8, dom)
        for nd, bud in S:
            for d in mtk(m, nd, c0, bud):
                if d[0] != "ex":
                    continue
                r, D = d[1], d[2]
                if kernel_served(m, nd, r, D):
                    continue
                if any(rel(reg_of(m, nd), reg_of(m, w)) == r and sat_of(m, w, D)
                       for (w, _) in S):
                    continue
                if any(rel(reg_of(m, nd), reg_of(m, w)) == r and sat_of(m, w, D)
                       for w in dom):
                    realgap += 1
                elif any(rel(reg_of(m, nd), reg_of(m, w)) == r and
                         sat_of(m, w, D) for w in W):
                    art += 1
    print(f"  unserved, witness INSIDE the domain but unreached : {realgap}"
          f"   <- real")
    print(f"  unserved, witness only outside the truncation     : {art}"
          f"   <- artifact")
    return realgap


def main():
    print("=" * 74)
    print("WP106 -- node set: closed (A) and counted (C)?")
    print("=" * 74)
    ok = part_r()
    print(f"\n  [rates below are {'meaningful' if ok else 'NOT to be quoted'}]")
    rows = part_a()
    part_t()
    part_c(rows)
    print("\n" + "=" * 74)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
