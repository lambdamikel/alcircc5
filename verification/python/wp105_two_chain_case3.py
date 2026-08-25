#!/usr/bin/env python3
"""WP105 -- case 3 reachability over a class with NO MAXIMAL ELEMENT ABOVE THE CHAIN.

THE GENERAL DIAGNOSIS (this probe exists because of it).  wp100, wp101 and
wp104-partA all reported ~100% one-shot, and all three have the SAME cause:

    a FINITE set of regions above the chain always contains a MAXIMAL element;
    a maximal element satisfies no exists-PP.X for any X;
    so every chain node beneath one fails forall-PP.exists-PP.D VACUOUSLY.

  wp100  : finite model            -> the model's top is maximal
  wp101  : N drawn as a side       -> N is maximal          (cold review, F1)
  wp104  : finite side set         -> 98.8% of top-free models still have a
                                      MAXIMAL side above the chain (measured)

Refusing the top (wp104's `has_top`) is not enough: it removes regions above
EVERYTHING while leaving regions above the CHAIN with nothing above them.  The
infinite chain escapes the problem; a finite side set cannot.

THE FIX.  The servers must form an infinite ascending family too.  Domain:

    a-chain   a_i = {0, P, ..., iP}                    (T empty)  -- the kernel
    s-chain   s_j = multiples of P, plus {1, 1+P, ..., 1+jP}      -- the servers
    low sides regions never above any a_i             (T inside {2,..,P-1})

Every a_i is below every s_j, every s_j is below s_{j+1}, so NOTHING above the
chain is maximal, and forall-PP.exists-PP.D can hold.  Part R checks exactly
that before any rate is quoted.

Self-contained; RCC5 relations re-derived from the set semantics of the class.
"""

import random

from wp104_topfree_case3 import (
    DR, PO, EQ, PP, PPI, P, Reg, rel, nonempty,
    mdepth, closure, rand_concept,
)


def a_reg(i):
    """Kernel chain: finite, residue-0 points only."""
    return Reg(set(), {P * k for k in range(i + 1)})


def b_reg(M):
    """BOUNDED-reach family: above a_i exactly for i <= M, and below every
    server, so it is never maximal.  This is the family wp105's first version
    lacked, which made branch 3 unrepresentable."""
    return Reg(set(), {P * k for k in range(M + 1)} | {1})


def s_reg(j):
    """Server chain: ALL residue-0 points, plus j+1 residue-1 points."""
    return Reg({0}, {1 + P * k for k in range(j + 1)})


class TwoChain:
    def __init__(self, pa, ps, aval, sval, lows, lval, stab, bs, bval):
        self.pa, self.ps, self.aval, self.sval = pa, ps, aval, sval
        self.lows, self.lval, self._stab = lows, lval, stab
        self.bs, self.bval = bs, bval           # bounded-reach family
        self._memo = {}

    def _arep(self, t):
        return self.pa * 3 + t

    def _srep(self, t):
        return self.ps * 3 + t

    # ---- relations
    def rel_al(self, i, t):
        return rel(a_reg(i), self.lows[t])

    def rel_sl(self, j, t):
        return rel(s_reg(j), self.lows[t])

    def rel_ll(self, t, u):
        return rel(self.lows[t], self.lows[u])

    # ---- satisfaction (closed form on both chains)
    def sat_a(self, i, c, hi):
        key = ("a", i, c)
        if key in self._memo:
            return self._memo[key]
        k = c[0]
        if k == "at":
            v = self.aval.get((c[1], i % self.pa), False)
        elif k == "nat":
            v = not self.aval.get((c[1], i % self.pa), False)
        elif k == "and":
            v = self.sat_a(i, c[1], hi) and self.sat_a(i, c[2], hi)
        elif k == "or":
            v = self.sat_a(i, c[1], hi) or self.sat_a(i, c[2], hi)
        else:
            r, x = c[1], c[2]
            if r == PP:
                # above a_i: higher a's (every a-residue recurs) and EVERY s
                hit = (any(self.sat_a(self._arep(t), x, hi)
                           for t in range(self.pa)) or
                       any(self.sat_s(self._srep(t), x, hi)
                           for t in range(self.ps)))
                alw = (all(self.sat_a(self._arep(t), x, hi)
                           for t in range(self.pa)) and
                       all(self.sat_s(self._srep(t), x, hi)
                           for t in range(self.ps)))
            elif r == PPI:
                hit = any(self.sat_a(t, x, hi) for t in range(i))
                alw = all(self.sat_a(t, x, hi) for t in range(i))
            elif r == EQ:
                hit = alw = self.sat_a(i, x, hi)
            else:
                hit, alw = False, True
            lt = [t for t in range(len(self.lows)) if self.rel_al(i, t) == r]
            hit = hit or any(self.sat_l(t, x, hi) for t in lt)
            alw = alw and all(self.sat_l(t, x, hi) for t in lt)
            bt = [u for u in range(len(self.bs))
                  if rel(a_reg(i), b_reg(self.bs[u])) == r]
            hit = hit or any(self.sat_b(u, x, hi) for u in bt)
            alw = alw and all(self.sat_b(u, x, hi) for u in bt)
            v = hit if k == "ex" else alw
        self._memo[key] = v
        return v

    def sat_b(self, u, c, hi):
        key = ("b", u, c)
        if key in self._memo:
            return self._memo[key]
        M = self.bs[u]
        k = c[0]
        if k == "at":
            v = self.bval.get((c[1], u), False)
        elif k == "nat":
            v = not self.bval.get((c[1], u), False)
        elif k == "and":
            v = self.sat_b(u, c[1], hi) and self.sat_b(u, c[2], hi)
        elif k == "or":
            v = self.sat_b(u, c[1], hi) or self.sat_b(u, c[2], hi)
        else:
            r, x = c[1], c[2]
            tgt = []
            for u2 in range(len(self.bs)):
                if u2 != u and rel(b_reg(M), b_reg(self.bs[u2])) == r:
                    tgt.append(("b", u2))
            for t in range(self.ps):
                if rel(b_reg(M), s_reg(self._srep(t))) == r:
                    tgt.append(("s", self._srep(t)))
            for i in range(hi):
                if rel(b_reg(M), a_reg(i)) == r:
                    tgt.append(("a", i))
            for t in range(len(self.lows)):
                if rel(b_reg(M), self.lows[t]) == r:
                    tgt.append(("l", t))
            f = {"a": self.sat_a, "s": self.sat_s, "l": self.sat_l,
                 "b": self.sat_b}
            hit = any(f[kk](ii, x, hi) for kk, ii in tgt)
            alw = all(f[kk](ii, x, hi) for kk, ii in tgt)
            v = hit if k == "ex" else alw
        self._memo[key] = v
        return v

    def sat_s(self, j, c, hi):
        key = ("s", j, c)
        if key in self._memo:
            return self._memo[key]
        k = c[0]
        if k == "at":
            v = self.sval.get((c[1], j % self.ps), False)
        elif k == "nat":
            v = not self.sval.get((c[1], j % self.ps), False)
        elif k == "and":
            v = self.sat_s(j, c[1], hi) and self.sat_s(j, c[2], hi)
        elif k == "or":
            v = self.sat_s(j, c[1], hi) or self.sat_s(j, c[2], hi)
        else:
            r, x = c[1], c[2]
            if r == PP:
                # every s-residue recurs above ANY j, so this does not depend
                # on j -- and crucially there is no top of the s-chain
                hit = any(self.sat_s(self._srep(t), x, hi)
                          for t in range(self.ps))
                alw = all(self.sat_s(self._srep(t), x, hi)
                          for t in range(self.ps))
            elif r == PPI:
                hit = (any(self.sat_s(t, x, hi) for t in range(j)) or
                       any(self.sat_a(t, x, hi) for t in range(hi)))
                alw = (all(self.sat_s(t, x, hi) for t in range(j)) and
                       all(self.sat_a(t, x, hi) for t in range(hi)))
            elif r == EQ:
                hit = alw = self.sat_s(j, x, hi)
            else:
                hit, alw = False, True
            lt = [t for t in range(len(self.lows)) if self.rel_sl(j, t) == r]
            hit = hit or any(self.sat_l(t, x, hi) for t in lt)
            alw = alw and all(self.sat_l(t, x, hi) for t in lt)
            bt = [u for u in range(len(self.bs))
                  if rel(s_reg(j), b_reg(self.bs[u])) == r]
            hit = hit or any(self.sat_b(u, x, hi) for u in bt)
            alw = alw and all(self.sat_b(u, x, hi) for u in bt)
            v = hit if k == "ex" else alw
        self._memo[key] = v
        return v

    def sat_l(self, t, c, hi):
        key = ("l", t, c)
        if key in self._memo:
            return self._memo[key]
        k = c[0]
        if k == "at":
            v = self.lval.get((c[1], t), False)
        elif k == "nat":
            v = not self.lval.get((c[1], t), False)
        elif k == "and":
            v = self.sat_l(t, c[1], hi) and self.sat_l(t, c[2], hi)
        elif k == "or":
            v = self.sat_l(t, c[1], hi) or self.sat_l(t, c[2], hi)
        else:
            r, x = c[1], c[2]
            conv = {DR: DR, PO: PO, EQ: EQ, PP: PPI, PPI: PP}[r]
            ai = [i for i in range(hi) if self.rel_al(i, t) == conv]
            sj = [j for j in range(hi) if self.rel_sl(j, t) == conv]
            lu = [u for u in range(len(self.lows)) if self.rel_ll(t, u) == r]
            bu = [u for u in range(len(self.bs))
                  if rel(self.lows[t], b_reg(self.bs[u])) == r]
            hit = (any(self.sat_a(i, x, hi) for i in ai) or
                   any(self.sat_s(j, x, hi) for j in sj) or
                   any(self.sat_l(u, x, hi) for u in lu) or
                   any(self.sat_b(u, x, hi) for u in bu))
            alw = (all(self.sat_a(i, x, hi) for i in ai) and
                   all(self.sat_s(j, x, hi) for j in sj) and
                   all(self.sat_l(u, x, hi) for u in lu) and
                   all(self.sat_b(u, x, hi) for u in bu))
            v = hit if k == "ex" else alw
        self._memo[key] = v
        return v


def build(rng, natoms=2, nlow=3, pa=3, ps=2, stab=4):
    lows = []
    guard = 0
    while len(lows) < nlow and guard < 200:
        guard += 1
        T = set(rng.sample(range(2, P), rng.randint(0, P - 2)))
        pts = [n for n in range(2, 40) if n % P >= 2]
        r = Reg(T, set(rng.sample(pts, rng.randint(1, 3))))
        if nonempty(r) and r not in lows:
            lows.append(r)
    aval = {(a, t): rng.random() < 0.5 for a in range(natoms) for t in range(pa)}
    sval = {(a, t): rng.random() < 0.5 for a in range(natoms) for t in range(ps)}
    lval = {(a, t): rng.random() < 0.5 for a in range(natoms)
            for t in range(len(lows))}
    bs = sorted(rng.sample(range(stab, stab + 8), rng.randint(2, 4)))
    bval = {(a, u): rng.random() < 0.5 for a in range(natoms)
            for u in range(len(bs))}
    return TwoChain(pa, ps, aval, sval, lows, lval, stab, bs, bval)


# --------------------------------------------------------------------- parts
def part_r(trials=400):
    print("PART R -- REPRESENTABILITY AUDIT (run before any rate is quoted)")
    ok_nomax = ok_cofinal = 0
    bad = None
    for i in range(trials):
        m = build(random.Random(1000 + i))
        # (1) is anything above the chain maximal?
        maximal = False
        for j in range(12):
            if not any(rel(s_reg(j), s_reg(j2)) == PP for j2 in range(j + 1, 14)):
                maximal = True
        for t in range(len(m.lows)):
            if rel(a_reg(m._stab), m.lows[t]) == PP:
                up = (any(rel(m.lows[t], m.lows[u]) == PP
                          for u in range(len(m.lows))) or
                      any(rel(m.lows[t], s_reg(j)) == PP for j in range(14)) or
                      any(rel(m.lows[t], a_reg(i2)) == PP for i2 in range(14)))
                if not up:
                    maximal = True
                    bad = ("low side above the chain with nothing above it", t)
        if not maximal:
            ok_nomax += 1
        if all(rel(a_reg(i2), s_reg(0)) == PP for i2 in range(14)):
            ok_cofinal += 1
    print(f"  models sampled                                  : {trials}")
    print(f"    NO maximal element above the chain            : {ok_nomax}"
          f"  ({100*ok_nomax/trials:5.1f}%)")
    print(f"    a COFINAL server exists (s_0 above every a_i) : {ok_cofinal}"
          f"  ({100*ok_cofinal/trials:5.1f}%)")
    if bad:
        print(f"    (residual defect seen: {bad[0]})")
    # branch-3 representability: bounded-reach regions ABOVE the chain
    reach = 0
    for i in range(trials):
        m = build(random.Random(1000 + i))
        if any(rel(a_reg(m._stab), b_reg(M)) == PP and
               any(rel(a_reg(i2), b_reg(M)) != PP for i2 in range(14))
               for M in m.bs):
            reach += 1
    print(f"    BOUNDED-reach region ABOVE the chain          : {reach}"
          f"  ({100*reach/trials:5.1f}%)   <- branch 3 needs this")
    print("  All three must hold for the case-3 question to be REACHABLE:")
    print("  no maximal element above the chain (else 100% one-shot), a")
    print("  cofinal server family (else branch 2 is unrepresentable), and")
    print("  bounded-reach regions above the chain (else branch 3 is).")
    return ok_nomax == trials and ok_cofinal == trials and reach > 0


def part_a(trials=1500, seed=555):
    print("\nPART A -- VALIDITY: do PERSISTENT demands now appear?")
    rng = random.Random(seed)
    hi = 14
    per = one = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build(rng)
        for d in closure(c0):
            if d[0] != "ex" or d[1] != PP:
                continue
            for i in range(m._stab, m._stab + 2 * m.pa):
                if not m.sat_a(i, d, hi):
                    continue
                if m.sat_a(i, ("all", PP, d), hi):
                    per += 1
                else:
                    one += 1
    tot = per + one
    print(f"  chain-node exists-PP demands : {tot}")
    if tot:
        print(f"    PERSISTENT                 : {per:6d}  ({100*per/tot:5.1f}%)")
        print(f"    ONE-SHOT                   : {one:6d}  ({100*one/tot:5.1f}%)")
    print("  wp100/101/104 all reported ~100% one-shot for the SAME structural")
    print("  reason.  A nonzero persistent rate here is the first evidence any")
    print("  of these classes has offered that the distinction is measurable.")
    return tot > 0 and per > 0


def part_b(trials=1500, seed=666):
    print("\nPART B -- the section 49 trichotomy, on a class that can express it")
    rng = random.Random(seed)
    hi = 14
    ink = cof = c3 = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build(rng)
        for d in closure(c0):
            if d[0] != "ex" or d[1] != PP:
                continue
            occ = [i for i in range(m._stab, m._stab + 6)
                   if m.sat_a(i, d, hi)
                   and not m.sat_a(i, ("all", PP, d), hi)]
            if len(occ) < 4:
                continue
            X = d[2]
            if len([k for k in range(m._stab, hi) if m.sat_a(k, X, hi)]) >= 2:
                ink += 1
            elif any(m.sat_s(j, X, hi) for j in range(hi)):
                cof += 1
            else:
                c3 += 1
    tot = ink + cof + c3
    print(f"  cofinally recurring one-shot demands : {tot}")
    if tot:
        print(f"    branch 1  in-kernel              : {ink:5d}  ({100*ink/tot:5.1f}%)")
        print(f"    branch 2  cofinal server         : {cof:5d}  ({100*cof/tot:5.1f}%)")
        print(f"    branch 3  NEITHER                : {c3:5d}  ({100*c3/tot:5.1f}%)")
    print("  Branch 3 nonzero => the cap machinery (sections 50-68) is NEEDED.")
    return tot > 0


def main():
    print("=" * 74)
    print("WP105 -- case 3 over a class with no maximal element above the chain")
    print("=" * 74)
    ok = part_r()
    print(f"\n  [class audit {'PASSES' if ok else 'FAILS'} -- rates below are"
          f" {'meaningful' if ok else 'NOT to be quoted'}]")
    part_a()
    part_b()
    print("\n" + "=" * 74)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
