#!/usr/bin/env python3
"""WP104 -- is case 3 REACHABLE at all?  A top-free, cofinal-capable model class.

Replaces wp101, which the cold review (F1) showed was 100% artifact: its
cofinite branch drew Reg(True, empty) = N, the whole universe, in 37.8% of
models, reintroducing exactly the maximal element wp100 died of.

WHY A NEW REPRESENTATION IS NEEDED -- and this is the deeper point.  In the
finite/cofinite class a cofinite region N\\S contains {0..i} iff i < min(S), so
EVERY cofinite region reaches only a BOUNDED prefix of the chain.  The only
region above cofinally many chain nodes is N itself.  So refusing N (the obvious
fix) makes cofinal witnesses UNREPRESENTABLE rather than rare, which is why the
referee measured an empty qualifying population.  The class could not reach the
question either way.

THE CLASS USED HERE.  Eventually-periodic subsets of N:

    R = (T, X)   with   n in R  iff  (n mod P in T)  XOR  (n in X)

T a set of residues mod P, X a finite exception set.  Subset/disjointness are
decidable by checking the finite set X_A u X_B pointwise and the residue sets
otherwise.  This class has what the old one lacked:

  * an infinite ascending chain            a_i = {0, P, 2P, ..., iP}  (T empty)
  * a region above the WHOLE chain         E = (T={0}, X empty)
      -- infinite, infinite complement, and NOT a top: anything whose T contains
         a nonzero residue is not below it
  * regions of BOUNDED reach               T empty, X a finite prefix + extras
  * and NO forced maximum -- part R checks this directly, per model

REPRESENTABILITY AUDIT FIRST (part R), before any rate is quoted.  That is the
discipline the six artifacts of wp100/wp101 cost.

Self-contained: the RCC5 relations are re-derived from the set semantics of this
class.
"""

import random
from itertools import combinations

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
ATOMS = [DR, PO, EQ, PP, PPI]
P = 4                                  # the period


class Reg:
    """Eventually-periodic subset of N: (T residues mod P, X finite exceptions)."""
    __slots__ = ("T", "X")

    def __init__(self, T, X):
        self.T, self.X = frozenset(T), frozenset(X)

    def has(self, n):
        return ((n % P) in self.T) != (n in self.X)

    def __eq__(self, o):
        return self.T == o.T and self.X == o.X

    def __hash__(self):
        return hash((self.T, self.X))

    def __repr__(self):
        return f"({sorted(self.T)}|{sorted(self.X)})"

    def infinite(self):
        return bool(self.T)

    def cofinite_complement_finite(self):
        return len(self.T) == P


def _pts(a, b):
    return a.X | b.X


def sub(a, b):
    if not (a.T <= b.T):
        return False
    return all((not a.has(n)) or b.has(n) for n in _pts(a, b))


def disj(a, b):
    if a.T & b.T:
        return False
    return all(not (a.has(n) and b.has(n)) for n in _pts(a, b))


def nonempty(a):
    return bool(a.T) or bool(a.X)


def rel(a, b):
    if a == b:
        return EQ
    if sub(a, b):
        return PP
    if sub(b, a):
        return PPI
    if disj(a, b):
        return DR
    return PO


# ------------------------------------------------- the certified comp table
def _rel_fin(a, b):
    if a == b:
        return EQ
    if a < b:
        return PP
    if b < a:
        return PPI
    if not (a & b):
        return DR
    return PO


def comp_table(n=4):
    regs = [frozenset(c) for k in range(1, n + 1)
            for c in combinations(range(n), k)]
    t = {}
    for a in regs:
        for b in regs:
            r = _rel_fin(a, b)
            for c in regs:
                t.setdefault((r, _rel_fin(b, c)), set()).add(_rel_fin(a, c))
    return t


CT = comp_table(4)


# ------------------------------------------------------------------ concepts
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
        closure(c[1], acc); closure(c[2], acc)
    elif k in ("ex", "all"):
        closure(c[2], acc)
    return acc


def rand_concept(rng, depth, natoms=2):
    if depth == 0 or rng.random() < 0.22:
        i = rng.randrange(natoms)
        return ("at", i) if rng.random() < 0.6 else ("nat", i)
    r = rng.random()
    if r < 0.16:
        return ("and", rand_concept(rng, depth - 1, natoms),
                rand_concept(rng, depth - 1, natoms))
    if r < 0.28:
        return ("or", rand_concept(rng, depth - 1, natoms),
                rand_concept(rng, depth - 1, natoms))
    if r < 0.74:
        rr = PP if rng.random() < 0.55 else rng.choice(ATOMS)
        return ("ex", rr, rand_concept(rng, depth - 1, natoms))
    return ("all", rng.choice([DR, PP, PPI, EQ]),
            rand_concept(rng, depth - 1, natoms))


# ------------------------------------------------------- the model and exact sat
class Model:
    """Chain a_i = {0,P,...,iP} (T empty), plus a finite side set."""

    def __init__(self, per, chain_val, sides, side_val, stab):
        self.per, self.chain_val = per, chain_val
        self.sides, self.side_val, self._stab = sides, side_val, stab
        self._memo = {}

    def a(self, i):
        return Reg(set(), {P * j for j in range(i + 1)})

    def rel_cs(self, i, j):
        return rel(self.a(i), self.sides[j])

    def rel_ss(self, j, k):
        return rel(self.sides[j], self.sides[k])

    def sat_side(self, j, c, hi):
        key = ("s", j, c)
        if key in self._memo:
            return self._memo[key]
        k = c[0]
        if k == "at":
            v = self.side_val.get((c[1], j), False)
        elif k == "nat":
            v = not self.side_val.get((c[1], j), False)
        elif k == "and":
            v = self.sat_side(j, c[1], hi) and self.sat_side(j, c[2], hi)
        elif k == "or":
            v = self.sat_side(j, c[1], hi) or self.sat_side(j, c[2], hi)
        else:
            r, x = c[1], c[2]
            hit_s = any(self.rel_ss(j, m) == r and self.sat_side(m, x, hi)
                        for m in range(len(self.sides)))
            all_s = all(self.sat_side(m, x, hi)
                        for m in range(len(self.sides)) if self.rel_ss(j, m) == r)
            conv = {DR: DR, PO: PO, EQ: EQ, PP: PPI, PPI: PP}[r]
            ch = [i for i in range(hi) if self.rel_cs(i, j) == conv]
            hit_c = any(self.sat_chain(i, x, hi) for i in ch)
            all_c = all(self.sat_chain(i, x, hi) for i in ch)
            v = (hit_s or hit_c) if k == "ex" else (all_s and all_c)
        self._memo[key] = v
        return v

    def sat_chain(self, i, c, hi):
        key = ("c", i, c)
        if key in self._memo:
            return self._memo[key]
        k = c[0]
        if k == "at":
            v = self.chain_val.get((c[1], i % self.per), False)
        elif k == "nat":
            v = not self.chain_val.get((c[1], i % self.per), False)
        elif k == "and":
            v = self.sat_chain(i, c[1], hi) and self.sat_chain(i, c[2], hi)
        elif k == "or":
            v = self.sat_chain(i, c[1], hi) or self.sat_chain(i, c[2], hi)
        else:
            r, x = c[1], c[2]
            if r == PP:
                hit_ch = any(self.sat_chain(j, x, hi) for j in range(i + 1, hi))
                all_ch = all(self.sat_chain(j, x, hi) for j in range(i + 1, hi))
            elif r == PPI:
                hit_ch = any(self.sat_chain(j, x, hi) for j in range(i))
                all_ch = all(self.sat_chain(j, x, hi) for j in range(i))
            elif r == EQ:
                hit_ch = all_ch = self.sat_chain(i, x, hi)
            else:
                hit_ch, all_ch = False, True
            sj = [j for j in range(len(self.sides)) if self.rel_cs(i, j) == r]
            hit_s = any(self.sat_side(j, x, hi) for j in sj)
            all_s = all(self.sat_side(j, x, hi) for j in sj)
            v = (hit_ch or hit_s) if k == "ex" else (all_ch and all_s)
        self._memo[key] = v
        return v


def build_model(rng, natoms=2, nsides=6, per=3, stab=6):
    sides = []
    guard = 0
    while len(sides) < nsides and guard < 400:
        guard += 1
        u = rng.random()
        if u < 0.34:
            # COFINAL reach: T contains residue 0, so it holds every chain point
            T = {0} | set(rng.sample(range(1, P), rng.randint(0, P - 2)))
            r = Reg(T, set(rng.sample(range(0, 40), rng.randint(0, 2))))
        elif u < 0.67:
            # BOUNDED reach: T omits residue 0, chain points only via X
            T = set(rng.sample(range(1, P), rng.randint(0, P - 1)))
            M = rng.randint(1, 8)
            r = Reg(T, {P * j for j in range(M + 1)} |
                    set(rng.sample(range(41, 80), rng.randint(0, 2))))
        else:
            # generic
            T = set(rng.sample(range(P), rng.randint(0, P - 1)))
            r = Reg(T, set(rng.sample(range(0, 60), rng.randint(0, 4))))
        if nonempty(r) and r not in sides:
            sides.append(r)
    chain_val = {(a, t): rng.random() < 0.5
                 for a in range(natoms) for t in range(per)}
    side_val = {(a, j): rng.random() < 0.5
                for a in range(natoms) for j in range(len(sides))}
    return Model(per, chain_val, sides, side_val, stab)


def has_top(m, hi=40):
    """A region above EVERY other domain element -- what wp101 failed to exclude."""
    for j in range(len(m.sides)):
        s = m.sides[j]
        if all(rel(m.a(i), s) == PP for i in range(hi)) and \
           all(rel(m.sides[k], s) in (PP, EQ) for k in range(len(m.sides))):
            return True
    return False


# --------------------------------------------------------------------- parts
def part_r(trials=3000, seed=104104):
    """REPRESENTABILITY AUDIT -- run before any rate is quoted."""
    print("PART R -- what can this class represent, and does it have a top?")
    rng = random.Random(seed)
    tops = cofinal = bounded = both = 0
    for _ in range(trials):
        m = build_model(rng)
        if has_top(m):
            tops += 1
        cof = [j for j in range(len(m.sides))
               if all(rel(m.a(i), m.sides[j]) == PP for i in range(40))]
        bnd = [j for j in range(len(m.sides))
               if rel(m.a(0), m.sides[j]) == PP
               and any(rel(m.a(i), m.sides[j]) != PP for i in range(40))]
        if cof:
            cofinal += 1
        if bnd:
            bounded += 1
        if cof and bnd:
            both += 1
    print(f"  models sampled                              : {trials}")
    print(f"    containing a TOP (above everything)       : {tops}"
          f"  ({100*tops/trials:5.1f}%)   <- wp101's defect")
    print(f"    containing a COFINAL-reach region         : {cofinal}"
          f"  ({100*cofinal/trials:5.1f}%)")
    print(f"    containing a BOUNDED-reach region         : {bounded}"
          f"  ({100*bounded/trials:5.1f}%)")
    print(f"    containing BOTH                           : {both}"
          f"  ({100*both/trials:5.1f}%)")
    print("  A class that can represent both, with no top, is the minimum")
    print("  needed to reach the case-3 question at all.")
    return tops == 0 and cofinal > 0 and bounded > 0


def cofinal_oneshot(m, c0, hi, WIN):
    """Demands that are cofinally recurring AND one-shot, on the chain."""
    out = []
    for d in closure(c0):
        if d[0] != "ex" or d[1] != PP:
            continue
        occ = [i for i in range(m._stab, m._stab + WIN)
               if m.sat_chain(i, d, hi)
               and not m.sat_chain(i, ("all", PP, d), hi)]
        if not occ or len([i for i in occ
                           if i > m._stab + 3 * WIN // 4]) < m.per:
            continue
        out.append(d[2])
    return out


def part_a(trials=4000, seed=205205):
    print("\nPART A -- are cofinally recurring ONE-SHOT demands REACHABLE?")
    print("  (the referee's question: in a top-free class, does the")
    print("   qualifying population exist at all?)")
    rng = random.Random(seed)
    hi, WIN = 40, 24
    models = withtop = found = 0
    persistent = oneshot = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build_model(rng)
        if has_top(m):
            withtop += 1
            continue
        models += 1
        for d in closure(c0):
            if d[0] != "ex" or d[1] != PP:
                continue
            for i in range(m._stab, m._stab + 2 * m.per):
                if not m.sat_chain(i, d, hi):
                    continue
                if m.sat_chain(i, ("all", PP, d), hi):
                    persistent += 1
                else:
                    oneshot += 1
        if cofinal_oneshot(m, c0, hi, WIN):
            found += 1
    tot = persistent + oneshot
    print(f"  top-free models examined                 : {models}"
          f"   (rejected for having a top: {withtop})")
    if tot:
        print(f"  chain-node exists-PP demands             : {tot}")
        print(f"    PERSISTENT                             : {persistent:6d}"
              f"  ({100*persistent/tot:5.1f}%)")
        print(f"    ONE-SHOT                               : {oneshot:6d}"
              f"  ({100*oneshot/tot:5.1f}%)")
    print(f"  models with a COFINALLY RECURRING one-shot demand : {found}"
          f"  ({100*found/max(models,1):5.1f}%)")
    return models > 0


def part_b(trials=4000, seed=306306):
    print("\nPART B -- for those, which branch of the section 49 trichotomy?")
    rng = random.Random(seed)
    hi, WIN = 40, 24
    inkernel = cofinal_ext = case3 = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build_model(rng)
        if has_top(m):
            continue
        for X in cofinal_oneshot(m, c0, hi, WIN):
            if len([k for k in range(m._stab, m._stab + WIN)
                    if m.sat_chain(k, X, hi)]) >= 3:
                inkernel += 1
                continue
            cof = [j for j in range(len(m.sides))
                   if m.sat_side(j, X, hi)
                   and all(rel(m.a(i), m.sides[j]) == PP
                           for i in range(m._stab, m._stab + WIN))]
            if cof:
                cofinal_ext += 1
            else:
                case3 += 1
    tot = inkernel + cofinal_ext + case3
    print(f"  cofinally recurring one-shot demands : {tot}")
    if tot:
        print(f"    branch 1  in-kernel                : {inkernel:5d}"
              f"  ({100*inkernel/tot:5.1f}%)")
        print(f"    branch 2  one cofinal external     : {cofinal_ext:5d}"
              f"  ({100*cofinal_ext/tot:5.1f}%)")
        print(f"    branch 3  NEITHER                  : {case3:5d}"
              f"  ({100*case3/tot:5.1f}%)  <- needs the cap")
    print("  Branch 3 nonzero => the cap machinery (sections 50-68) is NEEDED.")
    print("  Branch 3 zero    => the mixed quadrant may close on 1-2 alone.")
    return tot > 0


def main():
    print("=" * 74)
    print("WP104 -- is case 3 reachable?  top-free, cofinal-capable class")
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
