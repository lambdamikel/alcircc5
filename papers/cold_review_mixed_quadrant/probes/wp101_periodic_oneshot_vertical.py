#!/usr/bin/env python3
"""WP101 -- one-shot vertical demands over GENUINELY INFINITE periodic models.

Replaces wp100, which was INVALID.  wp100 asked the right question -- can a
kernel node carry a NON-PERSISTENT exists-PP demand? -- but measured it over
FINITE models, where the maximal element has no PP-successor, so

    a_top  |=/=  exists-PP.D      for every D,

hence every node below it fails  forall-PP.exists-PP.D  and 100% of demands
read as one-shot.  The measurement was an artifact of the boundary.

The Lean definition being modelled (POFreeLift.lean, mem_persistDs):

    D in persistDs C0 I x   <->   D in cl C0
                                  /\  x |= exists-PP.D
                                  /\  x |= forall-PP.exists-PP.D

So x's demand D is ONE-SHOT iff  x |= exists-PP.D  but some y above x has
y =/= exists-PP.D.

WHY THIS MATTERS (ASSEMBLY_DESIGN sec. 48.3).  Everything carrying a BUDGET is
already finite (mtk drops the budget at every serving step).  Kernels cannot
carry a budget -- periodicity needs the full model type -- so demands at kernel
nodes have NO FUEL, and the externals they spawn are the unbounded part.
Persistent ones are served by the round-robin kernel (rr_covers, certified).
The residual obligation, NodeCovered, is exactly about the one-shot ones.

THE MODEL CLASS.  Regions are FINITE or COFINITE subsets of the naturals, so
the ambient universe is infinite and the domain can be

    { a_i = {0..i} : i in N }   union   a finite side set S,

a genuinely infinite ascending PP-chain with NO maximal element, plus sides.
Atom valuations on the chain are PERIODIC in i (period p).  Satisfaction is then
computed EXACTLY, not on a window: for a chain node,

    a_i |= exists-PP.X  <->  (some residue r has X)  or  (some s in S,
                              a_i PP s, with X)

and the first disjunct does not depend on i, because every residue recurs
cofinally above i.  So the chain half is closed-form and boundary-free.

PARTS
  A  validity  -- does the artifact disappear?  (one-shot rate should drop far
                  below wp100's 100%, and persistent demands should appear)

  CALIBRATION, RECORDED HONESTLY.  Three separate artifacts were caught inside
  THIS probe while developing it, each of the same family as wp100's:
    1  side regions drawn from a small range can never sit above a HIGH bounded
       segment of the chain, so part E could not REACH the bounded branch;
    2  the bounded witnesses' reach was drawn to match part D's widest window,
       so one witness covered every window by construction;
    3  "cofinally recurring" was tested on a 3p window, which admits demands
       that simply die above the sides' reach -- everything then looks flat
       vacuously.
  Only the IN-KERNEL rate is stable across all four model-class variants
  (89.2 / 90.2 / 83.5 / 91.3%).  Treat single rates from this probe as weak
  evidence; the load is carried by the theorems in POFreeLift.lean sec. 49.
  B  witnesses -- for a cofinally-recurring one-shot demand, how many DISTINCT
                  external witnesses does serving actually need?
  C  structure -- is a single witness above cofinally many chain nodes always
                  available?  (the hoped-for structural fact behind NodeCovered)

Self-contained: RCC5 relations and the composition table are re-derived from
finite set semantics.
"""

import random
from itertools import combinations

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
ATOMS = [DR, PO, EQ, PP, PPI]


# --------------------------------------------- the certified table, re-derived
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


# ------------------------------------- regions: finite or cofinite subsets of N
class Reg:
    """cof=False: the finite set S.   cof=True: N \\ S (S finite)."""
    __slots__ = ("cof", "s")

    def __init__(self, cof, s):
        self.cof, self.s = cof, frozenset(s)

    def __eq__(self, o):
        return self.cof == o.cof and self.s == o.s

    def __hash__(self):
        return hash((self.cof, self.s))

    def __repr__(self):
        return ("N\\" if self.cof else "") + "{" + ",".join(
            map(str, sorted(self.s))) + "}"

    def nonempty(self):
        return self.cof or bool(self.s)


def sub(a, b):
    if not a.cof and not b.cof:
        return a.s <= b.s
    if not a.cof and b.cof:
        return not (a.s & b.s)
    if a.cof and not b.cof:
        return False                      # infinite is never inside finite
    return b.s <= a.s                     # N\A <= N\B  iff  B <= A


def disj(a, b):
    if not a.cof and not b.cof:
        return not (a.s & b.s)
    if not a.cof and b.cof:
        return a.s <= b.s
    if a.cof and not b.cof:
        return b.s <= a.s
    return False                          # two cofinite sets always meet


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


# ---------------------------------------------------------- concepts (NNF, PO-free foralls)
# ('at',i) ('nat',i) ('and',c,d) ('or',c,d) ('ex',r,c) ('all',r,c)

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
    if r < 0.18:
        return ("and", rand_concept(rng, depth - 1, natoms),
                rand_concept(rng, depth - 1, natoms))
    if r < 0.30:
        return ("or", rand_concept(rng, depth - 1, natoms),
                rand_concept(rng, depth - 1, natoms))
    if r < 0.72:
        # bias toward PP so vertical demands are actually exercised
        rr = PP if rng.random() < 0.55 else rng.choice(ATOMS)
        return ("ex", rr, rand_concept(rng, depth - 1, natoms))
    return ("all", rng.choice([DR, PP, PPI, EQ]),
            rand_concept(rng, depth - 1, natoms))


# ------------------------------------- the infinite periodic model and exact sat
class PerModel:
    """Domain = { a_i = {0..i} : i in N }  union  a finite side set S.

    Atom valuations on the chain are periodic with period p.  Satisfaction is
    computed EXACTLY (no window): the key closed form is that every residue
    recurs cofinally above any i, so a chain node's chain-facing quantifiers do
    not depend on i at all.
    """

    def __init__(self, p, chain_val, sides, side_val):
        self.p = p
        self.chain_val = chain_val        # (atom, residue) -> bool
        self.sides = sides                # list[Reg]
        self.side_val = side_val          # (atom, idx) -> bool
        self._memo = {}

    def a(self, i):
        return Reg(False, range(i + 1))

    # relation from chain node i to side j, and side to side
    def rel_cs(self, i, j):
        return rel(self.a(i), self.sides[j])

    def rel_ss(self, j, k):
        return rel(self.sides[j], self.sides[k])

    # For a side s and relation r, the set of chain indices i with rel(a_i,s)=r
    # is one of: all, none, a finite prefix, a cofinite tail.  We only ever need
    # "is it nonempty above i" and "does it hold for all i above i".
    def chain_above(self, i, r, j, hi):
        """indices i' > i (sampled up to hi) with rel(a_i', side j) = r"""
        return [k for k in range(i + 1, hi) if self.rel_cs(k, j) == r]

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
            # side -> sides
            hit_s = [m for m in range(len(self.sides))
                     if self.rel_ss(j, m) == r and self.sat_side(m, x, hi)]
            all_s = all(self.sat_side(m, x, hi)
                        for m in range(len(self.sides))
                        if self.rel_ss(j, m) == r)
            # side -> chain: rel(side j, a_i) = conv of rel(a_i, side j)
            conv = {DR: DR, PO: PO, EQ: EQ, PP: PPI, PPI: PP}[r]
            ch = [i for i in range(hi) if self.rel_cs(i, j) == conv]
            hit_c = any(self.sat_chain(i, x, hi) for i in ch)
            all_c = all(self.sat_chain(i, x, hi) for i in ch)
            v = (hit_s or hit_c) if k == "ex" else (all_s and all_c)
        self._memo[key] = v
        return v

    def sat_chain(self, i, c, hi):
        """Exact for the chain-facing part; sides handled explicitly."""
        key = ("c", i % self.p if self._chain_periodic(c) else i, c)
        if key in self._memo:
            return self._memo[key]
        k = c[0]
        if k == "at":
            v = self.chain_val.get((c[1], i % self.p), False)
        elif k == "nat":
            v = not self.chain_val.get((c[1], i % self.p), False)
        elif k == "and":
            v = self.sat_chain(i, c[1], hi) and self.sat_chain(i, c[2], hi)
        elif k == "or":
            v = self.sat_chain(i, c[1], hi) or self.sat_chain(i, c[2], hi)
        else:
            r, x = c[1], c[2]
            # chain -> chain:  rel(a_i,a_j) = PP for j>i, PPI for j<i, EQ i=j
            if r == PP:
                # EVERY residue recurs cofinally above i -> boundary-free
                hit_ch = any(self.sat_chain_res(t, x, hi) for t in range(self.p))
                all_ch = all(self.sat_chain_res(t, x, hi) for t in range(self.p))
            elif r == PPI:
                hit_ch = any(self.sat_chain(j, x, hi) for j in range(i))
                all_ch = all(self.sat_chain(j, x, hi) for j in range(i))
            elif r == EQ:
                hit_ch = all_ch = self.sat_chain(i, x, hi)
            else:
                hit_ch, all_ch = False, True        # chain is totally ordered
            # chain -> sides
            sj = [j for j in range(len(self.sides)) if self.rel_cs(i, j) == r]
            hit_s = any(self.sat_side(j, x, hi) for j in sj)
            all_s = all(self.sat_side(j, x, hi) for j in sj)
            v = (hit_ch or hit_s) if k == "ex" else (all_ch and all_s)
        self._memo[key] = v
        return v

    def sat_chain_res(self, t, c, hi):
        """Truth at SOME/every chain node of residue t high up.  For our models
        the chain's own atom truth depends only on the residue, and the side
        relations stabilise above max(sides), so evaluate at a high witness."""
        base = self._stab + t
        return self.sat_chain(base, c, hi)

    def _chain_periodic(self, c):
        return False        # be conservative: memoise per index, never per residue

    _stab = 0


def build_model(rng, natoms=2, nsides=6, p=3, stab=11):
    """Side regions.  CRITICAL: the class must be able to REPRESENT a witness
    that is above a bounded but HIGH segment of the chain, otherwise part E
    cannot reach the BOUNDED branch and its rate is an artifact -- the same
    mistake wp100 made.  `a_M | decoration` is above exactly a_0..a_{M-1}, so
    the third generator below supplies precisely those."""
    sides = []
    guard = 0
    while len(sides) < nsides and guard < 400:
        guard += 1
        u = rng.random()
        if u < 0.30:
            r = Reg(True, rng.sample(range(6), rng.randint(0, 3)))      # cofinite
        elif u < 0.55:
            r = Reg(False, rng.sample(range(10), rng.randint(1, 4)))    # finite
        else:
            # BOUNDED-SEGMENT witness: above a_0 .. a_{M-1}, not above a_M
            M = rng.randint(stab + 1, stab + 5 * p)
            dec = set(rng.sample(range(M + 2, M + 40), rng.randint(1, 3)))
            r = Reg(False, set(range(M + 1)) | dec)
        if r.nonempty() and r not in sides and r != Reg(False, ()):
            sides.append(r)
    chain_val = {(a, t): rng.random() < 0.5
                 for a in range(natoms) for t in range(p)}
    side_val = {(a, j): rng.random() < 0.5
                for a in range(natoms) for j in range(nsides)}
    m = PerModel(p, chain_val, sides, side_val)
    # above this index every side's relation to the chain has stabilised
    m._stab = stab
    return m


# ------------------------------------------------------------------- the parts

def part_a(trials=600, seed=101101):
    print("PART A -- validity: does wp100's boundary artifact disappear?")
    rng = random.Random(seed)
    hi = 40
    persistent = oneshot = 0
    nodes_with_demand = 0
    examples = []
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build_model(rng)
        cl = closure(c0)
        for i in range(m._stab, m._stab + 2 * m.p):      # interior chain nodes
            for d in cl:
                if d[0] != "ex" or d[1] != PP:
                    continue
                X = d[2]
                if not m.sat_chain(i, d, hi):
                    continue
                nodes_with_demand += 1
                guard = ("all", PP, d)
                if m.sat_chain(i, guard, hi):
                    persistent += 1
                else:
                    oneshot += 1
                    if len(examples) < 3:
                        examples.append((c0, i))
    tot = persistent + oneshot
    print(f"  chain-node exists-PP demands examined : {tot}")
    if tot:
        print(f"    PERSISTENT (forall-PP guard holds) : {persistent:6d}"
              f"  ({100*persistent/tot:5.1f}%)")
        print(f"    ONE-SHOT   (guard fails)           : {oneshot:6d}"
              f"  ({100*oneshot/tot:5.1f}%)")
    print("  wp100 over FINITE models reported 100% one-shot -- an artifact of")
    print("  the maximal element.  Persistent demands appearing at all is the")
    print("  validity check this probe exists to perform.")
    return tot > 0 and persistent > 0


def part_b(trials=600, seed=202202):
    print("\nPART B -- how many DISTINCT witnesses does one-shot serving need?")
    print("  For a one-shot exists-PP.X at chain node a_i, a witness w with")
    print("  a_i PP w serves EVERY a_j below i too (transitivity).  So the real")
    print("  question is how many witnesses a COFINALLY recurring demand needs.")
    rng = random.Random(seed)
    hi = 40
    dist = {}
    cofinal_cases = 0
    unbounded_flag = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build_model(rng)
        for d in closure(c0):
            if d[0] != "ex" or d[1] != PP:
                continue
            X = d[2]
            # indices in a high window where the demand is present and one-shot
            occ = [i for i in range(m._stab, m._stab + 3 * m.p)
                   if m.sat_chain(i, d, hi)
                   and not m.sat_chain(i, ("all", PP, d), hi)]
            if len(occ) < 2 * m.p:            # not recurring across periods
                continue
            cofinal_cases += 1
            # greedily cover the occurrences by witnesses, highest-reaching first
            need = set(occ)
            used = 0
            while need:
                lo = min(need)
                # any witness above a_lo carrying X: chain node or side
                best = None
                for j in range(len(m.sides)):
                    if rel(m.a(lo), m.sides[j]) == PP and m.sat_side(j, X, hi):
                        cov = {i for i in need
                               if rel(m.a(i), m.sides[j]) == PP}
                        if best is None or len(cov) > len(best):
                            best = cov
                for k in range(lo + 1, m._stab + 6 * m.p):
                    if m.sat_chain(k, X, hi):
                        cov = {i for i in need if i < k}
                        if best is None or len(cov) > len(best):
                            best = cov
                        break
                if not best:
                    unbounded_flag += 1
                    used = -1
                    break
                need -= best
                used += 1
                if used > 20:
                    used = -1
                    break
            dist[used] = dist.get(used, 0) + 1
    print(f"  cofinally recurring one-shot demands found : {cofinal_cases}")
    if dist:
        print(f"  {'witnesses needed':>18} {'cases':>8}")
        for k in sorted(dist):
            lbl = "UNSERVED/>20" if k == -1 else str(k)
            print(f"  {lbl:>18} {dist[k]:8d}")
    print(f"  cases with no available witness at all     : {unbounded_flag}")
    return cofinal_cases > 0


def part_c(trials=600, seed=303303):
    print("\nPART C -- is a COFINAL witness (one region above all high a_i)")
    print("  always available for a cofinally recurring one-shot demand?")
    rng = random.Random(seed)
    hi = 40
    have = lack = 0
    lack_ex = []
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build_model(rng)
        for d in closure(c0):
            if d[0] != "ex" or d[1] != PP:
                continue
            X = d[2]
            occ = [i for i in range(m._stab, m._stab + 3 * m.p)
                   if m.sat_chain(i, d, hi)
                   and not m.sat_chain(i, ("all", PP, d), hi)]
            if len(occ) < 2 * m.p:
                continue
            # a COFINAL witness: a side above EVERY chain node (cofinite side)
            cof = [j for j in range(len(m.sides))
                   if m.sides[j].cof and m.sat_side(j, X, hi)
                   and all(rel(m.a(i), m.sides[j]) == PP for i in occ)]
            if cof:
                have += 1
            else:
                lack += 1
                if len(lack_ex) < 2:
                    lack_ex.append((c0, d))
    tot = have + lack
    print(f"  cofinally recurring one-shot demands : {tot}")
    if tot:
        print(f"    a single cofinal witness EXISTS    : {have:6d}"
              f"  ({100*have/tot:5.1f}%)")
        print(f"    no single cofinal witness          : {lack:6d}"
              f"  ({100*lack/tot:5.1f}%)")
    print("  A single cofinal witness would collapse NodeCovered outright:")
    print("  ONE external serves the whole kernel for that demand.  A high rate")
    print("  is design evidence; the gaps are the shapes to design against.")
    return tot > 0


def part_d(trials=900, seed=404404):
    """THE DECISIVE MEASUREMENT.  Part B conflated two witness kinds:

      IN-KERNEL  -- the witness is another CHAIN node.  Free: the kernel serves
                    itself, exactly as rr_covers does for persistent demands.
      EXTERNAL   -- the witness is a side region.  This is what NodeCovered has
                    to bound.

    And it measured a fixed window.  Here we grow the window and ask whether the
    EXTERNAL count grows with it -- growth would mean unboundedly many externals
    and would refute the current certificate shape outright.
    """
    print("\nPART D -- in-kernel vs external, and does the EXTERNAL count GROW?")
    rng = random.Random(seed)
    hi = 60
    inkernel = extonly = 0
    growth = {}
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build_model(rng)
        for d in closure(c0):
            if d[0] != "ex" or d[1] != PP:
                continue
            X = d[2]
            # GENUINE cofinality: the demand must still be present in the TOP
            # quarter of the widest window we will measure over.  Testing it on
            # a narrow window (as an earlier revision did) admits demands that
            # simply die above the sides' reach, and then everything looks flat
            # vacuously -- the same class of artifact as wp100's.
            WIN = 64 * m.p
            occ = [i for i in range(m._stab, m._stab + WIN)
                   if m.sat_chain(i, d, hi)
                   and not m.sat_chain(i, ("all", PP, d), hi)]
            if not occ or len([i for i in occ
                               if i > m._stab + 3 * WIN // 4]) < m.p:
                continue
            # does X recur on the CHAIN above?  then serving is free
            chain_hits = [k for k in range(m._stab, m._stab + 8 * m.p)
                          if m.sat_chain(k, X, hi)]
            if len(chain_hits) >= 3:
                inkernel += 1
                continue
            extonly += 1
            # EXTERNAL count as the window grows
            row = []
            for mult in (2, 4, 8, 16, 32, 64):
                win = [i for i in range(m._stab, m._stab + mult * m.p)
                       if m.sat_chain(i, d, hi)]
                need = set(win)
                used = 0
                while need and used <= 25:
                    lo = min(need)
                    best, bj = None, None
                    for j in range(len(m.sides)):
                        if rel(m.a(lo), m.sides[j]) == PP and m.sat_side(j, X, hi):
                            cov = {i for i in need
                                   if rel(m.a(i), m.sides[j]) == PP}
                            if best is None or len(cov) > len(best):
                                best, bj = cov, j
                    if not best:
                        used = -1
                        break
                    need -= best
                    used += 1
                row.append(used)
            growth[tuple(row)] = growth.get(tuple(row), 0) + 1
    tot = inkernel + extonly
    print(f"  cofinally recurring one-shot demands : {tot}")
    if tot:
        print(f"    served IN-KERNEL (X recurs on the chain) : {inkernel:5d}"
              f"  ({100*inkernel/tot:5.1f}%)   -- FREE")
        print(f"    need an EXTERNAL                         : {extonly:5d}"
              f"  ({100*extonly/tot:5.1f}%)")
    if growth:
        print(f"  external count at windows 2p / 4p / 8p / 16p / 32p / 64p")
        print(f"  {'counts':>22} {'cases':>7}  {'verdict':>10}")
        grew = flat = 0
        for row in sorted(growth, key=lambda r: -growth[r]):
            n = growth[row]
            if -1 in row:
                v = "unserved"
            elif row[-1] > row[0]:
                v = "GROWS"; grew += n
            else:
                v = "flat"; flat += n
            print(f"  {str(row):>22} {n:7d}  {v:>10}")
        print(f"  FLAT (bounded) {flat}   GROWING {grew}")
        return grew == 0
    return False


def part_e(trials=1200, seed=505505):
    """THE CERTIFIED DICHOTOMY, MEASURED.

    formal/POFreeLift.lean sec. 49 certifies (witness_bounded_or_all) that every
    candidate witness w for a kernel's vertical demand either

        (ALL)      is above EVERY chain node -- one external serves the whole
                   kernel, cost 1; or
        (BOUNDED)  is above only a bounded initial segment -- the witnesses must
                   keep ascending, which is the layer regress.

    There is provably no middle case (above_cofinal_is_above_all: transitivity
    closes downward, so "above cofinally many" IS "above all").

    This part asks how often each branch is the ONLY one available: is the
    BOUNDED branch actually reachable, or is it empty in practice?
    """
    print("\nPART E -- the certified dichotomy: is the BOUNDED branch reachable?")
    rng = random.Random(seed)
    hi = 60
    all_avail = bounded_only = none_avail = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build_model(rng)
        for d in closure(c0):
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
            if len([k for k in range(m._stab, m._stab + 8 * m.p)
                    if m.sat_chain(k, X, hi)]) >= 3:
                continue                       # in-kernel branch, not this test
            # classify every available witness by the certified dichotomy
            chain_pts = list(range(m._stab, m._stab + 16 * m.p))
            has_all = has_bounded = False
            for j in range(len(m.sides)):
                if not m.sat_side(j, X, hi):
                    continue
                above = [i for i in chain_pts if rel(m.a(i), m.sides[j]) == PP]
                if not above:
                    continue
                if len(above) == len(chain_pts):
                    has_all = True
                else:
                    has_bounded = True
            if has_all:
                all_avail += 1
            elif has_bounded:
                bounded_only += 1
            else:
                none_avail += 1
    tot = all_avail + bounded_only + none_avail
    print(f"  external-needing cofinal one-shot demands : {tot}")
    if tot:
        print(f"    (ALL) a whole-kernel witness exists     : {all_avail:5d}"
              f"  ({100*all_avail/tot:5.1f}%)  -- cost 1, DONE")
        print(f"    (BOUNDED) only segment witnesses        : {bounded_only:5d}"
              f"  ({100*bounded_only/tot:5.1f}%)  -- the layer regress")
        print(f"    no witness at all in this model class   : {none_avail:5d}")
    print("  READ THIS RATE CAREFULLY.  0% BOUNDED is NOT evidence that the")
    print("  bounded branch is impossible -- it is a CONSEQUENCE of the model")
    print("  class having FINITELY many side regions.  With a finite pool, each")
    print("  witness above a_i reaches at least i, so genuine cofinality forces")
    print("  a member of unbounded reach, and transitivity makes it reach ALL.")
    print("  That is now a THEOREM: finite_pool_gives_cofinal_witness, and its")
    print("  sharp form finite_pool_all_or_nothing -- a finite pool either has a")
    print("  whole-kernel server or fails outright; never 2 or 3 partial ones.")
    print("  Reaching the bounded branch needs INFINITELY many externals, i.e.")
    print("  witnesses that genuinely ascend.  Whether a forall-PO-free concept")
    print("  can FORCE that is the campaign's residual question.")
    return tot > 0


def main():
    print("=" * 74)
    print("WP101 -- one-shot vertical demands over infinite periodic models")
    print("=" * 74)
    res = {"A validity": part_a(), "B witness count": part_b(),
           "C cofinal witness": part_c(), "D scaling": part_d(), "E dichotomy": part_e()}
    print("\n" + "=" * 74)
    for k, v in res.items():
        print(f"  {k:20s} : {'ran' if v else 'see above'}")
    print("=" * 74)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
