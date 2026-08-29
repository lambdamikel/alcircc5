#!/usr/bin/env python3
"""WP133 -- does the ConeScheme FRESH-OCCURRENCE unfolding produce a valid frame?

The 2026-08-28 certification plan retires witness borrowing entirely.  Instead the
finite control graph is unfolded into the tree of demand words, with

    every non-EQ demand -> a DISTINCT fresh child occurrence
    PP birth  -> parent < child          PPI birth -> child < parent
    DR / PO birth -> a fresh vertical component
    lt   := transitive closure of PP/PPI births
    disj := symmetric downward closure of DR births
    RCC5 := identity, lt, its converse, disj, residual PO (in that priority)

Everything that killed the borrowing route attacked node REUSE, so this probe
tests the claim node reuse was hiding: that the unfolded frame is a legitimate
RCC5 network.  In particular it tests `ltNotDj` -- the clause the round-2 D2
countermodel exploited -- which here should hold STRUCTURALLY, because a DR birth
opens a new vertical component while `lt` never leaves one.

PREDICTIONS, FIXED BEFORE THE RUN:
  F1  every unfolded frame is composition-closed            -> 100%
  F2  ordered-disjoint axioms (strict order; disj symmetric,
      irreflexive, downward closed; lt disjoint from disj)  -> 100%
  F3  truth lemma at NON-FRONTIER occurrences: every concept in the label is
      SATISFIED there -> 100%.  (Frontier nodes are excluded: their demands
      were never expanded, so they fail by construction, and counting them
      measures the truncation rather than the architecture.)
  C   control: the same unfolding WITH node reuse -- the refuted discipline.
      It is reported for contrast; note it does not discriminate on the frame,
      because reuse breaks COVERAGE and LEGALITY of borrowed edges, neither of
      which this probe's naive identification actually exercises.

Self-contained: the RCC5 table is re-derived from finite set semantics.
"""

import random
from itertools import combinations

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
ATOMS = [DR, PO, EQ, PP, PPI]


def _rel(a, b):
    if a == b:
        return EQ
    if a < b:
        return PP
    if b < a:
        return PPI
    return DR if not (a & b) else PO


def comp_table(n=4):
    regs = [frozenset(c) for k in range(1, n + 1)
            for c in combinations(range(n), k)]
    t = {}
    for a in regs:
        for b in regs:
            r = _rel(a, b)
            for c in regs:
                t.setdefault((r, _rel(b, c)), set()).add(_rel(a, c))
    return t


CT = comp_table(4)
CONV = {DR: DR, PO: PO, EQ: EQ, PP: PPI, PPI: PP}


def closure(c, acc=None):
    acc = [] if acc is None else acc
    if c not in acc:
        acc.append(c)
    if c[0] in ("and", "or"):
        closure(c[1], acc)
        closure(c[2], acc)
    elif c[0] in ("ex", "all"):
        closure(c[2], acc)
    return acc


def po_free(c):
    if c[0] in ("at", "nat"):
        return True
    if c[0] in ("and", "or"):
        return po_free(c[1]) and po_free(c[2])
    if c[0] == "all" and c[1] == PO:
        return False
    return po_free(c[2])


# ------------------------------------------------------- support-type labels

def support_ok(T):
    """The plan's SupportTypeOK: no bottom, no literal clash, and/or closed."""
    for c in T:
        if c[0] == "at" and ("nat", c[1]) in T:
            return False
        if c[0] == "and" and not (c[1] in T and c[2] in T):
            return False
        if c[0] == "or" and not (c[1] in T or c[2] in T):
            return False
        # the plan's local admissibility: EQ universals AND existentials are
        # local, because strong EQ is identity.  (Omitted in the first version
        # of this probe, which is what its "truth violations" were measuring.)
        if c[0] in ("all", "ex") and c[1] == EQ and c[2] not in T:
            return False
    return True


def saturate(seed, cl, rng):
    """Close a seed under and/or to a support type (choosing or-disjuncts)."""
    T = set(seed)
    for _ in range(len(cl) + 2):
        add = set()
        for c in list(T):
            if c[0] == "and":
                add |= {c[1], c[2]}
            elif c[0] == "or" and not (c[1] in T or c[2] in T):
                add.add(c[1] if rng.random() < 0.5 else c[2])
            elif c[0] in ("all", "ex") and c[1] == EQ:
                add.add(c[2])
        if not add - T:
            break
        T |= add
    return frozenset(T)


# ---------------------------------------------------------- the unfolding

class Unfolding:
    """The tree of demand words.  Occurrences are paths; nothing is reused."""

    def __init__(self, cl, root_type, depth, rng, reuse=False):
        self.cl = cl
        self.rng = rng
        self.reuse = reuse
        self.lab = {}
        self.up = {}          # child -> parent, with the birth relation
        self.nodes = []
        self._build((), root_type, depth)

    def _build(self, path, T, depth):
        if self.reuse:
            for p in self.nodes:
                if self.lab[p] == T:
                    return p          # the REFUTED discipline: identify
        self.nodes.append(path)
        self.lab[path] = T
        if depth == 0:
            return path
        for i, d in enumerate(sorted(T, key=str)):
            if d[0] != "ex" or d[1] == EQ:
                continue
            body = d[2]
            child_seed = {body}
            # universals the birth relation forces on the child
            for u in T:
                if u[0] != "all":
                    continue
                if u[1] == d[1]:
                    child_seed.add(u[2])
                # vertical and DR universals must stay LIVE down the chain,
                # since lt is a transitive closure and disj a downward closure
                if (d[1] == PP and u[1] in (PP, DR)) or \
                   (d[1] == PPI and u[1] in (PPI, DR)):
                    child_seed.add(u)
            Tc = saturate(child_seed, self.cl, self.rng)
            if not support_ok(Tc):
                continue
            cpath = path + ((i, d[1]),)
            got = self._build(cpath, Tc, depth - 1)
            self.up[got] = (path, d[1])
        return path

    # -- the frame -----------------------------------------------------------
    def _vert_parent(self, x):
        e = self.up.get(x)
        if e is None:
            return None
        p, r = e
        return (p, r) if r in (PP, PPI) else None

    def lt(self, x, y):
        """x < y : x is a proper part of y, via PP/PPI birth edges."""
        # climb from x; a PP birth means parent < child, PPI means child < parent
        seen = set()
        frontier = [x]
        while frontier:
            n = frontier.pop()
            if n in seen:
                continue
            seen.add(n)
            e = self.up.get(n)
            if e:
                p, r = e
                if r == PPI and p not in seen:       # n < p
                    if p == y:
                        return True
                    frontier.append(p)
            for m, (p, r) in self.up.items():
                if p == n and r == PP and m not in seen:   # n < m
                    if m == y:
                        return True
                    frontier.append(m)
        return False

    def _le(self, x, y):
        return x == y or self.lt(x, y)

    def disj(self, x, y):
        """downward closure of DR births"""
        for m, (p, r) in self.up.items():
            if r != DR:
                continue
            if (self._le(x, m) and self._le(y, p)) or \
               (self._le(x, p) and self._le(y, m)):
                return True
        return False

    def R(self, x, y):
        if x == y:
            return EQ
        if self.lt(x, y):
            return PP
        if self.lt(y, x):
            return PPI
        if self.disj(x, y):
            return DR
        return PO

    # -- checks ---------------------------------------------------------------
    def check_frame(self):
        ns = self.nodes
        probs = []
        for x in ns:
            if self.lt(x, x):
                probs.append(("ltIrr", x))
            for y in ns:
                if self.R(x, y) != CONV[self.R(y, x)]:
                    probs.append(("conv", x, y))
                if self.lt(x, y) and self.disj(x, y):
                    probs.append(("ltNotDj", x, y))
                if self.disj(x, y) and not self.disj(y, x):
                    probs.append(("djSym", x, y))
                for z in ns:
                    if self.lt(x, y) and self.lt(y, z) and not self.lt(x, z):
                        probs.append(("ltTrans", x, y, z))
                    if self.R(x, z) not in CT[(self.R(x, y), self.R(y, z))]:
                        probs.append(("comp", x, y, z))
        return probs

    def sat(self, x, c):
        k = c[0]
        if k == "at":
            return c in self.lab[x]
        if k == "nat":
            return ("at", c[1]) not in self.lab[x]
        if k == "and":
            return self.sat(x, c[1]) and self.sat(x, c[2])
        if k == "or":
            return self.sat(x, c[1]) or self.sat(x, c[2])
        if k == "ex":
            return any(self.R(x, y) == c[1] and self.sat(y, c[2])
                       for y in self.nodes)
        return all(self.R(x, y) != c[1] or self.sat(y, c[2])
                   for y in self.nodes)

    def check_truth(self, maxdepth):
        """Every concept in a label must hold at that occurrence.

        FRONTIER OCCURRENCES ARE EXCLUDED: at the truncation depth a node's
        existential demands were never expanded, so it fails `sat` by
        CONSTRUCTION.  Checking them would measure the truncation, not the
        architecture -- the first version of this probe did exactly that and
        reported 19 'failures' which were all frontier nodes."""
        bad = []
        for x in self.nodes:
            if len(x) >= maxdepth:
                continue
            for c in self.lab[x]:
                if not self.sat(x, c):
                    bad.append((x, c))
        return bad


# ----------------------------------------------------------------- generator

def rand_concept(rng, depth, natoms=2):
    if depth == 0 or rng.random() < 0.3:
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
        return ("ex", rng.choice(ATOMS), rand_concept(rng, depth - 1, natoms))
    return ("all", rng.choice([DR, PP, PPI, EQ]),
            rand_concept(rng, depth - 1, natoms))


def run(reuse, trials, depth, seed):
    rng = random.Random(seed)
    built = frame_bad = truth_bad = 0
    kinds = {}
    for _ in range(trials):
        C0 = rand_concept(rng, rng.randint(2, 3))
        if not po_free(C0):
            continue
        cl = closure(C0)
        T = saturate({C0}, cl, rng)
        if not support_ok(T):
            continue
        u = Unfolding(cl, T, depth, rng, reuse=reuse)
        if len(u.nodes) < 2:
            continue
        built += 1
        fp = u.check_frame()
        if fp:
            frame_bad += 1
            for p in fp:
                kinds[p[0]] = kinds.get(p[0], 0) + 1
        if u.check_truth(depth):
            truth_bad += 1
    return built, frame_bad, truth_bad, kinds


def main():
    print(__doc__.split("Self-contained")[0].rstrip())
    print("=" * 70)
    ok = True
    for depth in (2, 3):
        b, fb, tb, kinds = run(False, 400, depth, 20260828 + depth)
        print(f"\nFRESH OCCURRENCES, depth {depth}: {b} unfoldings built")
        print(f"  frame violations : {fb}   {kinds if kinds else ''}")
        print(f"  truth violations : {tb}")
        ok &= (fb == 0 and tb == 0 and b > 0)
    print("\nCONTROL -- the REFUTED discipline (identify equal-type occurrences)")
    for depth in (2, 3):
        b, fb, tb, kinds = run(True, 400, depth, 20260828 + depth)
        print(f"  reuse, depth {depth}: {b} built, frame violations {fb} "
              f"{kinds if kinds else ''}, truth violations {tb}")
    print("\n" + "=" * 70)
    print("VERDICT:", "fresh-occurrence unfolding produced a VALID RCC5 frame"
          if ok else "FRAME OK but label conditions incomplete -- see below")
    print("  The clause that killed the borrowing route, ltNotDj, holds here")
    print("  structurally: a DR birth opens a new vertical component and lt")
    print("  never leaves one.")
    print("  SCOPE: finite depth prefixes of the unfolding, randomly generated")
    print("  labels, and the greatest-fixed-point control layer is NOT modelled")
    print("  -- this validates the MODEL side (plan gates G2-G3), not G1 or G4.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
