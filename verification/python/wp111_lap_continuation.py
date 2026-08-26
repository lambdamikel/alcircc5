#!/usr/bin/env python3
"""WP111 -- does a BLOCKED LAP continue?  Measured where the answer can differ.

ASSEMBLY_DESIGN sec. 116.3.  wp110 part C asked whether, from a cut leaf, the
demand path reaches another node of the leaf's own type -- what would turn a
blocked lap into a KERNEL and let sec. 114's kernelData_of_chain apply.  It read
~0.5% over finite set models, and that number is worthless: a lap that continues
indefinitely is exactly what a finite model cannot represent (the wp100 pattern).

wp101's class is no good either, for the OPPOSITE reason: its chain valuation is
periodic in i, so every type recurs cofinally BY CONSTRUCTION and C would read
100% for free.

THE CLASS USED HERE.  An EVENTUALLY periodic tower, represented exactly on its
finite quotient:

    P_0 < P_1 < ... < P_{L-1}   <   R_0 , R_1 , ... , R_{p-1}   (+ sides)

`P_i` is an APERIODIC PREFIX node (one element each); `R_t` stands for the
infinitely many chain elements of residue t in the periodic tail.  Every residue
recurs cofinally above every tail element, so

    R_s |= exists-PP.X   <->   some R_t |= X   (t arbitrary)   or a side above

which is closed-form and boundary-free -- no maximal element, no window.
Crucially the PREFIX is aperiodic, so a type repeat there need NOT continue,
while one in the tail does.  The class can therefore represent BOTH answers,
which is the property wp110's class lacked.

Sides are chosen above-all or below-all the chain so tail relations are uniform.

REPORTED SPLIT: prefix vs tail.  A single pooled rate would hide exactly the
distinction the class was built to expose.
"""

import random

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"


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
        closure(c[1], acc)
        closure(c[2], acc)
    elif k in ("ex", "all"):
        closure(c[2], acc)
    return acc


def po_free(c):
    k = c[0]
    if k in ("at", "nat"):
        return True
    if k in ("and", "or"):
        return po_free(c[1]) and po_free(c[2])
    if k == "all" and c[1] == PO:
        return False
    return po_free(c[2])


class Tower:
    """Nodes: ('P', i) i<L  |  ('R', t) t<p  |  ('S', j) sides.

    Order: P_0 < ... < P_{L-1} < every R; every R is below/above every R
    (residues recur cofinally in both directions inside the tail).
    Sides: kind 'up' = above the whole chain, 'dn' = below it, 'dr' = disjoint.
    """

    def __init__(self, L, p, pref_val, tail_val, sides, side_val):
        self.L, self.p = L, p
        self.pref_val, self.tail_val = pref_val, tail_val
        self.sides, self.side_val = sides, side_val
        self.nodes = ([("P", i) for i in range(L)] + [("R", t) for t in range(p)]
                      + [("S", j) for j in range(len(sides))])
        self._memo = {}

    def val(self, a, n):
        if n[0] == "P":
            return self.pref_val[(a, n[1])]
        if n[0] == "R":
            return self.tail_val[(a, n[1])]
        return self.side_val[(a, n[1])]

    def rel(self, x, y):
        if x == y:
            return EQ
        if x[0] == "P" and y[0] == "P":
            return PP if x[1] < y[1] else PPI
        if x[0] == "P" and y[0] == "R":
            return PP
        if x[0] == "R" and y[0] == "P":
            return PPI
        if x[0] == "R" and y[0] == "R":
            # distinct residues: each recurs above and below the other.  Fix a
            # consistent orientation by index so the order stays a strict order
            # on the QUOTIENT (the underlying elements realise both).
            return PP if x[1] < y[1] else PPI
        # sides
        s = y if y[0] == "S" else x
        k = self.sides[s[1]]
        other_is_x = (s is y)
        if k == "up":
            r = PP if other_is_x else PPI
        elif k == "dn":
            r = PPI if other_is_x else PP
        else:
            r = DR
        if x[0] == "S" and y[0] == "S":
            return DR if x != y else EQ
        return r

    def sat(self, n, c):
        key = (n, c)
        if key in self._memo:
            return self._memo[key]
        k = c[0]
        if k == "at":
            v = self.val(c[1], n)
        elif k == "nat":
            v = not self.val(c[1], n)
        elif k == "and":
            v = self.sat(n, c[1]) and self.sat(n, c[2])
        elif k == "or":
            v = self.sat(n, c[1]) or self.sat(n, c[2])
        elif k == "ex":
            v = any(self.rel(n, m) == c[1] and self.sat(m, c[2])
                    for m in self.nodes)
        else:
            v = all(self.rel(n, m) != c[1] or self.sat(m, c[2])
                    for m in self.nodes)
        self._memo[key] = v
        return v

    def mty(self, c0, n):
        return frozenset(d for d in closure(c0) if self.sat(n, d))


def build(rng, natoms=3, L=4, p=3, nsides=3):
    pref = {(a, i): rng.random() < 0.5 for a in range(natoms) for i in range(L)}
    tail = {(a, t): rng.random() < 0.5 for a in range(natoms) for t in range(p)}
    sides = [rng.choice(["up", "dn", "dr"]) for _ in range(nsides)]
    sval = {(a, j): rng.random() < 0.5 for a in range(natoms)
            for j in range(nsides)}
    return Tower(L, p, pref, tail, sides, sval)


def rand_c(rng, depth, natoms=3):
    if depth == 0 or rng.random() < 0.2:
        i = rng.randrange(natoms)
        return ("at", i) if rng.random() < 0.6 else ("nat", i)
    r = rng.random()
    if r < 0.2:
        return ("and", rand_c(rng, depth - 1), rand_c(rng, depth - 1))
    if r < 0.32:
        return ("or", rand_c(rng, depth - 1), rand_c(rng, depth - 1))
    if r < 0.68:
        return ("ex", rng.choice([PP, PPI, PP, PPI, DR]), rand_c(rng, depth - 1))
    return ("all", rng.choice([PP, PPI, DR, EQ]), rand_c(rng, depth - 1))


def persistent(T, c0, x, D, d):
    return (("ex", d, D) in T.mty(c0, x)
            and T.sat(x, ("all", d, ("ex", d, D))))


def run(T, c0, root, cap=300):
    """cutNodes: keep the witness, expand unless its type is on the path."""
    budget = mdepth(c0) + 1
    lab = lambda n: frozenset(d for d in T.mty(c0, n) if mdepth(d) <= budget)
    cuts = []
    stack = [(root, frozenset({T.mty(c0, root)}))]
    seen_nodes = {root}
    steps = 0
    while stack and steps < cap:
        steps += 1
        x, seen = stack.pop()
        for d in sorted(lab(x)):
            if d[0] != "ex" or d[1] not in (PP, PPI):
                continue
            D = d[2]
            if persistent(T, c0, x, D, d[1]):
                continue
            for y in T.nodes:
                if T.rel(x, y) == d[1] and T.sat(y, D):
                    seen_nodes.add(y)
                    ty = T.mty(c0, y)
                    if ty in seen:
                        cuts.append(y)
                    elif y not in [s[0] for s in stack]:
                        stack.append((y, seen | {ty}))
                    break
    return cuts, seen_nodes


def lap_continues(T, c0, v):
    """From v, does an ascending demand path reach another node of v's type?"""
    budget = mdepth(c0) + 1
    tv = T.mty(c0, v)
    seen, frontier = {v}, [v]
    for _ in range(6):
        nxt = []
        for x in frontier:
            for d in T.mty(c0, x):
                if d[0] != "ex" or d[1] != PP or mdepth(d) > budget:
                    continue
                for y in T.nodes:
                    if T.rel(x, y) == PP and T.sat(y, d[2]):
                        if y not in seen:
                            if T.mty(c0, y) == tv:
                                return True
                            seen.add(y)
                            nxt.append(y)
                        break
        frontier = nxt
        if not frontier:
            break
    return False


def sweep(seed, trials, L, p):
    rng = random.Random(seed)
    stats = {"P": [0, 0], "R": [0, 0], "S": [0, 0]}
    models = leaves = 0
    for _ in range(trials):
        c0 = rand_c(rng, rng.randint(2, 4))
        if not po_free(c0):
            continue
        T = build(rng, L=L, p=p)
        root = next((n for n in T.nodes if T.sat(n, c0)), None)
        if root is None:
            continue
        models += 1
        cuts, _ = run(T, c0, root)
        for v in cuts:
            leaves += 1
            k = v[0]
            stats[k][0] += 1
            if lap_continues(T, c0, v):
                stats[k][1] += 1
    return models, leaves, stats


def report(label, r):
    models, leaves, st = r
    print(f"  {label}: models {models}, cut leaves {leaves}")
    names = {"P": "prefix (aperiodic)", "R": "tail (periodic)", "S": "side"}
    for k in ("P", "R", "S"):
        tot, yes = st[k]
        if tot:
            print(f"    {names[k]:22s} {tot:5d} leaves, lap continues "
                  f"{yes:5d} ({100.0*yes/tot:5.1f}%)")
        else:
            print(f"    {names[k]:22s}     0 leaves")


def main():
    print("WP111 -- lap continuation over an EVENTUALLY PERIODIC tower")
    print("(the class can represent BOTH answers; wp110's could represent neither)\n")
    report("L=4 p=3", sweep(20260826, 4000, 4, 3))
    print()
    report("L=6 p=2", sweep(777, 4000, 6, 2))
    print()
    report("L=2 p=5", sweep(31337, 4000, 2, 5))
    print("\n" + "=" * 72)
    print("  READ: the TAIL rate is near-100% by construction (residues recur)")
    print("  and is a sanity check, not a finding.  The PREFIX rate is the")
    print("  measurement: a type repeat in an aperiodic region need not continue.")
    print("  A high prefix rate says blocking-to-kernel is generally available;")
    print("  a low one says the cut leaf needs treatment other than a kernel.")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
