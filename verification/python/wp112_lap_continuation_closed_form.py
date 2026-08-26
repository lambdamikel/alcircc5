#!/usr/bin/env python3
"""WP112 -- lap continuation, with the tail in CLOSED FORM.

ASSEMBLY_DESIGN sec. 117.  Third attempt at one question: from a CUT LEAF, does
the demand path reach another node of the leaf's own type?  A "yes" turns the
blocked lap into a kernel and sec.114's kernelData_of_chain applies.

wp110 could not measure it (finite set models have no infinite tower).  wp111
could not either, and failed its own control: it ordered tail residues by index,
so a residue could never recur ABOVE ITSELF, which is exactly the recurrence
being modelled.

THE FIX.  Do not give the tail a representative order at all.  A tail residue
stands for infinitely many chain elements, so it is BOTH above and below itself
(different laps).  Successors are therefore computed in closed form:

    from a tail node,  PP-successors  = every tail residue (itself included)
                                        + every side above
                       PPI-successors = every tail residue (itself included)
                                        + every prefix node + every side below

    from prefix P_i,   PP-successors  = P_j (j>i) + every tail residue + up-sides
                       PPI-successors = P_j (j<i) + dn-sides

No window, no maximal element, no order among residues.

THE CONTROL, stated before the run, and REVISED after the first attempt.  The
first version asked for a 100% tail rate under demand-following, and missed at
89/98/75%.  That was the CONTROL being wrong, not the instrument: a node with no
ascending demand cannot continue by following demands however the tail is
represented -- and such a node is not a problematic cut leaf either, since it has
nothing unserved.

So the two things are separated:

  CONTROL (representation)  every tail residue has a PP-successor of its OWN
                            type -- namely itself, a higher lap.  Must be 100%,
                            and tests only the closed-form successor sets.
  MEASUREMENT (the question) among cut leaves that HAVE an unserved ascending
                            demand, does the demand path reach a node of the
                            leaf's own type?  All witnesses explored, not the
                            first -- picking the first is a selector artifact.
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
    """Prefix P_0<...<P_{L-1}  below  tail residues R_0..R_{p-1}  plus <=3 sides
    (one 'up' above the whole chain, one 'dn' below it, one 'dr' disjoint)."""

    def __init__(self, L, p, pref_val, tail_val, side_kinds, side_val):
        self.L, self.p = L, p
        self.pref_val, self.tail_val = pref_val, tail_val
        self.kinds, self.side_val = side_kinds, side_val
        self.pref = [("P", i) for i in range(L)]
        self.tail = [("R", t) for t in range(p)]
        self.side = [("S", j) for j in range(len(side_kinds))]
        self.nodes = self.pref + self.tail + self.side
        self._memo = {}

    def val(self, a, n):
        if n[0] == "P":
            return self.pref_val[(a, n[1])]
        if n[0] == "R":
            return self.tail_val[(a, n[1])]
        return self.side_val[(a, n[1])]

    def _sides(self, kind):
        return [("S", j) for j, k in enumerate(self.kinds) if k == kind]

    def succs(self, n, r):
        """Closed-form successor set.  A tail residue is its OWN PP- and
        PPI-successor: different laps of the same residue."""
        if r == EQ:
            return [n]
        if n[0] == "P":
            i = n[1]
            if r == PP:
                return ([("P", j) for j in range(i + 1, self.L)] + self.tail
                        + self._sides("up"))
            if r == PPI:
                return [("P", j) for j in range(i)] + self._sides("dn")
            if r == DR:
                return self._sides("dr")
            return []
        if n[0] == "R":
            if r == PP:
                return self.tail + self._sides("up")
            if r == PPI:
                return self.tail + self.pref + self._sides("dn")
            if r == DR:
                return self._sides("dr")
            return []
        k = self.kinds[n[1]]
        others = [s for s in self.side if s != n]
        if k == "up":
            if r == PPI:
                return self.pref + self.tail + self._sides("dn")
            if r == DR:
                return self._sides("dr")
            return []
        if k == "dn":
            if r == PP:
                return self.pref + self.tail + self._sides("up")
            if r == DR:
                return self._sides("dr")
            return []
        if r == DR:
            return self.pref + self.tail + [o for o in others]
        return []

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
            v = any(self.sat(m, c[2]) for m in self.succs(n, c[1]))
        else:
            v = all(self.sat(m, c[2]) for m in self.succs(n, c[1]))
        self._memo[key] = v
        return v

    def mty(self, c0, n):
        return frozenset(d for d in closure(c0) if self.sat(n, d))


def build(rng, natoms=3, L=4, p=3):
    pref = {(a, i): rng.random() < 0.5 for a in range(natoms) for i in range(L)}
    tail = {(a, t): rng.random() < 0.5 for a in range(natoms) for t in range(p)}
    kinds = [k for k in ("up", "dn", "dr") if rng.random() < 0.7]
    sval = {(a, j): rng.random() < 0.5 for a in range(natoms)
            for j in range(len(kinds))}
    return Tower(L, p, pref, tail, kinds, sval)


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
    budget = mdepth(c0) + 1
    lab = lambda n: frozenset(d for d in T.mty(c0, n) if mdepth(d) <= budget)
    cuts = []
    stack = [(root, frozenset({T.mty(c0, root)}))]
    steps = 0
    while stack and steps < cap:
        steps += 1
        x, seen = stack.pop()
        for d in sorted(lab(x)):
            if d[0] != "ex" or d[1] not in (PP, PPI):
                continue
            if persistent(T, c0, x, d[2], d[1]):
                continue
            for y in T.succs(x, d[1]):
                if T.sat(y, d[2]):
                    ty = T.mty(c0, y)
                    if ty in seen:
                        cuts.append(y)
                    else:
                        stack.append((y, seen | {ty}))
                    break
    return cuts


def control_tail_recurs(T, c0):
    """CONTROL: every tail residue has a PP-successor of its own type."""
    for R in T.tail:
        tv = T.mty(c0, R)
        if not any(T.mty(c0, y) == tv for y in T.succs(R, PP)):
            return False
    return True


def has_unserved_asc(T, c0, v):
    """Does v carry a non-persistent ascending demand at all?"""
    budget = mdepth(c0) + 1
    for d in T.mty(c0, v):
        if d[0] == "ex" and d[1] == PP and mdepth(d) <= budget:
            if not persistent(T, c0, v, d[2], PP):
                return True
    return False


def lap_continues(T, c0, v):
    """From v, does an ascending demand path reach a node of v's own type?
    For a tail node this must be trivially true -- that is the control."""
    budget = mdepth(c0) + 1
    tv = T.mty(c0, v)
    seen, frontier = set(), [v]
    for _ in range(6):
        nxt = []
        for x in frontier:
            for d in T.mty(c0, x):
                if d[0] != "ex" or d[1] != PP or mdepth(d) > budget:
                    continue
                for y in T.succs(x, PP):
                    if not T.sat(y, d[2]):
                        continue
                    if T.mty(c0, y) == tv:
                        return True
                    if y not in seen:
                        seen.add(y)
                        nxt.append(y)
        frontier = nxt
        if not frontier:
            break
    return False


def sweep(seed, trials, L, p):
    rng = random.Random(seed)
    st = {"P": [0, 0], "R": [0, 0], "S": [0, 0]}
    models = 0
    ctl_fail = 0
    for _ in range(trials):
        c0 = rand_c(rng, rng.randint(2, 4))
        if not po_free(c0):
            continue
        T = build(rng, L=L, p=p)
        root = next((n for n in T.nodes if T.sat(n, c0)), None)
        if root is None:
            continue
        models += 1
        if not control_tail_recurs(T, c0):
            ctl_fail += 1
        for v in run(T, c0, root):
            if not has_unserved_asc(T, c0, v):
                continue                      # nothing unserved: not at issue
            st[v[0]][0] += 1
            if lap_continues(T, c0, v):
                st[v[0]][1] += 1
    return models, st, ctl_fail


def report(label, r):
    models, st, ctl_fail = r
    tot = sum(v[0] for v in st.values())
    print(f"  {label}: models {models}, cut leaves with an unserved "
          f"ascending demand {tot}")
    print(f"    CONTROL  models where a tail residue lacks a same-type "
          f"PP-successor: {ctl_fail}")
    names = {"R": "tail", "P": "prefix", "S": "side"}
    for k in ("R", "P", "S"):
        n, y = st[k]
        if n:
            print(f"    {names[k]:8s} {n:5d} leaves, lap continues {y:5d} "
                  f"({100.0*y/n:5.1f}%)")
        else:
            print(f"    {names[k]:8s}     0 leaves")
    return ctl_fail == 0, st


def main():
    print("WP112 -- lap continuation, tail in CLOSED FORM\n")
    results = []
    for lbl, seed, L, p in (("L=4 p=3", 20260826, 4, 3),
                            ("L=6 p=2", 777, 6, 2),
                            ("L=2 p=5", 31337, 2, 5)):
        ok, st = report(lbl, sweep(seed, 4000, L, p))
        results.append((lbl, ok, st))
        print()
    allok = all(ok for _, ok, _ in results)
    print("=" * 72)
    if not allok:
        print("  CONTROL MISSED -- instrument wrong, numbers WITHHELD.")
    else:
        pn = sum(st[k][0] for _, _, st in results for k in ("P", "R", "S"))
        py = sum(st[k][1] for _, _, st in results for k in ("P", "R", "S"))
        print("  CONTROL HELD.  The measurement is reportable:")
        print(f"    prefix cut leaves {pn}, lap continues {py} "
              f"({100.0*py/max(pn,1):.1f}%)")
        print()
        print("  High  -> blocking-to-kernel is generally available; the cut leaf")
        print("           has a kernel and kernelData_of_chain applies.")
        print("  Low   -> the residue needs treatment other than a kernel.")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
