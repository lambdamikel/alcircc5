#!/usr/bin/env python3
"""WP115 -- FULL acceptance test of the declared edge (ASSEMBLY_DESIGN sec.123).

sec.123 proved that a declared edge  v < s  discharges ee_all for FORALL-PP by
label equality, and wp114 measured the acyclicity obstruction at 95-100%.  That
verified ONE obligation and ONE obstruction.  It is not enough, and the project's
history with blocking says so: round 6's blocking attempt passed its local checks
and still collapsed distinct laps to EQ.

What sec.123 did NOT check, and what can break:

  djDown   the ordered-disjoint frame closes disjointness DOWNWARD, so declaring
           v < s forces  disj s y  =>  disj v y  for every y.  If the model has
           v overlapping y, the declared frame now says they are disjoint, and
           any obligation reading that pair is affected.
  ltNotDj  comparable pairs must not be disjoint -- the new edge could collide.
  ee_all   checked only for forall-PP.  The other relations read the SAME
           declared frame and were never checked.
  e_ex     the demands of every OTHER node, not just the leaf's.

This probe builds the whole certificate the way the extraction would, adds the
declared edges, recomputes the ordered-disjoint closure, and checks EVERY
obligation.  It is the wp16 / wp94 acceptance pattern.

A pass is evidence the route survives; a failure names which obligation kills it.
Either is worth more than the partial check sec.123 ran.

Self-contained: RCC5 relations re-derived from finite set semantics.
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


def subsets(univ):
    out = []
    for k in range(1, len(univ) + 1):
        for c in combinations(sorted(univ), k):
            out.append(frozenset(c))
    return out


def comp_table(n=4):
    regs = subsets(set(range(n)))
    t = {}
    for a in regs:
        for b in regs:
            r = rel(a, b)
            for c in regs:
                t.setdefault((r, rel(b, c)), set()).add(rel(a, c))
    return t


CT = comp_table(4)


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


def sat(model, val, x, c):
    k = c[0]
    if k == "at":
        return val.get((c[1], x), False)
    if k == "nat":
        return not val.get((c[1], x), False)
    if k == "and":
        return sat(model, val, x, c[1]) and sat(model, val, x, c[2])
    if k == "or":
        return sat(model, val, x, c[1]) or sat(model, val, x, c[2])
    if k == "ex":
        return any(rel(x, y) == c[1] and sat(model, val, y, c[2]) for y in model)
    return all(rel(x, y) != c[1] or sat(model, val, y, c[2]) for y in model)


def mty(model, val, c0, x):
    return frozenset(d for d in closure(c0) if sat(model, val, x, d))


def persistent(model, val, c0, x, D, d):
    return (("ex", d, D) in mty(model, val, c0, x)
            and sat(model, val, x, ("all", d, ("ex", d, D))))


# ------------------------------------------- build the closure with its steps

def build(model, val, c0, root, cap=400):
    """Returns (nodes, up_steps, cut_leaves) where up_steps is the extraction's
    own order-generating relation, ALWAYS oriented upward."""
    budget = mdepth(c0) + 1
    lab = lambda x: frozenset(d for d in mty(model, val, c0, x)
                              if mdepth(d) <= budget)
    nodes = {root}
    ups = set()
    cuts = []
    stack = [(root, frozenset({mty(model, val, c0, root)}), (root,))]
    steps = 0
    while stack and steps < cap:
        steps += 1
        x, seen, path = stack.pop()
        for d in sorted(lab(x)):
            if d[0] != "ex" or d[1] not in (PP, PPI):
                continue
            D = d[2]
            if persistent(model, val, c0, x, D, d[1]):
                continue
            for y in model:
                if rel(x, y) == d[1] and sat(model, val, y, D):
                    nodes.add(y)
                    ups.add((x, y) if d[1] == PP else (y, x))
                    ty = mty(model, val, c0, y)
                    if ty in seen:
                        blk = next((z for z in path
                                    if mty(model, val, c0, z) == ty), None)
                        cuts.append((y, blk, frozenset(path)))
                    else:
                        stack.append((y, seen | {ty}, path + (y,)))
                    break
    return nodes, ups, cuts, lab


def tcl(pairs, nodes):
    r = set(pairs)
    changed = True
    while changed:
        changed = False
        for (a, b) in list(r):
            for (c, d) in list(r):
                if b == c and (a, d) not in r:
                    r.add((a, d))
                    changed = True
    return r


def declared_edges(model, val, c0, nodes, cuts, lab, lt):
    """For each residue demand at a cut leaf, declare an edge to a blocker
    witness that is not an ancestor.  Returns the new edges, or None if some
    demand has no cycle-free choice."""
    new = set()
    for (v, blk, pset) in cuts:
        if blk is None:
            continue
        for d in sorted(lab(v)):
            if d[0] != "ex" or d[1] not in (PP, PPI):
                continue
            D = d[2]
            if persistent(model, val, c0, v, D, d[1]):
                continue
            if any(rel(v, w) == d[1] and D in lab(w) for w in nodes):
                continue                       # already served
            cand = [s for s in model if rel(blk, s) == d[1] and sat(model, val, s, D)]
            pick = None
            for s in cand:
                edge = (v, s) if d[1] == PP else (s, v)
                if (edge[1], edge[0]) in lt or edge[1] == edge[0]:
                    continue                   # would cycle
                if rel(v, s) == DR:
                    continue                   # would break ltNotDj
                pick = s
                new.add(s)
                new.add(edge)
                break
            if pick is None:
                return None
    return new


def od_from(nodes, lt, model):
    """Ordered-disjoint structure: lt as given, disjointness = DOWNWARD CLOSURE
    of the model's DR pairs (the odSeed discipline)."""
    dj = set()
    for x in nodes:
        for y in nodes:
            if x != y and rel(x, y) == DR:
                dj.add((x, y))
    changed = True
    while changed:
        changed = False
        for (x, y) in list(dj):
            for x2 in nodes:
                if x2 != x and (x2, x) not in lt:
                    continue
                for y2 in nodes:
                    if y2 != y and (y2, y) not in lt:
                        continue
                    if (x2, y2) not in dj and x2 != y2:
                        dj.add((x2, y2))
                        changed = True
    return dj


def odnet(x, y, lt, dj):
    if x == y:
        return EQ
    if (x, y) in lt:
        return PP
    if (y, x) in lt:
        return PPI
    if (x, y) in dj:
        return DR
    return PO


def check(nodes, lt, dj, lab, budget):
    bad = {}

    def note(k):
        bad[k] = bad.get(k, 0) + 1

    ns = sorted(nodes, key=lambda t: (len(t), sorted(t)))
    for x in ns:
        if (x, x) in lt:
            note("ltIrr")
        if (x, x) in dj:
            note("djIrr")
        for y in ns:
            if (x, y) in dj and (y, x) not in dj:
                note("djSym")
            if (x, y) in lt and (x, y) in dj:
                note("ltNotDj")
            for z in ns:
                if (x, y) in lt and (y, z) in lt and (x, z) not in lt:
                    note("ltTr")
                if odnet(x, z, lt, dj) not in CT[(odnet(x, y, lt, dj),
                                                  odnet(y, z, lt, dj))]:
                    note("comp")
    # djDown
    for (x, y) in dj:
        for x2 in ns:
            if x2 != x and (x2, x) not in lt:
                continue
            for y2 in ns:
                if y2 != y and (y2, y) not in lt:
                    continue
                if x2 != y2 and (x2, y2) not in dj:
                    note("djDown")
    # ee_all, EVERY relation
    for x in ns:
        for d in lab(x):
            if d[0] != "all":
                continue
            for y in ns:
                if odnet(x, y, lt, dj) == d[1] and d[2] not in lab(y):
                    note("ee_all_" + d[1])
    # e_ex -- VERTICAL only.  This probe builds the vertical closure; the
    # horizontal one is mixNodes' `b` recursion and is not modelled here, so
    # checking exists-DR / exists-PO would report the probe's own omission.
    for x in ns:
        for d in lab(x):
            if d[0] != "ex" or d[1] not in (PP, PPI):
                continue
            if not any(odnet(x, y, lt, dj) == d[1] and d[2] in lab(y) for y in ns):
                note("e_ex_" + d[1])
    return bad


def rand_c(rng, depth):
    if depth == 0 or rng.random() < 0.2:
        i = rng.randrange(3)
        return ("at", i) if rng.random() < 0.6 else ("nat", i)
    r = rng.random()
    if r < 0.2:
        return ("and", rand_c(rng, depth - 1), rand_c(rng, depth - 1))
    if r < 0.32:
        return ("or", rand_c(rng, depth - 1), rand_c(rng, depth - 1))
    if r < 0.78:
        return ("ex", rng.choice([PP, PPI, PP, PPI]), rand_c(rng, depth - 1))
    return ("all", rng.choice([PP, PPI, PP, PPI, DR]), rand_c(rng, depth - 1))


def main(trials=9000, seed=606060, usize=5, use_edges=True):
    print(f"WP115 -- acceptance test, declared edges "
          f"{'ON' if use_edges else 'OFF (CONTROL)'}\n")
    rng = random.Random(seed)
    regs = subsets(set(range(usize)))
    tested = withedges = nochoice = 0
    fails = {}
    for _ in range(trials):
        c0 = rand_c(rng, rng.randint(2, 4))
        if not po_free(c0):
            continue
        m = rng.sample(regs, min(len(regs), rng.randint(3, 8)))
        val = {}
        for a in range(3):
            for x in m:
                val[(a, x)] = rng.random() < 0.5
        root = next((x for x in m if sat(m, val, x, c0)), None)
        if root is None:
            continue
        nodes, ups, cuts, lab = build(m, val, c0, root)
        lt = tcl(ups, nodes)
        new = declared_edges(m, val, c0, nodes, cuts, lab, lt) if use_edges else set()
        if new is None:
            nochoice += 1
            continue
        edges = {e for e in new if isinstance(e, tuple) and len(e) == 2
                 and not isinstance(e[0], frozenset) is False}
        extra = {e for e in new if isinstance(e, tuple)}
        pts = {p for p in new if isinstance(p, frozenset)}
        nodes2 = set(nodes) | pts
        lt2 = tcl(ups | {e for e in extra if len(e) == 2
                         and isinstance(e[0], frozenset)
                         and isinstance(e[1], frozenset)}, nodes2)
        if extra:
            withedges += 1
        dj2 = od_from(nodes2, lt2, m)
        tested += 1
        for k, v in check(nodes2, lt2, dj2, lab, mdepth(c0) + 1).items():
            fails[k] = fails.get(k, 0) + v
    print(f"  certificates built and fully checked : {tested}")
    print(f"  of which carry a DECLARED EDGE       : {withedges}")
    print(f"  abandoned (no cycle-free choice)     : {nochoice}")
    print()
    if not fails:
        print("  ALL OBLIGATIONS HOLD:")
        print("    ODStruct axioms (ltIrr/ltTr/djSym/djIrr/ltNotDj/djDown)")
        print("    composition closure of odNet")
        print("    ee_all for EVERY relation")
        print("    e_ex for EVERY node")
    else:
        print("  FAILURES (obligation -> count):")
        for k in sorted(fails):
            print(f"    {k:16s} {fails[k]}")
    print("\n" + "=" * 72)
    print("  A failure names the obligation the declared edge breaks.  Note the")
    print("  DECLARED EDGE count: if it is small the run says little about the")
    print("  edge itself, whatever the failure column shows.")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    main(use_edges=False)
    print()
    raise SystemExit(main(use_edges=True))
