#!/usr/bin/env python3
"""WP114 -- can the residue be served by a DECLARED edge to the blocker's witness?

ASSEMBLY_DESIGN sec. 123.  The residue is one shape: a cut leaf v, blocked by a
with mty v = mty a, carrying a demand pointing AWAY from a.

THE ROUTE.  The certificate's frame is DECLARED, not read off the model, and
ee_all reads only LABELS.  Since mty v = mty a, v and a carry the SAME label, so
a universal at v has the same body obligation as at a -- and a really does have
its witness s above it.  So DECLARING v < s satisfies ee_all even though the
model may not relate v and s.

THE OBSTRUCTION.  The declared order is the transitive closure of the
extraction's own steps, and it must stay a strict order (mElt_irrefl).  Adding
v < s creates a cycle exactly when s is an ANCESTOR of v -- then s < v already.

THE MEASUREMENT.  For each residue demand, does a have a D-witness that is NOT
an ancestor of v?  If yes, the declared edge is available and cycle-free.  If the
only D-witnesses of a lie on the path from a to v, the route is blocked there.


ASSEMBLY_DESIGN sec. 115.2.  The mixed quadrant's vertical closure is certified
down to one narrow item.  `cutNodes` stops expanding at a repeated type but
KEEPS the node (sec. 113's fix).  Such a node -- a CUT LEAF -- has demands whose
witnesses were never added.  Its type equals an expanded ancestor's, which is
exactly the blocking configuration, and wp8's round-7 lesson governs it: the lap
is PP-labelled, never EQ.

Three questions, in order of what they would cost to fix:

  A  Do cut leaves with unserved demands ARISE at all?  If the closure happens to
     close before any cut fires, there is nothing to do.
  B  When one arises, is the demand served by a node ALREADY in the set with the
     right relation?  That is the cheapest possible repair -- no new node.
  C  Does the blocked lap CONTINUE, i.e. from the cut leaf does the same demand
     path reach another node of the same type?  That is what turns a blocked lap
     into a KERNEL (the round-7 unravelling), and it is the uniformization
     question in its sharpest local form.

Question C is the one that has been argued in prose for three sections without
being measured.  A "no" there means blocking-to-kernel fails for one-shot
demands and the cut leaf needs different treatment; a "yes, always" means the
kernel is available and sec. 114's kernelData_of_chain applies.

Self-contained: RCC5 relations re-derived from finite set semantics.

SCOPE, stated up front: finite set models.  Per the companion rule in memory, a
rate that moves when the generator changes is a property of the generator, so
part D varies the model class.
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


def mtk(model, val, c0, x, k):
    return frozenset(d for d in mty(model, val, c0, x) if mdepth(d) <= k)


def persistent(model, val, c0, x, D, direction):
    ex = ("ex", direction, D)
    return ex in mty(model, val, c0, x) and sat(model, val, x, ("all", direction, ex))


def build_cut(model, val, c0, root, cap=600):
    """The Lean `cutNodes`: expand a demand's witness unless its type is already
    on the path, in which case KEEP the witness but do not expand.

    Returns (set of nodes, list of cut leaves, expanded set)."""
    budget = mdepth(c0) + 1
    nodes = {root}
    cut_leaves = []
    expanded = {root}
    # stack of (node, seen-types-on-this-path)
    stack = [(root, frozenset({mty(model, val, c0, root)}), [root])]
    steps = 0
    while stack and steps < cap:
        steps += 1
        x, seen, path = stack.pop()
        for d in sorted(mtk(model, val, c0, x, budget)):
            if d[0] != "ex" or d[1] not in (PP, PPI):
                continue
            D = d[2]
            if persistent(model, val, c0, x, D, d[1]):
                continue                        # kernel-served
            for y in model:
                if rel(x, y) == d[1] and sat(model, val, y, D):
                    ty = mty(model, val, c0, y)
                    nodes.add(y)
                    if ty in seen:
                        blk = next((z for z in path
                                    if mty(model, val, c0, z) == ty), None)
                        cut_leaves.append((y, blk, frozenset(path)))
                    else:
                        if y not in expanded:
                            expanded.add(y)
                            stack.append((y, seen | {ty}, path + [y]))
                    break
    return nodes, cut_leaves, expanded


def unserved_at(model, val, c0, nodes, v):
    """Demands at v with no server inside `nodes`."""
    budget = mdepth(c0) + 1
    out = []
    for d in sorted(mtk(model, val, c0, v, budget)):
        if d[0] != "ex" or d[1] not in (PP, PPI):
            continue
        D = d[2]
        if persistent(model, val, c0, v, D, d[1]):
            continue
        if not any(rel(v, w) == d[1] and sat(model, val, w, D) for w in nodes):
            out.append((d[1], D))
    return out


def lap_continues(model, val, c0, v):
    """Question C: from v, does some ascending demand path reach another node of
    v's own type?  That is what turns the blocked lap into a kernel."""
    budget = mdepth(c0) + 1
    tv = mty(model, val, c0, v)
    seen = {v}
    frontier = [v]
    for _ in range(6):
        nxt = []
        for x in frontier:
            for d in mtk(model, val, c0, x, budget):
                if d[0] != "ex" or d[1] != PP:
                    continue
                for y in model:
                    if rel(x, y) == PP and sat(model, val, y, d[2]):
                        if y not in seen:
                            if mty(model, val, c0, y) == tv:
                                return True
                            seen.add(y)
                            nxt.append(y)
                        break
        frontier = nxt
        if not frontier:
            break
    return False


def declared_edge_available(model, val, c0, v, blk, path_set, d, D):
    """Does the blocker have a D-witness in the right direction that is NOT an
    ancestor of v?  Ancestors are the nodes on the closure path to v."""
    if blk is None:
        return None
    cand = [s for s in model
            if rel(blk, s) == d and sat(model, val, s, D)]
    if not cand:
        return None
    return any(s not in path_set for s in cand)


def classify(model, val, c0, nodes, v, blk):
    """Split v's unserved demands into the FREE cases (sec.121) and the residue.

      leaf BELOW blocker + exists-PP   -> free (blocked_below_inherits)
      leaf ABOVE blocker + exists-PPI  -> free (blocked_above_inherits_ppi)
      the other two                    -> residue
    """
    if blk is None or blk == v:
        return 0, 0
    r = rel(v, blk)
    free = hard = 0
    for (d, D) in unserved_at(model, val, c0, nodes, v):
        if r == PP and d == PP:
            free += 1                      # v inside blocker, demand upward
        elif r == PPI and d == PPI:
            free += 1                      # v outside blocker, demand downward
        else:
            hard += 1
    return free, hard


def rand_c(rng, depth, vert=True):
    if depth == 0 or rng.random() < 0.2:
        i = rng.randrange(3)
        return ("at", i) if rng.random() < 0.6 else ("nat", i)
    r = rng.random()
    if r < 0.2:
        return ("and", rand_c(rng, depth - 1, vert), rand_c(rng, depth - 1, vert))
    if r < 0.32:
        return ("or", rand_c(rng, depth - 1, vert), rand_c(rng, depth - 1, vert))
    pool = [PP, PPI, PP, PPI, DR] if vert else [PP, PPI, DR, EQ]
    if r < 0.68:
        return ("ex", rng.choice(pool), rand_c(rng, depth - 1, vert))
    return ("all", rng.choice([PP, PPI, DR, EQ]), rand_c(rng, depth - 1, vert))


def sweep(seed, trials, usize, vert=True):
    rng = random.Random(seed)
    regs = subsets(set(range(usize)))
    tot = leaves = with_unserved = served_in_set = laps = lap_yes = 0
    served_in_set_none = [0]
    for _ in range(trials):
        c0 = rand_c(rng, rng.randint(2, 4), vert)
        if not po_free(c0):
            continue
        m = rng.sample(regs, min(len(regs), rng.randint(3, min(len(regs), 10))))
        val = {}
        for a in range(3):
            for x in m:
                val[(a, x)] = rng.random() < 0.5
        root = None
        for x in m:
            if sat(m, val, x, c0):
                root = x
                break
        if root is None:
            continue
        tot += 1
        nodes, cuts, _ = build_cut(m, val, c0, root)
        for (v, blk, pset) in cuts:
            leaves += 1
            u = unserved_at(m, val, c0, nodes, v)
            if u:
                with_unserved += 1
                for (d, D) in u:
                    laps += 1
                    r = declared_edge_available(m, val, c0, v, blk, pset, d, D)
                    if r is True:
                        lap_yes += 1
                    elif r is None:
                        served_in_set_none[0] += 1
            else:
                served_in_set += 1
    return (tot, leaves, with_unserved, served_in_set, laps, lap_yes,
            served_in_set_none[0])


def report(label, r):
    tot, leaves, unserved, served, free, hard, nowit = r
    print(f"  {label}")
    print(f"    concepts with a model             : {tot}")
    print(f"    CUT LEAVES that arose             : {leaves}")
    if leaves:
        print(f"    leaves with UNSERVED demands      : {unserved} "
              f"({100.0*unserved/leaves:.1f}%)")
        print(f"    leaves already served in-set      : {served} "
              f"({100.0*served/leaves:.1f}%)")
        n = free
        print(f"    RESIDUE demands                   : {n}")
        if n:
            print(f"      declared edge AVAILABLE           : {hard} "
                  f"({100.0*hard/n:.1f}%)")
            print(f"      blocker has NO witness at all     : {nowit} "
                  f"({100.0*nowit/n:.1f}%)")
            print(f"      only ancestors -> CYCLE           : "
                  f"{n - hard - nowit} ({100.0*(n-hard-nowit)/n:.1f}%)")
    return leaves


def main():
    print("PART A/B/C -- cut leaves, vertical-biased concepts")
    r1 = report("universe 5", sweep(4242, 5000, 5))
    print()
    print("PART D -- generator variation")
    r2 = report("universe 6", sweep(9191, 4000, 6))
    print()
    r3 = report("universe 5, uniform relations", sweep(313, 5000, 5, vert=False))
    print("\n" + "=" * 72)
    print("  READ:")
    print("   sec.121 proves the two orientations where the leaf's demand points")
    print("   TOWARD its blocker: PP-transitivity carries the blocker's own server")
    print("   to the leaf.  This measures how much of the residue that removes.")
    print("   The remaining cases point AWAY from the blocker, where")
    print("   comp(PPI,PP) = {PPI,PO,PP,EQ} forces nothing.")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
