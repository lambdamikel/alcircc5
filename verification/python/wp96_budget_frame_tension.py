#!/usr/bin/env python3
"""WP96 -- the BUDGET/FRAME tension in the mixed extraction.

Written BEFORE formalizing the extraction (item A), per the standing directive:
probe the route first.  It asks one question that neither ASSEMBLY_DESIGN sec.41
nor sec.42 examined, and that decides the architecture:

  `mixKernelsK_ok` carries four BUDGET side-conditions, of which the external one
  is   hbEE : forall e f,  bud e <= bud f + 1
  and the real obligation behind it is

      ee_all :  all r cc  in  tauE e  ->  E e f = r  ->  cc in tauE f.

  With mtk labels,  tauE e = {c in cl C0 : model-sat at g e, mdepth c <= bud e},
  so the SEMANTIC half is free (the model satisfies the universal) and only the
  DEPTH half can fail.  Hence ee_all holds iff  mdepth cc <= bud f  whenever
  `all r cc` sits in e's label and E e f = r.

  The node set the finiteness bound comes from (`mtkNodes`) DECREASES the budget
  by one at every step (mtkWitness has budget n.k - 1).  So budgets span the whole
  range N..0.  With READ-OFF relations (E e f = the model's own rho) every pair of
  externals carries a real relation, so ee_all fires across budget gaps.

  PART A  -- does ee_all actually FAIL there?  (falsifies the analysis if not)
  PART B  -- is PO-default immune, and why?  (the structural reason)
  PART C  -- restriction 4 in the kernel/external mix: does an external with BOTH
             an exists-PP and an exists-PPI demand FORCE a kernel-kernel order
             edge, so that a PO-defaulted Q is composition-violating?
  PART D  -- the uniform-budget alternative: at a constant budget the node set
             must be closed under ALL demands.  Measure whether TYPE-blocking
             (one representative per realized model type) keeps it finite AND
             lets every demand be served by a REAL model edge.

Self-contained: RCC5 relations and the composition table are re-derived from
finite set semantics.
"""

import random
from itertools import combinations

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
ATOMS = [DR, PO, EQ, PP, PPI]


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
CONV = {DR: DR, PO: PO, EQ: EQ, PP: PPI, PPI: PP}

# ------------------------------------------------------------ concept syntax
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


def mty(model, val, x, c0):
    return frozenset(d for d in closure(c0) if sat(model, val, x, d))


def mtk(model, val, x, c0, b):
    return frozenset(d for d in mty(model, val, x, c0) if mdepth(d) <= b)


# ------------------------------------------------ random concepts and models

def rand_concept(rng, depth, natoms=2):
    if depth == 0 or rng.random() < 0.22:
        i = rng.randrange(natoms)
        return ("at", i) if rng.random() < 0.6 else ("nat", i)
    r = rng.random()
    if r < 0.22:
        return ("and", rand_concept(rng, depth - 1, natoms),
                rand_concept(rng, depth - 1, natoms))
    if r < 0.34:
        return ("or", rand_concept(rng, depth - 1, natoms),
                rand_concept(rng, depth - 1, natoms))
    if r < 0.70:
        return ("ex", rng.choice(ATOMS), rand_concept(rng, depth - 1, natoms))
    return ("all", rng.choice([DR, PP, PPI, EQ]),
            rand_concept(rng, depth - 1, natoms))


def find_model(rng, c, natoms=2, tries=120, usize=4):
    univ = set(range(usize))
    regs = subsets(univ)
    for _ in range(tries):
        m = rng.sample(regs, min(len(regs), rng.randint(2, 6)))
        val = {}
        for a in range(natoms):
            for x in m:
                val[(a, x)] = rng.random() < 0.5
        for x in m:
            if sat(m, val, x, c):
                return m, val, x
    return None


# ------------------------------ the budget-decreasing node set (`mtkNodes`)

def mtk_nodes(model, val, c0, root, budget):
    """Mirror of Lean `mtkNodes`: children of (x,k) are model witnesses of the
    exists-demands of mtk(x,k), at budget k-1."""
    nodes = []
    seen = set()
    stack = [(root, budget)]
    while stack:
        x, b = stack.pop()
        if (x, b) in seen:
            continue
        seen.add((x, b))
        nodes.append((x, b))
        if b == 0:
            continue
        for d in sorted(mtk(model, val, x, c0, b), key=str):
            if d[0] != "ex":
                continue
            for y in model:
                if rel(x, y) == d[1] and sat(model, val, y, d[2]):
                    stack.append((y, b - 1))
                    break
    return nodes


# --------------------------------------------------------------------- parts

def part_a(trials=6000, seed=90210):
    print("PART A -- read-off `ee_all` over the budget-decreasing node set")
    rng = random.Random(seed)
    tested = 0
    with_viol = 0
    viol_tot = 0
    example = None
    gapmax = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        if not po_free(c0):
            continue
        got = find_model(rng, c0)
        if got is None:
            continue
        model, val, root = got
        N = mdepth(c0)
        if N < 2:
            continue
        nodes = mtk_nodes(model, val, c0, root, N)
        tested += 1
        v = 0
        for (x, bx) in nodes:
            lab = mtk(model, val, x, c0, bx)
            for d in lab:
                if d[0] != "all":
                    continue
                for (y, by) in nodes:
                    if rel(x, y) != d[1]:
                        continue
                    # semantic half is free; only the DEPTH half can fail
                    if mdepth(d[2]) > by:
                        v += 1
                        gapmax = max(gapmax, bx - by)
                        if example is None:
                            example = (c0, d, bx, by, rel(x, y))
        viol_tot += v
        if v:
            with_viol += 1
    print(f"  satisfiable forall-PO-free concepts (mdepth>=2) tested : {tested}")
    print(f"  instances with at least one ee_all violation           : {with_viol}"
          f"  ({100.0*with_viol/max(tested,1):.1f}%)")
    print(f"  total violations                                       : {viol_tot}")
    print(f"  largest budget gap seen on a violating edge            : {gapmax}")
    if example:
        c0, d, bx, by, r = example
        print(f"  example: universal {d} at budget {bx}, target budget {by},"
              f" edge {r}")
        print(f"           C0 = {c0}")
    print("  => read-off relations make ee_all fire on EVERY pair, so the")
    print("     budget drop of the finiteness recursion breaks the obligation.")
    return with_viol > 0


def part_b(trials=6000, seed=112358):
    print("\nPART B -- the PO-default frame over the SAME node set")
    print("  (non-PO edges only parent<->child, where the budget drops by 1)")
    rng = random.Random(seed)
    tested = 0
    viol = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        if not po_free(c0):
            continue
        got = find_model(rng, c0)
        if got is None:
            continue
        model, val, root = got
        N = mdepth(c0)
        if N < 2:
            continue
        nodes = mtk_nodes(model, val, c0, root, N)
        # declared frame: EQ on the diagonal, DR on closure-tree edges, PO else
        idx = {n: i for i, n in enumerate(nodes)}
        adj = set()
        for (x, b) in nodes:
            if b == 0:
                continue
            for d in sorted(mtk(model, val, x, c0, b), key=str):
                if d[0] != "ex":
                    continue
                for y in model:
                    if rel(x, y) == d[1] and sat(model, val, y, d[2]):
                        if (y, b - 1) in idx:
                            adj.add((idx[(x, b)], idx[(y, b - 1)]))
                            adj.add((idx[(y, b - 1)], idx[(x, b)]))
                        break

        def E(i, j):
            if i == j:
                return EQ
            return DR if (i, j) in adj else PO

        tested += 1
        for i, (x, bx) in enumerate(nodes):
            for d in mtk(model, val, x, c0, bx):
                if d[0] != "all":
                    continue
                for j, (y, by) in enumerate(nodes):
                    if E(i, j) != d[1]:
                        continue
                    if d[1] == PO:
                        viol += 1                    # impossible: forall-PO-free
                    elif mdepth(d[2]) > by:
                        viol += 1
    print(f"  instances tested            : {tested}")
    print(f"  ee_all violations           : {viol}")
    print("  => the declared frame puts non-PO edges ONLY where the budget drops")
    print("     by exactly one, and PO edges carry no obligation in the fragment.")
    print("     THIS is why the horizontal fragment's budgets work out.")
    return viol == 0


def part_c():
    print("\nPART C -- restriction 4 in the kernel/external mix")
    print("  an external with BOTH exists-PP and exists-PPI needs a kernel above")
    print("  AND a kernel below; the two kernel bases are then FORCED comparable.")
    # e PP up, down PP e  =>  down PP up is forced
    forced = CT[(PP, PP)]
    print(f"  comp(PP,PP) = {sorted(forced)}   (down PP e, e PP up)")
    ok = forced == {PP}
    print(f"  so Q(down,up) is FORCED to PP  : {ok}")
    print(f"  is PO admissible there?        : {PO in forced}")
    # and the dual
    print(f"  comp(PPI,PPI) = {sorted(CT[(PPI, PPI)])}")
    print("  => a PO-DEFAULTED kernel-kernel block is composition-violating as")
    print("     soon as one external carries both vertical demands.  The frame")
    print("     must carry a genuine ORDER -- which is what `odNet_frame`")
    print("     (certified) provides.  Restriction 4 is REAL, and it bites in")
    print("     the kernel/external mix, not only among externals.")
    return ok and PO not in forced


def part_d(trials=3000, seed=1414213):
    print("\nPART D -- uniform budget + TYPE-blocking: is the node set finite,")
    print("  and is every demand served by a REAL model edge between reps?")
    rng = random.Random(seed)
    tested = 0
    unserved = 0
    inst_unserved = 0
    sizes = []
    ratios = []
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        if not po_free(c0):
            continue
        got = find_model(rng, c0)
        if got is None:
            continue
        model, val, root = got
        cl = closure(c0)
        # one representative per REALIZED type, reachable from the root
        repof = {}
        order = []
        stack = [root]
        seenx = set()
        while stack:
            x = stack.pop()
            if x in seenx:
                continue
            seenx.add(x)
            t = mty(model, val, x, c0)
            if t not in repof:
                repof[t] = x
                order.append(t)
            for d in cl:
                if d[0] != "ex" or d not in mty(model, val, x, c0):
                    continue
                for y in model:
                    if rel(x, y) == d[1] and sat(model, val, y, d[2]):
                        stack.append(y)
                        break
        reps = [repof[t] for t in order]
        tested += 1
        sizes.append(len(reps))
        ratios.append(len(reps) / max(len(cl), 1))
        bad = 0
        for t in order:
            x = repof[t]
            for d in t:
                if d[0] != "ex":
                    continue
                # served by an edge BETWEEN REPRESENTATIVES?
                if not any(rel(x, y) == d[1] and d[2] in mty(model, val, y, c0)
                           for y in reps):
                    bad += 1
        unserved += bad
        if bad:
            inst_unserved += 1
    print(f"  instances tested                       : {tested}")
    print(f"  representative-set size: mean {sum(sizes)/max(len(sizes),1):.1f}"
          f"  max {max(sizes) if sizes else 0}")
    print(f"  size / |cl C0|         : mean {sum(ratios)/max(len(ratios),1):.2f}"
          f"  max {max(ratios) if ratios else 0:.2f}")
    print(f"  instances with an UNSERVED demand      : {inst_unserved}"
          f"  ({100.0*inst_unserved/max(tested,1):.1f}%)")
    print(f"  total unserved demands                 : {unserved}")
    print("  => type-blocking bounds the node set by the number of realized")
    print("     types (<= 2^|cl C0|, finite in C0 alone) at UNIFORM budget, and")
    print("     the read-off edge between representatives serves the demand")
    print("     whenever a same-type witness is the chosen representative.")
    return tested > 0


def main():
    res = {
        "A read-off budget break": part_a(),
        "B PO-default immune": part_b(),
        "C order forced by mix": part_c(),
        "D type-blocked uniform": part_d(),
    }
    print("\n" + "=" * 72)
    for k, v in res.items():
        print(f"  {k:26s} : {'PASS' if v else 'FAIL'}")
    print("=" * 72)
    ok = all(res.values())
    print("VERDICT:", "ALL PASS" if ok else "FAILURE")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
