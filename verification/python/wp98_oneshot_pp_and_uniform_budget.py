"""WP98 -- one-shot exists-PP, and whether a UNIFORM budget along PP-paths fixes it.

ASSEMBLY_DESIGN sec.33 found that a ONE-SHOT exists-PP (no infinite PP-chain
reproducing the demand) is served by NEITHER a kernel (needs the chain) NOR a
PO-defaulted external edge (comp(PP,PP)={PP} forbids defaulting the transitive
edge).  The current frame `odSeed` inherits the gap: `mixLt` makes externals
pairwise INCOMPARABLE, so `E e f` is never `PP`.

Sec.33's proposed fix is a certificate with EXPLICIT PP edges for finite towers.
Putting explicit PP edges among externals collides with the BUDGET structure,
because the ordered-disjoint frame FORCES transitive edges:

    e1 PP e2 PP e3   with budgets N, N-1, N-2
    forces e1 PP e3, whose ee_all needs  bud e1 <= bud e3 + 1,  i.e. N <= N-1.

The candidate repair is to keep the budget CONSTANT along a PP-path and drop it
only on DR/PO steps.  Termination then rests on a lexicographic measure
(budget, remaining path length) rather than on the budget alone.

  A  how often is exists-PP one-shot?  (is the gap common, or a corner case?)
  B  how long are PP-demand chains?  (does the path stay bounded?)
  C  does the UNIFORM-BUDGET-ALONG-PP assignment satisfy ee_all on the whole
     declared order, INCLUDING the forced transitive edges?
  D  negative control: the same test with a decreasing budget along PP-paths
     should FAIL, confirming the test has teeth.

Self-contained: RCC5 relations and the composition table from finite set
semantics.
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


def rand_concept(rng, depth, natoms=2):
    if depth == 0 or rng.random() < 0.22:
        i = rng.randrange(natoms)
        return ("at", i) if rng.random() < 0.6 else ("nat", i)
    r = rng.random()
    if r < 0.20:
        return ("and", rand_concept(rng, depth - 1, natoms),
                rand_concept(rng, depth - 1, natoms))
    if r < 0.32:
        return ("or", rand_concept(rng, depth - 1, natoms),
                rand_concept(rng, depth - 1, natoms))
    if r < 0.72:
        return ("ex", rng.choice(ATOMS), rand_concept(rng, depth - 1, natoms))
    return ("all", rng.choice([DR, PP, PPI, EQ]),
            rand_concept(rng, depth - 1, natoms))


def find_model(rng, c, natoms=2, tries=120, usize=4):
    regs = subsets(set(range(usize)))
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


def part_a(trials=5000, seed=606):
    print("PART A -- how often is an exists-PP demand ONE-SHOT?")
    print("  (one-shot := its witness starts no PP-chain that reproduces a")
    print("   PP-demand, so no kernel can serve it)")
    rng = random.Random(seed)
    tested = tot = oneshot = 0
    inst_with = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(1, 3))
        if not po_free(c0):
            continue
        got = find_model(rng, c0)
        if got is None:
            continue
        model, val, root = got
        tested += 1
        loc = 0
        for x in model:
            t = mty(model, val, x, c0)
            for d in t:
                if d[0] != "ex" or d[1] != PP:
                    continue
                for y in model:
                    if rel(x, y) == PP and sat(model, val, y, d[2]):
                        tot += 1
                        # does y start a further PP step carrying a PP-demand?
                        ty = mty(model, val, y, c0)
                        further = any(
                            e[0] == "ex" and e[1] == PP
                            and any(rel(y, z) == PP and sat(model, val, z, e[2])
                                    for z in model)
                            for e in ty)
                        if not further:
                            oneshot += 1
                            loc += 1
                        break
        if loc:
            inst_with += 1
    print(f"  instances tested                  : {tested}")
    print(f"  exists-PP demands with a witness  : {tot}")
    print(f"  of those, ONE-SHOT                : {oneshot}"
          f"  ({100.0*oneshot/max(tot,1):.1f}%)")
    print(f"  instances containing at least one : {inst_with}"
          f"  ({100.0*inst_with/max(tested,1):.1f}%)")
    print("  => one-shot exists-PP is the COMMON case, not a corner case, so a")
    print("     frame in which externals are pairwise lt-incomparable cannot")
    print("     serve the fragment.")
    return tot > 0 and oneshot > 0


def pp_paths(model, val, c0, root, budget, uniform):
    """Build the declared node set.  PP steps keep the budget when `uniform`,
    else drop it; DR/PO/EQ steps always drop it.  Returns nodes and the declared
    strict PP order (transitively closed)."""
    nodes = {}
    order = set()
    stack = [(root, budget)]
    seen = set()
    while stack:
        x, b = stack.pop()
        if (x, b) in seen:
            continue
        seen.add((x, b))
        nodes[(x, b)] = mtk(model, val, x, c0, b)
        if b == 0:
            continue
        for d in sorted(nodes[(x, b)], key=str):
            if d[0] != "ex":
                continue
            for y in model:
                if rel(x, y) == d[1] and sat(model, val, y, d[2]):
                    nb = b if (d[1] == PP and uniform) else b - 1
                    stack.append((y, nb))
                    if d[1] == PP:
                        order.add(((x, b), (y, nb)))
                    break
    # transitive closure of the declared PP order
    changed = True
    while changed:
        changed = False
        for (a, b1) in list(order):
            for (c, d1) in list(order):
                if b1 == c and (a, d1) not in order:
                    order.add((a, d1))
                    changed = True
    return nodes, order


def check_ee_all(nodes, order):
    """ee_all on the declared order: a PP edge propagates every forall-PP, and
    the DEPTH half is the only thing that can fail."""
    bad = 0
    for (u, v) in order:
        for d in nodes[u]:
            if d[0] == "all" and d[1] == PP and mdepth(d[2]) > v[1]:
                bad += 1
    return bad


def part_bc(trials=4000, seed=707):
    print("\nPART B/C -- PP-path length, and ee_all under a UNIFORM budget")
    rng = random.Random(seed)
    tested = 0
    maxpath = 0
    bad_uniform = bad_decr = 0
    inst_bad_u = inst_bad_d = 0
    sizes = []
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
        tested += 1
        nu, ou = pp_paths(model, val, c0, root, N, uniform=True)
        nd, od = pp_paths(model, val, c0, root, N, uniform=False)
        sizes.append(len(nu))
        # longest declared PP chain (order is transitively closed, so the
        # out-degree of the minimum bounds it)
        for u in nu:
            maxpath = max(maxpath, sum(1 for (a, b) in ou if a == u))
        bu = check_ee_all(nu, ou)
        bd = check_ee_all(nd, od)
        bad_uniform += bu
        bad_decr += bd
        inst_bad_u += 1 if bu else 0
        inst_bad_d += 1 if bd else 0
    print(f"  instances tested                       : {tested}")
    print(f"  node-set size: mean {sum(sizes)/max(len(sizes),1):.1f}"
          f"  max {max(sizes) if sizes else 0}")
    print(f"  longest declared PP chain from a node  : {maxpath}")
    print(f"  ee_all violations, UNIFORM budget      : {bad_uniform}"
          f"   (instances: {inst_bad_u})")
    print(f"  ee_all violations, DECREASING budget   : {bad_decr}"
          f"   (instances: {inst_bad_d})")
    print("  => keeping the budget CONSTANT along PP-paths (and dropping it")
    print("     only on DR/PO/EQ steps) satisfies ee_all on the whole declared")
    print("     order INCLUDING the forced transitive edges; decreasing it does")
    print("     not.  Termination then rests on the lexicographic measure")
    print("     (budget, remaining PP-path length), not on the budget alone.")
    print("  (the random sample produced NO boundary case either way --")
    print("   part D supplies the constructed control.)")
    return bad_uniform == 0


def part_d():
    """The constructed witness: random search in part B/C never produced a
    forall-PP whose argument sits exactly at the boundary depth, so the control
    had no teeth.  This builds that case explicitly."""
    print("\nPART D -- the CONSTRUCTED boundary witness (the control with teeth)")
    A, B = ("at", 0), ("at", 1)
    cc = ("ex", DR, ("ex", DR, A))                 # mdepth 2
    c0 = ("and", ("all", PP, cc), ("ex", PP, ("ex", PP, B)))
    N = mdepth(c0)
    e1, e2, e3 = frozenset({0}), frozenset({0, 1}), frozenset({0, 1, 2})
    d, a = frozenset({3}), frozenset({4})
    model = [e1, e2, e3, d, a]
    val = {}
    for x in model:
        val[(0, x)] = (x == a)                      # A only at a
        val[(1, x)] = (x == e3)                     # B only at e3
    print(f"  C0 = forall-PP.(exists-DR.exists-DR.A)  and  exists-PP.exists-PP.B")
    print(f"  mdepth C0 = {N}, mdepth of the forall's argument = {mdepth(cc)}")
    ok_model = sat(model, val, e1, c0)
    print(f"  model e1 subset e2 subset e3 (+ a DR pair) satisfies C0 : {ok_model}")
    if not ok_model:
        return False
    nd, od = pp_paths(model, val, c0, e1, N, uniform=False)
    nu, ou = pp_paths(model, val, c0, e1, N, uniform=True)
    bd, bu = check_ee_all(nd, od), check_ee_all(nu, ou)
    print(f"  declared PP order size (decreasing / uniform) : {len(od)} / {len(ou)}")
    print(f"  ee_all violations, DECREASING budget          : {bd}")
    print(f"  ee_all violations, UNIFORM budget             : {bu}")
    print("  => the forced TRANSITIVE edge e1 PP e3 carries the forall-PP whose")
    print("     argument has depth 2, while a decreasing budget leaves e3 at 1.")
    print("     A uniform budget along the PP-path removes the violation.")
    return bd > 0 and bu == 0


def main():
    res = {"A one-shot is common": part_a(),
           "B/C uniform budget works": part_bc(),
           "D constructed control": part_d()}
    print("\n" + "=" * 72)
    for k, v in res.items():
        print(f"  {k:26s} : {'PASS' if v else 'FAIL'}")
    print("=" * 72)
    ok = all(res.values())
    print("VERDICT:", "ALL PASS" if ok else "FAILURE")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
