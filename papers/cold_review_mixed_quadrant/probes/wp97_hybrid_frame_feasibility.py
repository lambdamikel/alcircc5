#!/usr/bin/env python3
"""WP97 -- is the HYBRID frame always realizable?

wp96 showed each single architecture fails somewhere:

  read-off  + budget-decreasing node set : `ee_all` BREAKS (wp96 A, 4.1%)
  PO-default                             : budgets fine (wp96 B, 0 violations)
                                           but no order, and wp96 C shows an
                                           external with BOTH vertical demands
                                           FORCES a kernel-kernel order edge
  read-off  + type-blocking              : coverage fails (wp96 D, 8.4%)

The architecture the three results point at is a HYBRID declared frame:

  externals   pairwise lt-INCOMPARABLE, related by EQ / DR / PO
              (= the PO-default frame, so budgets drop along tree edges)
  kernels     carry a genuine ORDER (lt) among themselves and to externals
  everything  one ORDERED-DISJOINT structure, so `odNet_frame` (certified)
              supplies `frame_q`

This probe asks the question that decides whether the hybrid can always be built:

  A  Given externals with an arbitrary DR/PO pattern, and kernels each attached
     to an external by PP or PPI, does an ORDERED-DISJOINT completion always
     exist?  Exhaustive over small configurations.
  B  Does it survive the wp96-C forcing (one external with BOTH directions)?
  C  Which constraint is the binding one -- `disj_down` or `lt_trans`?
  D  Does the completion still SERVE every demand, i.e. are the edges it needs
     present with the right labels?

Self-contained: RCC5 relations and the composition table re-derived from finite
set semantics.
"""

from itertools import combinations, product

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


# ------------------------------------------- ordered-disjoint structures

def od_ok(n, lt, dj):
    """OrderedDisjoint: lt a strict order, dj symmetric/irreflexive/downward
    closed, comparable never disjoint."""
    for x in range(n):
        if lt[x][x] or dj[x][x]:
            return False
        for y in range(n):
            if dj[x][y] != dj[y][x]:
                return False
            if lt[x][y] and dj[x][y]:
                return False
            for z in range(n):
                if lt[x][y] and lt[y][z] and not lt[x][z]:
                    return False
    le = lambda a, b: a == b or lt[a][b]
    for x in range(n):
        for y in range(n):
            if not dj[x][y]:
                continue
            for x2 in range(n):
                if not le(x2, x):
                    continue
                for y2 in range(n):
                    if le(y2, y) and not dj[x2][y2]:
                        return False
    return True


def od_net(lt, dj):
    def R(x, y):
        if x == y:
            return EQ
        if lt[x][y]:
            return PP
        if lt[y][x]:
            return PPI
        if dj[x][y]:
            return DR
        return PO
    return R


def closed(n, R):
    for x in range(n):
        for y in range(n):
            if CONV[R(x, y)] != R(y, x):
                return False
            for z in range(n):
                if R(x, z) not in CT[(R(x, y), R(y, z))]:
                    return False
    return True


# ----------------------------------------------------- the hybrid search

def solve_hybrid(nE, extdisj, attach, extra_lt=()):
    """externals 0..nE-1 (pairwise lt-incomparable, disjointness = `extdisj`);
    kernels nE.. ; `attach` = list of (kernel, external, direction) with
    direction 'up'  meaning  external lt kernel   (serves the external's exists-PP)
    direction 'down' meaning kernel lt external   (serves its exists-PPI).
    Returns an ordered-disjoint completion or None.  Brute force over the free
    entries, so keep the sizes small."""
    nK = len(attach)
    n = nE + nK
    base_lt = [[False] * n for _ in range(n)]
    for kidx, (e, d) in enumerate(attach):
        k = nE + kidx
        if d == "up":
            base_lt[e][k] = True
        else:
            base_lt[k][e] = True
    for (a, b) in extra_lt:
        base_lt[a][b] = True
    # free lt entries: any pair NOT both external (externals stay incomparable)
    free_lt = [(x, y) for x in range(n) for y in range(n)
               if x != y and not base_lt[x][y] and not (x < nE and y < nE)]
    free_dj = [(x, y) for x in range(n) for y in range(n) if x < y
               and not (x < nE and y < nE)]
    # externals' mutual disjointness is GIVEN
    for ltbits in product([False, True], repeat=len(free_lt)):
        lt = [row[:] for row in base_lt]
        for (x, y), v in zip(free_lt, ltbits):
            if v:
                lt[x][y] = True
        # quick reject: strict order
        bad = any(lt[x][x] for x in range(n))
        if bad:
            continue
        if any(lt[x][y] and lt[y][z] and not lt[x][z]
               for x in range(n) for y in range(n) for z in range(n)):
            continue
        for djbits in product([False, True], repeat=len(free_dj)):
            dj = [[False] * n for _ in range(n)]
            for x in range(nE):
                for y in range(nE):
                    if extdisj[x][y]:
                        dj[x][y] = True
            for (x, y), v in zip(free_dj, djbits):
                if v:
                    dj[x][y] = True
                    dj[y][x] = True
            if od_ok(n, lt, dj) and closed(n, od_net(lt, dj)):
                return lt, dj
    return None


def part_a():
    print("PART A -- exhaustive: does an ordered-disjoint completion exist?")
    print("  externals pairwise incomparable, arbitrary DR/PO pattern;")
    print("  kernels attached up/down to externals.")
    tot = 0
    fail = []
    for nE in (1, 2, 3):
        pairs = [(x, y) for x in range(nE) for y in range(nE) if x < y]
        for djbits in product([False, True], repeat=len(pairs)):
            extdisj = [[False] * nE for _ in range(nE)]
            for (x, y), v in zip(pairs, djbits):
                extdisj[x][y] = extdisj[y][x] = v
            for nK in (1, 2):
                for att in product([(e, d) for e in range(nE)
                                    for d in ("up", "down")], repeat=nK):
                    tot += 1
                    if solve_hybrid(nE, extdisj, list(att)) is None:
                        fail.append((nE, djbits, att))
    print(f"  configurations tried : {tot}")
    print(f"  with NO completion   : {len(fail)}")
    for f in fail[:5]:
        print(f"    {f}")
    return not fail


def part_b():
    print("\nPART B -- the wp96-C forcing: ONE external with BOTH directions")
    extdisj = [[False]]
    sol = solve_hybrid(1, extdisj, [(0, "up"), (0, "down")])
    ok = sol is not None
    print(f"  external 0 with a kernel above AND below : "
          f"{'realizable' if ok else 'NO COMPLETION'}")
    if ok:
        lt, dj = sol
        R = od_net(lt, dj)
        print(f"    Q(down,up) = {R(2, 1)}   (comp(PP,PP) forces PP)")
        print(f"    K(up, e)   = {R(1, 0)}   K(down, e) = {R(2, 0)}")
    # two DR externals, each with a kernel below: the kernels must be DR too
    extdisj2 = [[False, True], [True, False]]
    sol2 = solve_hybrid(2, extdisj2, [(0, "down"), (1, "down")])
    ok2 = sol2 is not None
    print(f"  two DR externals, a kernel below each    : "
          f"{'realizable' if ok2 else 'NO COMPLETION'}")
    if ok2:
        lt, dj = sol2
        R = od_net(lt, dj)
        print(f"    Q(k0,k1) = {R(2, 3)}   (disj_down forces DR)")
    return ok and ok2


def part_c():
    print("\nPART C -- which axiom is binding?  drop one and see what changes")
    extdisj = [[False, True], [True, False]]
    att = [(0, "down"), (1, "down")]
    sol = solve_hybrid(2, extdisj, att)
    lt, dj = sol
    R = od_net(lt, dj)
    n = 4
    # is a PO-defaulted kernel-kernel block admissible instead?
    dj2 = [row[:] for row in dj]
    dj2[2][3] = dj2[3][2] = False               # try PO between the kernels
    ok_od = od_ok(n, lt, dj2)
    ok_cl = closed(n, od_net(lt, dj2))
    print(f"  forcing Q(k0,k1)=PO : ordered-disjoint {ok_od}, closed {ok_cl}")
    print("  => `disj_down` is the binding axiom here: kernels under DR")
    print("     externals inherit the disjointness.  A PO default is WRONG,")
    print("     which is precisely why the frame must be an order+disjointness")
    print("     structure and not a default.")
    return not (ok_od and ok_cl)


def part_d():
    print("\nPART D -- do the completions SERVE the demands they were built for?")
    bad = 0
    tot = 0
    for nE in (1, 2, 3):
        pairs = [(x, y) for x in range(nE) for y in range(nE) if x < y]
        for djbits in product([False, True], repeat=len(pairs)):
            extdisj = [[False] * nE for _ in range(nE)]
            for (x, y), v in zip(pairs, djbits):
                extdisj[x][y] = extdisj[y][x] = v
            for nK in (1, 2):
                for att in product([(e, d) for e in range(nE)
                                    for d in ("up", "down")], repeat=nK):
                    sol = solve_hybrid(nE, extdisj, list(att))
                    if sol is None:
                        continue
                    lt, dj = sol
                    R = od_net(lt, dj)
                    tot += 1
                    for kidx, (e, d) in enumerate(att):
                        k = nE + kidx
                        want = PP if d == "up" else PPI
                        if R(e, k) != want:
                            bad += 1
                    for x in range(nE):
                        for y in range(nE):
                            if x != y and extdisj[x][y] and R(x, y) != DR:
                                bad += 1
    print(f"  completions checked        : {tot}")
    print(f"  attachment/DR label errors : {bad}")
    print("  => every completion realizes the attachment edges with the exact")
    print("     labels the demands need, and keeps the externals' DR pattern.")
    return bad == 0


def main():
    res = {
        "A completion exists": part_a(),
        "B forcing survived": part_b(),
        "C disj_down binding": part_c(),
        "D demands served": part_d(),
    }
    print("\n" + "=" * 72)
    for k, v in res.items():
        print(f"  {k:22s} : {'PASS' if v else 'FAIL'}")
    print("=" * 72)
    ok = all(res.values())
    print("VERDICT:", "ALL PASS" if ok else "FAILURE")
    print()
    print("  The HYBRID frame -- externals lt-incomparable (so the PO-default")
    print("  budget structure of wp96 B is preserved) inside ONE ordered-disjoint")
    print("  structure whose order lives on the kernels -- is realizable for")
    print("  every small configuration, realizes the attachment labels exactly,")
    print("  and needs `odNet_frame` because `disj_down` forbids the PO default.")
    print()
    print("  SCOPE: frame feasibility only, exhaustive at nE<=3, nK<=2.  It does")
    print("  NOT show the node set is bounded, nor that phases stabilize --")
    print("  those are `hstab`/`hrectQ` and the counting, tested elsewhere.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
