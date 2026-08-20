#!/usr/bin/env python3
"""WP92 -- capacity of the PO-DEFAULT certificate frame (ASSEMBLY_DESIGN sec. 40).

The file contains two mixed-certificate architectures:

  read-off (mixKernels)     E/K/Q are the model's own relations.  Needs hstab and
                            hrectQ (the whole sec.39 apparatus), and exists-PO at
                            a phase needs the pool.  Supports BOTH directions.
  PO-default (mtkKernelsDR) E/K/Q DECLARED, Q identically PO.  No hstab, no
                            hrectQ, exists-PO free.  ASCENDING only, and only ONE
                            PPI edge (to the kernel root v0).

Option (c): before committing to either, check whether a dir-generalized
PO-default frame can actually host what the fragment needs.  The binding question
is CAPACITY, not direction: a phase may carry several distinct exists-PPI demands,
so the frame would need SEVERAL ppi-children, where mtkKernelsDR declares one.

Adding declared edges to a PO-default frame is not free -- section 33 already
showed a PP edge cannot be PO-defaulted (comp(PP,PP)={PP} forces the transitive
edge, which the PO default would set to PO).  This probe asks the same question
for PPI edges, and for their interaction with DR children, by checking
composition closure of the declared net EXHAUSTIVELY.

Self-contained: RCC5 relations and the composition table are re-derived from
finite set semantics, per project convention.
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
    univ = set(range(n))
    regs = subsets(univ)
    table = {(r, s): set() for r in ATOMS for s in ATOMS}
    for a in regs:
        for b in regs:
            r = rel(a, b)
            for c in regs:
                table[(r, rel(b, c))].add(rel(a, c))
    return table


CT = comp_table(4)
CONV = {DR: DR, PO: PO, EQ: EQ, PP: PPI, PPI: PP}


# ------------------------------------------------- the declared PO-default net

def declared_net(P, a, b, c, dadj=None):
    """Nodes: P phases (ascending PP), `a` ppi-children (inside every phase),
    `b` dr-children (disjoint from every phase), `c` plain PO-externals.

    Declared exactly as the PO-default architecture does, with the FORCED edges
    filled in rather than PO-defaulted:
      phase_i - phase_j : PP  (i<j)          the kernel chain
      phase   - u_s     : PPI                ppi-children sit inside
      phase   - d_t     : DR                 dr-children are disjoint
      phase   - o_r     : PO                 the default
      u - u'            : PO                 (default; comp allows it)
      u - d             : DR                 FORCED: comp(PP,DR) = {DR}
      u - o             : PO
      d - d'            : dadj ? DR : PO     the skeleton's choice
      d - o, o - o'     : PO
    """
    nodes = ([("p", i) for i in range(P)] + [("u", i) for i in range(a)]
             + [("d", i) for i in range(b)] + [("o", i) for i in range(c)])
    idx = {n: i for i, n in enumerate(nodes)}

    def R(x, y):
        if x == y:
            return EQ
        (tx, ix), (ty, iy) = x, y
        if tx == "p" and ty == "p":
            return PP if ix < iy else PPI
        if tx == "p" and ty == "u":
            return PPI
        if tx == "u" and ty == "p":
            return PP
        if tx == "p" and ty == "d":
            return DR
        if tx == "d" and ty == "p":
            return DR
        if {tx, ty} == {"u", "d"}:
            return DR                      # forced by comp(PP,DR) = {DR}
        if tx == "d" and ty == "d":
            if dadj is not None:
                return DR if dadj(ix, iy) else PO
            return PO
        return PO                          # everything else defaults to PO
    return nodes, R


def closed(nodes, R):
    """Composition closure + converse coherence of the declared net."""
    bad = []
    for x in nodes:
        for y in nodes:
            if CONV[R(x, y)] != R(y, x):
                bad.append(("conv", x, y))
    for x in nodes:
        for y in nodes:
            for z in nodes:
                if R(x, z) not in CT[(R(x, y), R(y, z))]:
                    bad.append(("comp", x, y, z, R(x, y), R(y, z), R(x, z)))
    return bad


# --------------------------------------------------------------------- parts

def part_a():
    print("PART A -- composition facts the declared net leans on")
    checks = {
        ("PP", "DR"): {DR},
        ("PP", "PP"): {PP},
        ("PPI", "PPI"): {PPI},
    }
    ok = True
    for (r, s), exp in checks.items():
        got = CT[(r, s)]
        ok &= got == exp
        print(f"  comp({r:3s},{s:3s}) = {sorted(got)!s:22s} expected {sorted(exp)}")
    print(f"  PO in comp(PO,x) for every x : {all(PO in CT[(PO, x)] for x in ATOMS)}")
    print(f"  PO in comp(x,PO) for every x : {all(PO in CT[(x, PO)] for x in ATOMS)}")
    return ok


def part_b(maxP=4, maxA=3, maxB=3, maxC=2):
    """Is the declared net closed, and how many ppi-children can it host?"""
    print("\nPART B -- capacity: how many PPI-children can the frame host?")
    worst = None
    allok = True
    for P in range(1, maxP + 1):
        for a in range(0, maxA + 1):
            for b in range(0, maxB + 1):
                for c in range(0, maxC + 1):
                    nodes, R = declared_net(P, a, b, c)
                    bad = closed(nodes, R)
                    if bad:
                        allok = False
                        if worst is None:
                            worst = (P, a, b, c, bad[0])
    print(f"  swept P<={maxP} phases, a<={maxA} ppi-children, b<={maxB} dr-children,"
          f" c<={maxC} po-externals")
    if allok:
        print("  ALL declared nets composition-closed and converse-coherent")
        print("  => the PO-default frame hosts ARBITRARILY MANY ppi-children,")
        print("     not just the single v0 edge mtkKernelsDR declares.  The")
        print("     u-d edge must be DR (forced), and u-u' PO is consistent.")
    else:
        print(f"  FAILURE at (P,a,b,c) = {worst[:4]}: {worst[4]}")
    return allok


def part_c(maxP=4, maxB=4):
    """The dr-children skeleton: may adjacent/non-adjacent DR children coexist?"""
    print("\nPART C -- the DR-children skeleton (dadj free or forced?)")
    ok = True
    fails = 0
    total = 0
    for P in range(1, maxP + 1):
        for b in range(2, maxB + 1):
            for bits in product([False, True], repeat=b * (b - 1) // 2):
                pairs = list(combinations(range(b), 2))
                m = {p: v for p, v in zip(pairs, bits)}

                def dadj(i, j, m=m):
                    return m.get((min(i, j), max(i, j)), False)
                nodes, R = declared_net(P, 0, b, 0, dadj=dadj)
                total += 1
                if closed(nodes, R):
                    fails += 1
                    ok = False
    print(f"  swept {total} skeletons (P<={maxP}, b<={maxB}, all dadj choices)")
    print(f"  non-closed: {fails}")
    if ok:
        print("  => dadj is FREE: any DR/PO pattern among the dr-children is")
        print("     composition-closed, so the skeleton imposes no extra burden.")
    return ok


def part_d():
    """Section 33's negative, tested correctly: PP edges CHAINING.

    NOTE a modelling correction.  Two PP-SIBLINGS (both containing the same
    phase) are perfectly fine PO-defaulted: comp(PPI,PP) is all of RCC5, so PO
    between them is allowed -- part D originally tested that and, rightly, found
    no violation.  Section 33's obstruction is different: it is PP edges in a
    CHAIN.  e PP w and w PP g force e PP g by comp(PP,PP) = {PP}, so the
    non-adjacent pair cannot be PO-defaulted."""
    print("\nPART D -- can PP edges CHAIN in a PO-default frame?  (sec.33)")
    # siblings first, to record that they are fine
    sib = [("p", 0), ("w", 0), ("w", 1)]

    def Rsib(x, y):
        if x == y:
            return EQ
        (tx, _), (ty, _) = x, y
        if tx == "p" and ty == "w":
            return PP
        if tx == "w" and ty == "p":
            return PPI
        return PO
    sib_ok = not closed(sib, Rsib)
    print(f"  two PP-SIBLINGS of one phase, PO-defaulted : "
          f"{'closed (fine)' if sib_ok else 'NOT closed'}")

    # now the chain e PP w PP g with e-g PO-defaulted
    ch = [("e", 0), ("w", 0), ("g", 0)]
    order = {("e", 0): 0, ("w", 0): 1, ("g", 0): 2}

    def Rch(x, y):
        if x == y:
            return EQ
        i, j = order[x], order[y]
        if abs(i - j) == 1:
            return PP if i < j else PPI
        return PO                       # the non-adjacent pair, PO-defaulted
    bad = closed(ch, Rch)
    print(f"  PP-CHAIN e PP w PP g, e-g PO-defaulted     : "
          f"{'NOT closed' if bad else 'closed'}")
    if bad:
        v = [t for t in bad if t[0] == "comp"][0]
        print(f"    violation: comp({v[4]},{v[5]}) forces the pair, default gave {v[6]}")
    print("  => PP SIBLINGS are free; PP CHAINS are not.  So going PO-default")
    print("     does NOT fix the one-shot exists-PP gap (sec.33) -- but the gap")
    print("     is narrower than 'no PP edges': it is specifically NESTED")
    print("     exists-PP, matching ascNodes' deferred non-nested restriction.")
    return sib_ok and bool(bad)


def part_e(maxP=5):
    """The realistic one-shot exists-PP configuration: a PP-child attached to a
    KERNEL PHASE, inside the chain.  Part D showed PP siblings are fine and only
    PP CHAINS break, so the question is whether a pp-child can coexist with the
    phase chain -- which is itself a PP chain.

    Declared: phases p_0 PP ... PP p_{P-1}; the child w attached at phase i, so
    p_j PP w for every j <= i (FORCED upward by comp(PP,PP) = {PP}); and
    p_j - w = PO for j > i (allowed, comp(PPI,PP) is unrestricted)."""
    print("\nPART E -- a PP-child attached INSIDE the phase chain (one-shot)")
    allok = True
    for P in range(1, maxP + 1):
        for i in range(P):
            nodes = [("p", j) for j in range(P)] + [("w", 0)]

            def R(x, y, i=i):
                if x == y:
                    return EQ
                (tx, ix), (ty, iy) = x, y
                if tx == "p" and ty == "p":
                    return PP if ix < iy else PPI
                if tx == "p" and ty == "w":
                    return PP if ix <= i else PO
                if tx == "w" and ty == "p":
                    return PPI if iy <= i else PO
                return PO
            if closed(nodes, R):
                allok = False
                print(f"    NOT closed at P={P}, attach={i}")
    print(f"  swept P<={maxP} phases, every attachment point")
    if allok:
        print("  ALL closed => a one-shot (NON-NESTED) exists-PP demand at a")
        print("  phase IS servable by a declared PP edge, provided the edge is")
        print("  propagated DOWN the chain (p_j PP w for every j <= i, forced by")
        print("  comp(PP,PP)={PP}) and left PO above.")
        print("  This NARROWS sec.33: its argument assumed the pp-child itself")
        print("  has a PP-successor.  Without one there is no chain and no")
        print("  violation -- the gap is specifically NESTED exists-PP.")
    return allok


def main():
    res = {
        "A comp facts": part_a(),
        "B ppi-capacity": part_b(),
        "C dr-skeleton free": part_c(),
        "D pp-child still blocked": part_d(),
        "E one-shot PP servable": part_e(),
    }
    print("\n" + "=" * 68)
    for k, v in res.items():
        print(f"  {k:26s} : {'PASS' if v else 'FAIL'}")
    print("=" * 68)
    ok = all(res.values())
    print("VERDICT:", "ALL PASS" if ok else "FAILURE")
    print()
    print("  VERDICT for option (c): the PO-default frame has the capacity the")
    print("  fragment needs.")
    print("   B: arbitrarily many PPI-children (mtkKernelsDR declares only one),")
    print("      with u-d forced DR and u-u' PO -- so exists-PPI at a phase is")
    print("      coverable, which is what a dir-generalization needs.")
    print("   C: the DR skeleton is free -- any dadj pattern is closed.")
    print("   D: PP SIBLINGS are free; only PP CHAINS violate closure.")
    print("   E: hence a one-shot NON-NESTED exists-PP at a phase IS servable by")
    print("      a declared PP edge propagated down the chain.")
    print()
    print("  So sec.33's one-shot exists-PP gap is NARROWER than recorded: its")
    print("  argument assumed the pp-child has a PP-successor.  What remains open")
    print("  is specifically NESTED exists-PP -- matching ascNodes' own deferred")
    print("  'non-nested restriction'.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
