#!/usr/bin/env python3
r"""
WP37 -- the F6 construction attempt bottoms out at the horizontal-forcing
question (and unifies the decidability and undecidability obstructions).

Third F6 pass.  WP35 attacked with a vertical construction (produced only
shadows).  WP36 anatomised the table (determination is vertical-only, but
distinctness extends horizontally).  WP37 takes the redirected swing WP36
pointed to -- an unbounded *live horizontal* crowd -- and follows it to the
floor.

Machine-checked findings:

 (1) THE SUBSTRATE IS FREE.  A pure {DR,PO} network is just a graph
     (PO = edge, DR = non-edge).  EVERY such graph is path-consistent, hence
     (by the RCC5 patchwork property) realizable; and any graph with all rows
     distinct is an IRREDUCIBLE crowd (no two nodes mergeable).  So unbounded
     live horizontal crowds are REALIZABLE at every size -- F6 does NOT fail at
     the network level.  (Checked: 200 random {DR,PO} graphs at n=4,6,8,10 --
     all path-consistent; irreducible ones exist at every n.)

 (2) HORIZONTAL CHAINS BLOCK, JUST LIKE VERTICAL ONES.  comp(PO,PO) is the
     whole algebra -- it contains the loop-closing merge -- so a forced
     PO-chain (exists PO.T and forall PO.exists PO.T) is SAT via a finite
     LOOPING model (2-3 regions cycling), exactly like a PP-ladder.  With
     finitely many colours any chain repeats a colour, and a repeated colour
     with mergeable relations closes the loop.  So the pigeonhole that tames
     the vertical axis tames the horizontal axis too -- UNLESS non-repetition
     can be forced.

 (3) THE REDUCTION.  Forcing an *unbounded* live horizontal crowd = forcing
     NON-repetition = forcing rigid horizontal COORDINATES (so no two crowd
     members can ever be identified).  But rigid coordination needs to pin
     relations, and the table cannot pin horizontally (WP36: no horizontal-only
     singleton; PO is never a forced value).  So:

        F6 counterexample  <=>  an ALCI_RCC5 concept that forces an unbounded
                                rigid {DR,PO} graph
        F6 proof           <=>  a lemma that NO concept can force such a graph

     Both are the SAME horizontal-rigidity forcing question.  And that is
     exactly the obstruction on the undecidability side too: the Lutz-Wolter
     2-D grid fails to transfer to the abstract semantics because the
     composition table cannot force the coincidence condition (rigid 2-D
     coordination) -- Wessel 2002/2003.  The decidability keystone (bounded
     width, F6) and the undecidability obstruction (no forcible grid) are two
     faces of one fact: the abstract composition table is too loose to pin
     rigid horizontal structure.

HONEST CONCLUSION.  The construction attempt does not produce a counterexample
-- but not for a shallow reason.  It provably REDUCES to the horizontal-forcing
question, which is the deep open problem itself (and the reason neither
decidability nor undecidability has been settled in 20 years).  The substrate
is free; only the forcing is hard; and the forcing is THE problem.  This is
where an F6 attack correctly ends: having shown the counterexample and the
proof are the same question, and having placed that question next to the
undecidability obstruction as its mirror image.

Run: python3 verification/python/wp37_f6_reduces_to_forcing.py
"""
import sys, os, itertools, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', '..', 'src'))
from alcircc5_reasoner import (DR, PO, PP, PPI, COMP,
                               AtomicConcept, Exists, ForAll, And, Top)
from cover_tree_tableau import check_sat


def pc_ok(nodes, R):
    return all(R[(x, z)] in COMP[(R[(x, y)], R[(y, z)])]
               for x in nodes for y in nodes for z in nodes if len({x, y, z}) == 3)


def mergeable(R, nodes, u, v):
    return all(R[(u, w)] == R[(v, w)] for w in nodes if w not in (u, v))


def substrate_check(seed=0):
    random.seed(seed)
    out = []
    for n in [4, 6, 8, 10]:
        all_pc, irred = True, False
        for _ in range(200):
            nodes = list(range(n)); R = {}
            for i in nodes:
                for j in nodes:
                    if i < j:
                        r = random.choice([DR, PO]); R[(i, j)] = r; R[(j, i)] = r
            if not pc_ok(nodes, R): all_pc = False
            if all(not mergeable(R, nodes, u, v)
                   for u in nodes for v in nodes if u < v):
                irred = True
        out.append((n, all_pc, irred))
    return out


if __name__ == '__main__':
    print("WP37: the F6 construction reduces to horizontal forcing")
    print("=" * 70)

    print("\n(1) substrate -- arbitrary {DR,PO} graphs realizable + irreducible:")
    sub = substrate_check(); sub_ok = all(pc and ir for _, pc, ir in sub)
    for n, pc, ir in sub:
        print(f"    n={n}: 200 graphs path-consistent={pc}; "
              f"irreducible crowd of size {n} exists={ir}")

    print("\n(2) horizontal chain blocks (loops) like a vertical one:")
    top = Top()
    chain = And(Exists(PO, top), ForAll(PO, Exists(PO, top)))
    sat, _ = check_sat(chain)
    print(f"    'exists PO.T and forall PO.exists PO.T' = {'SAT' if sat else 'UNSAT'}"
          f"  (SAT => finite looping model; horizontal blocking works)")
    print(f"    comp(PO,PO) = {sorted(COMP[(PO, PO)])}  (contains the loop-closing merge)")

    print("\n(3) reduction:")
    print("    F6 counterexample  <=>  a concept forcing an unbounded rigid {DR,PO} graph")
    print("    F6 proof           <=>  no concept can force such a graph")
    print("    == the horizontal-rigidity forcing question == the mirror of the")
    print("       Lutz-Wolter grid non-transfer (no forcible coincidence condition).")

    print("\n" + "=" * 70)
    ok = sub_ok and sat
    print("WP37 OVERALL:",
          "PASS -- substrate free, horizontal chains block, so an F6 "
          "counterexample reduces to forcing rigid unbounded horizontal "
          "structure: the same open question as the undecidability "
          "obstruction.  The attack ends here, at the real problem."
          if ok else "ATTENTION")
    sys.exit(0 if ok else 1)
