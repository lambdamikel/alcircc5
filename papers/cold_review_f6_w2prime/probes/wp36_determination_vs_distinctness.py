#!/usr/bin/env python3
r"""
WP36 -- the structural anatomy of RCC5 forcing, and what it says about F6.

Second adversarial pass at F6 (bounded live width).  Where WP35 attacked with
a construction, WP36 asks a structural question about the composition table
itself: what can RCC5 FORCE, and along which axis?

FINDINGS (all machine-checked, exhaustive over the table):

 (1) There are EXACTLY FOUR singleton compositions in RCC5 -- the only
     compositions that FULLY DETERMINE a relation:
        comp(DR,PPI) = {DR}      comp(PP,DR) = {DR}
        comp(PP,PP)  = {PP}      comp(PPI,PPI)= {PPI}
     EVERY one of them uses a VERTICAL (PP/PPI) leg.  There is NO singleton
     composition with both legs horizontal (DR/PO).  Moreover PO is never the
     forced value of ANY composition: a relation can never be pinned to
     exactly PO.

     => FULL DETERMINATION (a "shadow" -- a composition-forced, recoverable
        edge that costs nothing in the blueprint) always requires the vertical
        axis.  This is the exhaustive-table explanation of WP35: the natural
        "spy sees unboundedly many neighbours" attack could only ever make
        shadows, because the forcing that produced them (comp(PP,DR)={DR},
        comp(DR,PPI)={DR}) is vertical.

 (2) BUT determination is not the same as DISTINCTNESS.  Two same-type regions
     are mergeable (can be set EQ) UNLESS some constraint forces them != EQ.
     And EQ-exclusion CAN be achieved horizontally: a shared anchor w with
        u DR w  and  w PO v   =>   u-v in {DR,PO,PP}   (EXCLUDES EQ)
     forces u != v -- yet {DR,PO,PP} is NON-singleton, so the u-v edge is
     LIVE (its DR/PO/PP value is a free choice, not a shadow).

     => DISTINCTNESS (EQ-exclusion) extends to the HORIZONTAL axis, while
        DETERMINATION (singletons) does not.  The two notions come apart.

HONEST CONCLUSION.  Finding (1) is a clean, exhaustive reason WP35's attack
produced only shadows -- and mild further evidence for F6.  But finding (2)
shows (1) does NOT close F6: a *live* horizontal distinct crowd is not ruled
out, because you can force regions apart horizontally (via DR-anchors) while
their mutual relations stay undetermined (live).  So F6 remains genuinely open,
and the frontier is now pinpointed exactly:

   Can a concept force UNBOUNDEDLY many regions to coexist at one interface,
   pairwise made distinct by shared horizontal DR-anchors, with their pairwise
   relations LIVE (undetermined) and un-mergeable -- without the distinctness
   collapsing into vertical shadows (as in WP35)?

That is the precise shape a real F6 counterexample must take, and the precise
lemma a real F6 proof must exclude.  (Connection: this is the same
composition-table looseness -- no horizontal-only determination, PO never
forced -- that blocks the Lutz-Wolter 2-D grid encoding from transferring to
the abstract semantics; see README.  The reason undecidability can't be forced
and the reason width should be bounded appear to be one and the same fact.)

Run: python3 verification/python/wp36_determination_vs_distinctness.py
"""
import sys, os, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', '..', 'src'))

def derive_full(n=6):
    U = range(n)
    subs = [frozenset(c) for k in range(1, n + 1)
            for c in itertools.combinations(U, k)]
    def r(a, b):
        if a == b: return 'EQ'
        if not a & b: return 'DR'
        if a < b: return 'PP'
        if b < a: return 'PPI'
        return 'PO'
    t = {}
    for a in subs:
        for b in subs:
            for c in subs:
                t.setdefault((r(a, b), r(b, c)), set()).add(r(a, c))
    return {k: frozenset(v) for k, v in t.items()}

FULL = derive_full()
REL = ['DR', 'PO', 'PP', 'PPI']            # off-diagonal atoms
VERT = {'PP', 'PPI'}

def part1_singletons():
    singles = {(a, b): sorted(FULL[(a, b)])[0]
               for a in REL for b in REL if FULL[(a, b)] == frozenset({sorted(FULL[(a, b)])[0]})}
    # recompute cleanly: singleton iff |value|==1
    singles = {(a, b): next(iter(FULL[(a, b)]))
               for a in REL for b in REL if len(FULL[(a, b)]) == 1}
    all_vertical = all((a in VERT or b in VERT) for (a, b) in singles)
    no_horiz_only = not any((a not in VERT and b not in VERT) for (a, b) in singles)
    po_ever_forced = any(v == 'PO' for v in singles.values())
    return singles, all_vertical, no_horiz_only, po_ever_forced

def part2_distinctness():
    # a shared anchor w: u (leg1) w (leg2) v ; forces u!=v iff EQ excluded
    rows = []
    for leg2 in REL:
        v = FULL[('DR', leg2)]
        rows.append(('DR', leg2, sorted(v), 'EQ' not in v, len(v) > 1))
    return rows

if __name__ == '__main__':
    print("WP36: determination vs distinctness in RCC5")
    print("=" * 70)

    singles, all_vert, no_horiz, po_forced = part1_singletons()
    print("\n(1) singleton (fully-determining) compositions:")
    for (a, b), v in singles.items():
        print(f"    comp({a},{b}) = {{{v}}}   vertical-leg? {a in VERT or b in VERT}")
    print(f"    exactly {len(singles)} singletons; ALL have a vertical leg: {all_vert}")
    print(f"    no horizontal-only singleton: {no_horiz}")
    print(f"    PO is ever a forced value: {po_forced}  (=> PO never determined)")

    print("\n(2) horizontal distinctness via a shared DR-anchor "
          "(u DR w, w R v):")
    live_distinct = False
    for leg1, leg2, val, excl_eq, nonsingle in part2_distinctness():
        tag = ""
        if excl_eq and nonsingle:
            tag = "  <= forces u!=v AND stays LIVE (undetermined)"
            live_distinct = True
        print(f"    comp({leg1},{leg2}) = {val}   forces!=EQ? {excl_eq}   "
              f"live(non-singleton)? {nonsingle}{tag}")

    print("\n" + "=" * 70)
    ok = (len(singles) == 4 and all_vert and no_horiz and not po_forced
          and live_distinct)
    print("WP36 OVERALL:",
          "PASS -- determination is vertical-only (4 singletons, all vertical; "
          "PO never forced) => explains WP35's shadows; BUT distinctness is "
          "achievable horizontally and stays live => the 4-singleton fact does "
          "NOT close F6.  Frontier pinpointed: a live horizontally-distinct "
          "crowd." if ok else "ATTENTION -- table facts changed")
    sys.exit(0 if ok else 1)
