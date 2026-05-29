"""
WP10 -- round-9 forced-verticalization certificate-EMISSION test (self-contained).

This is the one part of round-9's new machinery that the earlier scripts do not
exercise end-to-end.  The opus4.8_review scripts established the pieces:
  * rcc5_compose.py        -- reproduces the D-1 *defect* of round-8.
  * fix_feasibility.py     -- the trace arithmetic (monotone DR>PO>PPI, PPI
                              absorbing, bounded threshold).
  * repaired_certificate.py-- HAND-PLACES the splice on a depth-8 prefix and
                              checks RCC5 frame axioms + concept demands.

What was still missing -- and what this script does -- is to glue them into the
actual round-9 *emission* pipeline, deriving (not hand-placing) the splice and
then building and validating a genuine round-9 certificate OBJECT:

  (1) DETECT  : compute the ancestor trace r_m = L(a_m, w) by composition +
                universal pruning; confirm shape DR* PO* PPI* (monotone-trace
                lemma) and find the threshold k_0 (bounded-threshold lemma);
                if no composition-legal label survives at some level, EMISSION
                FAILS -> REJECT (this is how the UNSAT sibling is refused).
  (2) SPLICE  : if the trace has a PPI-tail, splice w into E_up at a_{k_0}
                (splice-faithfulness: only because the forced label is already
                PPI).  Otherwise w stays an ordinary DR/PO side witness.
  (3) BUILD   : assemble a finite certificate as occurrence-sensitive pair
                shapes with incidence tags iota in {self,eq,up,down,side_R,
                front_R} and the label map l_Q; the infinite tower is
                regularised to a request-closed cycle (finite prefix whose top
                profile recurs).  Reach_PP carries the splice up the tail, so
                every (a_m, w) becomes a 'down' (PPI) pair, NOT a bounded side
                pair.
  (4) VALIDATE: run the round-9 validity clauses on the emitted object --
                converse, triple composition (V6), universal safety
                (V2/V7/V12), equality (V9, no EQ across distinct laps without a
                port -> blocking-not-equality), existential request discharge
                (with the PP-eventuality discharged by the cycle), and the
                global residual-frontier lemma (every front pair is DR or PO).

Expected outcome: C0' emits a VALID certificate; the UNSAT sibling is REJECTED,
and the rejection is shown to be "all routings fail" (splice -> forall PPI.Y
clash; no-splice -> the forced PPI cannot be a DR/PO residual-frontier pair).

The composition table is transcribed verbatim from the round-8 expanded
companion, Section 2.1 (identical to opus4.8_review/rcc5_compose.py); this
script is otherwise self-contained, like wp7/wp8/wp9.
"""

from itertools import product

# --------------------------------------------------------------------------- #
#  RCC5 base relations + composition table (round-8 expanded companion, S2.1)
# --------------------------------------------------------------------------- #
EQ, DR, PO, PP, PPI = "EQ", "DR", "PO", "PP", "PPI"
BASE = (EQ, DR, PO, PP, PPI)
INV = {EQ: EQ, DR: DR, PO: PO, PP: PPI, PPI: PP}

COMP = {
    (EQ, EQ): {EQ}, (EQ, DR): {DR}, (EQ, PO): {PO}, (EQ, PP): {PP}, (EQ, PPI): {PPI},
    (DR, EQ): {DR}, (DR, DR): set(BASE), (DR, PO): {DR, PO, PP},
    (DR, PP): {DR, PO, PP}, (DR, PPI): {DR},
    (PO, EQ): {PO}, (PO, DR): {DR, PO, PPI}, (PO, PO): set(BASE),
    (PO, PP): {PO, PP}, (PO, PPI): {DR, PO, PPI},
    (PP, EQ): {PP}, (PP, DR): {DR}, (PP, PO): {DR, PO, PP},
    (PP, PP): {PP}, (PP, PPI): set(BASE),
    (PPI, EQ): {PPI}, (PPI, DR): {DR, PO, PPI}, (PPI, PO): {PO, PPI},
    (PPI, PP): {EQ, PO, PP, PPI}, (PPI, PPI): {PPI},
}


def compose(R, S):
    return COMP[(R, S)]


# --------------------------------------------------------------------------- #
#  Concept model for the D-1 witness family.
#
#  A node carries:
#    pos       : flags known TRUE  (concept names it satisfies)
#    neg       : flags known FALSE (concept names it violates)
#    univ      : list of (R, D): a  forall R.D  demand
#    pp_demand : True if the node carries  exists PP.G  (an upward eventuality)
#    po_demand : (D,) if the node carries  exists PO.D  (a side eventuality), else None
#  All tower nodes share one "G profile"; the cycle has period 1.
# --------------------------------------------------------------------------- #
def scenario_C0prime():
    """C0' = (exists PP.G) and (exists PO.~X),  G = (forall PO.X) and (exists PP.G).
    SAT.  The round-9 emission should splice w and emit a valid certificate."""
    G_univ = [(PO, "X")]
    return {
        "name": "C0' = (EPP.G) & (EPO.~X),  G = (APO.X) & (EPP.G)   [SAT]",
        "G_univ": G_univ,
        "u":   dict(pos=set(),  neg=set(),       univ=[],     pp_demand=True,  po_demand=("notX",)),
        # the PO-witness w of u:  w in ~X
        "w":   dict(pos=set(),  neg={"X"},        univ=[],     pp_demand=False, po_demand=None),
        # the recurring tower (G) profile
        "a":   dict(pos={"G"},  neg=set(),        univ=G_univ, pp_demand=True,  po_demand=None),
        "rho_uw": PO,     # u PO w  (the side relation of the witness)
        "expect": "VALID",
    }


def scenario_UNSAT_sibling():
    """UNSAT sibling: G also carries forall PPI.Y, and the PO-witness is in ~X and ~Y.
    Every routing of w fails -> emission must REJECT."""
    G_univ = [(PO, "X"), (PPI, "Y")]
    return {
        "name": "C0  = (EPP.G) & (EPO.(~X&~Y)),  G = (APO.X)&(APPI.Y)&(EPP.G)   [UNSAT]",
        "G_univ": G_univ,
        "u":   dict(pos=set(),  neg=set(),        univ=[],     pp_demand=True,  po_demand=("notXY",)),
        "w":   dict(pos=set(),  neg={"X", "Y"},   univ=[],     pp_demand=False, po_demand=None),
        "a":   dict(pos={"G", "Y"}, neg=set(),    univ=G_univ, pp_demand=True,  po_demand=None),
        "rho_uw": PO,
        "expect": "REJECT",
    }


# --------------------------------------------------------------------------- #
#  STEP 1 -- DETECT: forced ancestor trace + threshold (the round-9 test).
# --------------------------------------------------------------------------- #
def prune_by_universals(cands, a_profile, w_profile):
    """Remove every label r such that putting (a, w) = r would fire a universal
    forall r.D at a with D in neg(w).  (a sees w as an r-successor.)"""
    out = set()
    for r in cands:
        violated = any(R == r and D in w_profile["neg"] for (R, D) in a_profile["univ"])
        if not violated:
            out.add(r)
    return out


def forced_trace(sc, n_levels=4):
    """Propagate r_m = L(a_m, w) up the tower.  a_m PPI u (u PP a_m) so the base
    step is comp(PPI, rho_uw); the inductive step is comp(PPI, r_{m-1}) because
    a_m PPI a_{m-1}.  Each level is pruned by the universals in the G profile.

    Returns (trace, k0, status):
       status 'ok'      : trace is DR* PO* PPI*, k0 = first PPI (or None if no tail)
       status 'reject'  : some level has NO composition-legal, universal-safe label
    """
    a, w = sc["a"], sc["w"]
    trace = []
    prev = sc["rho_uw"]               # L(u, w)
    for m in range(1, n_levels + 1):
        cand = compose(PPI, prev) & {DR, PO, PPI}   # EQ/PP impossible for a side witness
        survive = prune_by_universals(cand, a, w)
        if not survive:
            return trace, None, "reject"            # no legal placement -> UNSAT
        # the construction follows the forced label; if PPI is forced it wins
        # (PPI is absorbing), else keep the smallest in DR>PO>PPI that survives.
        order = {DR: 0, PO: 1, PPI: 2}
        r = sorted(survive, key=lambda x: order[x])[-1] if PPI in survive else \
            sorted(survive, key=lambda x: order[x])[0]
        trace.append(r)
        prev = r
    # monotone-trace lemma: shape must be DR* PO* PPI*
    order = {DR: 0, PO: 1, PPI: 2}
    assert all(order[trace[i]] <= order[trace[i + 1]] for i in range(len(trace) - 1)), \
        ("monotone-trace violated", trace)
    k0 = next((i + 1 for i, r in enumerate(trace) if r == PPI), None)
    return trace, k0, "ok"


# --------------------------------------------------------------------------- #
#  STEP 3 -- BUILD: emit the certificate object (nodes, E_up, residual, tags).
# --------------------------------------------------------------------------- #
def reach_pp(e_up):
    """strict transitive closure of selected cover edges (child, parent)."""
    up = set(e_up)
    changed = True
    while changed:
        changed = False
        for (a, b) in list(up):
            for (c, d) in list(up):
                if b == c and (a, d) not in up:
                    up.add((a, d)); changed = True
    return up


def build_certificate(sc, trace, k0, n_laps=3):
    """Regularise the tower to n_laps occurrences a1..aN (request-closed: the top
    profile recurs).  Splice w at a_{k0} when the trace has a PPI-tail."""
    tower = [f"a{i}" for i in range(1, n_laps + 1)]
    nodes = ["u", "w"] + tower
    profile = {"u": sc["u"], "w": sc["w"]}
    for t in tower:
        profile[t] = sc["a"]

    e_up = set()
    e_up.add(("u", "a1"))                              # u PP a1  (u's exists PP.G)
    for i in range(n_laps - 1):                        # tower ascending PP-chain
        e_up.add((tower[i], tower[i + 1]))
    spliced = False
    if k0 is not None:                                 # PPI-tail -> forced verticalization
        e_up.add(("w", f"a{k0}"))                      # SPLICE: w PP a_{k0}
        spliced = True

    residual = {}
    if not spliced:                                    # w stays a side witness
        lab = trace[-1] if trace else sc["rho_uw"]
        for t in tower:
            residual[("w", t)] = lab; residual[(t, "w")] = INV[lab]
    # the source side relation u--w is always the inherited residual pair
    residual[("u", "w")] = sc["rho_uw"]; residual[("w", "u")] = INV[sc["rho_uw"]]

    return dict(nodes=nodes, tower=tower, profile=profile, e_up=e_up,
                residual=residual, eq_ports=set(), spliced=spliced,
                reach=reach_pp(e_up))


def pair_label(cert, x, y):
    """l_Q(alpha(x,y)) with the incidence tag, from the emitted certificate."""
    if x == y:
        return EQ, "self"
    if (x, y) in cert["eq_ports"]:
        return EQ, "eq"
    if (x, y) in cert["reach"]:        # x proper part of y
        return PP, "up"
    if (y, x) in cert["reach"]:        # y proper part of x
        return PPI, "down"
    if (x, y) in cert["residual"]:
        R = cert["residual"][(x, y)]
        return R, f"front_{R}"
    return None, "MISSING"             # no admissible pair shape -> invalid


# --------------------------------------------------------------------------- #
#  STEP 4 -- VALIDATE: the round-9 validity clauses on the emitted object.
# --------------------------------------------------------------------------- #
def validate(cert):
    nodes, prof = cert["nodes"], cert["profile"]
    errs = []
    lab = {}
    for x, y in product(nodes, repeat=2):
        R, tag = pair_label(cert, x, y)
        if R is None:
            errs.append(("MISSING pair shape", x, y)); R = None
        lab[(x, y)] = (R, tag)

    # F1: EQ only on self/eq tags (no EQ across distinct laps -> blocking-not-eq, V9)
    for x, y in product(nodes, repeat=2):
        R, tag = lab[(x, y)]
        if x != y and R == EQ:
            errs.append(("V9 EQ across distinct occurrences", x, y, tag))
        if x == y and R != EQ:
            errs.append(("F1 reflexive", x, R))

    # F2: converse
    for x, y in product(nodes, repeat=2):
        Rxy = lab[(x, y)][0]; Ryx = lab[(y, x)][0]
        if Rxy is not None and Ryx is not None and Ryx != INV[Rxy]:
            errs.append(("F2 converse", x, y, Rxy, Ryx))

    # F3 / V6: triple composition on every ordered triple
    for x, y, z in product(nodes, repeat=3):
        Rxy, Ryz, Rxz = lab[(x, y)][0], lab[(y, z)][0], lab[(x, z)][0]
        if None in (Rxy, Ryz, Rxz):
            continue
        if Rxz not in compose(Rxy, Ryz):
            errs.append(("V6 composition", x, y, z, Rxy, Ryz, Rxz))

    # universal safety (V2/V7/V12): forall R.D at a => every R-neighbour has D, none in neg
    for a in nodes:
        for (R, D) in prof[a]["univ"]:
            for y in nodes:
                if y == a:
                    continue
                if lab[(a, y)][0] == R:
                    if D in prof[y]["neg"]:
                        errs.append(("universal-safety clash", a, "forall", R, D, "at", y))

    # global residual-frontier lemma: every front_* pair is DR or PO
    for x, y in product(nodes, repeat=2):
        R, tag = lab[(x, y)]
        if tag.startswith("front_") and R not in (DR, PO):
            errs.append(("residual-frontier not DR/PO", x, y, R))

    # existential request discharge
    for a in nodes:
        if prof[a]["pp_demand"]:
            up_ok = any(lab[(a, y)][0] == PP for y in nodes if y != a)
            # cycle discharge: top lap's profile recurs (request-closed)
            cyc = (a in cert["tower"])
            if not (up_ok or cyc):
                errs.append(("exists PP.* undischarged", a))
        if prof[a]["po_demand"] is not None:
            D = prof[a]["po_demand"][0]
            # the witness must be a PO-neighbour in ~X (D encodes the witness flag set)
            need_neg = {"notX": {"X"}, "notXY": {"X", "Y"}}[D]
            po_ok = any(lab[(a, y)][0] == PO and need_neg <= prof[y]["neg"]
                        for y in nodes if y != a)
            if not po_ok:
                errs.append(("exists PO.* undischarged", a, D))

    return errs


# --------------------------------------------------------------------------- #
#  Emission pipeline + the "all routings fail" witness for the UNSAT sibling.
# --------------------------------------------------------------------------- #
def emit(sc):
    print("-" * 72)
    print(sc["name"])
    print("-" * 72)
    trace, k0, status = forced_trace(sc)
    print(f"  [DETECT] ancestor trace L(a_m,w) = {trace if trace else '(none -- killed at a_1)'}")
    if status == "reject":
        print("  [DETECT] no composition-legal, universal-safe label at the first")
        print("           tower level: the side witness cannot be placed at all.")
        explain_all_routings_fail(sc)
        print("  >>> EMISSION REJECTS: no valid certificate exists.  (UNSAT)\n")
        return "REJECT"
    print(f"  [DETECT] trace shape DR*PO*PPI* with threshold k_0 = {k0} "
          f"({'PPI-tail -> splice' if k0 else 'no tail -> ordinary side witness'})")
    if k0 is not None:
        # splice-faithfulness guard: only splice because PPI is the forced label
        assert trace[k0 - 1] == PPI
        print(f"  [SPLICE] forced label at a_{k0} is PPI -> add E_up edge  w -> a_{k0}")
    cert = build_certificate(sc, trace, k0)
    print(f"  [BUILD]  nodes={cert['nodes']}  spliced={cert['spliced']}")
    print(f"           Reach_PP carries w up the tail: "
          f"{[t for t in cert['tower'] if ('w', t) in cert['reach']]}")
    # show the emitted labels of the deep pairs and the source pair
    shapes = {t: pair_label(cert, t, 'w') for t in cert['tower']}
    print("           emitted (a_m, w) pair shapes: "
          + ", ".join(f"{t}:{lab}/{tag}" for t, (lab, tag) in shapes.items()))
    print(f"           source pair (u,w): {pair_label(cert,'u','w')}")
    errs = validate(cert)
    if errs:
        print(f"  [VALIDATE] FAILED with {len(errs)} clause violation(s):")
        for e in errs[:6]:
            print("            ", e)
        print("  >>> EMISSION INVALID.\n")
        return "INVALID"
    print("  [VALIDATE] all round-9 clauses pass (converse, V6 composition,")
    print("             universal safety, V9 equality, request discharge,")
    print("             residual-frontier ⊆ {DR,PO}).")
    print("  >>> EMISSION VALID: round-9 emits a valid certificate.  (SAT)\n")
    return "VALID"


def explain_all_routings_fail(sc):
    """For the UNSAT sibling, make the rejection transparent: BOTH routings fail."""
    base = compose(PPI, sc["rho_uw"])
    print(f"           every routing of w fails (comp(PPI,{sc['rho_uw']})={sorted(base)}):")
    print("             - splice (w PP a_m, 'down'=PPI): forall PPI.Y at a_m fires on")
    print("               w, but w in ~Y.  CLASH.")
    print("             - no-splice (w stays side): the forced label is PPI, which is")
    print("               not DR/PO, so it cannot be a residual-frontier pair (global")
    print("               residual-frontier lemma).  And PO would fire forall PO.X on")
    print("               w with w in ~X.  CLASH.")
    print("             - DR is not composition-legal (DR not in comp(PPI,PO)).")


# --------------------------------------------------------------------------- #
def main():
    print("=" * 72)
    print("WP10: round-9 forced-verticalization certificate-EMISSION test")
    print("=" * 72)
    print()
    r_sat = emit(scenario_C0prime())
    r_uns = emit(scenario_UNSAT_sibling())

    ok = (r_sat == "VALID" and r_uns == "REJECT")
    print("=" * 72)
    print(f"  C0' (SAT)            -> {r_sat:7}  (expected VALID)")
    print(f"  UNSAT sibling        -> {r_uns:7}  (expected REJECT)")
    print("=" * 72)
    if ok:
        print("VERDICT: PASS.  Round-9 forced verticalization, run end-to-end as an")
        print("         emission pipeline, derives the splice from the forced trace,")
        print("         builds a valid tagged certificate for C0', and refuses the")
        print("         UNSAT sibling -- the one part of the new machinery not")
        print("         exercised by the existing WP / opus4.8 scripts.")
    else:
        print("VERDICT: FAIL.  See clause violations above.")
    return 0 if ok else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
