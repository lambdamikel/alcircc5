"""
WP12 -- dual (descendant-tower) forced-verticalization emission test.

This is the round-10 MIRROR of WP10.  The round-9 cold review (referee report,
29 May 2026) found that round-9's forced verticalization handled only the
ANCESTOR case -- a DR/PO side witness forced into an infinite ancestor PP-tower
ABOVE u (an eventual PPI-tail).  The DUAL case it missed (referee Critical 1):
a PO side witness forced to be a proper SUPERPART of an infinite descendant
PP-tower BELOW u (an eventual PP-tail).  Round-10 adds a dual splice rule.

This script machine-checks that dual repair end-to-end on the referee's own
witness:

    C  =  exists PO.A
        & exists PPI.T
        & forall PPI.( exists PPI.T & forall DR.~A & forall PO.~A )

Geometry of a model:  root u; a PO-witness w with w |= A; an infinite descendant
tower  ... PP d2 PP d1 PP d0 PP u  with each d_i carrying the profile.  RCC5
composition forces L(d_i,w)=PP for every i:

    d_i PP u, u PO w  =>  L(d_i,w) in comp(PP,PO) = {DR,PO,PP};
    forall DR.~A & forall PO.~A at d_i with w|=A  kill DR and PO  =>  PP;
    d_{i+1} PP d_i, comp(PP,PP)={PP}  =>  PP absorbing.

So w is a proper SUPERPART of the whole descendant tower (the dual of D-1, where
w was a proper PART of the whole ancestor tower).

Pipeline (mirrors WP10):
  DETECT  -- descendant trace s_i=L(d_i,w) by comp(PP,.) + universal pruning;
             monotone DR<PO<PP, PP absorbing; threshold k0 = first PP.
  SPLICE  -- splice w as the descendant-tower superpart: add cover edge
             d_{k0} -> w (d_{k0} PP w).  Deeper d_j PP w via Reach_PP.
  BUILD   -- incidence-tagged certificate; u--w stays the inherited PO residual.
  VALIDATE-- round-9 clauses (converse, V6 composition over all triples,
             universal safety, V9 equality, residual-frontier subset {DR,PO}).

Result: C emits a VALID certificate; the UNSAT sibling (add forall PP.B at the
descendants and w|=~B, so the splice fires forall PP.B on the superpart w) is
REJECTED.  Negative-controlled: withholding the splice files (d_i,w) as a
residual PP, which the residual-frontier clause rejects (the dual D-1 failure).

Self-contained (round-8 composition table, as in WP10).
"""

from itertools import product

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


def comp(R, S):
    return COMP[(R, S)]


# descendant-trace order: going DOWN, comp(PP,.) moves DR < PO < PP, PP absorbing
DRANK = {DR: 0, PO: 1, PP: 2}


# --------------------------------------------------------------------------- #
#  scenarios: a universal is (R, lit, pol) meaning  forall R.lit (pol='+') or
#  forall R.~lit (pol='-').  A witness has pos/neg literal sets.
# --------------------------------------------------------------------------- #
def scenario_C():
    """The referee's dual witness C.  w|=A; descendants carry forall DR.~A,
    forall PO.~A.  SAT -> the splice makes w the descendant-tower superpart."""
    return {
        "name": "C = EPO.A & EPPI.T & APPI.(EPPI.T & ADR.~A & APO.~A)   [SAT]",
        "duniv": [(DR, "A", "-"), (PO, "A", "-")],        # at every descendant
        "w": dict(rel=PO, pos={"A"}, neg=set()),
        "expect": "VALID",
    }


def scenario_unsat():
    """UNSAT sibling: also forall PP.B at the descendants, w|=A&~B.  Now the
    splice (d_i PP w) fires forall PP.B on the superpart w, forcing B(w); but
    w|=~B.  Every routing fails -> REJECT."""
    return {
        "name": "C' = EPO.(A&~B) & EPPI.T & APPI.(EPPI.T & ADR.~A & APO.~A & APP.B)   [UNSAT]",
        "duniv": [(DR, "A", "-"), (PO, "A", "-"), (PP, "B", "+")],
        "w": dict(rel=PO, pos={"A"}, neg={"B"}),
        "expect": "REJECT",
    }


def clashes(univ_R, lit, pol, w):
    """does forall univ_R.(lit/pol) fire on w and clash?"""
    if pol == "+":
        return lit in w["neg"]      # forall R.lit forces lit; w says ~lit
    return lit in w["pos"]          # forall R.~lit forces ~lit; w says lit


def forced_route(sc, n_levels):
    """Descendant trace s_i = L(d_i, w).  Base: comp(PP, rel) [d_0 PP u, u rel w].
    Step: comp(PP, s_{i-1}) [d_{i+1} PP d_i].  Prune label r at level i if some
    descendant universal forall r.(..) fires on w.  Returns
    ('splice',(k0,trace)) | ('side',trace) | ('unplaceable', level)."""
    w = sc["w"]
    trace = []
    prev = w["rel"]                                   # L(u, w)
    k0 = None
    for i in range(n_levels):
        cand = comp(PP, prev) & {DR, PO, PP}          # EQ/PPI impossible for a superpart witness
        survive = {r for r in cand
                   if not any(R == r and clashes(R, lit, pol, w)
                              for (R, lit, pol) in sc["duniv"])}
        if not survive:
            return "unplaceable", i
        r = sorted(survive, key=lambda x: DRANK[x])[0]   # most side-like that survives
        trace.append(r)
        if r == PP and k0 is None:
            k0 = i
        prev = r
    if k0 is not None:
        assert trace[k0] == PP                         # splice-faithfulness
        return "splice", (k0, trace)
    return "side", trace


# --------------------------------------------------------------------------- #
def reach_pp(e_up):
    up = set(e_up)
    changed = True
    while changed:
        changed = False
        for (a, b) in list(up):
            for (c, d) in list(up):
                if b == c and (a, d) not in up:
                    up.add((a, d)); changed = True
    return up


def pair_label(cert, x, y):
    if x == y:
        return EQ, "self"
    if (x, y) in cert["eq_ports"]:
        return EQ, "eq"
    if (x, y) in cert["reach"]:        # x proper part of y
        return PP, "up"
    if (y, x) in cert["reach"]:
        return PPI, "down"
    if (x, y) in cert["residual"]:
        R = cert["residual"][(x, y)]
        return R, f"front_{R}"
    return None, "MISSING"


def validate(cert):
    nodes = cert["nodes"]
    inv = dict(INV); inv[EQ] = EQ
    errs = []
    lab = {}
    for x in nodes:
        for y in nodes:
            R, tag = pair_label(cert, x, y)
            if R is None:
                errs.append(("MISSING pair shape", x, y))
            lab[(x, y)] = (R, tag)
    for x in nodes:
        for y in nodes:
            R, tag = lab[(x, y)]
            if x != y and R == EQ:
                errs.append(("V9 EQ across distinct occurrences", x, y, tag))
            if x == y and R != EQ:
                errs.append(("F1 reflexive", x, R))
    for x in nodes:
        for y in nodes:
            Rxy, Ryx = lab[(x, y)][0], lab[(y, x)][0]
            if Rxy is not None and Ryx is not None and Ryx != inv[Rxy]:
                errs.append(("F2 converse", x, y, Rxy, Ryx))
    for x in nodes:
        for y in nodes:
            for z in nodes:
                if len({x, y, z}) < 3:
                    continue
                Rxy, Ryz, Rxz = lab[(x, y)][0], lab[(y, z)][0], lab[(x, z)][0]
                if None in (Rxy, Ryz, Rxz):
                    continue
                if Rxz not in comp(Rxy, Ryz):
                    errs.append(("V6 composition", x, y, z, Rxy, Ryz, Rxz))
    # universal safety: forall R.(lit/pol) at each descendant
    for d in cert["tower"]:
        for (R, lit, pol) in cert["duniv"]:
            for y in cert["nodes"]:
                if y == d:
                    continue
                if lab[(d, y)][0] == R:
                    bad = (lit in cert["neg"][y]) if pol == "+" else (lit in cert["pos"][y])
                    if bad:
                        errs.append(("universal-safety clash", d, "forall", R,
                                     ("" if pol == "+" else "~") + lit, "at", y))
    for x in nodes:
        for y in nodes:
            R, tag = lab[(x, y)]
            if tag.startswith("front_") and R not in (DR, PO):
                errs.append(("residual-frontier not DR/PO", x, y, R))
    return errs


def build(sc, kind, data, n_levels):
    tower = [f"d{i}" for i in range(n_levels)]
    nodes = ["u", "w"] + tower
    pos = {x: set() for x in nodes}
    neg = {x: set() for x in nodes}
    pos["w"] = set(sc["w"]["pos"]); neg["w"] = set(sc["w"]["neg"])
    e_up = {("d0", "u")}                              # d_0 PP u
    for i in range(n_levels - 1):
        e_up.add((tower[i + 1], tower[i]))            # d_{i+1} PP d_i
    residual = {("u", "w"): sc["w"]["rel"], ("w", "u"): INV[sc["w"]["rel"]]}
    if kind == "splice":
        k0, trace = data
        e_up.add((tower[k0], "w"))                    # SPLICE: d_{k0} PP w
        for i in range(k0):                           # above threshold: residual DR/PO
            residual[(tower[i], "w")] = trace[i]; residual[("w", tower[i])] = INV[trace[i]]
    else:                                             # side: all residual
        trace = data
        for i in range(n_levels):
            residual[(tower[i], "w")] = trace[i]; residual[("w", tower[i])] = INV[trace[i]]
    return dict(nodes=nodes, tower=tower, e_up=e_up, residual=residual,
                eq_ports=set(), pos=pos, neg=neg, duniv=sc["duniv"],
                reach=reach_pp(e_up))


def emit(sc, n_levels=4):
    print("-" * 72)
    print(sc["name"])
    print("-" * 72)
    kind, data = forced_route(sc, n_levels)
    if kind == "unplaceable":
        print(f"  [DETECT] descendant trace killed at level {data}: every routing of w")
        print("           clashes (DR/PO killed by forall DR.~A/forall PO.~A; PP killed by")
        print("           forall PP.B firing on the spliced superpart).")
        print("  >>> EMISSION REJECTS: no valid certificate.  (UNSAT)\n")
        return "REJECT"
    if kind == "splice":
        k0, trace = data
        print(f"  [DETECT] descendant trace L(d_i,w) = {trace}  (shape DR*PO*PP*, PP absorbing)")
        print(f"  [SPLICE] PP-tail at threshold k0={k0} -> add cover edge  d{k0} -> w "
              f"(d{k0} PP w: w is the descendant-tower superpart)")
    else:
        print(f"  [DETECT] descendant trace L(d_i,w) = {data}  (no PP-tail -> ordinary side witness)")
    cert = build(sc, kind, data, n_levels)
    shapes = {t: pair_label(cert, t, "w") for t in cert["tower"]}
    print(f"  [BUILD]  nodes={cert['nodes']}")
    print("           emitted (d_i, w) pair shapes: "
          + ", ".join(f"{t}:{lab}/{tag}" for t, (lab, tag) in shapes.items()))
    print(f"           source pair (u,w): {pair_label(cert,'u','w')}")
    errs = validate(cert)
    if errs:
        print(f"  [VALIDATE] FAILED ({len(errs)} clause violations):")
        for e in errs[:6]:
            print("            ", e)
        print("  >>> EMISSION INVALID.\n")
        return "INVALID"
    print("  [VALIDATE] all round-9 clauses pass (converse, V6 composition, universal")
    print("             safety, V9 equality, residual-frontier subset {DR,PO}).")
    print("  >>> EMISSION VALID.  (SAT)\n")
    return "VALID"


def negative_control():
    """Withhold the splice for C: file (d_i,w) as a residual PP -> must trip the
    residual-frontier clause (the dual D-1 failure)."""
    sc = scenario_C()
    nodes = ["u", "w", "d0", "d1", "d2", "d3"]
    e_up = {("d0", "u"), ("d1", "d0"), ("d2", "d1"), ("d3", "d2")}   # NO splice
    residual = {("u", "w"): PO, ("w", "u"): PO}
    for t in ["d0", "d1", "d2", "d3"]:
        residual[(t, "w")] = PP; residual[("w", t)] = PPI            # PP as residual (illegal)
    cert = dict(nodes=nodes, tower=["d0", "d1", "d2", "d3"], e_up=e_up, residual=residual,
                eq_ports=set(), pos={x: set() for x in nodes}, neg={x: set() for x in nodes},
                duniv=sc["duniv"], reach=reach_pp(e_up))
    cert["pos"]["w"] = {"A"}
    errs = validate(cert)
    has_rf = any(e[0] == "residual-frontier not DR/PO" for e in errs)
    print(f"  negative control (withhold splice for C): validator errors={len(errs)}, "
          f"catches dual-D-1 residual-frontier = {has_rf}\n")
    return has_rf and len(errs) > 0


def main():
    print("=" * 72)
    print("WP12: round-10 DUAL (descendant-tower) forced-verticalization test")
    print("=" * 72)
    print()
    r1 = emit(scenario_C())
    r2 = emit(scenario_unsat())
    nc = negative_control()
    print("=" * 72)
    print(f"  C  (SAT)        -> {r1:7}  (expected VALID)")
    print(f"  UNSAT sibling   -> {r2:7}  (expected REJECT)")
    print(f"  negative control teeth: {nc}")
    print("=" * 72)
    ok = (r1 == "VALID" and r2 == "REJECT" and nc)
    if ok:
        print("VERDICT: PASS.  The round-10 DUAL splice -- splicing a PO witness as the")
        print("         superpart of an infinite descendant PP-tower -- emits a valid")
        print("         certificate for the referee's Critical-1 witness C, and rejects")
        print("         the UNSAT sibling.  The descendant-side defect round-9 missed is")
        print("         handled symmetrically to the ancestor case (WP10).")
    else:
        print("VERDICT: FAIL / INVESTIGATE.")
    print("=" * 72)
    return 0 if ok else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
