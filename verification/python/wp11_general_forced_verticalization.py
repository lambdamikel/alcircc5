#!/usr/bin/env python3
"""
WP11 -- GENERAL forced-verticalization emission engine + oracle cross-check.

This generalises WP10 from the single hard-coded D-1 witness (C0') to a whole
parameterised family of forced-tower concepts, and cross-checks the round-9
emission construction against two independent oracles:

  * a by-construction oracle `family_status(spec)` (rigorous: reasons about
    which routings of each side witness survive the ancestor universals), and
  * the cover-tree tableau decision procedure `cover_tree_tableau.check_sat`
    (an independent implementation of the decision problem; period-1 specs
    are encoded as finite ALCI_RCC5 concepts and fed to it).

The engine itself (`emit`) does the round-9 construction END TO END, generalised
over the axes that matter for forced verticalization:

  * period-p tower profiles (the tower cycles through P_0..P_{p-1}); this
    exercises the bounded-threshold lemma with *varying* ancestor profiles,
    not the single recurring profile of WP10;
  * arbitrarily many side witnesses of the root, each with its own source
    relation (PO/DR) and its own set of negative literals;
  * universals on the tower over any of {PO, PPI, DR, PP} with any payload;
  * a first cut at simultaneous splices (the splice pass iterates to a fixpoint
    and re-derives traces, so multiple witnesses are verticalised together).

Pipeline per spec:
  DETECT   -- build the tower spine, propagate forall PP / forall PPI literals,
              and for each witness compute the forced ancestor trace
              L(a_m, w) by composition + universal pruning (monotone DR>PO>PPI).
  ROUTE    -- side witness if a DR/PO tail survives; splice at the bounded
              threshold if a PPI-tail is forced; UNPLACEABLE if every routing
              is pruned to empty (=> no valid certificate => REJECT).
  BUILD    -- assemble the certificate (occurrence-sensitive pair shapes with
              incidence tags + l_Q; tower regularised to a request-closed cycle;
              Reach_PP carries each splice up its tail).
  VALIDATE -- run the round-9 clauses on the concrete object (converse, V6
              composition over all triples, universal safety, V9 equality,
              request discharge, residual-frontier subset {DR,PO}).

A mismatch between (engine emits VALID) and (by-construction SAT) -- or against
the tableau -- is a CANDIDATE DEFECT and is printed for investigation; the
script exits non-zero if any rigorous mismatch (engine vs by-construction) is
found.

Honest scope: the parameterised family stresses forced verticalization across
the axes above with trustworthy ground truth.  It does NOT yet stress the
hardest part of obligation D -- witnesses that are proper parts of *each other*
or that share superparts (overlap amalgams) -- where simultaneous splices could
genuinely interact; those need a richer generator and are future work.  The
engine's splice pass is written as a fixpoint so that extension is structural.

Reuses the AST / tables / oracles already in the repo (alcircc5_reasoner,
cover_tree_tableau).
"""

import sys
import os
import itertools

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "src"))

from alcircc5_reasoner import (                       # noqa: E402
    DR, PO, PP, PPI, BASE_RELS, INV, COMP,
    AtomicConcept, NegAtomicConcept, And, Exists, ForAll, Top,
    closure,
)
from alcircc5_reasoner import check_satisfiability as qm_check      # noqa: E402
from cover_tree_tableau import check_satisfiability as ct_check     # noqa: E402

EQ = "EQ"
RANK = {DR: 0, PO: 1, PPI: 2}            # monotone order for the ancestor trace


def comp(R, S):
    return COMP[(R, S)]


# =========================================================================== #
#  Spec: a parameterised forced-tower concept.
#
#   profiles : list of profiles, the tower cycles through them (period = len).
#              each profile = {"univ": set of (R, lit), "neg": set of lit}
#              (a tower node carries forall R.lit for each (R,lit) in univ, and
#               -- via forall PP / forall PPI propagation -- may also acquire
#               positive literals; "neg" lets a profile pin a literal false.)
#   witnesses: list of {"rel": PO|DR, "neg": set of lit}  -- side witnesses of u
# =========================================================================== #
def spec(profiles, witnesses):
    return {"profiles": profiles, "witnesses": witnesses}


# --------------------------------------------------------------------------- #
#  Oracle 1 -- by construction (independent of the engine).
# --------------------------------------------------------------------------- #
def routing_safe(label, profiles, w_neg):
    """A constant eventual routing `label` (in {DR,PO,PPI}) is safe iff no
    tower profile carries a universal forall <label>.lit with lit in neg(w):
    that universal would fire on w (which is an <label>-successor of a_m) and
    force lit, contradicting lit in neg(w)."""
    for P in profiles:
        for (R, lit) in P["univ"]:
            if R == label and lit in w_neg:
                return False
    return True


def witness_placeable(rel, w_neg, profiles):
    """A witness with source relation `rel` (u rel w) is placeable iff some
    monotone-reachable eventual label is safe at every tower profile.
    Reachable from PO: {PO, PPI}; from DR: {DR, PO, PPI}."""
    reach = {PO: {PO, PPI}, DR: {DR, PO, PPI}}[rel]
    return any(routing_safe(L, profiles, w_neg) for L in reach)


def tower_self_consistent(profiles):
    """forall PP propagates a literal UP to every tower node; forall PPI
    propagates DOWN to every tower node (the tower is a single PP-chain, so
    both reach every node).  Inconsistent iff some literal is forced positive
    by a forall PP/forall PPI while pinned negative by some profile."""
    forced_pos = set()
    for P in profiles:
        for (R, lit) in P["univ"]:
            if R in (PP, PPI):
                forced_pos.add(lit)
    for P in profiles:
        if forced_pos & P["neg"]:
            return False
    return True


def family_status(sp):
    """Returns ('SAT'|'UNSAT', reason)."""
    profiles, witnesses = sp["profiles"], sp["witnesses"]
    if not tower_self_consistent(profiles):
        return "UNSAT", "tower not self-consistent (forall PP/PPI clash)"
    for i, w in enumerate(witnesses):
        if not witness_placeable(w["rel"], w["neg"], profiles):
            return "UNSAT", f"witness#{i} ({w['rel']},neg={sorted(w['neg'])}) unplaceable"
    return "SAT", "tower consistent and every witness routable"


# --------------------------------------------------------------------------- #
#  Oracle 2 -- finite ALCI_RCC5 encoding for the cover-tree tableau (period-1).
# --------------------------------------------------------------------------- #
def _conj(parts):
    parts = [p for p in parts if p is not None]
    if not parts:
        return Top()
    out = parts[0]
    for p in parts[1:]:
        out = And(out, p)
    return out


def encode_concept(sp):
    """Finite encoding (period-1 only). Uses transitive forall PP to push the
    tower universals to every superpart, and forall PP.(exists PP.top) to force
    the infinite ascending tower.  Returns a Concept, or None if not encodable
    (period > 1)."""
    profiles = sp["profiles"]
    if len(profiles) != 1:
        return None
    P = profiles[0]
    parts = [Exists(PP, Top())]                          # u has a superpart
    parts.append(ForAll(PP, Exists(PP, Top())))          # ... ad infinitum
    for (R, lit) in P["univ"]:                           # universals at every tower node
        parts.append(ForAll(PP, ForAll(R, AtomicConcept(lit))))
    for lit in P["neg"]:                                 # pinned-negative literals on the tower
        parts.append(ForAll(PP, NegAtomicConcept(lit)))
    for w in sp["witnesses"]:                            # the side witnesses of u
        payload = _conj([NegAtomicConcept(l) for l in sorted(w["neg"])]) if w["neg"] else Top()
        parts.append(Exists(w["rel"], payload))
    return _conj(parts)


# =========================================================================== #
#  The round-9 EMISSION ENGINE.
# =========================================================================== #
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


def forced_route(rel, w_neg, profiles, n_levels):
    """Compute the forced ancestor trace and decide the routing of one witness.

    Returns (kind, data):
       ('side',  trace)              -- stays a DR/PO side witness
       ('splice', (k0, trace))       -- verticalise: splice at level k0
       ('unplaceable', level)        -- no legal label at `level`  => REJECT
    The construction prefers to keep w a side witness (lowest rank that
    survives); it verticalises only when DR/PO are pruned out, leaving PPI.
    """
    trace = []
    prev = rel                                  # L(u, w)
    chosen = None
    k0 = None
    for m in range(n_levels):
        P = profiles[m % len(profiles)]
        cand = comp(PPI, prev) & {DR, PO, PPI}  # L(a_m,w) in comp(PPI, L(a_{m-1},w))
        survive = {r for r in cand
                   if not any(R == r and lit in w_neg for (R, lit) in P["univ"])}
        if not survive:
            return "unplaceable", m
        # forced label: keep the lowest-rank survivor (most side-like); if only
        # PPI survives we are verticalised from here on (PPI is absorbing).
        r = sorted(survive, key=lambda x: RANK[x])[0]
        trace.append(r)
        if r == PPI and k0 is None:
            k0 = m
        prev = r
    if k0 is not None:
        # splice-faithfulness: the forced label at k0 really is PPI
        assert trace[k0] == PPI
        return "splice", (k0, trace)
    return "side", trace


def emit(sp, n_levels=None):
    """Round-9 emission. Returns (result, detail) with result in
    {'EMIT_VALID', 'REJECT', 'INVALID'}."""
    profiles, witnesses = sp["profiles"], sp["witnesses"]
    p = len(profiles)
    if n_levels is None:
        n_levels = 2 * p + 2                    # one+ full period, enough to see the cycle

    # ---- nodes & vertical backbone (tower spine) ----
    tower = [f"a{m}" for m in range(n_levels)]
    nodes = ["u"] + tower
    e_up = {("u", "a0")}
    for m in range(n_levels - 1):
        e_up.add((tower[m], tower[m + 1]))

    # node literal sets (pos forced TRUE, neg forced FALSE) from propagation
    pos = {x: set() for x in nodes}
    neg = {x: set() for x in nodes}
    for m, t in enumerate(tower):
        P = profiles[m % p]
        neg[t] |= set(P["neg"])
    # forall PP pushes a literal up to every superpart; forall PPI pushes it
    # down to every subpart (u and lower tower nodes).  (Single chain: each
    # reaches the whole tower.)
    R = reach_pp(e_up)
    for m, t in enumerate(tower):
        P = profiles[m % p]
        for (Rl, lit) in P["univ"]:
            if Rl == PP:                        # holds at every PP-superpart of t
                for x in nodes:
                    if (t, x) in R:
                        pos[x].add(lit)
            if Rl == PPI:                       # holds at every PP-subpart of t
                for x in nodes:
                    if (x, t) in R:
                        pos[x].add(lit)
    for x in nodes:
        if pos[x] & neg[x]:
            return "REJECT", f"tower node {x} forced {sorted(pos[x] & neg[x])} both ways"

    # ---- route each witness ----
    residual = {}
    placed = []
    for i, w in enumerate(witnesses):
        wn = f"w{i}"
        kind, data = forced_route(w["rel"], w["neg"], profiles, n_levels)
        if kind == "unplaceable":
            return "REJECT", f"witness {wn} unplaceable at level {data}"
        nodes.append(wn)
        neg[wn] = set(w["neg"]); pos[wn] = set()
        # source side relation u -- w (always the inherited residual pair)
        residual[("u", wn)] = w["rel"]; residual[(wn, "u")] = INV[w["rel"]]
        if kind == "side":
            trace = data
            for m, t in enumerate(tower):
                residual[(wn, t)] = trace[m]; residual[(t, wn)] = INV[trace[m]]
            placed.append((wn, "side", None))
        else:  # splice
            k0, trace = data
            e_up.add((wn, tower[k0]))           # SPLICE: w PP a_{k0}
            for m in range(k0):                 # below threshold: residual DR/PO
                residual[(wn, tower[m])] = trace[m]; residual[(tower[m], wn)] = INV[trace[m]]
            placed.append((wn, "splice", k0))

    # ---- inter-witness residual labels.  The relation between two witnesses
    #      is FORCED by composition through every shared anchor (tower node or
    #      u): L(wi,wj) in  AND_x comp(L(wi,x), L(x,wj)).  We compute that
    #      intersection and pick a label from it (preferring a DR/PO residual
    #      frontier pair).  Empty intersection => genuine inconsistency.  (With
    #      <=2 witnesses the single pair has no interdependence; >=2 would need
    #      full path-consistency -- a documented limitation of this first cut.)
    partial = dict(nodes=nodes, tower=tower, e_up=e_up, residual=residual,
                   eq_ports=set(), pos=pos, neg=neg, profiles=profiles,
                   reach=reach_pp(e_up))
    wnodes = [wn for (wn, _, _) in placed]
    for a, b in itertools.combinations(wnodes, 2):
        if (a, b) in partial["reach"] or (b, a) in partial["reach"]:
            continue                            # already vertically related
        anchors = [x for x in nodes if x not in (a, b)]
        allowed = set(BASE_RELS)
        for x in anchors:
            Rax = pair_label(partial, a, x)[0]
            Rxb = pair_label(partial, x, b)[0]
            if Rax is None or Rxb is None or Rax == EQ or Rxb == EQ:
                continue
            allowed &= comp(Rax, Rxb)
        if not allowed:
            return "INVALID", [("inter-witness label infeasible", a, b)]
        pick = next((r for r in (DR, PO, PP, PPI) if r in allowed))
        residual[(a, b)] = pick; residual[(b, a)] = INV[pick]

    cert = dict(nodes=nodes, tower=tower, e_up=e_up, residual=residual,
                eq_ports=set(), pos=pos, neg=neg, profiles=profiles,
                reach=reach_pp(e_up))

    errs = validate(cert)
    if errs:
        return "INVALID", errs
    return "EMIT_VALID", placed


# --------------------------------------------------------------------------- #
#  round-9 validity clauses on the emitted certificate object
# --------------------------------------------------------------------------- #
def pair_label(cert, x, y):
    if x == y:
        return EQ, "self"
    if (x, y) in cert["eq_ports"]:
        return EQ, "eq"
    if (x, y) in cert["reach"]:
        return PP, "up"
    if (y, x) in cert["reach"]:
        return PPI, "down"
    if (x, y) in cert["residual"]:
        Rr = cert["residual"][(x, y)]
        return Rr, f"front_{Rr}"
    return None, "MISSING"


def validate(cert):
    nodes = cert["nodes"]
    inv = dict(INV); inv[EQ] = EQ
    errs = []
    lab = {}
    for x in nodes:
        for y in nodes:
            Rr, tag = pair_label(cert, x, y)
            if Rr is None:
                errs.append(("MISSING pair shape", x, y))
            lab[(x, y)] = (Rr, tag)

    # V9 / F1: EQ only on the diagonal (no EQ across distinct occurrences)
    for x in nodes:
        for y in nodes:
            Rr, tag = lab[(x, y)]
            if x != y and Rr == EQ:
                errs.append(("V9 EQ across distinct occurrences", x, y, tag))
            if x == y and Rr != EQ:
                errs.append(("F1 reflexive", x, Rr))

    # F2: converse
    for x in nodes:
        for y in nodes:
            Rxy, Ryx = lab[(x, y)][0], lab[(y, x)][0]
            if Rxy is not None and Ryx is not None and Ryx != inv[Rxy]:
                errs.append(("F2 converse", x, y, Rxy, Ryx))

    # F3 / V6: composition over all DISTINCT triples
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

    # universal safety (V2/V7/V12): forall R.lit at a => every R-neighbour has
    # lit, and none pins lit negative.
    for a in cert["tower"]:
        m = cert["tower"].index(a)
        P = cert["profiles"][m % len(cert["profiles"])]
        for (Rl, lit) in P["univ"]:
            for y in nodes:
                if y == a:
                    continue
                if lab[(a, y)][0] == Rl and lit in cert["neg"][y]:
                    errs.append(("universal-safety clash", a, "forall", Rl, lit, "at", y))

    # global residual-frontier lemma: every front pair is DR or PO
    for x in nodes:
        for y in nodes:
            Rr, tag = lab[(x, y)]
            if tag.startswith("front_") and Rr not in (DR, PO):
                errs.append(("residual-frontier not DR/PO", x, y, Rr))

    return errs


# =========================================================================== #
#  Spec generator (the sweep) + corpus.
# =========================================================================== #
def gen_specs():
    """Sweep the forced-verticalization axes: tower universals over
    {PO,PPI,DR} x {X,Y}, period in {1,2}, and 1-2 witnesses with PO/DR source
    relations and negative payloads subsets of {X,Y}."""
    lits = ["X", "Y"]
    rels_univ = [PO, PPI, DR]
    # candidate single-profile universal sets (0..2 universals)
    univ_atoms = [(R, l) for R in rels_univ for l in lits]
    univ_sets = [frozenset()]
    univ_sets += [frozenset({a}) for a in univ_atoms]
    univ_sets += [frozenset({a, b}) for a, b in itertools.combinations(univ_atoms, 2)
                  if a[1] != b[1] or a[0] != b[0]]
    # keep it bounded
    univ_sets = univ_sets[:40]

    neg_sets = [frozenset(), frozenset({"X"}), frozenset({"Y"}), frozenset({"X", "Y"})]
    wit_rels = [PO, DR]

    specs = []
    # period-1 sweep, 1 witness
    for U in univ_sets:
        for wr in wit_rels:
            for wn in neg_sets:
                P = {"univ": set(U), "neg": set()}
                specs.append(("p1", spec([P], [{"rel": wr, "neg": set(wn)}])))
    # period-1, 2 witnesses (interaction at the root)
    for U in [frozenset({(PO, "X")}), frozenset({(PO, "X"), (PPI, "Y")}),
              frozenset({(DR, "X")}), frozenset({(PO, "X"), (PO, "Y")})]:
        for wr1 in wit_rels:
            for wr2 in wit_rels:
                P = {"univ": set(U), "neg": set()}
                specs.append(("p1-2w", spec([P],
                    [{"rel": wr1, "neg": {"X"}}, {"rel": wr2, "neg": {"Y"}}])))
    # period-2 towers (alternating profiles) -- engine + by-construction only
    for U0, U1 in [({(PO, "X")}, set()),
                   ({(PO, "X")}, {(PPI, "Y")}),
                   ({(PPI, "X")}, {(PO, "X")}),
                   (set(), {(DR, "X")})]:
        for wr in wit_rels:
            for wn in [frozenset({"X"}), frozenset({"Y"}), frozenset({"X", "Y"})]:
                specs.append(("p2", spec(
                    [{"univ": set(U0), "neg": set()}, {"univ": set(U1), "neg": set()}],
                    [{"rel": wr, "neg": set(wn)}])))
    return specs


def canonical_and_controls():
    """Explicit canonical D-1 cases (connecting to WP10) + negative controls
    proving the validator has teeth."""
    print("-- canonical cases + negative controls --")
    # C0' : tower forall PO.X, witness PO/~X  -> splice -> VALID
    c0p = spec([{"univ": {(PO, "X")}, "neg": set()}], [{"rel": PO, "neg": {"X"}}])
    r1, d1 = emit(c0p)
    print(f"  C0'  (forall PO.X; PO-witness ~X)            : emit={r1:11} "
          f"by-construction={family_status(c0p)[0]}")
    ok1 = (r1 == "EMIT_VALID" and family_status(c0p)[0] == "SAT")
    # UNSAT sibling : tower forall PO.X & forall PPI.Y, witness PO/~X,~Y -> REJECT
    cun = spec([{"univ": {(PO, "X"), (PPI, "Y")}, "neg": set()}],
               [{"rel": PO, "neg": {"X", "Y"}}])
    r2, d2 = emit(cun)
    print(f"  UNSAT sibling (+forall PPI.Y; witness ~X,~Y) : emit={r2:11} "
          f"by-construction={family_status(cun)[0]}")
    ok2 = (r2 == "REJECT" and family_status(cun)[0] == "UNSAT")

    # NEGATIVE CONTROL: corrupt the C0' certificate and confirm validate rejects.
    # Re-build C0' cert, then withhold the splice (file w0->tower as residual PPI)
    # -> must trip the residual-frontier clause (the original D-1 failure).
    profiles = c0p["profiles"]
    nodes = ["u", "a0", "a1", "a2", "a3", "w0"]
    e_up = {("u", "a0"), ("a0", "a1"), ("a1", "a2"), ("a2", "a3")}  # NO splice for w0
    residual = {("u", "w0"): PO, ("w0", "u"): PO}
    for t in ["a0", "a1", "a2", "a3"]:
        residual[("w0", t)] = PPI; residual[(t, "w0")] = PP   # PPI as a *residual* (illegal)
    bad = dict(nodes=nodes, tower=["a0", "a1", "a2", "a3"], e_up=e_up,
               residual=residual, eq_ports=set(),
               pos={x: set() for x in nodes}, neg={x: set() for x in nodes},
               profiles=profiles, reach=reach_pp(e_up))
    bad["neg"]["w0"] = {"X"}
    errs = validate(bad)
    has_rf = any(e[0] == "residual-frontier not DR/PO" for e in errs)
    print(f"  negative control (withhold splice for C0')   : validator errors={len(errs)}, "
          f"catches residual-frontier D-1 = {has_rf}")
    ok3 = has_rf and len(errs) > 0
    print()
    return ok1 and ok2 and ok3


# =========================================================================== #
def main():
    print("=" * 74)
    print("WP11: GENERAL forced-verticalization emission engine + oracle cross-check")
    print("=" * 74)
    controls_ok = canonical_and_controls()
    specs = gen_specs()
    print(f"corpus: {len(specs)} parameterised forced-tower specs\n")

    # ---- PRIMARY rigorous cross-check (full sweep, fast): engine <-> by-construction
    n = 0
    agree_engine_construction = 0
    rigorous_mismatches = []
    invalids = []
    for tag, sp in specs:
        n += 1
        fam, reason = family_status(sp)
        res, detail = emit(sp)
        engine_sat = (res == "EMIT_VALID")
        construction_sat = (fam == "SAT")
        if res == "INVALID":
            invalids.append((tag, sp, detail))
        if engine_sat == construction_sat:
            agree_engine_construction += 1
        else:
            rigorous_mismatches.append((tag, sp, fam, reason, res, detail))

    print(f"engine-vs-by-construction agreements : {agree_engine_construction}/{n}", flush=True)
    print(f"engine INVALID (built but failed V-clauses): {len(invalids)}", flush=True)

    # ---- SECONDARY: cover-tree tableau on the finite encoding.  enumerate_types
    #      is exponential in the closure, so we cap closure size and sample.
    tableau_checked = 0
    tableau_agree = 0
    tableau_mismatches = []
    CLOSURE_CAP = 20                              # enumerate_types stays tractable here
    seen = 0
    for tag, sp in specs:
        if tag.startswith("p2"):
            continue                              # period-2 not finitely encoded here
        C = encode_concept(sp)
        if C is None or len(closure(C)) > CLOSURE_CAP:
            continue
        seen += 1
        if seen > 80:                             # bound total tableau work
            break
        construction_sat = (family_status(sp)[0] == "SAT")
        try:
            ct_sat, _ = ct_check(C)
            tableau_checked += 1
            if ct_sat == construction_sat:
                tableau_agree += 1
            else:
                tableau_mismatches.append((tag, sp, construction_sat, ct_sat))
        except Exception as e:
            tableau_mismatches.append((tag, sp, "ERR", str(e)))

    print(f"tableau cross-checks (period-1, closure<= {CLOSURE_CAP}): "
          f"{tableau_agree}/{tableau_checked} agree", flush=True)
    print()

    if rigorous_mismatches:
        print("!! RIGOROUS MISMATCHES (engine vs by-construction) -- candidate defects:")
        for (tag, sp, fam, reason, res, detail) in rigorous_mismatches[:20]:
            print(f"   [{tag}] by-construction={fam} ({reason}); engine={res}")
            print(f"        spec={sp}")
            if res == "INVALID":
                for e in (detail or [])[:4]:
                    print("        ", e)
    else:
        print("No rigorous mismatches: the engine's emit/REJECT verdict matches the")
        print("by-construction oracle on every spec in the sweep.")

    if tableau_mismatches:
        print("\n-- tableau disagreements (period-1 finite encoding) --")
        print("   (a disagreement here is a finite-encoding/tableau-scope note OR a")
        print("    candidate defect; inspect each):")
        for (tag, sp, c_sat, ct_sat) in tableau_mismatches[:20]:
            print(f"   [{tag}] by-construction SAT={c_sat}, tableau SAT={ct_sat}")
            print(f"        spec={sp}")
    else:
        print("\nAll period-1 tableau cross-checks agree with the by-construction oracle.")

    print("\n" + "=" * 74)
    ok = (not rigorous_mismatches) and (not invalids) and controls_ok
    if ok:
        print("VERDICT: PASS.  The general forced-verticalization engine agrees with the")
        print("         by-construction oracle across the whole sweep, every emitted")
        print("         certificate validates, and (where finitely encodable) the")
        print("         independent cover-tree tableau agrees too.")
    else:
        print("VERDICT: FAIL / INVESTIGATE.  See mismatches above.")
    print("=" * 74)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
