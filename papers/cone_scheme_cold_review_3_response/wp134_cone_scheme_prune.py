#!/usr/bin/env python3
"""WP134 -- is the ConeScheme's `prune` STRONG ENOUGH?

ASSEMBLY_DESIGN §273 records the balance point the whole route now rests on:

  * `prune` must be WEAK enough to be MONOTONE, or `gfp_greatest` fails and
    completeness dies -- this is how the project's retracted type-elimination
    route died (its (Q3) was anti-monotone);
  * `prune` must be STRONG enough that survivors are REALIZABLE, or the
    fresh-occurrence unfolding of a surviving signature set is not a model and
    soundness dies.

Monotonicity is proved (`pruneSig_mono`, propext + Quot.sound).  Strength is
UNTESTED, and this probe tests it, needing none of gates G2/G3: transcribe the
control layer and check that the greatest fixed point REJECTS concepts that are
unsatisfiable, and ACCEPTS ones that are satisfiable.

PREDICTIONS, FIXED BEFORE THE RUN.

  U1  exists PP.(exists DR.A) and forall DR.not A          REJECT
      x PP y, y DR z forces x DR z by comp(PP,DR)={DR}; forall DR.not A then
      kills A at z.  Hand-traced expectation: the DR transition condition puts
      A_DR(T_x) = {not A} into every member of the target's cone, so the target
      type would need A and not A, which `supportB` forbids.  If the probe
      rejects for a different reason, the trace is wrong.
  U2  exists PP.exists PP.(exists DR.A) and forall DR.not A   REJECT (two hops;
      comp(PP,PP)={PP} then comp(PP,DR)={DR})
  U3  exists DR.(exists PPI.A) and forall DR.not A          REJECT
      (comp(DR,PPI)={DR})
  S1  exists DR.(A and exists DR.B)                         ACCEPT
  S2  exists PP.TOP and forall PP.exists PP.TOP             ACCEPT (an infinite
      tower is satisfiable and within the framework)
  S3  exists PO.A and forall DR.B                           ACCEPT
  S4  exists PPI.A and exists DR.B                          ACCEPT

  A REJECT among S1-S4 means `prune` is TOO STRONG -- completeness would be
  violated, contradicting `coneScheme_complete`, so it would indict this
  transcription rather than the Lean.
  An ACCEPT among U1-U3 means `prune` is TOO WEAK: survivors are not realizable
  and soundness cannot be proved without strengthening it -- at which point
  `pruneSig_mono` must be re-proved.

NON-VACUITY is reported first: how many signatures are admissible, and how many
survive.  If nothing is admissible, or nothing is ever eliminated, the verdicts
below carry no information.

SCOPE, stated carefully.  The full signature space has 2^(2^m) predecessor sets,
so the GFP below runs at |S| <= 1.  A rejection on a TRUNCATED space is NOT by
itself conclusive -- a smaller space makes `prune` remove more -- so the UNSAT
verdicts are backed separately by `dr_wall`, which quantifies over TYPES only and
therefore holds at every cap.  The capped GFP is corroboration; the cap-free
check is the argument.  All concepts here are forall-PO-free.

Self-contained: the RCC5 table is re-derived from finite set semantics.
"""

from itertools import combinations

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"


def _rel(a, b):
    if a == b:
        return EQ
    if a < b:
        return PP
    if b < a:
        return PPI
    return DR if not (a & b) else PO


def comp_table(n=4):
    regs = [frozenset(c) for k in range(1, n + 1)
            for c in combinations(range(n), k)]
    t = {}
    for a in regs:
        for b in regs:
            r = _rel(a, b)
            for c in regs:
                t.setdefault((r, _rel(b, c)), set()).add(_rel(a, c))
    return t


CT = comp_table(4)
assert sorted(CT[(PP, PP)]) == [PP]
assert sorted(CT[(PP, DR)]) == [DR]
assert sorted(CT[(DR, PPI)]) == [DR]

# ------------------------------------------------------------ concept syntax
# ('at',i) ('nat',i) ('top',) ('and',c,d) ('or',c,d) ('ex',r,c) ('all',r,c)


def closure(c, acc=None):
    acc = [] if acc is None else acc
    if c not in acc:
        acc.append(c)
    if c[0] in ("and", "or"):
        closure(c[1], acc)
        closure(c[2], acc)
    elif c[0] in ("ex", "all"):
        closure(c[2], acc)
    return acc


def po_free(c):
    if c[0] in ("at", "nat", "top", "bot"):   # "bot" added 2026-08-29: the
        return True                           # cold review hit an IndexError

    if c[0] in ("and", "or"):
        return po_free(c[1]) and po_free(c[2])
    if c[0] == "all" and c[1] == PO:
        return False
    return po_free(c[2])


# ------------------------------------------- the control layer (transcribed)

def supportB(T):
    """`supportB` of §270: no bottom, no literal clash, and/or closed, and EQ
    universals AND existentials LOCAL (strong EQ is identity)."""
    for c in T:
        if c[0] == "bot":
            return False
        if c[0] == "at" and ("nat", c[1]) in T:
            return False
        if c[0] == "and" and not (c[1] in T and c[2] in T):
            return False
        if c[0] == "or" and not (c[1] in T or c[2] in T):
            return False
        if c[0] in ("all", "ex") and c[1] == EQ and c[2] not in T:
            return False
    return True


def allBodies(r, T):
    return frozenset(c[2] for c in T if c[0] == "all" and c[1] == r)


def sigOkB(q):
    T, S = q
    if not supportB(T):
        return False
    for U in S:
        if not supportB(U):
            return False
        if not allBodies(PP, U) <= T:
            return False
        if not allBodies(PPI, T) <= U:
            return False
    return True


def sigCone(q):
    return (q[0],) + tuple(q[1])


def compatB(r, D, q, qp):
    if D not in qp[0]:
        return False
    if r == PP:
        return all(U in qp[1] for U in sigCone(q))
    if r == PPI:
        return all(U in q[1] for U in sigCone(qp))
    if r == DR:
        for U in sigCone(q):
            for V in sigCone(qp):
                if not (allBodies(DR, U) <= V and allBodies(DR, V) <= U):
                    return False
        return True
    return True                       # PO, EQ: no structural condition


def sigDemands(q):
    return [(c[1], c[2]) for c in q[0] if c[0] == "ex" and c[1] != EQ]


def prune(X, cone_of, bodies_of, by_body, demands_of):
    """One round.  Targets are indexed by the demand's BODY: only a signature
    whose type contains `D` can serve `exists r.D`, which is what makes the
    quadratic scan affordable."""
    Xs = set(X)
    out = []
    for q in X:
        ok = True
        for (r, D) in demands_of[q]:
            cands = by_body.get(D, ())
            found = False
            for qp in cands:
                if qp not in Xs:
                    continue
                if _compat_fast(r, q, qp, cone_of, bodies_of):
                    found = True
                    break
            if not found:
                ok = False
                break
        if ok:
            out.append(q)
    return out


def _compat_fast(r, q, qp, cone_of, bodies_of):
    if r == PP:
        return all(U in qp[1] for U in cone_of[q])
    if r == PPI:
        return all(U in q[1] for U in cone_of[qp])
    if r == DR:
        for U in cone_of[q]:
            bU = bodies_of[U]
            for V in cone_of[qp]:
                if not (bU <= V and bodies_of[V] <= U):
                    return False
        return True
    return True


# ------------------------------------------------------------- the state space

def support_types(cl):
    out = []
    for k in range(len(cl) + 1):
        for sub in combinations(cl, k):
            T = frozenset(sub)
            if supportB(T):
                out.append(T)
    return out


def signatures(cl, cap):
    Ts = support_types(cl)
    sigs = []
    for T in Ts:
        for k in range(min(cap, len(Ts)) + 1):
            for S in combinations(Ts, k):
                q = (T, frozenset(S))
                if sigOkB(q):
                    sigs.append(q)
    return sigs


def gfp(cl, C0, cap):
    X = signatures(cl, cap)
    n0 = len(X)
    cone_of = {q: sigCone(q) for q in X}
    demands_of = {q: sigDemands(q) for q in X}
    allT = set()
    for q in X:
        allT.update(cone_of[q])
    bodies_of = {U: allBodies(DR, U) for U in allT}
    by_body = {}
    for q in X:
        for c in q[0]:
            by_body.setdefault(c, []).append(q)
    rounds = 0
    while True:
        Y = prune(X, cone_of, bodies_of, by_body, demands_of)
        rounds += 1
        if len(Y) == len(X):
            break
        X = Y
        Xset = set(X)
        by_body = {k: [q for q in v if q in Xset] for k, v in by_body.items()}
        if rounds > 100:
            break
    accept = any(C0 in q[0] for q in X)
    return accept, n0, len(X), rounds


# --------------------------------------------------------------- diagnostics

A = ("at", 0)
NA = ("nat", 0)
B = ("at", 1)
TOP = ("top",)

CASES = [
    ("U1 exPP(exDR A) & allDR notA", False,
     ("and", ("ex", PP, ("ex", DR, A)), ("all", DR, NA))),
    ("U2 exPP exPP(exDR A) & allDR notA", False,
     ("and", ("ex", PP, ("ex", PP, ("ex", DR, A))), ("all", DR, NA))),
    ("U3 exDR(exPPI A) & allDR notA", False,
     ("and", ("ex", DR, ("ex", PPI, A)), ("all", DR, NA))),
    ("S1 exDR(A & exDR B)", True,
     ("ex", DR, ("and", A, ("ex", DR, B)))),
    ("S2 exPP TOP & allPP exPP TOP", True,
     ("and", ("ex", PP, TOP), ("all", PP, ("ex", PP, TOP)))),
    ("S3 exPO A & allDR B", True,
     ("and", ("ex", PO, A), ("all", DR, B))),
    ("S4 exPPI A & exDR B", True,
     ("and", ("ex", PPI, A), ("ex", DR, B))),
]

CAPS = [1]      # see SCOPE: rejection is argued cap-free by dr_wall


def dr_wall(cl):
    """A CAP-INDEPENDENT check of the mechanism behind the UNSAT verdicts.

    The DR transition condition demands `A_DR(U) subset V` for every U in the
    source's cone and V in the target's.  So if a cone member carries
    `forall DR.not A`, every target-cone member must carry `not A` -- and a
    target type carrying `A` is then rejected by supportB's literal-clash
    clause.  This quantifies over TYPES only, never over S, so it holds at every
    cap, which a truncated brute force cannot establish."""
    Ts = support_types(cl)
    walls = breaches = 0
    for U in Ts:
        bU = allBodies(DR, U)
        for V in Ts:
            clash = any((c[0] == "nat" and ("at", c[1]) in V) or
                        (c[0] == "at" and ("nat", c[1]) in V) for c in bU)
            if not clash:
                continue
            if bU <= V:
                breaches += 1
            else:
                walls += 1
    return walls, breaches


def main():
    print(__doc__.split("Self-contained")[0].rstrip())
    print("=" * 72)
    walls, breaches = dr_wall(closure(CASES[0][2]))
    print("CAP-FREE MECHANISM CHECK (quantifies over types only):")
    print(f"  DR transitions blocked by a forall-DR body clashing with the "
          f"target: {walls} blocked, {breaches} breaches"
          f"  {'OK' if breaches == 0 else '<-- BREACH'}")
    print()
    print(f"{'case':34s} {'want':>6} {'|sigs|':>8} {'survive':>8} "
          f"{'rounds':>7} {'verdict':>8}")
    ok = True
    vacuous = True
    inconclusive = []
    for (name, want, C0) in CASES:
        assert po_free(C0), name
        cl = closure(C0)
        verdicts = []
        line = None
        for cap in CAPS:
            acc, n0, n1, rd = gfp(cl, C0, cap)
            verdicts.append(acc)
            if cap == CAPS[-1]:
                line = (n0, n1, rd)
            if n0 > 0 and n1 < n0:
                vacuous = False
        n0, n1, rd = line
        stable = len(set(verdicts)) == 1
        got = verdicts[-1]
        good = stable and (got == want)
        if not stable:
            inconclusive.append(name)
        ok &= good
        print(f"  {name:32s} {'SAT' if want else 'UNSAT':>6} {n0:8d} "
              f"{n1:8d} {rd:7d} "
              f"{('ACCEPT' if got else 'REJECT'):>8}"
              f"{'' if good else '   <-- MISMATCH'}"
              f"{'' if stable else '  (cap-dependent)'}")
    print()
    print(f"  non-vacuous (elimination actually removed signatures): "
          f"{'YES' if not vacuous else 'NO'}")
    if inconclusive:
        print(f"  cap-dependent verdicts: {inconclusive}")
    print("=" * 72)
    if vacuous:
        print("VERDICT: VACUOUS -- nothing was ever eliminated; the run says")
        print("  nothing about prune's strength.")
        return 1
    if ok and breaches == 0:
        print("VERDICT: prune REJECTS every unsatisfiable diagnostic and")
        print("  ACCEPTS every satisfiable one.")
        print("  The ACCEPTs are conclusive at any cap: prune is MONOTONE, so a")
        print("  larger signature space can only keep more.  The REJECTs at cap")
        print("  1 are corroboration only; what carries them is the cap-free")
        print("  wall check above, which quantifies over types alone.")
        print("  This is NOT a soundness proof -- that is gate G2/G3 and needs")
        print("  the unfolding.  It shows prune is not too weak on the standing")
        print("  diagnostics; it does not show survivors are realizable.")
        return 0
    print("VERDICT: MISMATCH.  An accepted UNSAT case means prune is TOO WEAK")
    print("  and must be strengthened -- after which pruneSig_mono has to be")
    print("  re-proved (the §270 tripwire).  A rejected SAT case would instead")
    print("  indict this transcription, since coneScheme_complete is certified.")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
