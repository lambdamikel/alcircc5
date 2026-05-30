"""
WP13 -- the automata-route referee's four acceptance tests, machine-checked
against a model of the repaired proof's PRODUCT-STATE representation.

The 5th cold review (papers/automata_route_repairs/rcc5_split_forest_referee_report)
found that the automata route's `Patch` invariant -- a finite local check that is
supposed to guarantee global RCC5 composition + universal propagation to all
composition-forced targets + equality congruence -- was asserted, not
constructed.  Its decisive symptom: a checker that only records *selected*
witnesses misses that a witness-of-a-witness is also a composition-forced target
of an ancestor, so it wrongly accepts small UNSAT concepts.  The repair
(split_forest_automata_repaired_full_proof + the A/B/C companion, Theorem B)
replaces the informal patch with finite pair/triple PRODUCT-STATE representatives
that *derive* the forced label of every global pair and check universals on it.

This script models that mechanism at small scale -- composition closure
(path-consistency) over the occurrence set, with universal-aware and type-aware
(EQ) domain pruning, plus existential-demand discharge with request-closed
blocking -- and runs the referee's four acceptance tests (report Section 9):

  Test 1  C_force     = EPP.(EDR.A) & ADR.~A                      -> REJECT (UNSAT)
  Test 2  C_split     = EPP.(A & ~B & APP.~B & APPI.~B & APO.~B)
                        & EPP.B                                    -> REJECT (UNSAT)
  Test 3  C_recursive = EDR.(A & EDR.B)                            -> ACCEPT (SAT)
                        (and: REJECT if the recursive B-witness is omitted)
  Test 4  C_up        = EPP.T & APP.EPP.T                          -> ACCEPT (SAT,
                        infinite PP-chain; repeated profile lap is PP, not EQ)

Each verdict is (a) produced by the product-state engine here and (b)
cross-checked against the independent cover-tree tableau decision procedure
(src/cover_tree_tableau.py).  This is the analog of WP10/WP12 for the automata
route's Theorem B keystone: it checks that the product-state representation
derives the forced labels and applies universals to them, exactly where the old
`Patch` failed.  It does NOT verify Theorem B's general finiteness/adequacy --
that is the manuscript-level keystone awaiting cold review.

Self-contained RCC5 table (with EQ); imports the AST + cover-tree tableau only
for the oracle cross-check.
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "src"))

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


# --------------------------------------------------------------------------- #
#  occurrence structure.  A type is
#     dict(pos=set, neg=set, univ=[(R, '+'|'-', atom)],
#          exists=[(R, req_pos:frozenset, req_neg:frozenset)], blocked=bool)
#  edges = list of (src, R, dst) selected witnesses.
# --------------------------------------------------------------------------- #
def T(pos=(), neg=(), univ=(), exists=(), blocked=False):
    return dict(pos=set(pos), neg=set(neg), univ=list(univ),
                exists=[(R, frozenset(p), frozenset(n)) for (R, p, n) in exists],
                blocked=blocked)


def violates(sign, atom, ty):
    """does target type ty violate forall R.(atom/sign)?"""
    return (atom in ty["neg"]) if sign == "+" else (atom in ty["pos"])


def eq_compatible(t1, t2):
    return not (t1["pos"] & t2["neg"] or t2["pos"] & t1["neg"])


def meets(ty, req_pos, req_neg):
    return req_pos <= ty["pos"] and req_neg <= ty["neg"]


def product_state_sat(nodes, types, edges):
    """Composition closure (path-consistency) with universal-aware + type-aware
    domain pruning -- a model of the repaired proof's product-state
    representation.  Returns ('SAT'|'UNSAT', reason, D)."""
    D = {(x, y): set(BASE) for x in nodes for y in nodes if x != y}
    for x in nodes:
        for y in nodes:
            if x != y and not eq_compatible(types[x], types[y]):
                D[(x, y)].discard(EQ)
    for (a, R, b) in edges:
        D[(a, b)] = {R}; D[(b, a)] = {INV[R]}

    while True:
        changed = False
        # universal-aware pruning
        for x in nodes:
            for (R, sign, atom) in types[x]["univ"]:
                for y in nodes:
                    if x != y and R in D[(x, y)] and violates(sign, atom, types[y]):
                        D[(x, y)].discard(R); D[(y, x)].discard(INV[R]); changed = True
        # composition closure
        for x in nodes:
            for y in nodes:
                for z in nodes:
                    if len({x, y, z}) < 3:
                        continue
                    allowed = set()
                    for r in D[(x, y)]:
                        for s in D[(y, z)]:
                            allowed |= comp(r, s)
                    if D[(x, z)] & allowed != D[(x, z)]:
                        D[(x, z)] &= allowed; changed = True
        # converse sync
        for x in nodes:
            for y in nodes:
                if x != y:
                    inv = {INV[r] for r in D[(x, y)]}
                    if D[(y, x)] & inv != D[(y, x)]:
                        D[(y, x)] &= inv; changed = True
        for x in nodes:
            for y in nodes:
                if x != y and not D[(x, y)]:
                    return "UNSAT", f"forced relation ({x},{y}) ruled out by composition+universals", D
        if not changed:
            break

    # existential demand discharge (blocked nodes are request-closed by the cycle)
    for x in nodes:
        if types[x]["blocked"]:
            continue
        for (R, rp, rn) in types[x]["exists"]:
            if not any(R in D[(x, y)] and meets(types[y], rp, rn)
                       for y in nodes if y != x):
                return "UNSAT", f"existential demand {R}.(+{set(rp)}-{set(rn)}) of {x} undischarged", D
    return "SAT", "consistent product-state network; all demands discharged", D


# --------------------------------------------------------------------------- #
#  the four referee tests as occurrence structures
# --------------------------------------------------------------------------- #
def test_C_force():
    nodes = ["x", "y", "z"]
    types = {
        "x": T(univ=[(DR, "-", "A")], exists=[(PP, (), ())]),
        "y": T(exists=[(DR, ("A",), ())]),
        "z": T(pos=["A"]),
    }
    edges = [("x", PP, "y"), ("y", DR, "z")]
    note = ("x PP y, y DR z  =>  x DR z  (comp(PP,DR)={DR}); "
            "ADR.~A at x then forces z:~A, contradicting z:A")
    return "C_force = EPP.(EDR.A) & ADR.~A", nodes, types, edges, "UNSAT", note


def test_C_split():
    nodes = ["x", "y", "z"]
    types = {
        "x": T(exists=[(PP, ("A",), ("B",)), (PP, ("B",), ())]),
        "y": T(pos=["A"], neg=["B"],
               univ=[(PP, "-", "B"), (PPI, "-", "B"), (PO, "-", "B")]),
        "z": T(pos=["B"]),
    }
    edges = [("x", PP, "y"), ("x", PP, "z")]
    note = ("y PPI x, x PP z  =>  rho(y,z) in comp(PPI,PP)={EQ,PP,PPI,PO}; "
            "EQ excluded (y:~B vs z:B); PP/PPI/PO each fire y's APP/APPI/APO.~B on z:B")
    return ("C_split = EPP.(A&~B&APP.~B&APPI.~B&APO.~B) & EPP.B",
            nodes, types, edges, "UNSAT", note)


def test_C_recursive(with_witness=True):
    nodes = ["x", "y"] + (["w"] if with_witness else [])
    types = {
        "x": T(exists=[(DR, ("A",), ())]),
        "y": T(pos=["A"], exists=[(DR, ("B",), ())]),
    }
    edges = [("x", DR, "y")]
    if with_witness:
        types["w"] = T(pos=["B"]); edges.append(("y", DR, "w"))
    note = ("EDR.(A & EDR.B): the A-witness y must ITSELF have a represented "
            "DR-witness w:B (recursive child obligation)")
    return ("C_recursive = EDR.(A & EDR.B)" + ("" if with_witness else "  [B-witness omitted]"),
            nodes, types, edges, "SAT" if with_witness else "UNSAT", note)


def test_C_up():
    # blocking model: a0 PP a1 PP a2, profile(a1)=profile(a2); a2 blocked (cycle)
    nodes = ["a0", "a1", "a2"]
    types = {
        "a0": T(exists=[(PP, (), ())]),
        "a1": T(exists=[(PP, (), ())]),
        "a2": T(exists=[(PP, (), ())], blocked=True),
    }
    edges = [("a0", PP, "a1"), ("a1", PP, "a2")]
    note = ("infinite PP-chain via repeated profile, a2 blocked by a1 (request-closed); "
            "the repeated lap a1 PP a2 is PP, NOT EQ -- profile repetition is not equality")
    return "C_up = EPP.T & APP.EPP.T", nodes, types, edges, "SAT", note


# --------------------------------------------------------------------------- #
#  oracle cross-check: build the concepts in the AST, run the cover-tree tableau
# --------------------------------------------------------------------------- #
def oracle_verdicts():
    from alcircc5_reasoner import (AtomicConcept, NegAtomicConcept, And, Exists,
                                   ForAll, Top, DR as rDR, PO as rPO, PP as rPP, PPI as rPPI)
    from cover_tree_tableau import check_satisfiability as ct
    A, B = AtomicConcept("A"), AtomicConcept("B")
    nA, nB = NegAtomicConcept("A"), NegAtomicConcept("B")

    def conj(xs):
        o = xs[0]
        for c in xs[1:]:
            o = And(o, c)
        return o

    concepts = {
        "C_force": And(Exists(rPP, Exists(rDR, A)), ForAll(rDR, nA)),
        "C_split": And(Exists(rPP, conj([A, nB, ForAll(rPP, nB), ForAll(rPPI, nB),
                                         ForAll(rPO, nB)])), Exists(rPP, B)),
        "C_recursive": Exists(rDR, And(A, Exists(rDR, B))),
        "C_up": And(Exists(rPP, Top()), ForAll(rPP, Exists(rPP, Top()))),
    }
    return {k: ("SAT" if ct(C)[0] else "UNSAT") for k, C in concepts.items()}


# --------------------------------------------------------------------------- #
def main():
    print("=" * 74)
    print("WP13: automata-route referee acceptance tests vs product-state engine")
    print("=" * 74)
    print()
    cases = [test_C_force(), test_C_split(), test_C_recursive(True),
             test_C_recursive(False), test_C_up()]
    engine_ok = True
    results = {}
    blk_ok = True
    for (name, nodes, types, edges, expect, note) in cases:
        print("-" * 74)
        print(name)
        print(f"  derivation: {note}")
        got, reason, D = product_state_sat(nodes, types, edges)
        tag = "PASS" if got == expect else "FAIL"
        engine_ok &= (got == expect)
        print(f"  product-state engine: {got:5}  (expected {expect})  [{tag}]  -- {reason}")
        if name.startswith("C_up"):                       # blocking-not-equality check
            lap = D[("a1", "a2")]
            blk_ok = (lap == {PP})
            print(f"  blocking-not-equality: rho(a1,a2)={sorted(lap)}  "
                  f"(must be {{PP}}, not EQ)  [{'PASS' if blk_ok else 'FAIL'}]")
        if "[B-witness omitted]" not in name:
            results[name.split(" =")[0]] = got
        print()

    print("-" * 74)
    print("oracle cross-check (independent cover-tree tableau decision procedure):")
    try:
        orc = oracle_verdicts()
        oracle_ok = all(results.get(k) == orc[k] for k in orc)
        for k in ["C_force", "C_split", "C_recursive", "C_up"]:
            print(f"  {k:12}: engine={results.get(k):5}  tableau={orc[k]:5}  "
                  f"{'agree' if results.get(k) == orc[k] else 'MISMATCH'}")
    except Exception as e:
        oracle_ok = False
        print(f"  oracle cross-check failed: {e}")
    print()
    print("=" * 74)
    ok = engine_ok and oracle_ok and blk_ok
    if ok:
        print("VERDICT: PASS.  The product-state representation derives the forced")
        print("         labels (x PP y, y DR z => x DR z, etc.) and applies universals")
        print("         to them: it REJECTS the referee's UNSAT tests (C_force, C_split)")
        print("         where the old Patch wrongly accepted, ACCEPTS C_recursive only")
        print("         with the recursive child-witness, and ACCEPTS C_up via a")
        print("         PP-labelled (not EQ) repeated lap.  Engine and the independent")
        print("         cover-tree tableau agree on all four.")
        print("         (Checks Theorem B's MECHANISM on these witnesses; does NOT")
        print("          verify Theorem B's general finiteness/adequacy.)")
    else:
        print("VERDICT: FAIL / INVESTIGATE.")
    print("=" * 74)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
