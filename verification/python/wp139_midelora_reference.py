#!/usr/bin/env python3
"""
WP139 -- the MiDeLoRa calculus as a reference reasoner (2026-11-11)

src/midelora_tableau.py is a complete-graph ABox tableau for ALCI_RCC5 after the
ALCI_RA_JEPD prover of M. Wessel's MiDeLoRa (dissertation 2008, sections 6.2.7.2
and 6.4.4; github.com/lambdamikel/midelora). The claim (papers/midelora_calculus):
it is sound and complete and does not terminate -- UNSAT on every unsatisfiable
concept, SAT with a finite model on every concept that has one, no answer on
satisfiable concepts whose models are all infinite.

This probe is the evidence for the IMPLEMENTATION. It checks

  A  the composition table the reasoner derives from sets: stable in the size of
     the universe; equal to MiDeLoRa's rcc5-rolebox (transcribed from
     tables/tables2.lisp, with its own argument swap); equal on proper relations
     to the table of src/alcircc5_reasoner.py;
  B  named concepts whose status is known independently -- by a Lean theorem, by
     a set model, or by a two-line argument -- including the project's gate
     (C_bad, C_joint, C_dir rejected; C_sat accepted), K2, C_cyc (which neither
     existing reasoner returns on), the strong-EQ PO-loop, and MiDeLoRa's own
     test concepts. Every SAT answer comes with a model, re-checked here by a
     function that shares nothing with the search;
  C  EXACT ground truth. For conjunctions of <= 3 existentials without nested
     existentials a satisfiable concept has a model on <= 4 points, so exhaustive
     search over closed atomic networks decides it. 1,000 random concepts under
     strong EQ, 300 under weak EQ (MiDeLoRa as implemented), no size cap;
  D  the 911-case suite: the reasoner must DECIDE every concept and agree with
     the quasimodel oracle, the cover-tree tableau and the suite's labels;
  E  non-termination where it belongs: on concepts with only infinite models the
     answer must be UNKNOWN -- neither a false refutation nor a false model --
     and the 4-colour spiral, which has a 4-point model, must be found SAT;
  F  strong against weak EQ: K2x is unsatisfiable under strong EQ and
     satisfiable under weak EQ, and UNSAT-weak implies UNSAT-strong on the
     sample of part C.

Not shown: anything about concepts beyond these. The proof is on paper.

Usage:  python3 wp139_midelora_reference.py        (about 2 minutes)
"""
import collections
import itertools
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, '..', '..', 'src')))
from alcircc5_reasoner import (DR, PO, PP, PPI, AtomicConcept as At, NegAtomicConcept as Nat,
                               And, Or, Exists as Ex, ForAll as All, Top, COMP as QCOMP)
import alcircc5_reasoner as Q
import cover_tree_tableau as T
import midelora_tableau as M
import stress_test_cover_tree as ST

EQ = M.EQ
RESULTS = []


def check(name, ok, detail=''):
    RESULTS.append(bool(ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"  -- {detail}" if detail else ''), flush=True)


def conj(*xs):
    r = xs[0]
    for x in xs[1:]:
        r = And(r, x)
    return r


def disj(*xs):
    r = xs[0]
    for x in xs[1:]:
        r = Or(r, x)
    return r


A, B, C, D = At('A'), At('B'), At('C'), At('D')
nA, nB, nC = Nat('A'), Nat('B'), Nat('C')
ALLP = (PO, DR, PP, PPI)


def W(P, nQ):
    return conj(P, nQ, All(PO, nQ), All(DR, nQ), All(PPI, nQ))


def spiral(m):
    """Marzec & Tendera's spiral, read in RCC5, with m colours (m = 5: only infinite models)."""
    a = [At(f'A{i}') for i in range(m)]
    n = [Nat(f'A{i}') for i in range(m)]
    parts = [disj(*a)] + [Or(n[i], n[j]) for i in range(m) for j in range(i + 1, m)]
    for i in range(m):
        parts.append(Or(n[i], And(All(PO, n[(i + 2) % m]), All(DR, n[(i + 2) % m]))))
        parts.append(Or(n[i], And(Or(Ex(PO, a[(i + 1) % m]), Ex(DR, a[(i + 1) % m])),
                                  Or(Ex(PO, a[(i - 1) % m]), Ex(DR, a[(i - 1) % m])))))
    body = conj(*parts)
    return conj(a[0], body, *[All(r, body) for r in ALLP])


NAMED = [
    # name, concept, expected, why
    ('K2', conj(Ex(PO, conj(A, All(PO, nB), All(DR, nB))), Ex(PO, conj(B, nA))), 'SAT', 'Lean k2_sat'),
    ('K2dr', conj(Ex(DR, conj(A, All(PO, nB), All(DR, nB))), Ex(DR, conj(B, nA))), 'SAT', 'set model, wp137 E2'),
    ('K2x', conj(Ex(PO, conj(A, *[All(r, nB) for r in ALLP])), Ex(PO, conj(B, nA))), 'UNSAT',
     'no relation left between two distinct witnesses'),
    ('C_cyc', conj(Ex(PP, W(A, nB)), Ex(PP, W(B, nC)), Ex(PP, W(C, nA))), 'UNSAT', 'Lean ccyc_unsat'),
    ('C_cyc erased', conj(*[Ex(PP, conj(P, nQ, All(DR, nQ), All(PPI, nQ)))
                            for P, nQ in ((A, nB), (B, nC), (C, nA))]), 'SAT', 'Lean ccycErased_sat'),
    ('H3cyc', conj(Ex(PO, W(A, nB)), Ex(PO, W(B, nC)), Ex(PO, W(C, nA))), 'UNSAT', 'a < b < c < a'),
    ('H3chain', conj(Ex(PO, W(A, nB)), Ex(PO, W(B, nC)), Ex(PO, conj(C, nA, nB))), 'SAT', 'a < b < c'),
    ('C_bad', conj(Ex(PPI, Ex(PP, A)), All(PP, nA), All(PPI, nA), nA, All(PO, nA)), 'UNSAT', 'overview, gate'),
    ('C_joint', conj(Ex(PP, conj(All(PPI, A), All(PO, A))), Ex(PO, nA)), 'UNSAT', 'overview, gate'),
    ('C_dir', conj(All(PO, A), Ex(PO, nA)), 'UNSAT', 'Lean cpo_unsat'),
    ('C_sat', conj(Ex(PP, conj(A, All(PO, A))), Ex(PP, nA)), 'SAT', 'overview, gate'),
    ('C_force', conj(Ex(PP, Ex(DR, A)), All(DR, nA)), 'UNSAT', 'comp(PP,DR) = {DR}'),
    ('C_recursive', Ex(DR, conj(A, Ex(DR, B))), 'SAT', '5th review'),
    ('C_optional', conj(All(PPI, A), Ex(PO, All(PPI, nA))), 'SAT', 'Astra 6'),
    ('PO-loop', conj(C, Ex(PO, Ex(PO, C)), *[All(r, nC) for r in ALLP]), 'SAT',
     'the witness must be the root itself'),
    ('MiDeLoRa: EPO^4.c, c excluded everywhere incl. EQ',
     conj(Ex(PO, Ex(PO, Ex(PO, Ex(PO, C)))), *[All(r, nC) for r in ALLP], All(EQ, nC)), 'UNSAT',
     'prover/examples.lisp'),
    ('MiDeLoRa: the same with AEQ.d', conj(Ex(PO, Ex(PO, Ex(PO, Ex(PO, C)))), *[All(r, nC) for r in ALLP],
                                           All(EQ, D)), 'SAT', 'prover/examples.lisp'),
    ('MiDeLoRa: EPP.EPP.c & APP.e', conj(Ex(PP, Ex(PP, C)), All(PP, At('E'))), 'SAT', 'prover/examples.lisp'),
    ('spiral, 4 colours', spiral(4), 'SAT', 'a 4-point model, wp137 D4'),
]

INFINITE = [
    ('EPP.T & APP.EPP.T', conj(Ex(PP, Top()), All(PP, Ex(PP, Top()))), 5),
    ('EPPI.T & APPI.EPPI.T', conj(Ex(PPI, Top()), All(PPI, Ex(PPI, Top()))), 5),
    ('Cdchain = EDR.ADR.EPPI.A', Ex(DR, All(DR, Ex(PPI, A))), 5),
    ('spiral, 5 colours', spiral(5), 4),
]

# MiDeLoRa's +rcc5-rolebox+ exactly as listed in tables/tables2.lisp; the source applies
# swap-first-args to every row, so a listed row (S R result) is the composition R ; S.
MIDELORA_ROWS = """
dr dr *      | dr po dr,po,ppi | dr eq dr | dr pp dr           | dr ppi dr,po,ppi
po dr dr,po,pp | po po *       | po eq po | po pp dr,po,pp     | po ppi po,ppi
eq dr dr     | eq po po        | eq eq eq | eq pp pp           | eq ppi ppi
pp dr dr,po,pp | pp po po,pp   | pp eq pp | pp pp pp           | pp ppi po,eq,pp,ppi
ppi dr dr    | ppi po dr,po,ppi | ppi eq ppi | ppi pp *        | ppi ppi ppi
"""
NAME = {'dr': DR, 'po': PO, 'eq': EQ, 'pp': PP, 'ppi': PPI}


def midelora_table():
    t = {}
    for cell in MIDELORA_ROWS.replace('\n', '|').split('|'):
        cell = cell.split()
        if not cell:
            continue
        s, r, res = cell
        res = M.ALL5 if res == '*' else tuple(NAME[x] for x in res.split(','))
        t[(NAME[r], NAME[s])] = frozenset(res)       # the swap
    return t


# ---------------------------------------------------------------- exact ground truth
def networks(n, rels):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for choice in itertools.product(rels, repeat=len(pairs)):
        rel = [[None] * n for _ in range(n)]
        for (i, j), r in zip(pairs, choice):
            rel[i][j] = r
            rel[j][i] = M.INV5[r]
        if all(rel[i][l] in M.COMP5[(rel[i][j], rel[j][l])]
               for i in range(n) for j in range(n) if j != i
               for l in range(n) if l != i and l != j):
            yield rel


NETS = {False: {n: list(networks(n, M.PROPER)) for n in (1, 2, 3, 4)},
        True: {n: list(networks(n, M.ALL5)) for n in (1, 2, 3, 4)}}
VALS = [frozenset(s) for s in ([], ['A'], ['B'], ['A', 'B'])]


def holds(c, x, rel, val, n):
    if isinstance(c, At):
        return c.name in val[x]
    if isinstance(c, Nat):
        return c.name not in val[x]
    if isinstance(c, And):
        return holds(c.left, x, rel, val, n) and holds(c.right, x, rel, val, n)
    if isinstance(c, Or):
        return holds(c.left, x, rel, val, n) or holds(c.right, x, rel, val, n)
    if isinstance(c, Ex):
        return any(y != x and rel[x][y] == c.role and holds(c.concept, y, rel, val, n) for y in range(n))
    if isinstance(c, All):
        return all(y == x or rel[x][y] != c.role or holds(c.concept, y, rel, val, n) for y in range(n))
    raise TypeError(c)


def truth(c, k, weak=False):
    for n in range(1, k + 2):
        for rel in NETS[weak][n]:
            for val in itertools.product(VALS, repeat=n):
                if holds(c, 0, rel, val, n):
                    return True
    return False


LITS = [A, nA, B, nB]


def gen(rng):
    def lits(n):
        return [(At(x) if rng.random() < .5 else Nat(x)) for x in rng.sample(['A', 'B'], n)]

    def univs(n):
        return [All(rng.choice(ALLP), rng.choice(LITS)) for _ in range(n)]
    k = rng.choice([2, 2, 3])
    parts = []
    for _ in range(k):
        role = rng.choices((DR, PO, PP, PPI), weights=[3, 4, 1.5, 1.5])[0]
        parts.append(Ex(role, conj(*(lits(rng.choice([1, 1, 2])) + univs(rng.choice([0, 1, 2, 2, 3, 4]))))))
    parts += lits(rng.choice([0, 0, 1])) + univs(rng.choice([0, 0, 1, 2]))
    return conj(*parts), k


def main():
    t0 = time.time()
    print("=" * 78)
    print("WP139 -- the MiDeLoRa calculus as a reference reasoner")
    print("=" * 78)

    print("\nPart A -- the composition table")
    check("A1 derived from sets: the same table for universes of 4, 5 and 6 points",
          M.derive_table(4) == M.COMP5 == M.derive_table(6))
    mt = midelora_table()
    check("A2 equal to MiDeLoRa's rcc5-rolebox, all 25 cells", len(mt) == 25 and mt == M.COMP5)
    check("A3 equal on proper relations to the table of alcircc5_reasoner.py",
          all(frozenset(x for x in M.COMP5[(r, s)] if x != EQ) == frozenset(QCOMP[(r, s)])
              for r in M.PROPER for s in M.PROPER))

    print("\nPart B -- named concepts (strong EQ); every SAT answer's model is re-checked")
    for name, c, expected, why in NAMED:
        r = M.check(c, max_nodes=6, time_limit=120)
        ok = r.verdict == expected and (expected != 'SAT' or M.verify_model(c, r.model))
        check(f"B  {name}: {expected}", ok,
              f"{r.verdict}, {r.nodes} nodes, {r.closed} closed leaves, {r.seconds:.2f}s; {why}")

    print("\nPart C -- exact ground truth")
    rng = random.Random(20261111)
    stats = collections.Counter()
    sample = []
    for _ in range(1000):
        c, k = gen(rng)
        sample.append((c, k))
        r = M.check(c, max_nodes=4)
        t = truth(c, k)
        good = (r.verdict == ('SAT' if t else 'UNSAT')) and (r.verdict != 'SAT' or M.verify_model(c, r.model))
        stats[(r.verdict, 'SAT' if t else 'UNSAT', good)] += 1
    wrong = sum(v for (_, _, g), v in stats.items() if not g)
    nsat = sum(v for (_, t, _), v in stats.items() if t == 'SAT')
    check("C1 strong EQ: 1,000 concepts, the reasoner equals the truth on each", wrong == 0,
          f"{wrong} wrong; {nsat} satisfiable, {1000 - nsat} unsatisfiable; no UNKNOWN: "
          f"{not any(v == 'UNKNOWN' for (v, _, _) in stats)}")
    wstats = collections.Counter()
    implied = True
    for c, k in sample[:300]:
        r = M.check(c, max_nodes=4, eq='weak')
        t = truth(c, k, weak=True)
        good = (r.verdict == ('SAT' if t else 'UNSAT')) and (r.verdict != 'SAT' or M.verify_model(c, r.model, 'weak'))
        wstats[(r.verdict, good)] += 1
        if r.verdict == 'UNSAT' and truth(c, k):
            implied = False
    wwrong = sum(v for (_, g), v in wstats.items() if not g)
    check("C2 weak EQ (MiDeLoRa as implemented): 300 concepts, the reasoner equals the weak truth",
          wwrong == 0, f"{wwrong} wrong; {wstats[('SAT', True)]} weakly satisfiable")

    print("\nPart D -- the 911-case suite")
    tests = (ST.gen_known_sat() + ST.gen_known_unsat() + ST.gen_adversarial() + ST.gen_systematic_pairs()
             + ST.gen_random(2, 200) + ST.gen_random(3, 100))
    cnt = collections.Counter()
    for name, c, exp in tests:
        r = M.check(c, max_nodes=5, time_limit=10)
        v = r.verdict
        if v == 'UNKNOWN':
            cnt['unknown'] += 1
            continue
        s = v == 'SAT'
        cnt[v] += 1
        if s and not M.verify_model(c, r.model):
            cnt['bad model'] += 1
        if s != Q.check_satisfiability(c)[0]:
            cnt['vs oracle'] += 1
        if s != T.check_satisfiability(c)[0]:
            cnt['vs tableau'] += 1
        if exp is not None and s != exp:
            cnt['vs label'] += 1
    check("D1 all 911 concepts are decided (no UNKNOWN)", len(tests) == 911 and cnt['unknown'] == 0,
          f"{cnt['SAT']} SAT, {cnt['UNSAT']} UNSAT")
    check("D2 every SAT answer carries a model that passes the independent check", cnt['bad model'] == 0)
    check("D3 agreement with the oracle, the cover-tree tableau and the suite's labels",
          cnt['vs oracle'] == cnt['vs tableau'] == cnt['vs label'] == 0,
          f"disagreements: oracle {cnt['vs oracle']}, tableau {cnt['vs tableau']}, labels {cnt['vs label']}")

    print("\nPart E -- concepts with only infinite models: no answer, as it must be")
    for name, c, bound in INFINITE:
        r = M.check(c, max_nodes=bound, time_limit=120)
        check(f"E  {name}: UNKNOWN up to {bound} nodes", r.verdict == 'UNKNOWN' and r.reason == 'node bound',
              f"{r.verdict} ({r.reason}); {r.closed} closed leaves, {r.cut} cut; {r.seconds:.1f}s")

    print("\nPart F -- strong against weak EQ")
    k2x = NAMED[2][1]
    rs, rw = M.check(k2x), M.check(k2x, eq='weak')
    eq_edge = rw.verdict == 'SAT' and any(EQ in row for row in rw.model[1])
    check("F1 K2x: UNSAT under strong EQ, SAT under weak EQ, by two witnesses that are EQ",
          rs.verdict == 'UNSAT' and rw.verdict == 'SAT' and eq_edge and M.verify_model(k2x, rw.model, 'weak'))
    check("F2 on the sample of C2, UNSAT under weak EQ implies UNSAT under strong EQ", implied)

    print("\n" + "=" * 78)
    print(f"{sum(RESULTS)}/{len(RESULTS)} checks pass   ({time.time() - t0:.0f}s)")
    print("=" * 78)
    return 0 if all(RESULTS) else 1


if __name__ == '__main__':
    sys.exit(main())
