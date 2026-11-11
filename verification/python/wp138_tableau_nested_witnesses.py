#!/usr/bin/env python3
"""
WP138 -- the cover-tree tableau's sibling check, and an experimental repair (2026-11-11)

Background (ERRATA.md, E2). src/cover_tree_tableau.py answers UNSAT on the
satisfiable concept

    K2 = EPO.(A & APO.~B & ADR.~B) & EPO.(B & ~A)

because its sibling check (step 6) admits only {DR,PO} between two DR/PO
witnesses of one node, and K2's two witnesses must be nested.

The repair tested here is behind a flag that is OFF by default:

    check_satisfiability(C, nested_witnesses=True)

It admits PP/PPI between two cross witnesses of one node as well, and replaces
the pairwise test by a JOINT one: the witnesses of a node must carry one
composition-closed atomic network. (Pairwise is not enough once nesting is
allowed: a < b, b < c, c < a pass pair by pair.)

This probe is evidence, not a proof. It checks

  A  the default is unchanged: K2 and K2dr are still rejected (so wp137 E6 and
     every document describing the shipped procedure remain accurate);
  B  with the flag: K2, K2dr and two further concepts found by part C are
     accepted; a control with no admissible relation is still rejected; the 35
     built-in tests and the 911-case cross-validation suite give the same
     verdicts as before;
  C  a differential test with EXACT ground truth. Concept class: a conjunction
     of <= 3 existentials whose bodies contain no existentials, plus root
     literals and root universals. A satisfiable concept of this class has a
     model on <= k+1 points (restrict a model to the root and one witness per
     existential: universals and composition closure survive restriction), so
     exhaustive search over closed atomic RCC5 networks on <= 4 points decides
     it. Shipped tableau, flagged tableau and quasimodel oracle are each
     compared with that truth.

What it does NOT show: soundness or completeness of the flagged procedure
outside these tests. Class C has no nested existentials and no infinite models;
both reasoners enumerate types and do not return on the larger concepts that
would matter most (C_cyc, the spiral).

Usage:  python3 wp138_tableau_nested_witnesses.py [N=400] [seed=20261111] [cap=20]
Part C keeps concepts whose closure has at most `cap` members: both reasoners
enumerate types, and single concepts with a closure of 24 took minutes. At
cap 20 (about one minute) the sample contains no concept on which the shipped
tableau errs -- K2's closure has 22 members. An earlier run of this generator
at cap 24 (462 concepts, 9 minutes; shipped 2 wrong, flagged 0, oracle 0)
found the two that part B lists as F1 and F2.
"""
import io, os, sys, time, random, itertools, contextlib

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.normpath(os.path.join(HERE, '..', '..', 'src'))
sys.path.insert(0, SRC)
from alcircc5_reasoner import (DR, PO, PP, PPI, INV, COMP, AtomicConcept as At,
                               NegAtomicConcept as Nat, And, Or, Exists as Ex,
                               ForAll as All, closure)
import alcircc5_reasoner as Q
import cover_tree_tableau as T

RELS = (DR, PO, PP, PPI)
CAP = 20          # closure-size cap for part C: both reasoners enumerate types
RESULTS = []


def check(name, ok, detail=''):
    RESULTS.append(bool(ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"  -- {detail}" if detail else ''), flush=True)


def conj(*xs):
    r = xs[0]
    for x in xs[1:]:
        r = And(r, x)
    return r


def shipped(c):
    return T.check_satisfiability(c)[0]


def flagged(c):
    return T.check_satisfiability(c, nested_witnesses=True)[0]


A, B = At('A'), At('B')
nA, nB = Nat('A'), Nat('B')
K2 = conj(Ex(PO, conj(A, All(PO, nB), All(DR, nB))), Ex(PO, conj(B, nA)))
K2DR = conj(Ex(DR, conj(A, All(PO, nB), All(DR, nB))), Ex(DR, conj(B, nA)))
CTRL = conj(Ex(PO, conj(A, All(PO, nB))), Ex(PO, conj(B, nA)))
K2X = conj(Ex(PO, conj(A, All(PO, nB), All(DR, nB), All(PP, nB), All(PPI, nB))), Ex(PO, conj(B, nA)))
# found by an earlier run of part C (closure <= 24): mixed DR/PO witnesses that must be nested
F1 = conj(Ex(DR, conj(B, All(PO, B), All(DR, A))), Ex(PO, conj(nA, nB)), A)
F2 = conj(Ex(DR, conj(A, B)), Ex(PO, conj(B, All(PO, nA), All(DR, nA))))


# ---------------------------------------------------------------- ground truth
def networks(n):
    """closed atomic networks on n labelled points; distinct points are never EQ"""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for choice in itertools.product(RELS, repeat=len(pairs)):
        rel = [[None] * n for _ in range(n)]
        for (i, j), r in zip(pairs, choice):
            rel[i][j] = r
            rel[j][i] = INV[r]
        if all(rel[i][l] in COMP[(rel[i][j], rel[j][l])]
               for i in range(n) for j in range(n) if j != i
               for l in range(n) if l != i and l != j):
            yield rel


NETS = {n: list(networks(n)) for n in (1, 2, 3, 4)}
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


def truth(c, k):
    """exact for the class of part C: a model on <= k+1 points exists iff satisfiable"""
    for n in range(1, k + 2):
        for rel in NETS[n]:
            for val in itertools.product(VALS, repeat=n):
                if holds(c, 0, rel, val, n):
                    return True
    return False


LITS = [A, nA, B, nB]


def gen(rng):
    def lits(n):
        return [(At(x) if rng.random() < .5 else Nat(x)) for x in rng.sample(['A', 'B'], n)]

    def univs(n):
        return [All(rng.choice(RELS), rng.choice(LITS)) for _ in range(n)]
    k = rng.choice([2, 2, 3])
    parts = []
    for _ in range(k):
        role = rng.choices(RELS, weights=[3, 4, 1.5, 1.5])[0]
        parts.append(Ex(role, conj(*(lits(rng.choice([1, 1, 2])) + univs(rng.choice([0, 1, 2, 2, 3]))))))
    parts += lits(rng.choice([0, 0, 1])) + univs(rng.choice([0, 0, 1, 2]))
    return conj(*parts), k


def captured(fn):
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        fn()
    return buf.getvalue()


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20261111
    global CAP
    if len(sys.argv) > 3:
        CAP = int(sys.argv[3])
    t0 = time.time()
    print("=" * 76)
    print("WP138 -- cover-tree tableau: the sibling check and an experimental repair")
    print("=" * 76)

    print("\nPart A -- the default is the shipped procedure")
    check("A1 default rejects K2 (the documented wrong verdict)", shipped(K2) is False)
    check("A2 default rejects K2dr", shipped(K2DR) is False)
    check("A3 ground truth: K2 and K2dr are satisfiable (3-point search)", truth(K2, 2) and truth(K2DR, 2))

    print("\nPart B -- nested_witnesses=True")
    check("B1 accepts K2", flagged(K2) is True)
    check("B2 accepts K2dr", flagged(K2DR) is True)
    check("B3 accepts the control (no forall-DR)", flagged(CTRL) is True and shipped(CTRL) is True)
    check("B4 rejects K2x (no admissible relation); ground truth UNSAT",
          flagged(K2X) is False and truth(K2X, 2) is False)
    check("B5 accepts F1 and F2 (found by part C); shipped rejects both; both satisfiable",
          flagged(F1) and flagged(F2) and not shipped(F1) and not shipped(F2) and truth(F1, 2) and truth(F2, 2))
    orig = T.check_satisfiability
    try:
        T.check_satisfiability = lambda C0, verbose=False, **kw: orig(C0, verbose=verbose, nested_witnesses=True)
        out = captured(T.run_tests)
    finally:
        T.check_satisfiability = orig
    line = next((l.strip() for l in out.splitlines() if 'Results:' in l), '?')
    check("B6 the 35 built-in tests under the flag", '35 passed, 0 failed' in line, line)
    import stress_test_cover_tree as ST
    old_ct = ST.check_sat_ct
    try:
        ST.check_sat_ct = lambda C0, *a, **kw: orig(C0, nested_witnesses=True)
        out = captured(ST.run_cross_validation)
    finally:
        ST.check_sat_ct = old_ct
    tail = ' '.join(l.strip() for l in out.splitlines() if 'OVERALL' in l or 'Mismatches' in l)
    check("B7 the 911-case suite under the flag", 'OVERALL: 911 tests' in tail and 'Mismatches (CT ≠ QM): 0' in tail, tail)

    print(f"\nPart C -- differential test with exact ground truth ({N} concepts, seed {seed}, closure <= {CAP})")
    print(f"  closed atomic networks on 1..4 points: {[len(NETS[n]) for n in (1, 2, 3, 4)]}")
    rng = random.Random(seed)
    stats = {}
    done = 0
    while done < N:
        c, k = gen(rng)
        if len(closure(c)) > CAP:
            continue
        done += 1
        s, f, t = shipped(c), flagged(c), truth(c, k)
        try:
            q = Q.check_satisfiability(c)[0]
        except Exception:
            q = None
        key = tuple('S' if v else ('?' if v is None else 'U') for v in (s, f, q, t))
        stats[key] = stats.get(key, 0) + 1
        if done % 50 == 0:
            print(f"  ... {done} concepts, {time.time() - t0:.0f}s", flush=True)
    print("  verdicts as (shipped, flagged, oracle, TRUTH):")
    for key in sorted(stats, key=lambda z: -stats[z]):
        print("     ", ' '.join(key), ' x', stats[key])
    sw = sum(v for k_, v in stats.items() if k_[0] != k_[3])
    sfalse_sat = sum(v for k_, v in stats.items() if k_[0] == 'S' and k_[3] == 'U')
    fw = sum(v for k_, v in stats.items() if k_[1] != k_[3])
    qw = sum(v for k_, v in stats.items() if k_[2] != k_[3])
    nsat = sum(v for k_, v in stats.items() if k_[3] == 'S')
    check("C1 the flagged tableau agrees with the truth on every concept", fw == 0, f"{fw} wrong of {done}")
    check("C2 the shipped tableau never accepts an unsatisfiable concept; its errors are false UNSAT",
          sfalse_sat == 0, f"{sw} wrong of {done}" + (", each an UNSAT on a satisfiable concept" if sw else ""))
    check("C3 the oracle agrees with the truth on every concept", qw == 0, f"{qw} wrong of {done}")
    check("C4 the sample is not one-sided", 0 < nsat < done, f"{nsat} satisfiable, {done - nsat} unsatisfiable")

    print("\n" + "=" * 76)
    print(f"{sum(RESULTS)}/{len(RESULTS)} checks pass   ({time.time() - t0:.0f}s)")
    print("=" * 76)
    return 0 if all(RESULTS) else 1


if __name__ == '__main__':
    sys.exit(main())
