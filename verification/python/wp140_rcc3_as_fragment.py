#!/usr/bin/env python3
"""
wp140 -- ALCI_RCC3 as a syntactic fragment of ALCI_RCC5 (2026-11-11)
====================================================================

Question (Michael Wessel): how does the coarser logic ALCI_RCC3 of the 2003
report relate to the fragments discussed around the poset bridge?

RCC3 merges PO, PP and PPI into ONE ("overlapping but not equal") and keeps DR
and EQ. Read ONE as a defined role of RCC5 (report7, section 2):

    EX ONE.C  :=  EX PO.C | EX PP.C | EX PPI.C
    ALL ONE.C :=  ALL PO.C & ALL PP.C & ALL PPI.C

CLAIM. An ALCI_RCC3 concept is satisfiable (RCC3 composition-table semantics,
strong EQ) iff its translation is satisfiable in ALCI_RCC5.

  =>  an RCC3 structure is any symmetric labelling of the distinct pairs by
      DR / ONE (the RCC3 table constrains no triple of distinct elements).
      Relabel ONE as PO: every {PO,DR}-labelled complete graph is closed under
      the RCC5 table (part A), and ONE-witnesses are PO-witnesses.
  <=  merge PO, PP, PPI of an RCC5 model into ONE.

So ALCI_RCC3 -- decided in 2003 through two-variable logic with equality -- is,
in the sense of the poset bridge, a decided slice of ALCI_RCC5, and one in
which an ALL PO restriction can change the answer (part D).

This is a probe, not a proof: A is exhaustive for n <= 5; C compares a brute
force over all RCC3 structures on <= 3 points with the reference reasoner on
the translation, and re-checks every model the reasoner returns after merging.
"""
import itertools, os, random, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'src'))
from alcircc5_reasoner import (DR, PO, PP, PPI, COMP, INV, AtomicConcept as At,
                               NegAtomicConcept as Nat, And, Or, Exists, ForAll)
from midelora_tableau import check

ok_all = True
def report(name, ok, detail=''):
    global ok_all
    ok_all &= bool(ok)
    print('  [%s] %s%s' % ('PASS' if ok else 'FAIL', name, ('  -- ' + detail) if detail else ''))

# ---- A: every {PO,DR}-labelled complete graph is closed under the RCC5 table
print('Part A -- {PO,DR}-labelled graphs are RCC5 networks')
bad = 0; tot = 0
for n in (3, 4, 5):
    pairs = list(itertools.combinations(range(n), 2))
    for lab in itertools.product((PO, DR), repeat=len(pairs)):
        tot += 1
        rho = {}
        for (i, j), r in zip(pairs, lab):
            rho[i, j] = r; rho[j, i] = INV[r]
        for x, y, z in itertools.permutations(range(n), 3):
            if rho[x, z] not in COMP[(rho[x, y], rho[y, z])]:
                bad += 1; break
report('all %d labellings on 3..5 points are composition-closed' % tot, bad == 0, '%d violations' % bad)

# ---- RCC3 concepts: ('at',A) ('nat',A) ('and',c,d) ('or',c,d) ('ex',r,c) ('all',r,c), r in {'ONE','DR'}
def tr(c):
    t = c[0]
    if t == 'at': return At(c[1])
    if t == 'nat': return Nat(c[1])
    if t == 'and': return And(tr(c[1]), tr(c[2]))
    if t == 'or': return Or(tr(c[1]), tr(c[2]))
    d = tr(c[2])
    if t == 'ex':
        return Exists(DR, d) if c[1] == 'DR' else Or(Exists(PO, d), Or(Exists(PP, d), Exists(PPI, d)))
    return ForAll(DR, d) if c[1] == 'DR' else And(ForAll(PO, d), And(ForAll(PP, d), ForAll(PPI, d)))

def sat3(c, x, n, one, val):
    t = c[0]
    if t == 'at': return c[1] in val[x]
    if t == 'nat': return c[1] not in val[x]
    if t == 'and': return sat3(c[1], x, n, one, val) and sat3(c[2], x, n, one, val)
    if t == 'or': return sat3(c[1], x, n, one, val) or sat3(c[2], x, n, one, val)
    ys = [y for y in range(n) if y != x and ((frozenset((x, y)) in one) == (c[1] == 'ONE'))]
    if t == 'ex': return any(sat3(c[2], y, n, one, val) for y in ys)
    return all(sat3(c[2], y, n, one, val) for y in ys)

def brute3(c, maxn=3, atoms=('A', 'B')):
    subs = [frozenset(s) for k in range(len(atoms) + 1) for s in itertools.combinations(atoms, k)]
    for n in range(1, maxn + 1):
        pairs = [frozenset(p) for p in itertools.combinations(range(n), 2)]
        for k in range(len(pairs) + 1):
            for one in itertools.combinations(pairs, k):
                one = set(one)
                for val in itertools.product(subs, repeat=n):
                    if sat3(c, 0, n, one, val): return True
    return False

def rnd(depth, rng):
    if depth == 0 or rng.random() < 0.25:
        return (rng.choice(('at', 'nat')), rng.choice('AB'))
    t = rng.choice(('and', 'and', 'or', 'ex', 'ex', 'all', 'all'))
    if t in ('and', 'or'): return (t, rnd(depth - 1, rng), rnd(depth - 1, rng))
    return (t, rng.choice(('ONE', 'DR')), rnd(depth - 1, rng))

# ---- C: random concepts
print('Part C -- random ALCI_RCC3 concepts against the translation')
rng = random.Random(20261111)
t0 = time.time(); n_sat = n_unsat = n_unk = 0; wrong = 0; merged_bad = 0
for _ in range(400):
    c = rnd(3, rng)
    r = check(tr(c), max_nodes=5, time_limit=20)
    b = brute3(c)
    if r.verdict == 'SAT':
        n_sat += 1
        labels, rel = r.model            # labels: list of sets; rel: matrix; node 0 is the root
        m = len(labels)
        one = {frozenset((u, v)) for u in range(m) for v in range(u + 1, m) if rel[u][v] in (PO, PP, PPI)}
        val = [frozenset(a.name for a in labels[v] if isinstance(a, At)) for v in range(m)]
        if not sat3(c, 0, m, one, val): merged_bad += 1
    elif r.verdict == 'UNSAT':
        n_unsat += 1
        if b: wrong += 1
    else:
        n_unk += 1
report('no RCC3 model on <= 3 points for a concept whose translation is refuted', wrong == 0, '%d contradictions' % wrong)
report('every model of a translation, with PO/PP/PPI merged, is an RCC3 model of the concept', merged_bad == 0,
       '%d failures; %d SAT, %d UNSAT, %d UNKNOWN, %.0fs' % (merged_bad, n_sat, n_unsat, n_unk, time.time() - t0))

# ---- D: in this slice an ALL PO restriction changes the answer
print('Part D -- ALL PO is not vacuous in the RCC3 slice')
A = At('A'); nA = Nat('A')
c1 = And(Or(Exists(PO, A), Or(Exists(PP, A), Exists(PPI, A))), And(ForAll(PO, nA), And(ForAll(PP, nA), ForAll(PPI, nA))))
c2 = And(Or(Exists(PO, A), Or(Exists(PP, A), Exists(PPI, A))), And(ForAll(PP, nA), ForAll(PPI, nA)))
r1 = check(c1, max_nodes=4); r2 = check(c2, max_nodes=4)
report('EX ONE.A & ALL ONE.~A is unsatisfiable', r1.verdict == 'UNSAT', r1.verdict)
report('with its ALL PO conjunct erased it is satisfiable', r2.verdict == 'SAT', r2.verdict)

print('\nALL PASS' if ok_all else '\nFAILURES')
sys.exit(0 if ok_all else 1)
