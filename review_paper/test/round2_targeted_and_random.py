#!/usr/bin/env python3
"""Round-2 final attacks: targeted + random sampling."""
import sys
import time
import random
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'src'))

import cover_tree_tableau as ct
import alcircc5_reasoner as qm
from alcircc5_reasoner import (
    DR, PO, PP, PPI,
    AtomicConcept, NegAtomicConcept, Top, Bottom,
    And, Or, Exists, ForAll, Concept,
)

def qm_sat(C, cycle_close=True):
    r, _ = qm.check_satisfiability(C, cycle_close=cycle_close)
    return r

def ct_sat(C):
    r, _ = ct.check_satisfiability(C)
    return r

def andall(*xs):
    r = xs[0]
    for x in xs[1:]:
        r = And(r, x)
    return r

def orall(*xs):
    r = xs[0]
    for x in xs[1:]:
        r = Or(r, x)
    return r

A = AtomicConcept('A'); nA = NegAtomicConcept('A')
B = AtomicConcept('B'); nB = NegAtomicConcept('B')
C_ = AtomicConcept('C'); nC = NegAtomicConcept('C')
D = AtomicConcept('D'); nD = NegAtomicConcept('D')

# ══════════════════════════════════════════════════════════════
# Round-2 final attacks
# ══════════════════════════════════════════════════════════════

tests = []

# -- G-family: Triple cross-edge demands with pairwise constraints --
# G1: type has ∃DR.A, ∃PO.B, ∃DR.C where no pair of witnesses works
# (forcing pairwise constraints in sibling check).
tests.append(('G1_triple_cross', andall(
    Exists(DR, A), Exists(PO, B), Exists(DR, C_),
    ForAll(PO, orall(nB, nA)),  # restricts cross-sibling relation PO
)))

# G2: Triple DR where DR/PO between DR-sibs would force clash via comp
# comp(DR, DR) ∩ {DR,PO} = {DR, PO} — usually always OK, so no clash expected.
tests.append(('G2_triple_DR', andall(
    Exists(DR, A), Exists(DR, B), Exists(DR, C_),
    A, nB, nC, ForAll(DR, Top),  # no pairwise constraint, should be SAT
)))

# -- H-family: 4-chain potential gaps --
# H1: grandchild has ∃DR.D with ∀PP.∀DR.¬D propagating from root.
tests.append(('H1_4chain_DRpropag', andall(
    A,
    ForAll(PP, ForAll(DR, nD)),
    Exists(PP, Exists(PP, Exists(DR, D))),
)))

# H2: 4-chain via PPI then DR then PPI
tests.append(('H2_4chain_PPI_DR_PPI', andall(
    A,
    ForAll(PPI, ForAll(DR, ForAll(PPI, nD))),
    Exists(PPI, Exists(DR, Exists(PPI, D))),
)))

# H3: grandparent-grandchild via PP; grandparent ∀DR.nB, grandchild ∃DR.B
tests.append(('H3_4chain_crossinside', andall(
    A,
    ForAll(PP, Exists(PP, andall(
        Exists(DR, B),
        nA,
    ))),
    ForAll(PP, ForAll(DR, nB)),  # transitive should propagate
)))

# -- I-family: stress sibling backtracking --
# I1: parent has ∃DR.A ⊓ ∃PO.A ⊓ ∃DR.nA
tests.append(('I1_sibling_backtrack', andall(
    Exists(DR, A), Exists(PO, A), Exists(DR, nA),
)))

# I2: ∃DR.A, ∃DR.B, ∃DR.C_, forcing three distinct sibs (maybe?)
tests.append(('I2_three_DRdistinct', andall(
    Exists(DR, andall(A, nB, nC)),
    Exists(DR, andall(nA, B, nC)),
    Exists(DR, andall(nA, nB, C_)),
)))

# -- J-family: EQ-admitting close boundary cases --
# J1: chain where closing via EQ is NECESSARY (cyclic model)
tests.append(('J1_EQclose_necessary', andall(
    A,
    Exists(PP, Exists(PPI, Exists(PP, A))),  # cycle
    ForAll(PP, ForAll(PPI, ForAll(PP, nA))),  # transitive reflection
)))

# J2: chain where EQ close is forbidden by nA at root + A at grandchild
tests.append(('J2_EQclose_blocked', andall(
    nA,
    ForAll(PP, ForAll(PPI, A)),  # forces A at pos after PP∘PPI
)))

# -- K-family: random generation --
def rand_concept(depth, atoms=['A', 'B', 'C'], roles=[DR, PO, PP, PPI], p_atom=0.4):
    if depth == 0 or random.random() < p_atom:
        a = random.choice(atoms)
        if random.random() < 0.5:
            return AtomicConcept(a)
        return NegAtomicConcept(a)
    kind = random.random()
    if kind < 0.2:
        return And(rand_concept(depth-1, atoms, roles), rand_concept(depth-1, atoms, roles))
    elif kind < 0.4:
        return Or(rand_concept(depth-1, atoms, roles), rand_concept(depth-1, atoms, roles))
    elif kind < 0.7:
        return Exists(random.choice(roles), rand_concept(depth-1, atoms, roles))
    else:
        return ForAll(random.choice(roles), rand_concept(depth-1, atoms, roles))


print('=' * 72)
print('ROUND 2 FINAL ATTACKS — cover-tree tableau vs QMc')
print('=' * 72)
mismatches = []
for name, C in tests:
    t0 = time.time()
    try:
        ct_r = ct_sat(C)
    except Exception as e:
        print(f'{name:30s} CT EXCEPTION: {e}')
        continue
    t1 = time.time() - t0
    try:
        qm_r = qm_sat(C, cycle_close=True)
    except Exception as e:
        print(f'{name:30s} QMc EXCEPTION: {e}')
        continue
    t2 = time.time() - t0 - t1
    status = 'OK ' if ct_r == qm_r else '***MISMATCH***'
    print(f'{name:30s} CT={"SAT" if ct_r else "UNSAT":5s} QMc={"SAT" if qm_r else "UNSAT":5s} {status} '
          f'[{t1:.2f}s / {t2:.2f}s]')
    if ct_r != qm_r:
        mismatches.append(name)

print()
print('=' * 72)
print('RANDOM ATTACK: 60 concepts, depth 3-4, 2-3 atoms')
print('=' * 72)
random.seed(424242)
n_random = 60
rand_mismatches = []
for i in range(n_random):
    depth = random.choice([3, 4])
    n_atoms = random.choice([2, 3])
    atoms = ['A', 'B', 'C'][:n_atoms]
    C = rand_concept(depth, atoms=atoms)
    try:
        ct_r = ct_sat(C)
        qm_r = qm_sat(C, cycle_close=True)
        if ct_r != qm_r:
            rand_mismatches.append((i, C, ct_r, qm_r))
            print(f'  [{i:3d}] MISMATCH: CT={ct_r} QMc={qm_r}  C={C}')
    except Exception as e:
        print(f'  [{i:3d}] EXCEPTION: {type(e).__name__}: {e}')
        continue
    if i % 10 == 9:
        print(f'  ...{i+1}/{n_random} done, {len(rand_mismatches)} mismatches so far')

print()
print('=' * 72)
print('FINAL VERDICT')
print('=' * 72)
print(f'Targeted attacks: {len(tests)} run, {len(mismatches)} mismatches')
print(f'Random attacks:   {n_random} run, {len(rand_mismatches)} mismatches')
if mismatches:
    print(f'Targeted mismatches: {mismatches}')
if rand_mismatches:
    print('Random mismatches:')
    for i, C, ctr, qmr in rand_mismatches:
        print(f'  [{i}] CT={ctr} QMc={qmr}  {C}')
