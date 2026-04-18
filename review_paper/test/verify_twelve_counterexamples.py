#!/usr/bin/env python3
"""Verify the 12 counterexamples from round 1 all pass now."""
import sys, time, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'src'))
import cover_tree_tableau as ct
import alcircc5_reasoner as qm
from alcircc5_reasoner import (
    DR, PO, PP, PPI,
    AtomicConcept, NegAtomicConcept,
    And, Or, Exists, ForAll,
)

def qm_sat(C): return qm.check_satisfiability(C, cycle_close=True)[0]
def ct_sat(C): return ct.check_satisfiability(C)[0]
def andall(*xs):
    r = xs[0]
    for x in xs[1:]: r = And(r, x)
    return r

A = AtomicConcept('A'); nA = NegAtomicConcept('A')

# The 4x4 grid: ∃R1.∃R2.A ⊓ ⊓_{R ∈ R1∘R2} ∀R.¬A
# (R2 ≠ inv(R1); diagonal excluded). 12 cells.
BASES = [DR, PO, PP, PPI]
INV = {DR: DR, PO: PO, PP: PPI, PPI: PP}
COMP = {
    (DR,DR): {DR,PO,PP,PPI}, (DR,PO): {DR,PO,PP}, (DR,PP): {DR,PO,PP}, (DR,PPI): {DR},
    (PO,DR): {DR,PO,PPI}, (PO,PO): {DR,PO,PP,PPI}, (PO,PP): {PP,PO}, (PO,PPI): {DR,PO,PPI},
    (PP,DR): {DR}, (PP,PO): {DR,PO,PP}, (PP,PP): {PP}, (PP,PPI): {DR,PO,PP,PPI,'EQ'},
    (PPI,DR): {DR,PO,PPI}, (PPI,PO): {PO,PPI}, (PPI,PP): {DR,PO,PP,PPI,'EQ'}, (PPI,PPI): {PPI},
}
NAMES = {DR:'DR', PO:'PO', PP:'PP', PPI:'PPI'}

print('Checking the 4x4 grid of 12 structural counterexamples from round 1:')
print(f'{"R1":4s}{"R2":4s}{"CT":6s}{"QMc":6s}{"agree?"}')
n = 0; mis = 0
for R1 in BASES:
    for R2 in BASES:
        if R2 == INV[R1]:
            continue
        # composition members (excluding EQ — can't use as top-level ∀)
        comp_set = [r for r in COMP[(R1,R2)] if r != 'EQ']
        if not comp_set: continue
        forall_part = None
        for R in comp_set:
            f = ForAll(R, nA)
            forall_part = f if forall_part is None else And(forall_part, f)
        C = andall(Exists(R1, Exists(R2, A)), forall_part)
        ct_r = ct_sat(C); qm_r = qm_sat(C)
        ok = 'YES' if ct_r == qm_r else '***NO***'
        print(f'{NAMES[R1]:4s}{NAMES[R2]:4s}{str(ct_r):6s}{str(qm_r):6s}{ok}')
        n += 1
        if ct_r != qm_r: mis += 1

print(f'\n{n} tests, {mis} mismatches')
