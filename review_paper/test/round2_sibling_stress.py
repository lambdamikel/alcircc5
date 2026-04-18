#!/usr/bin/env python3
"""Simpler versions of O1/O2 that should finish."""
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
B = AtomicConcept('B'); nB = NegAtomicConcept('B')

tests = [
  # O1a: two DR siblings, one has A and ∀PO.nB, one has B
  ('O1a_DR_sibs_PO_univ', andall(
    Exists(DR, andall(A, ForAll(PO, nB))),
    Exists(DR, B))),
  # O1b: two DR siblings, one forbids B via ∀DR.nB (sibling restriction)
  ('O1b_DR_sib_DR_univ', andall(
    Exists(DR, andall(A, ForAll(DR, nB))),
    Exists(DR, B))),
  # O2a: two PO siblings
  ('O2a_PO_sibs_PO_univ', andall(
    Exists(PO, andall(A, ForAll(PO, nB))),
    Exists(PO, B))),
  # O2b: PO child forbids sibling via DR
  ('O2b_PO_sib_DR_univ', andall(
    Exists(PO, andall(A, ForAll(DR, nB))),
    Exists(DR, B))),
  # Q1: non-singleton composition: (PO,PP) -> {PP,PO}, both maybe bad
  ('Q1_PO_PP_nonsingleton', andall(
    Exists(PO, andall(ForAll(PP, nA))),
    Exists(PP, A))),
  # Q2: PP-PO composition forced inconsistent
  ('Q2_PP_PO_nonsing', andall(
    Exists(PP, andall(B, ForAll(PP, nA), ForAll(PO, nA))),
    Exists(PP, andall(Exists(PO, A))))),
]
mis = []
for name, C in tests:
    t0 = time.time()
    try:
        ctr = ct_sat(C); ct_t = time.time() - t0
        t1 = time.time()
        qmr = qm_sat(C); qm_t = time.time() - t1
    except Exception as e:
        print(f'{name:30s} EXCEPTION: {e}')
        continue
    st = 'OK' if ctr == qmr else '***MISMATCH***'
    print(f'{name:30s} CT={"SAT" if ctr else "UNSAT":5s} QMc={"SAT" if qmr else "UNSAT":5s} {st} [ct:{ct_t:.2f}s qm:{qm_t:.2f}s]')
    if ctr != qmr: mis.append(name)
print(f'\n{len(tests)} run, {len(mis)} mismatches')
if mis: print(f'Mismatches: {mis}')
