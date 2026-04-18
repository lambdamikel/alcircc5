#!/usr/bin/env python3
"""Run each test with per-test timeout."""
import sys, time, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'src'))
import cover_tree_tableau as ct
import alcircc5_reasoner as qm
from alcircc5_reasoner import (
    DR, PO, PP, PPI,
    AtomicConcept, NegAtomicConcept,
    And, Or, Exists, ForAll,
)

def qm_sat(C):
    r, _ = qm.check_satisfiability(C, cycle_close=True); return r
def ct_sat(C):
    r, _ = ct.check_satisfiability(C); return r
def andall(*xs):
    r = xs[0]
    for x in xs[1:]: r = And(r, x)
    return r

A = AtomicConcept('A'); nA = NegAtomicConcept('A')
B = AtomicConcept('B'); nB = NegAtomicConcept('B')
C_ = AtomicConcept('C'); nC = NegAtomicConcept('C')
D = AtomicConcept('D'); nD = NegAtomicConcept('D')

# Pick the test number from argv
idx = int(sys.argv[1])
tests = [
  ('L1_4chain_3universal', andall(
    ForAll(PP, ForAll(DR, ForAll(PP, nA))),
    Exists(PP, Exists(DR, Exists(PP, A))))),
  ('L2_4chain_mixed', andall(
    ForAll(PPI, ForAll(DR, ForAll(PP, nA))),
    Exists(PPI, Exists(DR, Exists(PP, A))))),
  ('L3_4chain_EQclose_ok', andall(
    A, Exists(PP, Exists(PPI, Exists(PP, Exists(PPI, A)))))),
  ('M1_tree_cross_parent', andall(
    Exists(PP, A), Exists(DR, B))),
  ('M3_gc_sib_forall', andall(
    ForAll(PP, ForAll(DR, nA)),
    Exists(PP, Exists(DR, A)))),
  ('N1_EQ_admit_blocked', andall(
    A, Exists(PP, Exists(PPI, nA)))),
  ('N2_EQ_admit_both_A', andall(
    A, Exists(PP, Exists(PPI, A)))),
  ('O1_sib_univ', andall(
    Exists(DR, andall(A, ForAll(PO, nB), ForAll(DR, nB))),
    Exists(DR, andall(B, ForAll(PO, nA), ForAll(DR, nA))))),
  ('O2_PO_sibs_univ', andall(
    Exists(PO, andall(A, ForAll(DR, nB), ForAll(PO, nB))),
    Exists(PO, andall(B, ForAll(DR, nA), ForAll(PO, nA))))),
  ('P1_chain_plus_forall', andall(
    Exists(PP, Exists(DR, A)),
    ForAll(PP, ForAll(DR, nA)))),
  ('P2_PP_PP_DR', andall(
    Exists(PP, Exists(PP, Exists(DR, A))),
    ForAll(PP, ForAll(PP, ForAll(DR, nA))))),
  ('P3_DR_PP', andall(
    Exists(DR, Exists(PP, A)),
    ForAll(DR, ForAll(PP, nA)))),
  ('P4_PO_PPI', andall(
    Exists(PO, Exists(PPI, A)),
    ForAll(PO, ForAll(PPI, nA)))),
]
name, C = tests[idx]
t0 = time.time()
ct_r = ct_sat(C); ct_t = time.time() - t0
t1 = time.time()
qm_r = qm_sat(C); qm_t = time.time() - t1
status = 'OK' if ct_r == qm_r else '***MISMATCH***'
print(f'{idx:2d} {name:30s} CT={"SAT" if ct_r else "UNSAT":5s} QMc={"SAT" if qm_r else "UNSAT":5s} {status} [ct:{ct_t:.2f}s qm:{qm_t:.2f}s]')
