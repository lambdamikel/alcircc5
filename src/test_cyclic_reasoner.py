"""Adversarial cyclic-pattern test suite for the quasimodel reasoner.

Tests concepts whose satisfiability requires witnesses forming a cycle
through a symmetric relation (PO or DR) or through a PP/PPI inverse pair.
The baseline ``alcircc5_reasoner.py`` is known to wrongly reject such
concepts; the cycle-aware variant ``alcircc5_reasoner_cyclic.py`` should
handle them. The cover-tree tableau serves as an independent oracle.

Each case lists the expected answer and the reason. The cycle-aware
reasoner must match the cover-tree tableau; the baseline reasoner is
allowed to diverge on cases tagged ``baseline_incomplete=True``.
"""

import time

from alcircc5_reasoner import (
    AtomicConcept, NegAtomicConcept, And, Or, Exists, ForAll,
    DR, PO, PP, PPI,
    check_satisfiability as qm_baseline,
)
from alcircc5_reasoner_cyclic import check_satisfiability as qm_cyclic
from cover_tree_tableau import check_satisfiability as ct_tableau


def conj(*xs):
    """Right-fold And over the sequence."""
    r = xs[-1]
    for x in reversed(xs[:-1]):
        r = And(x, r)
    return r


A = AtomicConcept('A')
nA = NegAtomicConcept('A')
C = AtomicConcept('C')
nC = NegAtomicConcept('C')

# All four non-EQ universals mapped to a target concept.
def forall_all(target):
    return conj(ForAll(PO, target), ForAll(DR, target),
                ForAll(PP, target), ForAll(PPI, target))


CASES = [
    # (label, concept, expected_sat, baseline_incomplete, notes)
    (
        'po-loop-depth-2',
        conj(C, Exists(PO, Exists(PO, C)), forall_all(nC)),
        True, True,
        'Classic PO-loop. 2-element model {d,a} with C={d}, PO(d,a). '
        'Baseline rejects (tree-model assumption); cycle-aware accepts.',
    ),
    (
        'dr-loop-depth-2',
        conj(C, Exists(DR, Exists(DR, C)), forall_all(nC)),
        True, True,
        'DR-loop: DR is symmetric, comp(DR, DR) admits EQ. 2-element '
        'model {d, a} with C={d}, DR(d, a). The chain d-DR-a-DR-d closes.',
    ),
    (
        'pp-ppi-cycle',
        conj(C, Exists(PP, Exists(PPI, C)), forall_all(nC)),
        True, True,
        'PP/PPI inverse cycle: (PP, PPI) admits EQ. 2-element model '
        '{d, a} with C={d}, PP(d, a), PPI(a, d) (inverses). The chain '
        'd-PP-a-PPI-d is the cycle-close through EQ.',
    ),
    (
        'ppi-pp-cycle',
        conj(C, Exists(PPI, Exists(PP, C)), forall_all(nC)),
        True, True,
        'PPI then PP: (PP, PPI) with inverse direction. Same principle '
        'as pp-ppi-cycle.',
    ),
    (
        'pp-pp-not-a-cycle',
        conj(C, Exists(PP, Exists(PP, C)), forall_all(nC)),
        False, False,
        'PP-PP is NOT a cycle candidate: comp(PP, PP) = {PP}, no EQ. '
        'PP is irreflexive and transitive, so the chain d-PP-a-PP-b '
        'would force b ∈ C via comp = PP (the only option), but '
        '∀PP.¬C at d requires b ∈ ¬C. Clash. Genuine UNSAT.',
    ),
    (
        'clash-out-to-eq',
        conj(C, Exists(PO, Exists(PO, nC)), forall_all(C)),
        False, False,
        'Universals force c ∈ C through every non-EQ composition; '
        'only EQ remains; strong-EQ forces d = c, yielding '
        'C(d) ∧ ¬C(d). Genuine UNSAT.',
    ),
    (
        'pp-transitivity-depth-2',
        And(ForAll(PP, nC), Exists(PP, Exists(PP, C))),
        False, False,
        'Minimal PP-transitivity UNSAT: d-PP-a-PP-b with comp(PP,PP)={PP} '
        'forces d-PP-b, so ∀PP.¬C at d forces ¬C(b), clashing with C(b). '
        'Pre-fix cover-tree tableau wrongly returned SAT because its '
        'compute_safe did not propagate the universal ∀PP.¬C into '
        'PP-successor types. Both QM reasoners get this right via '
        'disjunctive path-consistency.',
    ),
    (
        'pp-transitivity-depth-3',
        And(ForAll(PP, nC), Exists(PP, Exists(PP, Exists(PP, C)))),
        False, False,
        'Depth-3 variant of pp-transitivity-depth-2. Same principle: '
        'PP is transitive, so d-PP-...-PP-b forces d-PP-b. UNSAT.',
    ),
    (
        'ppi-transitivity-depth-2',
        And(ForAll(PPI, nC), Exists(PPI, Exists(PPI, C))),
        False, False,
        'PPI analogue: comp(PPI,PPI)={PPI}. Same transitivity argument.',
    ),
    (
        'po-loop-with-distinguishing-universal',
        # Adds ∀PO.A that is CONSISTENT with the PO-loop: the loop node a
        # must have A, and d must have A (since a-PO-d returns to d).
        # Model {d, a} with C={d, a}, A={d, a}, PO(d, a). SAT.
        conj(C, Exists(PO, Exists(PO, C)),
             ForAll(PO, A), ForAll(DR, nC), ForAll(PP, nC), ForAll(PPI, nC)),
        True, True,
        'PO-loop variant: d must also be in A (via a-PO-d with ∀PO.A at a'
        ' — but a does not have ∀PO.A; only d does). d-PO-a requires a ∈ A.'
        ' a-PO-d requires d ∈ ? a has no ∀PO, so no constraint. 2-element'
        ' SAT model: {d, a} with C={d, a}(? no wait), A={a, d}, PO(d,a).',
    ),
]


def fmt(b):
    return 'SAT' if b else 'UNSAT'


def run():
    print(f'{"case":<40} {"expected":>8} {"baseline":>10} {"cyclic":>10} {"cover-tree":>12} {"verdict":>10}')
    print('-' * 100)
    errors = []
    for label, concept, expected, baseline_inc, _notes in CASES:
        t0 = time.time()
        is_sat_base, _ = qm_baseline(concept, verbose=False)
        t_base = time.time() - t0
        t0 = time.time()
        is_sat_cyc, _ = qm_cyclic(concept, verbose=False)
        t_cyc = time.time() - t0
        t0 = time.time()
        is_sat_ct, _ = ct_tableau(concept, verbose=False)
        t_ct = time.time() - t0

        # Verdict logic
        cyclic_ok = is_sat_cyc == expected
        ct_ok = is_sat_ct == expected
        baseline_ok = is_sat_base == expected
        baseline_expected_ok = baseline_ok or baseline_inc

        all_ok = cyclic_ok and ct_ok and baseline_expected_ok
        verdict = 'PASS' if all_ok else 'FAIL'
        if not all_ok:
            errors.append((label, expected, is_sat_base, is_sat_cyc, is_sat_ct,
                          baseline_inc))

        print(f'{label:<40} {fmt(expected):>8} {fmt(is_sat_base):>10} '
              f'{fmt(is_sat_cyc):>10} {fmt(is_sat_ct):>12} {verdict:>10}')

    print('-' * 100)
    if errors:
        print(f'\n{len(errors)} FAILURES:')
        for lbl, exp, b, c, ct, b_inc in errors:
            print(f'  {lbl}: expected {fmt(exp)}, baseline={fmt(b)} '
                  f'(allowed wrong: {b_inc}), cyclic={fmt(c)}, ct={fmt(ct)}')
        return 1
    print('\nAll cases pass. Cycle-aware reasoner and cover-tree tableau '
          'agree with expected answers on all adversarial cyclic patterns.')
    return 0


if __name__ == '__main__':
    import sys
    sys.exit(run())
