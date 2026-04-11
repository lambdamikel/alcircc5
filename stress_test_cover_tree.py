#!/usr/bin/env python3
"""
Cross-validation: run the cover-tree tableau against the stress test suite.

Compares results with the quasimodel reasoner and reports mismatches.
"""

import sys
import time

from alcircc5_reasoner import (
    DR, PO, PP, PPI,
    AtomicConcept, NegAtomicConcept, Top, Bottom,
    And, Or, Exists, ForAll,
    check_satisfiability as check_sat_qm,
)
from cover_tree_tableau import check_satisfiability as check_sat_ct

# ── Concept helpers ──────────────────────────────────────────
A = AtomicConcept('A')
B = AtomicConcept('B')
C = AtomicConcept('C')
D = AtomicConcept('D')
nA = NegAtomicConcept('A')
nB = NegAtomicConcept('B')
nC = NegAtomicConcept('C')
nD = NegAtomicConcept('D')
top = Top()
bot = Bottom()

ROLES = [DR, PO, PP, PPI]
ATOMS = [A, B, C, D]
NEG_ATOMS = [nA, nB, nC, nD]
LITERALS = ATOMS + NEG_ATOMS


def conj(*args):
    result = args[0]
    for c in args[1:]:
        result = And(result, c)
    return result


# ── Test generators (from stress_test.py) ────────────────────

def gen_known_sat():
    tests = []
    for a in ATOMS[:2]:
        tests.append((f"{a}", a, True))
        for R in ROLES:
            tests.append((f"∃{R}.{a}", Exists(R, a), True))
            tests.append((f"∀{R}.{a}", ForAll(R, a), True))
            tests.append((f"∃{R}.{a} ⊓ ∀{R}.{a}",
                          And(Exists(R, a), ForAll(R, a)), True))

    for R1 in ROLES:
        for R2 in ROLES:
            tests.append((f"∃{R1}.A ⊓ ∃{R2}.B",
                          And(Exists(R1, A), Exists(R2, B)), True))

    # Nested
    for R in ROLES:
        tests.append((f"∃{R}.∃{R}.A", Exists(R, Exists(R, A)), True))
        tests.append((f"∃{R}.(A ⊓ B)", Exists(R, And(A, B)), True))

    return tests


def gen_known_unsat():
    tests = []
    tests.append(("⊥", bot, False))
    tests.append(("A ⊓ ¬A", And(A, nA), False))
    tests.append(("∃DR.⊥", Exists(DR, bot), False))

    for R in ROLES:
        tests.append((f"∃{R}.A ⊓ ∀{R}.¬A",
                      And(Exists(R, A), ForAll(R, nA)), False))

    # Cross-role singleton-composition UNSAT
    for a, na in [(A, nA), (B, nB)]:
        tests.append((f"∃PPI.(∀DR.{a}) ⊓ ∃DR.{na}",
                      And(Exists(PPI, ForAll(DR, a)), Exists(DR, na)), False))
        tests.append((f"∃PP.(∀PPI.{a}) ⊓ ∃PPI.{na}",
                      And(Exists(PP, ForAll(PPI, a)), Exists(PPI, na)), False))
        tests.append((f"∃PPI.(∀PP.{a}) ⊓ ∃PP.{na}",
                      And(Exists(PPI, ForAll(PP, a)), Exists(PP, na)), False))

    return tests


def gen_systematic_pairs():
    """All ∃R₁.L₁ ⊓ ∃R₂.L₂ ⊓ ∀R₃.L₃ triples for small R, L."""
    tests = []
    lits = [A, nA]
    for R1 in ROLES:
        for R2 in ROLES:
            for R3 in ROLES:
                for l1 in lits:
                    for l2 in lits:
                        for l3 in lits:
                            c = conj(Exists(R1, l1), Exists(R2, l2), ForAll(R3, l3))
                            name = f"∃{R1}.{l1} ⊓ ∃{R2}.{l2} ⊓ ∀{R3}.{l3}"
                            tests.append((name, c, None))  # unknown expected
    return tests


def gen_adversarial():
    """Concepts designed to stress the cover-tree approach."""
    tests = []

    # The 7 cyclic-model concepts
    tests.append(("∃DR.A ⊓ ∃PP.¬A ⊓ ∀PO.A",
                  conj(Exists(DR, A), Exists(PP, nA), ForAll(PO, A)), True))
    tests.append(("∃PO.A ⊓ ∃PP.¬A ⊓ ∀PO.A",
                  conj(Exists(PO, A), Exists(PP, nA), ForAll(PO, A)), True))
    tests.append(("∃PO.A ⊓ ∃PP.¬B ⊓ ∀DR.A",
                  conj(Exists(PO, A), Exists(PP, nB), ForAll(DR, A)), True))
    tests.append(("∃PO.A ⊓ ∃PP.¬B ⊓ ∀PO.A",
                  conj(Exists(PO, A), Exists(PP, nB), ForAll(PO, A)), True))
    tests.append(("∃PO.A ⊓ ∃PP.¬B ⊓ ∀PP.A",
                  conj(Exists(PO, A), Exists(PP, nB), ForAll(PP, A)), True))
    tests.append(("∃PO.A ⊓ ∃PP.¬B ⊓ ∀PPI.A",
                  conj(Exists(PO, A), Exists(PP, nB), ForAll(PPI, A)), True))
    tests.append(("∃PP.A ⊓ ∃PP.¬A ⊓ ∀PO.A",
                  conj(Exists(PP, A), Exists(PP, nA), ForAll(PO, A)), True))

    # Deeper nesting
    tests.append(("∃PP.(∃PP.(∃PP.A ⊓ ∀DR.B) ⊓ ∀DR.B) ⊓ ∀DR.B",
                  And(Exists(PP, And(Exists(PP, And(Exists(PP, A),
                      ForAll(DR, B))), ForAll(DR, B))), ForAll(DR, B)), True))

    # Mix of all roles
    tests.append(("∃PP.A ⊓ ∃PPI.B ⊓ ∃DR.A ⊓ ∃PO.B",
                  conj(Exists(PP, A), Exists(PPI, B),
                       Exists(DR, A), Exists(PO, B)), True))

    # All 4 roles simultaneously
    for l in [A, nA]:
        tests.append((f"∃PP.A ⊓ ∃PPI.B ⊓ ∃DR.A ⊓ ∃PO.B ⊓ ∀DR.{l}",
                      conj(Exists(PP, A), Exists(PPI, B),
                           Exists(DR, A), Exists(PO, B), ForAll(DR, l)), None))

    # Nested cross-demands
    for R1 in ROLES:
        for R2 in ROLES:
            tests.append((f"∃{R1}.(∃{R2}.A ⊓ ∀{R2}.A)",
                          Exists(R1, And(Exists(R2, A), ForAll(R2, A))), None))

    # DR/PO-only concepts (no PP/PPI tree forced) — tests that the
    # cover-tree tableau handles cross-edge demands without tree expansion
    tests.append(("∃DR.A", Exists(DR, A), True))
    tests.append(("∃PO.A", Exists(PO, A), True))
    tests.append(("∃DR.(∃PO.A)", Exists(DR, Exists(PO, A)), True))
    tests.append(("∃PO.(∃PO.A)", Exists(PO, Exists(PO, A)), True))
    tests.append(("∃DR.(∃DR.A)", Exists(DR, Exists(DR, A)), True))
    tests.append(("∃DR.(∃PO.A ⊓ ∃DR.A)",
                  Exists(DR, conj(Exists(PO, A), Exists(DR, A))), True))

    # DR/PO demand with universals blocking all relations — UNSAT
    # The ∃PO.C witness of the DR-witness must relate to root,
    # but all relations from root force ¬C
    tests.append(("∃DR.(∃PO.C) ⊓ ∀PO.¬C ⊓ ∀DR.¬C ⊓ ∀PPI.¬C ⊓ ∀PP.¬C",
                  conj(Exists(DR, Exists(PO, C)),
                       ForAll(PO, nC), ForAll(DR, nC),
                       ForAll(PPI, nC), ForAll(PP, nC)), False))

    # Same pattern with different filler concept
    tests.append(("∃PO.(∃DR.A) ⊓ ∀PO.¬A ⊓ ∀DR.¬A ⊓ ∀PPI.¬A ⊓ ∀PP.¬A",
                  conj(Exists(PO, Exists(DR, A)),
                       ForAll(PO, nA), ForAll(DR, nA),
                       ForAll(PPI, nA), ForAll(PP, nA)), False))

    # Deeper: ∃DR.(∃DR.(∃PO.A)) — 3 levels of cross-edge demands
    tests.append(("∃DR.(∃DR.(∃PO.A))",
                  Exists(DR, Exists(DR, Exists(PO, A))), True))

    return tests


import random


def gen_random(depth, count, seed=42):
    """Generate random concepts of given depth."""
    rng = random.Random(seed)
    tests = []

    def rand_concept(d):
        if d == 0:
            return rng.choice(LITERALS[:4])
        choice = rng.randint(0, 4)
        if choice == 0:
            return And(rand_concept(d - 1), rand_concept(d - 1))
        elif choice == 1:
            return Or(rand_concept(d - 1), rand_concept(d - 1))
        elif choice == 2:
            R = rng.choice(ROLES)
            return Exists(R, rand_concept(d - 1))
        elif choice == 3:
            R = rng.choice(ROLES)
            return ForAll(R, rand_concept(d - 1))
        else:
            return rng.choice(LITERALS[:4])

    for i in range(count):
        c = rand_concept(depth)
        tests.append((f"rand_d{depth}_{i}", c, None))

    return tests


# ── Main test runner ─────────────────────────────────────────

def run_cross_validation(timeout_per_test=5.0):
    print("=" * 70)
    print("COVER-TREE TABLEAU CROSS-VALIDATION")
    print("=" * 70)

    categories = [
        ("Known SAT", gen_known_sat()),
        ("Known UNSAT", gen_known_unsat()),
        ("Adversarial", gen_adversarial()),
        ("Systematic triples", gen_systematic_pairs()),
        ("Random depth-2", gen_random(2, 200)),
        ("Random depth-3", gen_random(3, 100, seed=123)),
    ]

    total = 0
    correct = 0
    mismatches = 0
    ct_errors = 0
    qm_errors = 0

    for cat_name, tests in categories:
        cat_total = len(tests)
        cat_correct = 0
        cat_mismatch = 0
        cat_errors = []
        t_cat = time.time()

        for name, concept, expected in tests:
            total += 1
            try:
                ct_sat, ct_info = check_sat_ct(concept)
            except Exception as e:
                ct_sat = None
                ct_errors += 1
                cat_errors.append((name, f"CT ERROR: {e}"))
                continue

            try:
                qm_sat, qm_info = check_sat_qm(concept)
            except Exception as e:
                qm_sat = None
                qm_errors += 1
                cat_errors.append((name, f"QM ERROR: {e}"))
                continue

            if ct_sat is None or qm_sat is None:
                continue

            # Check against expected (if known)
            if expected is not None:
                if ct_sat != expected:
                    cat_errors.append((name, f"CT wrong: got {'SAT' if ct_sat else 'UNSAT'}, "
                                            f"expected {'SAT' if expected else 'UNSAT'}"))
                elif ct_sat == expected:
                    cat_correct += 1
                    correct += 1
            else:
                # No expected — just check CT matches QM
                if ct_sat == qm_sat:
                    cat_correct += 1
                    correct += 1
                else:
                    cat_mismatch += 1
                    mismatches += 1
                    cat_errors.append((name,
                        f"MISMATCH: CT={'SAT' if ct_sat else 'UNSAT'}, "
                        f"QM={'SAT' if qm_sat else 'UNSAT'}"))

        elapsed = time.time() - t_cat
        print(f"\n  [{cat_name}] {cat_total} tests, {elapsed:.1f}s")
        print(f"    Correct/matching: {cat_correct}")
        if cat_errors:
            print(f"    Errors ({len(cat_errors)}):")
            for name, msg in cat_errors[:10]:
                print(f"      {name}: {msg}")
            if len(cat_errors) > 10:
                print(f"      ... and {len(cat_errors) - 10} more")

    print(f"\n{'=' * 70}")
    print(f"OVERALL: {total} tests")
    print(f"  Correct/matching: {correct}")
    print(f"  Mismatches (CT ≠ QM): {mismatches}")
    print(f"  CT errors: {ct_errors}")
    print(f"  QM errors: {qm_errors}")
    print(f"{'=' * 70}")

    return mismatches == 0 and ct_errors == 0


if __name__ == '__main__':
    success = run_cross_validation()
    sys.exit(0 if success else 1)
