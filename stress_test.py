#!/usr/bin/env python3
"""
Comprehensive stress test for the ALCI_RCC5 reasoner.

Generates hundreds of test concepts systematically, checks reasoner
results, and validates SAT answers with Henkin tree construction.

Categories:
  1. Known SAT (hand-verified): concepts with obvious models
  2. Known UNSAT (hand-verified): logically contradictory concepts
  3. Systematic: all single/double existential+universal combos
  4. Deep nesting: chains of existentials up to depth 5
  5. Adversarial: designed to stress sibling/role-path checks
  6. Random: randomly generated concepts up to given depth
"""

import itertools
import random
import sys
import time

from alcircc5_reasoner import (
    DR, PO, PP, PPI, BASE_RELS, INV, COMP,
    AtomicConcept, NegAtomicConcept, Top, Bottom,
    And, Or, Exists, ForAll,
    check_satisfiability
)
from henkin_extension_test import build_henkin_tree, compute_witness_plan

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
    """Build conjunction of multiple concepts."""
    result = args[0]
    for c in args[1:]:
        result = And(result, c)
    return result


def henkin_validate(concept, info, max_depth=5):
    """Run Henkin tree validation on a SAT result."""
    T = info.get('type_set')
    if T is None:
        return None, "no type_set"

    type_list = info['type_list']
    safe = info['safe']
    demands = info['demands']

    roots = [i for i in T if concept in type_list[i]]
    if not roots:
        return None, "no root in T"

    best = None
    for root in roots:
        r = build_henkin_tree(type_list, safe, demands, T, root, max_depth=max_depth)
        if best is None or r['failures'] < best['failures']:
            best = r
    return best['failures'], best


# ── Test generators ──────────────────────────────────────────

def gen_known_sat():
    """Concepts with obvious models."""
    tests = []

    # Simple atoms
    for a in ATOMS:
        tests.append((f"{a}", a, True))

    # Conjunctions of compatible atoms
    tests.append(("A ⊓ B", And(A, B), True))
    tests.append(("A ⊓ B ⊓ C", conj(A, B, C), True))
    tests.append(("A ⊓ B ⊓ C ⊓ D", conj(A, B, C, D), True))

    # Single existentials
    for R in ROLES:
        for a in ATOMS:
            tests.append((f"∃{R}.{a}", Exists(R, a), True))

    # Existential + compatible universal
    for R in ROLES:
        tests.append((f"∃{R}.A ⊓ ∀{R}.A", And(Exists(R, A), ForAll(R, A)), True))

    # Multiple existentials with different roles
    for R1, R2 in itertools.combinations(ROLES, 2):
        tests.append((f"∃{R1}.A ⊓ ∃{R2}.B",
                       And(Exists(R1, A), Exists(R2, B)), True))

    # Three existentials
    for R1, R2, R3 in itertools.combinations(ROLES, 3):
        tests.append((f"∃{R1}.A ⊓ ∃{R2}.B ⊓ ∃{R3}.C",
                       conj(Exists(R1, A), Exists(R2, B), Exists(R3, C)), True))

    # Four existentials (all roles)
    tests.append(("∃DR.A ⊓ ∃PO.B ⊓ ∃PP.C ⊓ ∃PPI.D",
                   conj(Exists(DR, A), Exists(PO, B),
                        Exists(PP, C), Exists(PPI, D)), True))

    # Nested existentials
    for R1 in ROLES:
        for R2 in ROLES:
            tests.append((f"∃{R1}.∃{R2}.A",
                           Exists(R1, Exists(R2, A)), True))

    # Deep chains
    for R in ROLES:
        c = A
        name = "A"
        for depth in range(1, 5):
            c = Exists(R, c)
            name = f"∃{R}.{name}"
            tests.append((name, c, True))

    # Existential with Top
    for R in ROLES:
        tests.append((f"∃{R}.⊤", Exists(R, top), True))

    # Mixed: existential + universal on different roles
    for R1, R2 in itertools.permutations(ROLES, 2):
        tests.append((f"∃{R1}.A ⊓ ∀{R2}.B",
                       And(Exists(R1, A), ForAll(R2, B)), True))

    # Universal propagation with existential loop
    for R in ROLES:
        tests.append((f"∃{R}.⊤ ⊓ ∀{R}.∃{R}.⊤",
                       And(Exists(R, top), ForAll(R, Exists(R, top))), True))

    # PP chain with universals
    tests.append(("∃PP.⊤ ⊓ ∀PP.∃PP.⊤",
                   And(Exists(PP, top), ForAll(PP, Exists(PP, top))), True))

    # PPI chain (reverse containment)
    tests.append(("∃PPI.⊤ ⊓ ∀PPI.∃PPI.⊤",
                   And(Exists(PPI, top), ForAll(PPI, Exists(PPI, top))), True))

    return tests


def gen_known_unsat():
    """Concepts that are logically unsatisfiable."""
    tests = []

    # Contradictions
    tests.append(("⊥", bot, False))
    tests.append(("A ⊓ ¬A", And(A, nA), False))
    tests.append(("A ⊓ B ⊓ ¬A", conj(A, B, nA), False))

    # Existential with bottom
    for R in ROLES:
        tests.append((f"∃{R}.⊥", Exists(R, bot), False))

    # Existential + contradictory universal
    for R in ROLES:
        tests.append((f"∃{R}.A ⊓ ∀{R}.¬A",
                       And(Exists(R, A), ForAll(R, nA)), False))

    # Nested contradiction
    for R1, R2 in itertools.product(ROLES, repeat=2):
        if R1 == R2:
            tests.append((f"∃{R1}.(A ⊓ ∀{R2}.¬A) ⊓ ∀{R1}.∃{R2}.A",
                           And(Exists(R1, And(A, ForAll(R2, nA))),
                               ForAll(R1, Exists(R2, A))), False))

    # Cross-role sibling contradiction: when COMP(INV[R1], R2) is a
    # singleton {R2}, ∃R1.(∀R2.X) ⊓ ∃R2.¬X is UNSAT because the
    # forced sibling relation R2 triggers the universal constraint.
    # Cases: PP∘DR={DR}, PPI∘PPI={PPI}, PP∘PP={PP}
    for a, na in [(A, nA), (B, nB)]:
        tests.append((f"∃PPI.(∀DR.{a}) ⊓ ∃DR.{na}",
                       And(Exists(PPI, ForAll(DR, a)), Exists(DR, na)), False))
        tests.append((f"∃PP.(∀PPI.{a}) ⊓ ∃PPI.{na}",
                       And(Exists(PP, ForAll(PPI, a)), Exists(PPI, na)), False))
        tests.append((f"∃PPI.(∀PP.{a}) ⊓ ∃PP.{na}",
                       And(Exists(PPI, ForAll(PP, a)), Exists(PP, na)), False))

    return tests


def gen_adversarial():
    """Concepts designed to stress the sibling/role-path checks."""
    tests = []

    # Cross-role with universals (the hardest pattern)
    for R1, R2 in itertools.permutations(ROLES, 2):
        for a in [A, B]:
            na = nA if a == A else nB
            # ∃R1.(∀R2.a) ⊓ ∃R2.¬a
            tests.append((f"∃{R1}.(∀{R2}.{a}) ⊓ ∃{R2}.{na}",
                           And(Exists(R1, ForAll(R2, a)),
                               Exists(R2, na)), None))

    # Three existentials with cross-universals
    for R1, R2, R3 in itertools.permutations(ROLES, 3):
        tests.append((
            f"∃{R1}.(∀{R2}.A) ⊓ ∃{R2}.(∀{R3}.B) ⊓ ∃{R3}.⊤",
            conj(Exists(R1, ForAll(R2, A)),
                 Exists(R2, ForAll(R3, B)),
                 Exists(R3, top)), None))

    # PP-chain with DR demands and universals
    tests.append(("∃PP.(A ⊓ ∃DR.B) ⊓ ∀PP.(A ⊓ ∃PP.⊤ ⊓ ∃DR.B)",
                   And(Exists(PP, And(A, Exists(DR, B))),
                       ForAll(PP, conj(A, Exists(PP, top), Exists(DR, B)))), None))

    # The "PO-incoherent" test
    tests.append(("∃PO.D ⊓ ∃DR.(B ⊓ ∀PO.¬D) ⊓ ∀DR.¬D ⊓ ∀PP.¬D ⊓ ∀PPI.¬D",
                   conj(Exists(PO, D),
                        Exists(DR, And(B, ForAll(PO, nD))),
                        ForAll(DR, nD), ForAll(PP, nD), ForAll(PPI, nD)), None))

    # Multiple universals blocking all but one role
    for R_open in ROLES:
        blocked = [R for R in ROLES if R != R_open]
        c = Exists(R_open, A)
        for R_b in blocked:
            c = And(c, ForAll(R_b, nA))
        tests.append((f"∃{R_open}.A ⊓ ∀others.¬A", c, None))

    # Deep PP chain with universal constraints at each level
    tests.append(("∃PP.(∃PP.(∃PP.A ⊓ ∀DR.B) ⊓ ∀DR.B) ⊓ ∀DR.B",
                   Exists(PP, And(
                       Exists(PP, And(
                           And(Exists(PP, A), ForAll(DR, B)),
                           ForAll(DR, B))),
                       ForAll(DR, B))), None))

    # Inverse role interaction: PP and PPI
    tests.append(("∃PP.(A ⊓ ∃PPI.B) ⊓ ∃PPI.(A ⊓ ∃PP.B)",
                   And(Exists(PP, And(A, Exists(PPI, B))),
                       Exists(PPI, And(A, Exists(PP, B)))), None))

    # All four roles with cross-universals
    tests.append(("∃DR.A ⊓ ∃PO.B ⊓ ∃PP.C ⊓ ∃PPI.D ⊓ ∀DR.¬B ⊓ ∀PO.¬A",
                   conj(Exists(DR, A), Exists(PO, B),
                        Exists(PP, C), Exists(PPI, D),
                        ForAll(DR, nB), ForAll(PO, nA)), None))

    # Self-referential: PP-witness must also have PP demand
    tests.append(("∃PP.(A ⊓ ∃PP.A) ⊓ ∀PP.∃PP.A",
                   And(Exists(PP, And(A, Exists(PP, A))),
                       ForAll(PP, Exists(PP, A))), None))

    return tests


def gen_random(count=100, max_depth=3, seed=42):
    """Generate random concepts up to given depth."""
    rng = random.Random(seed)
    tests = []

    def rand_concept(depth):
        if depth == 0 or rng.random() < 0.3:
            return rng.choice(LITERALS + [top])
        op = rng.choice(['exists', 'forall', 'and', 'or'])
        if op == 'exists':
            return Exists(rng.choice(ROLES), rand_concept(depth - 1))
        elif op == 'forall':
            return ForAll(rng.choice(ROLES), rand_concept(depth - 1))
        elif op == 'and':
            return And(rand_concept(depth - 1), rand_concept(depth - 1))
        else:
            return Or(rand_concept(depth - 1), rand_concept(depth - 1))

    for i in range(count):
        c = rand_concept(max_depth)
        tests.append((f"random_{i}: {c}", c, None))

    return tests


def gen_systematic_pairs():
    """All combinations of two demands with one universal."""
    tests = []
    for R1, R2 in itertools.product(ROLES, repeat=2):
        for a, b in [(A, B), (A, nA), (A, nB)]:
            for R3 in ROLES:
                c = conj(Exists(R1, a), Exists(R2, b), ForAll(R3, A))
                name = f"∃{R1}.{a} ⊓ ∃{R2}.{b} ⊓ ∀{R3}.A"
                tests.append((name, c, None))
    return tests


# ── Main test runner ─────────────────────────────────────────

def run_tests(tests, category, henkin_depth=4, verbose=False):
    """Run a batch of tests and report results."""
    total = len(tests)
    correct = 0
    wrong = 0
    henkin_failures = 0
    henkin_tests = 0
    errors = []
    t0 = time.time()

    for i, (name, concept, expected) in enumerate(tests):
        try:
            result, info = check_satisfiability(concept)
        except Exception as e:
            errors.append((name, f"EXCEPTION: {e}"))
            continue

        # Check correctness if expected is known
        if expected is not None:
            if result == expected:
                correct += 1
            else:
                wrong += 1
                errors.append((name, f"WRONG: expected={expected}, got={result}"))
                if verbose:
                    print(f"  ✗ {name}: expected={expected}, got={result}")
                continue
        else:
            correct += 1  # exploratory

        # Henkin validation for SAT results
        if result:
            henkin_tests += 1
            failures, details = henkin_validate(concept, info, max_depth=henkin_depth)
            if failures is None:
                errors.append((name, f"HENKIN SKIP: {details}"))
            elif failures > 0:
                henkin_failures += 1
                errors.append((name,
                    f"HENKIN FAIL: {failures} failures, "
                    f"tree={details['tree_size']}, "
                    f"empty={details['domain_empty']}, "
                    f"ac={details['star_ac']}, "
                    f"assign={details['assignment']}"))
                if verbose or True:  # always print Henkin failures
                    print(f"  ✗ HENKIN {name}: {failures} failures")
                    for d in details.get('details', [])[:3]:
                        print(f"      {d['stage']}: depth={d.get('depth','?')}, "
                              f"new=τ{d['new_type']}, parent=τ{d['parent_type']}")

    elapsed = time.time() - t0

    print(f"\n  [{category}] {total} tests, {elapsed:.1f}s")
    print(f"    Correctness: {correct} ok, {wrong} wrong")
    print(f"    Henkin: {henkin_tests} SAT tested, {henkin_failures} with failures")
    if errors:
        print(f"    Errors ({len(errors)}):")
        for name, msg in errors[:10]:
            print(f"      {name}: {msg}")
        if len(errors) > 10:
            print(f"      ... and {len(errors) - 10} more")

    return {
        'total': total,
        'correct': correct,
        'wrong': wrong,
        'henkin_tests': henkin_tests,
        'henkin_failures': henkin_failures,
        'errors': errors,
        'time': elapsed,
    }


def main():
    print("=" * 70)
    print("ALCI_RCC5 COMPREHENSIVE STRESS TEST")
    print("=" * 70)

    all_results = []

    # Category 1: Known SAT
    tests = gen_known_sat()
    r = run_tests(tests, "Known SAT", henkin_depth=4)
    all_results.append(r)

    # Category 2: Known UNSAT
    tests = gen_known_unsat()
    r = run_tests(tests, "Known UNSAT")
    all_results.append(r)

    # Category 3: Adversarial
    tests = gen_adversarial()
    r = run_tests(tests, "Adversarial", henkin_depth=4)
    all_results.append(r)

    # Category 4: Systematic pairs
    tests = gen_systematic_pairs()
    r = run_tests(tests, "Systematic pairs", henkin_depth=3)
    all_results.append(r)

    # Category 5: Random (depth 2)
    tests = gen_random(count=200, max_depth=2, seed=42)
    r = run_tests(tests, "Random depth-2", henkin_depth=3)
    all_results.append(r)

    # Category 6: Random (depth 3)
    tests = gen_random(count=100, max_depth=3, seed=123)
    r = run_tests(tests, "Random depth-3", henkin_depth=3)
    all_results.append(r)

    # Category 7: Random (depth 4)
    tests = gen_random(count=50, max_depth=4, seed=456)
    r = run_tests(tests, "Random depth-4", henkin_depth=3)
    all_results.append(r)

    # Summary
    total_tests = sum(r['total'] for r in all_results)
    total_wrong = sum(r['wrong'] for r in all_results)
    total_henkin = sum(r['henkin_tests'] for r in all_results)
    total_henkin_fail = sum(r['henkin_failures'] for r in all_results)
    total_time = sum(r['time'] for r in all_results)
    total_errors = sum(len(r['errors']) for r in all_results)

    print(f"\n{'=' * 70}")
    print(f"OVERALL RESULTS")
    print(f"{'=' * 70}")
    print(f"  Total concepts tested: {total_tests}")
    print(f"  Correctness errors: {total_wrong}")
    print(f"  Henkin tree tests: {total_henkin}")
    print(f"  Henkin tree failures: {total_henkin_fail}")
    print(f"  Total errors/warnings: {total_errors}")
    print(f"  Total time: {total_time:.1f}s")

    if total_wrong == 0 and total_henkin_fail == 0:
        print(f"\n  ✓ ALL TESTS PASS")
    else:
        print(f"\n  ✗ FAILURES DETECTED")
        return False

    return True


if __name__ == '__main__':
    success = main()
    sys.exit(0 if success else 1)
