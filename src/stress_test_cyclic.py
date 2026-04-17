#!/usr/bin/env python3
"""Cross-validate the cover-tree tableau against the cycle-aware quasimodel reasoner.

Same test generators and methodology as stress_test_cover_tree.py, but uses
alcircc5_reasoner_cyclic (cycle_close=True) in place of the baseline QM. If
this run also reports zero mismatches, we recover the original cross-validation
claim with a reasoner that is known-complete on the PO-loop / DR-loop /
PP-PPI cycle patterns the baseline wrongly rejects.
"""

import sys
import time

from stress_test_cover_tree import (
    gen_known_sat, gen_known_unsat, gen_adversarial,
    gen_systematic_pairs, gen_random,
)
from alcircc5_reasoner_cyclic import check_satisfiability as check_sat_qm
from cover_tree_tableau import check_satisfiability as check_sat_ct


def run(timeout_per_test=10.0):
    print("=" * 70)
    print("COVER-TREE vs. CYCLE-AWARE QUASIMODEL CROSS-VALIDATION")
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
    mismatch_records = []

    t_all = time.time()
    for cat_name, tests in categories:
        cat_total = len(tests)
        cat_correct = 0
        cat_mismatch = 0
        cat_errors = []
        t_cat = time.time()

        for name, concept, expected in tests:
            total += 1
            try:
                ct_sat, _ = check_sat_ct(concept)
            except Exception as e:
                ct_sat = None
                ct_errors += 1
                cat_errors.append((name, f"CT ERROR: {e}"))
                continue

            try:
                qm_sat, _ = check_sat_qm(concept)
            except Exception as e:
                qm_sat = None
                qm_errors += 1
                cat_errors.append((name, f"QM-cyclic ERROR: {e}"))
                continue

            if ct_sat is None or qm_sat is None:
                continue

            if expected is not None:
                if ct_sat != expected:
                    cat_errors.append((name,
                        f"CT wrong: got {'SAT' if ct_sat else 'UNSAT'}, "
                        f"expected {'SAT' if expected else 'UNSAT'}"))
                elif ct_sat == expected:
                    cat_correct += 1
                    correct += 1
            else:
                if ct_sat == qm_sat:
                    cat_correct += 1
                    correct += 1
                else:
                    cat_mismatch += 1
                    mismatches += 1
                    mismatch_records.append((cat_name, name, ct_sat, qm_sat))
                    cat_errors.append((name,
                        f"MISMATCH: CT={'SAT' if ct_sat else 'UNSAT'}, "
                        f"QM-cyclic={'SAT' if qm_sat else 'UNSAT'}"))

        elapsed = time.time() - t_cat
        print(f"\n  [{cat_name}] {cat_total} tests, {elapsed:.1f}s")
        print(f"    Correct/matching: {cat_correct}")
        if cat_errors:
            print(f"    Errors ({len(cat_errors)}):")
            for name, msg in cat_errors[:10]:
                print(f"      {name}: {msg}")
            if len(cat_errors) > 10:
                print(f"      ... and {len(cat_errors) - 10} more")

    elapsed_all = time.time() - t_all
    print(f"\n{'=' * 70}")
    print(f"OVERALL: {total} tests in {elapsed_all:.1f}s")
    print(f"  Correct/matching: {correct}")
    print(f"  Mismatches CT vs. QM-cyclic: {mismatches}")
    print(f"  CT errors: {ct_errors}")
    print(f"  QM-cyclic errors: {qm_errors}")
    if mismatch_records:
        print(f"\n  Full mismatch list:")
        for cat, name, ct, qm in mismatch_records:
            print(f"    [{cat}] {name}: CT={'SAT' if ct else 'UNSAT'}, "
                  f"QM-cyclic={'SAT' if qm else 'UNSAT'}")
    print("=" * 70)
    return 0 if mismatches == 0 and ct_errors == 0 and qm_errors == 0 else 1


if __name__ == '__main__':
    sys.exit(run())
