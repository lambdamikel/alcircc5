#!/usr/bin/env python3
"""
WP7: Side-witness comparability stress test (GPT-5.5 round-5 review, May 2026).

The round-5 review identified a completeness gap in the (M6) verticalization
discipline: it forbids non-vertical PP/PPI relations among side-witness
positions, but such relations CAN occur in satisfiable witness-generated
models. The concrete stress concept is:

    C_side := exists DR.(A and exists PP.B) and exists DR.B

Reading: source x has two DR-witnesses y, z; y is A and has a PP-witness
satisfying B; z itself is B. Then y PP z is consistent (and forced, since
y can be a proper part of z while both are DR-related to x).

If our reasoners report SAT, the review's claim that the concept is
satisfiable is computationally corroborated, and the (M6) clause "all
non-EQ side-frontier pairs are DR/PO" is too strong.

Expected: all three reasoners report SAT.
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'src'))

from alcircc5_reasoner import (
    AtomicConcept, And, Exists, DR, PO, PP, PPI,
    check_satisfiability as check_sat_qm,
)
from alcircc5_reasoner_cyclic import check_satisfiability as check_sat_qm_cyclic
from cover_tree_tableau import check_sat as check_sat_ct


def run():
    A = AtomicConcept('A')
    B = AtomicConcept('B')
    C_side = And(Exists(DR, And(A, Exists(PP, B))), Exists(DR, B))

    print("WP7: side-witness comparability stress (round-5 review)")
    print(f"  Concept: {C_side}")
    print()

    results = []

    sat_ct, _ = check_sat_ct(C_side, verbose=False)
    print(f"  Cover-tree tableau:        SAT={sat_ct}")
    results.append(('cover-tree', sat_ct))

    qm = check_sat_qm(C_side)
    sat_qm = qm[0] if isinstance(qm, tuple) else qm
    print(f"  Quasimodel (baseline):     SAT={sat_qm}")
    results.append(('quasimodel-baseline', sat_qm))

    qmc = check_sat_qm_cyclic(C_side)
    sat_qmc = qmc[0] if isinstance(qmc, tuple) else qmc
    print(f"  Quasimodel (cycle-aware):  SAT={sat_qmc}")
    results.append(('quasimodel-cyclic', sat_qmc))

    print()
    all_sat = all(s for _, s in results)
    print(f"  All three SAT: {all_sat}")
    print(f"  Review expectation (SAT): MATCHES" if all_sat else "  Review expectation (SAT): MISMATCH")

    return 0 if all_sat else 1


if __name__ == '__main__':
    sys.exit(run())
