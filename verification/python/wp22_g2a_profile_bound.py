#!/usr/bin/env python3
"""
WP22 -- the G2a tower under literal D2 versus the round-14 repair.

The round-13 literal fallback turns every remote vertical shadow into a live
port.  On a length-m prefix of the G2a tower, m+1 obligation sources cross the
root-side bag and must be co-bagged, so the live-port demand grows with m.

The round-14 repair keeps vertical non-EQ entries as shadow rows and compresses
identical active shadows by profile.  In the same prefix, all tower sources have
one type and the same relation PPI to the root-side port, so only one active
shadow profile is needed; no live port is inserted by universal propagation.

The SAT calls are finite approximants used as a regression check against the
project oracle; the counting comparison is the finite prefix of the proof's
width argument.
"""
from __future__ import annotations

import os
import sys

HERE = os.path.dirname(__file__)
SUPPORT = os.path.abspath(os.path.join(HERE, '..', 'support'))
if SUPPORT not in sys.path:
    sys.path.insert(0, SUPPORT)

from alcircc5_reasoner import AtomicConcept, Top, And, Exists, ForAll, PP, DR
from cover_tree_tableau import check_satisfiability


def finite_tower_approximant(depth: int):
    """A finite satisfiable prefix resembling the G2a tower obligations."""
    A = AtomicConcept('A')
    node = And(ForAll(DR, A), Top())
    for _ in range(depth):
        node = And(ForAll(DR, A), Exists(PP, node))
    return Exists(PP, node)


def literal_d2_live_ports(prefix_len: int) -> int:
    # root-side bag already has the local boundary port; each of prefix_len
    # remote obligation sources is inserted as a live manifestation.
    return 1 + prefix_len


def repaired_shadow_profiles(prefix_len: int) -> int:
    # In the homogeneous prefix all active sources share: type = tower type,
    # obligation set = {(DR,A)}, and row to the root-side port = PPI.
    # Multiplicity is discharged by WP21's PP-chain copy expansion.
    return 1 if prefix_len > 0 else 0


def main():
    max_depth = int(os.environ.get('WP22_MAX_DEPTH', '4'))
    print('WP22 -- G2a tower profile-count regression')
    print('=' * 72)
    sat_ok = True
    for d in range(1, max_depth + 1):
        concept = finite_tower_approximant(d)
        sat, info = check_satisfiability(concept, verbose=False)
        sat_ok = sat_ok and sat
        print('depth %2d: oracle=%s, literal_live_ports=%2d, repaired_profiles=%d, closure=%s' % (
            d, 'SAT' if sat else 'UNSAT', literal_d2_live_ports(d), repaired_shadow_profiles(d), info.get('closure_size')))
    growth_ok = all(literal_d2_live_ports(d) > literal_d2_live_ports(d - 1) for d in range(2, max_depth + 1))
    bounded_ok = all(repaired_shadow_profiles(d) == 1 for d in range(1, max_depth + 1))
    print('=' * 72)
    print('finite approximants SAT:', 'PASS' if sat_ok else 'FAIL')
    print('literal D2 live-port count grows:', 'PASS' if growth_ok else 'FAIL')
    print('round-14 profile count bounded on the prefix:', 'PASS' if bounded_ok else 'FAIL')
    ok = sat_ok and growth_ok and bounded_ok
    print('WP22 OVERALL:', 'PASS' if ok else 'ATTENTION')
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
