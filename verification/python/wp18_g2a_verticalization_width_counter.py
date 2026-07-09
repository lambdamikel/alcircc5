#!/usr/bin/env python3
"""
WP18 -- G2a countercheck: literal round-13 D2 verticalization vs width.

The fixed robust concept

    C_G2a = ExPP.Top n AllPP.(ExPP.Top n (AllPP.ExPP.Top n AllDR.A))

is satisfiable (checked by the cover-tree tableau oracle). In every model,
a root a0 has an infinite strict PP-chain a0 PP a1 PP a2 ...; every a_i
with i>=1 satisfies AllDR.A, hence has a nonempty (horizontal) universal
obligation set.

Under the literal round-13 D2 rule, an obligation-carrying source must
propagate a shadow in every direction. If a boundary crossing would require
a vertical row entry, D2 falls back to verticalization: the source is inserted
as a live port in the target bag. In the standard edge-bag presentation of a
PP-chain, source a_k crossing downward over separator a_i (i<k) has relation
PPI to a_i, a vertical row entry. Therefore D2 inserts a_k into each lower
edge bag, in particular into the root edge bag b0={a0,a1}. For the length-m
prefix, b0 must contain a0,...,a_m: width m+1. Since m is arbitrary, no finite
K(C_G2a) can bound literal-D2 extraction.

This script checks the finite prefix facts mechanically:
  1. the robust concept is SAT by the project oracle;
  1a. the smaller literal-wording concept ExPP.Top n AllPP.(ExPP.Top n AllPP.ExPP.Top) is also SAT;
  2. the PP-chain prefix network is RCC5-composition closed;
  3. the literal D2 simulation forces root-bag size m+1 for m=1..N.
"""

import os
import sys

# Allow running from either repository root or verification/.
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
SUPPORT = os.path.join(ROOT, 'support')
if SUPPORT not in sys.path:
    sys.path.insert(0, SUPPORT)

from alcircc5_reasoner import (  # noqa: E402
    AtomicConcept, And, Exists, ForAll, Top, PP, DR
)
from cover_tree_tableau import check_sat  # noqa: E402

BASE = ('EQ', 'PP', 'PPI', 'PO', 'DR')
CONV = {'EQ': 'EQ', 'PP': 'PPI', 'PPI': 'PP', 'PO': 'PO', 'DR': 'DR'}
COMP = {
    ('EQ', 'EQ'): {'EQ'}, ('EQ', 'PP'): {'PP'}, ('EQ', 'PPI'): {'PPI'},
    ('EQ', 'PO'): {'PO'}, ('EQ', 'DR'): {'DR'},
    ('PP', 'EQ'): {'PP'}, ('PP', 'PP'): {'PP'},
    ('PP', 'PPI'): set(BASE), ('PP', 'PO'): {'PP', 'PO', 'DR'},
    ('PP', 'DR'): {'DR'},
    ('PPI', 'EQ'): {'PPI'}, ('PPI', 'PP'): {'EQ', 'PP', 'PPI', 'PO'},
    ('PPI', 'PPI'): {'PPI'}, ('PPI', 'PO'): {'PPI', 'PO'},
    ('PPI', 'DR'): {'PPI', 'PO', 'DR'},
    ('PO', 'EQ'): {'PO'}, ('PO', 'PP'): {'PP', 'PO'},
    ('PO', 'PPI'): {'PPI', 'PO', 'DR'}, ('PO', 'PO'): set(BASE),
    ('PO', 'DR'): {'PPI', 'PO', 'DR'},
    ('DR', 'EQ'): {'DR'}, ('DR', 'PP'): {'PP', 'PO', 'DR'},
    ('DR', 'PPI'): {'DR'}, ('DR', 'PO'): {'PP', 'PO', 'DR'},
    ('DR', 'DR'): set(BASE),
}
VERT = {'PP', 'PPI', 'EQ'}


def concept_min_literal():
    top = Top()
    # Smaller attack if D2 uses all vertical universals in Omega literally.
    D = And(Exists(PP, top), ForAll(PP, Exists(PP, top)))
    return And(Exists(PP, top), ForAll(PP, D))


def concept_g2a():
    top = Top()
    A = AtomicConcept('A')
    # Robust version: every strict PP-successor also has a horizontal universal.
    # D = ExPP.Top n (AllPP.ExPP.Top n AllDR.A)
    D = And(Exists(PP, top), And(ForAll(PP, Exists(PP, top)), ForAll(DR, A)))
    return And(Exists(PP, top), ForAll(PP, D))


def rel(i, j):
    if i == j:
        return 'EQ'
    return 'PP' if i < j else 'PPI'


def prefix_network(m):
    V = list(range(m + 1))
    N = {}
    for i in V:
        for j in V:
            if i != j:
                N[(i, j)] = rel(i, j)
    return V, N


def is_closed(V, N):
    for i in V:
        for j in V:
            if i == j:
                continue
            for k in V:
                if k == i or k == j:
                    continue
                if N[(i, k)] not in COMP[(N[(i, j)], N[(j, k)])]:
                    return False, (i, j, k, N[(i, j)], N[(j, k)], N[(i, k)])
    return True, None


def simulate_literal_d2_root_width(m):
    """Return root bag after applying literal D2 fallback to all obligation
    sources a_1..a_m on the downward path to b0.

    Edge bag b_i initially contains a_i,a_{i+1}; source a_k starts in b_{k-1}.
    Crossing from b_i to b_{i-1} has separator a_i, and rel(a_k,a_i)=PPI
    for i<k, hence vertical and not allowed as a D1 row entry. Literal D2
    therefore inserts a_k into the target bag. Repeat to b0.
    """
    bags = [set([i, i + 1]) for i in range(m)]
    fallbacks = []
    for k in range(1, m + 1):
        # a_k already live in b_{k-1}; move downward to b0.
        for i in range(k - 1, 0, -1):
            separator = i
            r = rel(k, separator)
            if r in VERT:
                bags[i - 1].add(k)
                fallbacks.append((k, i, i - 1, separator, r))
            else:
                raise AssertionError('unexpected horizontal crossing')
    return bags[0], fallbacks


def main():
    Cmin = concept_min_literal()
    sat_min, info_min = check_sat(Cmin, verbose=False)
    print('C_min_literal =', Cmin)
    print('oracle_sat_min =', sat_min, 'closure_size =', info_min.get('closure_size'))

    C = concept_g2a()
    sat, info = check_sat(C, verbose=False)
    print('C_G2a_robust =', C)
    print('oracle_sat_robust =', sat, 'closure_size =', info.get('closure_size'))
    if not sat_min or not sat:
        print('ERROR: oracle says a witness concept is not satisfiable')
        return 1

    print('\nfinite prefix check under literal D2:')
    print('m  chain_closed  root_bag_size  expected  fallbacks')
    ok = True
    for m in range(1, 11):
        V, N = prefix_network(m)
        closed, witness = is_closed(V, N)
        root_bag, fallbacks = simulate_literal_d2_root_width(m)
        expected = m + 1
        row_ok = closed and len(root_bag) == expected
        ok = ok and row_ok
        print(f'{m:2d} {str(closed):>12s} {len(root_bag):14d} {expected:9d} {len(fallbacks):10d}')
        if not closed:
            print('  closure failure witness:', witness)
    print('\nconclusion =', 'PASS: root width grows unboundedly with the prefix' if ok else 'FAIL')
    return 0 if ok else 2


if __name__ == '__main__':
    raise SystemExit(main())
