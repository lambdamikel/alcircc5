#!/usr/bin/env python3
"""
WP23 -- regression checks for the active-network repair.

The script checks that the round-14 discipline excludes the two finite defects
that survive the round-13 D1-D5 text:

  R1. No global DR default for ordinary nonlocal pairs: a two-edge PP chain
      must leave the endpoint pair to patchwork, which infers PP, rather than
      assigning DR.
  R2. Active closure catches the shadow-shadow vertical conflict: x PP y,
      y DR p forces x DR p, so a simultaneous x-row x PO p is rejected.

It also checks a positive vertical-row case that round 13 rejected: x PPI p as
an active shadow row is locally closed and realizable when the active network is
complete.
"""
from __future__ import annotations

import itertools

BASE = ('EQ', 'PP', 'PPI', 'PO', 'DR')
NONEQ = ('PP', 'PPI', 'PO', 'DR')
CONV = {'EQ': 'EQ', 'PP': 'PPI', 'PPI': 'PP', 'PO': 'PO', 'DR': 'DR'}


def derive_comp(n=5):
    universe = range(n)
    subsets = []
    for k in range(1, n + 1):
        subsets.extend(frozenset(c) for c in itertools.combinations(universe, k))

    def rel(a, b):
        if a == b:
            return 'EQ'
        if not (a & b):
            return 'DR'
        if a < b:
            return 'PP'
        if b < a:
            return 'PPI'
        return 'PO'

    table = {(r, s): set() for r in BASE for s in BASE}
    for a in subsets:
        for b in subsets:
            r = rel(a, b)
            for c in subsets:
                table[(r, rel(b, c))].add(rel(a, c))
    return {k: frozenset(v) for k, v in table.items()}


COMP = derive_comp()


def pc_complete(vertices, known):
    dom = {}
    for i in vertices:
        for j in vertices:
            if i == j:
                dom[(i, j)] = frozenset(['EQ'])
            elif (i, j) in known:
                dom[(i, j)] = frozenset([known[(i, j)]])
            else:
                dom[(i, j)] = frozenset(NONEQ)
    changed = True
    while changed:
        changed = False
        for i in vertices:
            for j in vertices:
                if i == j:
                    continue
                dij = dom[(i, j)]
                allowed = set(NONEQ)
                for k in vertices:
                    if k in (i, j):
                        continue
                    via = set()
                    for r in dom[(i, k)]:
                        for s in dom[(k, j)]:
                            via |= COMP[(r, s)]
                    allowed &= via
                nd = dij & allowed
                if not nd:
                    return False, (i, j, dij, allowed)
                if nd != dij:
                    dom[(i, j)] = frozenset(nd)
                    dom[(j, i)] = frozenset(CONV[r] for r in nd)
                    changed = True
    return True, dom


def closed(vertices, net):
    for x in vertices:
        for y in vertices:
            for z in vertices:
                if net[(x, z)] not in COMP[(net[(x, y)], net[(y, z)])]:
                    return False, (x, y, z, net[(x, z)], net[(x, y)], net[(y, z)], sorted(COMP[(net[(x, y)], net[(y, z)])]))
    return True, None


def no_global_default_check():
    known = {('x', 'z'): 'PP', ('z', 'x'): 'PPI', ('z', 'y'): 'PP', ('y', 'z'): 'PPI'}
    ok, dom = pc_complete(['x', 'z', 'y'], known)
    literal = dict(known)
    literal[('x', 'y')] = 'DR'
    literal[('y', 'x')] = 'DR'
    lit_ok, _ = pc_complete(['x', 'z', 'y'], literal)
    return ok and (not lit_ok) and dom[('x', 'y')] == frozenset(['PP']), dom.get(('x', 'y')) if ok else None


def shadow_shadow_conflict_check():
    known = {
        ('x', 'y'): 'PP', ('y', 'x'): 'PPI',
        ('x', 'p'): 'PO', ('p', 'x'): 'PO',
        ('y', 'p'): 'DR', ('p', 'y'): 'DR',
    }
    ok, why = pc_complete(['x', 'y', 'p'], known)
    return not ok, why


def positive_vertical_row_check():
    net = {
        ('x', 'x'): 'EQ', ('p', 'p'): 'EQ',
        ('x', 'p'): 'PPI', ('p', 'x'): 'PP',
    }
    ok, why = closed(['x', 'p'], net)
    ok_pc, _ = pc_complete(['x', 'p'], {('x', 'p'): 'PPI', ('p', 'x'): 'PP'})
    return ok and ok_pc, why


def main():
    print('WP23 -- active-closure regression checks')
    print('=' * 72)
    ok1, dom = no_global_default_check()
    print('R1 no global DR default; PP endpoint inferred:', 'PASS' if ok1 else 'FAIL', sorted(dom) if dom else '')
    ok2, why2 = shadow_shadow_conflict_check()
    print('R2 active closure rejects x PP y, y DR p, x PO p:', 'PASS' if ok2 else 'FAIL')
    if ok2:
        print('   conflict witness:', why2)
    ok3, why3 = positive_vertical_row_check()
    print('R3 vertical non-EQ row can be realized when closed:', 'PASS' if ok3 else 'FAIL')
    print('=' * 72)
    ok = ok1 and ok2 and ok3
    print('WP23 OVERALL:', 'PASS' if ok else 'ATTENTION')
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
