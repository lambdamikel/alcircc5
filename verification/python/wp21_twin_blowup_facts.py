#!/usr/bin/env python3
"""
WP21 -- finite RCC5 facts for profile-copy expansion.

Round 14 stores one active shadow representative for a profile and expands it to
as many same-profile occurrences as the tree contains.  The expansion assigns a
copy atom e_s to each profile s.  If e_s is PP or PPI, copies are arranged as a
strict chain; if e_s is PO or DR, copies form a symmetric clique.  Cross-profile
relations are kept equal to the representative relation.

This script checks:
  A1. Every RCC5 atom can serve as an internally closed copy atom.
  A2. The finite compatibility equations in Definition CopyOK are sufficient:
      every closed representative network satisfying them remains closed after
      all profiles are blown up.
  A3. The special PP-chain expansion used by the G2a homogeneous tower is a
      valid instance for every outside atom.
"""
from __future__ import annotations

import itertools

BASE = ('EQ', 'PP', 'PPI', 'PO', 'DR')
NONEQ = ('PP', 'PPI', 'PO', 'DR')
CONV = {'EQ': 'EQ', 'PP': 'PPI', 'PPI': 'PP', 'PO': 'PO', 'DR': 'DR'}


def derive_comp(n: int = 5):
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


def closed(vertices, net):
    for x in vertices:
        if net[(x, x)] != 'EQ':
            return False, ('diag', x, net[(x, x)])
        for y in vertices:
            if net[(x, y)] != CONV[net[(y, x)]]:
                return False, ('conv', x, y, net[(x, y)], net[(y, x)])
            if x != y and net[(x, y)] == 'EQ':
                return False, ('strong-eq', x, y)
    for x in vertices:
        for y in vertices:
            for z in vertices:
                if net[(x, z)] not in COMP[(net[(x, y)], net[(y, z)])]:
                    return False, ('comp', x, y, z, net[(x, z)], net[(x, y)], net[(y, z)], sorted(COMP[(net[(x, y)], net[(y, z)])]))
    return True, None


def all_closed_networks(n):
    verts = tuple(range(n))
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for labels in itertools.product(NONEQ, repeat=len(pairs)):
        net = {}
        for v in verts:
            net[(v, v)] = 'EQ'
        for (i, j), r in zip(pairs, labels):
            net[(i, j)] = r
            net[(j, i)] = CONV[r]
        ok, _ = closed(verts, net)
        if ok:
            yield verts, net


def copy_relation(e, i, j):
    if i == j:
        return 'EQ'
    if e in ('DR', 'PO'):
        return e
    # For vertical copy atoms, use a linear chain.  The forward relation is e.
    if i < j:
        return e
    return CONV[e]


def copy_ok_for_pair(e_s, c, e_u):
    """Finite equations for two copied profiles with cross atom c."""
    candidates_s = {e_s, CONV[e_s]}
    candidates_u = {e_u, CONV[e_u]}
    # Two copies of s and one copy of u.
    for es in candidates_s:
        if c not in COMP[(es, c)]:
            return False
        if es not in COMP[(c, CONV[c])]:
            return False
    # One copy of s and two copies of u.
    for eu in candidates_u:
        if c not in COMP[(c, eu)]:
            return False
        if eu not in COMP[(CONV[c], c)]:
            return False
    return True


def copy_ok_network(verts, net, copy_atoms):
    for v in verts:
        e = copy_atoms[v]
        for ev in {e, CONV[e]}:
            if ev not in COMP[(ev, ev)]:
                return False
    for s in verts:
        for u in verts:
            if s == u:
                continue
            if not copy_ok_for_pair(copy_atoms[s], net[(s, u)], copy_atoms[u]):
                return False
    return True


def expand_copies(verts, net, multiplicities, copy_atoms):
    new_verts = []
    origin = {}
    rank = {}
    for v in verts:
        for k in range(multiplicities[v]):
            nv = (v, k)
            new_verts.append(nv)
            origin[nv] = v
            rank[nv] = k
    out = {}
    for a in new_verts:
        for b in new_verts:
            va, vb = origin[a], origin[b]
            if va == vb:
                out[(a, b)] = copy_relation(copy_atoms[va], rank[a], rank[b])
            else:
                out[(a, b)] = net[(va, vb)]
    return tuple(new_verts), out


def stress_generic(max_n=3, max_mult=3):
    checked = 0
    failures = []
    for n in range(1, max_n + 1):
        for verts, net in all_closed_networks(n):
            for copy_tuple in itertools.product(NONEQ, repeat=n):
                copy_atoms = {v: copy_tuple[i] for i, v in enumerate(verts)}
                if not copy_ok_network(verts, net, copy_atoms):
                    continue
                if n <= 3:
                    mults_iter = itertools.product(range(1, max_mult + 1), repeat=n)
                else:
                    mults_iter = [(1, 1, 1, 1), (2, 1, 1, 1), (3, 2, 1, 1), (2, 2, 2, 2)]
                for mult_tuple in mults_iter:
                    mult = {v: mult_tuple[i] for i, v in enumerate(verts)}
                    ev, en = expand_copies(verts, net, mult, copy_atoms)
                    ok, why = closed(ev, en)
                    checked += 1
                    if not ok:
                        failures.append((verts, net, copy_atoms, mult, why))
                        return checked, failures
    return checked, failures


def pp_universal_for_outside_atoms():
    return all(copy_ok_for_pair('PP', c, 'PP') for c in NONEQ)


def main():
    print('WP21 -- profile-copy expansion facts')
    print('=' * 72)
    a1 = all(e in COMP[(e, e)] for e in NONEQ)
    print('A1 each atom is internally copy-closed:', 'PASS' if a1 else 'FAIL')
    checked, failures = stress_generic()
    print('A2 CopyOK blow-up stress cases:', checked)
    print('A2 result:', 'PASS' if not failures else 'FAIL')
    if failures:
        print('   first failure:', failures[0][-1])
    a3 = pp_universal_for_outside_atoms()
    print('A3 PP-chain works for every outside atom:', 'PASS' if a3 else 'FAIL')
    print('=' * 72)
    ok = a1 and (not failures) and a3
    print('WP21 OVERALL:', 'PASS' if ok else 'ATTENTION')
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
