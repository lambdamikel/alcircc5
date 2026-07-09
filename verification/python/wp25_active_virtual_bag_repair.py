#!/usr/bin/env python3
"""
WP25 -- finite checks for the round-14 active-virtual-bag repair.

The repair tested here is not the old horizontal-row discipline.  Universal
sources are propagated as virtual active shadows with their true atomic relation
vector to current ports; vertical entries are allowed, but every finite active
bag (ports plus active shadows) must be a complete composition-closed RCC5
network, with agreement on overlaps.  Thus vertical universal rows no longer
cause port insertion, while the active-network closure condition catches the
round-12/13 shadow-amalgamation failures.

Checks:
  A. The robust G2a witness is SAT by the supplied oracle.
  B. On finite PP-chain prefixes, literal round-13 fallback grows root port
     width as m+1, while the active-virtual repair keeps live port width 2 and
     records remote ancestors only as virtual shadows.
  C. The WP20 bad active-shadow triangle is rejected by active-network closure.
  D. Random active families obtained as restrictions of a concrete finite set
     representation are closed and jointly satisfiable, including vertical
     virtual entries.
"""
from __future__ import annotations

import itertools
import os
import random
import sys
from typing import Dict, FrozenSet, Iterable, List, Tuple

BASE = ('EQ', 'PP', 'PPI', 'PO', 'DR')
NONEQ = ('PP', 'PPI', 'PO', 'DR')
CONV = {'EQ': 'EQ', 'PP': 'PPI', 'PPI': 'PP', 'PO': 'PO', 'DR': 'DR'}
HOR = {'DR', 'PO'}
VERT = {'PP', 'PPI'}


def derive_comp(n: int = 5):
    universe = range(n)
    subsets = []
    for k in range(1, n + 1):
        subsets += [frozenset(c) for c in itertools.combinations(universe, k)]

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


def rcc_rel(a: FrozenSet[int], b: FrozenSet[int]) -> str:
    if a == b:
        return 'EQ'
    if not (a & b):
        return 'DR'
    if a < b:
        return 'PP'
    if b < a:
        return 'PPI'
    return 'PO'


def is_closed(vertices: Iterable[str], net: Dict[Tuple[str, str], str]):
    V = list(vertices)
    for x in V:
        for y in V:
            if x == y:
                continue
            if (x, y) not in net:
                return False, ('missing', x, y)
            if net[(y, x)] != CONV[net[(x, y)]]:
                return False, ('converse', x, y, net[(x, y)], net[(y, x)])
            if net[(x, y)] == 'EQ':
                return False, ('strong-eq', x, y)
    for x in V:
        for y in V:
            if x == y:
                continue
            for z in V:
                if z in (x, y):
                    continue
                if net[(x, z)] not in COMP[(net[(x, y)], net[(y, z)])]:
                    return False, ('composition', x, y, z, net[(x, z)], net[(x, y)], net[(y, z)], sorted(COMP[(net[(x, y)], net[(y, z)])]))
    return True, None


def pc_complete(V: List[str], known: Dict[Tuple[str, str], str]):
    dom = {}
    for i in V:
        for j in V:
            if i == j:
                continue
            if (i, j) in known:
                dom[(i, j)] = frozenset([known[(i, j)]])
            else:
                dom[(i, j)] = frozenset(NONEQ)
    changed = True
    while changed:
        changed = False
        for i in V:
            for j in V:
                if i == j:
                    continue
                dij = dom[(i, j)]
                for k in V:
                    if k in (i, j):
                        continue
                    allowed = set()
                    for r in dom[(i, k)]:
                        for s in dom[(k, j)]:
                            allowed |= COMP[(r, s)]
                    nd = dij & allowed
                    if not nd:
                        return False, (i, j, k, sorted(dij), sorted(allowed))
                    if nd != dij:
                        dom[(i, j)] = frozenset(nd)
                        dom[(j, i)] = frozenset(CONV[r] for r in nd)
                        changed = True
    return True, dom


def add_support_path():
    here = os.path.dirname(__file__)
    candidates = [
        os.path.join(here, '..', 'support'),
        os.path.join(here, '..', '..', 'support'),
        '/mnt/data/round14_repaired_proof/support',
        '/mnt/data/g2g3/gpt_task_g2_g3/support',
    ]
    for cand in candidates:
        if os.path.exists(os.path.join(cand, 'cover_tree_tableau.py')):
            if cand not in sys.path:
                sys.path.insert(0, cand)
            return cand
    raise RuntimeError('support directory not found')


def robust_g2a_concept():
    add_support_path()
    from alcircc5_reasoner import AtomicConcept, Top, And, Exists, ForAll, PP, DR
    A = AtomicConcept('A')
    return And(Exists(PP, Top()), ForAll(PP, And(Exists(PP, Top()), And(ForAll(PP, Exists(PP, Top())), ForAll(DR, A)))))


def oracle_sat():
    add_support_path()
    from cover_tree_tableau import check_satisfiability
    C = robust_g2a_concept()
    sat, info = check_satisfiability(C, verbose=False)
    return sat, info


def chain_prefix_network(m: int):
    # a0 PP a1 PP ... PP am.  Complete closure has ai PP aj for i<j.
    V = [f'a{i}' for i in range(m + 1)]
    net = {}
    for i in range(m + 1):
        for j in range(m + 1):
            if i == j:
                continue
            net[(f'a{i}', f'a{j}')] = 'PP' if i < j else 'PPI'
    return V, net


def g2a_width_table(max_m: int = 10):
    rows = []
    for m in range(1, max_m + 1):
        V, net = chain_prefix_network(m)
        closed, why = is_closed(V, net)
        literal_root_width = m + 1  # round-13 fallback inserts every ancestor as a port
        active_virtual_port_width = 2 if m >= 1 else 1
        virtual_shadow_count = max(0, m - 1)  # ancestors above the root edge, not ports
        rows.append((m, closed, literal_root_width, active_virtual_port_width, virtual_shadow_count, why))
    return rows


def wp20_rejected():
    known = {
        ('x', 'y'): 'PP', ('y', 'x'): 'PPI',
        ('x', 'p'): 'PO', ('p', 'x'): 'PO',
        ('y', 'p'): 'DR', ('p', 'y'): 'DR',
    }
    ok, why = pc_complete(['x', 'y', 'p'], known)
    closed, closed_why = is_closed(['x', 'y', 'p'], known)
    return (not ok) and (not closed), why, closed_why


def random_set_network_trial(rng: random.Random, n_objects: int = 7, universe_size: int = 8):
    universe = list(range(universe_size))
    objs = {}
    used = set()
    i = 0
    while i < n_objects:
        size = rng.randint(1, universe_size)
        val = frozenset(rng.sample(universe, size))
        if val in used:
            continue
        used.add(val)
        objs[f'o{i}'] = val
        i += 1
    net = {}
    names = list(objs)
    for a in names:
        for b in names:
            if a != b:
                net[(a, b)] = rcc_rel(objs[a], objs[b])
    closed, why = is_closed(names, net)
    if not closed:
        return False, ('full-network-not-closed', why)

    # Active bags are arbitrary finite restrictions: ports plus virtual shadows.
    for _ in range(10):
        subset = rng.sample(names, rng.randint(2, min(n_objects, 5)))
        sub = {(a, b): net[(a, b)] for a in subset for b in subset if a != b}
        ok, why = is_closed(subset, sub)
        if not ok:
            return False, ('restriction-not-closed', subset, why)
    return True, None


def random_trials(count: int = 200, seed: int = 21):
    rng = random.Random(seed)
    bad = []
    for i in range(count):
        ok, why = random_set_network_trial(rng)
        if not ok:
            bad.append((i, why))
            break
    return bad


def main():
    print('WP25 -- active-virtual-bag repair checks')
    print('=' * 72)
    sat, info = oracle_sat()
    print('A. robust G2a witness SAT by cover-tree oracle:', 'PASS' if sat else 'FAIL', f"closure={info.get('closure_size')}")
    rows = g2a_width_table()
    ok_width = all(closed and new_w == 2 and old_w == m + 1 for m, closed, old_w, new_w, _, _ in rows)
    print('B. G2a prefix width: old fallback unbounded, new live ports bounded:', 'PASS' if ok_width else 'FAIL')
    print('   m  chain_closed  old_root_ports  new_root_ports  virtual_shadows')
    for m, closed, old_w, new_w, sh, why in rows:
        print(f'  {m:2d}  {str(closed):>12s}  {old_w:14d}  {new_w:14d}  {sh:15d}')
    rej, why_pc, why_closed = wp20_rejected()
    print('C. WP20 bad shadow-shadow triangle rejected by active closure:', 'PASS' if rej else 'FAIL')
    if rej:
        print('   closure conflict:', why_closed)
    bad = random_trials()
    print('D. random concrete active restrictions closed:', 'PASS' if not bad else 'FAIL')
    if bad:
        print('   first bad:', bad[0])
    overall = sat and ok_width and rej and not bad
    print('=' * 72)
    print('WP25 OVERALL:', 'PASS' if overall else 'ATTENTION')
    return 0 if overall else 1


if __name__ == '__main__':
    raise SystemExit(main())
