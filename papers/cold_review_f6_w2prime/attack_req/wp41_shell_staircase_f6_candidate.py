#!/usr/bin/env python3
"""
WP41 -- shell-staircase F6 candidate.

This script checks finite prefixes of the following intended infinite set model:

  P_i = {0,...,i}
  Y_i = {i+1, a_i}

Then P_i PP P_j for i<j; Y_i DR P_i; Y_i PO P_j for all j>i;
and Y_i is never PP any P_j.  For i<j, the anchor P_j separates Y_i
from Y_j: Y_i PO P_j and P_j DR Y_j, so comp(PO,DR) excludes EQ and is
non-singleton.  Thus adding Y_n creates n non-shadow, non-mergeable
cross-pairs to old Y_i.
"""
from itertools import combinations, product

REL = ['EQ','DR','PO','PP','PPI']
OFF = ['DR','PO','PP','PPI']

def r(a,b):
    if a == b:
        return 'EQ'
    if a.isdisjoint(b):
        return 'DR'
    if a < b:
        return 'PP'
    if b < a:
        return 'PPI'
    return 'PO'

def derive_comp(max_atoms=6):
    atoms = list(range(max_atoms))
    subs = []
    for mask in range(1, 1 << max_atoms):
        subs.append(frozenset(i for i in atoms if mask & (1 << i)))
    comp = {}
    for a,b,c in product(subs, repeat=3):
        comp.setdefault((r(a,b), r(b,c)), set()).add(r(a,c))
    return {k: frozenset(v) for k,v in comp.items()}

COMP = derive_comp(6)

def build(N):
    # P_0..P_N and Y_0..Y_{N-1}
    elems = {}
    for i in range(N+1):
        elems[f'P{i}'] = frozenset(range(i+1))
    for i in range(N):
        elems[f'Y{i}'] = frozenset([i+1, ('a', i)])
    return elems

def check(N):
    E = build(N)
    names = list(E)
    # path-composition check for the finite set model
    for x,y,z in product(names, repeat=3):
        xy = r(E[x],E[y]); yz = r(E[y],E[z]); xz = r(E[x],E[z])
        if xz not in COMP[(xy,yz)]:
            raise AssertionError((x,y,z,xy,yz,xz,COMP[(xy,yz)]))
    # staircase properties
    for i in range(N+1):
        for j in range(N+1):
            if i < j:
                assert r(E[f'P{i}'], E[f'P{j}']) == 'PP'
            elif i > j:
                assert r(E[f'P{i}'], E[f'P{j}']) == 'PPI'
            else:
                assert r(E[f'P{i}'], E[f'P{j}']) == 'EQ'
    for i in range(N):
        assert r(E[f'P{i}'], E[f'Y{i}']) == 'DR'
        assert r(E[f'Y{i}'], E[f'P{i}']) == 'DR'
        assert r(E[f'Y{i}'], E[f'P{i+1}']) == 'PO'
        for j in range(N+1):
            assert r(E[f'Y{i}'], E[f'P{j}']) != 'PP'  # Shell: forall PP not P
            if j <= i:
                assert r(E[f'Y{i}'], E[f'P{j}']) == 'DR'
            else:
                assert r(E[f'Y{i}'], E[f'P{j}']) == 'PO'
    # live/non-mergeable cross-pairs when adding Y_n at anchor P_n
    live_sets = []
    for i in range(N):
        left = r(E[f'Y{i}'], E[f'P{N}'])  # PO
        right = r(E[f'P{N}'], E[f'Y{N-1}']) if i != N-1 else None
        # More generally, for a hypothetical fresh Y_N with P_N DR Y_N,
        # composition gives comp(Y_i,P_N) o comp(P_N,Y_N) = comp(PO,DR).
        dom = COMP[('PO','DR')]
        assert 'EQ' not in dom and len(dom) > 1
        live_sets.append((f'Y{i}-Ynew via P{N}', sorted(dom)))
    # pairwise old Y_i are also separated by a P_j anchor.
    sep = []
    for i,j in combinations(range(N), 2):
        # anchor P_j: Y_i PO P_j and P_j DR Y_j
        assert r(E[f'Y{i}'], E[f'P{j}']) == 'PO'
        assert r(E[f'P{j}'], E[f'Y{j}']) == 'DR'
        dom = COMP[('PO','DR')]
        sep.append((i,j,sorted(dom), r(E[f'Y{i}'],E[f'Y{j}'])))
    return live_sets, sep

if __name__ == '__main__':
    print('WP41: shell-staircase F6 candidate finite-prefix check')
    print('comp(PO,DR)=', sorted(COMP[('PO','DR')]), '(non-singleton, excludes EQ)')
    print('comp(DR,PO)=', sorted(COMP[('DR','PO')]), '(non-singleton, excludes EQ)')
    for N in [2,3,5,8,12]:
        live, sep = check(N)
        print(f'N={N}: PASS; P_N has {N} previous shell witnesses Y_0..Y_{N-1};')
        print(f'     adding a fresh Y_N would create {N} non-singleton EQ-excluding cross domains comp(PO,DR).')
    print('OVERALL: finite prefixes satisfy the advertised staircase and RCC5 composition closure.')
