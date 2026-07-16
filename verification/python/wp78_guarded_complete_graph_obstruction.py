#!/usr/bin/env python3
"""
WP78: why the off-the-shelf guarded/clique-guarded tree-cover theorem
is not directly enough for ALCI_RCC5 under total RCC5 edge-colouring.

In strong-EQ RCC5, every distinct pair carries one of PP/PPI/PO/DR.
Thus the ordinary Gaifman graph of every nontrivial model is complete.
For the simplest satisfiable vertical PP-chain, every finite prefix has
Gaifman graph K_n, hence treewidth n-1.  Any guarded/tree-decomposition
that must cover every guarded pair therefore has unbounded width even for
one-state regular models.

This script prints the finite-prefix data and a small sanity check for
RCC5 closure of the vertical chain.
"""
from itertools import product

ATOMS = ["EQ", "PP", "PPI", "PO", "DR"]
PROPER = ["PP", "PPI", "PO", "DR"]
CONV = {"EQ":"EQ", "PP":"PPI", "PPI":"PP", "PO":"PO", "DR":"DR"}

def rel_chain(i, j):
    if i == j:
        return "EQ"
    if i < j:
        return "PP"
    return "PPI"

# RCC5 composition table from finite-set semantics over a small universe.
def rcc5(a,b):
    if a == b: return "EQ"
    if a < b: return "PP"
    if b < a: return "PPI"
    if a.isdisjoint(b): return "DR"
    return "PO"

def derive_comp():
    U = range(4)
    subs = [frozenset(s) for mask in range(1, 1<<4) for s in [[i for i in U if mask>>i & 1]]]
    comp = {(r,s): set() for r in ATOMS for s in ATOMS}
    for A in subs:
        for B in subs:
            r = rcc5(A,B)
            for C in subs:
                s = rcc5(B,C)
                t = rcc5(A,C)
                comp[(r,s)].add(t)
    return comp
COMP = derive_comp()

def chain_closed(n):
    bad = []
    for i,j,k in product(range(n), repeat=3):
        r = rel_chain(i,j)
        s = rel_chain(j,k)
        t = rel_chain(i,k)
        if t not in COMP[(r,s)]:
            bad.append((i,j,k,r,s,t,COMP[(r,s)]))
    return bad

def gaifman_edges(n):
    # Because every distinct pair has a proper RCC relation, all pairs are edges.
    return n*(n-1)//2

def clique_number(n):
    return n

def treewidth_complete_graph(n):
    # tw(K_n) = n-1.
    return max(0, n-1)

def main():
    print("WP78 guarded/clique-guarded obstruction under total RCC5 edge-colouring")
    print("Finite prefixes of one infinite PP-chain x0 PP x1 PP x2 ...")
    print()
    for n in [1,2,3,4,5,8,12,20]:
        bad = chain_closed(n)
        print(f"n={n:2d}: closure_errors={len(bad):2d} gaifman_edges={gaifman_edges(n):3d} clique_number={clique_number(n):2d} treewidth_Kn={treewidth_complete_graph(n):2d}")
    print()
    print("Observation:")
    print("  Even this one-state regular vertical chain has complete Gaifman graph K_n on every n-prefix.")
    print("  Any standard guarded/tree-decomposition argument that treats every RCC atom as a guard")
    print("  sees unbounded clique/tree width. The model is regular, but not guarded-tree-like")
    print("  in the ordinary sparse-Gaifman sense.")
    print()
    print("Conclusion:")
    print("  Off-the-shelf guarded/clique-guarded covers do not directly close the proof.")
    print("  The needed cover theorem must exploit finite edge colours and realized triple patterns,")
    print("  rather than bounded Gaifman/clique width.")

if __name__ == "__main__":
    main()
