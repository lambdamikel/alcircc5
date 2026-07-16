#!/usr/bin/env python3
"""
WP43 -- Attempt to pump the W2' non-uniformity gadget along a vertical PP chain.

This script constructs finite set-model prefixes of a strengthened shell/W2
pump.  At level i there are T-twins L_i,U_i around an A_i selector:

    L_i PP A_i PP U_i.

At every later/same B_j, the intended W2 split holds:

    A_i PO B_j,   L_i DR B_j,   U_i PPI B_j      (i <= j).

Moreover L_i and U_i have the same row to the vertical P-interface P_j
for j>i, so with only the P-interface row they would require non-uniform
steering to fresh B_j.

The sting: the immediately previous B_{j-1} is a finite inherited slot that
separates all older pairs L_i/U_i.  Thus this natural pump collapses to a
finite row quotient.  The script verifies both facts.
"""
from itertools import combinations, permutations

BASE=("EQ","PP","PPI","PO","DR")
CONV={"EQ":"EQ","PP":"PPI","PPI":"PP","PO":"PO","DR":"DR"}

def derive_comp(n=5):
    U=range(n)
    subs=[frozenset(c) for k in range(1,n+1) for c in combinations(U,k)]
    def rel(a,b):
        if a==b: return "EQ"
        if not (a & b): return "DR"
        if a < b: return "PP"
        if b < a: return "PPI"
        return "PO"
    table={(r,s):set() for r in BASE for s in BASE}
    for a in subs:
        for b in subs:
            rab=rel(a,b)
            for c in subs:
                table[(rab,rel(b,c))].add(rel(a,c))
    return {k:frozenset(v) for k,v in table.items()}
COMP=derive_comp()

def r(A,B):
    if A==B: return "EQ"
    if not (A & B): return "DR"
    if A < B: return "PP"
    if B < A: return "PPI"
    return "PO"

def build_sets(N):
    # P_k is a strict increasing chain.  Each gap P_{k+1}\P_k has two
    # atoms so L_k and B_k can both be DR to P_k and PO to P_{k+1}
    # while remaining DR from each other.
    base=("base",)
    gap=lambda i,b:("g",i,b)
    sel=lambda i,j:("sel",i,j)      # selector atom shared by A_i and B_j
    priv=lambda tag,i:(tag,i)

    sets={}
    for k in range(N+1):
        S=set(base)
        for t in range(k):
            S.add(gap(t,0)); S.add(gap(t,1))
        sets[f"P{k}"]=frozenset(S)

    # First define B_j; U_i will contain all B_j for j>=i.
    for j in range(N):
        S={gap(j,1), priv("b",j)}
        for i in range(j+1):
            S.add(sel(i,j))
        sets[f"B{j}"]=frozenset(S)

    for i in range(N):
        L={gap(i,0), priv("l",i)}
        A=set(L)
        A.add(priv("a",i))
        for j in range(i,N):
            A.add(sel(i,j))
        U=set(A)
        U.add(priv("u",i))
        for j in range(i,N):
            U |= set(sets[f"B{j}"])
        sets[f"L{i}"]=frozenset(L)
        sets[f"A{i}"]=frozenset(A)
        sets[f"U{i}"]=frozenset(U)
    return sets

def check_closed(sets):
    names=list(sets)
    net={(x,y):r(sets[x],sets[y]) for x in names for y in names}
    errs=[]
    for x,y,z in permutations(names,3):
        if net[(x,z)] not in COMP[(net[(x,y)],net[(y,z)])]:
            errs.append((x,y,z,net[(x,y)],net[(y,z)],net[(x,z)],sorted(COMP[(net[(x,y)],net[(y,z)])])))
            if len(errs)>=10: break
    return net,errs

def row(net,x,slots):
    return tuple(net[(x,s)] for s in slots)

def main():
    for N in [2,3,5,8]:
        sets=build_sets(N)
        net,errs=check_closed(sets)
        assert not errs, errs[:3]

        # Intended pump relations.
        for i in range(N):
            assert net[(f"L{i}",f"A{i}")] == "PP"
            assert net[(f"A{i}",f"U{i}")] == "PP"
            for j in range(i,N):
                assert net[(f"A{i}",f"B{j}")] == "PO"
                assert net[(f"L{i}",f"B{j}")] == "DR"
                assert net[(f"U{i}",f"B{j}")] == "PPI"

        # With only the vertical interface P_j plus core P0, every old L_i/U_i
        # pair is row-identical for i<j and requires different values to B_j.
        raw_collisions=[]
        for j in range(1,N):
            slots=["P0",f"P{j}"]
            for i in range(j):
                if row(net,f"L{i}",slots)==row(net,f"U{i}",slots):
                    assert net[(f"L{i}",f"B{j}")] != net[(f"U{i}",f"B{j}")]
                    raw_collisions.append((i,j,row(net,f"L{i}",slots),net[(f"L{i}",f"B{j}")],net[(f"U{i}",f"B{j}")]))
        assert raw_collisions

        # But one extra inherited slot, the immediately previous B_{j-1},
        # separates all older L_i/U_i pairs at the next B_j step.
        separated=True
        for j in range(1,N):
            slots=["P0",f"P{j}",f"B{j-1}"]
            for i in range(j):
                if row(net,f"L{i}",slots)==row(net,f"U{i}",slots):
                    separated=False
                    print("unseparated",N,i,j,slots,row(net,f"L{i}",slots))
        assert separated

        print(f"N={N}: closed set-model prefix; raw P-row collisions={len(raw_collisions)}; previous-B slot separates all")

    # Show the local W2 forcing cells used in the construction.
    print("composition checks:")
    print("  PP ; PO ->", sorted(COMP[("PP","PO")]), "and B forbids PO/PPI-to-T => L-B=DR")
    print("  PPI ; PO ->", sorted(COMP[("PPI","PO")]), "and B forbids PO-to-T => U-B=PPI")

if __name__ == "__main__":
    main()
