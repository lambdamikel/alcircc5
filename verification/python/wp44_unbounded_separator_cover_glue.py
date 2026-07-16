#!/usr/bin/env python3
"""
WP44 -- an unbounded separator-cover glue-step family for RCC5.

This is NOT claimed to be ALCI-forced.  It shows that the algebraic
support-tree/separator-cover statement is false for arbitrary jointly
realizable glue steps: for every n there is a composition-closed finite
set model with n W2-style selector pairs (L_i,U_i), a fresh b, and old
selectors A_i such that b forces different rows for L_i and U_i, while
any old separator cover that distinguishes all n pairs must have size n.

The point is to isolate the extra burden in the ALCI-forced version:
finite modal concepts must rule out/force such identity-match selectors.
"""
from itertools import combinations, chain

ATOMS = ["DR","PO","PP","PPI"]

def rel(A,B):
    if A == B: return "EQ"
    if A.isdisjoint(B): return "DR"
    if A < B: return "PP"
    if B < A: return "PPI"
    return "PO"

def comp_table(universe_size=5):
    U = list(range(universe_size))
    subs = [frozenset(c) for k in range(1, universe_size+1) for c in combinations(U,k)]
    comp = {}
    for A in subs:
        for B in subs:
            for C in subs:
                comp.setdefault((rel(A,B), rel(B,C)), set()).add(rel(A,C))
    return {k: frozenset(v) for k,v in comp.items()}

COMP = comp_table(5)

def build(n):
    # atoms are strings.  e_{i,j} makes L_i PO A_j for j != i, while
    # L_i PP A_i.  c_i is the private b-overlap of A_i.
    b = {"d"} | {f"c{i}" for i in range(n)}
    sets = {"b": frozenset(b)}
    for i in range(n):
        L = ({f"l{i}"} | {f"e{i}_{j}" for j in range(n) if j != i} | {f"g{min(i,j)}_{max(i,j)}" for j in range(n) if j != i})
        # A_i contains L_i and all incoming e_{k,i}; hence L_k PO A_i for k != i.
        A = set(L) | {f"c{i}", f"a{i}"} | {f"e{k}_{i}" for k in range(n) if k != i}
        U = set(A) | set(b) | {f"u{i}"}
        sets[f"L{i}"] = frozenset(L)
        sets[f"A{i}"] = frozenset(A)
        sets[f"U{i}"] = frozenset(U)
    return sets

def check_closed(sets):
    names = list(sets)
    errs = []
    for x in names:
        for y in names:
            if x == y: continue
            rxy = rel(sets[x], sets[y])
            if rel(sets[y], sets[x]) != {"PP":"PPI","PPI":"PP","DR":"DR","PO":"PO","EQ":"EQ"}[rxy]:
                errs.append(("conv",x,y))
            for z in names:
                if len({x,y,z}) < 3: continue
                rxz = rel(sets[x], sets[z])
                ryz = rel(sets[y], sets[z])
                if rxz not in COMP[(rxy, ryz)]:
                    errs.append(("tri",x,y,z,rxz,rxy,ryz,COMP[(rxy,ryz)]))
    return errs

def separators_for_pair(sets, i):
    # Old separators allowed: all old nodes except the two members of the pair.
    # Fresh b is not allowed as an inherited separator at its own birth.
    old = [x for x in sets if x != "b"]
    out = []
    for s in old:
        if s in (f"L{i}", f"U{i}"):
            continue
        if rel(sets[f"L{i}"], sets[s]) != rel(sets[f"U{i}"], sets[s]):
            out.append(s)
    return out

def min_cover_size(sets, n):
    universe = [x for x in sets if x != "b"]
    reqs = [set(separators_for_pair(sets,i)) for i in range(n)]
    # Brute force for modest n; structure should give n exactly.
    for k in range(n+1):
        for C in combinations(universe,k):
            C=set(C)
            if all(C & req for req in reqs):
                return k, sorted(C), reqs
    return None, [], reqs

def print_matrix(sets,n):
    print("separator incidence: row i needs a separator distinguishing L_i/U_i")
    seps=[f"A{j}" for j in range(n)]
    print("      "+" ".join(f"{s:>3}" for s in seps))
    for i in range(n):
        row=[]
        for s in seps:
            row.append(" 1 " if rel(sets[f"L{i}"],sets[s]) != rel(sets[f"U{i}"],sets[s]) else " . ")
        print(f"i={i:<2} "+" ".join(row))

def main():
    for n in [1,2,3,4,5,6,8]:
        sets=build(n)
        errs=check_closed(sets)
        k,C,reqs=min_cover_size(sets,n)
        print(f"n={n}: objects={len(sets)} closed_errors={len(errs)} min_separator_cover={k}")
        assert not errs
        assert k == n, (n,k,C,reqs)
        # Check W2 split by fresh b.
        for i in range(n):
            assert rel(sets[f"L{i}"], sets["b"]) == "DR"
            assert rel(sets[f"A{i}"], sets["b"]) == "PO"
            assert rel(sets[f"U{i}"], sets["b"]) == "PPI"
    print("\nExample n=5 incidence over A_j selectors:")
    print_matrix(build(5),5)
    print("\nWP44 OVERALL: PASS -- arbitrary jointly-realizable RCC5 glue steps can have unbounded separator-cover number.  Any positive theorem must use the ALCI-forced/quotientable hypothesis, not RCC5 path-consistency alone.")

if __name__ == "__main__":
    main()
