#!/usr/bin/env python3
"""
WP47: RCC5 atomic networks as posets plus downward-closed disjointness.

This probe supports the regular-cover route by isolating the exact algebraic
content of atomic RCC5 composition closure under strong-EQ semantics.

Claim tested exhaustively on all complete atomic networks over n<=4:
  A strong-EQ atomic network is RCC5 composition-closed iff
    (1) PP is an irreflexive transitive strict partial order;
    (2) DR is symmetric and irreflexive;
    (3) DR is incompatible with PP/PPI;
    (4) DR is downward closed along PP in both arguments:
          x' <= x, y' <= y, and x DR y  imply x' DR y'
        where <= is EQ or PP.
    (5) PO is exactly the residual relation between distinct pairs not in
        PP/PPI/DR.

The last item is automatic for complete atomic networks, but listed for clarity.
"""
from itertools import combinations, product

ATOMS = ["EQ", "PP", "PPI", "PO", "DR"]
PROPER = ["PP", "PPI", "PO", "DR"]
CONV = {"EQ":"EQ", "PP":"PPI", "PPI":"PP", "PO":"PO", "DR":"DR"}

def rcc5_rel(A, B):
    A=set(A); B=set(B)
    if A == B: return "EQ"
    if A < B: return "PP"
    if A > B: return "PPI"
    if A.isdisjoint(B): return "DR"
    return "PO"

def derive_comp(max_univ=5):
    U=list(range(max_univ))
    subsets=[]
    for mask in range(1,1<<max_univ):
        subsets.append(frozenset(i for i in U if mask>>i & 1))
    comp={(a,b):set() for a in ATOMS for b in ATOMS}
    for A in subsets:
        for B in subsets:
            r=rcc5_rel(A,B)
            for C in subsets:
                s=rcc5_rel(B,C)
                t=rcc5_rel(A,C)
                comp[(r,s)].add(t)
    return comp

COMP = derive_comp()

def get(net, i, j):
    if i == j: return "EQ"
    if i < j: return net[(i,j)]
    return CONV[net[(j,i)]]

def closure_errors(net, n):
    errs=[]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                r=get(net,i,j); s=get(net,j,k); t=get(net,i,k)
                if t not in COMP[(r,s)]:
                    errs.append((i,j,k,r,s,t,COMP[(r,s)]))
    return errs

def leq(net, x, y):
    # x <= y iff x=y or x PP y
    return x == y or get(net,x,y)=="PP"

def poset_disjoint_errors(net, n):
    errs=[]
    # diagonal/proper handled by representation; check PP transitive/irreflexive implicitly
    for i in range(n):
        if get(net,i,i)!="EQ":
            errs.append(("diag",i))
    # PP strict/asymmetric and transitive
    for i in range(n):
        for j in range(n):
            if i != j and get(net,i,j)=="PP" and get(net,j,i)=="PP":
                errs.append(("pp_sym",i,j))
            for k in range(n):
                if get(net,i,j)=="PP" and get(net,j,k)=="PP" and get(net,i,k)!="PP":
                    errs.append(("pp_trans",i,j,k,get(net,i,k)))
    # DR symmetric/irreflexive/incompatible with comparability automatic by atoms/converse,
    # but check no comparable is DR.
    for i in range(n):
        for j in range(n):
            if i==j and get(net,i,j)=="DR":
                errs.append(("dr_refl",i))
            if get(net,i,j)=="DR" and get(net,j,i)!="DR":
                errs.append(("dr_sym",i,j))
            if get(net,i,j)=="DR" and (get(net,i,j) in ("PP","PPI") or get(net,j,i) in ("PP","PPI")):
                errs.append(("dr_comp",i,j))
    # downward closure: if x DR y and xp <= x and yp <= y then xp DR yp, unless xp=yp impossible.
    for x in range(n):
        for y in range(n):
            if x==y or get(net,x,y)!="DR":
                continue
            for xp in range(n):
                if not leq(net,xp,x): continue
                for yp in range(n):
                    if not leq(net,yp,y): continue
                    if xp == yp:
                        errs.append(("dr_down_eq_collision",x,y,xp,yp))
                    elif get(net,xp,yp)!="DR":
                        errs.append(("dr_down",x,y,xp,yp,get(net,xp,yp)))
    return errs

def enumerate_networks(n):
    pairs=list(combinations(range(n),2))
    for labels in product(PROPER, repeat=len(pairs)):
        yield dict(zip(pairs, labels))

def main():
    print("RCC5 composition table (proper/proper singleton cells):")
    for a in PROPER:
        for b in PROPER:
            cell=COMP[(a,b)]
            if len(cell)==1:
                print(f"  comp({a},{b}) = {sorted(cell)}")
    for n in range(1,5):
        total=closed=char_ok=both=bad1=bad2=0
        example_mismatch=None
        for net in enumerate_networks(n):
            total+=1
            c_ok = not closure_errors(net,n)
            p_ok = not poset_disjoint_errors(net,n)
            if c_ok: closed+=1
            if p_ok: char_ok+=1
            if c_ok and p_ok: both+=1
            if c_ok != p_ok:
                if c_ok: bad1+=1
                else: bad2+=1
                if example_mismatch is None:
                    example_mismatch=(net,c_ok,p_ok,closure_errors(net,n)[:3],poset_disjoint_errors(net,n)[:3])
        print(f"n={n}: total={total} closure_ok={closed} poset_DR_ok={char_ok} both={both} mismatch={bad1+bad2}")
        if example_mismatch:
            print("  MISMATCH:", example_mismatch)
            raise SystemExit(1)
    print("PASS: exhaustive n<=4 agrees: RCC5 closure == strict PP poset + downward-closed DR residual PO.")

if __name__ == "__main__":
    main()
