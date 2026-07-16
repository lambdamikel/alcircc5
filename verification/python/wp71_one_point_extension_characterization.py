#!/usr/bin/env python3
# WP71: one-point extension characterization for ordered-disjoint RCC5 pockets.
# No dependencies.

from itertools import product

ATOMS = ["PP", "PPI", "PO", "DR"]
INV = {"PP":"PPI", "PPI":"PP", "PO":"PO", "DR":"DR", "EQ":"EQ"}

# RCC5 composition table for proper atoms under strong EQ, derived by finite sets.
def rel(a,b):
    if a == b: return "EQ"
    if a < b: return "PP"
    if b < a: return "PPI"
    if a.isdisjoint(b): return "DR"
    return "PO"

def derive_comp():
    universe = list(range(4))
    regs = [frozenset(s) for mask in range(1,1<<4) for s in [set(i for i in universe if mask>>i & 1)]]
    comp = {(r,s):set() for r in ["EQ"]+ATOMS for s in ["EQ"]+ATOMS}
    for x in regs:
        for y in regs:
            r = rel(x,y)
            for z in regs:
                s = rel(y,z)
                t = rel(x,z)
                comp[(r,s)].add(t)
    return comp
COMP = derive_comp()

def atom(net,i,j):
    if i==j: return "EQ"
    return net[(i,j)]

def closed(net,n):
    for i in range(n):
        if atom(net,i,i)!="EQ": return False
    for i in range(n):
        for j in range(n):
            if atom(net,j,i) != INV[atom(net,i,j)]:
                return False
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if atom(net,i,k) not in COMP[(atom(net,i,j), atom(net,j,k))]:
                    return False
    return True

def all_networks(n):
    pairs = [(i,j) for i in range(n) for j in range(i+1,n)]
    for vals in product(ATOMS, repeat=len(pairs)):
        net={}
        for (i,j),r in zip(pairs,vals):
            net[(i,j)] = r
            net[(j,i)] = INV[r]
        yield net

def less(net,x,y):
    return atom(net,x,y)=="PP"

def disj(net,x,y):
    return atom(net,x,y)=="DR"

def leq(net,x,y):
    return x==y or less(net,x,y)

def criterion(net,n,rels):
    # rels[x] is relation e -> x, where e is the new point.
    U = {x for x,r in enumerate(rels) if r=="PP"}   # e < x
    L = {x for x,r in enumerate(rels) if r=="PPI"}  # x < e
    D = {x for x,r in enumerate(rels) if r=="DR"}   # e # x
    # U upward closed.
    for x in list(U):
        for y in range(n):
            if less(net,x,y) and y not in U:
                return False, "U_not_upward"
    # L downward closed.
    for x in list(L):
        for y in range(n):
            if less(net,y,x) and y not in L:
                return False, "L_not_downward"
    # If e is below u and u is disjoint from x, then e is disjoint from x.
    for u in U:
        for x in range(n):
            if disj(net,u,x) and x not in D:
                return False, "U_disj_not_in_D"
    # L below U already in old order.
    for l in L:
        for u in U:
            if not less(net,l,u):
                return False, "L_not_below_U"
    # D downward closed.
    for d in list(D):
        for y in range(n):
            if leq(net,y,d) and y not in D:
                return False, "D_not_downward"
    # Elements below e must already be disjoint from elements disjoint from e.
    for l in L:
        for d in D:
            if not disj(net,l,d):
                return False, "L_D_not_disjoint"
    return True, "ok"

def extend(net,n,rels):
    m=n+1; e=n
    new=dict(net)
    for x,r in enumerate(rels):
        new[(e,x)] = r
        new[(x,e)] = INV[r]
    return new

def main():
    print("WP71 one-point extension characterization")
    print("Criterion uses U={x:ePPx}, L={x:ePPIx}, D={x:eDRx}.")
    print("Checks: U up-closed, U#-closure into D, L down-closed, L<U, D down-closed, L#D.")
    for n in range(1,5):
        total_closed=0; tested=0; mismatches=[]; reason_count={}
        for net in all_networks(n):
            if not closed(net,n):
                continue
            total_closed += 1
            for rels in product(ATOMS, repeat=n):
                crit,reason = criterion(net,n,rels)
                brute = closed(extend(net,n,rels), n+1)
                tested += 1
                if crit != brute:
                    mismatches.append((net,rels,crit,brute,reason))
                    if len(mismatches)>=3: break
                if not crit:
                    reason_count[reason]=reason_count.get(reason,0)+1
            if len(mismatches)>=3: break
        print(f"n={n}: closed_pockets={total_closed} tested_extensions={tested} mismatches={len(mismatches)}")
        if mismatches:
            for _,rels,crit,brute,reason in mismatches[:3]:
                print("  mismatch", rels, crit, brute, reason)
            break
    # Show a sample pocket with internal DR: a,b with a DR b.
    net={(0,1):"DR",(1,0):"DR"}
    print("\nSample pocket: 0 DR 1")
    for rels in [("PP","PP"),("DR","DR"),("PP","DR"),("PO","PO")]:
        crit,reason=criterion(net,2,rels)
        brute=closed(extend(net,2,rels),3)
        print(f"  e relations {rels}: criterion={crit} reason={reason} brute_closed={brute}")
    print("\nPASS if all mismatch counts are 0.")

if __name__ == "__main__":
    main()
