#!/usr/bin/env python3
"""
WP83: Non-uniform cross-policy characterization for two RCC5 pockets.

We use the ordered-disjoint normal form:
  PP  = strict order <
  DR  = disjointness #, symmetric/irreflexive/downward closed
  PO  = residual
  PPI = converse of PP

Given two closed pockets A and B and an arbitrary cross atom assignment on A x B,
we compare:
  (1) brute RCC5 composition closure of the combined atomic network;
  (2) a finite ordered-disjoint criterion:
      - transitive closure of old orders plus cross-order introduces no new internal
        order inside A or B and is irreflexive;
      - downward closure of old/cross disjointness under the new order introduces
        no diagonal, no comparable-disjoint pair, and no new internal disjointness
        inside A or B.

The goal is to confirm that arbitrary non-uniform cross policies are exactly finite
bipartite order/disjointness policies satisfying this criterion.
"""
from itertools import product, combinations
import random

ATOMS = ["PP", "PPI", "PO", "DR"]
ALL = ["EQ"] + ATOMS
CONV = {"EQ":"EQ", "PP":"PPI", "PPI":"PP", "PO":"PO", "DR":"DR"}

def rel_of(A,B):
    A=set(A); B=set(B)
    if A==B: return "EQ"
    if A < B: return "PP"
    if B < A: return "PPI"
    if A.isdisjoint(B): return "DR"
    return "PO"

def rcc_table():
    # derive from small finite universe sets
    U = list(range(4))
    regs = []
    for mask in range(1,1<<len(U)):
        regs.append(frozenset(i for i in U if mask>>i & 1))
    tbl = {(r,s):set() for r in ALL for s in ALL}
    for X in regs:
        for Y in regs:
            r=rel_of(X,Y)
            for Z in regs:
                s=rel_of(Y,Z); t=rel_of(X,Z)
                tbl[(r,s)].add(t)
    return tbl
COMP = rcc_table()

def label_from_choice(n, choices):
    lab = {}
    for i in range(n): lab[(i,i)]="EQ"
    idx=0
    for i in range(n):
        for j in range(i+1,n):
            r=choices[idx]; idx += 1
            lab[(i,j)] = r
            lab[(j,i)] = CONV[r]
    return lab

def is_closed(lab, nodes):
    for x in nodes:
        for y in nodes:
            for z in nodes:
                if lab[(x,z)] not in COMP[(lab[(x,y)], lab[(y,z)])]:
                    return False
    return True

def closed_pockets(n):
    res=[]
    m=n*(n-1)//2
    for choices in product(ATOMS, repeat=m):
        lab=label_from_choice(n, choices)
        if is_closed(lab, list(range(n))):
            res.append(lab)
    return res

def combine(A, B, cross):
    # A nodes 0..a-1, B nodes a..a+b-1
    a = len({i for (i,j) in A if i==j})
    # easier infer B nodes from labels after relabeling externally
    lab={}
    lab.update(A); lab.update(B)
    for (i,j),r in cross.items():
        lab[(i,j)] = r
        lab[(j,i)] = CONV[r]
    return lab

def relabel(lab, offset):
    return {(i+offset,j+offset):r for (i,j),r in lab.items()}

def criterion(A_nodes, B_nodes, lab):
    nodes = A_nodes + B_nodes
    A=set(A_nodes); B=set(B_nodes)
    # initial order and disjointness from all labels (including cross)
    less = {(x,y) for x in nodes for y in nodes if lab[(x,y)]=="PP"}
    # transitive closure
    changed=True
    while changed:
        changed=False
        add=set()
        for x,y in less:
            for u,v in less:
                if y==u and (x,v) not in less:
                    add.add((x,v))
        if add:
            less |= add; changed=True
    # irreflexive
    for x in nodes:
        if (x,x) in less:
            return False, "order_cycle"
    # no new internal order
    for x,y in combinations(A_nodes,2):
        want_xy = lab[(x,y)]=="PP"; want_yx = lab[(y,x)]=="PP"
        if ((x,y) in less) != want_xy or ((y,x) in less) != want_yx:
            return False, "new_internal_order_A"
    for x,y in combinations(B_nodes,2):
        want_xy = lab[(x,y)]=="PP"; want_yx = lab[(y,x)]=="PP"
        if ((x,y) in less) != want_xy or ((y,x) in less) != want_yx:
            return False, "new_internal_order_B"
    # leq relation
    leq = set(less) | {(x,x) for x in nodes}
    # disjoint seeds
    disj = {(x,y) for x in nodes for y in nodes if lab[(x,y)]=="DR"}
    # symmetric already from lab; close downward along less
    changed=True
    while changed:
        changed=False
        add=set()
        for x,y in disj:
            for xp,a in leq:
                if a==x:
                    for yp,b in leq:
                        if b==y:
                            if (xp,yp) not in disj:
                                add.add((xp,yp)); add.add((yp,xp))
        if add:
            disj |= add; changed=True
    # no diagonal disjoint
    for x in nodes:
        if (x,x) in disj:
            return False, "disj_diagonal"
    # no comparable disjoint
    for x,y in nodes and []:
        pass
    for x in nodes:
        for y in nodes:
            if (x,y) in less and (x,y) in disj:
                return False, "comparable_disjoint"
    # no new internal disjointness
    for x,y in combinations(A_nodes,2):
        want = lab[(x,y)]=="DR"
        if ((x,y) in disj) != want:
            return False, "new_internal_disj_A"
    for x,y in combinations(B_nodes,2):
        want = lab[(x,y)]=="DR"
        if ((x,y) in disj) != want:
            return False, "new_internal_disj_B"
    # Need also ensure assigned PO cross is truly residual under closure and assigned PP/PPI/DR match closure.
    for x in nodes:
        for y in nodes:
            if x==y: continue
            derived = "PP" if (x,y) in less else "PPI" if (y,x) in less else "DR" if (x,y) in disj else "PO"
            if derived != lab[(x,y)]:
                return False, f"cross_or_label_changed_{x}_{y}_{lab[(x,y)]}_to_{derived}"
    return True, "ok"

def test_exhaustive_small():
    print("WP83 non-uniform cross-policy characterization")
    print("Criterion: cross order/disjointness closure preserves internal pockets and assigned labels.")
    for a,b in [(1,1),(1,2),(2,1),(2,2),(1,3),(3,1)]:
        As=closed_pockets(a); Bs0=closed_pockets(b)
        total=0; full_ok=0; crit_ok=0; mism=0; first=None
        for A0 in As:
            A=A0
            A_nodes=list(range(a))
            for B0 in Bs0:
                B=relabel(B0, a)
                B_nodes=list(range(a,a+b))
                pairs=[(i,j) for i in A_nodes for j in B_nodes]
                for vals in product(ATOMS, repeat=len(pairs)):
                    cross={p:r for p,r in zip(pairs, vals)}
                    lab=combine(A,B,cross)
                    nodes=A_nodes+B_nodes
                    f=is_closed(lab,nodes)
                    c,why=criterion(A_nodes,B_nodes,lab)
                    total += 1; full_ok += int(f); crit_ok += int(c)
                    if f!=c:
                        mism += 1
                        if first is None: first=(a,b,A0,B0,cross,f,c,why)
        print(f"A={a}, B={b}: total={total} full_ok={full_ok} crit_ok={crit_ok} mismatches={mism}")
        if first:
            print("  first mismatch", first[-3:])
            return False
    return True

def random_closed_ordered(n):
    # generate random sets model for pockets (ordinary finite regions) to get closed networks
    # Use n regions over small atom universe with random subsets, ensure distinct nonempty
    while True:
        m=max(4,n+2)
        regs=[]; seen=set()
        for _ in range(n):
            mask=0
            while mask==0 or mask in seen:
                mask=random.randint(1,(1<<m)-1)
            seen.add(mask); regs.append(frozenset(i for i in range(m) if mask>>i & 1))
        lab={}
        for i in range(n):
            for j in range(n): lab[(i,j)] = rel_of(regs[i],regs[j])
        if all(lab[(i,i)]=="EQ" for i in range(n)) and is_closed(lab,list(range(n))):
            return lab

def test_random():
    random.seed(83)
    tests=0; mism=0
    for a,b in [(3,3),(3,4),(4,3),(4,4),(5,3)]:
        for _ in range(500):
            A0=random_closed_ordered(a); B0=random_closed_ordered(b)
            A=A0; B=relabel(B0,a)
            A_nodes=list(range(a)); B_nodes=list(range(a,a+b)); pairs=[(i,j) for i in A_nodes for j in B_nodes]
            vals=[random.choice(ATOMS) for _ in pairs]
            cross={p:r for p,r in zip(pairs,vals)}
            lab=combine(A,B,cross)
            f=is_closed(lab,A_nodes+B_nodes); c,why=criterion(A_nodes,B_nodes,lab)
            tests += 1
            if f!=c:
                mism += 1
                print("random mismatch",a,b,f,c,why)
                return False
    print(f"random larger tests={tests}, mismatches={mism}")
    return True

if __name__ == "__main__":
    ok1=test_exhaustive_small()
    ok2=test_random()
    if ok1 and ok2:
        print("PASS: arbitrary non-uniform cross policies are characterized by finite order/disjointness closure preservation.")
