#!/usr/bin/env python3
"""
WP49: propagation table for the forall-PO-free regular-template proof.
Derives the RCC5 composition table from finite set semantics and prints
universal-propagation obligations for universals over PP, PPI, and DR.

The point of the probe is small but useful: no propagation rule from a
non-PO universal requires adding a forall-PO obligation. The singleton
rules needed by the (<,#) tree unfolding are exactly the vertical/order
and downward-disjointness rules.
"""
from itertools import combinations, product

ATOMS = ["EQ", "PP", "PPI", "PO", "DR"]
PROPER = ["PP", "PPI", "PO", "DR"]
INV = {"EQ":"EQ", "PP":"PPI", "PPI":"PP", "PO":"PO", "DR":"DR"}

def powerset_nonempty(U):
    U = list(U)
    for r in range(1, len(U)+1):
        for c in combinations(U, r):
            yield frozenset(c)

def rel(a,b):
    if a == b:
        return "EQ"
    if a < b:
        return "PP"
    if a > b:
        return "PPI"
    if a.isdisjoint(b):
        return "DR"
    return "PO"

def derive_comp(n=4):
    U = range(n)
    regs = list(powerset_nonempty(U))
    comp = {(r,s): set() for r in ATOMS for s in ATOMS}
    for x,y,z in product(regs, repeat=3):
        comp[(rel(x,y), rel(y,z))].add(rel(x,z))
    return {k: frozenset(v) for k,v in comp.items()}

comp = derive_comp()
print("RCC5 composition singleton cells among proper atoms:")
for r in PROPER:
    for s in PROPER:
        if len(comp[(r,s)]) == 1:
            print(f"  {r:3s} ; {s:3s} -> {sorted(comp[(r,s)])[0]}")

print("\nPropagation obligations for universals forall R.D with R in {PP,PPI,DR}.")
print("If x satisfies forall R.D and x --S--> y, then y must satisfy:")
print("  D, if S = R; and forall T.D whenever comp(S,T) is a subset of {R}.")
for R in ["PP", "PPI", "DR"]:
    print(f"\nforall {R}.D:")
    any_rule = False
    for S in PROPER:
        reqs = []
        if S == R:
            reqs.append("D")
        for T in PROPER:
            if comp[(S,T)] <= {R}:
                reqs.append(f"forall {T}.D")
        if reqs:
            any_rule = True
            print(f"  across {S:3s}: require {', '.join(reqs)}")
    if not any_rule:
        print("  <no rules>")

print("\nCheck: no non-PO universal propagation requires forall PO.D")
bad = []
for R in ["PP", "PPI", "DR"]:
    for S in PROPER:
        if comp[(S,"PO")] <= {R}:
            bad.append((R,S,"PO",comp[(S,"PO")]))
print("  bad rules:", bad)
assert not bad

print("\nKey singleton rules used by the order/disjointness tree induction:")
for pair in [("PP","PP"),("PPI","PPI"),("PP","DR"),("DR","PPI")]:
    print(f"  {pair[0]} ; {pair[1]} = {set(comp[pair])}")
assert comp[("PP","PP")] == frozenset({"PP"})
assert comp[("PPI","PPI")] == frozenset({"PPI"})
assert comp[("PP","DR")] == frozenset({"DR"})
assert comp[("DR","PPI")] == frozenset({"DR"})
print("\nPASS")
