#!/usr/bin/env python3
"""WP50: Full-logic PO-guard analysis for ALCI_RCC5 regular-template route.

This probe derives the RCC5 table from finite set semantics, computes universal
propagation rules of the form:

  if x satisfies forall R.D and x S y, what must y satisfy?

and isolates the special role of forall PO: it imposes only immediate
PO-neighbour type compatibility; it does not propagate to another universal
along any proper RCC5 atom.

It also gives a tiny finite type-level example showing why residual PO edges
must be guarded in the full logic.
"""
from itertools import combinations, product

ATOMS = ["EQ", "DR", "PO", "PP", "PPI"]
PROPER = ["DR", "PO", "PP", "PPI"]
INV = {"EQ":"EQ", "DR":"DR", "PO":"PO", "PP":"PPI", "PPI":"PP"}

# Generate non-empty subsets of a small universe as concrete regions.
U = frozenset(range(4))
REGIONS = [frozenset(s) for r in range(1, len(U)+1) for s in combinations(U, r)]

def rel(a,b):
    if a == b:
        return "EQ"
    if a.isdisjoint(b):
        return "DR"
    if a < b:
        return "PP"
    if b < a:
        return "PPI"
    return "PO"

# Derive composition table.
COMP = {(r,s): set() for r in ATOMS for s in ATOMS}
for x,y,z in product(REGIONS, repeat=3):
    COMP[(rel(x,y), rel(y,z))].add(rel(x,z))

print("RCC5 composition table (proper atoms only):")
for r in PROPER:
    for s in PROPER:
        print(f"  comp({r:3},{s:3}) = {{{','.join(sorted(COMP[(r,s)]))}}}")

# Universal propagation.
# If x has forall R.D and x S y:
# - if S == R, y must have D.
# - for any T with comp(S,T) subset {R}, y must have forall T.D.
print("\nUniversal propagation rules for proper roles:")
for R in PROPER:
    print(f"forall {R}.D:")
    any_rule = False
    for S in PROPER:
        reqs = []
        if S == R:
            reqs.append("D")
        for T in PROPER:
            if COMP[(S,T)] == {R}:
                reqs.append(f"forall {T}.D")
        if reqs:
            any_rule = True
            print(f"  across {S:3}: require {', '.join(reqs)}")
    if not any_rule:
        print("  (no proper-edge propagation)")

po_univ_props = []
for S in PROPER:
    for T in PROPER:
        if COMP[(S,T)] == {"PO"}:
            po_univ_props.append((S,T))
print("\nSingleton propagations into PO:", po_univ_props)
print("Conclusion: forall PO.D has only immediate PO-neighbour constraint; no forall T.D propagation over proper atoms.")

# Tiny type compatibility demo.
# Type A has forall PO.G; Type B lacks G. Then A-B cannot be PO. If a free
# tree/template leaves them unrelated and non-disjoint, residual PO violates.
print("\nTiny residual-PO guard demo:")
print("  Type A contains forall PO.G; type B omits G.")
print("  Therefore an A--B pair is PO-unsafe and must be guarded by PP, PPI, or DR.")

def allowed_atom(src_univ, tgt_type, atom):
    # src_univ is a dict R -> set of required concept names for forall R.
    # tgt_type is a set of concept names.
    return src_univ.get(atom, set()).issubset(tgt_type)

A_univ = {"PO": {"G"}}
B_type = set()
for atom in PROPER:
    ok_forward = allowed_atom(A_univ, B_type, atom)
    print(f"  A --{atom:3}--> B forward-universal safe? {ok_forward}")
print("  residual PO is rejected; DR/PP/PPI remain possible only if their own universals allow them.")

# Guarding choices as <,#:
print("\nGuard interpretation in <,# normal form:")
print("  PP/PPI guard: make the pair comparable in the generated strict order <.")
print("  DR guard: put the pair into downward-closed disjointness #.")
print("  PO: residual, allowed only when both endpoint types satisfy each other's forall PO demands.")
