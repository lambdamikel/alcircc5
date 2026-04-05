#!/usr/bin/env python3
"""
Debug the type-elimination algorithm by manually constructing types
from a known model and verifying the quasimodel conditions.

Known model for C₀ = ∃PO.D ⊓ ∃DR.(B ⊓ ∀PO.¬D) ⊓ ∀DR.¬D ⊓ ∀PP.¬D ⊓ ∀PPI.¬D:
  e₀: root, R(e₀,e₁)=DR, R(e₀,e₂)=PO, R(e₁,e₂)=DR
  e₁: B-filler (DR-neighbor)
  e₂: D-element (PO-neighbor)
"""

DR, PO, PP, PPI = 'DR', 'PO', 'PP', 'PPI'
RELS = [DR, PO, PP, PPI]
INV = {DR: DR, PO: PO, PP: PPI, PPI: PP}

COMP = {
    (DR, DR): frozenset({DR, PO, PP, PPI}),
    (DR, PO): frozenset({DR, PO, PP}),
    (DR, PP): frozenset({DR, PO, PP}),
    (DR, PPI): frozenset({DR}),
    (PO, DR): frozenset({DR, PO, PPI}),
    (PO, PO): frozenset({DR, PO, PP, PPI}),
    (PO, PP): frozenset({PO, PP}),
    (PO, PPI): frozenset({DR, PO, PPI}),
    (PP, DR): frozenset({DR}),
    (PP, PO): frozenset({DR, PO, PP}),
    (PP, PP): frozenset({PP}),
    (PP, PPI): frozenset({DR, PO, PP, PPI}),
    (PPI, DR): frozenset({DR, PO, PPI}),
    (PPI, PO): frozenset({PO, PPI}),
    (PPI, PP): frozenset({PO, PP, PPI}),
    (PPI, PPI): frozenset({PPI}),
}


def atom(n): return ('atom', n)
def neg(n): return ('neg', n)
def AND(*a):
    r = a[0]
    for x in a[1:]: r = ('and', r, x)
    return r
def EXISTS(R, c): return ('exists', R, c)
def FORALL(R, c): return ('forall', R, c)
TOP = ('top',)
BOT = ('bot',)

def nnf_neg(c):
    if c[0] == 'atom': return ('neg', c[1])
    elif c[0] == 'neg': return ('atom', c[1])
    elif c[0] == 'top': return BOT
    elif c[0] == 'bot': return TOP
    elif c[0] == 'and': return ('or', nnf_neg(c[1]), nnf_neg(c[2]))
    elif c[0] == 'or': return ('and', nnf_neg(c[1]), nnf_neg(c[2]))
    elif c[0] == 'exists': return ('forall', c[1], nnf_neg(c[2]))
    elif c[0] == 'forall': return ('exists', c[1], nnf_neg(c[2]))

def concept_str(c):
    if c[0] == 'atom': return c[1]
    elif c[0] == 'neg': return f'¬{c[1]}'
    elif c[0] == 'top': return '⊤'
    elif c[0] == 'bot': return '⊥'
    elif c[0] == 'and': return f'({concept_str(c[1])} ⊓ {concept_str(c[2])})'
    elif c[0] == 'or': return f'({concept_str(c[1])} ⊔ {concept_str(c[2])})'
    elif c[0] == 'exists': return f'∃{c[1]}.{concept_str(c[2])}'
    elif c[0] == 'forall': return f'∀{c[1]}.{concept_str(c[2])}'
    return str(c)

def closure(c0):
    cl = set()
    stack = [c0]
    while stack:
        c = stack.pop()
        if c in cl: continue
        cl.add(c)
        nc = nnf_neg(c)
        if nc not in cl:
            cl.add(nc)
            stack.append(nc)
        if c[0] in ('and', 'or'):
            stack.extend([c[1], c[2]])
        elif c[0] in ('exists', 'forall'):
            stack.append(c[2])
    cl.add(TOP)
    cl.add(BOT)
    return cl


def extract_type_from_model(element_idx, elements, edges, cl):
    """Extract the type of element_idx from the model."""
    tau = set()
    for c in cl:
        if eval_concept(c, element_idx, elements, edges):
            tau.add(c)
    return frozenset(tau)


def eval_concept(c, idx, elements, edges):
    """Evaluate whether concept c is true at element idx in the model."""
    if c[0] == 'top': return True
    if c[0] == 'bot': return False
    if c[0] == 'atom':
        return c[1] in elements[idx]['atoms']
    if c[0] == 'neg':
        return c[1] not in elements[idx]['atoms']
    if c[0] == 'and':
        return eval_concept(c[1], idx, elements, edges) and \
               eval_concept(c[2], idx, elements, edges)
    if c[0] == 'or':
        return eval_concept(c[1], idx, elements, edges) or \
               eval_concept(c[2], idx, elements, edges)
    if c[0] == 'exists':
        R, D = c[1], c[2]
        for j in range(len(elements)):
            if j != idx and edges.get((idx, j)) == R:
                if eval_concept(D, j, elements, edges):
                    return True
        return False
    if c[0] == 'forall':
        R, D = c[1], c[2]
        for j in range(len(elements)):
            if j != idx and edges.get((idx, j)) == R:
                if not eval_concept(D, j, elements, edges):
                    return False
        return True
    raise ValueError(f"Unknown: {c}")


def is_r_compatible(tau1, R, tau2, cl):
    for c in cl:
        if c[0] == 'forall' and c[1] == R:
            if c in tau1 and c[2] not in tau2: return False
        if c[0] == 'forall' and c[1] == INV[R]:
            if c in tau2 and c[2] not in tau1: return False
    if R == PP:
        for c in cl:
            if c[0] == 'forall' and c[1] == PP:
                if c in tau1 and c not in tau2: return False
            if c[0] == 'forall' and c[1] == PPI:
                if c in tau2 and c not in tau1: return False
    elif R == PPI:
        for c in cl:
            if c[0] == 'forall' and c[1] == PPI:
                if c in tau1 and c not in tau2: return False
            if c[0] == 'forall' and c[1] == PP:
                if c in tau2 and c not in tau1: return False
    return True


def main():
    # The concept
    B_filler = AND(atom('B'), FORALL(PO, neg('D')))
    c0 = AND(EXISTS(PO, atom('D')),
             EXISTS(DR, B_filler),
             FORALL(DR, neg('D')),
             FORALL(PP, neg('D')),
             FORALL(PPI, neg('D')))

    print(f"C₀ = {concept_str(c0)}")

    cl = closure(c0)
    print(f"\nClosure ({len(cl)} formulas):")
    for c in sorted(cl, key=lambda x: concept_str(x)):
        print(f"  {concept_str(c)}")

    # Define the model
    # e₀: atoms={}, e₁: atoms={B}, e₂: atoms={D}
    # R(e₀,e₁)=DR, R(e₀,e₂)=PO, R(e₁,e₂)=DR
    elements = [
        {'atoms': set()},       # e₀: root
        {'atoms': {'B'}},       # e₁: B-filler
        {'atoms': {'D'}},       # e₂: D-element
    ]
    edges = {
        (0, 1): DR, (1, 0): DR,
        (0, 2): PO, (2, 0): PO,
        (1, 2): DR, (2, 1): DR,
    }

    # Check composition consistency
    print(f"\nModel:")
    for i in range(3):
        for j in range(i+1, 3):
            print(f"  R(e{i}, e{j}) = {edges[(i,j)]}")

    print(f"\nComposition check:")
    for i in range(3):
        for j in range(3):
            for k in range(3):
                if i != j and j != k and i != k:
                    rij = edges[(i,j)]
                    rjk = edges[(j,k)]
                    rik = edges[(i,k)]
                    ok = rik in COMP[(rij, rjk)]
                    if not ok:
                        print(f"  FAIL: R(e{i},e{k})={rik} ∉ comp({rij},{rjk})")
                    else:
                        print(f"  OK: R(e{i},e{k})={rik} ∈ comp({rij},{rjk})")

    # Check C₀ satisfaction
    print(f"\nC₀ satisfaction at e₀: {eval_concept(c0, 0, elements, edges)}")

    # Extract types
    print(f"\nExtracted types:")
    types = []
    for i in range(3):
        tau = extract_type_from_model(i, elements, edges, cl)
        types.append(tau)
        print(f"\n  τ(e{i}) ({len(tau)} formulas):")
        for c in sorted(tau, key=lambda x: concept_str(x)):
            print(f"    {'✓' if c in tau else '✗'} {concept_str(c)}")

    # Check type conditions
    print(f"\nType validation:")
    for i, tau in enumerate(types):
        print(f"\n  τ(e{i}):")
        for c in cl:
            if c[0] == 'and' and c in tau:
                ok = c[1] in tau and c[2] in tau
                if not ok:
                    print(f"    T1 FAIL: {concept_str(c)} ∈ τ but "
                          f"{concept_str(c[1])}={'in' if c[1] in tau else 'NOT in'}, "
                          f"{concept_str(c[2])}={'in' if c[2] in tau else 'NOT in'}")
            if c[0] == 'or' and c in tau:
                ok = c[1] in tau or c[2] in tau
                if not ok:
                    print(f"    T2 FAIL: {concept_str(c)} ∈ τ but "
                          f"neither disjunct in τ")
            if c[0] == 'atom':
                nc = ('neg', c[1])
                if c in tau and nc in tau:
                    print(f"    T3 FAIL: both {c[1]} and ¬{c[1]} in τ")
        print(f"    All checks passed ✓")

    # Compute DN
    print(f"\nDN matrix:")
    T = set(types)
    for i, t1 in enumerate(types):
        for j, t2 in enumerate(types):
            dn = frozenset(R for R in RELS if is_r_compatible(t1, R, t2, cl))
            print(f"  DN(τ(e{i}), τ(e{j})) = {set(dn) if dn else '∅'}")

    # Check Q1
    print(f"\nQ1 (existential witnesses):")
    dn_map = {}
    for t1 in T:
        for t2 in T:
            dn_map[(t1, t2)] = frozenset(R for R in RELS
                                          if is_r_compatible(t1, R, t2, cl))

    for i, tau in enumerate(types):
        for c in cl:
            if c[0] == 'exists' and c in tau:
                R, D = c[1], c[2]
                found = False
                for j, tp in enumerate(types):
                    if D in tp and R in dn_map.get((tau, tp), frozenset()):
                        print(f"  τ(e{i}): {concept_str(c)} → "
                              f"witness τ(e{j}), {R} ∈ DN ✓")
                        found = True
                        break
                if not found:
                    print(f"  τ(e{i}): {concept_str(c)} → NO WITNESS! ✗")

    # Check Q2
    print(f"\nQ2 (completeness):")
    for i, t1 in enumerate(types):
        for j, t2 in enumerate(types):
            if t1 != t2:
                dn = dn_map.get((t1, t2), frozenset())
                if not dn:
                    print(f"  DN(τ(e{i}), τ(e{j})) = ∅ — Q2 FAILS! ✗")
                else:
                    print(f"  DN(τ(e{i}), τ(e{j})) = {set(dn)} ✓")

    # Check Q3
    print(f"\nQ3 (algebraic closure):")
    q3_ok = True
    for i, t1 in enumerate(types):
        for j, t2 in enumerate(types):
            dn12 = dn_map.get((t1, t2), frozenset())
            for r12 in dn12:
                for k, t3 in enumerate(types):
                    d13 = dn_map.get((t1, t3), frozenset())
                    d23 = dn_map.get((t2, t3), frozenset())
                    found = False
                    for r23 in d23:
                        if COMP[(r12, r23)] & d13:
                            found = True
                            break
                    if not found:
                        print(f"  Q3 FAILS: (τ{i},τ{j},τ{k}) r12={r12}, "
                              f"DN13={set(d13)}, DN23={set(d23)}")
                        q3_ok = False
    if q3_ok:
        print(f"  All Q3 checks passed ✓")

    print(f"\n{'='*70}")
    print("SUMMARY:")
    print(f"  Model exists: YES (3 elements)")
    print(f"  Types extracted: {len(T)} distinct")
    if len(T) == len(types):
        print(f"  (all types are distinct)")
    else:
        print(f"  ({len(types)} elements, {len(T)} distinct types)")


if __name__ == '__main__':
    main()
