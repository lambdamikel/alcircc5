#!/usr/bin/env python3
"""
Concrete test of the extension gap: fix the Q3 self-type bug,
run type elimination, then check if the Henkin construction
can get stuck on a satisfiable concept.

Bug found: Q3 enforcement crashes on τ₂=τ₃ triples because DN(τ,τ) may
be empty (EQ is the self-relation but not in DN). The paper's soundness
proof handles this via comp(R₁₂,EQ)={R₁₂}. Fix: skip Q3 for τ₂=τ₃.
"""

from itertools import product

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
        if nc not in cl: cl.add(nc); stack.append(nc)
        if c[0] in ('and', 'or'): stack.extend([c[1], c[2]])
        elif c[0] in ('exists', 'forall'): stack.append(c[2])
    cl.add(TOP); cl.add(BOT)
    return cl

def eval_concept(c, idx, elems, edges):
    if c[0] == 'top': return True
    if c[0] == 'bot': return False
    if c[0] == 'atom': return c[1] in elems[idx]['atoms']
    if c[0] == 'neg': return c[1] not in elems[idx]['atoms']
    if c[0] == 'and': return eval_concept(c[1],idx,elems,edges) and eval_concept(c[2],idx,elems,edges)
    if c[0] == 'or': return eval_concept(c[1],idx,elems,edges) or eval_concept(c[2],idx,elems,edges)
    if c[0] == 'exists':
        return any(edges.get((idx,j))==c[1] and eval_concept(c[2],j,elems,edges) for j in range(len(elems)) if j!=idx)
    if c[0] == 'forall':
        return all(not(edges.get((idx,j))==c[1]) or eval_concept(c[2],j,elems,edges) for j in range(len(elems)) if j!=idx)

def extract_types(elems, edges, cl):
    types = []
    for i in range(len(elems)):
        tau = frozenset(c for c in cl if eval_concept(c, i, elems, edges))
        types.append(tau)
    return types

def is_r_compat(t1, R, t2, cl):
    for c in cl:
        if c[0]=='forall' and c[1]==R and c in t1 and c[2] not in t2: return False
        if c[0]=='forall' and c[1]==INV[R] and c in t2 and c[2] not in t1: return False
    if R==PP:
        for c in cl:
            if c[0]=='forall' and c[1]==PP and c in t1 and c not in t2: return False
            if c[0]=='forall' and c[1]==PPI and c in t2 and c not in t1: return False
    elif R==PPI:
        for c in cl:
            if c[0]=='forall' and c[1]==PPI and c in t1 and c not in t2: return False
            if c[0]=='forall' and c[1]==PP and c in t2 and c not in t1: return False
    return True

def type_elimination_fixed(T_init, cl, c0, verbose=True):
    """Type elimination with FIXED Q3 (skip self-type triples)."""
    T = set(T_init)

    dn_map = {}
    for t1 in T:
        for t2 in T:
            dn_map[(t1,t2)] = frozenset(R for R in RELS if is_r_compat(t1,R,t2,cl))

    P = {(t1,R,t2) for t1 in T for t2 in T for R in dn_map.get((t1,t2),frozenset())}
    if verbose:
        print(f"  Initial: {len(T)} types, {len(P)} pair-types")

    iteration = 0
    changed = True
    while changed:
        changed = False
        iteration += 1

        # Q3 enforcement — FIXED: skip when t2 == t3
        to_remove_p = set()
        for t1 in list(T):
            for t2 in list(T):
                dn12 = dn_map.get((t1,t2), frozenset())
                for r12 in list(dn12):
                    for t3 in list(T):
                        if t2 == t3:
                            continue  # FIX: self-type handled by EQ
                        d13 = dn_map.get((t1,t3), frozenset())
                        d23 = dn_map.get((t2,t3), frozenset())
                        found = any(COMP[(r12,r23)] & d13 for r23 in d23)
                        if not found:
                            to_remove_p.add((t1, r12, t2))

        if to_remove_p:
            P -= to_remove_p
            for t1,r,t2 in to_remove_p:
                if (t1,t2) in dn_map:
                    dn_map[(t1,t2)] = dn_map[(t1,t2)] - frozenset({r})
            changed = True

        # Type elimination (Q1, Q2)
        to_remove_t = set()
        for tau in list(T):
            for c in cl:
                if c[0]=='exists' and c in tau:
                    R, D = c[1], c[2]
                    if not any(D in tp and R in dn_map.get((tau,tp),frozenset())
                               for tp in T):
                        to_remove_t.add(tau); break
            if tau not in to_remove_t:
                for t2 in T:
                    if t2 != tau and not dn_map.get((tau,t2), frozenset()):
                        to_remove_t.add(tau); break

        if to_remove_t:
            T -= to_remove_t
            P = {(t1,r,t2) for (t1,r,t2) in P if t1 in T and t2 in T}
            dn_map = {k:v for k,v in dn_map.items() if k[0] in T and k[1] in T}
            changed = True

    tau0s = [t for t in T if c0 in t]
    if verbose:
        print(f"  After {iteration} iterations: {len(T)} types, {len(P)} pair-types")
        print(f"  τ₀ candidates: {len(tau0s)}")
        print(f"  {'ACCEPTS' if tau0s else 'REJECTS'}")
    return len(tau0s) > 0, T, dn_map, tau0s


def main():
    print("="*70)
    print("Extension Gap: Concrete Test with Fixed Q3")
    print("="*70)

    # === CONCEPT 1: Simple (known satisfiable with 3 elements) ===
    B_filler = AND(atom('B'), FORALL(PO, neg('D')))
    c1 = AND(EXISTS(PO, atom('D')),
             EXISTS(DR, B_filler),
             FORALL(DR, neg('D')),
             FORALL(PP, neg('D')),
             FORALL(PPI, neg('D')))

    print(f"\n--- Concept 1 (simple, satisfiable) ---")
    print(f"C₀ = {concept_str(c1)}")

    # Build known model
    elems = [{'atoms': set()}, {'atoms': {'B'}}, {'atoms': {'D'}}]
    edges = {(0,1):DR,(1,0):DR, (0,2):PO,(2,0):PO, (1,2):DR,(2,1):DR}
    cl1 = closure(c1)
    types1 = extract_types(elems, edges, cl1)

    print(f"  Model: 3 elements, C₀ satisfied: {eval_concept(c1, 0, elems, edges)}")
    print(f"  Running type elimination (fixed Q3)...")
    ok1, T1, dn1, tau0s1 = type_elimination_fixed(set(types1), cl1, c1)

    if ok1:
        print(f"  ✓ ACCEPTS (correctly — concept is satisfiable)")
        # Show DN
        tnames = {t: f"τ{i}" for i,t in enumerate(types1)}
        for t1 in types1:
            for t2 in types1:
                if t1 != t2:
                    dn = dn1.get((t1,t2), frozenset())
                    print(f"    DN({tnames[t1]},{tnames[t2]}) = {set(dn)}")
    else:
        print(f"  ✗ Still rejects! Bug remains.")
        return

    # === CONCEPT 2: The gap concept (forces 4-type triangle) ===
    print(f"\n{'='*70}")
    print(f"--- Concept 2 (targets extension gap) ---")

    # Forces: τ₀ demands DR-neighbor(B), DR-neighbor(C), PO-neighbor(D)
    # where B-type has ∀PO,PP,PPI.¬D → DN(τ₁,τ')={DR}
    # and C-type has ∀DR,PO.¬D → DN(τ₂,τ')={PP,PPI}
    # and B-type demands PO-neighbor(C) → forces τ₁-PO-τ₂

    B_filler2 = AND(atom('B'),
                    FORALL(PO, neg('D')),
                    FORALL(PP, neg('D')),
                    FORALL(PPI, neg('D')),
                    EXISTS(PO, atom('C')))
    C_filler2 = AND(atom('C'),
                    FORALL(DR, neg('D')),
                    FORALL(PO, neg('D')))

    c2 = AND(atom('A'),
             EXISTS(DR, B_filler2),
             EXISTS(DR, C_filler2),
             EXISTS(PO, atom('D')),
             FORALL(DR, neg('D')),
             FORALL(PP, neg('D')),
             FORALL(PPI, neg('D')))

    print(f"C₀ = {concept_str(c2)}")
    cl2 = closure(c2)
    print(f"Closure size: {len(cl2)}")

    # Build the known 5-element model (shown to work earlier)
    # e₀(A), e₁(B), e₂(C), e₂'(C), e₃(D)
    # R: e₀-DR-e₁, e₀-DR-e₂, e₁-PO-e₂', e₀-PO-e₃
    #    e₁-DR-e₂, e₁-DR-e₃, e₂-PP-e₂', e₂-PP-e₃, e₂'-PPI-e₃, e₀-PO-e₂'
    elems2 = [
        {'atoms': {'A'}},      # e₀: root
        {'atoms': {'B'}},      # e₁: B-filler
        {'atoms': {'C'}},      # e₂: C-filler (DR from e₀)
        {'atoms': {'C'}},      # e₂': C-filler (PO from e₁)
        {'atoms': {'D'}},      # e₃: D-element
    ]

    # From the analysis: e₀-DR-e₁, e₀-DR-e₂, e₁-PO-e₂', e₀-PO-e₃
    # e₁-DR-e₂, e₁-DR-e₃, e₂-PP-e₂', e₂-PP-e₃, e₂'-PPI-e₃, e₀-PO-e₂'
    edges2 = {}
    def set_edge(i,j,r):
        edges2[(i,j)] = r
        edges2[(j,i)] = INV[r]
    set_edge(0,1,DR)    # e₀-DR-e₁
    set_edge(0,2,DR)    # e₀-DR-e₂
    set_edge(0,3,PO)    # e₀-PO-e₂'
    set_edge(0,4,PO)    # e₀-PO-e₃
    set_edge(1,2,DR)    # e₁-DR-e₂
    set_edge(1,3,PO)    # e₁-PO-e₂'
    set_edge(1,4,DR)    # e₁-DR-e₃
    set_edge(2,3,PP)    # e₂-PP-e₂'
    set_edge(2,4,PP)    # e₂-PP-e₃
    set_edge(3,4,PPI)   # e₂'-PPI-e₃

    # Verify composition consistency
    print(f"\nModel verification:")
    comp_ok = True
    for i in range(5):
        for j in range(5):
            for k in range(5):
                if len({i,j,k}) == 3:
                    rij = edges2[(i,j)]
                    rjk = edges2[(j,k)]
                    rik = edges2[(i,k)]
                    if rik not in COMP[(rij,rjk)]:
                        print(f"  COMP FAIL: ({i},{j},{k}) {rik}∉comp({rij},{rjk})")
                        comp_ok = False
    print(f"  Composition: {'ALL OK' if comp_ok else 'FAILURES'}")
    print(f"  C₀ at e₀: {eval_concept(c2, 0, elems2, edges2)}")

    if not eval_concept(c2, 0, elems2, edges2):
        # Debug which conjuncts fail
        for sub in [atom('A'),
                    EXISTS(DR, B_filler2),
                    EXISTS(DR, C_filler2),
                    EXISTS(PO, atom('D')),
                    FORALL(DR, neg('D')),
                    FORALL(PP, neg('D')),
                    FORALL(PPI, neg('D'))]:
            print(f"    {concept_str(sub)}: {eval_concept(sub, 0, elems2, edges2)}")
        # Check B_filler at e₁
        print(f"  B_filler at e₁: {eval_concept(B_filler2, 1, elems2, edges2)}")
        for sub in [atom('B'), FORALL(PO,neg('D')), FORALL(PP,neg('D')),
                    FORALL(PPI,neg('D')), EXISTS(PO,atom('C'))]:
            print(f"    {concept_str(sub)}: {eval_concept(sub, 1, elems2, edges2)}")

    if comp_ok and eval_concept(c2, 0, elems2, edges2):
        # Extract types and run elimination
        types2 = extract_types(elems2, edges2, cl2)
        distinct = list(set(types2))
        print(f"  Distinct types: {len(distinct)}")

        # Name types by their markers
        for i, tau in enumerate(types2):
            markers = []
            for m in ['A','B','C','D']:
                if atom(m) in tau: markers.append(m)
                elif neg(m) in tau: markers.append(f'¬{m}')
            print(f"    e{i}: {markers}")

        print(f"\n  Running type elimination (fixed Q3)...")
        ok2, T2, dn2, tau0s2 = type_elimination_fixed(set(distinct), cl2, c2)

        if ok2:
            print(f"\n  ✓ ACCEPTS")
            # Show DN for the critical pattern
            tmap = {}
            for t in T2:
                markers = []
                for m in ['A','B','C','D']:
                    if atom(m) in t: markers.append(m)
                tmap[t] = ','.join(markers) if markers else '?'

            print(f"\n  DN matrix (surviving types):")
            for t1 in sorted(T2, key=lambda t: tmap[t]):
                for t2 in sorted(T2, key=lambda t: tmap[t]):
                    if t1 != t2:
                        dn = dn2.get((t1,t2), frozenset())
                        print(f"    DN({tmap[t1]:5s},{tmap[t2]:5s}) = {set(dn)}")

            # NOW: try Henkin construction (greedy)
            print(f"\n  Attempting Henkin construction (greedy)...")
            henkin_test(T2, dn2, tau0s2[0], cl2)

            # Also: try to find the 4-element deadlock
            print(f"\n  Checking for 4-element deadlock pattern...")
            check_deadlock(T2, dn2, tmap)
        else:
            print(f"\n  ✗ REJECTS")
    else:
        print(f"\n  Model invalid — need to fix")


def henkin_test(T, dn, tau0, cl, max_steps=20):
    """Greedy Henkin construction."""
    elems = [(tau0, 'e0')]
    edges = {}

    for step in range(max_steps):
        # Find unsatisfied demand
        demand = None
        for idx, (tau, name) in enumerate(elems):
            for c in cl:
                if c[0]=='exists' and c in tau:
                    R, D = c[1], c[2]
                    witnessed = any(edges.get((idx,j))==R and D in elems[j][0]
                                   for j in range(len(elems)) if j!=idx)
                    if not witnessed:
                        demand = (idx, R, D)
                        break
            if demand: break

        if not demand:
            print(f"    All demands satisfied! Model: {len(elems)} elements")
            return True

        idx, R, D = demand
        m = len(elems)

        # Find witness types and try extensions
        success = False
        for wt in T:
            if D not in wt: continue
            if R not in dn.get((elems[idx][0], wt), frozenset()): continue

            # Compute domains
            domains = []
            valid = True
            for j in range(m):
                if j == idx:
                    domains.append([R])
                else:
                    d = list(dn.get((elems[j][0], wt), frozenset()))
                    if not d: valid = False; break
                    domains.append(d)
            if not valid: continue

            # Try assignments
            for asgn in product(*domains):
                ok = True
                for i in range(m):
                    for j in range(i+1, m):
                        rij = edges[(i,j)]
                        si, sj = asgn[i], asgn[j]
                        if si not in COMP[(rij, sj)]:
                            ok = False; break
                    if not ok: break
                if ok:
                    new_name = f'e{m}'
                    elems.append((wt, new_name))
                    for i in range(m):
                        edges[(i,m)] = asgn[i]
                        edges[(m,i)] = INV[asgn[i]]
                    markers = [x for x in ['A','B','C','D'] if atom(x) in wt]
                    print(f"    Step {step+1}: {new_name}({markers}) "
                          f"as {R}-witness for e{idx}, "
                          f"assignment={asgn}")
                    success = True
                    break
            if success: break

        if not success:
            print(f"    Step {step+1}: EXTENSION FAILURE for demand at e{idx}")
            print(f"      Need {R}-neighbor with {concept_str(('exists',R,D))[1:]}")
            return False

    print(f"    Reached max steps")
    return False


def check_deadlock(T, dn, tmap):
    """Check if the 4-type deadlock pattern exists among surviving types."""
    # Look for types where DN to a D-type is narrow
    d_types = [t for t in T if atom('D') in t]
    nd_types = [t for t in T if atom('D') not in t]

    for td in d_types:
        td_name = tmap[td]
        narrow = []
        for t in T:
            if t == td: continue
            d = dn.get((t, td), frozenset())
            if len(d) <= 2:
                narrow.append((t, d))

        if narrow:
            print(f"    Narrow DN to {td_name}-type:")
            for t, d in narrow:
                print(f"      DN({tmap[t]},{td_name}) = {set(d)}")

            # Check if any triple among narrow-DN types creates the deadlock
            for i in range(len(narrow)):
                for j in range(i+1, len(narrow)):
                    t1, d1 = narrow[i]
                    t2, d2 = narrow[j]
                    dn12 = dn.get((t1, t2), frozenset())
                    # For each base relation between t1,t2
                    for r12 in dn12:
                        # Check: can we find s1∈d1, s2∈d2 with s1∈comp(r12,s2)?
                        pair_ok = any(s1 in COMP[(r12,s2)]
                                     for s1 in d1 for s2 in d2)
                        if not pair_ok:
                            continue  # this r12 isn't even pairwise sat
                        # Check global: any (s1,s2) ∈ d1×d2 consistent?
                        glob_ok = any(s1 in COMP[(r12,s2)]
                                     for s1 in d1 for s2 in d2)
                        if pair_ok and not glob_ok:
                            print(f"    DEADLOCK: {tmap[t1]}-{r12}-{tmap[t2]}, "
                                  f"DN1={set(d1)}, DN2={set(d2)}")

            # More thorough: check 3-type patterns
            for i in range(len(narrow)):
                for j in range(len(narrow)):
                    for k in range(len(narrow)):
                        if i==j or i==k or j==k: continue
                        t0, d0 = narrow[i]
                        t1, d1 = narrow[j]
                        t2, d2 = narrow[k]
                        r01 = dn.get((t0,t1), frozenset())
                        r02 = dn.get((t0,t2), frozenset())
                        r12 = dn.get((t1,t2), frozenset())
                        # For each base triple
                        for R01 in r01:
                            for R02 in r02:
                                for R12 in r12:
                                    if R02 not in COMP[(R01,R12)]: continue
                                    # This is a valid base triple
                                    # Check star extension
                                    pw_ok = True
                                    for di, dj, rij in [(d0,d1,R01),(d0,d2,R02),(d1,d2,R12)]:
                                        if not any(si in COMP[(rij,sj)]
                                                  for si in di for sj in dj):
                                            pw_ok = False; break
                                    if not pw_ok: continue

                                    glob_ok = False
                                    for s0 in d0:
                                        for s1 in d1:
                                            for s2 in d2:
                                                if (s0 in COMP[(R01,s1)] and
                                                    s0 in COMP[(R02,s2)] and
                                                    s1 in COMP[(R12,s2)]):
                                                    glob_ok = True
                                                    break
                                            if glob_ok: break
                                        if glob_ok: break

                                    if pw_ok and not glob_ok:
                                        print(f"\n    *** EXTENSION GAP REALIZED ***")
                                        print(f"    Types: {tmap[t0]}, {tmap[t1]}, {tmap[t2]} → {td_name}")
                                        print(f"    Base: R01={R01}, R02={R02}, R12={R12}")
                                        print(f"    DN to new: {set(d0)}, {set(d1)}, {set(d2)}")
                                        print(f"    Pairwise satisfiable: YES")
                                        print(f"    Globally satisfiable: NO")


if __name__ == '__main__':
    main()
