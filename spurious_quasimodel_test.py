#!/usr/bin/env python3
"""
Attempt to construct a concrete ALCI_RCC5 concept that produces a
spurious quasimodel — accepted by type-elimination but unsatisfiable.

Uses smart type enumeration (backtracking, not brute force).
"""

import sys
from itertools import product
from collections import defaultdict

# ── RCC5 basics ──────────────────────────────────────────────────────

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


def comp(r, s):
    return COMP[(r, s)]


# ── Concept representation ──────────────────────────────────────────

def atom(name): return ('atom', name)
def neg(name): return ('neg', name)
def AND(*args):
    result = args[0]
    for a in args[1:]: result = ('and', result, a)
    return result
def OR(*args):
    result = args[0]
    for a in args[1:]: result = ('or', result, a)
    return result
def EXISTS(R, c): return ('exists', R, c)
def FORALL(R, c): return ('forall', R, c)
TOP = ('top',)
BOT = ('bot',)


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


def nnf_neg(c):
    if c[0] == 'atom': return ('neg', c[1])
    elif c[0] == 'neg': return ('atom', c[1])
    elif c[0] == 'top': return BOT
    elif c[0] == 'bot': return TOP
    elif c[0] == 'and': return ('or', nnf_neg(c[1]), nnf_neg(c[2]))
    elif c[0] == 'or': return ('and', nnf_neg(c[1]), nnf_neg(c[2]))
    elif c[0] == 'exists': return ('forall', c[1], nnf_neg(c[2]))
    elif c[0] == 'forall': return ('exists', c[1], nnf_neg(c[2]))
    raise ValueError(f"Cannot negate: {c}")


def closure(c0):
    cl = set()
    stack = [c0]
    while stack:
        c = stack.pop()
        if c in cl:
            continue
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


def enumerate_types_smart(cl):
    """Smart type enumeration using backtracking.

    Decision points: atoms (A vs ¬A) and disjunctions (pick a disjunct).
    Everything else is propagated deterministically.
    """
    cl_list = sorted(cl, key=str)
    types = []

    # Identify decision points
    atoms = set()
    for c in cl:
        if c[0] == 'atom':
            atoms.add(c[1])

    # For each combination of atom polarities, propagate and check
    atom_list = sorted(atoms)
    n_atoms = len(atom_list)

    # Also identify disjunctions
    disjs = [c for c in cl if c[0] == 'or']

    def propagate(tau, cl):
        """Propagate deterministic constraints. Returns None if inconsistent."""
        changed = True
        while changed:
            changed = False
            for c in cl:
                if c[0] == 'top' and c not in tau:
                    tau = tau | {c}
                    changed = True
                elif c[0] == 'bot' and c in tau:
                    return None
                elif c[0] == 'and' and c in tau:
                    if c[1] not in tau:
                        tau = tau | {c[1]}
                        changed = True
                    if c[2] not in tau:
                        tau = tau | {c[2]}
                        changed = True
                elif c[0] == 'atom' and c in tau:
                    nc = ('neg', c[1])
                    if nc in cl and nc in tau:
                        return None
                elif c[0] == 'neg' and c in tau:
                    ac = ('atom', c[1])
                    if ac in cl and ac in tau:
                        return None
        return tau

    def backtrack(tau, remaining_disjs, cl):
        """Backtracking search over disjunction choices."""
        tau = propagate(tau, cl)
        if tau is None:
            return

        # Find first undecided disjunction in tau
        for c in remaining_disjs:
            if c in tau and c[1] not in tau and c[2] not in tau:
                # Must choose: include c[1] or c[2] (or both)
                # Try c[1]
                rest = [d for d in remaining_disjs if d != c]
                backtrack(tau | {c[1]}, rest, cl)
                # Try c[2]
                backtrack(tau | {c[2]}, rest, cl)
                return

        # No undecided disjunctions — check if tau is a valid type
        # Add all formulas that must be present
        final_tau = set(tau)
        for c in cl:
            if c[0] == 'or' and c not in final_tau:
                # Check if either disjunct forces it
                if c[1] in final_tau or c[2] in final_tau:
                    final_tau.add(c)

        # Verify all type conditions
        valid = True
        for c in cl:
            if c[0] == 'and':
                if c in final_tau:
                    if c[1] not in final_tau or c[2] not in final_tau:
                        valid = False
                        break
                # If both conjuncts present, conjunction should be too
                if c[1] in final_tau and c[2] in final_tau and c not in final_tau:
                    # This is an open question — should we force it?
                    # Actually types are not required to contain all consequences,
                    # just the formulas from the closure that are "true"
                    # Let me re-think...
                    pass
            elif c[0] == 'or':
                if c in final_tau:
                    if c[1] not in final_tau and c[2] not in final_tau:
                        valid = False
                        break
            elif c[0] == 'atom':
                nc = ('neg', c[1])
                if nc in cl and c in final_tau and nc in final_tau:
                    valid = False
                    break

        if valid:
            types.append(frozenset(final_tau))

    # For each atom polarity combination
    for atom_mask in range(1 << n_atoms):
        base = {TOP}
        for i, a in enumerate(atom_list):
            if atom_mask & (1 << i):
                base.add(('atom', a))
            else:
                neg_c = ('neg', a)
                if neg_c in cl:
                    base.add(neg_c)

        backtrack(frozenset(base), disjs, cl)

    # Deduplicate
    types = list(set(types))
    return types


def enumerate_types_complete(cl):
    """Complete type enumeration: a type is a MAXIMAL consistent subset
    of cl satisfying T1-T3.

    More precisely: for every formula in cl, either it or its negation
    is in the type (maximality). Plus T1 (and-closure), T2 (or-witness),
    T3 (no contradictions).
    """
    types = []
    cl_list = sorted(cl, key=str)

    # Decision points: for each pair {c, nnf_neg(c)}, choose one
    pairs = []
    seen = set()
    for c in cl_list:
        if c in seen:
            continue
        nc = nnf_neg(c)
        if nc == c:  # self-dual (shouldn't happen for proper concepts)
            seen.add(c)
            continue
        if nc in seen:
            continue
        # Skip top/bot — always determined
        if c[0] == 'top' or c[0] == 'bot':
            seen.add(c)
            if nc in cl:
                seen.add(nc)
            continue
        pairs.append((c, nc))
        seen.add(c)
        seen.add(nc)

    print(f"    Decision pairs: {len(pairs)}")
    if len(pairs) > 20:
        print(f"    Too many decisions for brute force ({2**len(pairs)} combinations)")
        return []

    # Try all combinations
    for mask in range(1 << len(pairs)):
        tau = {TOP}
        for i, (c, nc) in enumerate(pairs):
            if mask & (1 << i):
                tau.add(c)
                # Don't add nc
            else:
                if nc in cl:
                    tau.add(nc)
                # Don't add c

        # Propagate: add consequences
        changed = True
        consistent = True
        while changed and consistent:
            changed = False
            for c in cl:
                if c[0] == 'and' and c in tau:
                    for sub in [c[1], c[2]]:
                        if sub not in tau:
                            tau.add(sub)
                            changed = True
                            # Check for contradiction
                            nsub = nnf_neg(sub)
                            if nsub in tau:
                                consistent = False
                                break
                    if not consistent:
                        break
                elif c[0] == 'or' and c[1] in tau and c[2] in tau:
                    if c not in tau:
                        tau.add(c)
                        changed = True
                elif c[0] == 'or' and c[1] in tau and c not in tau:
                    tau.add(c)
                    changed = True
                elif c[0] == 'or' and c[2] in tau and c not in tau:
                    tau.add(c)
                    changed = True
                elif c[0] == 'and' and c[1] in tau and c[2] in tau and c not in tau:
                    tau.add(c)
                    changed = True

        if not consistent:
            continue

        # Check T1-T3
        valid = True
        for c in cl:
            if c[0] == 'and' and c in tau:
                if c[1] not in tau or c[2] not in tau:
                    valid = False
                    break
            if c[0] == 'or' and c in tau:
                if c[1] not in tau and c[2] not in tau:
                    valid = False
                    break
            if c[0] == 'atom':
                nc = ('neg', c[1])
                if nc in cl and c in tau and nc in tau:
                    valid = False
                    break
            if c[0] == 'bot' and c in tau:
                valid = False
                break

        if valid:
            types.append(frozenset(tau))

    return list(set(types))


def is_r_compatible(tau1, R, tau2, cl):
    """Check (P1), (P2), (P1'), (P2')."""
    for c in cl:
        if c[0] == 'forall' and c[1] == R:
            if c in tau1 and c[2] not in tau2:
                return False
        if c[0] == 'forall' and c[1] == INV[R]:
            if c in tau2 and c[2] not in tau1:
                return False

    if R == PP:
        for c in cl:
            if c[0] == 'forall' and c[1] == PP:
                if c in tau1 and c not in tau2:
                    return False
            if c[0] == 'forall' and c[1] == PPI:
                if c in tau2 and c not in tau1:
                    return False
    elif R == PPI:
        for c in cl:
            if c[0] == 'forall' and c[1] == PPI:
                if c in tau1 and c not in tau2:
                    return False
            if c[0] == 'forall' and c[1] == PP:
                if c in tau2 and c not in tau1:
                    return False

    return True


def type_elimination(c0, verbose=True):
    """Full type-elimination algorithm."""
    cl = closure(c0)
    if verbose:
        print(f"  Closure size: {len(cl)}")
        for c in sorted(cl, key=str):
            print(f"    {concept_str(c)}")

    all_types = enumerate_types_complete(cl)
    if verbose:
        print(f"  Types: {len(all_types)}")

    T = set(all_types)

    # Compute DN
    dn_map = {}
    for t1 in T:
        for t2 in T:
            dn = frozenset(R for R in RELS if is_r_compatible(t1, R, t2, cl))
            dn_map[(t1, t2)] = dn

    P = {(t1, R, t2) for t1 in T for t2 in T
         for R in dn_map.get((t1, t2), frozenset())}
    if verbose:
        print(f"  Initial pair-types: {len(P)}")

    # Iterative elimination
    iteration = 0
    changed = True
    while changed:
        changed = False
        iteration += 1

        # Q3 enforcement
        to_remove_p = set()
        for t1 in list(T):
            for t2 in list(T):
                dn12 = dn_map.get((t1, t2), frozenset())
                for r12 in list(dn12):
                    for t3 in list(T):
                        d13 = dn_map.get((t1, t3), frozenset())
                        d23 = dn_map.get((t2, t3), frozenset())
                        found = False
                        for r23 in d23:
                            if comp(r12, r23) & d13:
                                found = True
                                break
                        if not found:
                            to_remove_p.add((t1, r12, t2))

        if to_remove_p:
            P -= to_remove_p
            for t1, r, t2 in to_remove_p:
                if (t1, t2) in dn_map:
                    dn_map[(t1, t2)] = dn_map[(t1, t2)] - frozenset({r})
            changed = True

        # Type elimination
        to_remove_t = set()
        for tau in list(T):
            # Q1
            for c in cl:
                if c[0] == 'exists' and c in tau:
                    R, D = c[1], c[2]
                    found = False
                    for tp in T:
                        if D in tp and R in dn_map.get((tau, tp), frozenset()):
                            found = True
                            break
                    if not found:
                        to_remove_t.add(tau)
                        break

            if tau not in to_remove_t:
                for t2 in T:
                    if t2 != tau and not dn_map.get((tau, t2), frozenset()):
                        to_remove_t.add(tau)
                        break

        if to_remove_t:
            T -= to_remove_t
            P = {(t1, r, t2) for (t1, r, t2) in P if t1 in T and t2 in T}
            dn_map = {k: v for k, v in dn_map.items() if k[0] in T and k[1] in T}
            changed = True

    tau0s = [tau for tau in T if c0 in tau]
    accepted = len(tau0s) > 0

    if verbose:
        print(f"  After elimination ({iteration} iters):")
        print(f"    Types: {len(T)}, Pair-types: {len(P)}")
        print(f"    τ₀ candidates: {len(tau0s)}")
        print(f"    {'ACCEPTS' if accepted else 'REJECTS'}")

    return accepted, T, P, dn_map, tau0s, cl


def try_build_model(T, dn_map, tau0, cl, max_elems=8, verbose=True):
    """Try to build a model by adding elements one at a time.

    Uses backtracking: if extension fails, try different choices.
    """
    type_list = list(T)

    def find_demands(elements, edges):
        """Find unsatisfied existential demands."""
        for idx, (eid, tau) in enumerate(elements):
            for c in cl:
                if c[0] == 'exists' and c in tau:
                    R, D = c[1], c[2]
                    witnessed = False
                    for jdx, (ejd, tj) in enumerate(elements):
                        if jdx != idx and D in tj:
                            rij = edges.get((idx, jdx))
                            if rij == R:
                                witnessed = True
                                break
                    if not witnessed:
                        yield (idx, R, D)

    def try_extend(elements, edges, demand_idx, R, D, depth=0):
        """Try to add a new element to satisfy a demand."""
        if len(elements) >= max_elems:
            return None

        m = len(elements)
        e_idx = demand_idx

        # Find all possible witness types
        witness_types = []
        for tp in type_list:
            if D in tp and R in dn_map.get((elements[e_idx][1], tp), frozenset()):
                witness_types.append(tp)

        for wt in witness_types:
            # Compute domains
            domains = []
            for jdx, (ejd, tj) in enumerate(elements):
                if jdx == e_idx:
                    domains.append([R])
                else:
                    d = dn_map.get((tj, wt), frozenset())
                    if not d:
                        break
                    domains.append(list(d))
            else:
                # Try all global assignments
                for assignment in product(*domains):
                    ok = True
                    for i in range(m):
                        for j in range(i+1, m):
                            rij = edges[(i, j)]
                            si, sj = assignment[i], assignment[j]
                            if si not in comp(rij, sj):
                                ok = False
                                break
                        if not ok:
                            break
                    if ok:
                        # Found valid extension
                        new_elements = list(elements) + [(f'e{m}', wt)]
                        new_edges = dict(edges)
                        for i in range(m):
                            new_edges[(i, m)] = assignment[i]
                            new_edges[(m, i)] = INV[assignment[i]]
                        return (new_elements, new_edges)

        return None  # Failed

    def build_model(elements, edges, depth=0):
        """Recursive model building with backtracking."""
        demands = list(find_demands(elements, edges))
        if not demands:
            return elements, edges  # All demands satisfied!

        if len(elements) >= max_elems:
            return None

        # Try to satisfy each demand (try the first one with backtracking)
        idx, R, D = demands[0]

        # Find all witness types
        witness_types = []
        for tp in type_list:
            if D in tp and R in dn_map.get((elements[idx][1], tp), frozenset()):
                witness_types.append(tp)

        m = len(elements)

        for wt in witness_types:
            domains = []
            valid = True
            for jdx, (ejd, tj) in enumerate(elements):
                if jdx == idx:
                    domains.append([R])
                else:
                    d = list(dn_map.get((tj, wt), frozenset()))
                    if not d:
                        valid = False
                        break
                    domains.append(d)
            if not valid:
                continue

            for assignment in product(*domains):
                ok = True
                for i in range(m):
                    for j in range(i+1, m):
                        rij = edges[(i, j)]
                        si, sj = assignment[i], assignment[j]
                        if si not in comp(rij, sj):
                            ok = False
                            break
                    if not ok:
                        break
                if not ok:
                    continue

                # Valid extension — recurse
                new_elems = list(elements) + [(f'e{m}', wt)]
                new_edges = dict(edges)
                for i in range(m):
                    new_edges[(i, m)] = assignment[i]
                    new_edges[(m, i)] = INV[assignment[i]]

                result = build_model(new_elems, new_edges, depth + 1)
                if result is not None:
                    return result

        return None  # All choices exhausted

    if verbose:
        print(f"  Building model from τ₀ (max {max_elems} elements)...")

    elements = [('e0', tau0)]
    edges = {}
    result = build_model(elements, edges)

    if result:
        elements, edges = result
        if verbose:
            print(f"  MODEL FOUND with {len(elements)} elements")
            for i, (eid, tau) in enumerate(elements):
                markers = []
                for m in ['A', 'B', 'C', 'D']:
                    if atom(m) in tau: markers.append(m)
                    elif neg(m) in tau: markers.append(f'¬{m}')
                print(f"    {eid}: markers={markers}")
            for i in range(len(elements)):
                row = f"    {elements[i][0]}: "
                for j in range(len(elements)):
                    if i == j:
                        row += "EQ  "
                    else:
                        row += f"{edges[(i,j)]:4s}"
                print(row)
        return True, (elements, edges)
    else:
        if verbose:
            print(f"  NO MODEL FOUND (exhausted search up to {max_elems} elements)")
        return False, None


def main():
    print("="*70)
    print("Spurious Quasimodel Search for ALCI_RCC5")
    print("="*70)

    # Design concept targeting the extension gap pattern
    # DN(τ₀,τ')={PO}, DN(τ₁,τ')={DR}, DN(τ₂,τ')={PP,PPI}
    #
    # τ₀: A, ∀DR.¬D, ∀PP.¬D, ∀PPI.¬D, ∃DR.B_full, ∃DR.C_full, ∃PO.D
    # τ₁: B, ∀PO.¬D, ∀PP.¬D, ∀PPI.¬D, ∃PO.C
    # τ₂: C, ∀DR.¬D, ∀PO.¬D
    # τ': D

    B_filler = AND(atom('B'),
                   FORALL(PO, neg('D')),
                   FORALL(PP, neg('D')),
                   FORALL(PPI, neg('D')),
                   EXISTS(PO, atom('C')))

    C_filler = AND(atom('C'),
                   FORALL(DR, neg('D')),
                   FORALL(PO, neg('D')))

    c0 = AND(atom('A'),
             EXISTS(DR, B_filler),
             EXISTS(DR, C_filler),
             EXISTS(PO, atom('D')),
             FORALL(DR, neg('D')),
             FORALL(PP, neg('D')),
             FORALL(PPI, neg('D')))

    print(f"\nC₀ = {concept_str(c0)}")
    print()

    # Type elimination
    print("Type elimination:")
    accepted, T, P, dn_map, tau0s, cl = type_elimination(c0, verbose=True)

    if not accepted:
        print("\n*** REJECTED — no quasimodel. ***")
        print("Trying simpler concept...")

        # Even simpler: just the core conflict
        c0 = AND(EXISTS(PO, atom('D')),
                 EXISTS(DR, AND(atom('B'), FORALL(PO, neg('D')))),
                 FORALL(DR, neg('D')),
                 FORALL(PP, neg('D')),
                 FORALL(PPI, neg('D')))

        print(f"\nC₀ = {concept_str(c0)}")
        accepted, T, P, dn_map, tau0s, cl = type_elimination(c0, verbose=True)

        if not accepted:
            print("\n*** Also rejected. ***")
            return

    # Analyze types
    print(f"\n{'='*70}")
    print("Type analysis:")
    print(f"{'='*70}")

    type_names = {}
    for idx, tau in enumerate(sorted(T, key=lambda t: ''.join(
            sorted(concept_str(c) for c in t)))):
        markers = []
        for m in ['A', 'B', 'C', 'D']:
            if atom(m) in tau: markers.append(m)
            elif neg(m) in tau: markers.append(f'¬{m}')
        foralls = []
        for c in tau:
            if c[0] == 'forall':
                foralls.append(concept_str(c))
        exists_ = []
        for c in tau:
            if c[0] == 'exists':
                exists_.append(concept_str(c))
        name = f"τ{idx}"
        type_names[tau] = name
        is_root = " ← ROOT" if tau in tau0s else ""
        print(f"  {name}: {markers} ∀:{foralls} ∃:{exists_}{is_root}")

    # DN matrix
    print(f"\n  DN matrix:")
    sT = sorted(T, key=lambda t: type_names[t])
    header = "         " + " ".join(f"{type_names[t]:>6s}" for t in sT)
    print(header)
    for t1 in sT:
        row = f"  {type_names[t1]:>5s}  "
        for t2 in sT:
            dn = dn_map.get((t1, t2), frozenset())
            if not dn:
                cell = "∅"
            else:
                cell = ''.join(sorted(r[0] for r in dn))
            row += f"{cell:>6s} "
        print(row)

    # Check for the extension gap pattern
    print(f"\n{'='*70}")
    print("Checking for extension gap patterns:")
    print(f"{'='*70}")

    d_types = [t for t in T if atom('D') in t]
    for td in d_types:
        print(f"\n  Target type: {type_names[td]}")
        for t in T:
            dn = dn_map.get((t, td), frozenset())
            print(f"    DN({type_names[t]}, {type_names[td]}) = "
                  f"{set(dn) if dn else '∅'}")

    # Try to build model
    print(f"\n{'='*70}")
    print("Model construction (backtracking):")
    print(f"{'='*70}")

    for tau0 in tau0s:
        print(f"\n  Starting from {type_names[tau0]}:")
        success, model = try_build_model(T, dn_map, tau0, cl,
                                         max_elems=10, verbose=True)
        if success:
            print(f"\n  *** CONCEPT IS SATISFIABLE ***")
            print(f"  The quasimodel is NOT spurious.")
        else:
            print(f"\n  *** POTENTIAL SPURIOUS QUASIMODEL ***")
            print(f"  Type elimination accepts but model construction fails!")
            print(f"  This is evidence of a genuine gap in the decidability proof.")


if __name__ == '__main__':
    main()
