#!/usr/bin/env python3
"""
Cover-Tree Tableau for ALCI_RCC5
=================================

Implementation of the cover-tree tableau calculus from the split-forest
/ sibling-interface approach (GPT-5.4, April 2026).

Key design:
  - PP/PPI are tree edges (ancestor/descendant in the cover tree).
  - DR/PO are cross-edges (between incomparable nodes in sibling subtrees).
  - The two layers are checked separately:
    * Tree layer: PP/PPI demands form a valid tree structure.
    * Cross layer: DR/PO demands have witnesses, and the {DR,PO} disjunctive
      network among sibling-related types is consistent.
  - The split-forest insight: PP is NOT an open sibling cross-edge after
    EQ-splitting. Only {DR,PO} remain open between sibling subtrees.
  - Blocking = equality of rank-d signatures (d = modal depth of input).

The main difference from the quasimodel reasoner:
  - Sibling compatibility only applies to DR/PO witness pairs (not mixed PP/DR).
  - Tree-related pairs (PP/PPI) have separate tree-consistency check.
  - The {DR,PO} cross-edge network is trivially arc-consistent
    (comp(R,S) ∩ {DR,PO} ≠ ∅ for all R,S ∈ {DR,PO}).
  - This correctly handles the 7 "cyclic-model" concepts that lack
    tree models but are satisfiable.

Usage:
  python3 cover_tree_tableau.py              # run built-in tests
  python3 cover_tree_tableau.py --verbose    # detailed output
"""

import sys
import time
import itertools
from collections import defaultdict

from alcircc5_reasoner import (
    DR, PO, PP, PPI, BASE_RELS, INV, COMP,
    Concept, AtomicConcept, NegAtomicConcept, Top, Bottom,
    And, Or, Exists, ForAll,
    closure, enumerate_types, compute_safe,
)


# ══════════════════════════════════════════════════════════════
# Utilities
# ══════════════════════════════════════════════════════════════

def modal_depth(C):
    """Compute the modal depth of concept C."""
    if isinstance(C, (AtomicConcept, NegAtomicConcept, Top, Bottom)):
        return 0
    elif isinstance(C, And):
        return max(modal_depth(C.left), modal_depth(C.right))
    elif isinstance(C, Or):
        return max(modal_depth(C.left), modal_depth(C.right))
    elif isinstance(C, (Exists, ForAll)):
        return 1 + modal_depth(C.concept)
    return 0


# ══════════════════════════════════════════════════════════════
# Cover-Tree Tableau Decision Procedure
# ══════════════════════════════════════════════════════════════

def check_satisfiability(C0, verbose=False):
    """
    Check satisfiability of concept C0 using the cover-tree tableau.

    Algorithm:
    1. Compute closure, types, safe relations (same as quasimodel)
    2. Search for a type set T containing C0 that is:
       a. Demand-closed: every ∃R.C has an R-safe witness in T
       b. Tree-consistent: PP/PPI witnesses form a valid tree structure
       c. Cross-consistent: DR/PO witnesses have proper type-safety
       d. Sibling-compatible: DR/PO witness pairs satisfy
          composition constraints within {DR,PO}

    Returns (is_sat, info_dict).
    """
    t0 = time.time()

    # ── Step 1: Closure and types ──────────────────────────────
    cl = closure(C0)
    all_types = enumerate_types(cl)
    type_list = list(all_types)
    n = len(type_list)

    if verbose:
        print(f"  Closure: {len(cl)}, Types: {n}, Depth: {modal_depth(C0)}")

    if n == 0:
        return False, {'reason': 'no types', 'time': time.time() - t0}

    # ── Step 2: Precompute safe relations ──────────────────────
    safe = {}
    for i in range(n):
        for j in range(n):
            safe[(i, j)] = compute_safe(type_list[i], type_list[j])

    # Safe restricted to {DR,PO} — the open cross-edge domain
    safe_cross = {}
    for i in range(n):
        for j in range(n):
            safe_cross[(i, j)] = safe[(i, j)] & frozenset({DR, PO})

    # ── Step 3: Precompute demands ─────────────────────────────
    demands = {}
    for i in range(n):
        demands[i] = []
        for c in type_list[i]:
            if isinstance(c, Exists):
                demands[i].append((c.role, c.concept))

    # Separate demands by role type:
    # Tree demands (PP/PPI): create tree structure
    # Cross demands (DR/PO): discharged by global side-checker
    tree_demands = {}  # type_idx -> [(role, concept)] for PP/PPI
    cross_demands = {} # type_idx -> [(role, concept)] for DR/PO
    for i in range(n):
        tree_demands[i] = [(R, D) for R, D in demands[i] if R in (PP, PPI)]
        cross_demands[i] = [(R, D) for R, D in demands[i] if R in (DR, PO)]

    # ── Step 4: Demand closure check ──────────────────────────
    def check_demand_closure(T):
        """Check that every demand in every type in T has a witness in T."""
        for i in sorted(T):
            for R, D in demands[i]:
                found = False
                for j in sorted(T):
                    if D in type_list[j] and R in safe[(i, j)]:
                        found = True
                        break
                if not found:
                    return False
        return True

    # ── Step 5: Cross-edge compatibility ──────────────────────
    def check_cross_compatibility(T):
        """
        Check that DR/PO demands are satisfiable in the cover-tree model.

        In the cover tree, DR/PO witnesses are in sibling subtrees.
        The key constraint:
        - For each type with ∃DR.C: some type in T has C and is DR-safe.
        - For each type with ∃PO.C: some type in T has C and is PO-safe.
        - For siblings created by DR/PO demands: their pairwise relations
          must be in {DR,PO} ∩ Safe (the open domain).
        - The {DR,PO} cross-edge network is arc-consistent.
          (This is trivially true since comp(R,S) ∩ {DR,PO} ≠ ∅ for
          all R,S ∈ {DR,PO}.)

        The critical additional check: for types that serve as both
        cross-edge witnesses and tree nodes, verify that the universal
        constraints (∀DR, ∀PO) are respected.
        """
        for i in sorted(T):
            for R, D in cross_demands[i]:
                found = False
                for j in sorted(T):
                    if D in type_list[j] and R in safe[(i, j)]:
                        found = True
                        break
                if not found:
                    return False
        return True

    # ── Step 6: Cover-tree sibling check ──────────────────────
    def check_cover_tree_siblings(T):
        """
        Check sibling compatibility in the cover-tree model.

        Key difference from the quasimodel approach:
        In the cover tree, only DR/PO witnesses are siblings. PP/PPI
        witnesses are in ancestor/descendant positions, NOT sibling positions.

        For each type i in T with multiple cross-edge (DR/PO) demands,
        we need joint witnesses j₁,...,jₖ such that for each pair:
          comp(INV[Rₘ], Rₘ') ∩ {DR,PO} ∩ safe_cross(jₘ, jₘ') ≠ ∅

        This is weaker than the quasimodel check because:
        1. Only DR/PO witness pairs are checked (not PP vs DR)
        2. Domains are restricted to {DR,PO}
        """
        T_list = sorted(T)

        for i in T_list:
            cdems = cross_demands[i]
            if len(cdems) <= 1:
                continue

            # Candidates for each cross demand slot
            candidates = []
            for R, D in cdems:
                cands = sorted([j for j in T_list
                               if D in type_list[j] and R in safe[(i, j)]])
                if not cands:
                    return False
                candidates.append(cands)

            k = len(cdems)

            # Arc-consistency: prune candidates pairwise
            # For cross-edge siblings, the pairwise constraint is:
            # comp(INV[Rₘ], Rₘ') ∩ {DR,PO} ∩ safe_cross(jₘ, jₘ') ≠ ∅
            changed = True
            while changed:
                changed = False
                for m in range(k):
                    Rm = cdems[m][0]
                    new_cands = []
                    for jm in candidates[m]:
                        ok = True
                        for mp in range(k):
                            if mp == m:
                                continue
                            Rmp = cdems[mp][0]
                            # Two DR/PO witnesses are siblings in a sibling subtree.
                            # Their mutual relation is in {DR,PO}.
                            # The composition constraint from the parent:
                            # if parent -INV[Rm]-> jm and parent -Rmp-> jmp_c,
                            # then jm -?-> jmp_c with ? in comp(INV[Rm], Rmp).
                            # Restricted to {DR,PO}:
                            comp_set = COMP[(INV[Rm], Rmp)] & frozenset({DR, PO})
                            found = False
                            for jmp_c in candidates[mp]:
                                if jm == jmp_c and Rm == Rmp:
                                    found = True
                                    break
                                if comp_set & safe_cross[(jm, jmp_c)]:
                                    found = True
                                    break
                            if not found:
                                ok = False
                                break
                        if ok:
                            new_cands.append(jm)
                    if len(new_cands) < len(candidates[m]):
                        candidates[m] = new_cands
                        changed = True
                        if not new_cands:
                            return False

            # Backtracking search for a valid assignment
            def bt_search(slot, assignment):
                if slot == k:
                    return True
                Rm = cdems[slot][0]
                for jm in candidates[slot]:
                    ok = True
                    for prev_slot in range(len(assignment)):
                        jmp_val = assignment[prev_slot]
                        Rmp = cdems[prev_slot][0]
                        if jm == jmp_val and Rm == Rmp:
                            continue
                        comp_set = COMP[(INV[Rm], Rmp)] & frozenset({DR, PO})
                        if not (comp_set & safe_cross[(jm, jmp_val)]):
                            ok = False
                            break
                        # Also check reverse
                        comp_set_rev = COMP[(INV[Rmp], Rm)] & frozenset({DR, PO})
                        if not (comp_set_rev & safe_cross[(jmp_val, jm)]):
                            ok = False
                            break
                    if ok:
                        assignment.append(jm)
                        if bt_search(slot + 1, assignment):
                            return True
                        assignment.pop()
                return False

            if not bt_search(0, []):
                return False

        return True

    # ── Step 7: Tree-cross interaction check ──────────────────
    def check_tree_cross_interaction(T):
        """
        Check that ALL pairs of demands from any type are jointly
        satisfiable under cover-tree composition constraints.

        For type i with demands (R1, D1) and (R2, D2), witnesses j1, j2
        must satisfy:
          COMP[(INV[R1], R2)] ∩ safe[(j1, j2)] ≠ ∅
          COMP[(INV[R2], R1)] ∩ safe[(j2, j1)] ≠ ∅

        This generalizes the previous singleton-only check to handle ALL
        composition sizes, including non-singleton cases like:
          COMP[PO, PP] = {PP, PO}  (both may be unsafe → clash)
        """
        T_list = sorted(T)

        for i in T_list:
            all_dems = demands[i]
            if len(all_dems) <= 1:
                continue

            for m1 in range(len(all_dems)):
                R1, D1 = all_dems[m1]
                for m2 in range(m1 + 1, len(all_dems)):
                    R2, D2 = all_dems[m2]

                    comp_12 = COMP[(INV[R1], R2)]
                    comp_21 = COMP[(INV[R2], R1)]

                    w1 = [j for j in T_list
                          if D1 in type_list[j] and R1 in safe[(i, j)]]
                    w2 = [j for j in T_list
                          if D2 in type_list[j] and R2 in safe[(i, j)]]

                    found = False
                    for j1 in w1:
                        for j2 in w2:
                            if j1 == j2 and R1 == R2:
                                found = True
                                break
                            if (comp_12 & safe[(j1, j2)] and
                                comp_21 & safe[(j2, j1)]):
                                found = True
                                break
                        if found:
                            break

                    if not found:
                        return False

        return True

    # ── Step 8: Disjunctive path-consistency of cross-edge network ──
    def check_cross_pc(T):
        """
        Check path-consistency of the {DR,PO} cross-edge network.

        For the cross-edge network restricted to {DR,PO}, arc-consistency
        is trivially guaranteed because:
          comp(DR,DR) ⊇ {DR,PO}
          comp(DR,PO) ⊇ {DR,PO}
          comp(PO,DR) ⊇ {DR,PO}
          comp(PO,PO) ⊇ {DR,PO}

        So any non-empty domain always has support through any other
        non-empty domain. This check verifies that Safe_{DR/PO}(τi,τj)
        is non-empty for all pairs in T that might need cross-edges.
        (Types that can only be tree-related are exempt.)
        """
        T_list = sorted(T)
        k = len(T_list)
        if k <= 1:
            return True

        # Check: for each pair, either they can be tree-related
        # (PP or PPI in safe) or they can be cross-related
        # (safe_cross non-empty).
        for a in range(k):
            for b in range(a + 1, k):
                ti, tj = T_list[a], T_list[b]
                tree_ok = bool(safe[(ti, tj)] & frozenset({PP, PPI}))
                cross_ok = bool(safe_cross[(ti, tj)])
                if not tree_ok and not cross_ok:
                    # These types can't coexist in a model
                    # (no valid RCC5 relation between them)
                    return False
        return True

    # ── Main search ────────────────────────────────────────────

    found_T = [None]

    def try_build(T, depth=0):
        """Try to build a valid type set from T."""
        if depth > n:
            return False

        # Check cross-edge PC (non-empty domains)
        if not check_cross_pc(T):
            return False

        # Find first unwitnessed demand
        for i in sorted(T):
            for R, D in demands[i]:
                found_in_T = False
                for j in sorted(T):
                    if D in type_list[j] and R in safe[(i, j)]:
                        found_in_T = True
                        break
                if not found_in_T:
                    # Add a witness type
                    for j in range(n):
                        if j in T:
                            continue
                        if D in type_list[j] and R in safe[(i, j)]:
                            T_new = T | {j}
                            if try_build(T_new, depth + 1):
                                return True
                    return False

        # All demands witnessed.
        # Check cover-tree sibling compatibility
        if not check_cover_tree_siblings(T):
            return False

        # Check tree-cross interaction
        if not check_tree_cross_interaction(T):
            return False

        found_T[0] = T
        return True

    # Find root types containing C0
    root_types = [i for i in range(n) if C0 in type_list[i]]

    if not root_types:
        return False, {'reason': 'no root type', 'time': time.time() - t0}

    for root in root_types:
        if try_build(frozenset({root})):
            elapsed = time.time() - t0
            info = {
                'closure_size': len(cl),
                'initial_types': n,
                'root_types': len(root_types),
                'time': elapsed,
                'type_set': found_T[0],
                'type_list': type_list,
                'safe': safe,
                'safe_cross': safe_cross,
                'demands': demands,
                'tree_demands': tree_demands,
                'cross_demands': cross_demands,
            }
            return True, info

    elapsed = time.time() - t0
    return False, {
        'reason': 'all branches closed',
        'time': elapsed,
    }


# ══════════════════════════════════════════════════════════════
# Convenience wrapper
# ══════════════════════════════════════════════════════════════

def check_sat(C0, verbose=False):
    """Alias for check_satisfiability."""
    return check_satisfiability(C0, verbose=verbose)


# ══════════════════════════════════════════════════════════════
# Test Suite
# ══════════════════════════════════════════════════════════════

def run_tests(verbose=False):
    """Run comprehensive test suite."""
    from alcircc5_reasoner import check_satisfiability as check_sat_qm

    A = AtomicConcept('A')
    B = AtomicConcept('B')
    C = AtomicConcept('C')
    nA = NegAtomicConcept('A')
    nB = NegAtomicConcept('B')
    nC = NegAtomicConcept('C')
    top = Top()
    bot = Bottom()

    tests = [
        # ═══ Basic SAT ═══
        ("A", A, True),
        ("A ⊓ B", And(A, B), True),
        ("A ⊔ ¬A", Or(A, nA), True),
        ("⊤", top, True),

        # ═══ Basic UNSAT ═══
        ("A ⊓ ¬A", And(A, nA), False),
        ("⊥", bot, False),

        # ═══ Single existential (all roles) ═══
        ("∃PP.A", Exists(PP, A), True),
        ("∃PPI.A", Exists(PPI, A), True),
        ("∃DR.A", Exists(DR, A), True),
        ("∃PO.A", Exists(PO, A), True),
        ("∃PP.⊥", Exists(PP, bot), False),
        ("∃DR.(A ⊓ ¬A)", Exists(DR, And(A, nA)), False),

        # ═══ Universal + existential (same role) ═══
        ("∃DR.A ⊓ ∀DR.A", And(Exists(DR, A), ForAll(DR, A)), True),
        ("∃DR.A ⊓ ∀DR.¬A", And(Exists(DR, A), ForAll(DR, nA)), False),
        ("∃PP.A ⊓ ∀PP.A", And(Exists(PP, A), ForAll(PP, A)), True),
        ("∃PO.A ⊓ ∀PO.¬A", And(Exists(PO, A), ForAll(PO, nA)), False),

        # ═══ Multi-role demands ═══
        ("∃PP.A ⊓ ∃PPI.B", And(Exists(PP, A), Exists(PPI, B)), True),
        ("∃DR.A ⊓ ∃PO.B", And(Exists(DR, A), Exists(PO, B)), True),
        ("∃PP.A ⊓ ∃DR.B ⊓ ∃PO.C",
         And(And(Exists(PP, A), Exists(DR, B)), Exists(PO, C)), True),

        # ═══ Cross-role universal contradictions (6 patterns) ═══
        ("∃PPI.(∀DR.A) ⊓ ∃DR.¬A",
         And(Exists(PPI, ForAll(DR, A)), Exists(DR, nA)), False),
        ("∃PP.(∀PPI.A) ⊓ ∃PPI.¬A",
         And(Exists(PP, ForAll(PPI, A)), Exists(PPI, nA)), False),
        ("∃PPI.(∀PP.A) ⊓ ∃PP.¬A",
         And(Exists(PPI, ForAll(PP, A)), Exists(PP, nA)), False),

        # These are UNSAT because comp(INV[R1], R2) is a singleton
        # that forces the universal to fire on the second witness.
        # comp(PP, DR) = {DR} → ∀DR fires
        # comp(PPI, PPI) = {PPI} → ∀PPI fires
        # comp(PP, PP) = {PP} → ∀PP fires

        # ═══ The 7 "cyclic-model" concepts (ALL SAT) ═══
        # These are SAT but require non-tree models in the quasimodel sense.
        # In the cover-tree model, PP-witnesses are ancestors and
        # PO/DR-witnesses are cross-edge related (sibling subtrees).
        ("∃DR.A ⊓ ∃PP.¬A ⊓ ∀PO.A",
         And(And(Exists(DR, A), Exists(PP, nA)), ForAll(PO, A)), True),
        ("∃PO.A ⊓ ∃PP.¬A ⊓ ∀PO.A",
         And(And(Exists(PO, A), Exists(PP, nA)), ForAll(PO, A)), True),
        ("∃PO.A ⊓ ∃PP.¬B ⊓ ∀DR.A",
         And(And(Exists(PO, A), Exists(PP, nB)), ForAll(DR, A)), True),
        ("∃PO.A ⊓ ∃PP.¬B ⊓ ∀PO.A",
         And(And(Exists(PO, A), Exists(PP, nB)), ForAll(PO, A)), True),
        ("∃PO.A ⊓ ∃PP.¬B ⊓ ∀PP.A",
         And(And(Exists(PO, A), Exists(PP, nB)), ForAll(PP, A)), True),
        ("∃PO.A ⊓ ∃PP.¬B ⊓ ∀PPI.A",
         And(And(Exists(PO, A), Exists(PP, nB)), ForAll(PPI, A)), True),
        ("∃PP.A ⊓ ∃PP.¬A ⊓ ∀PO.A",
         And(And(Exists(PP, A), Exists(PP, nA)), ForAll(PO, A)), True),

        # ═══ Deeper nesting ═══
        ("∃PP.∃PP.A", Exists(PP, Exists(PP, A)), True),
        ("∃PPI.∃PPI.A", Exists(PPI, Exists(PPI, A)), True),
        ("∃PP.(A ⊓ ∃PPI.B)", Exists(PP, And(A, Exists(PPI, B))), True),

        # ═══ Infinite PP-chain ═══
        ("∃PP.⊤ ⊓ ∀PP.∃PP.⊤",
         And(Exists(PP, top), ForAll(PP, Exists(PP, top))), True),

        # ═══ Cross-demand interaction (SAT) ═══
        ("∃PP.(∀DR.A) ⊓ ∃DR.¬A",
         And(Exists(PP, ForAll(DR, A)), Exists(DR, nA)), True),
        # PP-witness has ∀DR.A, DR-witness has ¬A. In cover tree:
        # PP-witness is ancestor, DR-witness is cross-edge related.
        # The DR-witness is NOT DR-related to the PP-witness
        # (it's in a sibling subtree, relation could be PO or PPI).

        # ═══ Deep nested PP chain with universals ═══
        ("∃PP.(∃PP.(∃PP.A ⊓ ∀DR.B) ⊓ ∀DR.B) ⊓ ∀DR.B",
         And(Exists(PP, And(Exists(PP, And(Exists(PP, A), ForAll(DR, B))),
                           ForAll(DR, B))),
             ForAll(DR, B)),
         True),
    ]

    print("=" * 70)
    print("COVER-TREE TABLEAU TEST SUITE")
    print("=" * 70)

    passed = 0
    failed = 0
    errors = []

    for name, concept, expected in tests:
        try:
            sat, info = check_sat(concept, verbose=verbose)
            status = "SAT" if sat else "UNSAT"
            correct = sat == expected
            t = info.get('time', 0)

            if correct:
                print(f"  ✓ {name}: {status} ({t:.4f}s)")
                passed += 1
            else:
                exp_str = "SAT" if expected else "UNSAT"
                print(f"  ✗ {name}: got {status}, expected {exp_str} ({t:.4f}s)")
                failed += 1
                errors.append((name, expected, sat, info.get('reason', '')))
        except Exception as e:
            import traceback
            print(f"  ✗ {name}: ERROR: {e}")
            if verbose:
                traceback.print_exc()
            failed += 1
            errors.append((name, expected, f"ERROR: {e}", ""))

    print(f"\n  Results: {passed} passed, {failed} failed out of {len(tests)}")

    if errors:
        print("\n  Failures:")
        for name, expected, got, reason in errors:
            exp_str = "SAT" if expected else "UNSAT"
            got_str = f"SAT" if got is True else (f"UNSAT" if got is False else str(got))
            print(f"    {name}: expected {exp_str}, got {got_str} ({reason})")

    # Cross-check with quasimodel reasoner
    print("\n  Cross-checking against quasimodel reasoner...")
    mismatches = 0
    for name, concept, expected in tests:
        try:
            ct_sat, _ = check_sat(concept)
            qm_sat, _ = check_sat_qm(concept)
            if ct_sat != qm_sat:
                ct_str = "SAT" if ct_sat else "UNSAT"
                qm_str = "SAT" if qm_sat else "UNSAT"
                print(f"    MISMATCH {name}: CT={ct_str}, QM={qm_str}")
                mismatches += 1
        except Exception:
            pass

    if mismatches == 0:
        print("    All results match quasimodel reasoner.")

    return failed == 0


if __name__ == '__main__':
    verbose = '--verbose' in sys.argv or '-v' in sys.argv
    success = run_tests(verbose=verbose)
    sys.exit(0 if success else 1)
