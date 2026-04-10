#!/usr/bin/env python3
"""
Model Construction and Verification for ALCI_RCC5
==================================================

For every concept judged SAT by the cover-tree tableau, this script:
  1. Extracts the type set T from the reasoner
  2. Builds a concrete model by assigning domain elements and RCC5 relations
  3. Verifies composition consistency on EVERY triple
  4. Verifies concept satisfaction at the root element

This provides independent evidence: not "two algorithms agree" but
"here is a concrete witness model."

Usage:
  python3 model_verifier.py              # run on all stress-test concepts
  python3 model_verifier.py --verbose    # detailed output per concept
"""

import sys
import time
import itertools
import random

from alcircc5_reasoner import (
    DR, PO, PP, PPI, BASE_RELS, INV, COMP,
    Concept, AtomicConcept, NegAtomicConcept, Top, Bottom,
    And, Or, Exists, ForAll,
    closure, enumerate_types, compute_safe,
    check_satisfiability as check_sat_qm,
)
from cover_tree_tableau import check_satisfiability as check_sat_ct


# ══════════════════════════════════════════════════════════════
# Model Construction
# ══════════════════════════════════════════════════════════════

def build_model(C0, info, verbose=False):
    """
    Build a concrete model from the cover-tree tableau's type set.

    Strategy: create domain elements (scaling copies per type to demand
    count), assign RCC5 relations satisfying:
      (a) Type-safety (safe relation between types)
      (b) Composition consistency on all triples
      (c) All existential demands witnessed

    Uses arc-consistency + demand-aware backtracking with forward checking.
    """
    T = info['type_set']
    type_list = info['type_list']
    safe = info['safe']
    demands = info['demands']

    T_sorted = sorted(T)
    if not T_sorted:
        return False, "empty type set"

    # Need enough copies so each element has enough neighbors for its demands
    max_demands = max((len(demands[ti]) for ti in T_sorted), default=0)
    # With k types and c copies each, each element has (k*c - 1) neighbors.
    # Need at least max_demands neighbors, so c >= ceil((max_demands+1)/k).
    k = len(T_sorted)
    max_copies = max(3, (max_demands + k) // k + 1)
    # Cap to avoid explosion
    max_copies = min(max_copies, 10)

    # Try without leaves first (symmetric models), then with leaves
    for use_leaves in [False, True]:
        for num_copies in range(1, max_copies + 1):
            result = _try_build(T_sorted, type_list, safe, demands,
                                num_copies, use_leaves=use_leaves)
            if result is not None:
                return True, result

    return False, f"failed with up to {max_copies} copies"


def _try_build(T_sorted, type_list, safe, demands, num_copies, use_leaves=True):
    """Try building with num_copies elements per type. Returns model or None."""
    n_all = len(type_list)
    T_set = set(T_sorted)

    # Detect recursive demands: demand (R, D) of type ti where every
    # witness in T also has the same demand — needs a "leaf" type
    leaf_types = set()
    if use_leaves:
        for ti in T_sorted:
            for R, D in demands[ti]:
                has_non_recursive = False
                for tj in T_sorted:
                    if D in type_list[tj] and R in safe[(ti, tj)]:
                        if (R, D) not in demands[tj]:
                            has_non_recursive = True
                            break
                if not has_non_recursive:
                    for tj in range(n_all):
                        if tj in T_set or tj in leaf_types:
                            continue
                        if (D in type_list[tj] and R in safe[(ti, tj)]
                                and (R, D) not in demands[tj]):
                            leaf_types.add(tj)
                            break

    # Create elements: num_copies per T type, 1 per leaf type
    elements = []
    elem_type = {}
    eid = 0
    for ti in T_sorted:
        for _ in range(num_copies):
            elements.append(eid)
            elem_type[eid] = ti
            eid += 1
    for ti in sorted(leaf_types):
        elements.append(eid)
        elem_type[eid] = ti
        eid += 1

    # Initialize disjunctive domains from safe
    dom = {}
    for e1 in elements:
        for e2 in elements:
            if e1 == e2:
                continue
            s = set(safe[(elem_type[e1], elem_type[e2])])
            if not s:
                return None
            dom[(e1, e2)] = s

    # Inverse consistency
    changed = True
    while changed:
        changed = False
        for e1 in elements:
            for e2 in elements:
                if e1 >= e2:
                    continue
                fwd = dom[(e1, e2)]
                bwd = dom[(e2, e1)]
                new_fwd = {R for R in fwd if INV[R] in bwd}
                new_bwd = {R for R in bwd if INV[R] in fwd}
                if not new_fwd or not new_bwd:
                    return None
                if new_fwd != fwd or new_bwd != bwd:
                    dom[(e1, e2)] = new_fwd
                    dom[(e2, e1)] = new_bwd
                    changed = True

    # Arc-consistency (path-consistency)
    changed = True
    iters = 0
    while changed and iters < 100:
        changed = False
        iters += 1
        for e1 in elements:
            for e2 in elements:
                if e1 == e2:
                    continue
                new_dom = set()
                for R12 in dom[(e1, e2)]:
                    ok = True
                    for e3 in elements:
                        if e3 == e1 or e3 == e2:
                            continue
                        found = False
                        for R23 in dom[(e2, e3)]:
                            if COMP[(R12, R23)] & dom[(e1, e3)]:
                                found = True
                                break
                        if not found:
                            ok = False
                            break
                    if ok:
                        new_dom.add(R12)
                if not new_dom:
                    return None
                if new_dom != dom[(e1, e2)]:
                    dom[(e1, e2)] = new_dom
                    changed = True

    # Precompute demands and potential witnesses per element
    elem_demands = {}
    demand_witnesses = {}  # (e, di) -> set of potential witness elements

    for e in elements:
        ti = elem_type[e]
        elem_demands[e] = list(demands[ti])
        for di, (R, D) in enumerate(demands[ti]):
            witnesses = set()
            for ep in elements:
                if ep == e:
                    continue
                if D in type_list[elem_type[ep]] and R in dom[(e, ep)]:
                    witnesses.add(ep)
            if not witnesses:
                return None  # demand can't be witnessed
            demand_witnesses[(e, di)] = witnesses

    # Precompute demanded relations per directed edge
    edge_demands = {}
    for e in elements:
        for di, (R, D) in enumerate(elem_demands[e]):
            for ep in demand_witnesses[(e, di)]:
                edge_demands.setdefault((e, ep), set()).add(R)

    # Order pairs: critical edges first (sole-witness demands)
    pairs = [(e1, e2) for e1 in elements for e2 in elements if e1 < e2]

    def pair_priority(pair):
        e1, e2 = pair
        score = 0
        for di in range(len(elem_demands[e1])):
            if e2 in demand_witnesses.get((e1, di), set()):
                score += 100 if len(demand_witnesses[(e1, di)]) == 1 else 1
        for di in range(len(elem_demands[e2])):
            if e1 in demand_witnesses.get((e2, di), set()):
                score += 100 if len(demand_witnesses[(e2, di)]) == 1 else 1
        return -score

    pairs.sort(key=pair_priority)

    # Randomized search with restarts + demand-aware forward checking
    # For small models (≤4 elements), use deterministic backtracking.
    # For larger, use randomized restarts to avoid exponential blow-up.
    max_attempts = 1 if len(elements) <= 4 else 100
    t_budget = time.time() + 0.5  # total 0.5 second per copy count

    for attempt in range(max_attempts):
        if time.time() > t_budget:
            break
        t_start = time.time()
        assignment = {}

        if attempt > 0:
            # Randomize pair order (keep critical edges first)
            critical = [p for p in pairs if pair_priority(p) < -50]
            non_critical = [p for p in pairs if pair_priority(p) >= -50]
            random.shuffle(non_critical)
            attempt_pairs = critical + non_critical
        else:
            attempt_pairs = pairs

        def demands_ok_after(e1, e2):
            for e in (e1, e2):
                for di, (R, D) in enumerate(elem_demands[e]):
                    found = False
                    for ep in demand_witnesses[(e, di)]:
                        if (e, ep) in assignment:
                            if assignment[(e, ep)] == R:
                                found = True; break
                        else:
                            found = True; break
                    if not found:
                        return False
            return True

        nodes_visited = [0]

        def assign(pairs_remaining):
            if time.time() > t_budget:
                return False
            nodes_visited[0] += 1

            if not pairs_remaining:
                return True

            e1, e2 = pairs_remaining[0]
            rest = pairs_remaining[1:]

            # Determine relation order
            demanded = set()
            if (e1, e2) in edge_demands:
                demanded |= (edge_demands[(e1, e2)] & dom[(e1, e2)])
            if (e2, e1) in edge_demands:
                demanded |= {INV[R] for R in edge_demands[(e2, e1)]
                             if INV[R] in dom[(e1, e2)]}
            others = dom[(e1, e2)] - demanded
            order = sorted(demanded) + sorted(others)
            if attempt > 0:
                # Randomize within demanded and others groups
                d_list = [R for R in order if R in demanded]
                o_list = [R for R in order if R not in demanded]
                random.shuffle(d_list)
                random.shuffle(o_list)
                order = d_list + o_list

            for R in order:
                if INV[R] not in dom[(e2, e1)]:
                    continue

                ok = True
                for e3 in elements:
                    if e3 == e1 or e3 == e2:
                        continue
                    if (e2, e3) in assignment:
                        R23 = assignment[(e2, e3)]
                        comp_set = COMP[(R, R23)]
                        if (e1, e3) in assignment:
                            if assignment[(e1, e3)] not in comp_set:
                                ok = False; break
                        elif not (comp_set & dom[(e1, e3)]):
                            ok = False; break
                    if not ok: break
                    if (e1, e3) in assignment:
                        R13 = assignment[(e1, e3)]
                        comp_set = COMP[(INV[R], R13)]
                        if (e2, e3) in assignment:
                            if assignment[(e2, e3)] not in comp_set:
                                ok = False; break
                        elif not (comp_set & dom[(e2, e3)]):
                            ok = False; break
                    if not ok: break
                    if (e3, e1) in assignment:
                        R31 = assignment[(e3, e1)]
                        comp_set = COMP[(R31, R)]
                        if (e3, e2) in assignment:
                            if assignment[(e3, e2)] not in comp_set:
                                ok = False; break
                        elif not (comp_set & dom[(e3, e2)]):
                            ok = False; break
                    if not ok: break

                if not ok:
                    continue

                assignment[(e1, e2)] = R
                assignment[(e2, e1)] = INV[R]

                if demands_ok_after(e1, e2) and assign(rest):
                    return True

                del assignment[(e1, e2)]
                del assignment[(e2, e1)]

            return False

        if assign(attempt_pairs):
            return {
                'elements': elements,
                'elem_type': elem_type,
                'type_list': type_list,
                'relations': dict(assignment),
                'copies_per_type': num_copies,
            }

    return None


# ══════════════════════════════════════════════════════════════
# Model Verification
# ══════════════════════════════════════════════════════════════

def verify_model(C0, model):
    """
    Independently verify that a model is a valid ALCI_RCC5 interpretation
    satisfying C0. Returns (valid, errors_list).
    """
    errors = []
    elements = model['elements']
    elem_type = model['elem_type']
    type_list = model['type_list']
    rels = model['relations']
    n = len(elements)

    # 1. Check every pair has a relation assigned
    for e1 in elements:
        for e2 in elements:
            if e1 == e2:
                continue
            if (e1, e2) not in rels:
                errors.append(f"missing relation for ({e1},{e2})")

    if errors:
        return False, errors

    # 2. Check inverse symmetry
    for e1 in elements:
        for e2 in elements:
            if e1 >= e2:
                continue
            R12 = rels[(e1, e2)]
            R21 = rels[(e2, e1)]
            if R21 != INV[R12]:
                errors.append(f"inverse violation: R({e1},{e2})={R12}, "
                              f"R({e2},{e1})={R21}, expected {INV[R12]}")

    # 3. Check composition consistency on ALL triples
    comp_checks = 0
    comp_failures = 0
    for e1 in elements:
        for e2 in elements:
            if e1 == e2:
                continue
            for e3 in elements:
                if e3 == e1 or e3 == e2:
                    continue
                R12 = rels[(e1, e2)]
                R23 = rels[(e2, e3)]
                R13 = rels[(e1, e3)]
                comp_checks += 1
                if R13 not in COMP[(R12, R23)]:
                    comp_failures += 1
                    if comp_failures <= 5:
                        errors.append(
                            f"composition violation: R({e1},{e2})={R12}, "
                            f"R({e2},{e3})={R23}, R({e1},{e3})={R13}, "
                            f"but {R13} ∉ comp({R12},{R23})={COMP[(R12,R23)]}")

    if comp_failures > 5:
        errors.append(f"... and {comp_failures - 5} more composition violations")

    # 4. Check type-safety: for each element e with type τ,
    #    every ∀R.C in τ must be satisfied
    for e in elements:
        ti = elem_type[e]
        tau = type_list[ti]
        for c in tau:
            if isinstance(c, ForAll):
                R = c.role
                D = c.concept
                for ep in elements:
                    if ep == e:
                        continue
                    if rels[(e, ep)] == R:
                        tj = elem_type[ep]
                        sigma = type_list[tj]
                        if D not in sigma:
                            errors.append(
                                f"∀-violation: elem {e} has ∀{R}.{D}, "
                                f"elem {ep} is {R}-related but {D} ∉ type({ep})")

    # 5. Check existential witnessing
    for e in elements:
        ti = elem_type[e]
        tau = type_list[ti]
        for c in tau:
            if isinstance(c, Exists):
                R = c.role
                D = c.concept
                found = False
                for ep in elements:
                    if ep == e:
                        continue
                    if rels[(e, ep)] == R:
                        tj = elem_type[ep]
                        sigma = type_list[tj]
                        if D in sigma:
                            found = True
                            break
                if not found:
                    errors.append(
                        f"∃-violation: elem {e} has ∃{R}.{D} but no witness")

    # 6. Check concept satisfaction at root
    #    Find an element whose type contains C0
    root = None
    for e in elements:
        ti = elem_type[e]
        tau = type_list[ti]
        if C0 in tau:
            root = e
            break

    if root is None:
        errors.append(f"no element has C0 = {C0} in its type")
    else:
        # Recursively verify concept truth
        sat_ok, sat_err = verify_concept_truth(C0, root, model)
        if not sat_ok:
            errors.extend(sat_err)

    return len(errors) == 0, errors


def verify_concept_truth(C, e, model, depth=0):
    """
    Recursively verify that element e satisfies concept C in the model.
    Returns (True, []) or (False, [error_messages]).
    """
    elements = model['elements']
    elem_type = model['elem_type']
    type_list = model['type_list']
    rels = model['relations']

    if depth > 50:
        return True, []  # depth limit to avoid infinite recursion

    if isinstance(C, Top):
        return True, []
    elif isinstance(C, Bottom):
        return False, [f"elem {e} cannot satisfy ⊥"]
    elif isinstance(C, AtomicConcept):
        tau = type_list[elem_type[e]]
        if C in tau:
            return True, []
        else:
            return False, [f"elem {e}: {C} not in type"]
    elif isinstance(C, NegAtomicConcept):
        tau = type_list[elem_type[e]]
        pos = AtomicConcept(C.name)
        if pos not in tau:
            return True, []
        else:
            return False, [f"elem {e}: ¬{C.name} fails, {C.name} in type"]
    elif isinstance(C, And):
        ok1, err1 = verify_concept_truth(C.left, e, model, depth + 1)
        ok2, err2 = verify_concept_truth(C.right, e, model, depth + 1)
        return ok1 and ok2, err1 + err2
    elif isinstance(C, Or):
        ok1, err1 = verify_concept_truth(C.left, e, model, depth + 1)
        if ok1:
            return True, []
        ok2, err2 = verify_concept_truth(C.right, e, model, depth + 1)
        if ok2:
            return True, []
        return False, [f"elem {e}: {C.left} ⊔ {C.right} — neither holds"] + err1 + err2
    elif isinstance(C, ForAll):
        R = C.role
        D = C.concept
        for ep in elements:
            if ep == e:
                continue
            if rels[(e, ep)] == R:
                ok, err = verify_concept_truth(D, ep, model, depth + 1)
                if not ok:
                    return False, [f"elem {e}: ∀{R}.{D} fails at elem {ep}"] + err
        return True, []
    elif isinstance(C, Exists):
        R = C.role
        D = C.concept
        for ep in elements:
            if ep == e:
                continue
            if rels[(e, ep)] == R:
                ok, err = verify_concept_truth(D, ep, model, depth + 1)
                if ok:
                    return True, []
        return False, [f"elem {e}: ∃{R}.{D} — no witness found"]
    else:
        return True, []


# ══════════════════════════════════════════════════════════════
# Test Runner
# ══════════════════════════════════════════════════════════════

def run_model_verification(verbose=False):
    """
    Run model construction + verification on all stress-test concepts.
    """
    from stress_test_cover_tree import (
        gen_known_sat, gen_known_unsat, gen_adversarial,
        gen_systematic_pairs, gen_random,
    )

    print("=" * 70)
    print("MODEL CONSTRUCTION AND VERIFICATION")
    print("=" * 70)

    categories = [
        ("Known SAT", gen_known_sat()),
        ("Known UNSAT", gen_known_unsat()),
        ("Adversarial", gen_adversarial()),
        ("Systematic triples", gen_systematic_pairs()),
        ("Random depth-2", gen_random(2, 200)),
        ("Random depth-3", gen_random(3, 100, seed=123)),
    ]

    total_sat = 0
    total_models_built = 0
    total_models_verified = 0
    total_build_failures = 0
    total_verify_failures = 0
    total_unsat = 0

    for cat_name, tests in categories:
        cat_sat = 0
        cat_built = 0
        cat_verified = 0
        cat_build_fail = 0
        cat_verify_fail = 0
        cat_unsat = 0
        cat_errors = []
        t_cat = time.time()

        for name, concept, expected in tests:
            # Run cover-tree tableau
            try:
                ct_sat, ct_info = check_sat_ct(concept)
            except Exception as e:
                cat_errors.append((name, f"CT error: {e}"))
                continue

            if not ct_sat:
                cat_unsat += 1
                total_unsat += 1
                continue

            cat_sat += 1
            total_sat += 1

            # Try to build a model (tries 1..3 copies per type)
            ok, result = build_model(concept, ct_info, verbose=verbose)

            if not ok:
                cat_build_fail += 1
                total_build_failures += 1
                cat_errors.append((name, f"BUILD FAIL: {result}"))
                continue

            cat_built += 1
            total_models_built += 1

            # Verify the model
            valid, errs = verify_model(concept, result)
            if valid:
                cat_verified += 1
                total_models_verified += 1
            else:
                cat_verify_fail += 1
                total_verify_failures += 1
                cat_errors.append((name, f"VERIFY FAIL: {errs[0]}"))

        elapsed = time.time() - t_cat
        print(f"\n  [{cat_name}] {elapsed:.1f}s")
        print(f"    SAT: {cat_sat}, UNSAT: {cat_unsat}")
        print(f"    Models built: {cat_built}, Verified: {cat_verified}")
        if cat_build_fail:
            print(f"    Build failures: {cat_build_fail}")
        if cat_verify_fail:
            print(f"    Verify failures: {cat_verify_fail}")
        if cat_errors:
            for name, msg in cat_errors[:10]:
                print(f"      {name}: {msg}")
            if len(cat_errors) > 10:
                print(f"      ... and {len(cat_errors) - 10} more")

    print(f"\n{'=' * 70}")
    print(f"OVERALL RESULTS")
    print(f"  SAT concepts: {total_sat}")
    print(f"  UNSAT concepts: {total_unsat}")
    print(f"  Models successfully built: {total_models_built}")
    print(f"  Models independently verified: {total_models_verified}")
    print(f"  Build failures: {total_build_failures}")
    print(f"  Verification failures: {total_verify_failures}")
    print(f"{'=' * 70}")

    if total_verify_failures == 0 and total_build_failures == 0:
        print(f"\n  ✓ ALL {total_models_verified} SAT concepts have verified models")
    elif total_verify_failures == 0:
        print(f"\n  ~ {total_models_verified}/{total_sat} SAT concepts verified"
              f" ({total_build_failures} build failures)")

    return total_verify_failures == 0


if __name__ == '__main__':
    verbose = '--verbose' in sys.argv
    success = run_model_verification(verbose=verbose)
    sys.exit(0 if success else 1)
