#!/usr/bin/env python3
"""
Cover-Tree Decomposition Test for ALCI_RCC5
=============================================

Tests the cover-tree hypothesis: every satisfiable ALCI_RCC5 concept
has a model whose PP/PPI edges form a forest (each element has at most
one PP-parent, no PP-cycles) with {DR,PO}-only edges between non-ancestor
nodes.

Two-part test:
  Part A: Check models built by model_verifier for cover-tree structure.
          (These models are built WITHOUT any tree constraint, so finding
          cover-tree structure is non-trivial evidence.)

  Part B: Exhaustive enumeration of all valid small models (domain 2-4)
          using the tableau's type set. Count total vs. cover-tree models.
          A concept where NO model has cover-tree structure at any tested
          size would be evidence against the hypothesis.

A single counterexample would cast doubt on completeness of the cover-tree
tableau.  Zero counterexamples across hundreds of concepts = strong
evidence for decidability.

Usage:
  python3 decomposition_test.py              # run all tests
  python3 decomposition_test.py --verbose    # detailed output
"""

import sys
import time
import itertools

from alcircc5_reasoner import (
    DR, PO, PP, PPI, BASE_RELS, INV, COMP,
    Concept, AtomicConcept, NegAtomicConcept, Top, Bottom,
    And, Or, Exists, ForAll,
    closure, enumerate_types, compute_safe,
)
from cover_tree_tableau import check_satisfiability as check_sat_ct
from model_verifier import build_model


def flush_print(*args, **kwargs):
    """Print with immediate flush."""
    print(*args, **kwargs)
    sys.stdout.flush()


# ══════════════════════════════════════════════════════════════
# Cover-Tree Property Check
# ══════════════════════════════════════════════════════════════

def has_cover_tree(elements, rels):
    """
    Check if the PP relation's Hasse diagram forms a forest.

    PP is transitive (comp(PP,PP)={PP}), so a chain c PP d PP p means
    c PP p too.  The Hasse diagram retains only IMMEDIATE PP-parent edges
    (no transitive shortcuts).  The cover-tree property holds iff each
    element has at most one immediate PP-parent in the Hasse diagram.

    For n=2 this is trivially true.  For n>=3 the property fails when
    an element is PP to two elements that are NOT in a PP-chain with
    each other (i.e., two genuinely independent PP-parents).
    """
    # Build PP adjacency: pp_to[e] = {e2 : rels[(e,e2)] == PP}
    pp_to = {}
    for e in elements:
        pp_to[e] = set()
        for e2 in elements:
            if e2 != e and rels.get((e, e2)) == PP:
                pp_to[e].add(e2)

    # Compute Hasse diagram: immediate PP-parents only.
    # d is an immediate PP-parent of c iff:
    #   - c PP d, AND
    #   - there is no e with c PP e AND e PP d  (no element between them)
    for c in elements:
        if not pp_to[c]:
            continue

        immediate = []
        for d in pp_to[c]:
            is_immediate = True
            for e in pp_to[c]:
                if e != d and d in pp_to[e]:
                    # e is between c and d: c PP e PP d
                    is_immediate = False
                    break
            if is_immediate:
                immediate.append(d)

        if len(immediate) > 1:
            return False  # Two immediate PP-parents — not a forest

    return True


def cover_tree_info(elements, rels):
    """Return diagnostic info about the PP/PPI Hasse structure."""
    pp_to = {}
    for e in elements:
        pp_to[e] = set()
        for e2 in elements:
            if e2 != e and rels.get((e, e2)) == PP:
                pp_to[e].add(e2)

    # Compute Hasse immediate parents
    hasse_parent = {}
    multi_parent = []
    for c in elements:
        if not pp_to[c]:
            continue
        immediate = []
        for d in pp_to[c]:
            is_imm = True
            for e in pp_to[c]:
                if e != d and d in pp_to[e]:
                    is_imm = False
                    break
            if is_imm:
                immediate.append(d)
        if len(immediate) > 1:
            multi_parent.append((c, immediate))
        elif len(immediate) == 1:
            hasse_parent[c] = immediate[0]

    pp_count = sum(1 for e1 in elements for e2 in elements
                   if e1 < e2 and rels.get((e1, e2)) in (PP, PPI))
    dr_count = sum(1 for e1 in elements for e2 in elements
                   if e1 < e2 and rels.get((e1, e2)) == DR)
    po_count = sum(1 for e1 in elements for e2 in elements
                   if e1 < e2 and rels.get((e1, e2)) == PO)
    hasse_edges = len(hasse_parent)

    return {
        'pp_edges': pp_count,
        'hasse_edges': hasse_edges,
        'dr_edges': dr_count,
        'po_edges': po_count,
        'multi_parent': multi_parent,
    }


# ══════════════════════════════════════════════════════════════
# Part A: Check model_verifier's built models
# ══════════════════════════════════════════════════════════════

def check_built_models(verbose=False):
    """
    For each SAT concept, build a model via model_verifier and check
    if it has cover-tree structure.
    """
    from stress_test_cover_tree import (
        gen_known_sat, gen_known_unsat, gen_adversarial,
        gen_systematic_pairs, gen_random,
    )

    flush_print("\n" + "=" * 70)
    flush_print("PART A: COVER-TREE PROPERTY OF BUILT MODELS")
    flush_print("=" * 70)

    categories = [
        ("Known SAT", gen_known_sat()),
        ("Known UNSAT", gen_known_unsat()),
        ("Adversarial", gen_adversarial()),
        ("Systematic triples", gen_systematic_pairs()),
        ("Random depth-2", gen_random(2, 200)),
        ("Random depth-3", gen_random(3, 100, seed=123)),
    ]

    total_sat = 0
    total_built = 0
    total_ct = 0
    total_non_ct = 0
    non_ct_examples = []

    for cat_name, tests in categories:
        cat_sat = 0
        cat_built = 0
        cat_ct = 0
        cat_non_ct = 0
        cat_build_fail = 0
        cat_examples = []
        t_cat = time.time()

        for name, concept, expected in tests:
            try:
                ct_sat, ct_info = check_sat_ct(concept)
            except Exception:
                continue
            if not ct_sat:
                continue
            cat_sat += 1

            ok, result = build_model(concept, ct_info)
            if not ok:
                cat_build_fail += 1
                continue
            cat_built += 1

            if has_cover_tree(result['elements'], result['relations']):
                cat_ct += 1
            else:
                cat_non_ct += 1
                info = cover_tree_info(result['elements'], result['relations'])
                cat_examples.append((name, info))

        elapsed = time.time() - t_cat
        flush_print(f"\n  [{cat_name}] {elapsed:.1f}s")
        flush_print(f"    SAT: {cat_sat}, Built: {cat_built}, "
                    f"Build fail: {cat_build_fail}")
        flush_print(f"    Cover-tree: {cat_ct}, Non-cover-tree: {cat_non_ct}")
        if cat_examples:
            for ex_name, ex_info in cat_examples[:5]:
                flush_print(f"      Non-CT: {ex_name} — "
                            f"PP:{ex_info['pp_edges']} "
                            f"hasse:{ex_info['hasse_edges']} "
                            f"DR:{ex_info['dr_edges']}"
                            f" PO:{ex_info['po_edges']} "
                            f"multi-parent:{ex_info['multi_parent']}")

        total_sat += cat_sat
        total_built += cat_built
        total_ct += cat_ct
        total_non_ct += cat_non_ct
        non_ct_examples.extend(cat_examples)

    flush_print(f"\n  PART A SUMMARY")
    flush_print(f"    Models checked: {total_built}")
    pct = 100 * total_ct / max(1, total_built)
    flush_print(f"    Cover-tree: {total_ct} ({pct:.1f}%)")
    flush_print(f"    Non-cover-tree: {total_non_ct}")
    if non_ct_examples:
        flush_print(f"    Non-CT examples ({len(non_ct_examples)}):")
        for ex_name, ex_info in non_ct_examples[:10]:
            flush_print(f"      {ex_name}")

    return total_ct, total_non_ct, non_ct_examples


# ══════════════════════════════════════════════════════════════
# Infinite Cover-Tree Model Detection
# ══════════════════════════════════════════════════════════════

def _expand_pool(ct_info):
    """Expand the type pool beyond the tableau's type set T."""
    T = sorted(ct_info['type_set'])
    type_list = ct_info['type_list']
    safe = ct_info['safe']
    demands = ct_info['demands']
    n_all = len(type_list)

    T_set = set(T)
    extra_types = set()
    for ti in T:
        for R, D in demands[ti]:
            for tj in range(n_all):
                if tj not in T_set and D in type_list[tj] and R in safe[(ti, tj)]:
                    extra_types.add(tj)
    extra2 = set()
    for ti in extra_types:
        for R, D in demands[ti]:
            for tj in range(n_all):
                if tj not in T_set and tj not in extra_types:
                    if D in type_list[tj] and R in safe[(ti, tj)]:
                        extra2.add(tj)
    extra_types |= extra2
    return T + sorted(extra_types)


def needs_infinite_ct(C0, ct_info):
    """
    Check if the concept needs an infinite cover-tree model.

    Uses the expanded type pool (not just T) to check chain termination.
    """
    type_list = ct_info['type_list']
    safe = ct_info['safe']
    demands = ct_info['demands']
    pool = _expand_pool(ct_info)

    # Check PP-direction (upward chains)
    pp_demands = {ti: [(R, D) for R, D in demands[ti] if R == PP]
                  for ti in pool}
    can_top = set()
    changed = True
    while changed:
        changed = False
        for ti in pool:
            if ti in can_top:
                continue
            if not pp_demands[ti]:
                can_top.add(ti)
                changed = True
                continue
            all_ok = True
            for R, D in pp_demands[ti]:
                witnesses = [tj for tj in pool
                             if D in type_list[tj] and PP in safe[(ti, tj)]]
                if not any(tj in can_top for tj in witnesses):
                    all_ok = False
                    break
            if all_ok:
                can_top.add(ti)
                changed = True

    # Check PPI-direction (downward chains)
    ppi_demands = {ti: [(R, D) for R, D in demands[ti] if R == PPI]
                   for ti in pool}
    can_leaf = set()
    changed = True
    while changed:
        changed = False
        for ti in pool:
            if ti in can_leaf:
                continue
            if not ppi_demands[ti]:
                can_leaf.add(ti)
                changed = True
                continue
            all_ok = True
            for R, D in ppi_demands[ti]:
                witnesses = [tj for tj in pool
                             if D in type_list[tj] and PPI in safe[(ti, tj)]]
                if not any(tj in can_leaf for tj in witnesses):
                    all_ok = False
                    break
            if all_ok:
                can_leaf.add(ti)
                changed = True

    # Root types must be in both can_top and can_leaf for finite CT model
    root_types = [ti for ti in pool if C0 in type_list[ti]]

    pp_infinite = not root_types or all(ti not in can_top for ti in root_types)
    ppi_infinite = not root_types or all(ti not in can_leaf for ti in root_types)

    reason = None
    if pp_infinite:
        reason = "self-referencing PP-demands (infinite ascending chain)"
    elif ppi_infinite:
        reason = "self-referencing PPI-demands (infinite descending chain)"

    return pp_infinite or ppi_infinite, reason


def try_pp_chain_model(C0, ct_info, max_depth=8, timeout=10.0):
    """
    Try to construct a valid PP-chain (linear) cover-tree model.

    Builds a single PP-chain: d0 PP d1 PP d2 PP ... PP dk.
    At each step, all ancestors' unsatisfied PP demands are tracked.
    A demand ∃PP.D of ancestor a is satisfied when some descendant
    has D in its type (since a PP d_i PP ... PP d_j implies a PP d_j).
    Returns True if a valid finite chain is found.
    """
    type_list = ct_info['type_list']
    safe = ct_info['safe']
    demands = ct_info['demands']
    pool = _expand_pool(ct_info)

    root_types = [ti for ti in pool if C0 in type_list[ti]]
    if not root_types:
        return False

    # Sort: fewer ∀PP formulas = more permissive = tried first
    def forall_pp_count(t):
        return sum(1 for f in type_list[t]
                   if hasattr(f, 'role') and f.__class__.__name__ == 'ForAll'
                   and f.role == PP)
    root_types.sort(key=forall_pp_count)

    deadline = time.time() + timeout
    for root in root_types:
        if time.time() > deadline:
            break
        # pending = list of (demanded_concept) not yet satisfied
        pp_dems = [D for R, D in demands[root] if R == PP]
        if not pp_dems:
            return True  # Root has no PP demands — trivial model
        if _extend_chain(root, [root], pp_dems, type_list, safe, demands,
                         pool, max_depth, deadline):
            return True
    return False


def _extend_chain(new_type, chain_types, pending_demands, type_list, safe,
                  demands, pool, max_depth, deadline):
    """
    Extend a PP-chain by adding one more element.

    chain_types: types of elements so far [root_type, child_type, ...]
    pending_demands: list of concepts D where some ancestor has ∃PP.D unsatisfied
    new_type: the type just added at the end of the chain

    Any pending demand D is satisfied if D ∈ type_list[new_type].
    New PP demands from new_type are added to pending.
    Chain terminates when pending is empty.
    """
    if time.time() > deadline:
        return False

    # Remove satisfied demands
    remaining = [D for D in pending_demands if D not in type_list[new_type]]

    # Add new PP demands from the new element
    new_dems = [D for R, D in demands[new_type] if R == PP]
    # These new demands might also be immediately satisfied by new_type itself
    # (self-witnessing through ancestor relationship, which doesn't apply here)
    remaining.extend(new_dems)

    if not remaining:
        return True  # All demands satisfied — valid finite chain

    if len(chain_types) >= max_depth:
        return False

    # Try extending with another PP-child
    # Need: PP-safe from ALL existing chain elements
    # Collect candidates sorted by how many pending demands they satisfy (desc)
    candidates = []
    for cj in pool:
        ok = True
        for anc in chain_types:
            if PP not in safe[(anc, cj)] or PPI not in safe[(cj, anc)]:
                ok = False
                break
        if not ok:
            continue
        # Count how many pending demands this candidate satisfies
        sat_count = sum(1 for D in remaining if D in type_list[cj])
        pp_cnt = sum(1 for R, D in demands[cj] if R == PP)
        candidates.append((-sat_count, pp_cnt, cj))  # most satisfying first

    candidates.sort()

    for _, _, cj in candidates:
        if time.time() > deadline:
            return False
        if _extend_chain(cj, chain_types + [cj], remaining, type_list,
                         safe, demands, pool, max_depth, deadline):
            return True
    return False


# ══════════════════════════════════════════════════════════════
# Part B: Exhaustive Model Enumeration
# ══════════════════════════════════════════════════════════════

def exhaustive_count(C0, ct_info, max_domain=6, time_limit=1.5,
                     max_models=20000):
    """
    Enumerate all valid models for C0 using the tableau's type set T
    (plus leaf types for recursive demands).

    Returns {size: (total_models, cover_tree_models, timed_out)}
    """
    type_list = ct_info['type_list']
    safe = ct_info['safe']
    demands = ct_info['demands']

    type_pool = _expand_pool(ct_info)
    root_types = [i for i in type_pool if C0 in type_list[i]]
    if not root_types:
        return {}

    results = {}
    t_global = time.time()

    for n in range(2, max_domain + 1):
        if time.time() - t_global > time_limit * max_domain:
            break

        space = len(root_types) * len(type_pool) ** (n - 1)
        if space > 200000:
            results[n] = (0, 0, True)
            continue

        t0 = time.time()
        total = [0]
        ct = [0]
        timeout = [False]
        elems = list(range(n))
        pairs = [(i, j) for i in elems for j in elems if i < j]

        for rti in root_types:
            if timeout[0]:
                break

            for ot in itertools.product(type_pool, repeat=n - 1):
                if timeout[0]:
                    break
                if time.time() - t0 > time_limit:
                    timeout[0] = True
                    break
                if total[0] >= max_models:
                    timeout[0] = True
                    break

                ta = [rti] + list(ot)
                et = {e: ta[e] for e in elems}

                # Compute safe domains for directed pairs
                dom = {}
                skip = False
                for e1 in elems:
                    for e2 in elems:
                        if e1 == e2:
                            continue
                        s = set(safe[(et[e1], et[e2])])
                        if not s:
                            skip = True
                            break
                        dom[(e1, e2)] = s
                    if skip:
                        break
                if skip:
                    continue

                # Inverse pruning
                for e1 in elems:
                    for e2 in elems:
                        if e1 >= e2:
                            continue
                        fwd = {R for R in dom[(e1, e2)]
                               if INV[R] in dom[(e2, e1)]}
                        bwd = {R for R in dom[(e2, e1)]
                               if INV[R] in dom[(e1, e2)]}
                        if not fwd or not bwd:
                            skip = True
                            break
                        dom[(e1, e2)] = fwd
                        dom[(e2, e1)] = bwd
                    if skip:
                        break
                if skip:
                    continue

                # Backtracking: enumerate all valid relation assignments
                asgn = {}

                def bt(pidx):
                    if timeout[0]:
                        return
                    if time.time() - t0 > time_limit or total[0] >= max_models:
                        timeout[0] = True
                        return

                    if pidx == len(pairs):
                        # Check demand satisfaction
                        for e in elems:
                            for R, D in demands[et[e]]:
                                found = False
                                for ep in elems:
                                    if ep == e:
                                        continue
                                    if (asgn[(e, ep)] == R
                                            and D in type_list[et[ep]]):
                                        found = True
                                        break
                                if not found:
                                    return
                        total[0] += 1
                        if has_cover_tree(elems, asgn):
                            ct[0] += 1
                        return

                    e1, e2 = pairs[pidx]

                    for R in sorted(dom[(e1, e2)]):
                        if INV[R] not in dom[(e2, e1)]:
                            continue

                        # Composition consistency with assigned pairs
                        ok = True
                        for e3 in elems:
                            if e3 == e1 or e3 == e2:
                                continue
                            if (e2, e3) in asgn:
                                cs = COMP[(R, asgn[(e2, e3)])]
                                if (e1, e3) in asgn:
                                    if asgn[(e1, e3)] not in cs:
                                        ok = False
                                        break
                                elif not (cs & dom[(e1, e3)]):
                                    ok = False
                                    break
                            if (e1, e3) in asgn:
                                cs = COMP[(INV[R], asgn[(e1, e3)])]
                                if (e2, e3) in asgn:
                                    if asgn[(e2, e3)] not in cs:
                                        ok = False
                                        break
                                elif not (cs & dom[(e2, e3)]):
                                    ok = False
                                    break
                            if (e3, e1) in asgn:
                                cs = COMP[(asgn[(e3, e1)], R)]
                                if (e3, e2) in asgn:
                                    if asgn[(e3, e2)] not in cs:
                                        ok = False
                                        break
                                elif not (cs & dom[(e3, e2)]):
                                    ok = False
                                    break

                        if not ok:
                            continue

                        asgn[(e1, e2)] = R
                        asgn[(e2, e1)] = INV[R]
                        bt(pidx + 1)
                        del asgn[(e1, e2)]
                        del asgn[(e2, e1)]

                bt(0)

        results[n] = (total[0], ct[0], timeout[0])

    return results


def run_exhaustive_tests(verbose=False):
    """Run exhaustive enumeration for all stress-test SAT concepts."""
    from stress_test_cover_tree import (
        gen_known_sat, gen_known_unsat, gen_adversarial,
        gen_systematic_pairs, gen_random,
    )

    flush_print("\n" + "=" * 70)
    flush_print("PART B: EXHAUSTIVE MODEL ENUMERATION")
    flush_print("=" * 70)

    categories = [
        ("Known SAT", gen_known_sat()),
        ("Known UNSAT", gen_known_unsat()),
        ("Adversarial", gen_adversarial()),
        ("Systematic triples", gen_systematic_pairs()),
        ("Random depth-2", gen_random(2, 200)),
        ("Random depth-3", gen_random(3, 100, seed=123)),
    ]

    total_checked = 0
    total_has_ct = 0
    total_no_ct = 0
    total_infinite = 0
    total_no_models = 0
    no_ct_concepts = []
    infinite_concepts = []
    grand_total = 0
    grand_ct = 0

    for cat_name, tests in categories:
        cat_checked = 0
        cat_has_ct = 0
        cat_no_ct = 0
        cat_infinite = 0
        cat_no_models = 0
        cat_problems = []
        cat_total_models = 0
        cat_ct_models = 0
        t_cat = time.time()

        for name, concept, expected in tests:
            try:
                ct_sat, ct_info = check_sat_ct(concept)
            except Exception:
                continue
            if not ct_sat:
                continue

            cat_checked += 1
            res = exhaustive_count(concept, ct_info, max_domain=6,
                                   time_limit=1.5)

            concept_total = sum(r[0] for r in res.values())
            concept_ct = sum(r[1] for r in res.values())
            cat_total_models += concept_total
            cat_ct_models += concept_ct

            # Check if any size with models completed without timeout
            any_completed_with_models = any(
                r[0] > 0 and not r[2] for r in res.values())
            all_timed_out = all(
                r[2] for r in res.values() if r[0] > 0)

            if concept_ct > 0:
                cat_has_ct += 1
            elif concept_total == 0:
                # No models at tested sizes — try targeted chain search
                if try_pp_chain_model(concept, ct_info):
                    cat_has_ct += 1
                else:
                    inf, reason = needs_infinite_ct(concept, ct_info)
                    if inf:
                        cat_infinite += 1
                        infinite_concepts.append((name, reason))
                    else:
                        cat_no_models += 1
            else:
                # Models found but none with CT — check if infinite needed
                inf, reason = needs_infinite_ct(concept, ct_info)
                if inf:
                    cat_infinite += 1
                    infinite_concepts.append((name, reason))
                elif any_completed_with_models:
                    # At least one size completed fully with models,
                    # none had CT — genuine counterexample
                    cat_no_ct += 1
                    cat_problems.append((name, res))
                else:
                    # Only timed-out sizes had models — inconclusive
                    # Try targeted chain search
                    if try_pp_chain_model(concept, ct_info):
                        cat_has_ct += 1
                    else:
                        cat_no_models += 1

            if verbose and concept_total > 0:
                pct = 100 * concept_ct / concept_total
                sizes = " ".join(
                    f"n={sz}:{r[0]}/{r[1]}"
                    for sz, r in sorted(res.items()) if r[0] > 0)
                flush_print(f"    {name}: {concept_ct}/{concept_total} CT "
                            f"({pct:.0f}%) [{sizes}]")

        elapsed = time.time() - t_cat
        flush_print(f"\n  [{cat_name}] {elapsed:.1f}s")
        flush_print(f"    SAT concepts: {cat_checked}")
        flush_print(f"    Has finite CT model: {cat_has_ct}, "
                    f"Needs infinite CT: {cat_infinite}")
        if cat_no_ct:
            flush_print(f"    *** GENUINE counterexamples: {cat_no_ct}")
        if cat_no_models:
            flush_print(f"    No models at tested sizes: {cat_no_models}")
        if cat_total_models > 0:
            pct = 100 * cat_ct_models / cat_total_models
            flush_print(f"    Models: {cat_total_models} total, "
                        f"{cat_ct_models} CT ({pct:.1f}%)")
        if cat_problems:
            flush_print(f"    *** POTENTIAL COUNTEREXAMPLES:")
            for pname, pres in cat_problems[:5]:
                flush_print(f"      {pname}: {pres}")

        total_checked += cat_checked
        total_has_ct += cat_has_ct
        total_no_ct += cat_no_ct
        total_infinite += cat_infinite
        total_no_models += cat_no_models
        no_ct_concepts.extend(cat_problems)
        grand_total += cat_total_models
        grand_ct += cat_ct_models

    flush_print(f"\n  PART B SUMMARY")
    flush_print(f"    SAT concepts checked: {total_checked}")
    flush_print(f"    Has finite CT model: {total_has_ct} "
                f"({100 * total_has_ct / max(1, total_checked):.1f}%)")
    flush_print(f"    Needs infinite CT model: {total_infinite}")
    flush_print(f"    No models at tested sizes: {total_no_models}")
    flush_print(f"    Genuine counterexamples: {total_no_ct}")
    if grand_total > 0:
        pct = 100 * grand_ct / grand_total
        flush_print(f"    Total models: {grand_total}, "
                    f"Cover-tree: {grand_ct} ({pct:.1f}%)")
    if infinite_concepts:
        flush_print(f"\n    Concepts needing infinite CT model "
                    f"({len(infinite_concepts)}):")
        for pname, preason in infinite_concepts[:10]:
            flush_print(f"      {pname}: {preason}")
    if no_ct_concepts:
        flush_print(f"\n    *** GENUINE COUNTEREXAMPLES "
                    f"({len(no_ct_concepts)}): ***")
        for pname, pres in no_ct_concepts:
            flush_print(f"      {pname}: {pres}")

    return total_no_ct == 0, no_ct_concepts


# ══════════════════════════════════════════════════════════════
# Main
# ══════════════════════════════════════════════════════════════

if __name__ == '__main__':
    verbose = '--verbose' in sys.argv

    flush_print("=" * 70)
    flush_print("COVER-TREE DECOMPOSITION TEST")
    flush_print("=" * 70)

    # Part A: check models built by model_verifier
    ct_a, non_ct_a, non_ct_examples = check_built_models(verbose=verbose)

    # Part B: exhaustive enumeration
    no_counterexamples, counterexamples = run_exhaustive_tests(verbose=verbose)

    # Overall summary
    flush_print("\n" + "=" * 70)
    flush_print("OVERALL RESULTS")
    flush_print("=" * 70)
    total_a = ct_a + non_ct_a
    if total_a > 0:
        flush_print(f"  Part A: {ct_a}/{total_a} built models have CT "
                    f"structure ({100 * ct_a / total_a:.1f}%)")
    if no_counterexamples:
        flush_print(f"  Part B: ZERO genuine counterexamples")
        flush_print(f"          (concepts without finite CT models all"
                    f" need infinite CT trees)")
    else:
        flush_print(f"  Part B: {len(counterexamples)} GENUINE "
                    f"counterexamples found!")
    flush_print("=" * 70)

    sys.exit(0 if no_counterexamples else 1)
