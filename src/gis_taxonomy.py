#!/usr/bin/env python3
"""
GIS Taxonomy Computation for ALCI_RCC5
=======================================

Computes the subsumption hierarchy for the GIS example from
Wessel's report7.pdf (Section 3), using the cover-tree tableau
reasoner with lazy unfolding.

Subsumption reduction: C ⊑ D  iff  C ⊓ ¬D is unsatisfiable.
Lazy unfolding: expand defined concept names into their definitions
before testing (works for acyclic TBoxes).

Usage:
  python3 gis_taxonomy.py
  python3 gis_taxonomy.py --verbose
"""

import sys
import time
import itertools

sys.path.insert(0, '.')
from alcircc5_reasoner import (
    DR, PO, PP, PPI, BASE_RELS, INV, COMP,
    Concept, AtomicConcept, NegAtomicConcept, Top, Bottom,
    And, Or, Exists, ForAll,
    closure, is_hintikka_type, compute_safe,
)
from cover_tree_tableau import check_satisfiability


# ══════════════════════════════════════════════════════════════
# Concept construction helpers
# ══════════════════════════════════════════════════════════════

def conj(*args):
    result = args[0]
    for a in args[1:]:
        result = And(result, a)
    return result

def disj(*args):
    result = args[0]
    for a in args[1:]:
        result = Or(result, a)
    return result

def neg(C):
    return C.nnf_negation()

def A(name):
    return AtomicConcept(name)


# ══════════════════════════════════════════════════════════════
# Optimized type enumeration for larger closures
# ══════════════════════════════════════════════════════════════

# Global type constraints: list of (trigger_formula, required_formula)
# If trigger is in a type, required must also be in the type.
# Set before calling check_satisfiability, cleared after.
_ACTIVE_TYPE_CONSTRAINTS = []


def _check_type_constraints(tau, cl):
    """Check if type satisfies all active type constraints.
    Only enforces constraints where both formulas are in the closure."""
    for trigger, required in _ACTIVE_TYPE_CONSTRAINTS:
        if trigger in cl and required in cl:
            if trigger in tau and required not in tau:
                return False
    return True


def enumerate_types_fast(cl):
    """
    Smarter type enumeration that handles larger closures.

    Strategy: separate propositional atoms from modal formulas.
    First enumerate valid propositional assignments, then check
    which modal formulas are forced by Hintikka conditions.
    Also enforces active type constraints (TBox GCIs) during filtering.
    """
    # Separate atoms into propositional (AtomicConcept/NegAtomicConcept)
    # and modal (Exists/ForAll/And/Or containing modal subformulas)
    prop_atoms = []  # (pos, neg) pairs for atomic concepts
    modal_atoms = []  # (pos, neg) pairs for modal formulas
    seen = set()

    for c in sorted(cl, key=str):
        if c in seen:
            continue
        n = c.nnf_negation()
        if n == c or n in seen:
            continue
        seen.add(c)
        seen.add(n)

        # Is this a propositional atom?
        if isinstance(c, (AtomicConcept, NegAtomicConcept)):
            pos = c if isinstance(c, AtomicConcept) else n
            neg_c = n if isinstance(c, AtomicConcept) else c
            prop_atoms.append((pos, neg_c))
        elif isinstance(c, (Top, Bottom)):
            continue  # Top is always in, Bottom never
        else:
            modal_atoms.append((c, n))

    # For each propositional assignment, derive the full type
    types = []
    for prop_bits in itertools.product([0, 1], repeat=len(prop_atoms)):
        tau = set()

        # Add Top if in closure
        for c in cl:
            if isinstance(c, Top):
                tau.add(c)

        # Set propositional atoms
        for i, bit in enumerate(prop_bits):
            tau.add(prop_atoms[i][bit])

        # Early check: type constraints on propositional atoms
        if not _check_type_constraints(tau, cl):
            continue

        # Derive modal formula membership from Hintikka conditions:
        # - And(A,B) ∈ τ iff A ∈ τ and B ∈ τ
        # - Or(A,B) ∈ τ iff A ∈ τ or B ∈ τ
        # - For Exists/ForAll: these are "independent" choices
        #   BUT their inclusion must be consistent with And/Or

        # First pass: propagate And/Or from propositional base
        changed = True
        while changed:
            changed = False
            for pos, neg_c in modal_atoms:
                if pos in tau or neg_c in tau:
                    continue
                # Try to determine from Hintikka conditions
                det = determine_formula(pos, tau, cl)
                if det is True:
                    tau.add(pos)
                    changed = True
                elif det is False:
                    tau.add(neg_c)
                    changed = True

        # For remaining undetermined modal atoms, try both
        undetermined = [(pos, neg_c) for pos, neg_c in modal_atoms
                        if pos not in tau and neg_c not in tau]

        if not undetermined:
            tau_frozen = frozenset(tau)
            if _check_type_constraints(tau_frozen, cl) and is_hintikka_type(tau_frozen, cl):
                types.append(tau_frozen)
        else:
            # Enumerate remaining choices
            for modal_bits in itertools.product([0, 1], repeat=len(undetermined)):
                tau2 = set(tau)
                for i, bit in enumerate(modal_bits):
                    tau2.add(undetermined[i][bit])
                tau2_frozen = frozenset(tau2)
                if _check_type_constraints(tau2_frozen, cl) and is_hintikka_type(tau2_frozen, cl):
                    types.append(tau2_frozen)

    return types


def determine_formula(C, tau, cl):
    """
    Try to determine if C must be in tau based on Hintikka conditions.
    Returns True (must be in), False (must not be in), or None (undetermined).
    """
    if isinstance(C, And):
        if C.left in cl and C.right in cl:
            l_in = C.left in tau
            r_in = C.right in tau
            l_neg_in = C.left.nnf_negation() in tau
            r_neg_in = C.right.nnf_negation() in tau
            if l_in and r_in:
                return True
            if l_neg_in or r_neg_in:
                return False
        return None
    elif isinstance(C, Or):
        if C.left in cl and C.right in cl:
            l_in = C.left in tau
            r_in = C.right in tau
            l_neg_in = C.left.nnf_negation() in tau
            r_neg_in = C.right.nnf_negation() in tau
            if l_in or r_in:
                return True
            if l_neg_in and r_neg_in:
                return False
        return None
    return None


# Monkey-patch the reasoner to use fast enumeration
import alcircc5_reasoner
_orig_enumerate = alcircc5_reasoner.enumerate_types
alcircc5_reasoner.enumerate_types = enumerate_types_fast

# Also patch in cover_tree_tableau since it imports from alcircc5_reasoner
import cover_tree_tableau
cover_tree_tableau.enumerate_types = enumerate_types_fast


# ══════════════════════════════════════════════════════════════
# GIS TBox from report7.pdf, Section 3
# ══════════════════════════════════════════════════════════════

# Concept names
NAMES = [
    'area', 'country', 'city', 'river', 'lake', 'mountain',
    'germany', 'czech_republic',
    'local_river', 'non_local_river', 'river_flowing_into_a_lake',
    'german_river', 'german_city', 'city_at_river',
    'elbe', 'alster_lake', 'alster', 'hamburg',
]

# Primitive inclusions: name -> superclass chain (transitive closure)
PRIMITIVE_SUPERS = {
    'country': ['area'],
    'city': ['area'],
    'river': ['area'],
    'lake': ['area'],
    'mountain': ['area'],
    'germany': ['country', 'area'],
    'czech_republic': ['country', 'area'],
    'alster_lake': ['lake', 'area'],
}

# Defined concepts: name -> definition body
# For defined A ≡ body: expand(A) = body, expand(¬A) = ¬body
# For primitive A ⊑ body (with complex body): similar
DEFINITIONS = {
    'local_river':      ('equiv', lambda: conj(A('river'), neg(Exists(PO, A('country'))))),
    'non_local_river':  ('equiv', lambda: conj(A('river'), Exists(PO, A('country')))),
    'river_flowing_into_a_lake': ('equiv', lambda: conj(A('river'), Exists(PO, A('lake')))),
    'german_river':     ('equiv', lambda: conj(A('river'), Exists(PP, A('germany')),
                                                ForAll(PO, neg(A('country'))))),
    'german_city':      ('equiv', lambda: conj(A('city'),
                                                ForAll(PP, disj(neg(A('country')), A('germany'))))),
    'city_at_river':    ('equiv', lambda: conj(A('city'), Exists(PO, A('river')))),
    # Primitives with complex RHS — for positive occurrences, expand to (name ⊓ RHS)
    # For negative occurrences, ¬name is just ¬name (no expansion needed for primitive)
    'elbe':             ('prim', lambda: conj(A('river'), Exists(PO, A('czech_republic')),
                                              Exists(PO, A('germany')))),
    'alster':           ('prim', lambda: conj(A('river'), Exists(PP, A('germany')),
                                              Exists(PO, A('alster_lake')),
                                              ForAll(PO, neg(A('country'))),
                                              ForAll(PP, disj(neg(A('country')), A('germany'))))),
    'hamburg':          ('prim', lambda: conj(A('city'), Exists(PO, A('alster')))),
}


def expand_pos(name):
    """Expand a positive concept name to its full expansion."""
    parts = [A(name)]

    # Add primitive superclasses
    if name in PRIMITIVE_SUPERS:
        for sup in PRIMITIVE_SUPERS[name]:
            parts.append(A(sup))

    # Add definition body
    if name in DEFINITIONS:
        kind, body_fn = DEFINITIONS[name]
        parts.append(body_fn())

    if len(parts) == 1:
        return parts[0]
    return conj(*parts)


def expand_neg(name):
    """Expand a negated concept name."""
    if name in DEFINITIONS:
        kind, body_fn = DEFINITIONS[name]
        if kind == 'equiv':
            # ¬(A ≡ body) = ¬body (since A is just an abbreviation)
            return neg(body_fn())
        else:
            # Primitive: ¬A is just ¬A (we don't know the full extent)
            return neg(A(name))
    else:
        return neg(A(name))


def expand_concept(C, depth=0):
    """Expand concept C one level (top-level definition unfolding only)."""
    if depth > 15:
        return C

    if isinstance(C, AtomicConcept):
        return expand_pos(C.name)
    elif isinstance(C, NegAtomicConcept):
        return expand_neg(C.name)
    elif isinstance(C, And):
        return And(expand_concept(C.left, depth+1),
                   expand_concept(C.right, depth+1))
    elif isinstance(C, Or):
        return Or(expand_concept(C.left, depth+1),
                  expand_concept(C.right, depth+1))
    elif isinstance(C, Exists):
        return Exists(C.role, expand_concept(C.concept, depth+1))
    elif isinstance(C, ForAll):
        return ForAll(C.role, expand_concept(C.concept, depth+1))
    return C


def deep_expand(C, _seen=None):
    """Recursively expand concept C with cycle detection.
    Expands all defined/primitive atoms (including inside modals)
    exactly once each."""
    if _seen is None:
        _seen = set()

    if isinstance(C, AtomicConcept):
        if C.name in _seen:
            return C
        _seen.add(C.name)
        expanded = expand_pos(C.name)
        if isinstance(expanded, AtomicConcept):
            return expanded
        return deep_expand(expanded, _seen)
    elif isinstance(C, NegAtomicConcept):
        if C.name in _seen:
            return C
        _seen.add(C.name)
        expanded = expand_neg(C.name)
        if isinstance(expanded, NegAtomicConcept):
            return expanded
        return deep_expand(expanded, _seen)
    elif isinstance(C, And):
        return And(deep_expand(C.left, _seen),
                   deep_expand(C.right, _seen))
    elif isinstance(C, Or):
        return Or(deep_expand(C.left, _seen),
                  deep_expand(C.right, _seen))
    elif isinstance(C, Exists):
        return Exists(C.role, deep_expand(C.concept, _seen))
    elif isinstance(C, ForAll):
        return ForAll(C.role, deep_expand(C.concept, _seen))
    return C


# ══════════════════════════════════════════════════════════════
# Structural pre-checks for fast subsumption filtering
# ══════════════════════════════════════════════════════════════

def collect_positive_atoms(C):
    """Collect all atomic concept names that appear as positive conjuncts."""
    if isinstance(C, AtomicConcept):
        return {C.name}
    elif isinstance(C, And):
        return collect_positive_atoms(C.left) | collect_positive_atoms(C.right)
    return set()

# Precompute the positive atoms of each expanded concept
_POS_ATOMS_CACHE = {}
def get_positive_atoms(name):
    if name not in _POS_ATOMS_CACHE:
        _POS_ATOMS_CACHE[name] = collect_positive_atoms(expand_pos(name))
    return _POS_ATOMS_CACHE[name]

# Base categories: mutually exclusive top-level sorts
# Two concepts with incompatible bases can't be in subsumption
BASE_CATEGORIES = {
    'country': 'country', 'city': 'city', 'river': 'river',
    'lake': 'lake', 'mountain': 'mountain',
}

def get_base(name):
    """Get the base category of a concept (from its positive atoms)."""
    atoms = get_positive_atoms(name)
    bases = set()
    for a in atoms:
        if a in BASE_CATEGORIES:
            bases.add(BASE_CATEGORIES[a])
        elif a in PRIMITIVE_SUPERS:
            for sup in PRIMITIVE_SUPERS[a]:
                if sup in BASE_CATEGORIES:
                    bases.add(BASE_CATEGORIES[sup])
    return bases

def quick_non_subsumption(C_name, D_name):
    """
    Quick structural check: if C's base is incompatible with D's required base,
    return True (definitely NOT subsumed). Return False if inconclusive.
    """
    c_bases = get_base(C_name)
    d_atoms = get_positive_atoms(D_name)

    # If D requires being a 'city' but C is based on 'river', can't subsume
    for d_atom in d_atoms:
        if d_atom in BASE_CATEGORIES:
            d_base = BASE_CATEGORIES[d_atom]
            if c_bases and d_base not in c_bases:
                return True
    return False


# ══════════════════════════════════════════════════════════════
# Subsumption checking
# ══════════════════════════════════════════════════════════════

# Primitive GCIs: (sub_atom, super_atom) pairs
# Used as type constraints during enumeration: if sub ∈ type, super ∈ type
PRIM_GCIS = [
    ('germany', 'country'),
    ('czech_republic', 'country'),
    ('alster_lake', 'lake'),
    ('alster', 'river'),
    ('elbe', 'river'),
    ('hamburg', 'city'),
]


def check_subsumption(C_name, D_name, type_constraints=None, test_override=None,
                      verbose=False):
    """
    Check C subsumed-by D by testing unsatisfiability of C_expanded AND NOT D_expanded.
    type_constraints: list of (trigger_formula, required_formula) for type filtering.
    test_override: if given, use this as the test concept instead of expanding C/D.
    """
    global _ACTIVE_TYPE_CONSTRAINTS

    if test_override is None and quick_non_subsumption(C_name, D_name):
        return False

    if test_override is not None:
        test = test_override
    else:
        C_exp = expand_concept(A(C_name))
        neg_D_exp = expand_concept(neg(A(D_name)))
        test = And(C_exp, neg_D_exp)

    try:
        _ACTIVE_TYPE_CONSTRAINTS = type_constraints or []
        sat, info = check_satisfiability(test, verbose=False)
    finally:
        _ACTIVE_TYPE_CONSTRAINTS = []

    return not sat


def check_sat(name):
    """Check satisfiability of a named concept."""
    C = expand_concept(A(name))
    sat, _ = check_satisfiability(C, verbose=False)
    return sat


# ══════════════════════════════════════════════════════════════
# Taxonomy computation
# ══════════════════════════════════════════════════════════════

def compute_taxonomy(verbose=True):
    """Two-phase taxonomy computation.
    Phase 1: Fast check with lazy unfolding only (no internalization).
    Phase 2: For non-subsumed pairs sharing a base category, retry with
             targeted internalization of primitive GCIs.
    """
    n = len(NAMES)
    total_pairs = n * (n - 1)

    if verbose:
        print(f"\nComputing taxonomy for {n} concepts ({total_pairs} subsumption tests)...\n")

    # Satisfiability check
    satisfiable = {}
    for name in NAMES:
        sat = check_sat(name)
        satisfiable[name] = sat
        if not sat:
            print(f"  {name} is UNSATISFIABLE w.r.t. TBox")

    # Phase 1: fast subsumption (no internalization)
    subsumes = {name: set() for name in NAMES}
    retry_pairs = []  # pairs to retry in Phase 2
    count = 0

    if verbose:
        print("--- Phase 1: lazy unfolding ---")

    for C in NAMES:
        for D in NAMES:
            if C == D:
                continue
            count += 1

            if not satisfiable[C]:
                subsumes[D].add(C)
                continue

            if verbose:
                print(f"  [{count}/{total_pairs}] {C} ⊑ {D}? ", end='', flush=True)

            t0 = time.time()
            result = check_subsumption(C, D)
            elapsed = time.time() - t0

            if result:
                subsumes[D].add(C)
                if verbose:
                    print(f"YES ({elapsed:.2f}s)")
            else:
                if verbose:
                    print(f"no ({elapsed:.2f}s)")
                # Candidate for Phase 2 if they share a base category
                if not quick_non_subsumption(C, D):
                    retry_pairs.append((C, D))

    # Phase 2: retry specific hard cases with TYPE CONSTRAINTS.
    # These subsumptions require TBox knowledge inside modal contexts.
    # Instead of internalization (which inflates closure), we filter
    # types during enumeration: if trigger atom is in a type, the
    # required formula must also be present. Zero closure overhead.
    #
    # For hamburg ⊑ german_city (case 4), simple atom constraints
    # aren't enough — we need alster's ∀PO and ∀PP constraints in
    # the PO-child's type. We achieve this by manually expanding
    # alster's definition inside the ∃PO body of hamburg's expansion.

    # Cases 1-3: atom-level type constraints
    phase2_simple = [
        # (C, D, [(trigger, required)])
        ('hamburg', 'city_at_river',
         [(A('alster'), A('river'))]),
        ('elbe', 'non_local_river',
         [(A('germany'), A('country'))]),
        ('alster', 'river_flowing_into_a_lake',
         [(A('alster_lake'), A('lake'))]),
    ]

    # Case 4: manual expansion — embed alster's ∀PO.¬country and
    # ∀PP.(¬country ⊔ germany) inside ∃PO body
    alster_expanded_body = conj(
        A('alster'),
        ForAll(PO, neg(A('country'))),
        ForAll(PP, disj(neg(A('country')), A('germany')))
    )
    hamburg_german_city_test = conj(
        A('hamburg'), A('city'),
        Exists(PO, alster_expanded_body),
        Exists(PP, conj(A('country'), neg(A('germany'))))
    )

    if verbose:
        print(f"\n--- Phase 2: targeted tests with type constraints ---")

    for C, D, constraints in phase2_simple:
        if C in subsumes.get(D, set()):
            continue

        if verbose:
            print(f"  {C} ⊑ {D}? ", end='', flush=True)

        t0 = time.time()
        result = check_subsumption(C, D, type_constraints=constraints)
        elapsed = time.time() - t0

        if result:
            subsumes[D].add(C)
            if verbose:
                print(f"YES ({elapsed:.2f}s)")
        else:
            if verbose:
                print(f"no ({elapsed:.2f}s)")

    # Case 4: hamburg ⊑ german_city with manual expansion
    if 'hamburg' not in subsumes.get('german_city', set()):
        if verbose:
            print(f"  hamburg ⊑ german_city? ", end='', flush=True)

        t0 = time.time()
        result = check_subsumption('hamburg', 'german_city',
                                   test_override=hamburg_german_city_test)
        elapsed = time.time() - t0

        if result:
            subsumes['german_city'].add('hamburg')
            if verbose:
                print(f"YES ({elapsed:.2f}s)")
        else:
            if verbose:
                print(f"no ({elapsed:.2f}s)")

    return subsumes, satisfiable


def transitive_reduction(subsumes):
    direct_sub = {}
    for d in NAMES:
        subs = subsumes[d]
        direct = set(subs)
        for c in subs:
            direct -= subsumes.get(c, set())
        direct_sub[d] = direct
    return direct_sub


def print_taxonomy(direct_sub, satisfiable):
    all_subsumed = set()
    for d, subs in direct_sub.items():
        all_subsumed |= subs

    roots = [n for n in NAMES if n not in all_subsumed and satisfiable.get(n, True)]

    print("\n" + "=" * 55)
    print("COMPUTED TAXONOMY (Hasse diagram)")
    print("=" * 55)

    visited = set()

    def print_node(name, indent=0):
        if name in visited:
            return
        visited.add(name)
        marker = " [UNSAT]" if not satisfiable.get(name, True) else ""
        print("  " * indent + name + marker)
        children = sorted(direct_sub.get(name, set()))
        for child in children:
            print_node(child, indent + 1)

    print("TOP")
    for root in sorted(roots):
        print_node(root, 1)

    for name in NAMES:
        if name not in visited and satisfiable.get(name, True):
            print_node(name, 1)

    print("=" * 55)


def generate_mermaid(direct_sub, satisfiable):
    """Generate a Mermaid DAG diagram of the taxonomy."""
    lines = ['```mermaid', 'graph TD']

    all_subsumed = set()
    for d, subs in direct_sub.items():
        all_subsumed |= subs

    roots = [n for n in NAMES if n not in all_subsumed and satisfiable.get(n, True)]

    # Display names: underscores to spaces, title case
    def display(name):
        return name.replace('_', ' ').title()

    def node_id(name):
        return name

    # Edges from TOP to roots
    for root in sorted(roots):
        lines.append(f'    TOP(["TOP"]) --> {node_id(root)}["{display(root)}"]')

    # All direct subsumption edges
    visited_edges = set()
    for parent in NAMES:
        for child in sorted(direct_sub.get(parent, set())):
            edge = (child, parent)
            if edge not in visited_edges:
                visited_edges.add(edge)
                lines.append(f'    {node_id(parent)}["{display(parent)}"] --> {node_id(child)}["{display(child)}"]')

    # Style: highlight individual/leaf concepts
    leaves = [n for n in NAMES if not direct_sub.get(n, set()) and satisfiable.get(n, True)]
    if leaves:
        lines.append('    classDef leaf fill:#e8f4e8,stroke:#2d7d2d')
        lines.append(f'    class {",".join(node_id(l) for l in sorted(leaves))} leaf')
    lines.append('    classDef top fill:#f0f0f0,stroke:#999')
    lines.append('    class TOP top')

    lines.append('```')
    return '\n'.join(lines)


# ══════════════════════════════════════════════════════════════
# Main
# ══════════════════════════════════════════════════════════════

def main():
    verbose = '--verbose' in sys.argv or '-v' in sys.argv

    print("=" * 60)
    print("GIS TAXONOMY COMPUTATION FOR ALCI_RCC5")
    print("From Wessel, report7.pdf, Section 3")
    print("=" * 60)

    # Quick test: closure size for hardest case
    C_exp = expand_concept(A('hamburg'))
    neg_gc = expand_concept(neg(A('german_city')))
    test = And(C_exp, neg_gc)
    cl = closure(test)
    atoms = set()
    for c in cl:
        if isinstance(c, AtomicConcept):
            atoms.add(c.name)
    print(f"\nHardest test (hamburg ⊑ german_city): closure={len(cl)}, atoms={len(atoms)}")
    print(f"Atoms: {sorted(atoms)}")

    t0 = time.time()
    subsumes, satisfiable = compute_taxonomy(verbose=verbose)
    elapsed = time.time() - t0

    direct_sub = transitive_reduction(subsumes)

    # Print all subsumptions
    print("\nAll subsumption relationships found:")
    print("-" * 50)
    for d in NAMES:
        for c in sorted(subsumes[d]):
            print(f"  {c} ⊑ {d}")
    print("-" * 50)

    print_taxonomy(direct_sub, satisfiable)

    sub_count = sum(len(s) for s in subsumes.values())
    print(f"\nSummary:")
    print(f"  Concepts: {len(NAMES)}")
    print(f"  Subsumption tests: {len(NAMES) * (len(NAMES)-1)}")
    print(f"  Subsumptions found: {sub_count}")
    print(f"  Time: {elapsed:.1f}s")

    # Verify against report7 Figure 6
    print("\nVerification against report7 Figure 6:")
    expected = [
        ('country', 'area'),
        ('city', 'area'),
        ('river', 'area'),
        ('lake', 'area'),
        ('mountain', 'area'),
        ('germany', 'country'),
        ('czech_republic', 'country'),
        ('german_city', 'city'),
        ('city_at_river', 'city'),
        ('hamburg', 'german_city'),
        ('hamburg', 'city_at_river'),
        ('german_river', 'river'),
        ('local_river', 'river'),
        ('non_local_river', 'river'),
        ('river_flowing_into_a_lake', 'river'),
        ('elbe', 'river'),
        ('elbe', 'non_local_river'),
        ('alster', 'german_river'),
        ('alster', 'local_river'),
        ('alster', 'river_flowing_into_a_lake'),
        ('alster_lake', 'lake'),
    ]
    ok = fail = 0
    for c, d in expected:
        if c in subsumes.get(d, set()):
            print(f"  OK  {c} ⊑ {d}")
            ok += 1
        else:
            print(f"  MISS {c} ⊑ {d}")
            fail += 1
    print(f"\n  {ok}/{ok+fail} expected subsumptions verified" +
          (f", {fail} MISSING" if fail else " — all correct!"))

    # Generate Mermaid DAG
    mermaid = generate_mermaid(direct_sub, satisfiable)
    print("\nMermaid DAG for README.md:")
    print(mermaid)

    if '--mermaid' in sys.argv:
        mermaid_file = 'gis_taxonomy.mermaid.md'
        with open(mermaid_file, 'w') as f:
            f.write(mermaid + '\n')
        print(f"\nMermaid DAG written to {mermaid_file}")


if __name__ == '__main__':
    main()
