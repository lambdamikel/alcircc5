#!/usr/bin/env python3
"""
wp84_fo_pi01_transcription.py                (2026-07-17, DRAFT — not in repo)

Machine cross-check of the FO transcription behind the Pi^0_1 observation:

    SAT(ALCI_RCC5) under abstract composition-table semantics is Pi^0_1,
    because the model class is finitely FO-axiomatizable and ALCI embeds
    by the standard translation; Goedel completeness then makes UNSAT r.e.

The observation's only non-standard ingredient is the TRANSCRIPTION:
 (a) that a finite set of FO axioms carves out exactly the RCC5Interp
     frames of the certified Lean artifact (Round19Transport.lean:4214),
 (b) that the standard translation ST renders the certified `sat`
     (Round19Transport.lean:4143) faithfully.
This probe machine-checks both on finite structures, plus the usual
self-contained re-derivation of the composition table from set semantics
(cross-checked against the artifact's table, transcribed verbatim from
Round19Transport.lean:141-159).

Parts:
  A. Derive the RCC5 comp table + converse from finite set semantics
     (|U| = 5, nonempty subsets); assert equality with the certified table.
  B. FO frame axioms  <=>  RCC5Interp fields:
     exhaustive on raw 5-predicate structures for |D| = 2 (2^5 per ordered
     pair = 1,048,576 structures), exhaustive on total rho-functions for
     |D| = 3 (5^9 = 1,953,125), random raw structures for |D| = 3, 4.
  C. Standard-translation faithfulness: direct modal evaluator (transcribing
     `sat`) vs FO evaluator of ST(C) on random NNF concepts x set-semantic
     models (which are RCC5Interp-valid by construction). Exact agreement.

Deterministic (fixed seed). Exit 0 + final PASS iff every check passes.
"""

import random
from itertools import combinations, product

random.seed(84)

ATOMS = ["eq", "pp", "ppi", "po", "dr"]

# ---------------------------------------------------------------------------
# Part A: set semantics -> comp table; cross-check the certified table
# ---------------------------------------------------------------------------

def rel(X, Y):
    """RCC5 relation between nonempty sets X, Y (strong EQ)."""
    if X == Y:
        return "eq"
    if not (X & Y):
        return "dr"
    if X < Y:
        return "pp"
    if Y < X:
        return "ppi"
    return "po"

def derive_tables(n_universe=5):
    U = frozenset(range(n_universe))
    regions = [frozenset(s) for k in range(1, n_universe + 1)
               for s in combinations(U, k)]
    comp = {(a, b): set() for a in ATOMS for b in ATOMS}
    conv = {}
    for X in regions:
        for Y in regions:
            a = rel(X, Y)
            conv.setdefault(a, rel(Y, X))
            assert conv[a] == rel(Y, X), "converse not well-defined"
            for Z in regions:
                comp[(a, rel(Y, Z))].add(rel(X, Z))
    return comp, conv

# The certified artifact's table, verbatim (Round19Transport.lean:141-159).
LEAN_COMP = {
    ("eq", "eq"): {"eq"}, ("eq", "pp"): {"pp"}, ("eq", "ppi"): {"ppi"},
    ("eq", "po"): {"po"}, ("eq", "dr"): {"dr"},
    ("pp", "eq"): {"pp"}, ("ppi", "eq"): {"ppi"}, ("po", "eq"): {"po"},
    ("dr", "eq"): {"dr"},
    ("pp", "pp"): {"pp"},
    ("pp", "ppi"): {"eq", "pp", "ppi", "po", "dr"},
    ("pp", "po"): {"pp", "po", "dr"},
    ("pp", "dr"): {"dr"},
    ("ppi", "pp"): {"eq", "pp", "ppi", "po"},
    ("ppi", "ppi"): {"ppi"},
    ("ppi", "po"): {"ppi", "po"},
    ("ppi", "dr"): {"ppi", "po", "dr"},
    ("po", "pp"): {"pp", "po"},
    ("po", "ppi"): {"ppi", "po", "dr"},
    ("po", "po"): {"eq", "pp", "ppi", "po", "dr"},
    ("po", "dr"): {"ppi", "po", "dr"},
    ("dr", "pp"): {"pp", "po", "dr"},
    ("dr", "ppi"): {"dr"},
    ("dr", "po"): {"pp", "po", "dr"},
    ("dr", "dr"): {"eq", "pp", "ppi", "po", "dr"},
}
LEAN_CONV = {"eq": "eq", "pp": "ppi", "ppi": "pp", "po": "po", "dr": "dr"}

def part_a():
    comp, conv = derive_tables(5)
    assert conv == LEAN_CONV, "converse mismatch vs certified artifact"
    assert {k: v for k, v in comp.items()} == LEAN_COMP, \
        "comp table mismatch vs certified artifact"
    print("A. set-semantics tables == certified artifact tables: PASS "
          f"({len(LEAN_COMP)} cells, conv involution incl.)")
    return comp, conv

COMP, CONV = part_a()

# ---------------------------------------------------------------------------
# Part B: FO frame axioms  <=>  RCC5Interp fields
# ---------------------------------------------------------------------------
# An FO structure on domain D: S[(x,y)] = the SET of atoms holding at (x,y)
# (five binary predicates). The FO axiom set T_RCC5:
#   (A1) exactly one atom on every ordered pair
#   (A2) EQ(x,y) <-> x = y                                (strong EQ)
#   (A3) converse coherence: a in S(x,y) <-> conv(a) in S(y,x)
#   (A4) composition closure on pairwise-distinct triples:
#        a in S(x,y), b in S(y,z)  ->  some c in comp(a,b) in S(x,z)
# The Lean side (RCC5Interp, Round19Transport.lean:4214): a total FUNCTION
# rho with refl_eq, eq_id, conv_, comp_ (comp_ over ALL triples).

def fo_ok(D, S):
    for x in D:
        for y in D:
            cell = S[(x, y)]
            if len(cell) != 1:                      # (A1)
                return False
            if (x == y) != ("eq" in cell):          # (A2)
                return False
            a = next(iter(cell))
            if CONV[a] not in S[(y, x)] or len(S[(y, x)]) != 1:  # (A3)
                return False
    for x in D:
        for y in D:
            for z in D:
                if len({x, y, z}) < 3:
                    continue
                a = next(iter(S[(x, y)])); b = next(iter(S[(y, z)]))
                if not (COMP[(a, b)] & S[(x, z)]):  # (A4)
                    return False
    return True

def rcc5interp_ok(D, S):
    """Functional structure + the four RCC5Interp fields (comp_ over ALL
    triples, as in the Lean statement)."""
    for x in D:
        for y in D:
            if len(S[(x, y)]) != 1:
                return False
    rho = {p: next(iter(c)) for p, c in S.items()}
    for x in D:
        if rho[(x, x)] != "eq":                     # refl_eq
            return False
    for x in D:
        for y in D:
            if rho[(x, y)] == "eq" and x != y:      # eq_id
                return False
            if rho[(y, x)] != CONV[rho[(x, y)]]:    # conv_
                return False
    for x in D:
        for y in D:
            for z in D:
                if rho[(x, z)] not in COMP[(rho[(x, y)], rho[(y, z)])]:
                    return False                    # comp_ (all triples)
    return True

def all_subsets():
    out = []
    for mask in range(32):
        out.append(frozenset(a for i, a in enumerate(ATOMS) if mask >> i & 1))
    return out

def part_b():
    subsets = all_subsets()
    # B1: |D| = 2, exhaustive over RAW structures (32^4 = 1,048,576)
    D = [0, 1]
    pairs = [(x, y) for x in D for y in D]
    n = agree = fo_true = 0
    for assign in product(subsets, repeat=4):
        S = dict(zip(pairs, assign))
        f, r = fo_ok(D, S), rcc5interp_ok(D, S)
        n += 1; agree += (f == r); fo_true += f
    assert agree == n, f"B1 disagreement: {n - agree}"
    print(f"B1. |D|=2 exhaustive raw ({n:,} structures): FO == RCC5Interp "
          f"on all; {fo_true} models: PASS")

    # B2: |D| = 3, exhaustive over TOTAL rho functions (5^9 = 1,953,125)
    D = [0, 1, 2]
    pairs = [(x, y) for x in D for y in D]
    n = agree = fo_true = 0
    for assign in product(ATOMS, repeat=9):
        S = {p: frozenset([a]) for p, a in zip(pairs, assign)}
        f, r = fo_ok(D, S), rcc5interp_ok(D, S)
        n += 1; agree += (f == r); fo_true += f
    assert agree == n, f"B2 disagreement: {n - agree}"
    print(f"B2. |D|=3 exhaustive functional ({n:,} structures): FO == "
          f"RCC5Interp on all; {fo_true} models: PASS")

    # B3: |D| = 3, 4 random RAW structures (biased toward near-functional
    # so the interesting boundary is exercised)
    for size in (3, 4):
        D = list(range(size))
        pairs = [(x, y) for x in D for y in D]
        n = agree = 0
        for _ in range(100_000):
            S = {}
            for p in pairs:
                if random.random() < 0.8:
                    S[p] = frozenset([random.choice(ATOMS)])
                else:
                    S[p] = random.choice(subsets)
            f, r = fo_ok(D, S), rcc5interp_ok(D, S)
            n += 1; agree += (f == r)
        assert agree == n, f"B3 |D|={size} disagreement: {n - agree}"
        print(f"B3. |D|={size} random raw (100,000 structures): FO == "
              f"RCC5Interp on all: PASS")

part_b()

# ---------------------------------------------------------------------------
# Part C: standard-translation faithfulness
# ---------------------------------------------------------------------------
# Concepts in NNF (Round19Transport.lean:4124): top | bot | atom | natom |
# and | or | ex r | all r.  Modal evaluator = transcription of `sat`
# (4143: roles read rho x y = r).  FO evaluator = ST(C) over the
# 5-predicate structure.  Models come from SET SEMANTICS (distinct
# nonempty subsets), hence are RCC5Interp-valid by construction.

def random_concept(depth, n_atoms=3):
    ops = ["atom", "natom"] if depth == 0 else \
          ["atom", "natom", "and", "or", "ex", "all", "top", "bot"]
    op = random.choice(ops)
    if op in ("top", "bot"):
        return (op,)
    if op in ("atom", "natom"):
        return (op, random.randrange(n_atoms))
    if op in ("and", "or"):
        return (op, random_concept(depth - 1, n_atoms),
                random_concept(depth - 1, n_atoms))
    return (op, random.choice(ATOMS), random_concept(depth - 1, n_atoms))

def sat_modal(rho, val, x, C, D):
    """Transcription of Lean `sat` (dom = all of D)."""
    op = C[0]
    if op == "top":
        return True
    if op == "bot":
        return False
    if op == "atom":
        return x in val[C[1]]
    if op == "natom":
        return x not in val[C[1]]
    if op == "and":
        return sat_modal(rho, val, x, C[1], D) and sat_modal(rho, val, x, C[2], D)
    if op == "or":
        return sat_modal(rho, val, x, C[1], D) or sat_modal(rho, val, x, C[2], D)
    if op == "ex":
        return any(rho[(x, y)] == C[1] and sat_modal(rho, val, y, C[2], D)
                   for y in D)
    if op == "all":
        return all(not rho[(x, y)] == C[1] or sat_modal(rho, val, y, C[2], D)
                   for y in D)
    raise ValueError(op)

def st_fo(S, val, x, C, D):
    """FO evaluator of the standard translation ST_x(C) over the
    5-predicate structure S (R_r(x,y) := r in S[(x,y)])."""
    op = C[0]
    if op == "top":
        return True
    if op == "bot":
        return False
    if op == "atom":
        return x in val[C[1]]
    if op == "natom":
        return x not in val[C[1]]
    if op == "and":
        return st_fo(S, val, x, C[1], D) and st_fo(S, val, x, C[2], D)
    if op == "or":
        return st_fo(S, val, x, C[1], D) or st_fo(S, val, x, C[2], D)
    if op == "ex":   # exists y. R_r(x,y) /\ ST_y(C')
        return any(C[1] in S[(x, y)] and st_fo(S, val, y, C[2], D) for y in D)
    if op == "all":  # forall y. R_r(x,y) -> ST_y(C')
        return all(C[1] not in S[(x, y)] or st_fo(S, val, y, C[2], D)
                   for y in D)
    raise ValueError(op)

def part_c(n_concepts=300, n_models=20, max_dom=4, n_universe=5):
    U = list(range(n_universe))
    all_regions = [frozenset(s) for k in range(1, n_universe + 1)
                   for s in combinations(U, k)]
    checked = 0
    for _ in range(n_models):
        size = random.randrange(2, max_dom + 1)
        regions = random.sample(all_regions, size)   # distinct => strong EQ
        D = list(range(size))
        rho = {(x, y): rel(regions[x], regions[y]) for x in D for y in D}
        S = {p: frozenset([a]) for p, a in rho.items()}
        assert rcc5interp_ok(D, S) and fo_ok(D, S), \
            "set-semantic model not RCC5Interp-valid?!"
        val = {a: frozenset(x for x in D if random.random() < 0.5)
               for a in range(3)}
        for _ in range(n_concepts // n_models):
            C = random_concept(random.randrange(4))
            for x in D:
                m = sat_modal(rho, val, x, C, D)
                f = st_fo(S, val, x, C, D)
                assert m == f, f"ST mismatch at {x}: {C}"
                checked += 1
    print(f"C.  standard translation: modal `sat` == FO eval of ST on "
          f"{checked:,} (concept, model, point) triples, 0 mismatches: PASS")

part_c()

print()
print("ALL PASS -- the Pi^0_1 observation's transcription layer is faithful:")
print("  FO axiom set == RCC5Interp frames (exhaustive |D|<=3 + random |D|=4);")
print("  standard translation == certified `sat`;")
print("  comp/conv tables == certified artifact (derived from set semantics).")
print("Goedel completeness then gives: UNSAT(ALCI_RCC5) is r.e.; SAT is Pi^0_1.")
