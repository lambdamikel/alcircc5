#!/usr/bin/env python3
"""
rev1_comp_table.py -- self-contained re-derivation of the RCC5 composition and
converse tables from finite-set semantics, and comparison against the table
hard-coded in POFreeLift.lean (lines 51-71).

Regions = non-empty proper-or-not subsets of a finite universe.
  EQ (x,y)  :  x == y
  PP (x,y)  :  x subset y, x != y
  PPI(x,y)  :  y subset x, x != y
  PO (x,y)  :  x & y != {} and x-y != {} and y-x != {}
  DR (x,y)  :  x & y == {}

comp(R,S) = { T : exists regions x,y,z with R(x,y), S(y,z), T(x,z) }
(this is the *weak* composition / relation-algebraic composition that RCC5
qualitative calculi use; it is what a path-consistency check enforces).

No library assumptions -- everything is enumerated.
"""
from itertools import combinations, product

ATOMS = ["eq", "pp", "ppi", "po", "dr"]


def rel(x, y):
    if x == y:
        return "eq"
    if x < y:
        return "pp"
    if y < x:
        return "ppi"
    if not (x & y):
        return "dr"
    return "po"


def regions(n):
    """All non-empty subsets of {0..n-1} as frozensets."""
    out = []
    univ = list(range(n))
    for k in range(1, n + 1):
        for c in combinations(univ, k):
            out.append(frozenset(c))
    return out


def derive(n):
    R = regions(n)
    comp = {(a, b): set() for a in ATOMS for b in ATOMS}
    conv = {a: set() for a in ATOMS}
    for x in R:
        for y in R:
            conv[rel(x, y)].add(rel(y, x))
    for x in R:
        for y in R:
            rxy = rel(x, y)
            for z in R:
                comp[(rxy, rel(y, z))].add(rel(x, z))
    return comp, conv


# ---- the table as written in POFreeLift.lean ------------------------------
LEAN_COMP_RAW = """
eq b   -> b            (row/col identity)
a  eq  -> a
pp  pp  -> pp
pp  ppi -> eq pp ppi po dr
pp  po  -> pp po dr
pp  dr  -> dr
ppi pp  -> eq pp ppi po
ppi ppi -> ppi
ppi po  -> ppi po
ppi dr  -> ppi po dr
po  pp  -> pp po
po  ppi -> ppi po dr
po  po  -> eq pp ppi po dr
po  dr  -> ppi po dr
dr  pp  -> pp po dr
dr  ppi -> dr
dr  po  -> pp po dr
dr  dr  -> eq pp ppi po dr
"""

LEAN_COMP = {}
for a in ATOMS:
    LEAN_COMP[("eq", a)] = {a}
    LEAN_COMP[(a, "eq")] = {a}
for line in LEAN_COMP_RAW.strip().splitlines():
    if "->" not in line or "(" in line:
        continue
    lhs, rhs = line.split("->")
    parts = lhs.split()
    if len(parts) != 2 or parts[0] not in ATOMS or parts[1] not in ATOMS:
        continue
    LEAN_COMP[(parts[0], parts[1])] = set(rhs.split())

LEAN_CONV = {"eq": "eq", "pp": "ppi", "ppi": "pp", "po": "po", "dr": "dr"}


def main():
    print("universe size : #regions : table stable?")
    prev = None
    for n in range(2, 7):
        comp, conv = derive(n)
        key = {k: frozenset(v) for k, v in comp.items()}
        print(f"  n={n:>2}  regions={len(regions(n)):>3}  "
              f"{'same as n-1' if prev == key else 'CHANGED'}")
        prev = key
    comp, conv = derive(6)

    print("\n--- converse ---")
    bad = 0
    for a in ATOMS:
        got = conv[a]
        if got != {LEAN_CONV[a]}:
            print(f"  MISMATCH conv({a}): derived {sorted(got)} "
                  f"vs Lean {LEAN_CONV[a]}")
            bad += 1
    print(f"  converse mismatches: {bad}")

    print("\n--- composition (derived vs POFreeLift.lean) ---")
    mism = 0
    for a in ATOMS:
        for b in ATOMS:
            d = comp[(a, b)]
            l = LEAN_COMP[(a, b)]
            if d != l:
                mism += 1
                print(f"  MISMATCH comp({a},{b}):")
                print(f"      derived : {sorted(d)}")
                print(f"      Lean    : {sorted(l)}")
                print(f"      Lean\\derived (unsound, too permissive): "
                      f"{sorted(l - d)}")
                print(f"      derived\\Lean (incomplete, too strict) : "
                      f"{sorted(d - l)}")
    print(f"  composition mismatches: {mism} / 25 cells")
    if mism == 0 and bad == 0:
        print("\nRESULT: POFreeLift.lean's `comp`/`conv` tables agree EXACTLY "
              "with the\n        finite-set re-derivation. No table-input "
              "defect.")


if __name__ == "__main__":
    main()
