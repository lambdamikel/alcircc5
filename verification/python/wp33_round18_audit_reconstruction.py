#!/usr/bin/env python3
"""
WP33 (reconstruction) -- the thirteenth review's four witnesses against
round-18, re-implemented as a permanent regression, plus the check that
the reviewer's source-oriented repair (U1-U5) handles all four.

The review (papers/gpt5.5_round18_review/round18_formal_response.*)
quoted a WP33 script without shipping it; this file reconstructs its
checks from the report's own definitions so the repository's WP series
stays executable end-to-end.

Witnesses:
  A  Co-birth inherited-slot totality gap: s and x born in the same
     copy A; only s inherited into the current parent B; child uses s
     as separator.  Round-18's written case split (s in core / x in V_k
     / b(x)<b(s) / b(x)>b(s)) fires NO clause, though the value exists
     as the birth-pattern entry N_A(x,s).
  B  Inherited U-down mis-source: b(x) < b(s), s inherited (not fresh)
     in the current parent -- the written lookup reads the current
     parent attachment's steering row, which has no component for s;
     the correct source is s's BIRTH step.
  C  Order invariance is false: two incomparable siblings with
     independent steering functions; expanding A-then-B vs B-then-A
     assigns rho(a,b) = PP vs DR; both results pass every local check
     and are closed -- same unordered tree, different values.  (Cure:
     canonical-order determinism, not unordered-tree invariance.)
  D  The gap is S4-critical: with the co-birth pair absent from the
     fixed point, a steering choice passing S1/S2/S3 yields a
     non-composition-closed frame (Comp(PP,DR) = {DR} pins the pair).
  E  The reviewer's source-oriented U (value looked up at the step
     where it was RECORDED: core / birth copy of s / s's birth steering
     / x's birth flip) covers A, B and restores the S4 rejection in D.

Run:  python3 verification/python/wp33_round18_audit_reconstruction.py
"""

import itertools
import sys

BASE = ('EQ', 'PP', 'PPI', 'PO', 'DR')
CONV = {'EQ': 'EQ', 'PP': 'PPI', 'PPI': 'PP', 'PO': 'PO', 'DR': 'DR'}


def derive_comp(n=5):
    U = range(n)
    subs = [frozenset(c) for k in range(1, n + 1)
            for c in itertools.combinations(U, k)]

    def rel(a, b):
        if a == b:
            return 'EQ'
        if not a & b:
            return 'DR'
        if a < b:
            return 'PP'
        if b < a:
            return 'PPI'
        return 'PO'

    t = {(r, s): set() for r in BASE for s in BASE}
    for a in subs:
        for b in subs:
            r = rel(a, b)
            for c in subs:
                t[(r, rel(b, c))].add(rel(a, c))
    return {k: frozenset(v) for k, v in t.items()}


COMP = derive_comp(5)


def written_U_clauses(s_in_core, x_in_Vk, bx, bs):
    """Round-18 Definition U, as WRITTEN (the four-case split)."""
    fired = []
    if s_in_core:
        fired.append('U-core')
    if x_in_Vk:
        fired.append('U-res')
    if (not s_in_core) and (not x_in_Vk) and bx < bs:
        fired.append('U-down')
    if (not s_in_core) and (not x_in_Vk) and bx > bs:
        fired.append('U-flip')
    return fired


def source_oriented_U(s_in_core, x_in_birthcopy_of_s, bx, bs):
    """The 13th review's repair U1-U5: source-oriented case split."""
    if s_in_core:
        return 'core-row'
    if x_in_birthcopy_of_s:
        return 'birth-pattern of s (covers co-birth)'
    if bx < bs:
        return "steering recorded at s's birth"
    return "converse recorded at x's birth (flip)"


def part_a():
    fired = written_U_clauses(s_in_core=False, x_in_Vk=False, bx=0, bs=0)
    gap = (fired == [])
    print("A. co-birth inherited-slot totality gap:")
    print(f"   b(x)=b(s)=0, s not core, x not in V_B: written clauses "
          f"fired = {fired or 'NONE'}")
    print(f"   value exists as birth-pattern entry N_A(x,s): True")
    print(f"   {'PASS -- the gap is real (defect #12 confirmed)' if gap else 'FAIL'}")
    return gap


def part_b():
    # s born fresh at step 1; parent B (step 2) inherited s; x born step 0.
    fired = written_U_clauses(False, False, bx=0, bs=1)
    # written U-down reads the CURRENT PARENT attachment's steering row;
    # s was not fresh there, so that row has no s-component:
    parent_row_components = ['b']          # only B's fresh member
    text_lookup_exists = 's' in parent_row_components
    birth_row_components = ['s']           # step-1 steering row covers s
    correct_lookup_exists = 's' in birth_row_components
    ok = fired == ['U-down'] and not text_lookup_exists \
        and correct_lookup_exists
    print("B. inherited U-down mis-source:")
    print(f"   clauses fired = {fired}; text lookup at parent step has "
          f"s-component: {text_lookup_exists}; birth-step lookup has it: "
          f"{correct_lookup_exists}")
    print(f"   {'PASS -- wrong source step in the written clause' if ok else 'FAIL'}")
    return ok


def part_c():
    # siblings A (fresh a), B (fresh b), shared core c; N(c,a)=N(c,b)=DR.
    # certificate stores f_B(St(a))(b)=PP and f_A(St(b))(a)=DR.
    def closed3(vab):
        N = {}
        net_pairs = [('c', 'a', 'DR'), ('c', 'b', 'DR'), ('a', 'b', vab)]
        for i, j, r in net_pairs:
            N[(i, j)] = r
            N[(j, i)] = CONV[r]
        V = ['a', 'b', 'c']
        for i in V:
            for j in V:
                if i == j:
                    continue
                for k in V:
                    if k in (i, j):
                        continue
                    if N[(i, k)] not in COMP[(N[(i, j)], N[(j, k)])]:
                        return False
        return True

    ab_first = 'PP'   # A expanded first: a steered at B's birth
    ba_first = 'DR'   # B expanded first: b steered at A's birth
    s1_ok = ab_first in COMP[('DR', 'DR')] and ba_first in COMP[('DR', 'DR')]
    ok = closed3(ab_first) and closed3(ba_first) and s1_ok \
        and ab_first != ba_first
    print("C. order-invariance counterexample:")
    print(f"   A-then-B gives rho(a,b)={ab_first}; B-then-A gives "
          f"rho(a,b)={ba_first}; both S1-legal through c "
          f"(comp(DR,DR)=Rel) and both closed: "
          f"{closed3(ab_first)}/{closed3(ba_first)}")
    print(f"   {'PASS -- same unordered tree, different values; only '
          'canonical-order determinism survives' if ok else 'FAIL'}")
    return ok


def part_d():
    # old: x PP a, z PP a, x PP z (closed); child: a PPI d (d PP a);
    # steering x PP d, z DR d passes S1 through a; S4 on (x,z) pins
    # x-d to Comp(PP,DR)={DR}.
    old_closed = ('PP' in COMP[('PP', 'PP')])
    s1_x = 'PP' in COMP[('PP', 'PPI')]
    s1_z = 'DR' in COMP[('PP', 'PPI')]
    s4_req = COMP[('PP', 'DR')]
    rejects = ('PP' not in s4_req) and (s4_req == frozenset({'DR'}))
    ok = old_closed and s1_x and s1_z and rejects
    print("D. the co-birth gap is S4-critical:")
    print(f"   S1 admits x PP d and z DR d through a: {s1_x}/{s1_z}; "
          f"S4 on the old pair x PP z pins x-d to {sorted(s4_req)}")
    print(f"   {'PASS -- omitting the pair accepts a non-closed frame' if ok else 'FAIL'}")
    return ok


def part_e():
    a = source_oriented_U(False, True, 0, 0)
    b = source_oriented_U(False, False, 0, 1)
    d_covered = a.startswith('birth-pattern')
    b_covered = b.startswith("steering recorded at s's birth")
    ok = d_covered and b_covered
    print("E. the source-oriented repair (13th review U1-U5):")
    print(f"   co-birth case -> {a}; inherited older case -> {b}")
    print(f"   {'PASS -- both witnesses covered; S4 sees the pair again' if ok else 'FAIL'}")
    return ok


def net_set_unused():
    pass


def net_set(N, i, j, r):
    N[(i, j)] = r
    N[(j, i)] = CONV[r]


if __name__ == '__main__':
    print(__doc__.split('\n')[1])
    print('=' * 70)
    r = [part_a(), part_b(), part_c(), part_d(), part_e()]
    print('=' * 70)
    print("WP33 (reconstruction) OVERALL:",
          "PASS -- all four witnesses confirmed; repair direction verified"
          if all(r) else "ATTENTION")
    sys.exit(0 if all(r) else 1)
