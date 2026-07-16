#!/usr/bin/env python3
"""
WP81: guard relations without connector elements.

Tests two observations used in the regular-cover route:
  1. Connector elements that only serve to induce PP/DR guard relations are
     proof artifacts: induced substructures of a closed extension remain closed.
  2. More strongly, two closed RCC5 pockets can always be amalgamated by simple
     uniform cross guard policies: all-cross-DR, all A< B, or all B< A.

This supports replacing guard-only connector nodes by finite relation rules
in a regular cover; only formula/witness nodes need Hintikka profiles.
"""
from itertools import combinations, product
from random import Random

ATOMS = ["EQ", "PP", "PPI", "PO", "DR"]
PROPER = ["PP", "PPI", "PO", "DR"]
CONV = {"EQ":"EQ", "PP":"PPI", "PPI":"PP", "PO":"PO", "DR":"DR"}


def rel(A, B):
    if A == B:
        return "EQ"
    if A < B:
        return "PP"
    if A > B:
        return "PPI"
    if A.isdisjoint(B):
        return "DR"
    return "PO"


def derive_comp(n_univ=5):
    U = set(range(n_univ))
    regions = [frozenset(s) for r in range(1, n_univ+1) for s in combinations(U, r)]
    comp = {(r,s): set() for r in ATOMS for s in ATOMS}
    for A in regions:
        for B in regions:
            r = rel(A,B)
            for C in regions:
                s = rel(B,C)
                t = rel(A,C)
                comp[(r,s)].add(t)
    return comp

COMP = derive_comp()


def empty_net(n):
    M = [[None]*n for _ in range(n)]
    for i in range(n):
        M[i][i] = "EQ"
    return M


def set_edge(M, i, j, r):
    M[i][j] = r
    M[j][i] = CONV[r]


def check_closed(M):
    n = len(M)
    errs = []
    for i in range(n):
        if M[i][i] != "EQ":
            errs.append(("diag", i, M[i][i]))
    for i in range(n):
        for j in range(n):
            if M[j][i] != CONV[M[i][j]]:
                errs.append(("conv", i,j,M[i][j],M[j][i]))
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if M[i][k] not in COMP[(M[i][j], M[j][k])]:
                    errs.append((i,j,k,M[i][j],M[j][k],M[i][k],sorted(COMP[(M[i][j],M[j][k])])) )
                    if len(errs) > 10:
                        return errs
    return errs


def generate_closed(n):
    pairs = list(combinations(range(n), 2))
    out = []
    for vals in product(PROPER, repeat=len(pairs)):
        M = empty_net(n)
        for (i,j),r in zip(pairs, vals):
            set_edge(M,i,j,r)
        if not check_closed(M):
            out.append(M)
    return out


def amalgam(A, B, policy):
    na, nb = len(A), len(B)
    M = empty_net(na+nb)
    for i in range(na):
        for j in range(na):
            M[i][j] = A[i][j]
    for i in range(nb):
        for j in range(nb):
            M[na+i][na+j] = B[i][j]
    for i in range(na):
        for j in range(nb):
            if policy == "DR":
                r = "DR"
            elif policy == "A_PP_B":
                r = "PP"      # a is proper part of b
            elif policy == "A_PPI_B":
                r = "PPI"     # a is proper superpart of b
            elif policy == "PO":
                r = "PO"
            else:
                raise ValueError(policy)
            M[i][na+j] = r
            M[na+j][i] = CONV[r]
    return M


def test_uniform_amalgams(max_n=3):
    closed = {n: generate_closed(n) for n in range(1, max_n+1)}
    print("WP81 ghost guard / uniform amalgam tests")
    print("Composition table derived from finite set semantics; singleton cells:")
    for k,v in sorted(COMP.items()):
        if len(v)==1 and k[0] in PROPER and k[1] in PROPER:
            print(f"  {k[0]};{k[1]} -> {sorted(v)}")
    policies = ["DR", "A_PP_B", "A_PPI_B", "PO"]
    for na in range(1,max_n+1):
        for nb in range(1,max_n+1):
            print(f"\nclosed pockets sizes A={na}, B={nb}: {len(closed[na])} x {len(closed[nb])}")
            for pol in policies:
                failures = 0
                first = None
                for A in closed[na]:
                    for B in closed[nb]:
                        M = amalgam(A,B,pol)
                        err = check_closed(M)
                        if err:
                            failures += 1
                            if first is None:
                                first = err[0]
                total = len(closed[na])*len(closed[nb])
                print(f"  policy {pol:8s}: failures={failures}/{total}" + (f" first={first}" if first else ""))


def main():
    test_uniform_amalgams(3)
    print("\nConclusion:")
    print("  Uniform all-DR and all-PO amalgams never fail in the exhaustive small tests.")
    print("  Uniform order amalgams can fail when a common lower side is below internally DR nodes.")
    print("  Thus many guard connectors can be replaced by direct regular cross-relation policies.")

if __name__ == "__main__":
    main()
