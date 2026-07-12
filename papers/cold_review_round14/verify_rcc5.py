"""Cold-review verification computations for the ALCI_RCC5 stack (round 14).

Derives the RCC5 composition table independently from set semantics,
checks it against the manuscript table, verifies the four finite facts
of the round-13 delta, the WP20 triangle rejection, the finite patchwork
(amalgamation) property in the small, the DR-isolation extension lemma,
and the composition arithmetic used in Finding F1 of the referee report.
"""
from itertools import combinations, product

REL = ['EQ', 'PP', 'PPI', 'PO', 'DR']
CONV = {'EQ': 'EQ', 'PP': 'PPI', 'PPI': 'PP', 'PO': 'PO', 'DR': 'DR'}

# ---------------------------------------------------------------- 1. table
U = range(6)
regions = [frozenset(s) for k in range(1, 7) for s in combinations(U, k)]

def rel(X, Y):
    if X == Y: return 'EQ'
    if X < Y: return 'PP'
    if Y < X: return 'PPI'
    if X & Y: return 'PO'
    return 'DR'

derived = {(r, s): set() for r in REL for s in REL}
for X in regions:
    rxy = {}
    for Y in regions:
        rxy[Y] = rel(X, Y)
for X in regions:
    for Y in regions:
        r1 = rel(X, Y)
        for Z in regions:
            derived[(r1, rel(Y, Z))].add(rel(X, Z))

manuscript = {
 ('EQ','EQ'):{'EQ'}, ('EQ','PP'):{'PP'}, ('EQ','PPI'):{'PPI'}, ('EQ','PO'):{'PO'}, ('EQ','DR'):{'DR'},
 ('PP','EQ'):{'PP'}, ('PP','PP'):{'PP'}, ('PP','PPI'):set(REL), ('PP','PO'):{'PP','PO','DR'}, ('PP','DR'):{'DR'},
 ('PPI','EQ'):{'PPI'}, ('PPI','PP'):{'EQ','PP','PPI','PO'}, ('PPI','PPI'):{'PPI'}, ('PPI','PO'):{'PPI','PO'}, ('PPI','DR'):{'PPI','PO','DR'},
 ('PO','EQ'):{'PO'}, ('PO','PP'):{'PP','PO'}, ('PO','PPI'):{'PPI','PO','DR'}, ('PO','PO'):set(REL), ('PO','DR'):{'PPI','PO','DR'},
 ('DR','EQ'):{'DR'}, ('DR','PP'):{'PP','PO','DR'}, ('DR','PPI'):{'DR'}, ('DR','PO'):{'PP','PO','DR'}, ('DR','DR'):set(REL),
}

mismatch = [(k, sorted(derived[k]), sorted(manuscript[k]))
            for k in manuscript if derived[k] != manuscript[k]]
print("1. Composition table derived from set semantics (|U|=6, 63 regions, 63^3 triples):")
print("   match with manuscript Section 2 table:", "EXACT" if not mismatch else mismatch)
COMP = manuscript  # ground truth from here on

# ------------------------------------------------------- 2. the four facts
HOR = {'DR', 'PO'}
f21 = all(HOR <= COMP[(a, b)] for a in HOR for b in HOR)
f22 = COMP[('PP','PP')] == {'PP'} and COMP[('PPI','PPI')] == {'PPI'}
f23 = all(COMP[(h, r)] & HOR for h in HOR for r in ('PP', 'PPI'))
eq_cells = [k for k in COMP if 'EQ' in COMP[k] and k != ('EQ','EQ')]
f24 = all({'PP','PPI','PO'} <= COMP[k] for k in eq_cells)
print("2. Fact 2.1 (horizontal absorption):", f21)
print("   Fact 2.2 (vertical transitivity):", f22)
print("   Fact 2.3 (no horizontal dead ends):", f23)
print("   Fact 2.4 (EQ never forced) on cells", eq_cells, ":", f24)

# --------------------------------------------------------- 3. WP20 triangle
print("3. WP20 triangle x PP y, y DR p, x PO p:  Comp(PP,DR) =",
      sorted(COMP[('PP','DR')]), "-> PO admitted:", 'PO' in COMP[('PP','DR')])

# ------------------------------------------- 4. closed atomic networks, n<=4
def closed(n, N):
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if N[(i,k)] not in COMP[(N[(i,j)], N[(j,k)])]:
                    return False
    return True

def atomic_nets(n):
    pairs = list(combinations(range(n), 2))
    nets = []
    for vals in product([r for r in REL if r != 'EQ'], repeat=len(pairs)):
        N = {(i,i): 'EQ' for i in range(n)}
        for (i,j), v in zip(pairs, vals):
            N[(i,j)] = v; N[(j,i)] = CONV[v]
        if closed(n, N):
            nets.append(N)
    return nets

nets3 = atomic_nets(3)
nets4 = atomic_nets(4)
print("4. Closed complete atomic RCC5 networks: n=3:", len(nets3), " n=4:", len(nets4))

# --------------------- 5. patchwork (two-bag amalgamation) in the small
def try_complete(n, N, unknown):
    """Complete the partial network N on n vars; 'unknown' = list of pairs."""
    for vals in product([r for r in REL if r != 'EQ'], repeat=len(unknown)):
        M = dict(N)
        for (i,j), v in zip(unknown, vals):
            M[(i,j)] = v; M[(j,i)] = CONV[v]
        if closed(n, M):
            return True
    return False

# 5a. two triangles sharing an edge: vars {0,1,2} and {1,2,3}; unknown (0,3)
fail_a = 0; tested_a = 0
for N1 in nets3:
    for N2 in nets3:
        if N1[(0,1)] == N2[(0,1)] and False:
            pass
for N1 in nets3:
    for N2 in nets3:
        # N2 lives on {1,2,3} via i -> i+1; overlap {1,2} must agree
        if N1[(1,2)] != N2[(0,1)]:
            continue
        tested_a += 1
        N = {(i,i):'EQ' for i in range(4)}
        for (i,j) in combinations(range(3),2):
            N[(i,j)] = N1[(i,j)]; N[(j,i)] = CONV[N1[(i,j)]]
        for (i,j) in combinations(range(3),2):
            N[(i+1,j+1)] = N2[(i,j)]; N[(j+1,i+1)] = CONV[N2[(i,j)]]
        if not try_complete(4, N, [(0,3)]):
            fail_a += 1
print("5a. Patchwork 3+3 over 2-overlap:", tested_a, "agreeing pairs,",
      fail_a, "amalgamation failures")

# 5b. two 4-cliques sharing a triangle: vars {0,1,2,3} and {1,2,3,4}; unknown (0,4)
fail_b = 0; tested_b = 0
from collections import defaultdict
by_face = defaultdict(list)
for N in nets4:
    face = tuple(N[(i,j)] for (i,j) in combinations(range(1,4),2))
    by_face[face].append(N)
for N1 in nets4:
    face = tuple(N1[(i,j)] for (i,j) in combinations(range(1,4),2))
    # N2 on {1,2,3,4} via i -> i+1; its face on {1,2,3} is its {0,1,2} part
    for N2 in nets4:
        f2 = tuple(N2[(i,j)] for (i,j) in combinations(range(3),2))
        if f2 != face:
            continue
        tested_b += 1
        N = {(i,i):'EQ' for i in range(5)}
        for (i,j) in combinations(range(4),2):
            N[(i,j)] = N1[(i,j)]; N[(j,i)] = CONV[N1[(i,j)]]
        for (i,j) in combinations(range(4),2):
            N[(i+1,j+1)] = N2[(i,j)]; N[(j+1,i+1)] = CONV[N2[(i,j)]]
        if not try_complete(5, N, [(0,4)]):
            fail_b += 1
print("5b. Patchwork 4+4 over 3-overlap:", tested_b, "agreeing pairs,",
      fail_b, "amalgamation failures")

# ------------------------------------ 6. DR-isolation extension lemma
def dr_isolated_ok(n, N):
    M = dict(N)
    for i in range(n):
        M[(i,n)] = 'DR'; M[(n,i)] = 'DR'
    M[(n,n)] = 'EQ'
    return closed(n+1, M)

bad3 = sum(1 for N in nets3 if not dr_isolated_ok(3, N))
bad4 = sum(1 for N in nets4 if not dr_isolated_ok(4, N))
print("6. DR-isolation (fresh point DR to all) preserves closure:",
      "n=3 failures:", bad3, " n=4 failures:", bad4)

# ------------------------------------ 7. Finding F1 arithmetic
e_via_p = COMP[('PP', CONV['PPI'])]   # rho(x,y) in Comp(rho(x,p), rho(p,y)); rho(p,y)=conv(PPI)=PP
e_via_q = COMP[('PP', CONV['DR'])]    # rho(p,y)=conv(row(y,q))=conv(DR)=DR
print("7. F1 witness: rows row(x,p)=PP, row(y,p)=PPI, row(x,q)=PP, row(y,q)=DR")
print("   e forced via p: Comp(PP,PP) =", sorted(e_via_p))
print("   e forced via q: Comp(PP,DR) =", sorted(e_via_q))
print("   intersection:", sorted(e_via_p & e_via_q), "(empty => no coherent N* exists)")

# source-triangle necessity: PP,PP with third side DR is not closed
print("   source-triangle (PP,PP,DR): DR in Comp(PP,PP)?", 'DR' in COMP[('PP','PP')])

# ------------------------------------ 8. G2a tower row divergence (profiles equal, rows differ)
# a1 PP a2 PP a3 PP a4 PP a5 on a chain; row(a1, a3) vs row(a5, a3)
print("8. G2a tower: rho(a1,a3) = PP by Comp(PP,PP)={PP}; rho(a5,a3) = PPI by",
      "Comp(PPI,PPI)={PPI};  identical (type,Omega) profiles, distinct rows -> ",
      "profile-quotient loses necessary information")

# ------------------------------------ 9. G2a witness concept sanity (chain model, no DR pairs)
chain = [frozenset(range(k+1)) for k in range(6)]
rels = {rel(X, Y) for X in chain for Y in chain if X != Y}
print("9. G2a model sanity: pairwise relations on nested chain:", sorted(rels),
      "(no DR pairs; forall DR.A vacuous; concept satisfiable)")
