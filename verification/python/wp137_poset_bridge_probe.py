#!/usr/bin/env python3
"""WP137 -- the POSET BRIDGE, and what it finds.

Companion probe to formal/PosetBridge.lean.  The Lean file PROVES the
statements; this script re-checks them by brute force against an RCC5 table
derived here from set semantics, so that nothing rests on a shared
transcription, and it runs the project's own reasoners on the concepts the
bridge produces.

THE BRIDGE.  Read  E||.C  as  E PO.C or E DR.C,  and  A||.C  as
A PO.C and A DR.C.  Then a concept of the tense logic of strict partial orders
(modalities  =, <, >, ||  where || is incomparability) is satisfiable over a
strict partial order iff its reading is satisfiable in ALCI_RCC5:

  ->  a strict partial order, with every incomparable pair declared PO and DR
      left EMPTY, is a composition-closed RCC5 network;
  <-  in any RCC5 model, PP is a strict partial order and its incomparable
      pairs are exactly the PO-or-DR pairs.

Two constructors come for free on top: a bare  E PO.C  (read  E||.C)  and a
bare  A DR.C  (read  T).  Two do NOT: a bare  A PO.C  and a bare  E DR.C.

PARTS
  A  the RCC5 composition table, derived from set semantics (n = 4, 5, 6)
  B  frame level, exhaustive:
       B1  every strict partial order on <= 5 points, read with PO on every
           incomparable pair, is composition-closed            (bridge ->)
       B2  every composition-closed atomic network on <= 4 points has a
           strict-partial-order PP-reduct whose incomparable pairs are
           exactly its PO-or-DR pairs                          (bridge <-)
  C  truth level, pointwise on random models and random concepts, both
     directions, with the two negative controls (bare A PO, bare E DR)
  D  the spiral (Marzec & Tendera's Phi_spiral): the Z-spiral satisfies it;
     no strict partial order on <= 6 points does (<= 9 with python-sat); and
     the reason, a 5-cycle
  E  the project's reasoners on bridge concepts with a KNOWN answer:
       K2 = E PO.(A & A PO.~B & A DR.~B) & E PO.(B & ~A)
     is satisfiable in a three-region set model, verified here.  The
     cover-tree tableau answers UNSAT.  Also C_cyc, three proper superparts
     forced into a cycle: unsatisfiable, satisfiable once its A PO conjuncts
     are erased.

Self-contained except for part E, which imports the two reasoners from src/,
and the optional extension of D2, which uses python-sat if it is installed.
"""

import itertools
import os
import random
import sys
import time

EQ, PP, PPI, PO, DR = "EQ", "PP", "PPI", "PO", "DR"
ATOMS = [EQ, PP, PPI, PO, DR]
CONV = {EQ: EQ, PP: PPI, PPI: PP, PO: PO, DR: DR}

RESULTS = []


def check(name, ok, detail=""):
    RESULTS.append((name, ok))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"  -- {detail}" if detail else ""))
    return ok


# --------------------------------------------------------------------- part A
def set_rel(a, b):
    if a == b:
        return EQ
    if a < b:
        return PP
    if b < a:
        return PPI
    if not (a & b):
        return DR
    return PO


def derive_table(n):
    regs = [frozenset(c) for k in range(1, n + 1)
            for c in itertools.combinations(range(n), k)]
    t = {(r, s): set() for r in ATOMS for s in ATOMS}
    for a in regs:
        for b in regs:
            r = set_rel(a, b)
            for c in regs:
                t[(r, set_rel(b, c))].add(set_rel(a, c))
    return {k: frozenset(v) for k, v in t.items()}


def part_a():
    print("PART A -- the composition table, from set semantics")
    t4, t5, t6 = derive_table(4), derive_table(5), derive_table(6)
    check("A1 table stable from n=4 (n=4 == n=5 == n=6)", t4 == t5 == t6)
    check("A2 comp(PP,PP) = {PP}  (transitivity of the reduct)",
          t5[(PP, PP)] == {PP})
    vert = (PP, PPI, PO)
    check("A3 PO lies in comp(r,s) for all r,s in {PP,PPI,PO} except the two "
          "transitivity cells -- why DR can be left empty",
          all((PO in t5[(r, s)]) != ((r, s) in ((PP, PP), (PPI, PPI)))
              for r in vert for s in vert))
    return t5


# --------------------------------------------------------------------- part B
def strict_orders(n):
    """All strict partial orders on range(n), as frozensets of pairs."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for choice in itertools.product((0, 1, 2), repeat=len(pairs)):
        lt = set()
        for (i, j), c in zip(pairs, choice):
            if c == 1:
                lt.add((i, j))
            elif c == 2:
                lt.add((j, i))
        ok = True
        for (a, b) in lt:
            for c in range(n):
                if (b, c) in lt and (a, c) not in lt:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            yield frozenset(lt)


def po_completion(n, lt):
    """The bridge's RCC5 reading of a strict partial order: DR empty."""
    net = {}
    for i in range(n):
        for j in range(n):
            if i == j:
                net[(i, j)] = EQ
            elif (i, j) in lt:
                net[(i, j)] = PP
            elif (j, i) in lt:
                net[(i, j)] = PPI
            else:
                net[(i, j)] = PO
    return net


def closed(n, net, table):
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if net[(i, k)] not in table[(net[(i, j)], net[(j, k)])]:
                    return False
    return True


def atomic_networks(n, table):
    """All composition-closed, converse-coherent atomic networks, strong EQ."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for choice in itertools.product((PP, PPI, PO, DR), repeat=len(pairs)):
        net = {(i, i): EQ for i in range(n)}
        for (i, j), r in zip(pairs, choice):
            net[(i, j)] = r
            net[(j, i)] = CONV[r]
        if closed(n, net, table):
            yield net


def part_b(table):
    print("\nPART B -- frame level, exhaustive")
    tot = bad = 0
    for n in range(1, 6):
        for lt in strict_orders(n):
            tot += 1
            if not closed(n, po_completion(n, lt), table):
                bad += 1
    check("B1 every strict partial order on <=5 points is an RCC5 network "
          "under the PO-reading", bad == 0, f"{tot} orders, {bad} not closed")
    tot = bad = 0
    for n in range(1, 5):
        for net in atomic_networks(n, table):
            tot += 1
            lt = {(i, j) for i in range(n) for j in range(n)
                  if net[(i, j)] == PP}
            irr = all((i, i) not in lt for i in range(n))
            tr = all((a, c) in lt for (a, b) in lt for c in range(n)
                     if (b, c) in lt)
            inc_ok = all(
                ((i != j and (i, j) not in lt and (j, i) not in lt)
                 == (net[(i, j)] in (PO, DR)))
                for i in range(n) for j in range(n))
            if not (irr and tr and inc_ok):
                bad += 1
    check("B2 every closed atomic network on <=4 points: PP is a strict "
          "partial order, incomparable = PO-or-DR",
          bad == 0, f"{tot} networks, {bad} failures")


# --------------------------------------------------------------------- part C
# poset-logic concepts:  ('at',a) ('nat',a) ('and',c,d) ('or',c,d)
#   ('ex',r,c) ('all',r,c) with r in {'eq','lt','gt','inc'}
#   ('xpo',c)  bare E PO      ('adr',c)  bare A DR
# RCC5 concepts: same Boolean part, ('ex',R,c) / ('all',R,c) with R an atom.
ROLE = {"eq": EQ, "lt": PP, "gt": PPI}


def emb(c):
    k = c[0]
    if k in ("at", "nat", "top", "bot"):
        return c
    if k in ("and", "or"):
        return (k, emb(c[1]), emb(c[2]))
    if k == "xpo":
        return ("ex", PO, emb(c[1]))
    if k == "adr":
        return ("all", DR, emb(c[1]))
    r, body = c[1], emb(c[2])
    if r != "inc":
        return (k, ROLE[r], body)
    if k == "ex":
        return ("or", ("ex", PO, body), ("ex", DR, body))
    return ("and", ("all", PO, body), ("all", DR, body))


def sat(n, net, val, x, c):
    k = c[0]
    if k == "top":
        return True
    if k == "bot":
        return False
    if k == "at":
        return val[x][c[1]]
    if k == "nat":
        return not val[x][c[1]]
    if k == "and":
        return sat(n, net, val, x, c[1]) and sat(n, net, val, x, c[2])
    if k == "or":
        return sat(n, net, val, x, c[1]) or sat(n, net, val, x, c[2])
    ys = [y for y in range(n) if net[(x, y)] == c[1]]
    if k == "ex":
        return any(sat(n, net, val, y, c[2]) for y in ys)
    return all(sat(n, net, val, y, c[2]) for y in ys)


def prel(lt, r, x, y):
    if r == "eq":
        return x == y
    if r == "lt":
        return (x, y) in lt
    if r == "gt":
        return (y, x) in lt
    return x != y and (x, y) not in lt and (y, x) not in lt


def psat(n, lt, val, x, c):
    k = c[0]
    if k == "top":
        return True
    if k == "bot":
        return False
    if k == "at":
        return val[x][c[1]]
    if k == "nat":
        return not val[x][c[1]]
    if k == "and":
        return psat(n, lt, val, x, c[1]) and psat(n, lt, val, x, c[2])
    if k == "or":
        return psat(n, lt, val, x, c[1]) or psat(n, lt, val, x, c[2])
    if k == "xpo":
        return any(psat(n, lt, val, y, c[1]) for y in range(n)
                   if prel(lt, "inc", x, y))
    if k == "adr":
        return True
    ys = [y for y in range(n) if prel(lt, c[1], x, y)]
    if k == "ex":
        return any(psat(n, lt, val, y, c[2]) for y in ys)
    return all(psat(n, lt, val, y, c[2]) for y in ys)


def rand_pconcept(rng, depth, extras):
    if depth == 0 or rng.random() < 0.2:
        a = rng.randrange(2)
        return ("at", a) if rng.random() < 0.5 else ("nat", a)
    u = rng.random()
    if u < 0.2:
        return ("and", rand_pconcept(rng, depth - 1, extras),
                rand_pconcept(rng, depth - 1, extras))
    if u < 0.35:
        return ("or", rand_pconcept(rng, depth - 1, extras),
                rand_pconcept(rng, depth - 1, extras))
    if extras and u < 0.45:
        return ("xpo", rand_pconcept(rng, depth - 1, extras))
    if extras and u < 0.55:
        return ("adr", rand_pconcept(rng, depth - 1, extras))
    r = rng.choice(["lt", "gt", "inc", "inc", "eq"])
    q = "ex" if rng.random() < 0.5 else "all"
    return (q, r, rand_pconcept(rng, depth - 1, extras))


def pure(c):
    k = c[0]
    if k in ("xpo", "adr"):
        return False
    if k in ("and", "or"):
        return pure(c[1]) and pure(c[2])
    if k in ("ex", "all"):
        return pure(c[2])
    return True


def rand_set_model(rng):
    n = rng.randint(2, 7)
    univ = rng.randint(2, 6)
    regs = set()
    guard = 0
    while len(regs) < n and guard < 200:
        guard += 1
        s = frozenset(i for i in range(univ) if rng.random() < 0.45)
        if s:
            regs.add(s)
    regs = sorted(regs, key=sorted)
    n = len(regs)
    net = {(i, j): set_rel(regs[i], regs[j]) for i in range(n) for j in range(n)}
    return n, net


def rand_poset(rng):
    n = rng.randint(2, 7)
    order = list(range(n))
    rng.shuffle(order)
    lt = set()
    for a in range(n):
        for b in range(a + 1, n):
            if rng.random() < 0.3:
                lt.add((order[a], order[b]))
    changed = True
    while changed:
        changed = False
        for (a, b) in list(lt):
            for (c, d) in list(lt):
                if b == c and (a, d) not in lt:
                    lt.add((a, d))
                    changed = True
    return n, frozenset(lt)


def part_c():
    print("\nPART C -- truth level, pointwise")
    rng = random.Random(137137)
    # down: an RCC5 set model and its PP-reduct
    pts = viol = pure_pts = pure_viol = dr_models = 0
    for _ in range(3000):
        n, net = rand_set_model(rng)
        if any(v == DR for v in net.values()):
            dr_models += 1
        lt = frozenset((i, j) for i in range(n) for j in range(n)
                       if net[(i, j)] == PP)
        val = [[rng.random() < 0.5 for _ in range(2)] for _ in range(n)]
        c = rand_pconcept(rng, rng.randint(1, 3), extras=True)
        e = emb(c)
        isp = pure(c)
        for x in range(n):
            s, p = sat(n, net, val, x, e), psat(n, lt, val, x, c)
            pts += 1
            if s and not p:
                viol += 1
            if isp:
                pure_pts += 1
                if s != p:
                    pure_viol += 1
    check("C1 down: sat(emb c) in a set model  =>  psat(c) in its PP-reduct",
          viol == 0, f"{pts} points, {dr_models}/3000 models contain DR, "
                     f"{viol} violations")
    check("C2 down, pure concepts (no bare E PO / A DR): an EQUIVALENCE",
          pure_viol == 0 and pure_pts > 0,
          f"{pure_pts} points, {pure_viol} mismatches")
    # up: a strict partial order and its PO-reading
    pts = viol = pure_pts = pure_viol = 0
    for _ in range(3000):
        n, lt = rand_poset(rng)
        net = po_completion(n, lt)
        val = [[rng.random() < 0.5 for _ in range(2)] for _ in range(n)]
        c = rand_pconcept(rng, rng.randint(1, 3), extras=True)
        e = emb(c)
        isp = pure(c)
        for x in range(n):
            s, p = sat(n, net, val, x, e), psat(n, lt, val, x, c)
            pts += 1
            if p and not s:
                viol += 1
            if isp:
                pure_pts += 1
                if s != p:
                    pure_viol += 1
    check("C3 up: psat(c) in a strict partial order  =>  sat(emb c) in its "
          "PO-reading", viol == 0, f"{pts} points, {viol} violations")
    check("C4 up, pure concepts: an EQUIVALENCE", pure_viol == 0 and pure_pts > 0,
          f"{pure_pts} points, {pure_viol} mismatches")
    # negative controls -- the two constructors the bridge must NOT admit
    # (i) a bare A PO: two DISJOINT regions; A PO.bot holds, A||.bot does not
    regs = [frozenset({0}), frozenset({1})]
    net = {(i, j): set_rel(regs[i], regs[j]) for i in range(2) for j in range(2)}
    val = [[False, False], [False, False]]
    holds_rcc5 = sat(2, net, val, 0, ("all", PO, ("bot",)))
    holds_poset = psat(2, frozenset(), val, 0, ("all", "inc", ("bot",)))
    check("C5 control: a bare A PO does NOT transfer down "
          "(two disjoint regions)", holds_rcc5 and not holds_poset)
    # (ii) a bare E DR: two incomparable points; E||.top holds, E DR.top fails
    net = po_completion(2, frozenset())
    holds_poset = psat(2, frozenset(), val, 0, ("ex", "inc", ("top",)))
    holds_rcc5 = sat(2, net, val, 0, ("ex", DR, ("top",)))
    check("C6 control: a bare E DR does NOT transfer up "
          "(the PO-reading has no DR)", holds_poset and not holds_rcc5)


# --------------------------------------------------------------------- part D
class Cnf:
    def __init__(self):
        self.n = 0
        self.clauses = []

    def var(self):
        self.n += 1
        return self.n

    def add(self, *lits):
        self.clauses.append(list(lits))


def dpll(nvars, clauses, budget=4_000_000):
    """Plain DPLL with unit propagation.  Returns True/False, or None if the
    step budget runs out."""
    assign = [0] * (nvars + 1)
    occ = {}
    for ci, cl in enumerate(clauses):
        for l in cl:
            occ.setdefault(l, []).append(ci)
    steps = [0]

    def propagate(trail_start, trail):
        i = trail_start
        while i < len(trail):
            lit = trail[i]
            i += 1
            for ci in occ.get(-lit, ()):
                cl = clauses[ci]
                unassigned = None
                satisfied = False
                count = 0
                for l in cl:
                    v = assign[abs(l)]
                    if v == 0:
                        unassigned = l
                        count += 1
                    elif (v > 0) == (l > 0):
                        satisfied = True
                        break
                if satisfied:
                    continue
                if count == 0:
                    return False
                if count == 1:
                    assign[abs(unassigned)] = 1 if unassigned > 0 else -1
                    trail.append(unassigned)
        return True

    def solve(trail):
        steps[0] += 1
        if steps[0] > budget:
            return None
        # choose the variable from the shortest unsatisfied clause
        best = None
        for cl in clauses:
            free = []
            satisfied = False
            for l in cl:
                v = assign[abs(l)]
                if v == 0:
                    free.append(l)
                elif (v > 0) == (l > 0):
                    satisfied = True
                    break
            if satisfied:
                continue
            if not free:
                return False
            if best is None or len(free) < len(best):
                best = free
                if len(best) == 2:
                    break
        if best is None:
            return True
        for lit in (best[0], -best[0]):
            mark = len(trail)
            assign[abs(lit)] = 1 if lit > 0 else -1
            trail.append(lit)
            if propagate(mark, trail):
                r = solve(trail)
                if r is not False:
                    return r
            while len(trail) > mark:
                assign[abs(trail.pop())] = 0
        return False

    trail = []
    for cl in clauses:
        if len(cl) == 1:
            l = cl[0]
            v = assign[abs(l)]
            if v == 0:
                assign[abs(l)] = 1 if l > 0 else -1
                trail.append(l)
            elif (v > 0) != (l > 0):
                return False
    if not propagate(0, trail):
        return False
    return solve(trail)


def spiral_cnf(n, colours=5, entangle=True):
    """The spiral over a strict partial order on n points, as CNF."""
    f = Cnf()
    L = {(i, j): f.var() for i in range(n) for j in range(n) if i != j}
    C = {(i, a): f.var() for i in range(n) for a in range(colours)}
    for i in range(n):
        for j in range(i + 1, n):
            f.add(-L[(i, j)], -L[(j, i)])
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if len({i, j, k}) == 3:
                    f.add(-L[(i, j)], -L[(j, k)], L[(i, k)])
    for i in range(n):
        f.add(*[C[(i, a)] for a in range(colours)])
    f.add(C[(0, 0)])                       # symmetry: point 0 has colour 0
    if entangle:
        for i in range(n):
            for j in range(n):
                if i != j:
                    for a in range(colours):
                        f.add(-C[(i, a)], -C[(j, (a + 2) % colours)],
                              L[(i, j)], L[(j, i)])
    for step in (1, colours - 1):
        for i in range(n):
            for a in range(colours):
                ws = []
                for j in range(n):
                    if j == i:
                        continue
                    w = f.var()
                    ws.append(w)
                    f.add(-w, C[(j, (a + step) % colours)])
                    f.add(-w, -L[(i, j)])
                    f.add(-w, -L[(j, i)])
                f.add(-C[(i, a)], *ws)
    return f


def part_d():
    print("\nPART D -- the spiral")
    # D1: the Z-spiral, on a window; conditions checked at interior points
    lo, hi = -40, 40
    lt = lambda a, b: a + 2 <= b
    inc = lambda a, b: a != b and not lt(a, b) and not lt(b, a)
    col = lambda a: a % 5
    ok = True
    for x in range(lo + 2, hi - 1):
        for y in range(lo, hi + 1):
            if inc(x, y) and col(y) == (col(x) + 2) % 5:
                ok = False
        if not any(inc(x, y) and col(y) == (col(x) + 1) % 5
                   for y in range(lo, hi + 1)):
            ok = False
        if not any(inc(x, y) and col(y) == (col(x) + 4) % 5
                   for y in range(lo, hi + 1)):
            ok = False
    tr = all(lt(a, c) for a in range(lo, hi) for b in range(lo, hi)
             for c in range(lo, hi) if lt(a, b) and lt(b, c))
    check("D1 the Z-spiral (a<b iff a+2<=b, colour a mod 5) satisfies every "
          "condition on a window", ok and tr)
    # D2: no finite model.  The built-in DPLL covers n <= 6 with no
    # dependency; if python-sat happens to be installed, n = 7..9 as well.
    t0 = time.time()
    verdicts = {}
    for n in range(1, 7):
        f = spiral_cnf(n)
        verdicts[n] = dpll(f.n, f.clauses)
    check("D2 no strict partial order on <=6 points satisfies the spiral "
          "(built-in DPLL)", all(v is False for v in verdicts.values()),
          f"{time.time()-t0:.1f}s")
    try:
        from pysat.solvers import Cadical153
    except Exception:
        print("  [SKIP] python-sat not installed -- n = 7..9 not searched")
    else:
        t0 = time.time()
        ext = {}
        for n in range(7, 10):
            f = spiral_cnf(n)
            solver = Cadical153(bootstrap_with=f.clauses)
            ext[n] = solver.solve()
            solver.delete()
        check("D2+ nor on 7, 8 or 9 points (CaDiCaL via python-sat)",
              all(v is False for v in ext.values()), f"{time.time()-t0:.1f}s")
    # D3: the search is not vacuous -- drop the entanglements and it is SAT
    f = spiral_cnf(5, entangle=False)
    check("D3 control: without the entanglements a 5-point model exists",
          dpll(f.n, f.clauses) is True)
    # D4: with FOUR colours the same sentence has a finite model
    f = spiral_cnf(4, colours=4)
    check("D4 control: with four colours instead of five a 4-point model "
          "exists (2+2)", dpll(f.n, f.clauses) is True)
    # D5: the obstruction: on five points in a cycle of incomparabilities the
    # comparability graph is a 5-cycle, which has no transitive orientation
    edges = [(i, (i + 2) % 5) for i in range(5)]
    orient = 0
    for bits in itertools.product((0, 1), repeat=5):
        lt5 = {(a, b) if bit else (b, a) for (a, b), bit in zip(edges, bits)}
        tr5 = all((a, c) in lt5 for (a, b) in lt5 for (b2, c) in lt5 if b == b2)
        if tr5:
            orient += 1
    check("D5 the pentagon of comparabilities has no transitive orientation",
          orient == 0, f"{orient}/32 orientations transitive")


# --------------------------------------------------------------------- part E
def part_e(table):
    print("\nPART E -- the project's reasoners on bridge concepts")
    here = os.path.dirname(os.path.abspath(__file__))
    src = None
    for cand in (os.path.join(here, "..", "..", "src"), os.path.join(here, "src")):
        if os.path.exists(os.path.join(cand, "cover_tree_tableau.py")):
            src = os.path.abspath(cand)
            break
    # K2 and its explicit set model, independent of any reasoner
    A, B = 0, 1
    k2 = ("and",
          ("ex", PO, ("and", ("at", A),
                      ("and", ("all", PO, ("nat", B)), ("all", DR, ("nat", B))))),
          ("ex", PO, ("and", ("at", B), ("nat", A))))
    regs = [frozenset({1, 3}), frozenset({1, 4}), frozenset({1, 4, 5})]
    net = {(i, j): set_rel(regs[i], regs[j]) for i in range(3) for j in range(3)}
    val = [[False, False], [True, False], [False, True]]
    shape = (net[(0, 1)], net[(0, 2)], net[(1, 2)]) == (PO, PO, PP)
    check("E1 K2 is SATISFIABLE: r={1,3}, a={1,4}, b={1,4,5}; "
          "r PO a, r PO b, a PP b", shape and closed(3, net, table)
          and sat(3, net, val, 0, k2))
    k2dr = ("and",
            ("ex", DR, ("and", ("at", A),
                        ("and", ("all", PO, ("nat", B)), ("all", DR, ("nat", B))))),
            ("ex", DR, ("and", ("at", B), ("nat", A))))
    regs2 = [frozenset({3}), frozenset({1}), frozenset({1, 2})]
    net2 = {(i, j): set_rel(regs2[i], regs2[j]) for i in range(3) for j in range(3)}
    check("E2 K2dr (the same with DR witnesses) is SATISFIABLE: "
          "r={3}, a={1}, b={1,2}", closed(3, net2, table)
          and sat(3, net2, val, 0, k2dr))
    # exhaustive on <= 3 points: K2 needs three points, and every 3-point
    # model has the shape above up to the direction of the nesting
    sizes = set()
    shapes = set()
    for n in range(1, 4):
        for netn in atomic_networks(n, table):
            for bits in itertools.product((False, True), repeat=2 * n):
                valn = [[bits[2 * i], bits[2 * i + 1]] for i in range(n)]
                for x in range(n):
                    if sat(n, netn, valn, x, k2):
                        sizes.add(n)
                        others = [y for y in range(n) if y != x]
                        shapes.add(frozenset((netn[(others[0], others[1])],
                                              netn[(others[1], others[0])])))
    check("E3 exhaustive on <=3 points: K2 has no model on 1 or 2 points, "
          "and in every 3-point model the two witnesses are PP/PPI-related",
          sizes == {3} and shapes == {frozenset((PP, PPI))},
          f"model sizes {sorted(sizes)}, witness relations "
          f"{sorted(sorted(sh) for sh in shapes)}")
    # C_cyc: three proper superparts forced into a cycle a < b < c < a
    Cc = 2

    def wit(p, q, erase):
        boxes = [("all", DR, ("nat", q)), ("all", PPI, ("nat", q))]
        if not erase:
            boxes.insert(0, ("all", PO, ("nat", q)))
        body = ("at", p)
        for extra in [("nat", q)] + boxes:
            body = ("and", body, extra)
        return ("ex", PP, body)

    def ccyc(erase):
        return ("and", wit(A, B, erase),
                ("and", wit(B, Cc, erase), wit(Cc, A, erase)))

    regs4 = [frozenset({1}), frozenset({1, 2, 5}), frozenset({1, 3, 5}),
             frozenset({1, 4, 5})]
    net4 = {(i, j): set_rel(regs4[i], regs4[j]) for i in range(4) for j in range(4)}
    val4 = [[False] * 3, [True, False, False], [False, True, False],
            [False, False, True]]
    check("E4 C_cyc with its three A PO conjuncts ERASED is satisfiable: "
          "r={1}, a={1,2,5}, b={1,3,5}, c={1,4,5} (pairwise PO)",
          closed(4, net4, table) and sat(4, net4, val4, 0, ccyc(True))
          and not sat(4, net4, val4, 0, ccyc(False)))
    found = False
    for n in range(1, 5):
        for netn in atomic_networks(n, table):
            roots = [x for x in range(n)
                     if sum(1 for y in range(n) if netn[(x, y)] == PP) >= 3]
            for x in roots:
                for bits in itertools.product((False, True), repeat=3 * n):
                    valn = [list(bits[3 * i:3 * i + 3]) for i in range(n)]
                    if sat(n, netn, valn, x, ccyc(False)):
                        found = True
    check("E5 C_cyc itself has no model on <=4 points (exhaustive; it needs "
          "a root and three distinct proper superparts)", not found)
    if src is None:
        print("  [SKIP] src/ not found -- reasoner verdicts not run")
        return
    sys.path.insert(0, src)
    import alcircc5_reasoner as Q
    import cover_tree_tableau as T
    from alcircc5_reasoner import (AtomicConcept, NegAtomicConcept, And,
                                   Exists, ForAll)
    rel = {PO: Q.PO, DR: Q.DR, PP: Q.PP, PPI: Q.PPI}

    def conv(c):
        k = c[0]
        if k == "at":
            return AtomicConcept("AB"[c[1]])
        if k == "nat":
            return NegAtomicConcept("AB"[c[1]])
        if k == "and":
            return And(conv(c[1]), conv(c[2]))
        if k == "ex":
            return Exists(rel[c[1]], conv(c[2]))
        return ForAll(rel[c[1]], conv(c[2]))

    for name, c in (("K2", k2), ("K2dr", k2dr)):
        tv = T.check_satisfiability(conv(c))[0]
        qv = Q.check_satisfiability(conv(c))
        qv = qv[0] if isinstance(qv, tuple) else qv
        print(f"  {name}: cover-tree tableau says {'SAT' if tv else 'UNSAT'}, "
              f"quasimodel oracle says {'SAT' if qv else 'UNSAT'}; "
              f"truth: SAT (model above)")
        check(f"E6 {name}: the cover-tree tableau REJECTS a satisfiable "
              f"concept (verdict UNSAT)", tv is False)
        check(f"E7 {name}: the quasimodel oracle accepts it", bool(qv))
    # the control: uncouple the universal and the tableau accepts
    k2free = ("and",
              ("ex", PO, ("and", ("at", A), ("all", PO, ("nat", B)))),
              ("ex", PO, ("and", ("at", B), ("nat", A))))
    tv = T.check_satisfiability(conv(k2free))[0]
    check("E8 control: drop A DR.~B (the witnesses may then be disjoint) and "
          "the tableau accepts", tv is True)


def main():
    print("=" * 76)
    print("WP137 -- the poset bridge: FO2 over strict partial orders inside "
          "ALCI_RCC5")
    print("=" * 76)
    table = part_a()
    part_b(table)
    part_c()
    part_d()
    part_e(table)
    print("\n" + "=" * 76)
    bad = [n for n, ok in RESULTS if not ok]
    print(f"{len(RESULTS) - len(bad)}/{len(RESULTS)} checks pass"
          + ("" if not bad else "; FAILED: " + "; ".join(bad)))
    print("=" * 76)
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
