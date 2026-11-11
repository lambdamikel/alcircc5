#!/usr/bin/env python3
"""
A complete-graph ABox tableau for ALCI_RCC5, after MiDeLoRa
============================================================

A reference reasoner. Sound and complete, NOT terminating:

  * it answers UNSAT on every unsatisfiable concept (given enough nodes and time),
  * it answers SAT, with a finite model, on every concept that has a finite model,
  * on a satisfiable concept all of whose models are infinite it never answers
    (here: it returns UNKNOWN when the node bound or the time limit is reached).

That is the most a procedure can do without deciding the logic; the missing third
property, termination, is blocking, and blocking is the open problem. Statement
and proof: papers/midelora_calculus/README.md.

Where the calculus comes from. It is the calculus of the ALCI_RA_JEPD prover in
M. Wessel's MiDeLoRa (dissertation, TU Hamburg-Harburg 2008, sections 6.2.7.2
and 6.4.4; source: github.com/lambdamikel/midelora,
prover/alci-ra-jepd-prover.lisp, prover/some-expansion2.lisp,
thematic-substrate/jepd-substrate4.lisp):

    MiDeLoRa                                   here
    ------------------------------------------ ---------------------------------
    abox-role-completion: every pair of        a new node is related to EVERY
      individuals gets the full disjunction      existing node by one base
    abox-enumeration + role-consistent-p:        relation, and the composition
      resolve to base relations, keep only       table is checked on every
      relationally consistent configurations     triangle (_place)
    deterministic-expansion                    _saturate (and-rule, all-rule)
    or-expansion                               the or-rule
    some-expansion, *reuse-nodes-p*            the exists-rule: an existing
                                                 R-successor, or a fresh node
    no blocking                                no blocking

The one point of difference is EQ.

  eq='strong' (default; the semantics of this project): EQ is identity. Two
      different nodes are never EQ, so the only way to "be" an existing node is
      to reuse it, and reuse is always on. Equivalently: MiDeLoRa's enumeration
      with an EQ edge followed by its join-nodes (eq-collapse), which exists in
      the substrate but is not called by the prover.
  eq='weak': MiDeLoRa as implemented. EQ is an ordinary reflexive, symmetric,
      transitive role with its composition rows; two different nodes may be EQ
      and keep different labels. Every strong model is a weak model, so UNSAT
      under 'weak' implies UNSAT under 'strong'; the converse fails (K2x in
      verification/python/wp139_midelora_reference.py).

Search. Depth-first over the nondeterministic rules, inside iterative deepening
on the number of nodes. For a bound N a fresh node is refused when N nodes
exist; such a branch is CUT, not closed. "Every branch closed and none cut" is
a finite closed tableau, hence a refutation. Demands are served oldest node
first; labels are subsets of a finite closure, so that order is fair.

The composition table is derived here from sets (regions = non-empty subsets
of a 5-element universe) and not copied from anywhere.

Usage:
    from midelora_tableau import check
    r = check(concept, max_nodes=6)        # r.verdict in {'SAT','UNSAT','UNKNOWN'}
    r.model                                 # (labels, rel) when SAT
    python3 midelora_tableau.py             # a few examples
"""

import itertools
import time

from alcircc5_reasoner import (DR, PO, PP, PPI, AtomicConcept, NegAtomicConcept,
                               Top, Bottom, And, Or, Exists, ForAll)

EQ = 'EQ'
PROPER = (DR, PO, PP, PPI)
ALL5 = (DR, PO, EQ, PP, PPI)
INV5 = {DR: DR, PO: PO, EQ: EQ, PP: PPI, PPI: PP}


def _set_rel(a, b):
    if a == b:
        return EQ
    if a < b:
        return PP
    if a > b:
        return PPI
    return PO if a & b else DR


def derive_table(n=5):
    """RCC5 composition from set semantics: comp[(R,S)] = {rel(a,c) : a R b, b S c}."""
    regs = [frozenset(s) for k in range(1, n + 1) for s in itertools.combinations(range(n), k)]
    comp = {(r, s): set() for r in ALL5 for s in ALL5}
    for a in regs:
        for b in regs:
            rab = _set_rel(a, b)
            for c in regs:
                comp[(rab, _set_rel(b, c))].add(_set_rel(a, c))
    return {k: frozenset(v) for k, v in comp.items()}


COMP5 = derive_table()


class Timeout(Exception):
    pass


class Result:
    def __init__(self, verdict, model=None, nodes=None, closed=0, cut=0, seconds=0.0, reason=''):
        self.verdict = verdict      # 'SAT' | 'UNSAT' | 'UNKNOWN'
        self.model = model          # (labels: list[frozenset], rel: list[list]) when SAT
        self.nodes = nodes          # node bound at which the verdict was reached
        self.closed = closed        # closed leaves of the last tableau
        self.cut = cut              # branches cut by the node bound in the last tableau
        self.seconds = seconds
        self.reason = reason

    def __repr__(self):
        return (f"Result({self.verdict}, nodes={self.nodes}, closed={self.closed}, "
                f"cut={self.cut}, {self.seconds:.2f}s{', ' + self.reason if self.reason else ''})")


def _key(c):
    return str(c)


def _refuted(c, Li):
    """c is a literal (or bottom) that clashes with the label Li."""
    if isinstance(c, Bottom):
        return True
    if isinstance(c, AtomicConcept):
        return NegAtomicConcept(c.name) in Li
    if isinstance(c, NegAtomicConcept):
        return AtomicConcept(c.name) in Li
    return False


def _saturate(L, rel, n, weak):
    """Deterministic rules to a fixpoint. False on a clash. Unassigned relations are None."""
    changed = True
    while changed:
        changed = False
        for i in range(n):
            Li = L[i]
            for c in list(Li):
                if isinstance(c, And):
                    for d in (c.left, c.right):
                        if d not in Li:
                            Li.add(d)
                            changed = True
                elif isinstance(c, ForAll):
                    R = c.role
                    if R == EQ:
                        targets = [i]
                        if weak:
                            targets += [j for j in range(n) if j != i and rel[i][j] == EQ]
                    else:
                        targets = [j for j in range(n) if j != i and rel[i][j] == R]
                    for j in targets:
                        if c.concept not in L[j]:
                            L[j].add(c.concept)
                            changed = True
                elif isinstance(c, Exists) and c.role == EQ and not weak:
                    if c.concept not in Li:          # strong EQ: the only EQ-successor is the node itself
                        Li.add(c.concept)
                        changed = True
                elif isinstance(c, Or) and c.left not in Li and c.right not in Li:
                    # the or-rule when one alternative closes at once (a literal whose
                    # complement is present): take the other. Sound, and it saves a branch.
                    if _refuted(c.left, Li):
                        Li.add(c.right)
                        changed = True
                    elif _refuted(c.right, Li):
                        Li.add(c.left)
                        changed = True
    for i in range(n):
        for c in L[i]:
            if isinstance(c, Bottom):
                return False
            if isinstance(c, AtomicConcept) and NegAtomicConcept(c.name) in L[i]:
                return False
    return True


def _find_or(L, n):
    for i in range(n):
        for c in sorted(L[i], key=_key):
            if isinstance(c, Or) and c.left not in L[i] and c.right not in L[i]:
                return i, c
    return None


def _find_demand(L, rel, n, weak):
    for i in range(n):
        for c in sorted(L[i], key=_key):
            if not isinstance(c, Exists):
                continue
            R = c.role
            if R == EQ:
                if not weak:
                    continue                          # done by _saturate
                if c.concept in L[i] or any(j != i and rel[i][j] == EQ and c.concept in L[j]
                                            for j in range(n)):
                    continue
            elif any(j != i and rel[i][j] == R and c.concept in L[j] for j in range(n)):
                continue
            return i, c
    return None


class _Search:
    def __init__(self, weak, reuse, deadline):
        self.weak = weak
        self.reuse = reuse or not weak        # strong EQ needs reuse for completeness
        self.deadline = deadline
        self.closed = 0
        self.cut = 0
        self.model = None
        self.ticks = 0

    def tick(self):
        self.ticks += 1
        if self.deadline is not None and self.ticks % 256 == 0 and time.time() > self.deadline:
            raise Timeout()

    def dfs(self, L, rel, n, bound):
        """True iff a saturated clash-free state was reached (self.model is set)."""
        self.tick()
        if not _saturate(L, rel, n, self.weak):
            self.closed += 1
            return False
        hit = _find_or(L, n)
        if hit:
            i, c = hit
            for d in (c.left, c.right):
                L2 = [set(x) for x in L]
                L2[i].add(d)
                if self.dfs(L2, rel, n, bound):
                    return True
            return False
        hit = _find_demand(L, rel, n, self.weak)
        if not hit:
            self.model = ([frozenset(x) for x in L], [list(row) for row in rel])
            return True
        i, c = hit
        R, C = c.role, c.concept
        if self.reuse:
            cands = [j for j in range(n) if j != i and rel[i][j] == R]
            if R == EQ:
                cands = [i] + cands                   # weak EQ is reflexive
            for j in cands:
                L2 = [set(x) for x in L]
                L2[j].add(C)
                if self.dfs(L2, rel, n, bound):
                    return True
        if n >= bound:
            self.cut += 1
            return False
        # a fresh node y = n, related to EVERY existing node by one base relation
        rel2 = [list(row) + [None] for row in rel] + [[None] * (n + 1)]
        rel2[i][n] = R
        rel2[n][i] = INV5[R]
        L2 = [set(x) for x in L] + [{C}]
        order = [k for k in range(n) if k != i]
        return self._place(L2, rel2, n, order, 0, bound)

    def _place(self, L, rel, y, order, idx, bound):
        self.tick()
        L = [set(x) for x in L]
        if not _saturate(L, rel, y + 1, self.weak):   # early clash on the partial network
            self.closed += 1
            return False
        if idx == len(order):
            return self.dfs(L, rel, y + 1, bound)
        k = order[idx]
        for r in (ALL5 if self.weak else PROPER):
            ok = True
            for m in range(y):                        # every triangle (y, m, k) with m already related to y
                s = rel[y][m]
                if m == k or s is None:
                    continue
                if (r not in COMP5[(s, rel[m][k])]
                        or rel[m][k] not in COMP5[(INV5[s], r)]
                        or s not in COMP5[(r, rel[k][m])]):
                    ok = False
                    break
            if not ok:
                continue
            rel[y][k] = r
            rel[k][y] = INV5[r]
            found = self._place(L, rel, y, order, idx + 1, bound)
            if found:
                return True
            rel[y][k] = None
            rel[k][y] = None
        return False


def check(C0, max_nodes=6, eq='strong', reuse=True, time_limit=None, min_nodes=1):
    """Satisfiability of the NNF concept C0. See the module docstring for the guarantees."""
    assert eq in ('strong', 'weak')
    t0 = time.time()
    deadline = None if time_limit is None else t0 + time_limit
    last = None
    for bound in range(min_nodes, max_nodes + 1):
        s = _Search(eq == 'weak', reuse, deadline)
        try:
            found = s.dfs([{C0}], [[None]], 1, bound)
        except Timeout:
            return Result('UNKNOWN', nodes=bound, closed=s.closed, cut=s.cut,
                          seconds=time.time() - t0, reason='time limit')
        if found:
            return Result('SAT', model=s.model, nodes=len(s.model[0]), closed=s.closed, cut=s.cut,
                          seconds=time.time() - t0)
        if s.cut == 0:                                # a finite closed tableau: a refutation
            return Result('UNSAT', nodes=bound, closed=s.closed, cut=0, seconds=time.time() - t0)
        last = s
    return Result('UNKNOWN', nodes=max_nodes, closed=last.closed, cut=last.cut,
                  seconds=time.time() - t0, reason='node bound')


def verify_model(C0, model, eq='strong'):
    """Independent check of a returned model: a closed atomic network in which C0 holds at node 0
    under the valuation read off the labels. Uses nothing of the search."""
    L, rel = model
    n = len(L)
    weak = eq == 'weak'
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            r = rel[i][j]
            if r not in ALL5 or (r == EQ and not weak) or rel[j][i] != INV5[r]:
                return False
            for k in range(n):
                if k != i and k != j and rel[i][k] not in COMP5[(r, rel[j][k])]:
                    return False

    def holds(c, x):
        if isinstance(c, Top):
            return True
        if isinstance(c, Bottom):
            return False
        if isinstance(c, AtomicConcept):
            return c in L[x]
        if isinstance(c, NegAtomicConcept):
            return AtomicConcept(c.name) not in L[x]
        if isinstance(c, And):
            return holds(c.left, x) and holds(c.right, x)
        if isinstance(c, Or):
            return holds(c.left, x) or holds(c.right, x)
        succ = [x] if c.role == EQ else []
        succ += [y for y in range(n) if y != x and rel[x][y] == c.role]
        if isinstance(c, Exists):
            return any(holds(c.concept, y) for y in succ)
        if isinstance(c, ForAll):
            return all(holds(c.concept, y) for y in succ)
        raise TypeError(c)
    return holds(C0, 0)


if __name__ == '__main__':
    A, B = AtomicConcept('A'), AtomicConcept('B')
    nA, nB = NegAtomicConcept('A'), NegAtomicConcept('B')

    def conj(*xs):
        r = xs[0]
        for x in xs[1:]:
            r = And(r, x)
        return r
    K2 = conj(Exists(PO, conj(A, ForAll(PO, nB), ForAll(DR, nB))), Exists(PO, conj(B, nA)))
    K2X = conj(Exists(PO, conj(A, ForAll(PO, nB), ForAll(DR, nB), ForAll(PP, nB), ForAll(PPI, nB))),
               Exists(PO, conj(B, nA)))
    INF = conj(Exists(PP, Top()), ForAll(PP, Exists(PP, Top())))
    for name, c, kw in (('K2', K2, {}), ('K2x strong', K2X, {}), ('K2x weak', K2X, {'eq': 'weak'}),
                        ('EPP.T & APP.EPP.T', INF, {'max_nodes': 5})):
        r = check(c, **kw)
        extra = ''
        if r.verdict == 'SAT':
            extra = '  model verified: ' + str(verify_model(c, r.model, kw.get('eq', 'strong')))
        print(f"{name:20s} {r}{extra}")
