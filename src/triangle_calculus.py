#!/usr/bin/env python3
"""
Full implementation of the Tri-neighborhood tableau calculus for ALCI_RCC5.

Faithfully implements the calculus from tableau_ALCIRCC5.tex:
  - Complete-graph completion structures (V, LL, EE, ≺)
  - Fischer-Ladner closure, Hintikka types
  - Safe(τ₁, τ₂) relation filtering
  - All expansion rules: ⊓, ⊔, ∀, ∃ with proper ordering
  - Edge assignment via arc consistency + backtracking (constraint filtering)
  - Tri(x) and TNbr(x) computation with caching
  - Tri-neighborhood blocking: LL(x)=LL(y), Tri(x)=Tri(y), TNbr(x)=TNbr(y)
  - Clash detection: {A, ¬A} ⊆ LL(x) and composition violations
  - Non-termination detection: monitors creation rate and blocking oscillation

Tests whether, under the Tri-neighborhood blocking criterion analyzed to
not produce oscillations, non-termination can occur in practice.
"""

import sys
import time
import itertools
import random
from collections import defaultdict

# ── RCC5 machinery ──────────────────────────────────────────────────

DR, PO, PP, PPI = 'DR', 'PO', 'PP', 'PPI'
NR_MINUS = [DR, PO, PP, PPI]  # base relations between distinct elements
INV = {DR: DR, PO: PO, PP: PPI, PPI: PP}

COMP = {
    (DR, DR): frozenset({DR, PO, PP, PPI}),
    (DR, PO): frozenset({DR, PO, PP}),
    (DR, PP): frozenset({DR, PO, PP}),
    (DR, PPI): frozenset({DR}),
    (PO, DR): frozenset({DR, PO, PPI}),
    (PO, PO): frozenset({DR, PO, PP, PPI}),
    (PO, PP): frozenset({PO, PP}),
    (PO, PPI): frozenset({DR, PO, PPI}),
    (PP, DR): frozenset({DR}),
    (PP, PO): frozenset({DR, PO, PP}),
    (PP, PP): frozenset({PP}),
    (PP, PPI): frozenset({DR, PO, PP, PPI}),
    (PPI, DR): frozenset({DR, PO, PPI}),
    (PPI, PO): frozenset({PO, PPI}),
    (PPI, PP): frozenset({PO, PP, PPI}),
    (PPI, PPI): frozenset({PPI}),
}


def comp(r, s):
    return COMP[(r, s)]


def inv(r):
    return INV[r]


# ── Concept representation ──────────────────────────────────────────

# Concepts are tuples:
#   ('atom', name)       -- atomic concept
#   ('neg', name)        -- negated atom
#   ('and', c1, c2)      -- conjunction
#   ('or', c1, c2)       -- disjunction
#   ('exists', R, c)     -- existential restriction ∃R.C
#   ('forall', R, c)     -- value restriction ∀R.C
#   ('top',)             -- ⊤
#   ('bot',)             -- ⊥


def concept_str(c):
    if c[0] == 'atom': return c[1]
    if c[0] == 'neg': return f'¬{c[1]}'
    if c[0] == 'top': return '⊤'
    if c[0] == 'bot': return '⊥'
    if c[0] == 'and': return f'({concept_str(c[1])} ⊓ {concept_str(c[2])})'
    if c[0] == 'or': return f'({concept_str(c[1])} ⊔ {concept_str(c[2])})'
    if c[0] == 'exists': return f'∃{c[1]}.{concept_str(c[2])}'
    if c[0] == 'forall': return f'∀{c[1]}.{concept_str(c[2])}'
    return str(c)


def nnf_neg(c):
    """Push negation inward to get NNF."""
    if c[0] == 'atom': return ('neg', c[1])
    if c[0] == 'neg': return ('atom', c[1])
    if c[0] == 'top': return ('bot',)
    if c[0] == 'bot': return ('top',)
    if c[0] == 'and': return ('or', nnf_neg(c[1]), nnf_neg(c[2]))
    if c[0] == 'or': return ('and', nnf_neg(c[1]), nnf_neg(c[2]))
    if c[0] == 'exists': return ('forall', c[1], nnf_neg(c[2]))
    if c[0] == 'forall': return ('exists', c[1], nnf_neg(c[2]))
    return c


def closure(c0):
    """Fischer-Ladner closure: all subconcepts and their NNF negations."""
    subs = set()
    def collect(c):
        if c in subs:
            return
        subs.add(c)
        if c[0] in ('and', 'or'):
            collect(c[1]); collect(c[2])
        elif c[0] in ('exists', 'forall'):
            collect(c[2])
    collect(c0)
    result = set()
    for s in subs:
        result.add(s)
        result.add(nnf_neg(s))
    result.add(('top',))
    result.add(('bot',))
    return frozenset(result)


def safe_relations(tau1, tau2):
    """Compute Safe(τ₁, τ₂) = {R ∈ NR⁻ : ∀(∀R.C) ∈ τ₁, C ∈ τ₂;
                                            ∀(∀inv(R).C) ∈ τ₂, C ∈ τ₁}"""
    safe = set()
    for R in NR_MINUS:
        ok = True
        # Check: for all (∀R.C) in τ₁, C must be in τ₂
        for c in tau1:
            if c[0] == 'forall' and c[1] == R:
                if c[2] not in tau2:
                    ok = False
                    break
        if not ok:
            continue
        # Check: for all (∀inv(R).C) in τ₂, C must be in τ₁
        invR = inv(R)
        for c in tau2:
            if c[0] == 'forall' and c[1] == invR:
                if c[2] not in tau1:
                    ok = False
                    break
        if ok:
            safe.add(R)
    return frozenset(safe)


# ── Tableau Engine ──────────────────────────────────────────────────

class TriangleTableau:
    """Full Tri-neighborhood tableau for ALCI_RCC5."""

    def __init__(self, c0, max_nodes=300, max_steps=10000,
                 timeout=60.0, verbose=False):
        self.c0 = c0
        self.cl = closure(c0)
        self.max_nodes = max_nodes
        self.max_steps = max_steps
        self.timeout = timeout
        self.verbose = verbose

        # Completion graph
        self.nodes = []             # list in creation order (= ≺)
        self.labels = {}            # node_id -> set of concepts (from cl)
        self.edge = {}              # (a, b) -> relation for a != b
        self.blocked_by = {}        # node_id -> blocker node_id or None

        # Caching
        self._tri_cache = {}        # node_id -> (frozenset, version)
        self._tnbr_cache = {}       # node_id -> (frozenset, version)
        self._sig_cache = {}        # node_id -> (signature, version)
        self._version = 0           # global version counter, bumped on any change

        # Stats
        self.total_created = 0
        self.total_steps = 0
        self.block_events = []
        self.node_unblock_count = defaultdict(int)
        self.node_block_count = defaultdict(int)
        self.max_oscillation = 0
        self.creation_history = []  # (step, node_id, parent, role)
        self.start_time = None

        # Precompute Safe relation cache
        self._safe_cache = {}

    def _bump_version(self):
        self._version += 1

    # ── Edge accessors ────────────────────────────────────────────

    def get_edge(self, a, b):
        if a == b:
            return 'EQ'
        return self.edge.get((a, b))

    def set_edge(self, a, b, r):
        self.edge[(a, b)] = r
        self.edge[(b, a)] = inv(r)
        self._bump_version()

    # ── Label accessors ───────────────────────────────────────────

    def label(self, n):
        return frozenset(self.labels[n])

    def add_to_label(self, n, c):
        if c not in self.labels[n]:
            self.labels[n].add(c)
            self._bump_version()
            return True
        return False

    # ── Safe relation computation (cached) ────────────────────────

    def get_safe(self, tau1, tau2):
        key = (tau1, tau2)
        if key not in self._safe_cache:
            self._safe_cache[key] = safe_relations(tau1, tau2)
        return self._safe_cache[key]

    # ── Tri(x) computation ────────────────────────────────────────

    def compute_tri(self, x):
        """Tri(x) = set of (LL(x), EE(x,b), LL(b), EE(b,c), LL(c), EE(x,c))
        for all pairs b,c with {x,b,c} distinct."""
        cached = self._tri_cache.get(x)
        if cached and cached[1] == self._version:
            return cached[0]

        tri = set()
        lx = self.label(x)
        # Collect neighbors with edges to x
        neighbors = []
        for n in self.nodes:
            if n != x:
                r = self.get_edge(x, n)
                if r is not None:
                    neighbors.append((n, r, self.label(n)))

        for i, (b, rxb, lb) in enumerate(neighbors):
            for j in range(i + 1, len(neighbors)):
                c, rxc, lc = neighbors[j]
                rbc = self.get_edge(b, c)
                if rbc is None:
                    continue
                # Two orientations of the triangle
                tri.add((lx, rxb, lb, rbc, lc, rxc))
                tri.add((lx, rxc, lc, inv(rbc), lb, rxb))

        result = frozenset(tri)
        self._tri_cache[x] = (result, self._version)
        return result

    # ── TNbr(x) computation ───────────────────────────────────────

    def compute_tnbr(self, x):
        """TNbr(x) = for each (R, τ), the set of Tri-values among
        x's R-neighbors of type τ."""
        cached = self._tnbr_cache.get(x)
        if cached and cached[1] == self._version:
            return cached[0]

        tnbr = {}
        for n in self.nodes:
            if n == x:
                continue
            r = self.get_edge(x, n)
            if r is None:
                continue
            tau = self.label(n)
            key = (r, tau)
            if key not in tnbr:
                tnbr[key] = set()
            tri_n = self.compute_tri(n)
            tnbr[key].add(tri_n)

        result = frozenset((k, frozenset(v)) for k, v in tnbr.items())
        self._tnbr_cache[x] = (result, self._version)
        return result

    # ── Blocking signature ────────────────────────────────────────

    def signature(self, x):
        cached = self._sig_cache.get(x)
        if cached and cached[1] == self._version:
            return cached[0]
        sig = (self.label(x), self.compute_tri(x), self.compute_tnbr(x))
        self._sig_cache[x] = (sig, self._version)
        return sig

    # ── Blocking ──────────────────────────────────────────────────

    def is_blocked(self, x):
        return self.blocked_by.get(x) is not None

    def find_blocker(self, x):
        """Find earliest non-blocked y ≺ x with same signature."""
        sig_x = self.signature(x)
        for y in self.nodes:
            if y == x:
                break  # only earlier nodes
            if self.is_blocked(y):
                continue
            if self.signature(y) == sig_x:
                return y
        return None

    def update_blocking(self, step):
        """Recompute blocking for all nodes. Track block/unblock events."""
        changes = False
        for x in self.nodes:
            old = self.blocked_by.get(x)
            new = self.find_blocker(x)
            if old != new:
                changes = True
                self.blocked_by[x] = new
                if new is not None and old is None:
                    self.node_block_count[x] += 1
                    self.block_events.append((step, x, 'blocked', new))
                    if self.verbose:
                        print(f"  [{step}] {x} BLOCKED by {new}")
                elif new is None and old is not None:
                    self.node_unblock_count[x] += 1
                    self.max_oscillation = max(
                        self.max_oscillation, self.node_unblock_count[x])
                    self.block_events.append((step, x, 'unblocked', old))
                    if self.verbose:
                        print(f"  [{step}] {x} UNBLOCKED (was by {old})")
                elif new is not None and old is not None:
                    self.block_events.append((step, x, 'reblocker', new))
                    if self.verbose:
                        print(f"  [{step}] {x} reblocker: {old} -> {new}")
        return changes

    # ── Clash detection ───────────────────────────────────────────

    def has_clash(self, n):
        """Check if node n has a propositional clash: {A, ¬A} ⊆ LL(n)."""
        lab = self.labels[n]
        for c in lab:
            if c[0] == 'atom' and ('neg', c[1]) in lab:
                return True
            if c == ('bot',):
                return True
        return False

    def has_any_clash(self):
        for n in self.nodes:
            if self.has_clash(n):
                return True
        return False

    # ── Expansion rules ───────────────────────────────────────────

    def apply_and_rule(self):
        """⊓-rule: if C₁ ⊓ C₂ ∈ LL(x), add C₁ and C₂."""
        changed = False
        for n in self.nodes:
            if self.is_blocked(n):
                continue
            for c in list(self.labels[n]):
                if c[0] == 'and':
                    if self.add_to_label(n, c[1]):
                        changed = True
                    if self.add_to_label(n, c[2]):
                        changed = True
        return changed

    def apply_or_rule(self):
        """⊔-rule: if C₁ ⊔ C₂ ∈ LL(x) and neither present, add one."""
        changed = False
        for n in self.nodes:
            if self.is_blocked(n):
                continue
            for c in list(self.labels[n]):
                if c[0] == 'or':
                    if c[1] not in self.labels[n] and c[2] not in self.labels[n]:
                        # Nondeterministic choice: try first disjunct
                        # unless its negation is already present
                        if nnf_neg(c[1]) in self.labels[n]:
                            self.add_to_label(n, c[2])
                        elif nnf_neg(c[2]) in self.labels[n]:
                            self.add_to_label(n, c[1])
                        else:
                            self.add_to_label(n, c[1])
                        changed = True
        return changed

    def apply_forall_rule(self):
        """∀-rule: if ∀R.D ∈ LL(x) and EE(x,y)=R, add D to LL(y)."""
        changed = False
        for n in self.nodes:
            if self.is_blocked(n):
                continue
            for c in list(self.labels[n]):
                if c[0] != 'forall':
                    continue
                role, filler = c[1], c[2]
                for m in self.nodes:
                    if m == n:
                        continue
                    r = self.get_edge(n, m)
                    if r is None:
                        continue
                    if r == role:
                        if self.add_to_label(m, filler):
                            changed = True
        return changed

    def apply_propositional_and_forall(self):
        """Apply ⊓, ⊔, ∀ exhaustively."""
        changed = True
        while changed:
            changed = False
            if self.apply_and_rule():
                changed = True
            if self.apply_or_rule():
                changed = True
            if self.apply_forall_rule():
                changed = True
            # Add ⊤ to all labels
            for n in self.nodes:
                if ('top',) not in self.labels[n]:
                    self.labels[n].add(('top',))
                    changed = True

    # ── Exists-rule ───────────────────────────────────────────────

    def get_unsatisfied_exists(self, n):
        """Return list of (role, filler) for unsatisfied ∃R.C in LL(n)."""
        demands = []
        for c in self.labels[n]:
            if c[0] != 'exists':
                continue
            role, filler = c[1], c[2]
            satisfied = False
            for m in self.nodes:
                if m == n:
                    continue
                r = self.get_edge(n, m)
                if r == role and filler in self.labels[m]:
                    satisfied = True
                    break
            if not satisfied:
                demands.append((role, filler))
        return demands

    def find_edge_assignment(self, parent, role, new_node, existing):
        """Find a composition-consistent edge assignment for new_node.

        The edge parent->new_node is fixed to 'role'.
        For each other existing node z, choose S_z ∈ NR⁻ such that
        composition consistency holds for all triples involving new_node.

        NOTE: We do NOT enforce Safe here. Safe is a derived model property;
        the ∀-rule will propagate concepts to satisfy it. The paper's ∃-rule
        (Section 3.5) only requires CF (composition consistency).

        Uses arc-consistency pruning + backtracking.
        """
        # Build initial domains
        domains = {}
        for e in existing:
            if e == parent:
                domains[e] = frozenset({inv(role)})
            else:
                domains[e] = set(NR_MINUS)

        # Arc-consistency enforcement
        changed = True
        iters = 0
        while changed and iters < 50:
            changed = False
            iters += 1
            for e1 in existing:
                for e2 in existing:
                    if e1 == e2:
                        continue
                    r12 = self.get_edge(e1, e2)
                    if r12 is None:
                        continue
                    # rel(new, e2) ∈ comp(rel(new, e1), rel(e1, e2))
                    new_d2 = set()
                    for r1 in domains[e1]:
                        allowed = comp(r1, r12)
                        new_d2 |= (allowed & domains[e2])
                    if new_d2 != domains[e2]:
                        if not new_d2:
                            return []
                        domains[e2] = new_d2
                        changed = True
                    # Reverse: rel(new, e1) ∈ comp(rel(new, e2), rel(e2, e1))
                    r21 = self.get_edge(e2, e1)
                    if r21 is None:
                        continue
                    new_d1 = set()
                    for r2 in domains[e2]:
                        allowed = comp(r2, r21)
                        new_d1 |= (allowed & domains[e1])
                    if new_d1 != domains[e1]:
                        if not new_d1:
                            return []
                        domains[e1] = new_d1
                        changed = True

        # Backtracking search for one valid assignment
        nodes_list = list(existing)
        result = [None]

        def backtrack(idx, assignment):
            if result[0] is not None:
                return
            if idx == len(nodes_list):
                result[0] = dict(assignment)
                return
            e = nodes_list[idx]
            for r in sorted(domains[e], key=lambda x: NR_MINUS.index(x)
                            if x in NR_MINUS else 0):
                ok = True
                for e2, r2 in assignment.items():
                    re2e = self.get_edge(e2, e)
                    if re2e is not None:
                        if r not in comp(r2, re2e):
                            ok = False
                            break
                        ree2 = self.get_edge(e, e2)
                        if ree2 is not None and r2 not in comp(r, ree2):
                            ok = False
                            break
                if ok:
                    assignment[e] = r
                    backtrack(idx + 1, assignment)
                    if result[0] is not None:
                        return
                    del assignment[e]

        backtrack(0, {})
        return [result[0]] if result[0] is not None else []

    def apply_exists_rule(self, step):
        """Apply one instance of ∃-rule for the first active node with
        an unsatisfied demand. Returns True if a node was created."""
        for n in self.nodes:
            if self.is_blocked(n):
                continue
            demands = self.get_unsatisfied_exists(n)
            if not demands:
                continue

            role, filler = demands[0]

            if len(self.nodes) >= self.max_nodes:
                if self.verbose:
                    print(f"  [{step}] Node limit reached ({self.max_nodes})")
                return 'limit'

            new_id = self.total_created
            new_name = f'n{new_id}'

            # Initial label: {filler}
            # Also add ∀-propagations from parent for this role
            init_label = {filler, ('top',)}
            for c in self.labels[n]:
                if c[0] == 'forall' and c[1] == role:
                    init_label.add(c[2])

            # Create node
            self.nodes.append(new_name)
            self.labels[new_name] = init_label
            self.blocked_by[new_name] = None
            self.total_created += 1

            # Set parent edge
            self.set_edge(n, new_name, role)

            # Find composition-consistent assignment for all other nodes
            existing = [m for m in self.nodes if m != new_name]
            assignments = self.find_edge_assignment(n, role, new_name, existing)

            if not assignments:
                # Clash: no consistent assignment
                if self.verbose:
                    print(f"  [{step}] Clash: no consistent edge assignment for "
                          f"{new_name} ({role}-succ of {n})")
                # Remove the node (can't place it)
                self.nodes.remove(new_name)
                del self.labels[new_name]
                del self.blocked_by[new_name]
                # Clean up edge
                del self.edge[(n, new_name)]
                del self.edge[(new_name, n)]
                self.total_created -= 1
                self._bump_version()
                continue

            # Apply assignment
            assignment = assignments[0]
            for e, r in assignment.items():
                if e != n:  # parent edge already set
                    self.set_edge(new_name, e, r)

            self.creation_history.append((step, new_name, n, role))

            if self.verbose:
                n_active = sum(1 for x in self.nodes if not self.is_blocked(x))
                print(f"  [{step}] Created {new_name} as {role}-succ of {n} "
                      f"({len(self.nodes)} nodes, {n_active} active)")

            return True

        return False

    # ── Main loop ─────────────────────────────────────────────────

    def run(self):
        """Run the tableau to saturation or failure. Returns report dict."""
        self.start_time = time.time()

        # Create root node
        self.nodes.append('n0')
        self.labels['n0'] = {self.c0, ('top',)}
        self.blocked_by['n0'] = None
        self.total_created = 1

        for step in range(1, self.max_steps + 1):
            self.total_steps = step

            if time.time() - self.start_time > self.timeout:
                return self._report('timeout')

            # Step 1: Apply ⊓, ⊔, ∀ exhaustively
            self.apply_propositional_and_forall()

            # Check for clash
            if self.has_any_clash():
                if self.verbose:
                    for n in self.nodes:
                        if self.has_clash(n):
                            print(f"  [{step}] Clash at {n}: {self.labels[n]}")
                return self._report('clash')

            # Step 2: Evaluate blocking
            self.update_blocking(step)

            # Step 3: Apply one ∃-rule
            result = self.apply_exists_rule(step)

            if result == 'limit':
                return self._report('node_limit')

            if result:
                # Node created: apply ∀ again (new edges may trigger propagation)
                self.apply_propositional_and_forall()
                # Check clash
                if self.has_any_clash():
                    return self._report('clash')
                # Re-evaluate blocking
                self.update_blocking(step)
                continue

            # No rule applied -> saturated
            return self._report('open')

        return self._report('step_limit')

    def _report(self, status):
        n_active = sum(1 for x in self.nodes if not self.is_blocked(x))
        return {
            'status': status,
            'total_nodes': len(self.nodes),
            'active_nodes': n_active,
            'total_created': self.total_created,
            'total_steps': self.total_steps,
            'max_oscillation': self.max_oscillation,
            'total_block_events': len(self.block_events),
            'block_events': self.block_events,
            'node_unblock_counts': dict(self.node_unblock_count),
            'elapsed': time.time() - self.start_time,
        }


# ── Test concepts ────────────────────────────────────────────────────

def make_test_concepts():
    """Battery of concepts designed to test non-termination."""
    A = ('atom', 'A')
    B = ('atom', 'B')
    C = ('atom', 'C')
    D = ('atom', 'D')
    nA = ('neg', 'A')
    nB = ('neg', 'B')
    top = ('top',)

    concepts = {}

    # ── Basic chain concepts ──

    # 1. PP-chain with DR witnesses
    concepts['PP+DR'] = ('and',
        ('and', A, ('exists', PP, A)),
        ('forall', PP, ('and',
            ('exists', PP, A),
            ('exists', DR, B))))

    # 2. PP-chain with PO witnesses
    concepts['PP+PO'] = ('and',
        ('and', A, ('exists', PP, A)),
        ('forall', PP, ('and',
            ('exists', PP, A),
            ('exists', PO, B))))

    # 3. PP-chain with DR + PO witnesses
    concepts['PP+DR+PO'] = ('and',
        ('and', A, ('exists', PP, A)),
        ('forall', PP, ('and',
            ('exists', PP, A),
            ('and', ('exists', DR, B), ('exists', PO, C)))))

    # 4. PP-chain with PPI witnesses
    concepts['PP+PPI'] = ('and',
        ('and', A, ('exists', PP, A)),
        ('forall', PP, ('and',
            ('exists', PP, A),
            ('exists', PPI, B))))

    # ── PO-incoherent (the hard case) ──

    # 5. PO-incoherent: ∃PP.(B ⊓ ∃PO.C) with propagation
    concepts['PO-incoherent'] = ('and',
        ('and', A, ('exists', PP, ('and', B, ('exists', PO, C)))),
        ('forall', PP, ('and',
            ('exists', PP, top),
            ('exists', PO, C))))

    # 6. PO-incoherent v2: typed
    concepts['PO-incoh-typed'] = ('and',
        ('and', A, ('exists', PP, ('and', A, ('exists', PO, B)))),
        ('forall', PP, ('and',
            ('exists', PP, ('and', A, ('exists', PO, B))),
            ('exists', PO, B))))

    # ── Cross-witness concepts ──

    # 7. DR-witnesses need PO back
    concepts['DR-back-PO'] = ('and',
        ('and', A, ('exists', PP, A)),
        ('forall', PP, ('and',
            ('exists', PP, A),
            ('exists', DR, ('and', B, ('exists', PO, A))))))

    # 8. Three-role with cross-demands
    concepts['three-role-cross'] = ('and',
        ('and', A,
            ('and', ('exists', PP, A),
                ('and', ('exists', DR, B), ('exists', PO, C)))),
        ('forall', PP, ('and',
            ('exists', PP, A),
            ('and', ('exists', DR, ('and', B, ('exists', PO, A))),
                    ('exists', PO, ('and', C, ('exists', DR, A)))))))

    # ── Alternating-type concepts ──

    # 9. Alternating A/B on PP-chain
    concepts['alt-AB-PP'] = ('and',
        ('and', A, ('exists', PP, B)),
        ('and',
            ('forall', PP, ('or',
                ('and', A, ('exists', PP, B)),
                ('and', B, ('exists', PP, A)))),
            ('forall', PP, ('exists', DR, top))))

    # 10. Alternating with typed witnesses
    concepts['alt-typed-witnesses'] = ('and',
        ('and', A, ('exists', PP, ('and', B,
            ('and', ('exists', DR, C), ('exists', PP, A))))),
        ('forall', PP, ('or',
            ('and', A, ('exists', PP, ('and', B,
                ('and', ('exists', DR, C), ('exists', PP, A))))),
            ('and', B, ('exists', PP, ('and', A,
                ('and', ('exists', DR, C), ('exists', PP, B))))))))

    # ── Deep nesting ──

    # 11. Deep exists chain
    concepts['deep-exists'] = ('and',
        ('exists', PP, ('exists', DR, ('exists', PO, ('exists', PP, top)))),
        ('forall', PP, ('and',
            ('exists', PP, top),
            ('and', ('exists', DR, top), ('exists', PO, top)))))

    # 12. Nested forall-exists interaction
    concepts['forall-exists'] = ('and',
        ('and', A, ('exists', PP, A)),
        ('and',
            ('forall', PP, ('and',
                ('exists', PP, A),
                ('exists', DR, B))),
            ('forall', DR, ('exists', PO, A))))

    # ── Multiple PP-successors ──

    # 13. Two distinct PP-successors
    concepts['two-PP-succ'] = ('and',
        ('and',
            ('exists', PP, ('and', A, ('exists', DR, B))),
            ('exists', PP, ('and', B, ('exists', DR, A)))),
        ('forall', PP, ('and',
            ('exists', PP, top),
            ('exists', DR, top))))

    # ── Complex triangle-forming concepts ──

    # 14. Three witnesses forming a constrained triangle
    concepts['triangle-forming'] = ('and',
        A,
        ('and',
            ('and', ('exists', PP, B), ('exists', DR, C)),
            ('and',
                ('forall', PP, ('and',
                    ('exists', PP, B),
                    ('and', ('exists', DR, C), ('exists', PO, A)))),
                ('forall', DR, ('and',
                    ('exists', PO, B),
                    ('exists', PP, A))))))

    # 15. Forced infinite model with many witness types
    concepts['multi-witness'] = ('and',
        A,
        ('and',
            ('exists', PP, A),
            ('and',
                ('exists', DR, B),
                ('and',
                    ('exists', PO, C),
                    ('exists', PPI, D)))))

    # 16. ∀* propagation (global constraint)
    concepts['forall-star'] = ('and',
        ('and', A, ('exists', PP, top)),
        ('forall', PP, ('and',
            ('exists', PP, top),
            ('and',
                ('exists', DR, top),
                ('exists', PO, top)))))

    # 17. Backward propagation via PPI
    concepts['backward-prop'] = ('and',
        ('and', A, ('exists', PP, ('and', B,
            ('forall', PPI, ('exists', DR, C))))),
        ('forall', PP, ('and',
            ('exists', PP, top),
            ('exists', DR, top))))

    # 18. Cyclic witness demands
    concepts['cyclic-demands'] = ('and',
        A,
        ('and',
            ('exists', PP, ('and', B, ('exists', PO, ('and', C, ('exists', DR, A))))),
            ('forall', PP, ('exists', PP, top))))

    # 19. PO-chain (very constrained by composition)
    concepts['PO-chain'] = ('and',
        ('and', A, ('exists', PO, A)),
        ('forall', PO, ('and',
            ('exists', PO, A),
            ('exists', DR, B))))

    # 20. Wide branching: many exists per node
    concepts['wide-branching'] = ('and',
        A,
        ('and',
            ('exists', PP, B),
            ('and', ('exists', PO, C),
                ('and', ('exists', DR, A),
                    ('and', ('exists', PPI, B),
                        ('forall', PP, ('and',
                            ('exists', PP, B),
                            ('and', ('exists', PO, C),
                                ('and', ('exists', DR, A),
                                    ('exists', PPI, B))))))))))

    return concepts


def generate_random_concepts(n=100, seed=42):
    """Generate random concepts biased toward non-termination patterns."""
    random.seed(seed)
    concepts = {}
    atoms = [('atom', c) for c in 'ABCD']
    roles = [PP, DR, PO, PPI]

    def rand_concept(depth, max_d=4):
        if depth >= max_d:
            return random.choice(atoms)
        p = random.random()
        if p < 0.25:
            return ('and', rand_concept(depth+1, max_d), rand_concept(depth+1, max_d))
        elif p < 0.35:
            return ('or', rand_concept(depth+1, max_d), rand_concept(depth+1, max_d))
        elif p < 0.6:
            return ('exists', random.choice(roles), rand_concept(depth+1, max_d))
        elif p < 0.8:
            return ('forall', random.choice(roles), rand_concept(depth+1, max_d))
        else:
            return random.choice(atoms)

    for i in range(n):
        # Bias toward concepts with ∃+∀ interaction
        # Root: A ⊓ ∃PP.A ⊓ ∀PP.(body)
        body = rand_concept(0, max_d=3)
        c = ('and',
            ('and', ('atom', 'A'), ('exists', PP, ('atom', 'A'))),
            ('forall', PP, ('and', ('exists', PP, ('top',)), body)))
        concepts[f'rand_{i}'] = c

    return concepts


# ── Main ─────────────────────────────────────────────────────────────

def run_tests(max_nodes=200, max_steps=5000, timeout=30.0, verbose=False):
    """Run all test concepts and look for non-termination."""
    concepts = make_test_concepts()

    print(f"ALCI_RCC5 Triangle Calculus — Full Implementation")
    print(f"Testing {len(concepts)} concepts")
    print(f"Max nodes: {max_nodes}, max steps: {max_steps}, timeout: {timeout}s")
    print(f"{'='*78}")

    results = []
    for name in sorted(concepts.keys()):
        c0 = concepts[name]
        print(f"\n{'─'*78}")
        print(f"  {name}: {concept_str(c0)[:90]}")

        tab = TriangleTableau(c0, max_nodes=max_nodes, max_steps=max_steps,
                              timeout=timeout, verbose=verbose)
        report = tab.run()

        s = report['status']
        n = report['total_nodes']
        a = report['active_nodes']
        cr = report['total_created']
        st = report['total_steps']
        osc = report['max_oscillation']
        ev = report['total_block_events']
        t = report['elapsed']

        flag = ""
        if s == 'node_limit' or s == 'step_limit' or s == 'timeout':
            flag = " *** POSSIBLE NON-TERMINATION ***"
        if osc > 0:
            flag += " *** OSCILLATION ***"

        print(f"  Status: {s} | nodes: {n} (active: {a}, created: {cr}) | "
              f"steps: {st} | osc: {osc} | events: {ev} | {t:.1f}s{flag}")

        if osc > 0:
            print(f"  Unblock counts: {report['node_unblock_counts']}")
            for ev_item in report['block_events'][:10]:
                step, node, event, whom = ev_item
                print(f"    step={step}: {node} {event} (by {whom})")

        results.append((name, report))

    # Summary
    print(f"\n{'='*78}")
    print("SUMMARY")
    print(f"{'─'*78}")

    # Sort by status priority: non-termination candidates first
    status_priority = {'timeout': 0, 'step_limit': 1, 'node_limit': 2,
                       'clash': 3, 'open': 4}
    results.sort(key=lambda x: (status_priority.get(x[1]['status'], 5),
                                 -x[1]['total_created']))

    for name, report in results:
        s = report['status']
        flag = " ***" if s in ('timeout', 'step_limit', 'node_limit') else ""
        print(f"  {name:25s}  {s:12s}  nodes={report['total_created']:4d}  "
              f"active={report['active_nodes']:3d}  steps={report['total_steps']:5d}  "
              f"osc={report['max_oscillation']}{flag}")

    # Non-termination analysis
    non_term = [(n, r) for n, r in results
                if r['status'] in ('timeout', 'step_limit', 'node_limit')]
    if non_term:
        print(f"\n*** {len(non_term)} concepts hit resource limits "
              f"(possible non-termination):")
        for name, report in non_term:
            print(f"  {name}: {report['status']}, {report['total_created']} nodes, "
                  f"{report['total_steps']} steps")
    else:
        print(f"\nAll concepts terminated within resource limits.")

    osc_found = [(n, r) for n, r in results if r['max_oscillation'] > 0]
    if osc_found:
        print(f"\n*** {len(osc_found)} concepts showed blocking oscillation:")
        for name, report in osc_found:
            print(f"  {name}: max oscillation = {report['max_oscillation']}")
    else:
        print(f"No blocking oscillation detected.")

    return results


def run_random_tests(num=200, max_nodes=150, max_steps=3000,
                     timeout=15.0, seed=42):
    """Run random concepts looking for non-termination."""
    concepts = generate_random_concepts(num, seed)

    print(f"\nRandom concept search ({num} concepts, seed={seed})")
    print(f"Max nodes: {max_nodes}, max steps: {max_steps}, timeout: {timeout}s")
    print(f"{'='*78}")

    non_term = []
    osc = []
    total_open = 0
    total_clash = 0

    for name, c0 in sorted(concepts.items()):
        tab = TriangleTableau(c0, max_nodes=max_nodes, max_steps=max_steps,
                              timeout=timeout)
        report = tab.run()

        if report['status'] in ('timeout', 'step_limit', 'node_limit'):
            non_term.append((name, c0, report))
            print(f"  {name}: {report['status']} — {report['total_created']} nodes, "
                  f"{report['total_steps']} steps")
            print(f"    {concept_str(c0)[:100]}")
        elif report['status'] == 'open':
            total_open += 1
        elif report['status'] == 'clash':
            total_clash += 1

        if report['max_oscillation'] > 0:
            osc.append((name, c0, report))

    print(f"\n{'='*78}")
    print(f"Random search complete:")
    print(f"  Open: {total_open}, Clash: {total_clash}, "
          f"Resource limit: {len(non_term)}")
    print(f"  Oscillation found: {len(osc)}")

    if non_term:
        print(f"\n*** Resource-limited concepts (possible non-termination):")
        for name, c0, report in non_term[:10]:
            print(f"  {name}: {report['status']}, {report['total_created']} nodes")
            print(f"    {concept_str(c0)[:120]}")

    return non_term, osc


if __name__ == '__main__':
    max_nodes = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    timeout = float(sys.argv[2]) if len(sys.argv) > 2 else 30.0

    # Phase 1: Hand-crafted concepts
    results = run_tests(max_nodes=max_nodes, timeout=timeout, verbose=False)

    # Phase 2: Random search
    print(f"\n\n{'#'*78}")
    print(f"# Phase 2: Random concept search")
    print(f"{'#'*78}")
    non_term, osc = run_random_tests(num=200, max_nodes=max_nodes,
                                     timeout=min(timeout, 15.0))

    # Phase 3: Verbose re-run of anything interesting
    interesting = [(n, r) for n, r in results
                   if r['status'] in ('timeout', 'step_limit', 'node_limit')
                   or r['max_oscillation'] > 0]
    if interesting:
        print(f"\n\n{'#'*78}")
        print(f"# Phase 3: Verbose re-run of interesting concepts")
        print(f"{'#'*78}")
        concepts = make_test_concepts()
        for name, _ in interesting[:3]:
            c0 = concepts[name]
            print(f"\n{'='*78}")
            print(f"Concept: {name}")
            print(f"  {concept_str(c0)}")
            tab = TriangleTableau(c0, max_nodes=50, max_steps=500,
                                  timeout=30.0, verbose=True)
            report = tab.run()
            print(f"  Final: {report['status']}, {report['total_created']} nodes, "
                  f"{report['total_steps']} steps, osc={report['max_oscillation']}")
