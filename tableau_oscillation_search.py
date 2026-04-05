#!/usr/bin/env python3
"""
Search for concrete blocking/unblocking oscillation in the
Tri-neighborhood tableau for ALCI_RCC5.

Implements a simplified but faithful version of the tableau expansion:
  - Concepts in NNF with ∃R.C, ∀R.C, ⊓, ⊔, atoms, negated atoms
  - Exists-rule: create successor with edges to ALL existing nodes
  - Edge assignment: try all composition-consistent assignments
  - Tri(x) and TNbr(x) computation
  - Blocking: LL(x)=LL(y) ∧ Tri(x)=Tri(y) ∧ TNbr(x)=TNbr(y)
  - Track blocking/unblocking events

We search over a battery of small concepts designed to trigger oscillation.
"""

import itertools
import sys
import time
from collections import defaultdict
from copy import deepcopy

# ── RCC5 machinery ──────────────────────────────────────────────────

DR, PO, PP, PPI = 'DR', 'PO', 'PP', 'PPI'
RELS = [DR, PO, PP, PPI]
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
#   ('atom', 'A')          -- atomic concept A
#   ('neg', 'A')           -- ¬A
#   ('and', c1, c2)        -- c1 ⊓ c2
#   ('or', c1, c2)         -- c1 ⊔ c2
#   ('exists', 'PP', c)    -- ∃PP.C
#   ('forall', 'PP', c)    -- ∀PP.C
#   ('top',)               -- ⊤

def concept_str(c):
    if c[0] == 'atom': return c[1]
    if c[0] == 'neg': return f'¬{c[1]}'
    if c[0] == 'top': return '⊤'
    if c[0] == 'and': return f'({concept_str(c[1])} ⊓ {concept_str(c[2])})'
    if c[0] == 'or': return f'({concept_str(c[1])} ⊔ {concept_str(c[2])})'
    if c[0] == 'exists': return f'∃{c[1]}.{concept_str(c[2])}'
    if c[0] == 'forall': return f'∀{c[1]}.{concept_str(c[2])}'
    return str(c)

def closure(c):
    """Compute cl(C₀): all subconcepts and their NNF negations."""
    subs = set()
    def collect(x):
        subs.add(x)
        if x[0] in ('and', 'or'):
            collect(x[1]); collect(x[2])
        elif x[0] in ('exists', 'forall'):
            collect(x[2])
    collect(c)
    result = set()
    for s in subs:
        result.add(s)
        result.add(nnf_neg(s))
    result.add(('top',))
    return frozenset(result)

def nnf_neg(c):
    if c[0] == 'atom': return ('neg', c[1])
    if c[0] == 'neg': return ('atom', c[1])
    if c[0] == 'top': return ('bot',)
    if c[0] == 'bot': return ('top',)
    if c[0] == 'and': return ('or', nnf_neg(c[1]), nnf_neg(c[2]))
    if c[0] == 'or': return ('and', nnf_neg(c[1]), nnf_neg(c[2]))
    if c[0] == 'exists': return ('forall', c[1], nnf_neg(c[2]))
    if c[0] == 'forall': return ('exists', c[1], nnf_neg(c[2]))
    return c


# ── Tableau state ───────────────────────────────────────────────────

class TableauState:
    def __init__(self, c0, max_nodes=200, max_steps=5000, verbose=False, timeout=10.0):
        self.c0 = c0
        self.cl = closure(c0)
        self.max_nodes = max_nodes
        self.max_steps = max_steps
        self.verbose = verbose
        self.timeout = timeout

        # Nodes
        self.nodes = []
        self.labels = {}       # node -> set of concepts
        self.edges = {}        # (n1, n2) -> relation (for n1 < n2 by creation order)
        self.rel = {}          # (n1, n2) -> relation (for any pair, including inverses)
        self.blocked = {}      # node -> blocker node or None
        self.creation_order = {}  # node -> int

        # Tracking
        self.block_events = []   # list of (step, node, 'blocked'/'unblocked', by_whom)
        self.node_block_count = defaultdict(int)   # node -> number of blocking/unblocking transitions
        self.node_unblock_count = defaultdict(int)
        self.total_steps = 0
        self.total_nodes_created = 0
        self.max_oscillation = 0  # max unblock count for any single node
        self.parent = {}  # node -> parent node

    def get_rel(self, a, b):
        if a == b:
            return 'EQ'
        return self.rel.get((a, b))

    def set_rel(self, a, b, r):
        self.rel[(a, b)] = r
        self.rel[(b, a)] = inv(r)

    def label(self, n):
        return frozenset(self.labels[n])

    # ── Tri and TNbr computation ──────────────────────────────────

    def compute_tri(self, x):
        """Tri(x) = set of (LL(x), E(x,b), LL(b), E(b,c), LL(c), E(x,c))
        for all distinct b,c with {x,b,c} having 3 distinct elements."""
        tri = set()
        lx = self.label(x)
        # Pre-filter: only nodes with edges to x
        neighbors = []
        for n in self.nodes:
            if n != x and self.get_rel(x, n) is not None:
                neighbors.append((n, self.get_rel(x, n), self.label(n)))
        for i, (b, rxb, lb) in enumerate(neighbors):
            for j in range(i+1, len(neighbors)):
                c, rxc, lc = neighbors[j]
                rbc = self.get_rel(b, c)
                if rbc is None:
                    continue
                tri.add((lx, rxb, lb, rbc, lc, rxc))
                tri.add((lx, rxc, lc, inv(rbc), lb, rxb))
        return frozenset(tri)

    def compute_tnbr(self, x):
        """TNbr(x) = for each (R, τ), the set of Tri-values among
        x's R-neighbors of type τ."""
        tnbr = {}
        for n in self.nodes:
            if n == x:
                continue
            r = self.get_rel(x, n)
            if r is None:
                continue
            tau = self.label(n)
            key = (r, tau)
            if key not in tnbr:
                tnbr[key] = set()
            tri_n = self.compute_tri(n)
            tnbr[key].add(tri_n)
        # Freeze
        return frozenset((k, frozenset(v)) for k, v in tnbr.items())

    def signature(self, x):
        return (self.label(x), self.compute_tri(x), self.compute_tnbr(x))

    # ── Blocking ──────────────────────────────────────────────────

    def find_blocker(self, x):
        """Find the earliest non-blocked node y < x with same signature."""
        sig_x = self.signature(x)
        for y in self.nodes:
            if y == x:
                break  # only look at earlier nodes
            if self.blocked.get(y) is not None:
                continue
            if self.signature(y) == sig_x:
                return y
        return None

    def update_blocking(self, step):
        """Recompute blocking for all nodes. Track events."""
        changes = False
        for x in self.nodes:
            old_blocker = self.blocked.get(x)
            new_blocker = self.find_blocker(x)
            if old_blocker != new_blocker:
                changes = True
                self.blocked[x] = new_blocker
                if new_blocker is not None and old_blocker is None:
                    self.node_block_count[x] += 1
                    self.block_events.append((step, x, 'blocked', new_blocker))
                    if self.verbose:
                        print(f"  Step {step}: {x} BLOCKED by {new_blocker}")
                elif new_blocker is None and old_blocker is not None:
                    self.node_unblock_count[x] += 1
                    self.max_oscillation = max(self.max_oscillation,
                                               self.node_unblock_count[x])
                    self.block_events.append((step, x, 'unblocked', old_blocker))
                    if self.verbose:
                        print(f"  Step {step}: {x} UNBLOCKED (was by {old_blocker})")
                elif new_blocker is not None and old_blocker is not None:
                    # Blocker changed
                    self.block_events.append((step, x, 'reblocker', new_blocker))
        return changes

    # ── Concept expansion ─────────────────────────────────────────

    def expand_label(self, n):
        """Apply ⊓ and ⊔ rules to expand the label. Returns True if changed."""
        changed = False
        label = self.labels[n]
        to_add = set()
        for c in list(label):
            if c[0] == 'and':
                if c[1] not in label:
                    to_add.add(c[1])
                if c[2] not in label:
                    to_add.add(c[2])
            # For ⊔: choose first disjunct not already contradicted
            if c[0] == 'or':
                if c[1] not in label and c[2] not in label:
                    # Heuristic: try first disjunct
                    if nnf_neg(c[1]) not in label:
                        to_add.add(c[1])
                    elif nnf_neg(c[2]) not in label:
                        to_add.add(c[2])
                    else:
                        to_add.add(c[1])  # clash will be detected
        if to_add:
            label.update(to_add)
            changed = True
        # Add ⊤
        if ('top',) not in label:
            label.add(('top',))
            changed = True
        return changed

    def get_unsatisfied_exists(self, n):
        """Return list of (role, filler_concept) for unsatisfied ∃R.C in label."""
        demands = []
        for c in self.labels[n]:
            if c[0] == 'exists':
                role, filler = c[1], c[2]
                # Check if already satisfied
                satisfied = False
                for m in self.nodes:
                    if m == n:
                        continue
                    r = self.get_rel(n, m)
                    if r == role and self.blocked.get(m) is None:
                        if self.concept_in_label(m, filler):
                            satisfied = True
                            break
                if not satisfied:
                    demands.append((role, filler))
        return demands

    def concept_in_label(self, n, c):
        return c in self.labels[n]

    def get_forall_constraints(self, n, role):
        """Get all ∀R.C where R=role from n's label."""
        constraints = []
        for c in self.labels[n]:
            if c[0] == 'forall' and c[1] == role:
                constraints.append(c[2])
            # Universal role R* = all roles
            if c[0] == 'forall' and c[1] == '*':
                constraints.append(c[2])
        return constraints

    def find_consistent_edge_assignments(self, new_node, existing_nodes):
        """Find all composition-consistent relation assignments from new_node
        to all existing nodes."""
        if not existing_nodes:
            return [{}]

        # For each existing node, compute the domain of possible relations
        domains = {}
        for e in existing_nodes:
            domains[e] = set(RELS)

        # Apply composition constraints from existing pairwise relations
        # For each pair (e1, e2) of existing nodes:
        #   rel(new, e1) must be in comp(rel(new, e2), rel(e2, e1))
        #   rel(new, e2) must be in comp(rel(new, e1), rel(e1, e2))
        changed = True
        while changed:
            changed = False
            for e1 in existing_nodes:
                for e2 in existing_nodes:
                    if e1 == e2:
                        continue
                    r12 = self.get_rel(e1, e2)
                    if r12 is None:
                        continue
                    # new-e2 ∈ comp(new-e1, e1-e2)
                    for r_ne1 in list(domains[e1]):
                        allowed = comp(r_ne1, r12)
                        for r_ne2 in list(domains[e2]):
                            if r_ne2 not in allowed:
                                pass  # constraint on combination, not individual
                    # Prune: for each value in domains[e1], check if there exists
                    # a compatible value in domains[e2]
                    new_d1 = set()
                    for r1 in domains[e1]:
                        # Check: exists r2 in domains[e2] s.t. r2 in comp(r1, r12)?
                        allowed = comp(r1, r12)
                        if allowed & domains[e2]:
                            new_d1.add(r1)
                    if new_d1 != domains[e1]:
                        domains[e1] = new_d1
                        changed = True
                    if not domains[e1]:
                        return []

        # Enumerate valid assignments (with pruning, up to limit)
        result = []
        nodes_list = list(existing_nodes)

        def backtrack(idx, assignment):
            if len(result) >= 10:  # limit branching
                return
            if idx == len(nodes_list):
                result.append(dict(assignment))
                return
            e = nodes_list[idx]
            for r in domains[e]:
                # Check consistency with already assigned
                ok = True
                for e2, r2 in assignment.items():
                    r_e2_e = self.get_rel(e2, e)
                    if r_e2_e is not None:
                        if r not in comp(r2, self.get_rel(e2, e)):
                            ok = False
                            break
                        if r2 not in comp(r, self.get_rel(e, e2)):
                            ok = False
                            break
                if ok:
                    assignment[e] = r
                    backtrack(idx + 1, assignment)
                    del assignment[e]

        backtrack(0, {})
        return result

    # ── Main expansion loop ───────────────────────────────────────

    def create_node(self, name, initial_label, parent=None):
        self.nodes.append(name)
        self.labels[name] = set(initial_label)
        self.blocked[name] = None
        self.creation_order[name] = len(self.nodes) - 1
        self.total_nodes_created += 1
        if parent is not None:
            self.parent[name] = parent

    def run(self):
        """Run the tableau. Returns a report dict."""
        # Create root
        self.create_node('n0', {self.c0})
        self.start_time = time.time()

        step = 0
        while step < self.max_steps:
            if time.time() - self.start_time > self.timeout:
                return self.report("timeout")
            step += 1
            self.total_steps = step
            progress = False

            # 1. Expand all labels
            for n in self.nodes:
                if self.blocked.get(n) is not None:
                    continue
                if self.expand_label(n):
                    progress = True

            # 2. Apply ∀-rule: propagate forall constraints
            for n in self.nodes:
                if self.blocked.get(n) is not None:
                    continue
                for m in self.nodes:
                    if m == n:
                        continue
                    r = self.get_rel(n, m)
                    if r is None:
                        continue
                    for filler in self.get_forall_constraints(n, r):
                        if filler not in self.labels[m]:
                            self.labels[m].add(filler)
                            progress = True
                    # Also propagate via universal role
                    for filler in self.get_forall_constraints(n, '*'):
                        if filler not in self.labels[m]:
                            self.labels[m].add(filler)
                            progress = True

            # 3. Update blocking
            self.update_blocking(step)

            # 4. Apply ∃-rule for non-blocked nodes
            exists_fired = False
            for n in list(self.nodes):
                if self.blocked.get(n) is not None:
                    continue
                demands = self.get_unsatisfied_exists(n)
                if not demands:
                    continue

                # Fire first unsatisfied demand
                role, filler = demands[0]
                if len(self.nodes) >= self.max_nodes:
                    if self.verbose:
                        print(f"  Step {step}: node limit reached ({self.max_nodes})")
                    return self.report("node_limit")

                new_name = f'n{self.total_nodes_created}'
                existing = [m for m in self.nodes if m != new_name]

                # Initial label for new node
                init_label = {filler, ('top',)}
                # Add forall propagations from parent
                for fc in self.get_forall_constraints(n, role):
                    init_label.add(fc)

                # Find edge assignments
                assignments = self.find_consistent_edge_assignments_for_new(
                    n, role, new_name, existing)
                if not assignments:
                    if self.verbose:
                        print(f"  Step {step}: clash creating {role}-successor of {n}")
                    continue

                # Use first valid assignment
                assignment = assignments[0]
                self.create_node(new_name, init_label, parent=n)
                for e, r in assignment.items():
                    self.set_rel(new_name, e, r)

                exists_fired = True
                progress = True

                if self.verbose:
                    print(f"  Step {step}: created {new_name} as {role}-succ of {n} "
                          f"(total: {len(self.nodes)} nodes)")

                # Update blocking after creation
                self.update_blocking(step)
                break  # one creation per step to track events

            if not progress and not exists_fired:
                return self.report("complete")

        return self.report("step_limit")

    def find_consistent_edge_assignments_for_new(self, parent, role, new_name, existing):
        """Find edge assignments for a new node being created as role-successor of parent."""
        # Start with the parent edge fixed
        domains = {}
        for e in existing:
            if e == parent:
                domains[e] = {inv(role)}  # new --inv(role)--> parent means parent --role--> new
                # Actually: parent --role--> new means rel(parent, new) = role
                # So rel(new, parent) = inv(role)
            else:
                domains[e] = set(RELS)

        # Arc consistency
        changed = True
        iterations = 0
        while changed and iterations < 100:
            changed = False
            iterations += 1
            for e1 in existing:
                for e2 in existing:
                    if e1 == e2:
                        continue
                    r12 = self.get_rel(e1, e2)
                    if r12 is None:
                        continue
                    # rel(new, e2) must be in comp(rel(new, e1), rel(e1, e2))
                    new_d2 = set()
                    for r1 in domains[e1]:
                        allowed = comp(r1, r12)
                        new_d2 |= (allowed & domains[e2])
                    if new_d2 != domains[e2]:
                        domains[e2] = new_d2
                        changed = True
                    # Reverse: rel(new, e1) must be compatible
                    r21 = self.get_rel(e2, e1)
                    if r21 is None:
                        continue
                    new_d1 = set()
                    for r2 in domains[e2]:
                        allowed = comp(r2, r21)
                        new_d1 |= (allowed & domains[e1])
                    if new_d1 != domains[e1]:
                        domains[e1] = new_d1
                        changed = True
                    if not domains[e1] or not domains[e2]:
                        return []

        # Enumerate (limited)
        result = []
        nodes_list = list(existing)

        def backtrack(idx, assignment):
            if len(result) >= 5:
                return
            if idx == len(nodes_list):
                result.append(dict(assignment))
                return
            e = nodes_list[idx]
            for r in sorted(domains[e], key=lambda x: RELS.index(x)):
                ok = True
                for e2, r2 in assignment.items():
                    re2e = self.get_rel(e2, e)
                    if re2e is not None:
                        if r not in comp(r2, re2e):
                            ok = False
                            break
                        ree2 = self.get_rel(e, e2)
                        if r2 not in comp(r, ree2):
                            ok = False
                            break
                if ok:
                    assignment[e] = r
                    backtrack(idx + 1, assignment)
                    del assignment[e]

        backtrack(0, {})
        return result

    def report(self, status):
        return {
            'status': status,
            'total_nodes': len(self.nodes),
            'total_steps': self.total_steps,
            'total_created': self.total_nodes_created,
            'max_oscillation': self.max_oscillation,
            'total_block_events': len(self.block_events),
            'block_events': self.block_events,
            'node_unblock_counts': dict(self.node_unblock_count),
        }


# ── Test concepts ──────────────────────────────────────────────────

def make_concepts():
    """Generate a battery of concepts designed to trigger oscillation."""
    A = ('atom', 'A')
    B = ('atom', 'B')
    C = ('atom', 'C')
    nA = ('neg', 'A')
    nB = ('neg', 'B')
    nC = ('neg', 'C')
    top = ('top',)

    concepts = {}

    # 1. Basic infinite PP-chain with DR witnesses
    concepts['PP-chain+DR'] = (
        'and',
        ('exists', 'PP', top),
        ('forall', '*', ('and',
            ('exists', 'PP', top),
            ('exists', 'DR', top)
        ))
    )

    # 2. PP-chain with typed DR witnesses
    concepts['PP-chain+DR.B'] = (
        'and',
        ('and', A, ('exists', 'PP', A)),
        ('forall', '*', ('and',
            ('and', ('exists', 'PP', A), ('exists', 'DR', B)),
            ('forall', 'PP', A)
        ))
    )

    # 3. Alternating types on PP-chain with cross-DR
    concepts['alt-PP+DR'] = (
        'and',
        ('and', A, ('exists', 'PP', ('and', B, ('exists', 'DR', A)))),
        ('forall', '*', ('and',
            ('or',
                ('and', A, ('exists', 'PP', ('and', B, ('exists', 'DR', A)))),
                ('and', B, ('exists', 'PP', ('and', A, ('exists', 'DR', B))))
            ),
            ('forall', 'PP', ('exists', 'PP', top))
        ))
    )

    # 4. PP-chain + PO witnesses (PO is hardest for composition)
    concepts['PP-chain+PO'] = (
        'and',
        ('exists', 'PP', top),
        ('forall', '*', ('and',
            ('exists', 'PP', top),
            ('exists', 'PO', top)
        ))
    )

    # 5. PP-chain with PO and DR witnesses
    concepts['PP+PO+DR'] = (
        'and',
        ('and', A, ('exists', 'PP', top)),
        ('forall', '*', ('and',
            ('exists', 'PP', top),
            ('and', ('exists', 'PO', B), ('exists', 'DR', C))
        ))
    )

    # 6. Nested exists: ∃PP.(∃DR.(∃PP.⊤))
    concepts['nested-exists'] = (
        'and',
        ('exists', 'PP', ('exists', 'DR', ('exists', 'PP', top))),
        ('forall', '*', ('exists', 'PP', ('exists', 'DR', ('exists', 'PP', top))))
    )

    # 7. Two PP-successors with different witnesses
    concepts['two-PP-succ'] = (
        'and',
        ('and',
            ('exists', 'PP', ('and', A, ('exists', 'DR', B))),
            ('exists', 'PP', ('and', B, ('exists', 'DR', A)))
        ),
        ('forall', '*', ('and',
            ('exists', 'PP', top),
            ('exists', 'DR', top)
        ))
    )

    # 8. The PO-incoherent counterexample
    concepts['PO-incoherent'] = (
        'and',
        ('and', A, ('exists', 'PP', ('and', B, ('exists', 'PO', C)))),
        ('forall', 'PP', ('and',
            ('exists', 'PP', top),
            ('exists', 'PO', C)
        ))
    )

    # 9. Deep nesting: ∃PP.∃PP.∃DR.∃PP.⊤ with global propagation
    concepts['deep-nesting'] = (
        'and',
        ('exists', 'PP', ('exists', 'PP', ('exists', 'DR',
            ('exists', 'PP', top)))),
        ('forall', '*', ('and',
            ('exists', 'PP', top),
            ('exists', 'DR', top)
        ))
    )

    # 10. Mutual witnesses: A needs DR-to-B, B needs DR-to-A
    concepts['mutual-DR'] = (
        'and',
        A,
        ('and',
            ('exists', 'PP', ('and', B,
                ('and',
                    ('exists', 'DR', A),
                    ('exists', 'PP', ('and', A,
                        ('exists', 'DR', B)
                    ))
                )
            )),
            ('forall', '*', ('exists', 'PP', top))
        )
    )

    # 11. Three-role concept: PP + PO + DR all demanded
    concepts['three-role'] = (
        'and',
        ('and', A,
            ('and',
                ('exists', 'PP', B),
                ('and', ('exists', 'PO', C), ('exists', 'DR', A))
            )
        ),
        ('forall', '*', ('and',
            ('exists', 'PP', top),
            ('and', ('exists', 'PO', top), ('exists', 'DR', top))
        ))
    )

    # 12. Forall-DR propagation creating label growth
    concepts['forall-DR-prop'] = (
        'and',
        ('and', A, ('exists', 'PP', top)),
        ('forall', '*', ('and',
            ('exists', 'PP', top),
            ('and',
                ('exists', 'DR', B),
                ('forall', 'DR', ('exists', 'PO', A))
            )
        ))
    )

    # 13. Chain with backward forall propagation
    concepts['backward-forall'] = (
        'and',
        ('and', A, ('exists', 'PP', ('and', B, ('forall', 'PPI', ('exists', 'DR', C))))),
        ('forall', '*', ('and',
            ('exists', 'PP', top),
            ('exists', 'DR', top)
        ))
    )

    # 14. Simple oscillation candidate: concept that creates
    #     many witnesses which form varying triangles
    concepts['many-witnesses'] = (
        'and',
        ('and', A,
            ('and',
                ('exists', 'PP', A),
                ('and',
                    ('exists', 'DR', B),
                    ('exists', 'PO', C)
                )
            )
        ),
        ('forall', 'PP', ('and',
            ('exists', 'PP', A),
            ('and',
                ('exists', 'DR', B),
                ('exists', 'PO', C)
            )
        ))
    )

    return concepts


# ── Main ───────────────────────────────────────────────────────────

def run_search(verbose_threshold=1, max_nodes=100, max_steps=2000):
    concepts = make_concepts()

    print(f"Tableau oscillation search")
    print(f"Testing {len(concepts)} concepts (max {max_nodes} nodes, {max_steps} steps)")
    print(f"{'='*72}")

    results = []

    for name, c0 in sorted(concepts.items()):
        print(f"\n{'─'*72}")
        print(f"Concept: {name}")
        print(f"  {concept_str(c0)}")

        verbose = False
        tab = TableauState(c0, max_nodes=max_nodes, max_steps=max_steps,
                           verbose=verbose, timeout=15.0)
        report = tab.run()

        osc = report['max_oscillation']
        flag = " *** OSCILLATION ***" if osc >= verbose_threshold else ""
        print(f"  Status: {report['status']}")
        print(f"  Nodes created: {report['total_created']}, "
              f"final: {report['total_nodes']}, "
              f"steps: {report['total_steps']}")
        print(f"  Block events: {report['total_block_events']}, "
              f"max unblocks per node: {osc}{flag}")

        if osc >= verbose_threshold and report['block_events']:
            print(f"  Unblock counts: {report['node_unblock_counts']}")
            print(f"  Block event log (first 20):")
            for ev in report['block_events'][:20]:
                step, node, event, whom = ev
                print(f"    step={step}: {node} {event} (by {whom})")

        results.append((name, osc, report))

    # Summary
    print(f"\n{'='*72}")
    print("SUMMARY (sorted by max oscillation):")
    print(f"{'─'*72}")
    results.sort(key=lambda x: -x[1])
    for name, osc, report in results:
        flag = " <<<" if osc > 0 else ""
        print(f"  {name:30s}  osc={osc:3d}  nodes={report['total_created']:4d}  "
              f"events={report['total_block_events']:4d}  "
              f"status={report['status']}{flag}")

    max_osc = max(r[1] for r in results)
    if max_osc > 0:
        print(f"\n*** Found oscillation! Max unblocks per node: {max_osc}")
        best = [r for r in results if r[1] == max_osc][0]
        print(f"*** Concept: {best[0]}")
        print(f"\nRe-running with verbose output...")
        tab = TableauState(concepts[best[0]], max_nodes=max_nodes,
                           max_steps=max_steps, verbose=True)
        tab.run()
    else:
        print(f"\nNo oscillation detected in any concept.")
        print("All blocking was monotone (once blocked, stayed blocked).")

    return results


if __name__ == '__main__':
    max_nodes = int(sys.argv[1]) if len(sys.argv) > 1 else 80
    max_steps = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    run_search(max_nodes=max_nodes, max_steps=max_steps)
