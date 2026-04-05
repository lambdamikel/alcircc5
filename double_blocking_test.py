#!/usr/bin/env python3
"""
Test double (pairwise) blocking for the ALCI_RCC5 triangle calculus.

Standard DL pairwise blocking: x is blocked by y ≺ x when
  L(x) = L(y)  AND  L(parent(x)) = L(parent(y))  AND  E(parent(x),x) = E(parent(y),y)

In ALCI, this is the standard blocking for inverse roles. The idea:
if two nodes were created by parents with the same label via the same
role, they should develop identically.

We test several variants to find the sweet spot between termination
and soundness:

  1. PairLL:    Double blocking with label matching only
  2. PairTri:   Double blocking + Tri(x)=Tri(y)
  3. PairFull:  Double blocking + Tri + TNbr (full Tri-neighborhood)
  4. SingleLL:  Single blocking with label only (baseline, always terminates)
  5. SingleTri: Single blocking with Tri (known non-terminating)
  6. FullTNbr:  Single blocking with Tri + TNbr (paper's criterion, non-terminating)
"""

import sys
import time
from collections import defaultdict
from triangle_calculus import (
    TriangleTableau, concept_str, closure, nnf_neg, safe_relations,
    comp, inv, NR_MINUS, DR, PO, PP, PPI,
    make_test_concepts
)


class PairwiseBlockingTableau(TriangleTableau):
    """Tableau with configurable pairwise (double) blocking.

    blocking_mode controls what is compared:
      'pair_ll'    — L(x)=L(y), L(px)=L(py), E(px,x)=E(py,y)
      'pair_tri'   — above + Tri(x)=Tri(y)
      'pair_full'  — above + Tri(x)=Tri(y) + TNbr(x)=TNbr(y)
      'single_ll'  — L(x)=L(y) only
      'single_tri' — L(x)=L(y) + Tri(x)=Tri(y)
      'full_tnbr'  — L(x)=L(y) + Tri(x)=Tri(y) + TNbr(x)=TNbr(y)
    """

    def __init__(self, c0, blocking_mode='pair_ll', **kwargs):
        super().__init__(c0, **kwargs)
        self.blocking_mode = blocking_mode
        self.creator = {}       # node_id -> (parent_id, role) or None for root
        self.creator['n0'] = None

    def apply_exists_rule(self, step):
        """Override to track creator info."""
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

            init_label = {filler, ('top',)}
            for c in self.labels[n]:
                if c[0] == 'forall' and c[1] == role:
                    init_label.add(c[2])

            self.nodes.append(new_name)
            self.labels[new_name] = init_label
            self.blocked_by[new_name] = None
            self.total_created += 1
            self.creator[new_name] = (n, role)  # track creator

            self.set_edge(n, new_name, role)

            existing = [m for m in self.nodes if m != new_name]
            assignments = self.find_edge_assignment(n, role, new_name, existing)

            if not assignments:
                if self.verbose:
                    print(f"  [{step}] Clash: no consistent edge assignment for "
                          f"{new_name} ({role}-succ of {n})")
                self.nodes.remove(new_name)
                del self.labels[new_name]
                del self.blocked_by[new_name]
                del self.creator[new_name]
                del self.edge[(n, new_name)]
                del self.edge[(new_name, n)]
                self.total_created -= 1
                self._bump_version()
                continue

            assignment = assignments[0]
            for e, r in assignment.items():
                if e != n:
                    self.set_edge(new_name, e, r)

            self.creation_history.append((step, new_name, n, role))

            if self.verbose:
                n_active = sum(1 for x in self.nodes if not self.is_blocked(x))
                print(f"  [{step}] Created {new_name} as {role}-succ of {n} "
                      f"({len(self.nodes)} nodes, {n_active} active)")

            return True

        return False

    def find_blocker(self, x):
        """Find blocker based on blocking_mode."""
        mode = self.blocking_mode

        if mode == 'single_ll':
            lx = self.label(x)
            for y in self.nodes:
                if y == x: break
                if self.is_blocked(y): continue
                if self.label(y) == lx:
                    return y
            return None

        elif mode == 'single_tri':
            lx = self.label(x)
            tx = self.compute_tri(x)
            for y in self.nodes:
                if y == x: break
                if self.is_blocked(y): continue
                if self.label(y) == lx and self.compute_tri(y) == tx:
                    return y
            return None

        elif mode == 'full_tnbr':
            sig_x = self.signature(x)
            for y in self.nodes:
                if y == x: break
                if self.is_blocked(y): continue
                if self.signature(y) == sig_x:
                    return y
            return None

        elif mode.startswith('pair_'):
            # Pairwise (double) blocking
            cx = self.creator.get(x)
            if cx is None:
                return None  # root cannot be blocked
            px, rx = cx  # parent of x, role from parent to x

            lx = self.label(x)
            lpx = self.label(px)

            for y in self.nodes:
                if y == x: break
                if self.is_blocked(y): continue

                cy = self.creator.get(y)
                if cy is None:
                    continue  # root can't be a blocker for pairwise
                py, ry = cy

                # Basic pairwise condition: same labels, same creator role
                if self.label(y) != lx:
                    continue
                if self.label(py) != lpx:
                    continue
                if ry != rx:
                    continue
                # Also check the edge: E(parent(x), x) = E(parent(y), y)
                # This should be rx = ry (already checked), but let's verify
                # the actual edge in case it differs
                if self.get_edge(px, x) != self.get_edge(py, y):
                    continue

                if mode == 'pair_ll':
                    return y
                elif mode == 'pair_tri':
                    if self.compute_tri(x) == self.compute_tri(y):
                        return y
                elif mode == 'pair_full':
                    if (self.compute_tri(x) == self.compute_tri(y) and
                        self.compute_tnbr(x) == self.compute_tnbr(y)):
                        return y

            return None

        raise ValueError(f"Unknown blocking mode: {mode}")


def run_experiment(concepts, modes, max_nodes=80, max_steps=300,
                   timeout=15.0, verbose=False):
    """Run all concepts under all blocking modes."""

    print(f"Double Blocking Experiment for ALCI_RCC5")
    print(f"Max nodes: {max_nodes}, max steps: {max_steps}, timeout: {timeout}s")
    print(f"{'='*90}")

    # Results: mode -> [(name, report)]
    all_results = {}

    for mode in modes:
        print(f"\n{'─'*90}")
        print(f"  Blocking mode: {mode}")
        print(f"{'─'*90}")

        results = []
        for name in sorted(concepts.keys()):
            c0 = concepts[name]
            t0 = time.time()
            tab = PairwiseBlockingTableau(
                c0, blocking_mode=mode,
                max_nodes=max_nodes, max_steps=max_steps,
                timeout=timeout, verbose=verbose)
            report = tab.run()
            t = time.time() - t0

            s = report['status']
            flag = ""
            if s in ('node_limit', 'step_limit', 'timeout'):
                flag = " NON-TERM"
            if report['max_oscillation'] > 0:
                flag += " OSC=" + str(report['max_oscillation'])

            print(f"    {name:25s} {s:12s} nodes={report['total_created']:4d} "
                  f"active={report['active_nodes']:3d} "
                  f"osc={report['max_oscillation']} {t:.1f}s{flag}")

            results.append((name, report))
        all_results[mode] = results

    # Summary comparison table
    print(f"\n\n{'='*90}")
    print("COMPARISON TABLE")
    print(f"{'='*90}")
    print(f"{'Concept':25s}", end="")
    for mode in modes:
        print(f" | {mode:12s}", end="")
    print()
    print("─" * (25 + 15 * len(modes)))

    concept_names = sorted(concepts.keys())
    for name in concept_names:
        print(f"{name:25s}", end="")
        for mode in modes:
            results = all_results[mode]
            report = next(r for n, r in results if n == name)
            s = report['status']
            osc = report['max_oscillation']
            if s == 'open':
                cell = f"✓ {report['total_created']:3d}n"
            elif s == 'clash':
                cell = f"✗ clash"
            else:
                cell = f"✗ {report['total_created']:3d}n"
            if osc > 0:
                cell += f" o{osc}"
            print(f" | {cell:12s}", end="")
        print()

    # Summary counts
    print(f"\n{'─'*90}")
    print(f"{'TOTALS':25s}", end="")
    for mode in modes:
        results = all_results[mode]
        term = sum(1 for _, r in results if r['status'] in ('open', 'clash'))
        non_term = sum(1 for _, r in results
                       if r['status'] in ('node_limit', 'step_limit', 'timeout'))
        osc = sum(1 for _, r in results if r['max_oscillation'] > 0)
        print(f" | T={term:2d} N={non_term:2d} O={osc}", end="")
    print()

    return all_results


def run_verbose_analysis(concepts, mode, concept_name,
                         max_nodes=30, max_steps=60, timeout=15.0):
    """Run one concept in verbose mode for detailed analysis."""
    c0 = concepts[concept_name]
    print(f"\n{'='*90}")
    print(f"Verbose: {concept_name} with {mode} blocking")
    print(f"Concept: {concept_str(c0)[:90]}")
    print(f"{'='*90}")

    tab = PairwiseBlockingTableau(
        c0, blocking_mode=mode,
        max_nodes=max_nodes, max_steps=max_steps,
        timeout=timeout, verbose=True)
    report = tab.run()

    print(f"\nStatus: {report['status']}")
    print(f"Nodes: {report['total_created']}, active: {report['active_nodes']}")
    print(f"Oscillation: {report['max_oscillation']}")
    print(f"Block events: {report['total_block_events']}")

    if report['max_oscillation'] > 0:
        print(f"\n*** OSCILLATION DETECTED ***")
        print(f"Unblock counts: {report['node_unblock_counts']}")
        for ev in report['block_events'][:30]:
            step, node, event, whom = ev
            print(f"  step={step}: {node} {event} (by {whom})")

    # Show node structure
    print(f"\nNode structure:")
    for n in tab.nodes[:15]:
        creator = tab.creator.get(n)
        cr_str = f"root" if creator is None else f"{creator[1]}-succ of {creator[0]}"
        bl = "BLOCKED" if tab.is_blocked(n) else "active"
        tri_size = len(tab.compute_tri(n))
        print(f"  {n:5s}: {cr_str:20s} |LL|={len(tab.labels[n])} "
              f"|Tri|={tri_size:2d} {bl}")

    return report


if __name__ == '__main__':
    concepts = make_test_concepts()

    # Select most interesting concepts for testing
    key_concepts = {}
    for name in ['PP+DR', 'PP+PO', 'PP+DR+PO', 'PO-incoherent',
                  'PO-incoh-typed', 'alt-AB-PP', 'three-role-cross',
                  'DR-back-PO', 'forall-exists', 'triangle-forming',
                  'deep-exists', 'wide-branching', 'backward-prop',
                  'two-PP-succ']:
        if name in concepts:
            key_concepts[name] = concepts[name]

    modes = [
        'single_ll',    # baseline: type-equality only
        'pair_ll',       # STANDARD DOUBLE BLOCKING
        'pair_tri',      # double + Tri
        'single_tri',    # single + Tri (for comparison)
        'pair_full',     # double + Tri + TNbr
        'full_tnbr',     # single + Tri + TNbr (paper's criterion)
    ]

    max_nodes = int(sys.argv[1]) if len(sys.argv) > 1 else 80
    timeout = float(sys.argv[2]) if len(sys.argv) > 2 else 15.0

    all_results = run_experiment(
        key_concepts, modes,
        max_nodes=max_nodes, max_steps=300, timeout=timeout)

    # Verbose re-run of anything interesting under pair_ll
    pair_ll_results = all_results.get('pair_ll', [])

    # Show verbose for PP+DR under pair_ll (the simplest non-term case)
    run_verbose_analysis(key_concepts, 'pair_ll', 'PP+DR',
                         max_nodes=30, max_steps=60)

    # If pair_ll shows oscillation, show verbose for that too
    osc_cases = [(n, r) for n, r in pair_ll_results
                 if r['max_oscillation'] > 0]
    if osc_cases:
        print(f"\n*** Oscillation found under pair_ll! ***")
        for name, _ in osc_cases[:2]:
            run_verbose_analysis(key_concepts, 'pair_ll', name,
                                 max_nodes=40, max_steps=80)
    else:
        # Check pair_ll non-termination cases
        non_term = [(n, r) for n, r in pair_ll_results
                    if r['status'] in ('node_limit', 'step_limit', 'timeout')]
        if non_term:
            print(f"\n*** Non-termination under pair_ll: {len(non_term)} cases ***")
            for name, _ in non_term[:2]:
                run_verbose_analysis(key_concepts, 'pair_ll', name,
                                     max_nodes=40, max_steps=80)
        else:
            print(f"\n*** pair_ll terminates on all concepts! ***")
            # Show a verbose termination trace
            run_verbose_analysis(key_concepts, 'pair_ll', 'PP+DR',
                                 max_nodes=30, max_steps=60)
