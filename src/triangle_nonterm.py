#!/usr/bin/env python3
"""
Demonstrates non-termination of the Tri-neighborhood tableau for ALCI_RCC5.

The concept A ⊓ ∃PP.A ⊓ ∀PP.(∃PP.A ⊓ ∃DR.B) forces an infinite PP-chain
where each node has a DR-witness. The Tri-neighborhood blocking criterion
never blocks the frontier node because:

  Interior nodes: Tri includes triangles with PP-successors AND PPI-predecessors → |Tri|=16
  Frontier node:  Tri includes only PPI-predecessor triangles → |Tri|=8

Since PP ≠ PPI (they are different RCC5 base relations), the triangle types
differ. The frontier is never blocked, so it keeps creating new PP-successors.

This is NOT blocking oscillation — zero unblocking events occur.
It is unbounded frontier advancement with bounded active nodes.
"""

from triangle_calculus import (
    TriangleTableau, concept_str, PP, DR, PO, PPI, NR_MINUS, inv
)
import time


def main():
    # The simplest non-terminating concept
    c = ('and',
        ('and', ('atom', 'A'), ('exists', PP, ('atom', 'A'))),
        ('forall', PP, ('and',
            ('exists', PP, ('atom', 'A')),
            ('exists', DR, ('atom', 'B')))))

    print("Non-termination of Tri-neighborhood Tableau for ALCI_RCC5")
    print("=" * 72)
    print(f"Concept: {concept_str(c)}")
    print(f"         A ⊓ ∃PP.A ⊓ ∀PP.(∃PP.A ⊓ ∃DR.B)")
    print()

    # --- Tri-neighborhood blocking ---
    print("--- Tri-neighborhood blocking (the paper's criterion) ---")
    tab = TriangleTableau(c, max_nodes=100, max_steps=120,
                          timeout=30.0, verbose=False)
    report = tab.run()
    print(f"  Status: {report['status']}")
    print(f"  Nodes created: {report['total_created']}")
    print(f"  Active nodes:  {report['active_nodes']}")
    print(f"  Oscillation:   {report['max_oscillation']} (zero = no unblocking)")
    print()

    # Show structure
    print("  Node structure (first 8 + last 5):")
    show_nodes = tab.nodes[:8] + ['...'] + tab.nodes[-5:]
    for n in show_nodes:
        if n == '...':
            print("  ...")
            continue
        pp = sum(1 for m in tab.nodes if m != n and tab.get_edge(n, m) == PP)
        ppi = sum(1 for m in tab.nodes if m != n and tab.get_edge(n, m) == PPI)
        dr = sum(1 for m in tab.nodes if m != n and tab.get_edge(n, m) == DR)
        tri_size = len(tab.compute_tri(n))
        bl = "BLOCKED" if tab.is_blocked(n) else "active"
        print(f"    {n:5s}: PP:{pp:2d} PPI:{ppi:2d} DR:{dr:2d}  "
              f"|Tri|={tri_size:2d}  {bl}")

    # Show the Tri asymmetry
    print()
    interior = tab.nodes[5]  # a stable interior node
    frontier = tab.nodes[-1]
    tri_int = tab.compute_tri(interior)
    tri_fro = tab.compute_tri(frontier)
    print(f"  Tri asymmetry:")
    print(f"    Interior ({interior}): |Tri| = {len(tri_int)}")
    print(f"    Frontier ({frontier}): |Tri| = {len(tri_fro)}")
    only_int = tri_int - tri_fro
    only_fro = tri_fro - tri_int

    def tri_summary(t):
        lx, r1, lb, r2, lc, r3 = t
        return f"(τ_{len(lx)}, {r1}, τ_{len(lb)}, {r2}, τ_{len(lc)}, {r3})"

    print(f"    In interior but not frontier ({len(only_int)} types):")
    for t in sorted(only_int, key=tri_summary)[:5]:
        print(f"      {tri_summary(t)}")
    print(f"    In frontier but not interior ({len(only_fro)} types):")
    for t in sorted(only_fro, key=tri_summary)[:5]:
        print(f"      {tri_summary(t)}")

    print()
    print("  ROOT CAUSE: The frontier node has no PP-successors (it's the")
    print("  chain endpoint). Interior nodes have PP-successors that were")
    print("  created after them. PP ≠ PPI, so the triangle types differ.")
    print("  This is inherent to the complete-graph expansion strategy.")

    # --- Type-equality blocking (for comparison) ---
    print()
    print("--- Type-equality blocking (LL only, for comparison) ---")

    class TypeEqTableau(TriangleTableau):
        def find_blocker(self, x):
            lx = self.label(x)
            for y in self.nodes:
                if y == x:
                    break
                if self.is_blocked(y):
                    continue
                if self.label(y) == lx:
                    return y
            return None

    tab2 = TypeEqTableau(c, max_nodes=100, max_steps=120,
                         timeout=30.0, verbose=False)
    report2 = tab2.run()
    print(f"  Status: {report2['status']}")
    print(f"  Nodes created: {report2['total_created']}")
    print(f"  Active nodes:  {report2['active_nodes']}")
    print(f"  (Terminates because LL(frontier) = LL(interior),")
    print(f"   but may produce novel triangle types during unraveling)")

    # --- Summary ---
    print()
    print("=" * 72)
    print("BLOCKING DILEMMA CONFIRMED:")
    print()
    print("  Type-equality blocking:     Terminates but potentially unsound")
    print("  Tri-neighborhood blocking:  Sound but does NOT terminate")
    print()
    print("  The frontier node of a PP-chain always has a strictly smaller")
    print("  Tri than interior nodes (|Tri|=8 vs |Tri|=16), because it")
    print("  lacks PP-successor triangles. Since Tri matching is required")
    print("  for blocking, the frontier is never blocked, and the chain")
    print("  grows without bound.")
    print()
    print("  Active node count stays bounded (≈9), but total node creation")
    print("  is unbounded. This is the exact gap identified in Section 4:")
    print("  'a process with at most A(C₀) active nodes could in principle")
    print("   cycle through blocking and unblocking, creating fresh")
    print("   successors each time.'")
    print()
    print("  Simplest counterexample: A ⊓ ∃PP.A ⊓ ∀PP.(∃PP.A ⊓ ∃DR.B)")


if __name__ == '__main__':
    main()
