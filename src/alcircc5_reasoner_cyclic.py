"""Cycle-aware variant of the ALCI_RCC5 quasimodel reasoner.

Thin wrapper around ``alcircc5_reasoner.check_satisfiability`` that enables
the cycle-close case (``cycle_close=True``). The baseline reasoner in
``alcircc5_reasoner.py`` has a known incompleteness on cyclic-via-symmetric-role
SAT concepts such as the PO-loop

    C ⊓ ∃PO.∃PO.C ⊓ ∀PO.¬C ⊓ ∀DR.¬C ⊓ ∀PP.¬C ⊓ ∀PPI.¬C

which is satisfiable via the 2-element model {d, a} with C = {d} and
ρ(d, a) = PO (the chain d →PO→ a →PO→ d closes back to d itself under
strong-EQ identity). The baseline's role-path compatibility check rejects
such witnesses because it requires the grandchild w to be distinct from
the root g.

This variant admits the cycle-close case w = g, provided
(inv(S), inv(R)) ∈ EQ_ADMITTING_PAIRS (equivalently S = inv(R)), which is
the RCC5-algebraic condition for the cycle to close through EQ at g.

The baseline file is kept unchanged in its default behaviour so that its
cross-validation performance is preserved; use this file when completeness
on cyclic SAT concepts matters more than speed.
"""

from alcircc5_reasoner import (
    check_satisfiability as _baseline_check,
    Concept, AtomicConcept, NegAtomicConcept, Top, Bottom,
    And, Or, Exists, ForAll,
    DR, PO, PP, PPI, INV, COMP, EQ_ADMITTING_PAIRS,
    closure, is_hintikka_type, enumerate_types, compute_safe,
)


def check_satisfiability(C0, verbose=False):
    """Cycle-aware concept satisfiability check.

    Equivalent to calling the baseline reasoner with ``cycle_close=True``.
    Slower in corner cases but complete on cyclic-via-symmetric-role SAT
    concepts that the baseline rejects.
    """
    return _baseline_check(C0, verbose=verbose, cycle_close=True)


if __name__ == '__main__':
    import sys
    # Quick smoke test: the PO-loop concept should be SAT.
    C = AtomicConcept('C')
    po_loop = And(
        C,
        And(
            Exists(PO, Exists(PO, C)),
            And(
                ForAll(PO, NegAtomicConcept('C')),
                And(
                    ForAll(DR, NegAtomicConcept('C')),
                    And(
                        ForAll(PP, NegAtomicConcept('C')),
                        ForAll(PPI, NegAtomicConcept('C')),
                    ),
                ),
            ),
        ),
    )
    is_sat, info = check_satisfiability(po_loop, verbose=False)
    print(f'PO-loop SAT check (cycle-aware): {"SAT" if is_sat else "UNSAT"}')
    print(f'Baseline comparison:', end=' ')
    is_sat_base, _ = _baseline_check(po_loop, verbose=False)
    print(f'{"SAT" if is_sat_base else "UNSAT"} (expected UNSAT — demonstrates the bug)')
    if not is_sat:
        print('ERROR: cycle-aware reasoner also says UNSAT — fix did not take effect')
        sys.exit(1)
    if is_sat_base:
        print('NOTE: baseline agrees — the bug appears to have been patched elsewhere')
    else:
        print('OK: cycle-aware reasoner correctly accepts the PO-loop.')
