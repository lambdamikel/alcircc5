# Lean certification plan for the forall-PO-free fragment

This package proposes a replacement completeness architecture for concept
satisfiability in the forall-PO-free fragment of `ALCI_RCC5` under the project's
abstract composition-table semantics and strong equality.

The central recommendation is to retire finite-node witness borrowing from the
decidability proof. A finite `ConeScheme` is used only as a control graph.
Every non-EQ existential is unfolded to a fresh occurrence. PP/PPI birth edges
generate a strict order, DR birth edges generate downward-closed disjointness,
and all residual pairs are PO. Repeated signatures therefore generate regular
infinite models without identifying points or borrowing witnesses.

This is a detailed certification blueprint, not a completed Lean proof. The
reported 42,700-line Lean source tree was not present in the supplied packet and
could not be rebuilt here.

The ledger contains 24 planned obligations across gates G0--G6. The proposed
public executable is three-valued: `sat`, `unsat`, or `outOfScope`. The bundled
checks validate the dependency ledger and replay finite adversarial models;
they are not a substitute for the pending Lean build.

## Contents

- `report/forall_po_free_decidability_certification_plan.pdf`: formal report.
- `report/forall_po_free_decidability_certification_plan.tex`: LaTeX source.
- `blueprint/DECISION_PROCEDURE.md`: compact mathematical specification.
- `blueprint/LEAN_MODULE_MAP.md`: proposed module and public theorem layout.
- `blueprint/PROOF_OBLIGATIONS.json`: machine-readable theorem dependency ledger.
- `blueprint/check_blueprint.py`: validates the ledger.
- `regressions/`: exact Python countermodels from the round-2 cold attack.
- `run_checks.sh`: runs the blueprint validator and regression suite.
- `MANIFEST.sha256`: checksums for every other packaged file.

## Scope

The proposed public theorem is for:

- concept satisfiability, without TBoxes, ABoxes, nominals, or counting;
- NNF inputs whose positive subformula closure contains no `forall PO`;
- abstract strong RCC5 networks, with EQ equal to identity;
- inverse roles absorbed by RCC5 converse.

The optional token-representation lemma in the report strengthens the
constructed ordered-disjoint model to an exact nonempty-set RCC5 model, but
concrete topological-region representability is not required by the target
semantics.

## Run

```sh
./run_checks.sh
sha256sum -c MANIFEST.sha256
```

All bundled Python programs use only the standard library.
