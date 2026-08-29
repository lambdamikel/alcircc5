# Cone-scheme certification audit package

Date: 2026-08-29

This package accompanies `forall_po_free_cone_scheme_certification_report.pdf`.
It preserves the reviewed `cone_scheme_attack.zip`, the extracted Lean source,
the earlier certification blueprint, rerunnable probes, probe transcripts, and
the audit's full-logic and related-work notes.

## Verdict

The core Lean source chain appears to prove decidability for every already-NNF
`Concept` satisfying `POFree`, under the artifact's abstract composition-table
RCC5 semantics. No mathematical counterexample was found.

This is not a reproducibly release-certified build. The audit runtime contained
no Lean executable; the packet lacks a pinned toolchain; and raw syntax/NNF,
concrete-region adequacy, capstone axiom transcripts, generated-code tests, and
the prescribed Lean regression gate remain.

The proof does not establish full `ALCI_RCC5` decidability. The finite scheme's
completeness direction remains valid for arbitrary concepts, so absence of an
accepting survivor is a certified full-language UNSAT result. The converse fails
when universal PO restrictions are present. See
`audit/GENERALIZATION_TO_FULL_LOGIC.md` and the executable boundary probe.

## Contents

- `report/`: final PDF and LaTeX source.
- `original_artifact/`: exact uploaded ZIP and its extracted source tree.
- `prior_blueprint/`: the earlier 24-obligation certification plan and support files.
- `audit/`: theorem inventory, release findings, full-logic analysis, related work,
  and exact probe logs.
- `probes/`: original probes plus `wp_full_logic_boundary.py`.
- `run_audit_checks.sh`: safe, non-mutating package checks. It runs Python probes,
  verifies checksums and ZIP integrity, and reports that Lean was skipped if absent.
- `MANIFEST.sha256`: SHA-256 manifest for every packaged file other than the manifest
  itself.

## Quick verification

```sh
sh run_audit_checks.sh
```

Expected special case: the original `wp133_cone_scheme_unfolding.py` exits 1
because its intentionally incomplete truth column reports failures. The wrapper
records that as the documented result and checks that the frame-violation counts
are zero. It is not treated as a theorem counterexample.

If Lean 4.32.0 is available, the wrapper also attempts:

```sh
lean original_artifact/cone_scheme_attack/lean/POFreeLift.lean
```

The original source is preserved byte-for-byte. Audit additions do not modify it.
