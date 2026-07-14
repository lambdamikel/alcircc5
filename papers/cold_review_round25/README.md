# Cold-review packet — ALCI_RCC5 Lean development (rounds 19–25)

Self-contained packet for a cold, adversarial review of the Lean
formalization. Fourteenth review of the project; first of the Lean
development. Target: **statement adequacy and non-vacuity**, not proof
correctness (the kernel already checks the proofs — zero `sorry`, no
added axioms).

## Contents

- `REVIEW_PROMPT.md` — the review request. **Start here.**
- `ALCI_RCC5_REFERENCE.md` — neutral statement of the logic; the
  yardstick for adequacy (use this, not the companions).
- `Round19Transport.lean` — the normative artifact (≈4,500 lines,
  Lean 4 core, no mathlib, zero `sorry`).
- `companions/round19..25.pdf` — prose commentary, one per round
  (transport layer → characterization → S-layer closure → catalogue
  conditions → catalogue generator → logic layer → completeness of the
  abstraction).

## Ledger going in

Thirteen prior reviews: twelve defects-with-witness, one
no-counterexample. Rounds 19–25 are unreviewed. Presume a defect;
find it. The defect class that matters most here is **definitional**
(a statement that proves the wrong thing, or a predicate that is
vacuous / over-restrictive), because that is exactly what the kernel
cannot catch.

## Toolchain (optional — the review is about reading)

Lean 4.31.0 via `elan`; `lean Round19Transport.lean`. No mathlib, no
lakefile needed.
