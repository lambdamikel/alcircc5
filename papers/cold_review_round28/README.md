# Cold-review packet — ALCI_RCC5 Lean development, rounds 26–28 (15th review)

Self-contained packet for a cold, adversarial review. Target: whether the
**rounds 26–28 fixes** to the 14th review's interface findings (F1/F2/F3)
**genuinely close the gaps or merely appear to**. Authored by the same
model as the code, in response to the 14th review — so exactly where
cosmetic/vacuous "closure" would hide.

## Contents

- `REVIEW_PROMPT.md` — the review request. **Start here.** Its **Section 0 is a primer** on the structural assumptions a reviewer must not misread (esp.: a *finite* certificate legitimately unfolds to a *possibly infinite* model — the 14th review's misstep), so the same basic-assumption error does not recur.
- `ALCI_RCC5_REFERENCE.md` — neutral statement of the logic (the yardstick).
- `Round19Transport.lean` — the normative artifact (≈4,756 lines, Lean 4
  core, no mathlib, **zero `sorry`**).
- `companions/14th_review.pdf` — the prior review (defines F1–F4).
- `companions/width_barrier.pdf` — the current status report (conditional
  decidability, the F6/W2′ unification, and remarks on the 26–28 fixes).

## What rounds 26–28 claim

- **Round 26 (F3)** — `BoundedDecider.decidable`: a bounded, decidable
  certificate characterization *derives* `Decidable (Satisfiable C0)` by
  finite search. Decision-grade, not a semantic equivalence.
- **Round 27 (F2)** — `Interp`/`sat`/`RCC5Interp`/`Satisfiable` made
  carrier-polymorphic; `Satisfiable C0 = ∃ (α : Type), ∃ I : Interp α,
  …` = arbitrary-domain (reference) satisfiability; the Occ pipeline is
  the α = `Occ` instance.
- **Round 28 (F1)** — `fn_finitely_coded` (function = finite data on a
  finite domain) + finite code types `FinTemplate`/`FinCatalog` with
  total decoders + faithfulness (`template_net_coded`, `coreNet_coded`) +
  `f_factors_through_rows` (steering `f` factors through finite rows via
  the round-20 `f_reads_rows` clause). Claimed "substantially closed",
  with executable-checker wiring flagged as remaining engineering.

## Ledger going in

Fourteen prior reviews — a defect found in all but two. The 14th confirmed
the soundness pipeline's adequacy and found F1–F4 on the completeness
interface. Rounds 26–28 are unreviewed. Presume a defect; find it —
especially a "fix" that looks like it closes a gap but is cosmetic,
vacuous, or overclaimed (see prompt questions 8, 10). Note in particular
whether the finite-coding witnesses are degenerate (empty domains) and
whether F1 is honestly "substantially closed" or over-sold.

## Toolchain (optional)

Lean 4.31.0 via `elan`; `lean Round19Transport.lean`. No mathlib, no
lakefile.
