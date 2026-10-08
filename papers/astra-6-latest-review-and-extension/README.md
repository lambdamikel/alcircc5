# Astra 6 review: audit of the decidability claim, and two partial results (2026-10-07)

An 11-page technical report reviewing the project snapshot at commit `c0ad5b8`
(= tag `release-2026-09-14`), kept here unmodified. **Author: Astra 6** (per
Michael Wessel, who ran it; the PDF's own byline says "OpenAI Codex", the
product it was served through). The 22nd review on the project's ledger.

## What it contains

1. **An audit of the ∀PO-free decidability argument** — signatures, the
   compatibility table, where `POFree` enters, the raw polarity condition, the
   set-semantics equivalence. Verdict: *no gap found*. A source audit, not a
   kernel run (stated honestly; no Lean was available to it).
2. **Maximal disjointness** (its §4): for a fixed strict part order, the unique
   largest admissible disjointness is "no common lower bound"; principal
   down-sets realize exactly it; and truth of NNF concepts without `∃PO`/`∀DR`
   is preserved under maximizing disjointness. Plus `C_optional` — a concept
   satisfiable *only* when some overlap has no represented common part.
3. **PO-erasure** (its §5): for NNF concepts with no `∃PP`, `∃PO`, `∀DR` —
   `∀PO` *permitted* — replacing every `∀PO.D` by `⊤` preserves satisfiability.
   Composed with the certified procedure, this decides a strict syntactic
   extension of the ∀PO-free fragment. Counterexamples show each exclusion is
   necessary.
4. A calibrated, explicitly subjective outlook on AI-assisted resolution.

## Verification (2026-10-08, this project)

- **Both proofs hand-checked**: correct as written. The forest lemma's
  load-bearing step — incomparability is downward-hereditary in a
  unique-parent forest — holds; the maximality lemma is three lines of order
  theory.
- **`verification/python/wp136_astra6_audit_probe.py`** reproduces every
  number in the report's appendix (41 frames; 480/0, 12/0, 12/0) and tests
  both theorems against exhaustive small-model search with negative controls:
  **all checks pass** (222,008 normalization facts, 0 violations; 220
  erasure concepts, 0 divergences; both boundary counterexamples diverge
  exactly as claimed; `C_optional` confirmed).
- **The erasure theorem is now Lean-certified**: `formal/POFreeLift.lean`
  §299 (`erase_equisat`, `decidableSat_dfrag`, `decidableSetSat_dfrag`), by a
  PO-empty witness forest whose disjointness is incomparability; non-vacuity
  `allpo_satisfiable` (zero axioms), refutation `dfrag_clash_unsat`. §300
  certifies the order-level half of the maximal-disjointness result
  (`odMax`, `odMax_largest`, `pdown_subset_iff`, `pdown_disjoint_iff`,
  `pdown_inj` — all zero axioms). The interpretation-level normalization
  theorem remains theorem-level, probe-corroborated (`wp136` B). Built on the
  pinned Lean 4.33.1; capstone axioms `propext`/`Classical.choice`/`Quot.sound`.

## Assessment adopted into the project record

The audit passed — the first external review of the certified fragment to
find nothing to correct, in the artifact or its presentation. The erasure
extension is mathematically modest (the report itself notes its `∀PO`
constraints are provably erasable) but is the first decidable slice
*containing* `∀PO`. The forced-vs-optional overlap split and `C_optional`
are new structural vocabulary for the open full-logic problem and feed the
pair-matrix mosaic lead. Neither result touches F6 or the architectural gap
(`C_bad`, `C_joint` lie outside the fragment 𝒟).
