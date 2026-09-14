# GPT-5.6 Sol cold review (2026-09-09) and draft fragment paper

Two documents written by **GPT-5.6 Sol** (OpenAI), prompted by Michael Wessel, reviewing
repository commit `795b270` (the state of 2026-09-03). They are kept here unmodified.

| File | What it is |
|---|---|
| `alcircc5_cold_review_2026-09-09.tex` / `.pdf` (18pp) | Cold review of `papers/overview_arxiv.tex` and the Lean sources under `formal/`, plus a renewed attack on full decidability. |
| `forall_po_free_fragment_arxiv.tex` / `.pdf` (17pp) | GPT-5.6 Sol's draft of a focused paper on the ∀PO-free fragment, written to illustrate its recommendation to split the overview. |

## What the review concluded

- The ∀PO-free fragment result is "technically real": every capstone of the Lean decision
  chain was located in the source (line numbers exact), with no hidden hypothesis. No Lean
  build was possible in the reviewer's environment, so this is a source audit, not a rebuild.
- Full ALCI_RCC5 decidability is unresolved; the cone scheme's full-language soundness fails at
  positive ∀PO, with boundary concepts `C_dir`, `C_joint`, `C_bad`, `C_sat`.
- The overview paper overstated several claims (ranked findings O1–O12) and should be split into
  a focused fragment paper and a research-program/methodology paper.

## What was done with it (2026-09-14, Claude Opus 5)

- **Overview fixed** (`papers/overview_arxiv.tex`): retitled (no "reducing it to one keystone");
  status section and tables rewritten so the fragment leads and the stale three-quadrant wording
  is gone; the F6 route now shows its two unproved steps explicitly; the Lean-certified rows
  for "F6 ⇒ decidability" and the Π⁰₁ dovetailing relabelled as conditionals; the
  identity-selector "iff" downgraded to a candidate characterization; the patchwork, grid and
  concrete-domain (ALCRP(D)) statements corrected; review and year counts reconciled.
- **Prior art credited** that the project had missed: Lutz & Wolter (LMCS 2(2:5), 2006),
  Theorem 23 (representation of RCC5 structures by regions), Theorem 24 (ALCI_RCC5 = the
  substructure logic of regular closed regions in ℝⁿ), Theorem 28 (recursive enumerability —
  the overview's "Π⁰₁ observation", previously presented as new).
- **Split adopted.** The fragment paper was written afresh, in our own words and from the Lean
  artifact, as `papers/pofree_fragment_arxiv.tex`, crediting this review for the recommendation
  and the draft.

## Where our verification disagreed with the review

- `C_dir = ∀PO.A ⊓ ∃PO.¬A` is accepted only by a control with ∀PO erased; the shipped operator
  (with the §291 PO clause) refutes it in round one — the same argument as the kernel-checked
  `cpo_refuted_at_one`.
- `C_bad` is the example the project's own round-1 cone-scheme review had already recorded
  (ASSEMBLY_DESIGN §292). `C_joint` is new. Both are accepted by the full-logic test — confirmed
  on a transcription of the control layer by exhibiting three-signature post-fixed families —
  and `C_sat` is accepted, as `coneScheme_complete` requires.
- Finding O5 quotes a sentence that is not verbatim in the paper, but its substance was right: the
  overview's conclusion claimed no rejected-but-satisfiable or accepted-but-unsatisfiable concept
  was ever exhibited, which the project's own record contradicts.
