# 14th review — GPT-5.5 cold, the Lean development (rounds 19–25)

First cold review of the **Lean** formalization (`formal/Round19Transport.lean`),
targeting **adequacy** (do the statements mean ALCI_RCC5? are they
non-vacuous?) rather than proof correctness. Prompted by
`papers/cold_review_round25/`.

## Verdict: **gap, repairable** — soundness adequacy CONFIRMED

The review's most important outcome is a **positive**: the soundness
pipeline's adequacy holds up. GPT found **no** polarity error in `sat`,
**no** missing NNF constructor in `Concept`, **no** RCC5 composition-table
error, and confirmed `RCC5Interp` is the correct strong-EQ atomic-frame
notion (R1/R2/R3). The chain
`Wellformed + SCond + Hintikka ⟹ certInterp_rcc5 ⟹ truth_lemma ⟹ Satisfiable`
is "semantically meaningful." So the first review of the Lean did **not**
find the semantics vacuous or wrong — the thing the kernel cannot check
came back clean.

The gaps are all on the **finite-certificate / completeness interface**,
and are formalization-level, not soundness failures:

- **F1** — `Cert`/`Template`/`Catalog` carry higher-order *function* fields
  (`net`, `coreNet`, `f`), so they are not finite syntactic certificates;
  the "finite catalogue" is a semantic object. Repair: finite-code the
  syntax (arrays/`Fin`) with total evaluators.
- **F2** — `Satisfiable` fixes the carrier to `Occ`, whereas the reference
  semantics quantifies over arbitrary nonempty domains. Repair: a
  carrier-polymorphic `ReferenceSatisfiable` or a countable-model bridge
  theorem.
- **F3** (referee label; unrelated to the project's F3) — `Completeness‑`
  `Obligation` is an unbounded existence over higher-order objects, **not**
  a bounded, finite, decidable search statement, so it does not by itself
  yield `Decidable`. Repair: state it over finite codes bounded by a
  computable function of `C₀`, with an actual checker / `Decidable` theorem.
  GPT is explicit that this is **not** a second mathematical conjecture
  beyond bounded-width/F6 — it is the *under-formalization* of that
  assumption.
- **F4** — `SCat.net_r3` over-checks degenerate triples (only `p ≠ q`,
  missing `p ≠ fresh_j`/`q ≠ fresh_j`), so it inspects junk diagonal
  template values and can reject valid certificates. **Machine-verified**
  (`verification/python/wp38_...`): `PP ∉ comp(PP, conv DR) = {DR}`.
  Completeness-side over-rejection only, never unsoundness.
- **F5** — the positive witnesses (`certC`/`certK`) are all-DR and don't
  exercise PP/PPI transitivity, PO, core rows, or steering (and mask F4).
- **F6** (referee label) — headline statements mostly honest; a few prose
  claims overstate (`frame_closed` is conditional; `satisfiable_iff_hintikkaP`
  is *semantic* Hintikka completeness, not *finite* type-system
  completeness — already qualified in the width-barrier report).

## The genuine new result (verified)

After reading the width-barrier report, GPT produced a **path-automaton
lemma**, which we machine-verified (`wp38`): in the composition-path
subset-automaton, **there is no non-EQ cycle using a horizontal (DR/PO)
label** — every recurrence that never admits an EQ-fold is vertical
(PP/PPI). This strengthens WP36 ("only singleton determinations are
vertical") to the path level and handles non-singleton propagation sets
like `{DR,PO,PP}`. It does **not** close F6 (a width statement, not a path
statement) but removes a class of would-be counterexamples and matches
WP37's reduction.

GPT also sketched (unverified — no Lean in its container) an ω-limit
"stable certified run" and a decidability-from-bounded-checker reduction;
these build on the pre-repair interface F1–F3 flags, so they are recorded
but not integrated.

## Contents

- `alci_rcc5_round25_cold_review.pdf/.tex` — the referee report.
- `gpt_path_automaton_report.txt` — GPT's path-automaton finding.
- `session_chat.docx` — the full review session (incl. the initial
  misread — a bogus "infinite PP-chain" counterexample that mistook a
  finite certificate unfolding to an infinite model for a framework
  failure; retracted after steering).

## Integration

Verified and recorded: the path-automaton lemma and F4 (`wp38`). The
soundness-adequacy confirmation and the F1–F3 interface gaps are folded
into the width-barrier report and the project status. Ledger: **14 reviews
— the 14th finds no soundness/adequacy defect in the core semantics
(confirmed faithful) but real formalization gaps in the finite-certificate
interface (F1–F4) + witness weakness (F5) + wording (F6); all repairable.**
