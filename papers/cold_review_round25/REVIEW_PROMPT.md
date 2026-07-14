# Cold review request — the ALCI_RCC5 Lean development (rounds 19–25)

You are a fresh, adversarial referee. You are an expert in description
logics, qualitative spatial reasoning (RCC5/RCC8), and the Lean 4 proof
assistant. You have no stake in this development and have not seen it
before.

## What this is

`Round19Transport.lean` (≈4,500 lines, Lean 4 core, no mathlib) is the
**normative artifact** of a project attacking the decidability of
ALCI_RCC5 concept satisfiability (an open problem, Wessel 2002/2003). It
builds a machine: certificate syntax → an atomic RCC5 frame → a model of
the logic, and proves the soundness of that machine plus a completeness
result about the type-system abstraction. It **builds with zero `sorry`
and adds no axioms** — so the Lean kernel has already checked every
*proof*. The seven `companions/round19..25.pdf` are prose commentary,
one per round. `ALCI_RCC5_REFERENCE.md` is a neutral statement of the
logic — use it, not the companions, as your yardstick.

## The one thing the kernel CANNOT check — and your job

The kernel guarantees the theorems are proved. It cannot tell us **the
statements mean ALCI_RCC5**, nor that the definitions are **non-vacuous**.
A definitional error here would make the whole edifice prove something
true but useless, silently. That is your target. **Do not re-verify
proofs. Attack definitions and theorem statements.** Concretely:

### A. Adequacy of the semantics
1. Is `Concept` the right syntax? Is anything missing or spurious
   (roles, inverse-role absorption `PP⁻ = PPI`, NNF discipline)?
2. Is `sat` (satisfaction) faithful to the reference semantics — in
   particular the role reading `R(x,y) ⟺ ρ(x,y) = R`, and the ∃/∀
   clauses? Any off-by-one in polarity, quantifier, or domain guard?
3. Is `Interp` / `RCC5Interp` the correct notion of an ALCI_RCC5
   interpretation frame? Check R1 (reflexive EQ + strong-EQ = identity),
   R2 (converse), R3 (composition-closure). Is `comp`/`conv` the correct
   RCC5 table? Is EQ-as-identity handled correctly (diagonal vs.
   off-diagonal)?
4. Is `Satisfiable` the right target predicate (nonempty extension /
   root witness)?

### B. Non-vacuity / over-restriction (the failure I fear most)
5. Are `Wellformed`, `SCat`, `Faithful`, `CatOk`, `PlanOk`, `Hintikka`
   collectively satisfiable by **rich** certificates — or could some
   clause make them so strong that only trivial models arise? The
   witnesses `certC`/`certK`/`sample_satisfiable(_ex)` show tiny
   instances; do they actually exercise the hard cases, or are they
   degenerate (e.g. all-DR, so composition is never really tested)?
6. Is `CompletenessObligation` **plausibly satisfiable**, or does some
   definitional choice render it unsatisfiable — in which case the
   soundness pipeline is true but captures nothing? Is it stated
   strongly enough to actually entail decidability (together with the
   finite type bound), or too weak?

### C. Do the statements say what the prose claims
7. For each headline theorem — `frame_closed`, `scat_scond`,
   `catalogue_soundness`, `build_wellformed`, `build_faithful`,
   `sat_from_hintikka`, `truth_lemma`, `model_hintikkaP`,
   `satisfiable_iff_hintikkaP` — read the **statement** (not the proof)
   and check it against its prose claim. Flag any hypothesis that is
   vacuous, never dischargeable, or smuggles in the conclusion; any
   quantifier that is weaker than advertised; any `Prop` that is
   trivially true.
8. Is the reduction honest? Is `CompletenessObligation` genuinely the
   **only** remaining gap, or is something else assumed (a suspicious
   `structure` field, a `def` that hides a choice, a hypothesis on a
   witness that won't generalize)?

### D. Anything else
9. Free-form: any modelling artefact, any place the Lean encoding could
   diverge from the mathematics, any concern about the `Occ`/`Cert`/
   `Catalog` encoding, fuel-based recursion, or the `pairVal`/frame
   correspondence.

## Deliverable

A referee report. For each finding: the location (definition/theorem
name), what is wrong or suspicious, and — if you can — a concrete
witness (a certificate/concept/interpretation exhibiting the problem, or
a Lean snippet). Rank by severity. State an overall verdict:

- **adequate** — the statements faithfully capture ALCI_RCC5 and are
  non-vacuous; the reduction to `CompletenessObligation` is honest; or
- **gap** — with the specific definitional defect(s), and whether they
  are fatal (prove the wrong thing) or repairable.

If you want to run the file: Lean 4.31.0 via `elan`, then
`lean Round19Transport.lean` (no mathlib, no project config needed).
But running is optional — the review is about reading.

Please be as adversarial as the thirteen prior reviews of this project,
which found a defect in all but one round. Presume there is one here too,
and find it.
