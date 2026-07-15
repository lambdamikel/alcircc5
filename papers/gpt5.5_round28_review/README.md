# 15th review — GPT-5.5 cold, rounds 26–28 (the F1/F2/F3 "fixes")

Cold review of whether rounds 26–28 genuinely closed the 14th review's
interface findings. **Verdict: gap, repairable but not cosmetic** — and
it is correct. It caught real overclaims (two of which the prompt itself
flagged as suspects). Both of its central witnesses were **reproduced
locally and compile against `Round19Transport.lean`**.

## Verdict, verified

| Finding (14th review) | 15th-review verdict | Verified |
|---|---|---|
| **F2** (carrier) | **genuinely closed** (round 27) | — |
| **F3** (decision-grade) | **only partially reduced** | ✓ |
| **F1** (finite-coding) | **NOT closed; overclaimed** | ✓ |
| global "modulo exactly F6 ∧ W2′" | **overclaimed** | — |

- **F3 / Finding 1 (Critical, confirmed).** `BoundedDecider.decidable`
  is a correct finite-search reduction *relative to a supplied `D`*, but
  the premise `Nonempty BoundedDecider` is inhabitable by a **classical
  oracle** — `check C _ := if Satisfiable C then true else false` with
  `bound := 1` satisfies `sound` and `complete`. So
  `Nonempty BoundedDecider ⟹ Decidable` proves decidability from a
  premise that is *classically vacuous*, not from a finite syntactic
  certificate scheme. **The oracle witness compiles.** Repair: constrain
  `check` to a non-oracular first-order finite parser/verifier that does
  not mention `Satisfiable`.

- **F1 / Findings 2–7 (Critical/Major, confirmed).** The normative
  completeness objects remain higher-order (`Cert`/`Catalog`/`Template`
  function fields; the labelling `τ : Occ → List Concept`).
  `fn_finitely_coded` is a correct *local* tabulation lemma but merely
  copies finitely many (possibly oracle) values into a list; the total
  decoders have only *local* faithfulness (no global inspected-domain
  coverage); `f_factors_through_rows` is a correct *pointwise* factoring
  but builds no finite `F`-table; and `certK_finitely_codable` is
  **degenerate** — its witness has zero templates (vs. certK's two) and
  proves agreement only over the *empty* domain. **The degenerate
  witness compiles.** So calling F1 "substantially closed" was an
  overclaim; F1 is open.

- **F2 / Finding 8 (Positive).** Round 27's carrier-polymorphic
  `Interp`/`Satisfiable` genuinely closes F2; the soundness pipeline
  still produces a real reference model at α = `Occ`.

- **F4 / Finding 10.** Still unrepaired; so the obstacle ledger cannot
  honestly read "only F6 ∧ W2′".

## The repair program (the reviewer's "what would close the gap")

1. A **non-oracular** bounded checker: derive `check` from a first-order
   finite-code parser/verifier that never mentions `Satisfiable`.
2. State completeness **over finite codes**, or bridge the higher-order
   `Catalog`/`Template`/`τ` witnesses to finite codes preserving every
   predicate consumed by `sat_from_hintikka` and catalogue soundness.
3. **Finite-code `τ`** (a closure-bounded type assignment).
4. **Global inspected-domain coverage**: every lookup by
   `CatOk`/`SCat`/`buildCert`/`pairVal`/`Hintikka`/satisfaction lands in
   the decoded tables.
5. A **non-degenerate** `certK` codability theorem (real templates,
   real domains).

## Honest status after integration

Rounds 26–28 delivered: **F2 genuinely closed** (round 27); a **correct
finite-search reduction target** (round 26, but its `Nonempty` premise
is not yet honest); and **local finite-tabulation ingredients** (round
28, not wired in). The claim "all three interface findings discharged or
reduced to routine wiring" and "decidable modulo exactly F6 ∧ W2′" were
**overclaimed** and are hereby withdrawn. The honest position: F2 closed;
F3 and F1 are **open formalization work** (the repair program above),
*in addition to* the open mathematics F6 ∧ W2′ and the deferred F4.

Ledger: **15 reviews** — a defect (or overclaim) found in all but two.

## Contents

- `round26_28_referee_report.pdf/.tex` — the referee report.
- `supporting_witnesses.lean` — the reviewer's Lean witnesses (the oracle
  `BoundedDecider` and the degenerate `certK` code); both compile against
  the artifact (reproduced locally).
