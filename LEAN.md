# The Lean formalization

This file records the concrete Lean 4 formalization effort for the
$\mathcal{ALCI}_{\mathrm{RCC5}}$ decidability project. It is the detailed
counterpart to the high-level summaries in `README.md` and the overview
paper; those abstract the Lean work and point here.

**One-line status:** the *soundness* half of the decidability argument
and the *faithfulness* of the finite Hintikka abstraction are
kernel-checked (zero `sorry`); a *decision-grade, non-oracular* reduction
is certified down to a single open premise, which is exactly the open
mathematics (bounded width, F6). Nothing here proves decidability of the
full logic. Standing label: **strongly supported, not certified.**

## The artifacts

| File | Lines | Axioms | What it is |
|---|---|---|---|
| `formal/Round19Transport.lean` | ~5,300 | `propext`, `Quot.sound` (+ `ofReduceBool` in `native_decide` witnesses only) | The normative development: certificate transport → S-layer closure → catalogue → logic layer → abstraction-completeness → non-oracular decision-grade reduction. Zero `sorry`. |
| `formal/RCC5NormalForm.lean` | ~152 | `propext` | The RCC5 normal form (forward): every strong-EQ RCC5 network is an ordered-disjoint structure (PP = strict partial order, DR = downward-closed disjointness). Certified for arbitrary domains. |
| `formal/ForcingReduction.lean` | ~145 | `propext`, `Quot.sound`, `Classical.choice` | The forcing reduction (Obs. 7.5 formalized): `F6_fin` holds iff no satisfiable concept forces an unbounded rigid horizontal crowd — modulo the width-crowd adequacy lemma, carried as a hypothesis field (not an axiom). |
| `formal/SemiDecidability.lean` | ~262 | `propext`, `Quot.sound`, `Classical.choice` (+ `ofReduceBool` in the toy witness only) | The semi-decidability schema: since SAT is Π⁰₁ (see below), decidability follows from a dovetailed certificate/refutation search — `decidableSat` — needing only *qualitative* F6 (some finite certificate), **no computable width bound**; `quantitative_free` recovers the bound a posteriori. Four inputs are hypothesis fields, not axioms; the Markov search core is classical-free. Zero `sorry`. |

**Toolchain.** `elan`-installed Lean 4.32.0 at `~/.elan/bin`. No mathlib,
no lakefile. Build each file directly:

```
cd formal && ~/.elan/bin/lean Round19Transport.lean
cd formal && ~/.elan/bin/lean RCC5NormalForm.lean
cd formal && ~/.elan/bin/lean ForcingReduction.lean
cd formal && ~/.elan/bin/lean SemiDecidability.lean
```

The mirror harness `verification/python/wp34_round19_lean_mirror.py`
subprocess-builds `Round19Transport.lean`, asserts return code 0 and zero
`sorry`, and cross-checks a Python transcription of the transport layer.

## Why Lean, and what "certified" means here

The project ran an adversarial-review methodology: every prose proof was
handed to a fresh, skeptical reviewer, and a defect was found in all but
two of fifteen reviews. Prose proofs of this kind repeatedly *assumed*
the hard step. Moving the load-bearing soundness argument into a proof
assistant removes that failure mode for the parts it covers: the kernel
refuses to accept a gap.

What is kernel-checked is the **soundness** direction (a valid finite
certificate unfolds to a genuine RCC5 model of the concept) and the
**faithfulness** of the Hintikka abstraction (the type-level certificate
loses nothing relative to models). What is *not* proved — deliberately —
is the **completeness / finite-realizability** direction: that every
satisfiable concept admits a *bounded* finite certificate. That is the
open mathematics (F6, bounded width; and the uniformization W2′, which
folds into F6). The kernel checking the soundness proofs says nothing
about whether that open premise holds.

## The progression (rounds 19–30)

The Lean development grew round by round; each round was written to be
attacked by the next review. The line below "R*n*" names the object
added.

- **R19 — the transport layer, in Lean.** The certificate transport layer
  (the map from certificate syntax to the operational frame) was defined
  in Lean 4 core with exactly one intentional `sorry`
  (`uSource_eq_frame`). Prior prose renditions of this exact step had
  produced review defects #11 and #12; in Lean the totality/order issues
  that caused them are compiler-enforced or definitional.
- **R20 — the `sorry` is proved.** `uSource_eq_frame` becomes a
  kernel-checked theorem via `frame_char` + `uSourceFuel_irrel` (fuel
  adequacy at the exact threshold). The proof *forced* four `Wellformed`
  clauses (`targets_exist`, `targets_length`, `net_conv`, `f_reads_rows`)
  that had been intended-but-unstated since round 15 — in prose each would
  have been the next defect; in Lean they were unprovable-goal errors.
- **R21 — the S-layer soundness kernel.** `SCond` (the manuscripts' S4
  condition as certificate-computable checks) ⟹ `frame_closed`,
  `frame_conv`, `frame_proper`: a wellformed, S-conditioned certificate
  unfolds to a proper atomic RCC5 network. The `certD` witness reproduces
  the WP32-C adversarial negative control in the kernel.
- **R22 — the catalogue level.** `scat_scond`: the S-condition stated on
  the catalogue data alone (`SCat`, step-count-independent) plus
  parent-pattern agreement (`Faithful`) yields the full per-unfolding
  `SCond`. One finite check certifies unboundedly many step lists.
- **R23 — the catalogue generator.** `buildCert` folds a plan into a
  certificate; `build_wellformed` and `build_faithful` prove
  wellformedness and faithfulness *by construction*, so
  `catalogue_soundness` gives closed frames for every valid plan with no
  per-certificate proof.
- **R24 — the logic layer.** `Concept` (NNF, inverse roles absorbed),
  `sat` (satisfaction over an atomic frame), `Hintikka` (locally coherent
  type labelling, one-step ∃-fulfilment — no parity/eventuality
  condition), `truth_lemma`, and the capstone `sat_from_hintikka`
  (wellformed + S-conditioned + a root-anchored Hintikka labelling ⟹ an
  actual RCC5 model). The soundness pipeline now runs certificate syntax →
  RCC5 model of the logic, every step kernel-checked.
- **R25 — completeness of the abstraction.** `satisfiable_iff_hintikkaP`:
  a concept is RCC5-satisfiable iff there is an RCC5 frame with a Hintikka
  labelling carrying it (`←` soundness, `→` `model_hintikkaP` — every
  model's own satisfaction relation is a Hintikka labelling). So the
  type-system certificate loses nothing relative to models.
  `CompletenessObligation` *states* — but does not prove — the one open
  target: every satisfiable concept admits a *finite* catalogue + plan +
  Hintikka labelling. Its hard sub-parts are F6 and W2′.
- **R26 — a decision-grade reduction (later corrected).** `BoundedDecider`
  + `BoundedDecider.decidable`: a bounded decidable certificate
  characterization derives `Decidable (Satisfiable C0)` by finite search.
  *The 15th review correctly found this premise oracle-inhabitable* (a
  classical oracle `check C _ := decide (Satisfiable C)` inhabits it
  vacuously). Superseded by R29.
- **R27 — carrier-polymorphic satisfiability (F2 closed).** `Interp`,
  `sat`, `RCC5Interp`, `Satisfiable` made carrier-polymorphic:
  `Satisfiable C0 = ∃ α, ∃ I : Interp α, …` is genuine arbitrary-domain
  (reference) satisfiability; the occurrence-based pipeline is the
  `α = Occ` instance. Confirmed genuine by the 15th review.
- **R28 — finite-coding of certificates (F1, partial).** `fn_finitely_coded`
  (a function is finite data on a finite domain) + finite code types
  `FinTemplate`/`FinCatalog` with total decoders + `f_factors_through_rows`.
  *The 15th review correctly found the non-vacuity witness degenerate*
  (empty domain); repaired and completed in R29.
- **R29 — the honest non-oracular bridge (F1 wired, F3 oracle-vacuity
  closed).** The full finite-code bridge: `hintikkaB` (a decidable Boolean
  Hintikka-checker — the structural `Hintikka` quantifies over infinite
  types and is not directly decidable) + `convTableOk` (a finite converse
  check forcing the infinite-domain `net_conv`/`core_conv`) + `decodeB` (a
  bridge decoder with `F_reads` by construction) + `CatOkFin`/`SCatFin` +
  `decodeTau` (a finite labelling table) → `finAcceptB`, a **fixed,
  non-oracular** Boolean checker of first-order finite code; `finAccept_sound`
  proves passing ⟹ `Satisfiable`; `decidableSat_of_finScheme` derives
  `Decidable` from a fixed enumeration + a completeness premise *about the
  fixed checker*. Because the checker forces exhibiting a real certificate,
  the premise is not oracle-inhabitable — it is exactly F6 ∧ W2′.
  `finAccept_nonvacuous` witnesses that the checker genuinely accepts.
- **R30 — F4 fixed.** `SCat.net_r3` was over-checking degenerate
  fresh-port triples (reading junk diagonal values), a completeness-side
  over-restriction. Now guarded; the sole consumer `fresh_tri` supplies
  the guards from its own hypotheses, so soundness is unaffected.

Alongside the normative file: `RCC5NormalForm.lean` (the certified RCC5
normal form, harvested from the regular-cover pivot) and
`ForcingReduction.lean` (the forcing reduction of Observation 7.5,
formalized modulo a single adequacy hypothesis).

## The Π⁰₁ observation (2026-07-17)

A late observation, separate from the normative development and new to the
project record: **SAT(ALCI_RCC5) is Π⁰₁.** The abstract composition-table
semantics is finitely first-order axiomatizable (exactly-one-atom per pair,
EQ = identity, converse coherence, composition closure — all universal FO
sentences over the finite table), and ALCI embeds by the standard translation
over arbitrary carriers (exactly the round-27 carrier-polymorphic
`Satisfiable`). By Gödel completeness, UNSAT is r.e.; so SAT sits at Π⁰₁ — the
domino problem's level.

Consequence: decidability ⟺ SAT is *also* r.e. ⟺ every satisfiable concept has
*some* finite certificate, **with no computable bound demanded.**
`formal/SemiDecidability.lean` formalizes the dovetailing schema. Its four
inputs are hypothesis fields (never axiomatized): checker soundness (the
project's `finAccept_sound`), refutation soundness, *qualitative*
certificate-completeness (= F6 ∧ W2′ minus the width budgets), and Gödel
completeness. From them it derives `decideB_correct`, `decidableSat`, and
`quantitative_free` (the computable bound returns for free a posteriori). The
Markov search core (`firstHit`) is classical-free (propext + Quot.sound);
`Classical.choice` enters only through the termination certificate, an erased
`Prop`, so the compiled program is a plain loop and `#eval` runs it. The FO
transcription the observation rests on — that the axioms carve out exactly the
Lean frame conditions, and that the standard translation matches the certified
`sat` — is cross-checked in `verification/python/wp84_fo_pi01_transcription.py`
(exhaustive for domains ≤ 3 points, 0 mismatches).

**What it does and does not do.** It weakens the keystone from *quantitative*
F6 (a width bound computable from C₀ — the target behind most review defects)
to its *qualitative* core (some finite-width model exists). It does **not**
settle the problem: qualitative F6 is untouched, and the Π⁰₁ placement adds one
standard external theorem (Gödel completeness) to the RCC5 patchwork property
and parity-automaton emptiness. The Proposition itself is prose + probe, not
Lean (formalizing Gödel completeness is out of scope for the core-Lean,
no-mathlib artifact); `SemiDecidability.lean` formalizes the *reduction* that
consumes it. The natural next stone (recorded, not laid): a Gödel-numbering
of `FinCatalog` codes to instantiate `certB` concretely, plus a bridge lemma
finScheme ⟹ DovetailScheme, which would make the "strictly weaker premise"
ordering itself kernel-checked. Standing label unchanged: strongly
supported, not certified.

## The two cold reviews of the Lean

- **14th review (adequacy).** The first cold review of the Lean asked: do
  the statements *mean* $\mathcal{ALCI}_{\mathrm{RCC5}}$, and are they
  non-vacuous? Verdict: the soundness pipeline's adequacy is **confirmed**
  — no polarity error in `sat`, no missing constructor, correct
  composition/converse tables, correct strong-EQ frame. The gaps found
  were formalization-level on the completeness interface (F1 higher-order
  fields; F2 carrier fixed to `Occ`; F3 unbounded obligation; F4 diagonal
  over-check) — none a soundness defect, none a second conjecture beyond
  F6/W2′. It also contributed a machine-verified path-automaton lemma.
- **15th review (the 26–28 fixes).** A cold review of the R26–R28 "fixes"
  returned *gap, repairable*: it correctly caught that R26 was
  oracle-inhabitable and R28's non-vacuity witness degenerate. Both
  witnesses were reproduced locally. F2 (R27) was confirmed genuinely
  closed. The corrections drove R29–R30.

The pattern across both: the kernel confirmed there is no *soundness*
defect, and the cold reviews found real *interface* gaps — which R27–R30
then closed, leaving the reduction honest and pinned to exactly the open
mathematics.

## Honest boundary

The Lean development is a *certified surround* for a still-open problem.
It kernel-checks the soundness pipeline, the abstraction's faithfulness,
and the shape of a non-oracular decision procedure; it does **not** prove
decidability. The single remaining premise of the decision-grade
reduction — a computable, complete enumeration of bounded finite
certificates — is exactly F6 ∧ W2′, the open mathematics, unmoved by any
amount of the formalization above. Rounds 26–30 are themselves
unreviewed; on this project's ledger, presume a future review finds
something in them.
