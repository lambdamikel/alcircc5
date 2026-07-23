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
| `formal/RCC5NormalForm.lean` | ~215 | `propext` (forward); `+ Classical.choice` (one converse direction) | The RCC5 normal form, **both directions**, arbitrary domains. Forward (`toOrderedDisjoint`): every strong-EQ RCC5 network is an ordered-disjoint structure (PP = strict partial order, DR = downward-closed disjointness) — `propext` only. Converse (GPT-5.6 Pro's canonical set representation, `papers/final_paper_gpt_5.6_review/`; verified in wp88): `eta` maps each x to the non-disjoint pairs with a coordinate ≤ x; `sub_iff_le` (order reproduced) and `eta_injective` are **fully constructive (zero axioms)**, `disj_iff_eta_disjoint` needs `Classical.choice` only for the "sets-disjoint ⟹ D" direction. So the biconditional holds on arbitrary domains. |
| `formal/ForcingReduction.lean` | ~145 | `propext`, `Quot.sound`, `Classical.choice` | The forcing reduction (Obs. 7.5 formalized): `F6_fin` holds iff no satisfiable concept forces an unbounded rigid horizontal crowd — modulo the width-crowd adequacy lemma, carried as a hypothesis field (not an axiom). |
| `formal/SemiDecidability.lean` | ~262 | `propext`, `Quot.sound`, `Classical.choice` (+ `ofReduceBool` in the toy witness only) | The semi-decidability schema: since SAT is Π⁰₁ (see below), decidability follows from a dovetailed certificate/refutation search — `decidableSat` — needing only *qualitative* F6 (some finite certificate), **no computable width bound**; `quantitative_free` recovers the bound a posteriori. Four inputs are hypothesis fields, not axioms; the Markov search core is classical-free. Zero `sorry`. |
| `formal/POFreeLift.lean` | ~3,160 | `propext`, `Quot.sound` (+ `Classical.choice` in the D2 model-side analysis only) | The two-tier **chain-unfolding lift** + (2026-07-22, fragment-certification **round A**) the **logic layer over the unfolding**. Lift: `lift_cc` — if the augmented one-point network (`aug` on `Option β`) is composition-consistent and the kernel is distinct from every external (`K e ≠ EQ`, strong-EQ), then replacing the kernel by an infinite PP-chain under the constant interface (`unf` on `β ⊕ ℕ`) stays composition-consistent. CC = every ordered triple closed, so this **subsumes multi-path PO forcing** — the argument does NOT assume "PO is free" (the 16th review's concern). Eight-case ordered-triple proof. **`unf_is_frame`** strengthens this to a full RCC5 `Frame` (reflexive-EQ + strong-EQ + converse + CC): a finite valid atomic quotient unfolds to an infinite genuine ALCI_RCC5 frame — **no patchwork/compactness needed for the abstract-semantics core**. Round A (see below): `Concept`/`Interp`/`sat`/`Hintikka`/`truth_lemma`/`RCC5Interp`/`Satisfiable` mirroring the normative artifact + the **two-tier single-kernel certificate** (`TwoTier`: external part `E`/`K`/`tauE` + one kernel with `p` cyclic phase types; validity `TwoTierOk` = the lift's frame hypotheses + the Hintikka obligations per **edge class** of the unfolding) + **`twoTier_hintikka`** (a valid certificate's labelling is a Hintikka labelling of the unfolding; chain arithmetic: every rung has a phase, every phase recurs above every rung) + capstone **`twoTier_sound`** (valid certificate + concept at a node ⟹ `Satisfiable` — certificate-to-model soundness THROUGH THE LOGIC, end to end) + `POFree` (the fragment predicate; soundness is fragment-agnostic, `POFree` is completeness-side vocabulary) + witness **`cinf_satisfiable`** (`∃PP.⊤ ⊓ ∀PP.∃PP.⊤` — a concept with NO finite model — proved `Satisfiable` through the full pipeline). Round B (2026-07-22, same day): the **multi-kernel lift** — `desc_cc`/`cchain` (directed chains, ascending or descending), the finite quotient `qnet` on `β ⊕ κ`, the unfolding `munf` on `β ⊕ κ×ℕ`, **`munf_is_frame`** (`Frame qnet ⟹ Frame munf`, all properness derived from the quotient's own strong-EQ — no extra hypotheses), the **`MultiTier`** certificate (any kernel family, per-kernel direction, constant cross-kernel interfaces; validity = Hintikka obligations per edge class incl. cross-kernel `kq_all` and cross-kernel fulfilment), **`multiTier_hintikka`** + capstone **`multiTier_sound`**, and witness **`cboth_satisfiable`** (`Cinf ⊓ ∃DR.(∃PPI.⊤ ⊓ ∀PPI.∃PPI.⊤)` — an ascending AND a descending infinite tower, DR-linked: two kernels of opposite direction, beyond any single-kernel certificate with finite external part). Round C (2026-07-22/23): the **executable first-order checker** — `FinMT` (certificates as pure list data: atom tables, concept lists, direction flags; Gödel-numerable), total decoder `decodeMT`, computable oracle-free Boolean checker **`mtOkB`/`mtAcceptB`** (folds over index ranges and type lists; the frame conditions checked uniformly on a raw `Nat`-encoded quotient `qraw`), soundness **`mtOkB_sound`** (checker ⟹ `MultiTierOk (decodeMT F)`) and capstone **`mtAcceptB_sound`** (acceptance ⟹ `Satisfiable` — first-order data to model, end to end); witness `cboth_satisfiable_exec` re-derives the two-tower result through the checker with the certificate as plain lists, and the acceptance is proved **by kernel `decide`** — no `native_decide`, so the axiom profile stays `propext`/`Quot.sound` even for the executable witness. Round D1 (2026-07-23): checker **completeness** — **`mtOkB_iff`** (the Boolean checker accepts EXACTLY the valid decoded certificates), acceptance-completeness **`mtAcceptB_complete`** (a valid certificate carrying `C0` at any node yields an accepted root index), and the fragment's decision-grade reduction **`decidableSat_of_codes`** (a fixed candidate-code list + the completeness premise — every satisfiable concept has an accepted code in the list, i.e. exactly the round-D2 extraction — yields `Decidable (Satisfiable C0)`; soundness side premise-free). Zero `sorry`. |

**Toolchain.** `elan`-installed Lean 4.32.0 at `~/.elan/bin`. No mathlib,
no lakefile. Build each file directly:

```
cd formal && ~/.elan/bin/lean Round19Transport.lean
cd formal && ~/.elan/bin/lean RCC5NormalForm.lean
cd formal && ~/.elan/bin/lean ForcingReduction.lean
cd formal && ~/.elan/bin/lean SemiDecidability.lean
cd formal && ~/.elan/bin/lean POFreeLift.lean
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

## The fragment certification campaign (2026-07-22, round A)

A new campaign, distinct from the full-logic development: certify the
**∀PO-free fragment decidability theorem end-to-end** — the project's
strongest unconditional result, currently theorem-level
(`papers/two_tier_quotient_ALCIRCC5.tex`,
`papers/po_free_fragment_ALCIRCC5.tex`; explainer
`papers/WHY_PO_FREE_IS_DECIDABLE.md`). Unlike the full logic, there is
**no open mathematics** here — the remaining risk is transcription risk
(the round-19/20 lesson: prose proofs shed unstated clauses when
Lean-transcribed). Route decision (Michael, 2026-07-22): follow the
**established two-tier quotient route**, not a new ordered-disjoint
tableau calculus — the tableau sketch has two classic danger seams
(upward-travelling ∀DR obligations vs. blocking; the #-flood on unfolded
chain copies) that would themselves need adversarial review first.

**Round A (landed, in `POFreeLift.lean`): the logic layer over the
unfolding.** `Concept`/`Interp`/`sat`/`Hintikka`/`truth_lemma`/
`RCC5Interp`/`Satisfiable` mirror the normative artifact clause for
clause (a future bridge is transcription); the **two-tier single-kernel
certificate** (`TwoTier`/`TwoTierOk`) states validity as the Hintikka
obligations quotiented by the unfolding's finitely many **edge classes**
(ext–ext = `E`; ext–chain = the constant interface against every phase;
chain–chain = `PP` upward / `PPI` downward between every phase pair,
`EQ` on the diagonal); `twoTier_hintikka` proves a valid certificate's
labelling is a genuine Hintikka labelling of the infinite unfolding
(chain arithmetic: `Nat.mod_lt` + `exists_later_phase`); capstone
**`twoTier_sound`** = valid certificate ⟹ `Satisfiable`, via
`unf_is_frame` + truth lemma. Soundness is fragment-agnostic (all
universals are checked on all edge classes); `POFree` is defined as the
completeness-side vocabulary. Non-vacuity: **`cinf_satisfiable`** —
`∃PP.⊤ ⊓ ∀PP.∃PP.⊤`, which has *no finite model*, is proved
`Satisfiable` through the full pipeline. Round-A design restriction
(documented in-file): single ascending kernel; no chain-internal `PPI`
fulfilment (rung 0 has no predecessor) — the extraction uses stabilized
external `PPI` witnesses instead, per the paper's forward-absorption
discipline. Zero `sorry`; axioms `propext`, `Quot.sound`.

**Round B (landed, same day): the multi-kernel lift.** Rather than
iterating the one-kernel lift through a dependent chain of carriers,
round B defines the multi-kernel unfolding *directly*: the certificate's
finite quotient is `qnet` on `β ⊕ κ` (externals + one node per kernel,
kernel–kernel values `Q`), the generated structure `munf` on
`β ⊕ κ×ℕ` (one *directed* ℕ-chain per kernel — `up : κ → Bool`,
ascending or descending via the mirrored-chain fact `desc_cc`), all
interfaces constant. **`munf_is_frame`**: `Frame qnet ⟹ Frame munf`,
with every properness condition *derived* from the quotient's own
strong-EQ clause (no extra hypotheses); the new triple configurations
are same-kernel pairs (self-absorption/`conv_super` with the chain value
in `{PP,EQ,PPI}`) and all-distinct triples (which project onto quotient
triples). The `MultiTier` certificate generalizes `TwoTier` (validity
adds the cross-kernel edge classes `kq_all` and a cross-kernel
fulfilment branch in `k_ex`; chain-internal fulfilment runs in each
kernel's own direction `cdir`); `multiTier_hintikka` + capstone
**`multiTier_sound`**. Witness **`cboth_satisfiable`**:
`(∃PP.⊤ ⊓ ∀PP.∃PP.⊤) ⊓ ∃DR.(∃PPI.⊤ ⊓ ∀PPI.∃PPI.⊤)` — a model needs an
ascending and a descending infinite tower, DR-linked; the certificate
has two kernels of opposite direction and no externals. Zero `sorry`;
axioms unchanged.

**Round C (landed, 2026-07-22/23): the executable first-order
checker.** `FinMT` makes certificates pure list data — `tauE` (external
type lists), `E`/`K`/`Q` (atom tables), `up` (direction flags), `phases`
(per-kernel phase-type lists) — with out-of-range reads defaulted, so
the decoder `decodeMT : FinMT → MultiTier (Fin nE) (Fin nK)` is total
and reads exactly the same raw accessors the checker uses (defaults are
never a soundness concern). The checker `mtOkB`/`mtAcceptB` is a
computable, oracle-free Boolean program: the quotient-frame conditions
are checked uniformly on a raw `Nat`-encoded network (`qraw`, externals
then kernels), everything else by folds over index ranges (`ballB`/
`bexB`) and over the type lists with constructor matching. Soundness is
the round's theorem chain: `frameB_sound` (raw checks transfer to the
decoded quotient frame through an index correspondence `qraw_corr`),
`mtOkB_sound` (checker ⟹ `MultiTierOk (decodeMT F)`), capstone
**`mtAcceptB_sound`** (acceptance ⟹ `Satisfiable C0`). The two-tower
witness re-runs through this route as plain data (`cbothFin`), and its
acceptance `cbothFin_accept` is proved by kernel **`decide`** — the
checker literally executes inside the kernel, and no `native_decide` is
needed, keeping even the witness on `propext`/`Quot.sound`. What round C
does *not* include (deferred to round D, where it is needed): the
checker's *completeness* (`MultiTierOk (decodeMT F) → mtOkB F = true`),
and an enumerator of `FinMT` codes.

**Round D1 (landed, 2026-07-23): checker completeness + the decision
reduction.** The converse of round C: `mtOkB_complete` proves the
Boolean checker accepts every valid decoded certificate (per-check
intro lemmas mirroring the soundness eliminations; the frame direction
runs through the inverse index correspondence
`decIdx`/`encIdx_decIdx`/`qraw_eq`), giving **`mtOkB_iff`** — the
checker accepts EXACTLY the valid decoded certificates.
**`mtAcceptB_complete`**: a valid certificate carrying `C0` at any
node of its unfolding yields an accepted root index (the `rootB`
generalization from round C is what makes this true). Capstone:
**`decidableSat_of_codes`** — for any fixed candidate list
`codes : List (FinMT × Nat)`, the premise "`Satisfiable C0 → some code
in `codes` is accepted`" yields `Decidable (Satisfiable C0)` by
running the checker down the list; the accepting branch needs no
premise at all (`mtAcceptB_sound`). This is the fragment's exact
analogue of the normative artifact's `decidableSat_of_finScheme`, with
one decisive difference: for the full logic the premise is the OPEN
mathematics (F6 ∧ W2′); for the ∀PO-free fragment the premise is a
THEOREM-LEVEL statement (the two-tier extraction) awaiting
transcription. Zero `sorry`; axioms unchanged.

**Round D2a (landed, 2026-07-23): model-side chain analysis.** The
first stone of the extraction: the two-tier paper's
**external-relation stabilization lemma**, kernel-checked as a theorem
about arbitrary models. In any `RCC5Interp`, along an ascending
`PP`-chain (`chain_model_pp`/`chain_model_ppi`/`chain_model_distinct` —
model-side chain transitivity and strong-EQ distinctness), the relation
of a fixed external element follows the monotone rank order
`{DR,PP} → {PO,EQ} → {PPI}` (`stabRank_mono`/`stabRank_fix`, both
`decide`-checked against the table; `EQ` cannot even self-loop), hence
**`external_stabilizes`**: it is eventually constant. Corollaries
**`backward_forcing_dr`**/**`backward_forcing_pp`** (a `DR`/`PP`
external is `DR`/`PP` at ALL earlier positions) and
**`forward_absorption_ppi`** (a `PPI` external stays `PPI` at all later
ones) — exactly what makes one constant certificate edge an honest
summary of infinitely many model edges, now proved on the model side.
`external_stabilizes` is the file's first classical theorem
(`Classical.choice`, via `by_cases` on undecidable ∃ over ℕ —
inevitable: the stabilization index is not computable from an abstract
model); the forcing corollaries and everything before it remain
`propext`/`Quot.sound`. Zero `sorry`.

**Rounds D2b + D2c (landed, 2026-07-23): the extraction's model-side
toolkit is complete.** D2b: subformula closure `cl` (transitively
closed) + classical model types `mty` (with the semantic Hintikka facts
`mty_clash`/`mty_and`/`mty_or`/`mty_all`/`mty_ex`); the **infinite
pigeonhole** (`recurrent_tail`: past some index every occurring value
recurs infinitely often; `segment_exists`: equal-typed pairs past any
bound); **segment coherence** (`seg_pp`/`seg_ppi`/`seg_eq`: with
type-equal endpoints `mty(c i) = mty(c j)`, a segment's phase types
satisfy the kernel `kk`-conditions — `∀PP` climbs to the top endpoint
and re-enters through the type equality, `∀PPI` dually down). D2c:
**syntactic vacuity** (`pofree_cl_all`, axioms `propext` ONLY: a
∀PO-free concept's closure contains no `∀PO` subformula;
`mty_no_all_po`: no model type ever carries a `∀PO` obligation — the
kernel-checked escape-valve fact making every constant-`PO` interface
logically unchallengeable) + **witness selection**
(`dr_witness_all_below`/`pp_witness_all_below`: a recurring `DR`/`PP`
demand has, past any bound, a witness with the CONSTANT demanded
relation to all chain positions below — late occurrence + backward
forcing; `ppi_witness_all_above`: dual via forward absorption) — the
constant-interface rows a segment-kernel's designated witnesses need.

**The remaining assembly (recorded, not laid — the honest boundary).**
What separates the current state from end-to-end decidability is ONE
construction: from `Satisfiable C₀` (∀PO-free), assemble an accepted
`FinMT` code within `K(C₀)`. Every ingredient lemma is now certified;
the assembly itself is genuinely large, and parts of it are only
SKETCHED in the two-tier paper, so it needs careful proof engineering,
not a rushed transcription (the round-19/20 lesson). Recorded design
(from the 2026-07-23 analysis):
  1. **Chain construction**: vertical demand recursion (`∃PP`/`∃PPI`
     towers) needs dependent choice to build `c : ℕ → α` from repeated
     `mty_ex` — then D2b/c supply the recurrent tail, the segment, and
     the constant-interface witnesses.
  2. **The finite part**: requirement-typed unraveling — certificate
     types are the REQUIRED formulas (root `C₀`, ∧/∨ decomposition,
     ∀-firing along declared edges), not full model types; model
     elements guide ∨-choices and guarantee clash-freeness. Horizontal
     (`PO`/`DR`) demand steps strictly decrease formula size (nothing
     propagates across `PO` — the wp49 vocabulary closure; `∀DR` flips
     once to `∀PPI` and then feeds only vertical structure), so the
     horizontal unraveling terminates; vertical demand paths either
     terminate (finite external ladders) or pigeonhole into
     segment-kernels.
  3. **Defaults**: all undeclared edges and ALL cross-kernel values are
     `PO` — always frame-safe (`PO` inhabits every cell of its row and
     column, and `po ∈ comp(R,S)` for all horizontal `R,S`) and, by
     `mty_no_all_po`, never obligated. `kq_all` is vacuous; kernels
     never need to talk to each other.
  4. **D2d**: the `K(C₀)` counting (certificate dimensions bounded by
     computable functions of `|cl C₀|`) + a `FinMT` enumerator with a
     membership-completeness lemma, instantiating `codes` in
     `decidableSat_of_codes` — then `Decidable (Satisfiable C₀)` for
     ∀PO-free `C₀`, the project's first end-to-end kernel-checked
     decidability theorem.

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
