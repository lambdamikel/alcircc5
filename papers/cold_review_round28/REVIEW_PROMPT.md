# Cold review request — the ALCI_RCC5 Lean development, rounds 26–28

You are a fresh, adversarial referee: an expert in description logics,
qualitative spatial reasoning (RCC5/RCC8), and the Lean 4 proof assistant.
You have no stake in this development.

## 0. Primer — structural assumptions you must NOT misread

The 14th review lost time to a basic-assumption error: it proposed a
"counterexample" (`∀PP.∃PP.⊤ ⊓ ∃PP.∃⊤`) that mistook a *finite certificate
unfolding to an infinite model* for a framework failure. Read these first
so the same does not recur.

1. **A certificate is a FINITE syntactic generator; its model may be
   INFINITE.** A `Cert`/`Catalog` + plan is finite data. `unfoldAll` /
   `pairVal` produce the *operational unfolding* — the frame on
   occurrences — which can be **infinite**. A concept that forces an
   infinite model (an unbounded PP-tower, e.g. `∃PP.⊤ ⊓ ∀PP.∃PP.⊤`) is
   perfectly satisfiable and perfectly within the framework: the finite
   certificate is a *generator*, and its unfolding is the (possibly
   infinite) model. **This is NOT a defect. Do not offer an
   infinite-model-forcing concept as a counterexample to the
   finite-certificate framework.** (The blocking/looping that keeps the
   *certificate* finite is separate from the model being infinite.)

2. **Strong-EQ semantics.** `EQ` is identity; it holds only on the
   diagonal. Between *distinct* elements only `{DR, PO, PP, PPI}` occur.
   Composition is over these; `EQ` re-enters only via merges.

3. **Inverse roles are absorbed.** `PP⁻ = PPI`, `PPI⁻ = PP`, etc.; there
   is no separate inverse-role constructor. Concepts are in NNF —
   negation appears only on atoms (`natom`).

4. **`Occ` is the occurrence type** (`core i` / `born step j`), the domain
   of the *generated* model; it is countable. Genuine *reference* domains
   are arbitrary via the carrier-polymorphic `Interp α` (round 27).

5. **`Satisfiable` is now carrier-polymorphic** — `∃ (α : Type), ∃ I :
   Interp α, …` — i.e. arbitrary-domain (reference) satisfiability. This
   *was* the 14th review's F2; round 27 fixed it. **Do not assume
   `Satisfiable` is `Occ`-only** (that would be reviewing the pre-fix
   artifact).

6. **Directions.** The *soundness* direction (certificate ⟹ model) is
   kernel-certified. The *open* direction is satisfiable ⟹ finite
   certificate (completeness), whose only substantive obstacles are the
   mathematics F6 ∧ W2′ plus finite-coding. The kernel has checked every
   proof; **your job is whether the STATEMENTS mean ALCI_RCC5 and whether
   the rounds-26–28 fixes are genuine**, not to re-verify proofs.


## What this is, and what changed

`Round19Transport.lean` (≈4,756 lines, Lean 4 core, no mathlib) is the
normative artifact of a project on the decidability of ALCI_RCC5 concept
satisfiability (open since Wessel 2002/2003). It **builds with zero
`sorry` and no added axioms**, so the kernel has checked every *proof*.
`ALCI_RCC5_REFERENCE.md` is a neutral statement of the logic — your
yardstick. `companions/width_barrier.pdf` is the current status report.

**This is the 15th review, and it has a specific focus.** The **14th
review** (`companions/14th_review.pdf`, GPT-5.5 cold) reviewed the
soundness/completeness formalization and returned *"gap, repairable"*:
it **confirmed the soundness pipeline's adequacy** (correct `sat`, syntax,
frame, tables — no soundness defect) but found four interface findings on
the completeness side:

- **F1** — `Cert`/`Template`/`Catalog` carry higher-order *function* fields
  (`net`/`coreNet`/`f`), so they are not finite syntactic certificates.
- **F2** — `Satisfiable` fixed the carrier to the occurrence type `Occ`,
  not arbitrary domains.
- **F3** — `CompletenessObligation` is an unbounded existence, not a
  bounded/decidable statement yielding `Decidable`.
- **F4** — `SCat.net_r3` over-checks degenerate diagonal triples
  (completeness-side over-rejection; verified, repair deferred).

**Rounds 26–28 (the material you are reviewing) claim to close F1–F3.**
They were authored by the same model that wrote rounds 19–25, in direct
response to the 14th review. **Your job is to decide whether these fixes
genuinely close the gaps, or merely appear to.** Be maximally skeptical:
a fix authored to satisfy a review is exactly where cosmetic or vacuous
"closure" hides.

## The specific claims to attack

### Round 26 — decision-grade reduction (claims to close F3)
Location: `structure BoundedDecider`, `def BoundedDecider.decidable`,
`decidableSat_of_boundedDecider`, `decidableSat_of_nonempty`.

1. Does `BoundedDecider.decidable` genuinely derive
   `Decidable (Satisfiable C0)`, or is the `Decidable` it produces
   trivial / does the structure smuggle the answer?
2. Are the two fields `sound` and `complete` the *honest* obligation?
   In particular: is `complete` (`Satisfiable C0 → ∃ n < bound C0,
   check C0 n = true`) strong enough that `Nonempty BoundedDecider`
   really entails decidability — and weak enough to be *plausibly
   inhabitable* (modulo the open mathematics), rather than
   contradictory or vacuous?
3. Is `Nonempty BoundedDecider ⟹ ∀ C0, Decidable (Satisfiable C0)` an
   honest statement of "decidability modulo an inhabitant", or does the
   `Nat` code + Boolean `check` hide non-finiteness?

### Round 27 — carrier-polymorphic satisfiability (claims to close F2)
Location: `structure Interp (α : Type)`, `def sat`, `structure RCC5Interp`,
`def Satisfiable`, `theorem satisfiable_iff_hintikkaP`, and the pipeline's
`certInterp : ... → Interp Occ`, `sat_from_hintikka`.

4. Is `Satisfiable C0 := ∃ (α : Type), ∃ I : Interp α, RCC5Interp I ∧
   ∃ x, I.dom x ∧ sat I x C0` genuinely *arbitrary-domain* (reference)
   satisfiability, or does the `α : Type` (universe-0) quantifier
   under-approximate the reference semantics of `ALCI_RCC5_REFERENCE.md`?
   Is there a universe or size issue that makes it too narrow (or
   vacuously wide)?
5. Does the soundness pipeline still produce a *genuine* reference model
   (the α = `Occ` instance a real RCC5 interpretation)? Did the
   polymorphic refactor silently weaken any statement?
6. Is `satisfiable_iff_hintikkaP` still meaningful post-refactor, or now
   trivial?

### Round 28 — finite-coding of certificates (claims to close F1)
Location: `def lookupT`, `theorem lookupT_tableOf`,
`theorem fn_finitely_coded`, `structure FinTemplate`/`FinCatalog`,
`def FinTemplate.decode`/`FinCatalog.decode`, `theorem template_net_coded`,
`coreNet_coded`, `f_factors_through_rows`, `certK_finitely_codable`.

7. Is `fn_finitely_coded` (a function is finite data on a finite domain)
   a genuine, correctly-stated result, or trivial/misstated?
8. Do `FinTemplate.decode`/`FinCatalog.decode` produce *genuine*
   `Template`/`Catalog` objects, and are they *total*? Do
   `template_net_coded`/`coreNet_coded` prove faithfulness on a
   *meaningful* domain, or only on trivial/empty domains (note
   `certK_finitely_codable` uses an empty pair list — is that a red flag
   that the witnesses are degenerate)?
9. Is `f_factors_through_rows` a real factoring of the higher-order
   steering field through finite data, and does it actually rely on the
   round-20 `f_reads_rows` clause as claimed?
10. **The honesty question.** The project claims F1 is "substantially
    closed" with only "engineering wiring" remaining (no executable
    checker yet connects the finite codes to the decision procedure). Is
    that honest, or is the un-wired finite-coding a *larger* gap than
    presented — e.g., does closing F1 for real require re-proving the
    pipeline over the finite codes, which has not been done?

### Cross-cutting
11. Do rounds 26–28 collectively make the "conditional decidability"
    claim honest — i.e., is it now true that "ALCI_RCC5 reference
    satisfiability is decidable modulo exactly F6 ∧ W2′", or is something
    still smuggled or overclaimed?
12. Anything else: any new definition that is vacuous, any theorem whose
    statement is weaker than its name suggests, any place the three
    "fixes" interact badly.

## Deliverable

A referee report. Per finding: location (definition/theorem name), what is
wrong or suspicious, and a concrete witness if you can (a Lean snippet, a
degenerate instance, a counterexample to a claimed faithfulness). Rank by
severity. Overall verdict:

- **fixes adequate** — F1–F3 are genuinely closed (or honestly reduced to
  stated engineering), the new definitions are non-vacuous, and the
  decision-grade / carrier / finite-coding claims are honest; or
- **gap** — with the specific defect(s), and whether a claimed closure is
  cosmetic, vacuous, or overclaimed.

Running the file is optional (Lean 4.31.0 via `elan`, `lean
Round19Transport.lean`, no config). The review is about *reading the
statements* — the proofs are already kernel-checked; your target is
whether they mean what is claimed.

The prior fourteen reviews found a defect in all but two. Presume there is
one here — especially a fix that looks like it closes a gap but does not.
