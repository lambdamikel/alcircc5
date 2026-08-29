# Cold review #2 — attack the COMPLETENESS half, and a full-logic claim

You are the second cold reviewer of this Lean 4 artifact. The first audited the
*trusted base* (definitions, semantics) and *execution*. This round targets the
other half, which got less scrutiny and which now carries a larger claim.

## Before you start: what NOT to read

Do not read `CLAUDE.md`, `ASSEMBLY_DESIGN.md`, `README.md`, `LEAN.md`,
`CONVERSATION.md`, or `papers/`. Read the Lean source, this prompt, `BUILD.md`,
the two probes, and — only where §5 says — `ROUND1_REVIEW.md`.

## 1. The two claims under review

```lean
theorem coneScheme_complete (hI : RCC5Interp I) (C0 : Concept) {x : α}
    (hx : I.dom x) (hC0 : sat I x C0) (n : Nat) :
    ∃ q ∈ gfpIter pruneSig (sigStatic C0) n, C0 ∈ q.1

theorem coneScheme_unsat_full (C0 : Concept) (n : Nat)
    (h : ∀ q ∈ gfpIter pruneSig (sigStatic C0) n, C0 ∉ q.1) :
    ¬ Satisfiable C0
```

**Neither takes `POFree`.** The second is therefore a claim about the FULL
logic — `ALCI_RCC5` satisfiability, open since 2002 — namely that an empty
survivor set is a sound refutation. It is one-sided (the converse needs the
fragment), but it is full-language, and if it is wrong we are wrong about the
open problem, not merely about a fragment.

Supporting chain: `modelSigs`, `modelSigs_sub`, `mem_modelSigs`,
`modelSigs_survives`, `modelSigs_in_gfp`, `gfp_greatest`, `dkey`, `dspec`,
`dkey_sigOk`, `dkey_mem_keyEnum`, `dkey_compat`, `supportB_mty`, `mem_sigStatic`.

## 2. Why we are suspicious of exactly this

Completeness went through in a **single attempt**, no failed lemma, on a problem
whose previous four architectures were each refuted by explicit finite
countermodels within days. Our reading is that the architecture *moved* the
difficulty rather than beating it: the finite object is now the signature set,
finite by construction, and nothing is extracted from the model at all.

That reading may be wrong in two ways.

- **Something was lost in the move.** `modelSigs_survives` says a model's own
  signatures survive their own elimination because the model supplies every
  witness. Is that complete — does `sigDemands` capture every demand a model
  point actually has? It drops `EQ` existentials by design; is that sound given
  `∃EQ` is handled by `supportB`?
- **The balance is broken.** `compatB` must be WEAK enough that real model edges
  satisfy it (else completeness fails) and STRONG enough that survivors are
  realizable (else soundness fails). Both are proved. A defect would then be a
  wrong *definition* — so read `compatB`, `sigOkB`, `supportB`, `sigDemands`,
  `sigCone`, `dspec`, `dkey` and ask whether each says what its name suggests.
  In particular `sigCone q = q.1 :: q.2` and the direction convention of
  `dspec` (`I.rho y x = pp`, so `q.2` is the types strictly *below* `x`).

## 3. Phase 1 — your own pass, before §5

1. **Is `coneScheme_unsat_full` really full-logic?** Check no fragment
   hypothesis leaks in through `sigStatic`, `keyEnum`, `dspec`, `cl`,
   `typeEnum`, `supportB`. If one does, the claim is smaller than advertised.
2. **Is `modelSigs_survives` complete?** Every demand, every relation.
3. **Is `dkey_compat` right at every relation?** It claims a real model edge
   `rho x y = r` yields `compatB r D (dkey x) (dkey y)`. The `DR` case
   quantifies over both cones and needs DR downward-closure; the `PP`/`PPI`
   cases push whole cones and need PP transitivity. Check the arithmetic
   against the composition table in the file.
4. **Is anything vacuous?** Can `modelSigs` be empty for a satisfiable concept?
   Can `gfpIter` retain everything so the test never fires? Is `sigStatic`
   itself ever empty for a satisfiable `C0`?
5. **The best outcomes.** An unsatisfiable concept the procedure ACCEPTS
   refutes soundness. A satisfiable one it REJECTS refutes completeness — and
   if that concept needs no `∀PO`, it refutes the full-logic claim too.

## 4. What we already measured — verify or refute, don't redo

Build, 2026-08-29, Lean 4.32.0: exit 0, 1m14s, **0 errors, 0 warnings, 0
`sorry`**; every capstone reports `[propext, Classical.choice, Quot.sound]`.

`wp135_cone_completeness_attack.py` (shipped, ours, **in scope for review**)
tests the model-side content of the completeness proof — `dkey_sigOk`,
`dkey_mem_keyEnum`, `modelSigs_survives`, `dkey_compat` — on concrete finite set
models, because the statement itself is unrunnable (`sigStatic` has size
`2^|cl C₀| · 2^(2^|cl C₀|)`). Results:

| part | what | result |
|---|---|---|
| A | 2,415 satisfiable `∀PO`-free instances | all four obligations hold |
| B | 2,431 satisfiable FULL-logic instances (12.4% contain `∀PO`) | all four hold |
| C | strengthening control: stricter `compatB` must break completeness | breaks on 49–68% per clause — so the test can detect over-strength |
| D | how much each clause discriminates | PP 44.9%, PPI 40.5%, DR 1.9%, **PO 0.0%** |

Part D is the one result we would most like a second opinion on. `compatB` has
`| Atom.po => true`, so a PO demand is served by *any* signature carrying the
body. The full-logic UNSAT test is therefore **sound but blind to `∀PO`**: it
can reject only through PP/PPI/DR structure and `supportB`. If that reading is
right the bonus theorem is honest but weak, and we would like that said plainly.
If it is wrong — if PO does constrain something we missed — say so.

## 5. Phase 2 — what round 1 established (read after Phase 1)

`ROUND1_REVIEW.md`. Summary so you can skip it: the composition table was
re-derived from set semantics at three domain sizes and matches exactly; `sat`,
`Interp`, `RCC5Interp`, `Satisfiable`, `POFree`, `cl` were read line by line and
are adequate; the `Decidable` is genuinely executable and was evaluated at the
kernel; 4,000 random `∀PO`-free concepts agreed with exhaustive finite-model
search. It found one inverted comment (fixed) and two understated scope limits
(fixed/recorded).

It did **not** attack the completeness proof structure, and the full-logic claim
did not exist when it ran.

## 6. Known scope limits — do not report as new

- Input must already be in NNF; there is no `nnf`-preservation theorem here.
- The procedure is **not runnable** beyond `|cl C₀| ≤ 2`. Decidable ≠ runnable.
- Semantics is the abstract composition-table one, not concrete regions.
- `wp135` sees only finite models; infinite ones are exactly what the Lean
  proof has to cover in general.

## 7. Calibration

Eighteen adversarial reviews of this project; a defect or overclaim in all but
two. In the fortnight before this artifact, four successive designs were refuted
by exact finite countermodels, and a paper that had survived four review rounds
was found to contain a real gap. Round 1 found no counterexample but explicitly
did not re-verify the proofs — the kernel did that — and could not run the
procedure at any interesting size.

Assume something is wrong. The full-logic claim is where being wrong costs most.
