# Cold review #3 — attack SOUNDNESS, the half nobody has read

You are the third cold reviewer of this Lean 4 artifact. Two prior reviews
attacked the *trusted base and execution* (round 1) and the *completeness
direction* (round 2). **Neither read the soundness proof.** It is the half where
the fragment hypothesis actually does its work, and it is the last unexamined
load-bearing part of the result.

## Before you start: what NOT to read

Do not read `CLAUDE.md`, `ASSEMBLY_DESIGN.md`, `README.md`, `LEAN.md`,
`CONVERSATION.md`, or `papers/`. Read the Lean source, this prompt, `BUILD.md`,
the probes, and — only where §5 says — the two prior reviews.

## 1. The claim under review

```lean
theorem coneScheme_sound {X : List Sig} {q0 : Sig} {C0 : Concept}
    (hXS : ∀ q ∈ X, q ∈ sigStatic C0) (hfix : ∀ q ∈ X, q ∈ pruneSig X)
    (hpo : POFree C0) (hq0 : q0 ∈ X) (hC0 : C0 ∈ q0.1) : Satisfiable C0
```

A surviving signature carrying `C₀` yields a genuine model. Combined with
completeness this gives `decidableSat_cone`, the project's headline. Soundness is
the "no false positives" half: **if it is wrong, the procedure claims satisfiable
concepts that are not, and the decidability theorem is false.**

The chain: `coneScheme_sound` (:44069) → `unf_truth` (:43982) → the model
`unfInterp` (:43952) and `unfInterp_rcc5` (:43956) → `odNet` (:20057) over
`gOD` → the geometry `unfLt` / `unfDisj` / `unfLt_not_disj` / `vbase`
(:42381–42505) → the label lemmas `allPP_gLt`, `allPPI_gLt`, `allDR_gDisj`,
`allEQ_local`, `gchild_serves`, `olab_sub_cl`, `pofree_cl_all`.

## 2. What the construction does, so you can attack the right thing

The model is the **fresh-occurrence unfolding**: an infinite tree of demand
words. Every non-`EQ` demand spawns a *distinct* child; nothing is ever reused.
`lt` is the transitive closure of `PP`/`PPI` births, `disj` the downward closure
of `DR` births, and — this is the part to press on — `odNet` assigns **`PO` as
the residual**:

```lean
fun x y => if x = y then eq else if O.lt x y then pp
  else if O.lt y x then ppi else if O.disj x y then dr else po
```

So the model is *saturated with undeclared `PO` edges* between occurrences that
have nothing to do with each other. Soundness survives that only because **no
`∀PO` obligation can exist**, and that is the entire content of the fragment
restriction. The single use is one line in `unf_truth`'s `all` case:

```lean
| po => exact absurd (olab_sub_cl hXS hq0 u _ h)
          (fun hc => pofree_cl_all C0 hpo po c hc rfl)
```

**Any leak of `∀PO` into a label is immediately fatal**, and the two lemmas that
prevent it are `olab_sub_cl` (labels are inside `cl C₀`) and `pofree_cl_all`
(`cl C₀` has no `∀PO` under `POFree`). Those two are the highest-value targets in
the artifact.

## 3. Phase 1 — your own pass

1. **`olab_sub_cl`.** Can a label contain a concept outside `cl C₀`? It routes
   through `sigStatic_sub`, `keyEnum`'s shape, and `mem_sublists_sub`. Round 1
   changed `typeEnum` from `allListsLe` to `sublists`; check the argument still
   closes for *every* generated occurrence, not just the root.
2. **`pofree_cl_all`.** Induction over `Concept`; check the `all` and `ex` cases
   and that `POFree` is strong enough (it constrains `all r c` by `r ≠ po`, and
   says nothing about `ex po`, which is deliberate — is it safe?).
3. **The four universal lemmas.** `allPP_gLt` / `allPPI_gLt` / `allDR_gDisj` /
   `allEQ_local` each convert a *model relation* back into a *label membership*,
   through inversions (`odNet_pp_inv` etc.) of the residual-priority definition
   above. A misclassified residual pair is exactly how this breaks. The
   `∀PP`/`∀PPI` cases are the interesting ones: `lt` is a **transitive closure**,
   so a universal must reach occurrences several births away without the
   universal itself travelling. That invariant is `coneInto`.
4. **`gchild_serves`.** Existential fulfilment: does every demand really get a
   child whose label carries the body? It goes through `pickTarget`
   (`List.find?`) and `hfix`. And `∃EQ` is deliberately *not* a demand — it is
   discharged locally by `supportB` plus `refl_eq`. Is that sound under strong
   `EQ` (`eq_id`)?
5. **`gOD` is an `ODStruct`.** `unfLt_not_disj` is the clause whose failure
   killed this project's previous architecture. Here it is claimed to hold
   structurally — a `DR` birth opens a new vertical component and `lt` never
   leaves one. Is that true of the *transitive* closure, and of `unfDisj`'s
   *downward* closure?
6. **The model is infinite.** `GOcc` is all generated words. Any step that
   quietly assumes finiteness is a defect.
7. **`wp133`'s unexplained residue** (see `BUILD.md`): 4–5 truth violations that
   we attribute to unmodelled control-layer conditions. Confirm or refute that.
   If they localise a hole in `unf_truth`, that is the best outcome available.

**The decisive artifact** would be a `∀PO`-free NNF concept that the procedure
accepts and that is genuinely unsatisfiable. Prior reviews cross-checked 4,000
and 6,268 random concepts against exhaustive finite-model search without finding
one, so if it exists it is structured, not random — and the residual-`PO`
saturation above is where we would look.

## 4. A defect we already fixed, so you can judge our calibration

Round 2 found `compatB`'s `PO` branch was `true`, dropping `∀PO` propagation
valid at every model edge (`conv PO = PO`). It is now in the shipped definition
(§291). It changed nothing here: under `POFree` the clause is vacuous
(`allBodies_po_nil_of_pofree`). It also exposed that our own full-logic UNSAT
claim had been empty — withdrawn and repaired. Both are recorded in the source.

## 5. Phase 2 — the prior reviews (read after Phase 1)

`ROUND1_REVIEW.md`, `ROUND2_REVIEW.md`. Between them: the composition table was
re-derived from set semantics at three domain sizes; `sat`, `Interp`,
`RCC5Interp`, `Satisfiable`, `POFree`, `cl` were read line by line and are
adequate; the `Decidable` is genuinely executable and was evaluated at the
kernel; the elimination was run on 6,268 concepts against exhaustive model
search. **Do not redo this.** Neither review examined `unf_truth`,
`coneScheme_sound`, the unfolding geometry, or the label lemmas.

## 6. Known scope limits — do not report as new

- Input must already be in NNF; no `nnf`-preservation theorem here.
- Not runnable beyond `|cl C₀| ≤ 2` (round 2: direct generation of `sigStatic`
  moves this to ~4–5; the double exponential remains). Decidable ≠ runnable.
- Semantics is the abstract composition-table one. `RCC5NormalForm.lean` has the
  material for a set semantics (`eta`, `sub_iff_le`, `disj_iff_eta_disjoint`) and
  is imported nowhere.

## 7. Calibration

Twenty reviews of this project; a defect or overclaim in all but two. Rounds 1
and 2 each found a real one. Four successive architectures before this one were
refuted by exact finite countermodels. The soundness proof has strong *empirical*
cover — round 1's cross-check agreed in both directions — but **no human or model
has read it adversarially**, which is precisely the configuration in which this
project's defects have historically survived.

Assume something is wrong, and start with the `∀PO` vacuity argument.
