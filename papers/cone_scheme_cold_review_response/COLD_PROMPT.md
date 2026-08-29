# Cold review request — a claimed decision procedure in Lean 4

You are reviewing a Lean 4 artifact that claims to decide concept satisfiability
for a fragment of a description logic. **You have the toolchain and can build
it — please do.** That is the main thing the previous reviewer could not.

## Before you start: what NOT to read

This review is only worth something if it is COLD. The repository contains
extensive project framing that will anchor you. **Do not read:**

- `CLAUDE.md` (the project's own status narrative)
- `ASSEMBLY_DESIGN.md` (the design log, including the sections that built this)
- `README.md`, `LEAN.md`, `CONVERSATION.md`
- `papers/` — in particular the prior attack packets and their reports

Read the Lean source, this prompt, and nothing else. If you need a definition,
read it **in the source**, not in prose about the source.

## The claim

In `formal/POFreeLift.lean` (Lean 4.32.0 core, no mathlib):

```lean
def decidableSat_cone (C0 : Concept) (hpo : POFree C0) : Decidable (Satisfiable C0)
```

The intended reading: for every concept in the `∀PO`-free fragment of
`ALCI_RCC5`, satisfiability is decidable, with `hpo` the only hypothesis — no
unproved premise, no oracle.

Supporting chain, all in the same file:

| theorem | intended meaning |
|---|---|
| `coneScheme_correct_at` | `Satisfiable C0 ↔ ∃ q ∈ gfpIter …, C0 ∈ q.1` |
| `coneScheme_sound` | a surviving signature carrying `C0` gives a model |
| `coneScheme_complete` | a model gives a surviving signature carrying `C0` |
| `unf_truth` | every concept in an occurrence's label holds there |
| `unfInterp_rcc5` | the constructed unfolding IS an `RCC5Interp` |
| `pruneSig_mono` | the elimination operator is monotone |
| `coneScheme_unsat_full` | no survivor ⟹ UNSAT, for ARBITRARY concepts |

## Phase 1 — cold pass (do this first, before reading Phase 2)

Build it, then answer in your own words:

1. **Does `Satisfiable` mean what a description logician would mean?** Read
   `Concept`, `Interp`, `sat`, `RCC5Interp`, `Satisfiable`, `comp`, `conv`. Is
   the composition table RCC5's? Is strong EQ really identity? Is `sat`'s `∀`
   clause right? Is the semantics carrier-polymorphic or secretly fixed?
2. **Does `POFree` exclude exactly `∀PO`**, in the right closure?
3. **Is the `Decidable` real?** Is `decidableSat_cone` executable, or does it
   smuggle in choice/proof data? Where does `Classical.choice` enter?
4. **Is anything vacuous?** Empty carriers, empty signature sets, hypotheses
   that cannot be satisfied, a `Decidable` that is never used.
5. **Is the claim what the theorem says?** Note any gap between the English
   above and the Lean.

Then: **is there a concrete `∀PO`-free concept on which this gives the wrong
answer?** A counterexample beats everything else in this document.

## Phase 2 — where the authors think it is weakest

Read only after forming your own view.

- **Adequacy** is the class we can least self-check, and a previous review of an
  earlier artifact in this project found exactly that kind of defect.
- **`prune`'s balance**: it must be monotone (or completeness fails — an earlier
  route in this project died from an anti-monotone elimination condition that
  cascaded every type away) and strong enough that survivors are realizable.
- **The unfolding's geometry**: `unfOD`/`gOD` claim a fresh-occurrence unfolding
  is an ordered-disjoint structure hence an RCC5 frame. The load-bearing
  invariant is that order edges preserve a "vertical base" while `DR` births
  change it.
- **Completeness went through in one attempt**, which the authors read as the
  architecture having moved the difficulty rather than beaten it. Check what
  moved where.
- **Known scope limits, already recorded** (do not report as new): the input is
  already in NNF (no `nnf`/preservation theorem); there is no proved closed
  complexity bound; the semantics is the abstract composition-table one.

## What we want back

A verdict of the form "sound / gap / defect", with:
- what you built and what the build said (`#print axioms` on the capstones is at
  the end of the file);
- any counterexample, with the model or the impossibility argument;
- any statement that does not mean what §"The claim" says;
- and if you could not break it, precisely what you checked — that is genuinely
  informative here, given the history below.

## History you should know, because it calibrates the prior

This project has had seventeen adversarial reviews and a defect or overclaim was
found in all but two. In the week before this artifact was written, four
successive designs were refuted by exact finite countermodels, and a paper that
had survived four rounds of review was found to contain a real gap. The previous
review of THIS artifact found no counterexample but could not build it and was
not cold.

Assume something is wrong. Finding it is the job.
