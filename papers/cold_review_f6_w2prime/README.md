# Attack packet — F6 (bounded width) ∧ W2′ (uniformization)

A self-contained, cold packet aimed **not** at reviewing the ALCI_RCC5
development but at **attacking the two open mathematical sub-problems** it
has isolated. For a fresh expert (GPT-5.5 or Fable 5) in description
logics, RCC5, and finite model theory / definability.

**This is a research request, not a referee request.** The prior fourteen
documents were adversarial reviews. This one asks for *progress on open
math*: a proof, a counterexample, a decidable fragment, or a sharpened
reduction — not a "gap" verdict.

## Start here

1. `ATTACK_PROMPT.md` — **the request.** Section 0 is a primer on the
   assumptions not to misread (esp.: a finite certificate legitimately
   unfolds to an infinite model — do not offer infinite-model-forcing as
   a counterexample). Sections 1–2 state what is settled and the four
   ranked targets. **Target A (W2′) is the recommended one — best odds of
   a definitive answer.**
2. `width_barrier.pdf` — the 10pp status report (the main document): the
   composition table, determination-is-vertical / distinctness-is-
   horizontal, the reduction (F6 ⟺ horizontal forcing), and the knife's
   edge (F6 = the undecidability obstruction, one fact two faces).
3. `DEFINABILITY_TOOLKIT.md` — the model-theoretic toolbox aimed at the
   specific questions: locality (the primary lever for F6), EF/
   bisimulation games (the counterexample and W2′ tool), the composition
   method (the finite-algebra form), bounded-model machinery, and the
   grid-encodability analysis — plus why Ramsey theory does not fit.
4. `WHY_ITS_HARD.md` / `why_its_hard.pdf` — plain-language companion;
   fastest way to load the intuition first.
5. `probes/` — four runnable, dependency-free Python probes and their
   outputs (`wp35`–`wp38`): the width attack, determination vs.
   distinctness, the reduction to horizontal forcing, and the
   path-automaton lemma. Modify them to test a construction. Run all four
   with `./run_probes.sh`; the RCC5 composition table and cover-tree
   tableau they use are shipped in `src/` (Python 3 stdlib only, no
   external dependencies).

## The two problems in one paragraph each

- **F6 (bounded live width).** Does every satisfiable concept have a
  certificate whose *live* (non-shadow) width is bounded by a computable
  function of the concept? Reduces (Obs. 7.5) to: can a concept *force*
  an unbounded *rigid* {DR,PO} graph? That is the *same fact* as the
  undecidability obstruction (Obs. 8.1) — F6-proof = decidable,
  F6-counterexample = undecidable. **F6 in full = the 24-year open
  problem.** The realistic asks are a decidable *fragment* (Target B) or
  formalizing the reduction (Target D).

- **W2′ (uniformization).** In extraction, must every jointly-realizable
  glue step admit a *state-uniform* steering function (cross-pair value =
  a function of interface states, not identities)? Measured **208/211 =
  98.6%**; the 3 failures are the open content. Soundness does not depend
  on it (failure = over-rejection only). **This is the tractable target**
  — a bounded refinement of the interface state may well close it; the 3
  witnesses are a direct test. (Target A.)

## Honest framing

The conditional decidability theorem (bounded width ⟹ decidable) has its
soundness half **machine-checked in Lean, zero sorries**. F6 and W2′ are
the *open mathematics*; some finitary interface obligations are also
under-formalized on the completeness side, but those are finishable
formalization **orthogonal** to F6/W2′ and are **not** part of this
attack. The standing label is **strongly supported, not certified**, and
the project's cardinal sin is overclaiming — a null result stated cleanly
is worth more than a hedge.

Ledger for context: fifteen prior reviews of the surrounding development,
a defect or overclaim found in all but two. This packet is downstream of
all of them and targets only the residual open math.
