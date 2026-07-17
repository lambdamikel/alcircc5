# Approach: The Lean formalization and the reduction to F6

**Idea.** Move the load-bearing soundness argument into the Lean 4 kernel,
which refuses to accept a gap — removing the "prose proof assumed the hard
step" failure mode that every cold review had exploited.

**What is certified** (zero `sorry`): the **soundness** pipeline (a valid
finite certificate unfolds to a genuine RCC5 model of the concept); the
**faithfulness** of the Hintikka abstraction (satisfiability ⇔
Hintikka-realizability); and a **non-oracular, decision-grade reduction**
whose one remaining premise is a computable, complete enumeration of bounded
finite certificates.

**What remains open.** That premise is exactly **F6** (bounded live width) —
the completeness direction, the open mathematics — now sharpened to the
*identity-selector-minor dichotomy*, with the uniformization property W2′
folded into it.

Full treatment: overview paper, §"The Lean line and F6"; the
artifact-by-artifact history (rounds 19–30 + the two cold reviews of the
Lean) is in [`../../LEAN.md`](../../LEAN.md).

**Artifacts**
- [`formal/Round19Transport.lean`](../../formal/Round19Transport.lean) — the normative development
- [width-barrier status report and F6/W2′ analysis](../../papers/fable5_width_barrier/)

**Probes:** WP34 (Lean mirror), WP39–WP44 (F6/W2′ cold attacks) in
[`verification/python/`](../../verification/python/).

**Result.** A *certified surround* for a still-open problem: it kernel-checks
the soundness half and the shape of the decision procedure, but does **not**
prove decidability — the antecedent F6 is untouched.
