# Approach: The cone scheme — the route that certified the ∀PO-free fragment

**Idea (GPT-5.6 Sol, 2026-08-28).** Stop reusing nodes. Keep the finite scheme
only as a *control graph* of **signatures** — a support type together with the
set of types allowed strictly below it — eliminate unsupported signatures by a
**monotone, reductive** operator down to a greatest fixed point, and unfold every
non-EQ existential demand to a **fresh occurrence**. Part-of births generate a
strict order, disjointness births a downward-closed disjointness relation, and
every other pair is partial overlap: an ordered-disjoint structure, hence an
RCC5 frame, by construction.

**Why it works where reuse failed.** Four local disciplines for reusing nodes
(blocking, witness borrowing) were refuted by exact finite countermodels,
because reuse imposes *global* conditions — acyclicity of the order, joint
realizability of the forced relations — that no per-edge, per-node or per-type
test can see. Freshness removes those obligations instead of testing them.
Completeness needs no fragment hypothesis at all: the signatures realized by any
model survive their own elimination. Soundness uses ∀PO-freeness exactly once —
residual overlap edges are unconstrained when no formula can object to overlap.

**Status.** Machine-checked in Lean 4: `decidableSat_cone` (NNF),
`decidableFSat` (raw input), `decidableSetSat` (set semantics), fragment
membership the only hypothesis; three cold reviews of the formalization found
no counterexample. By Lutz & Wolter's Thm 24 the result also holds for
substructures of regular closed regions of ℝⁿ. For the full logic the same
scheme gives only a sound refutation test: obligations from non-singleton
compositions (e.g. `C_bad`, `C_joint`) are out of its reach.

**Manuscripts & artifacts**
- [**The fragment paper**](../../papers/pofree_fragment_arxiv.pdf) — the focused, self-contained write-up
- [`formal/POFreeLift.lean`](../../formal/POFreeLift.lean) — §§267–297 of [`ASSEMBLY_DESIGN.md`](../../ASSEMBLY_DESIGN.md)
- [The certification plan](../../papers/cone_scheme_plan/) and the three cold reviews (`papers/cone_scheme_cold_review*`)
- Overview paper, §"The ∀PO-free fragment, certified: the cone scheme"

**Probes:** WP133–WP135 in [`verification/python/`](../../verification/python/).

**Result.** The ∀PO-free fragment is **decidable, with a kernel-checked decision
procedure**. Decidable is not runnable: the signature space is doubly
exponential.
