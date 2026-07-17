# Approach: The regular-cover pivot and the certified RCC5 normal form

**Idea.** Reframe the problem as finding a bounded, coherent *regular cover*
of a satisfiable concept's model, and attack the local RCC5 algebra head-on.

**What it produced.** A complete, exhaustively machine-checked **local**
theory of strong-EQ RCC5 networks: a **normal form** (an RCC5 network ⇔ an
*ordered-disjoint* structure — PP a strict partial order, DR a
downward-closed disjointness, PO residual), free amalgamation, an exact
one-point extension criterion, and exact uniform / non-uniform cross-pocket
policies. The normal form's forward direction is **certified in Lean**.

**Why it is a better map, not a shorter path.** Its own keystone — a
bounded-cover / bounded-width property — is provably *not* a local
composition problem (RCC5 totality makes every Gaifman graph complete, so no
off-the-shelf guarded/bounded-treewidth cover theorem applies). It is
**F6 again**, in narrower vocabulary.

Full treatment: overview paper, §"The regular-cover pivot" (RCC5 normal-form
theorem).

**Manuscripts & artifacts**
- [Local amalgamation theory note](../../papers/rcc5_local_amalgamation_theory.pdf)
- [`formal/RCC5NormalForm.lean`](../../formal/RCC5NormalForm.lean) — the certified normal form (forward direction)
- [`formal/ForcingReduction.lean`](../../formal/ForcingReduction.lean) — the forcing reduction (Observation 7.5)
- [Regular-cover pivot packages](../../papers/regular_cover_route_pivot/)

**Probes:** WP45–WP83 in [`verification/python/`](../../verification/python/).

**Result.** The local algebra is now complete and, in part, **certified**;
the global keystone (F6) is unmoved. The right vocabulary for a future
solver — not closer to the summit.
