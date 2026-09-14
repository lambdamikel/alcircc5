# Approach: The regular-cover pivot and the certified RCC5 normal form

**Idea.** Reframe the problem as finding a bounded, coherent *regular cover*
of a satisfiable concept's model, and attack the local RCC5 algebra head-on.

**What it produced.** A **local** theory of strong-EQ RCC5 networks, its
witnesses exhaustively machine-checked on small structures: a **normal form** (an RCC5 network ⇔ an
*ordered-disjoint* structure — PP a strict partial order, DR a
downward-closed disjointness, PO residual), free amalgamation, an exact
one-point extension criterion, and exact uniform / non-uniform cross-pocket
policies. The normal form is **certified in Lean in both directions**
(forward in `RCC5NormalForm.lean`; the converse via GPT-5.6 Pro's canonical
set representation and `odNet_frame` in `POFreeLift.lean`). That RCC5
structures are representable by regions at all is Lutz & Wolter's Theorem 23
(2006); what is new is the order-and-disjointness form, the explicit
construction, and the kernel proofs.

**Why it is a better map, not a shorter path.** Its own keystone — a
bounded-cover / bounded-width property — is provably *not* a local
composition problem (RCC5 totality makes every Gaifman graph complete, so no
off-the-shelf guarded/bounded-treewidth cover theorem applies). It is
**F6 again**, in narrower vocabulary — for this route.

Full treatment: overview paper, §"The regular-cover pivot" (RCC5 normal-form
theorem).

**Manuscripts & artifacts**
- [Local amalgamation theory note](../../papers/rcc5_local_amalgamation_theory.pdf)
- [`formal/RCC5NormalForm.lean`](../../formal/RCC5NormalForm.lean) — the certified normal form (forward direction and the core of the set representation)
- [`formal/ForcingReduction.lean`](../../formal/ForcingReduction.lean) — the forcing reduction (Observation 7.5), abstract, with the RCC5 adequacy fact as a hypothesis
- [Regular-cover pivot packages](../../papers/regular_cover_route_pivot/)

**Probes:** WP45–WP83 in [`verification/python/`](../../verification/python/).

**Result.** The local algebra this route needed is characterized, and its
normal form **certified**; the global keystone of the certificate route (F6) is
unmoved. The right vocabulary for a future
solver — not closer to the summit.
