# Approach: Finite-model attempts and the two-tier quotient

**Idea.** Force models to be finite (enumerate-and-check), or quotient the
model by type.

**Why it fails in general.** There is no finite-model property — some
satisfiable concepts require infinite models — and the quasimodel /
type-elimination procedure over-eliminates (incompleteness, not
unsoundness). Finiteness is simply the wrong target.

**The win.** One fragment escapes unconditionally: the **∀PO-free**
concepts (a syntactic case of the two-tier *PO-coherent* fragment). PO is
the only relation the composition table cannot pin (no backward forcing, no
forward absorption); remove the ability to universally constrain it and the
logic becomes decidable, while still retaining ∃PO, ∀DR, ∃DR, and all
part-of modalities.

**Provenance.** The route has a specific lineage: the **human author**
seeded it with the *PP-kernel* idea (collapse same-type occurrences on a
PP-chain into a kernel node with a reflexive PP-loop); **Claude** built that
into the two-tier quotient construction; and **GPT-5.4 Pro**'s review exposed
the "PO gap," which narrowed the result to the ∀PO-free fragment where it is
sound. (It is *not* a consequence of the split-forest models — a different
route that shares only the RCC5 patchwork property; and it was GPT-5.4 Pro,
not GPT-5.5, in this thread.)

**Certified soundness core (2026-07-18).** Re-examined after the 16th review;
the chain-unfolding lift is now kernel-checked in
[`formal/POFreeLift.lean`](../../formal/POFreeLift.lean) (`lift_cc`,
`unf_is_frame`), and two independent decision procedures agree on the
fragment with zero mismatches ([`wp86`](../../verification/python/wp86_two_tier_lift_check.py),
[`wp87`](../../verification/python/wp87_po_free_end_to_end.py)). Full
end-to-end certification (the model-of-C₀ layer + completeness extraction)
remains open.

Full treatment: overview paper, §"Finite-model and reduction attempts"
(Theorem: the ∀PO-free fragment is decidable).

**Manuscripts**
- [Two-tier quotient — PO-coherent fragment decidable](../../papers/two_tier_quotient_ALCIRCC5.pdf)
- [The ∀PO-free fragment note](../../papers/po_free_fragment_ALCIRCC5.pdf)
- [Original quasimodel paper (retracted)](../../papers/decidability_ALCIRCC5.pdf)

**Result.** The ∀PO-free / PO-coherent fragment is **decidable** (with a
2-ExpTime quotient bound); the full logic is not settled by this route.
