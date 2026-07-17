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

Full treatment: overview paper, §"Finite-model and reduction attempts"
(Theorem: the ∀PO-free fragment is decidable).

**Manuscripts**
- [Two-tier quotient — PO-coherent fragment decidable](../../papers/two_tier_quotient_ALCIRCC5.pdf)
- [The ∀PO-free fragment note](../../papers/po_free_fragment_ALCIRCC5.pdf)
- [Original quasimodel paper (retracted)](../../papers/decidability_ALCIRCC5.pdf)

**Result.** The ∀PO-free / PO-coherent fragment is **decidable** (with a
2-ExpTime quotient bound); the full logic is not settled by this route.
