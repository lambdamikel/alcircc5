# Why the ∀PO-Free Fragment Is Decidable — A Guide for the Tableau-Minded

> **📄 The full explainer is the typeset PDF:
> [`why_po_free_decidable.pdf`](why_po_free_decidable.pdf)** (~18 pp) ·
> [LaTeX source](why_po_free_decidable.tex). The certified result itself is
> written up as a focused paper:
> [`pofree_fragment_arxiv.pdf`](pofree_fragment_arxiv.pdf).
>
> To keep the project's prose in **one** place (the no-redundancy principle),
> this Markdown file is a high-level pointer, not a second copy. Everything
> below is orientation only; the arguments, the composition-table facts, the
> two proof routes, and the per-claim status table live in the PDF.

## What it is

A companion to the ALCI_RCC5 decidability project, pitched one level more
technical than the non-technical
[`WHY_ITS_HARD.md`](../WHY_ITS_HARD.md): written for a
reader who knows description logics, tableaux, and blocking, but not automata
theory or model theory. It does not walk you through the proofs — it puts
enough intuition, and enough hard checkable facts, in front of you that you
can honestly say "yes, I believe that."

## The gist

ALCI_RCC5 models are complete graphs with a composition law, and they are
legitimately infinite — so deciding satisfiability means bounding the free
("live") content of a **finite certificate** for a possibly-infinite model.
The composition table transports DR/PP/PPI deterministically along the
part-of order (four singleton cells), but **no single composition forces PO**
(several constraints together can). That algebraic asymmetry is the heart of
the story: universal obligations over DR/PP/PPI are trackable in a finite
vocabulary, whereas a single `∀PO` sends witnesses "wandering" in a way that
provably defeats the two-tier route's finite certificate. **Ban `∀PO` and both
argued proof routes close** — the two-tier quotient (chain-and-phase) and the
ordered-disjoint normal form (structural). On the fragment, the live-width
bound that the full logic's certificate route needs (F6) is a *theorem* rather
than a conjecture — though the procedure that was finally certified needs no
width bound at all — and the boundary is one constructor wide. The PDF develops
all of this.

## Current status (2026-09-14)

**Certified decidable across all four quadrants**, including the mixing one
(∃PO + ∃PP) that was open when this note was first written. Three capstones in
Lean 4 ([`formal/POFreeLift.lean`](../formal/POFreeLift.lean), ~45,400 lines,
**zero sorries**, axioms `propext`/`Classical.choice`/`Quot.sound`), with
fragment membership the **only** hypothesis in each:

- `decidableFSat` — **raw** input, with negation;
- `decidableSat_cone` — NNF concepts;
- `decidableSetSat` — under **concrete set** semantics.

Two things the earlier status listed as gaps are closed. Input no longer has to
be pre-normalized (`nnfP_correct` proves the translation preserves meaning in
both polarities) — and the polarity flag exposed that the fragment condition on
*raw* input is **no ∀PO positively and no ∃PO negatively**, since an ∃PO under a
negation *becomes* a ∀PO. And satisfiability over the abstract composition-table
semantics is proved **equivalent** to satisfiability over families of non-empty
sets (`satisfiable_iff_set`), with no fragment hypothesis, so that equivalence
covers the whole logic.

This was reached by a **third** route, distinct from the two this note argues:
a finite control graph of signatures, a monotone elimination to a greatest fixed
point, and a fresh-occurrence unfolding in which no node is ever reused — a
split forest, built directly rather than extracted from a model. It does
not use the `K(C₀)` bound, so the two arguments here remain independent — and
remain *unformalized*. The earlier per-quadrant route (`rr_covers`,
`decidableSat_hfrag` and friends) is still in the artifact and still true, but it
is **not** what certifies the theorem; its general mixed extraction was never
completed, and cold attack refuted the architecture it needed.

**Three independent cold reviews** (2026-08-29) attacked the trusted base, the
completeness direction and the soundness direction. None found a counterexample
or a defect in the fragment result, and a fourth, source-level review
(2026-09-09) found no defect in the Lean. The one remaining caveat is
complexity, not correctness: the procedure is **decidable but not runnable** —
the signature space is doubly exponential.

**Prior art, credited (2026-09-14).** Lutz & Wolter (2006) already prove that
every RCC5 structure is representable by regions (Theorem 23) — so the certified
abstract-versus-sets equivalence is a machine-checked special case — and that
the logic coincides with its substructure logic over regular closed regions of
ℝⁿ (Theorem 24), so the fragment result holds verbatim there too. Neither says
anything about decidability.

*Full-logic* decidability stays **open**.

The precise, per-claim breakdown (Lean-certified vs. machine-checked vs. argued)
is the PDF's "What is certified…" section; the step-by-step provenance is
[`ASSEMBLY_DESIGN.md`](../ASSEMBLY_DESIGN.md) §§267–297.

## What the PDF covers

1. The claim, and the setting — why complete-graph models block naive tableaux
2. The certificate architecture — finite blueprints for infinite models
3. The algebraic heart — four forced composition cells, and the PO that no
   single cell forces
4. **Route 1** — the two-tier quotient (chain-and-phase), and exactly where
   PO breaks it
5. **Route 2** — the ordered-disjoint normal form (structural), and why its
   tableau terminates
6. Why the boundary is exactly `∀PO`-freeness — not "horizontal vs. vertical"
7. The proof ledger, the per-claim status table, and a one-paragraph summary

---

*Companions:* [`WHY_ITS_HARD.md`](../WHY_ITS_HARD.md) (the
full problem, non-technical) ·
[`two_tier_quotient_ALCIRCC5.tex`](two_tier_quotient_ALCIRCC5.tex) (Route 1 in
full) · [`overview_arxiv.pdf`](overview_arxiv.pdf) (the overview paper). Where
this pointer and the formal artifacts disagree, the formal artifacts win.
