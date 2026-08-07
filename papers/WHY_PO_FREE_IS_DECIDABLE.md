# Why the ∀PO-Free Fragment Is Decidable — A Guide for the Tableau-Minded

> **📄 The full explainer is the typeset PDF:
> [`why_po_free_decidable.pdf`](why_po_free_decidable.pdf)** (~15 pp) ·
> [LaTeX source](why_po_free_decidable.tex)
>
> To keep the project's prose in **one** place (the no-redundancy principle),
> this Markdown file is a high-level pointer, not a second copy. Everything
> below is orientation only; the arguments, the composition-table facts, the
> two proof routes, and the per-claim status table live in the PDF.

## What it is

A companion to the ALCI_RCC5 decidability project, pitched one level more
technical than the non-technical
[`WHY_ITS_HARD.md`](cold_review_f6_w2prime/WHY_ITS_HARD.md): written for a
reader who knows description logics, tableaux, and blocking, but not automata
theory or model theory. It does not walk you through the proofs — it puts
enough intuition, and enough hard checkable facts, in front of you that you
can honestly say "yes, I believe that."

## The gist

ALCI_RCC5 models are complete graphs with a composition law, and they are
legitimately infinite — so deciding satisfiability means bounding the free
("live") content of a **finite certificate** for a possibly-infinite model.
The composition table transports DR/PP/PPI deterministically along the
part-of order (four singleton cells), but it **never forces PO** by any single
composition. That one algebraic asymmetry is the whole story: universal
obligations over DR/PP/PPI are trackable in a finite vocabulary, whereas a
single `∀PO` sends witnesses "wandering" in a way that provably defeats the
finite certificate. **Ban `∀PO` and both known proof routes close** — the
two-tier quotient (chain-and-phase) and the ordered-disjoint normal form
(structural). The fragment is exactly the region where the open full-logic
keystone F6 ("bound the live width") is a *theorem* rather than a conjecture,
and its boundary is one constructor wide. The PDF develops all of this.

## Current status (2026-08-06)

Certified decidable across **three of its four quadrants** (horizontal
∃DR/PO/EQ, ascending-vertical ∃PP, descending-vertical ∃PPI) — a genuine
*computable* `Decidable (Satisfiable C₀)` in Lean 4
([`formal/POFreeLift.lean`](../formal/POFreeLift.lean), ~13,600 lines, **zero
sorries**), each non-vacuously witnessed. The fourth quadrant (**mixing**,
∃PO + ∃PP) has its merged certificate, its encoding, and a complete decision
certified on a concrete witness; the *general* mixed extraction is the one
remaining formalization. The keystone is a **constructive** uniformization
(`rr_covers`) — the vertical "W2′" is a kernel-checked theorem, not an oracle,
because removing `∀PO` lets the cross-relations coordinate for free. These
fragment theorems are **unreviewed**, and the *full-logic* decidability (F6)
stays **open** — it is forced by `∀PO`, which the fragment removes.

The precise, per-claim breakdown (Lean-certified vs. machine-checked vs.
argued) is the PDF's "What is certified…" section, mirrored in
[`LEAN.md`](../LEAN.md) and
[`ASSEMBLY_DESIGN.md`](../ASSEMBLY_DESIGN.md) §§24–25.

## What the PDF covers

1. The claim, and the setting — why complete-graph models block naive tableaux
2. The certificate architecture — finite blueprints for infinite models
3. The algebraic heart — four forced composition cells, and the PO that is
   never forced
4. **Route 1** — the two-tier quotient (chain-and-phase), and exactly where
   PO breaks it
5. **Route 2** — the ordered-disjoint normal form (structural), and why its
   tableau terminates
6. Why the boundary is exactly `∀PO`-freeness — not "horizontal vs. vertical"
7. The proof ledger, the per-claim status table, and a one-paragraph summary

---

*Companions:* [`WHY_ITS_HARD.md`](cold_review_f6_w2prime/WHY_ITS_HARD.md) (the
full problem, non-technical) ·
[`two_tier_quotient_ALCIRCC5.tex`](two_tier_quotient_ALCIRCC5.tex) (Route 1 in
full) · [`overview_arxiv.pdf`](overview_arxiv.pdf) (the overview paper). Where
this pointer and the formal artifacts disagree, the formal artifacts win.
