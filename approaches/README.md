# Approaches — organized by technique

This directory indexes the project's work **by approach/technique** (not by
round or date). The full narrative lives in one place — the
[overview paper](../papers/overview_arxiv.pdf) — and these folders are just
signposts into it.

Each folder holds a short **`Overview.md`**: a summary plus links to that
route's manuscripts, probes, and the relevant section of the paper. Nothing
is duplicated or moved — the hubs **link** to canonical locations
(`../papers/`, `../src/`, `../formal/`, `../verification/python/`), so the
paper stays the single source of the narrative and the build, imports, and
WP ledger stay intact.

Approaches, in rough order tried:

1. [**`Tableaux/`**](Tableaux/Overview.md) — naive tableau + blocking
   (triangle/quadruple types, profile/anywhere blocking); the cover-tree
   tableau.
2. [**`FiniteModel_TwoTier/`**](FiniteModel_TwoTier/Overview.md) —
   finite-bound / enumerate-and-check; the two-tier quotient; the
   **∀PO-free decidable fragment** (a genuine win).
3. [**`SplitForest/`**](SplitForest/Overview.md) — the split-forest normal
   form (Theorem A), the sound semantic foundation everything downstream
   consumes.
4. [**`NoAutomataCertificate/`**](NoAutomataCertificate/Overview.md) — the
   rounds-2–10 hand certificate that converged onto an automaton.
5. [**`Automata_Parity/`**](Automata_Parity/Overview.md) — the two-way
   parity tree-automaton route that "consumed" the split forests
   (Theorems A/B/C).
6. [**`Lean_F6/`**](Lean_F6/Overview.md) — the Lean formalization line
   culminating in the conditional decidability theorem and the reduction to
   F6 (see also [`../LEAN.md`](../LEAN.md)).
7. [**`RegularCovers/`**](RegularCovers/Overview.md) — the regular-cover
   pivot; the certified RCC5 normal form; the same ∀PO-free result.

Full state before this reorganization is preserved in the git tag
`pre-restructure-2026-07-16` and (locally) in `_backup_2026-07-16/`.
