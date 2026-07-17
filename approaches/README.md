# Approaches — organized by technique

This directory reorganizes the project's work **by approach/technique**
(not by round or date), as the source structure for the arXiv overview
paper (`papers/overview_arxiv.tex`).

Each approach folder contains an **`Overview.md`** — a self-contained
write-up (idea, techniques investigated, where/why it fails, the key
counterexamples, lessons) — plus a `papers/` subfolder with that
approach's manuscripts. Code artifacts (probes, reasoners, the Lean
development) are **linked** from each `Overview.md` to their canonical
locations (`verification/python/`, `src/`, `formal/`) rather than moved,
to avoid breaking imports, the WP ledger, and the Lean build.

Approaches, in rough order tried:

1. **`Tableaux/`** — naive tableau + blocking (triangle/quadruple types,
   profile/double blocking); the cover-tree tableau; the one-point
   extension problem and dormant-∀ / re-qualification failures.
2. **`FiniteModel_TwoTier/`** — finite-bound / enumerate-and-check;
   PP/PPI cluster-collapse; the two-tier quotient; the MSO encoding; the
   **∀PO-free decidable fragment** (a genuine win).
3. **`SplitForest/`** — the split-forest normal form (Theorem A), the
   sound semantic foundation everything downstream consumes.
4. **`NoAutomataCertificate/`** — the rounds-2–10 hand certificate that
   converged onto an automaton.
5. **`Automata_Parity/`** — the two-way parity tree-automaton route that
   "consumed" the split forests (Theorems A/B/C).
6. **`Lean_F6/`** — the Lean formalization line culminating in the
   conditional decidability theorem and the reduction to F6 (see also
   `../LEAN.md`).
7. **`RegularCovers/`** — the regular-cover pivot; the certified RCC5
   normal form; the same ∀PO-free result.

Full state before this reorganization is preserved in the git tag
`pre-restructure-2026-07-16` and (locally) in `_backup_2026-07-16/`.
