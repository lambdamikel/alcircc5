# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What This Repository Is

This is a **description logic research paper**, not a software project. It contains a proof that concept satisfiability in ALCI_RCC5 and ALCI_RCC8 is decidable (EXPTIME upper bound), settling open problems from Wessel (2002/2003). The paper was authored by Claude, prompted by Michael Wessel (miacwess@gmail.com, GitHub: lambdamikel).

The results are **unverified** and published as a discussion piece for the DL community.

## Build

Compile the paper:
```
pdflatex -interaction=nonstopmode decidability_ALCIRCC5.tex
pdflatex -interaction=nonstopmode decidability_ALCIRCC5.tex  # second pass for references
```

Two passes are needed to resolve `\ref` and `\cite` cross-references. The bibliography uses `thebibliography` (inline), not BibTeX.

## Key Files

- `decidability_ALCIRCC5.tex` -- The main paper (LaTeX). 19 pages, self-contained.
- `decidability_proof_ALCIRCC5.md` -- Earlier markdown proof sketch (quasimodel method only, no tableau).
- `README.md` -- Contains a full standalone description of the tableau calculus.
- `CONVERSATION.md` -- Full conversation log between Michael Wessel and Claude that produced this work.

## Paper Structure

The paper has two independent decision procedures for the same problem:

1. **Quasimodel method + type elimination** (Sections 4-6): Abstract types/pair-types/triple-types, quasimodel definition, soundness/completeness via Henkin construction, EXPTIME type-elimination algorithm.

2. **Tableau calculus with blocking** (Section 7): Complete-graph completion structures, expansion rules (the exists-rule assigns roles to ALL existing nodes), equality anywhere-blocking, constraint filtering via composition table. Soundness is indirect: extract quasimodel from open branch, then invoke Henkin construction.

Both rely on the **patchwork property** of RCC5/RCC8 (Renz & Nebel 1999): path-consistent atomic constraint networks are globally consistent. This is defined in Section 2.2.

## Technical Conventions

- Concepts are in **negation normal form** (NNF); inverse roles are absorbed (exists PP^-.C = exists PPI.C).
- **Strong EQ semantics** throughout (EQ = identity). Weak EQ reduces to strong via TBox internalization.
- The 5 base relations are DR, PO, EQ, PP, PPI. For edges between distinct nodes, only {DR, PO, PP, PPI} are used (EQ is reflexive only).
- LaTeX macros: `\ALCIRCC{5}`, `\DR`, `\PO`, `\PP`, `\PPI`, `\EQ`, `\comp`, `\cl`, `\Tp`, `\Pair`, `\Trip`, `\EXPTIME`, `\PSPACE`.
