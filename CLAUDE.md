# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What This Repository Is

This is a **description logic research project** investigating the decidability of concept satisfiability in ALCI_RCC5 and ALCI_RCC8, open problems from Wessel (2002/2003). The repository contains papers (LaTeX), implementations (Python), and documentation. The work was produced by AI assistants (Claude/Anthropic and GPT-5.4/OpenAI), prompted by Michael Wessel (miacwess@gmail.com, GitHub: lambdamikel).

The results are **unverified** and published as a discussion piece for the DL community.

## Repository Structure

- `papers/` -- All LaTeX sources, PDFs, and paper subdirectories (trees/, gpt/, review*/)
- `src/` -- All Python implementations (reasoners, tests, verification scripts)
- Root -- README.md, CONVERSATION.md, CLAUDE.md, OUTDATED.md

## Build

Compile papers:
```
cd papers
pdflatex -interaction=nonstopmode decidability_ALCIRCC5.tex
pdflatex -interaction=nonstopmode decidability_ALCIRCC5.tex  # second pass for references
```

Run tests:
```
cd src
python3 cover_tree_tableau.py          # cover-tree tableau (built-in tests)
python3 stress_test_cover_tree.py      # cross-validation (911 concepts)
python3 decomposition_test.py          # cover-tree decomposition test
python3 model_verifier.py             # independent model verification
python3 alcircc5_reasoner.py          # quasimodel reasoner (built-in tests)
```

Two LaTeX passes are needed to resolve `\ref` and `\cite` cross-references. The bibliography uses `thebibliography` (inline), not BibTeX.

## Key Files

- `papers/decidability_ALCIRCC5.tex` -- The main paper (LaTeX). 19 pages, self-contained.
- `papers/cover_tree_tableau_ALCIRCC5.tex` -- Cover-tree tableau implementation paper.
- `papers/two_tier_quotient_ALCIRCC5.tex` -- PO-coherent fragment decidability proof.
- `papers/trees/` -- GPT-5.4's split-forest and cover-tree tableau theory papers.
- `src/cover_tree_tableau.py` -- Cover-tree tableau implementation (~350 lines).
- `src/alcircc5_reasoner.py` -- Quasimodel-based reasoner.
- `src/decomposition_test.py` -- Cover-tree decomposition test (775/775 = 100%).
- `src/stress_test_cover_tree.py` -- Cross-validation suite (911 concepts, 0 mismatches).
- `README.md` -- Full project description with complexity landscape and all approach summaries.
- `CONVERSATION.md` -- Full conversation log between Michael Wessel and the AI assistants.

## Paper Structure (main paper)

The paper has two independent decision procedures for the same problem:

1. **Quasimodel method + type elimination** (Sections 4-6): Abstract types/pair-types/triple-types, quasimodel definition, soundness/completeness via Henkin construction, EXPTIME type-elimination algorithm.

2. **Tableau calculus with blocking** (Section 7): Complete-graph completion structures, expansion rules (the exists-rule assigns roles to ALL existing nodes), equality anywhere-blocking, constraint filtering via composition table. Soundness is indirect: extract quasimodel from open branch, then invoke Henkin construction.

Both rely on the **patchwork property** of RCC5/RCC8 (Renz & Nebel 1999): path-consistent atomic constraint networks are globally consistent. This is defined in Section 2.2.

## Technical Conventions

- Concepts are in **negation normal form** (NNF); inverse roles are absorbed (exists PP^-.C = exists PPI.C).
- **Strong EQ semantics** throughout (EQ = identity). Weak EQ reduces to strong via TBox internalization.
- The 5 base relations are DR, PO, EQ, PP, PPI. For edges between distinct nodes, only {DR, PO, PP, PPI} are used (EQ is reflexive only).
- LaTeX macros: `\ALCIRCC{5}`, `\DR`, `\PO`, `\PP`, `\PPI`, `\EQ`, `\comp`, `\cl`, `\Tp`, `\Pair`, `\Trip`, `\EXPTIME`, `\PSPACE`.
