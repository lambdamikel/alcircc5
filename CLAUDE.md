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
python3 gis_taxonomy.py               # GIS taxonomy (18 concepts, ~190s)
```

Two LaTeX passes are needed to resolve `\ref` and `\cite` cross-references. The bibliography uses `thebibliography` (inline), not BibTeX.

## Current Decidability Argument

The current decidability argument for ALCI_RCC5 rests on **two papers**:

1. `papers/trees/sibling_interface_descriptors_ALCIRCC5_completed_eqsync_canonical_needpatched.tex` -- GPT-5.4's split-forest paper. Proves the quotient-to-model (soundness) direction in full detail (Thms 1.17-1.19).
2. `papers/completeness_extraction_ALCIRCC5.tex` -- Claude's completeness extraction paper (11 pages). Closes the model-to-quotient (completeness) direction that GPT left as a proof sketch.

**No complexity bound is asserted for the full logic.** Plain ALCI is EXPTIME-complete (known). ALCI_RCC8 is EXPTIME-hard (Wessel lower bound). The PO-coherent fragment's quotient bound is 2-EXPTIME (`papers/two_tier_quotient_ALCIRCC5.tex`). Do not reintroduce an EXPTIME upper-bound claim for the full logic -- that was tied to the retracted quasimodel paper.

Both directions rely on the **patchwork property** of RCC5/RCC8 (Renz & Nebel 1999): path-consistent atomic constraint networks are globally consistent.

## Retracted / Superseded

- `papers/decidability_ALCIRCC5.tex` -- **Retracted.** Earlier quasimodel + type-elimination approach; type elimination's Q3 anti-monotonicity caused cascade elimination (incompleteness, not unsoundness). Kept in the repo for historical reference.
- The Python quasimodel reasoner `src/alcircc5_reasoner.py` is retained only as a cross-validation oracle. It is **known-incomplete** on the PO-loop pattern (e.g., `C ⊓ ∃PO.∃PO.C ⊓ ∀{PO,DR,PP,PPI}.¬C`, SAT via a 2-element symmetric loop under strong EQ identity). **SAT answers are trustworthy; UNSAT answers on cyclic-via-symmetric-role concepts are not.** The 911-concept "zero mismatches" cross-validation held because the test set did not include the blind-spot pattern.

## Key Files

- `papers/overview_ALCIRCC5.tex` -- Self-contained overview paper (9 pages). Cites all four core papers. Primary entry point for the current argument.
- `papers/completeness_extraction_ALCIRCC5.tex` -- Claude's completeness-extraction paper (closes the model-to-quotient gap).
- `papers/cover_tree_tableau_ALCIRCC5.tex` -- Claude's cover-tree tableau implementation paper (9 pages).
- `papers/two_tier_quotient_ALCIRCC5.tex` -- PO-coherent fragment decidability proof (12 pages).
- `papers/trees/` -- GPT-5.4's split-forest and cover-tree tableau theory papers.
- `papers/LRCC8_vs_ALCIRCC8.tex` -- Why the Lutz-Wolter undecidability of L_RCC8 does not transfer to ALCI_RCC8; documents priority claims relative to Wessel's 2002/2003 report.
- `src/cover_tree_tableau.py` -- Cover-tree tableau implementation (~350 lines).
- `src/alcircc5_reasoner.py` -- Quasimodel-based reasoner (cross-validation oracle; see caveat above).
- `src/decomposition_test.py` -- Cover-tree decomposition test (775/775 = 100%).
- `src/stress_test_cover_tree.py` -- Cross-validation suite (911 concepts, 0 mismatches post-fix).
- `src/gis_taxonomy.py` -- GIS taxonomy computation (18 concepts, 21/21 subsumptions from report7.pdf).
- `README.md` -- Full project description with complexity landscape and all approach summaries.
- `CONVERSATION.md` -- Full conversation log. **Before modifying settled topics (citations, decidability-argument wording, EXPTIME claims, Lutz-Wolter priority), check CONVERSATION.md for the relevant audit section.** Citations were verified in April 2026.

## Technical Conventions

- Concepts are in **negation normal form** (NNF); inverse roles are absorbed (exists PP^-.C = exists PPI.C).
- **Strong EQ semantics** throughout (EQ = identity). Weak EQ reduces to strong via TBox internalization.
- The 5 base relations are DR, PO, EQ, PP, PPI. For edges between distinct nodes, only {DR, PO, PP, PPI} are used (EQ is reflexive only).
- LaTeX macros: `\ALCIRCC{5}`, `\DR`, `\PO`, `\PP`, `\PPI`, `\EQ`, `\comp`, `\cl`, `\Tp`, `\Pair`, `\Trip`, `\EXPTIME`, `\PSPACE`.
- **Terminology.** Canonical name for the semantic framework is "split-forest model" (not "split-tree forest model"). The formal data object is a "weak-EQ split-tree presentation": one tree per connected component, produced by splitting join nodes into EQ-mates. A "split-forest" is the collection of such split-trees.
