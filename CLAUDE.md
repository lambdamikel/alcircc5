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

The current decidability argument for ALCI_RCC5 rests on **two papers** (as of May 2026, post Option 4):

1. `papers/trees/sibling_interface_descriptors_ALCIRCC5_completed_eqsync_canonical_needpatched.tex` -- GPT-5.4's v1 split-forest paper. Proves the quotient-to-model (soundness) direction in full detail (Thms 1.17-1.19). A delta paper `papers/sibling_interface_descriptors_ALCIRCC5_v2.tex` replaces the surrounding Def 1.5 / Def 1.7 / Thm 1.20-sketch with the corrected generated-cover statements; the proofs of 1.17-1.19 carry over verbatim.
2. `papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.tex` -- GPT-5.5's repaired split-forest decidability proof (May 2026, 16 pages, no-automata route). Formulates rank-d split-forest certificates with ten finite-checkable validity conditions (V1)-(V10) and proves **both directions** in their entirety, including the model-to-quotient (completeness) direction. The three structural ingredients that make the proof go through are (i) occurrence-level equality, (ii) mates with different parents, and (iii) request-closed cycles in place of omega-acceptance.

Claude's earlier completeness-extraction papers (`papers/completeness_extraction_ALCIRCC5.tex` = v1, and `papers/completeness_extraction_ALCIRCC5_v2.tex` = v2.1) are **superseded** by GPT-5.5's repaired proof and kept for historical reference. Do not cite them as the current completeness pillar.

**No complexity bound is asserted for the full logic.** Plain ALCI is EXPTIME-complete (known). ALCI_RCC8 is EXPTIME-hard (Wessel lower bound). The PO-coherent fragment's quotient bound is 2-EXPTIME (`papers/two_tier_quotient_ALCIRCC5.tex`). The repaired proof's coarse bound is B(C_0) = 2^(2^p(n)) (doubly exponential). Do not reintroduce an EXPTIME upper-bound claim for the full logic -- that was tied to the retracted quasimodel paper.

Both directions rely on the **patchwork property** of RCC5/RCC8 (Renz & Nebel 1999): path-consistent atomic constraint networks are globally consistent.

## Computational Verification (WP1-WP6)

Six Python work packages under `verification/python/` cross-check the finite combinatorial content of the repaired proof. All six **PASS**, no counterexample found:

- WP1: RCC5 composition table by exhaustive subset enumeration
- WP2: bounded certificate-soundness fuzzing for (V1)/(V3)/(V4)/(V5)/(V9)/(V10)
- WP3: small-model SAT/UNSAT oracle
- WP4: multiple-superpart C_AB stress (folded into WP2/WP3)
- WP5: request-closed blocking-cycle tests (folded into WP2)
- WP6: mosaic closure search (M1)-(M5) and (SC1)-(SC4)

## Retracted / Superseded

- `papers/decidability_ALCIRCC5.tex` -- **Retracted.** Earlier quasimodel + type-elimination approach; type elimination's Q3 anti-monotonicity caused cascade elimination (incompleteness, not unsoundness). Kept in the repo for historical reference.
- `papers/completeness_extraction_ALCIRCC5.tex` (v1) and `papers/completeness_extraction_ALCIRCC5_v2.tex` (v2.1) -- **Superseded** by GPT-5.5's repaired proof after the round-2 review found two structural defects in v1 and a residual omega-acceptance dependency in v2.1.
- The Python quasimodel reasoner `src/alcircc5_reasoner.py` is retained only as a cross-validation oracle. It is **known-incomplete** on the PO-loop pattern (e.g., `C ⊓ ∃PO.∃PO.C ⊓ ∀{PO,DR,PP,PPI}.¬C`, SAT via a 2-element symmetric loop under strong EQ identity). **SAT answers are trustworthy; UNSAT answers on cyclic-via-symmetric-role concepts are not.** The 911-concept "zero mismatches" cross-validation held because the test set did not include the blind-spot pattern.

## Key Files

- `papers/overview_ALCIRCC5.tex` -- Self-contained overview paper. Primary entry point for the current argument; cites the v1 split-forest paper and GPT-5.5's repaired proof as the two core papers, with the cover-tree tableau papers as the operational layer.
- `papers/dl2026_abstract_ALCIRCC5.tex` -- DL 2026 abstract, parallel content to the overview.
- `papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.tex` -- GPT-5.5's repaired decidability proof (current completeness pillar).
- `papers/sibling_interface_descriptors_ALCIRCC5_v2.tex` -- v2 sibling-interface delta paper (fixes v1 Def 1.5, 1.7, Thm 1.20-sketch).
- `papers/cover_tree_tableau_ALCIRCC5.tex` -- Claude's cover-tree tableau implementation paper (9 pages).
- `papers/two_tier_quotient_ALCIRCC5.tex` -- PO-coherent fragment decidability proof (12 pages).
- `papers/trees/` -- GPT-5.4's v1 split-forest and cover-tree tableau theory papers.
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
