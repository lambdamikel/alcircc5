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

**Status (2026-05-29): strongly supported, NOT mechanically certified.** GPT-5.5's round-9 forced-verticalization proof closes the round-8 completeness gap (D-1) at the manuscript level. D-1 was found by a cold Opus 4.8 review of round-8 (`papers/opus4.8_review/`): round-8's cross side/tree exhaustion lemma closes the side/tree gap only on the finite, depth-bounded boundary `B_k(u)`, while a DR/PO side witness can be RCC5-composition-forced to be a proper part of an *infinite* pumped tower whose tail the bounded saturated side context cannot carry. Concrete satisfiable witness: `C0' = (∃PP.G) ⊓ (∃PO.¬X)` with `G = (∀PO.X) ⊓ (∃PP.G)` (machine-checked, `papers/opus4.8_review/rcc5_compose.py`). The cold reviewer (Opus 4.8) proposed the repair; the proof author (GPT-5.5) ratified the defect and integrated the repair into round-9 (`papers/gpt5.5_round3/`). **Do not describe the theorem as proven or mechanically certified.** GPT-5.5 itself calls round-9 "a serious proof manuscript rather than a mechanically certified theorem," and round-9 has not itself been cold-reviewed in turn. The parts most worth future formalization (per GPT-5.5): the bounded-threshold replacement lemma, the typed-equality quotient lemma, the support-closed mosaic patchwork theorem.

The most developed statement is **GPT-5.5's round-9 forced-verticalization proof** (May 29, 2026). Two documents form the no-automata pillar, plus one independent witness via parity-tree automata:

1. `papers/gpt5.5_round3/repaired_split_forest_abstract_round9_forced_verticalization.tex` -- GPT-5.5's round-9 no-automata proof (16-page sketch, May 2026). Round-9 preserves the round-7/round-8 architecture (occurrence-sensitive pair shapes `α(u,v) = (s_u, p_u, s_v, p_v, ι(u,v))` with incidence tags `ι ∈ {self, eq, up, down, side_R, front_R}`; round-8 saturated side contexts) and adds **composition-forced verticalization** to close D-1:
   - A selected DR/PO side witness is first tested for composition-forced verticalization. If its ancestor trace has a PPI-tail, an occurrence/equality mate of the witness is spliced into the generated cover relation `E_up` at a bounded threshold; the source-witness relation stays the inherited DR/PO residual pair; deep tail pairs are carried by equality-aware vertical reachability, not bounded side contexts.
   - **Monotone ancestor traces:** for a DR/PO witness `w` of `u` and a tower `u < a_1 < a_2 < …`, the trace `r_m = L(a_m, w)` has shape `DR* PO* PPI*` (monotone in DR ≻ PO ≻ PPI, PPI absorbing), because `comp(PPI,·)` never increases the rank.
   - **Bounded threshold after regular replacement:** the augmented tower descriptor (ordinary descriptor + 3-valued trace status) has finitely many values, so the first retained PPI-point is at a computable bounded height `N_thr(C0)`.
   - **Global residual frontier:** after equality closure, finite containment saturation, and forced verticalization, every remaining residual-frontier pair has label DR or PO.

2. `papers/gpt5.5_round3/expanded_split_forest_full_details_round9_forced_verticalization.tex` -- detailed round-9 companion (33 pages). Full forced-verticalization construction with the three lemmas above plus the splice-faithfulness lemma; split-cover and extraction updated to apply the forced-verticalization test before ordinary side-context attachment.

3. `papers/gpt5.5_round3/formal_response_opus48_round9_repair.tex` -- GPT-5.5's 5-page response memo confirming D-1 and stating the repair (ran the three Opus 4.8 scripts, all pass).

4. `papers/gpt5.5_final/split_forest_automata_decidability_proof_detailed.tex` -- alternative parity-tree-automata route (21 pages). Same decidability theorem via reduction to non-emptiness of a parity tree automaton. Retained as an independent witness, not as the canonical statement.

Claude's [round-7 audit/response](papers/gpt5.5_final/claude_round7_audit_response.tex) (9 pages) maps round-6 (G1)–(G6) and round-7 (D1)–(D5) to their resolutions in GPT-5.5's round-7 architecture, and documents the three self-contained Python verifications.

**Superseded** (retained as historical audit trail in `papers/gpt5.5_round2/`):
- `repaired_split_forest_no_automata_proof.tex` (round-4, 31 pages)
- `repaired_split_forest_no_automata_proof_v2.tex` (Claude's round-5 (M6') delta, 15 pages)
- `repaired_split_forest_no_automata_proof_items4to8.tex` (Claude's round-5 items 4-8 delta, 12 pages)
- `repaired_split_forest_no_automata_proof_v2_consolidated.tex` (Claude's round-5 consolidation, 36 pages)
- `repaired_split_forest_no_automata_proof_v2_consolidated_round6.tex` (Claude's round-6 internal-coherence pass, 39 pages)
- `papers/gpt5.5_final/repaired_split_forest_all_in_one_round7.tex` (GPT-5.5's round-7 sketch, 14 pages)
- `papers/gpt5.5_final/expanded_split_forest_full_details_proof.tex` (GPT-5.5's round-7 expanded companion, 28 pages)

The round-6 critical defect found in GPT-5.5's round-7 review: in round-6, `lab(u,v) := L_Q(q(u), q(v))` with `L_Q(π, π) = EQ` collapses distinct laps of a blocking cycle into semantic equality. The defect is intrinsic to indexing labels by position-symbol pairs and cannot be locally patched. GPT-5.5's round-7 fix (incidence tags on pair shapes) is structural; round-8 preserves round-7's pair-shape architecture and adds the saturated side-context construction described above.

The round-7 defects found in the cold Claude review: (i) missing side/tree pair exhaustion; (ii) residual DR/PO frontier imposed before saturation; (iii) pair/triple catalogues bounded but not constructed. GPT-5.5's round-8 fix closes all three via the saturated side-context S_k(u), the cross side/tree exhaustion lemma, and the constructed Pair_Q / Tri_Q catalogues. **But** the cold Opus 4.8 review of round-8 found that this closes the side/tree gap only on the *finite* boundary; the D-1 completeness gap (infinite-tower case) is the open issue described in the Status note above. The round-8 manuscripts carry an editorial status note flagging D-1.

**Verification scripts.** Claude's role is verification + audit + documentation. Self-contained Python verification scripts under `verification/python/`:
- `wp7_selfcontained_side_witness.py` -- comparable side witnesses stress
- `wp8_round7_blocking_chain.py` -- blocking-not-equality stress (round-7 central repair, still load-bearing in round-8/9)
- `wp9_round7_split_copies.py` -- split copies for incomparable proper superparts
- `wp10_round9_forced_verticalization.py` -- round-9 forced-verticalization certificate-**emission** test: drives `C0'` end-to-end through DETECT (forced ancestor trace + threshold) → SPLICE (derive, not hand-place, the `E_up` edge) → BUILD (tagged certificate, tower regularized to a request-closed cycle) → VALIDATE (round-9 clauses: converse, V6 composition, universal safety, V9 equality, request discharge, residual-frontier ⊆ {DR,PO}). Emits a VALID certificate for `C0'` and REJECTS the UNSAT sibling (all routings fail). Negative-controlled (the validator catches the D-1 residual-frontier violation when the splice is withheld).
- `wp11_general_forced_verticalization.py` -- **general** forced-verticalization engine + oracle cross-check: generalizes WP10 from the single `C0'` witness to a parameterized family (period-p tower profiles, many side witnesses with arbitrary source relations and negative-literal payloads, universals over {PO,PPI,DR,PP}). For each spec it runs the full DETECT→ROUTE→BUILD→VALIDATE pipeline and cross-checks the emit/REJECT verdict three ways: against a by-construction oracle (`family_status`), against the independent validator on the concrete certificate, and (period-1, finitely encodable, closure ≤ 20) against the cover-tree tableau decision procedure. Result on the current sweep (216 specs): **216/216** engine-vs-by-construction agreement, **0** invalid certificates, **32/32** tableau confirmations — i.e. no round-9 completeness/soundness gap found on this family. Honest scope: it does NOT yet stress the hardest part of obligation D — witnesses that are proper parts of *each other* or that share superparts (overlap amalgams), where simultaneous splices could genuinely interact; the splice pass is written as a fixpoint so that extension is structural. The harness has teeth: it caught a real composition bug in its own inter-witness labeling during development, and the negative control catches D-1.

All pass. They corroborate the central stress concepts that round-7 introduced and round-8/9 preserve. WP10 fulfils the round-8 review's recommendation to add `C0'` (and its UNSAT sibling) as a constructive certificate-emission test, exercising the round-9 infinite-tower/forced-verticalization machinery that wp7-9 did not; WP11 generalizes that test across the forced-verticalization axes with an independent oracle cross-check. The D-1 composition arithmetic and the proposed-repair certificates are machine-checked under `papers/opus4.8_review/` (`rcc5_compose.py`, `fix_feasibility.py`, `repaired_certificate.py`).

Claude's earlier completeness-extraction papers (`papers/completeness_extraction_ALCIRCC5.tex` = v1, and `papers/completeness_extraction_ALCIRCC5_v2.tex` = v2.1) are **superseded** by GPT-5.5's round-8 proof and kept for historical reference. Do not cite them as the current completeness pillar.

**No complexity bound is asserted for the full logic.** Plain ALCI is EXPTIME-complete (known). ALCI_RCC8 is EXPTIME-hard (Wessel lower bound). The PO-coherent fragment's quotient bound is 2-EXPTIME (`papers/two_tier_quotient_ALCIRCC5.tex`). The round-7 / round-8 proof commits only to an effectively computable bound on the certificate space. Do not reintroduce an EXPTIME upper-bound claim for the full logic -- that was tied to the retracted quasimodel paper.

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
