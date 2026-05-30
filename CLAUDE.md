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

**Status (2026-05-30): strongly supported, NOT certified. The automata route was cold-reviewed (5th cold review) and repaired; canonical statement is now the repaired automata proof + its A/B/C companion.** The decidability theorem is plausible and the split-forest *semantic normal form* (witness thinning → generated containment covers → split copies → side-interface mosaics → typed-EQ quotient) has been repeatedly found sound. What no manuscript has yet done is survive a cold review without a new defect. The parity-tree-automata route promoted to primary on 2026-05-29 was then cold-reviewed (`papers/automata_route_repairs/`) and found to have the **same keystone gap as the no-automata route**; GPT-5.5 repaired it. The **canonical statement is now GPT-5.5's repaired automata proof + A/B/C companion** in `papers/automata_route_repairs/`: `split_forest_automata_repaired_full_proof.tex` (19pp) and `split_forest_companion_ABC_paper.tex` (18pp); the earlier `papers/gpt5.5_final/split_forest_automata_decidability_proof_detailed.tex` is superseded. **Do not describe the theorem as proven or certified, and do not describe the repaired proof / Theorem B as cold-reviewed — they have not been.**

**Why the switch (the no-automata thread converged onto an automaton).** Across rounds 2–10 the no-automata route repeatedly reduced to automaton-shaped machinery it could not fully discharge: request-closed cycles ≈ Büchi/parity acceptance; "finite product-state exhaustion" ≈ product-automaton reachability. The round-9 proof (`papers/gpt5.5_round3/`) was cold-reviewed by a fresh GPT-5.5 session (via the `papers/cold_review_round9/` packet); the referee report (`papers/gpt5.5_round4/referee_response_alci_rcc5.tex`) found, with machine-checked composition arithmetic:
   - **Critical 1 — one-sided verticalization.** Round-9 handled a DR/PO witness forced into an infinite *ancestor* PPI-tower but missed the dual *descendant* PP-tower. Witness `C = (∃PO.A) ⊓ (∃PPI.⊤) ⊓ ∀PPI.(∃PPI.⊤ ⊓ ∀DR.¬A ⊓ ∀PO.¬A)` (machine-checked in `verification/python/wp12_round10_dual_descendant_verticalization.py`).
   - **Critical 2 — finite-checkability never proved.** V6/V7 were *asserted* to be finite syntactic checks but quantify over the infinite unfolding; the finite catalogues were never shown to exhaust it.
   - **Critical 3 — boundary non-determinacy.** Boundary descriptors do not determine mixed outside/internal labels (`i PP b, o PO b ⟹ L(o,i) ∈ {DR,PO,PPI}`).
   - Plus four majors including a *false* simple-cycle bound (a request-closed cycle may need a closed walk that revisits descriptors).

   Round-10 (`papers/gpt5.5_round4/`) accepts all findings and repairs them: dual splice, occurrence-local requests, ranked side-width, global-quotient-first extraction, a corrected `(M+1)N` closed-walk bound, and — for Critical 2/3 — **finite product-state exhaustion** and **complete interface descriptors**. A deep read of `expanded_split_forest_full_details_round10_merged.tex` found the entire decidability burden now funnels into exactly two named lemmas (Finite Product Exhaustion, Complete-Interface Replacement), both proved by case-list + "the alphabets are finite" + "the descriptor prescribes it" — i.e. asserted, not discharged, and both automaton-shaped. The convergent move is therefore to use the automaton directly.

**The automata proof keeps the split-forest model idea; it only replaces the brittle half.** Per its own §"Why this proof keeps the split-forest idea": *"the automaton does not replace the split forest. It consumes it."* It retains witness thinning, generated containment covers, split copies, side-interface mosaics, and typed-EQ quotient (the sound semantic normal form, shared verbatim with the no-automata thread), and uses a parity tree automaton over the finite split-forest profile alphabet — decided by **non-emptiness** — only for "the parts that were most brittle in a hand certificate: regular infinite branches, simultaneous eventuality fulfillment, recursive side contexts, and profile repetition without semantic equality." Parity-tree-automaton non-emptiness is decidable by construction, so the finite-checkability and eventuality keystones the no-automata route could not discharge come for free.

**The 2026-05-29 promotion was strategic, not a proof upgrade — and the automata route was then cold-reviewed (5th cold review) and had the same gap.** A fresh GPT-5.5 session reviewed it (`papers/automata_route_repairs/rcc5_split_forest_referee_report.tex`) and found that the automata route's `Patch` invariant — that a finite *local* check guarantees *global* RCC5 composition + universal propagation to all composition-forced targets + equality congruence — was **assumed, not constructed**, and that the "automaton" was prose, not a total finite transition function. Concrete UNSAT concepts it would wrongly accept: `C_force = ∃PP.(∃DR.A) ⊓ ∀DR.¬A` (`x PP y, y DR z ⟹ x DR z` forced via `comp(PP,DR)={DR}`, so `∀DR.¬A` kills `z:A`), `C_split = ∃PP.(A ⊓ ¬B ⊓ ∀PP.¬B ⊓ ∀PPI.¬B ⊓ ∀PO.¬B) ⊓ ∃PP.B`, `C_recursive = ∃DR.(A ⊓ ∃DR.B)`. Composition table re-verified correct; witness thinning sound. So the automata route had the no-automata route's keystone gap all along.

**GPT-5.5's repair, and the convergence point.** GPT-5.5 accepted all findings and produced a repaired proof + an **A/B/C companion paper**. The central fix is **finite pair/triple product-state representatives** (computed from nearest-common-interface transformers) — the *same* convergent idea as round-10's product-state exhaustion in the no-automata route. The ABC paper isolates the argument into **Theorem A** (split-forest normal form — shared, found sound), **Theorem B** (finite abstraction adequacy: finite frontier/pair/triple/equality-port abstractions capture saturated split forests up to satisfiability of all closure formulas), and **Theorem C** (a finite alternating parity tree automaton accepts exactly the valid abstractions). **Theorem B is the single load-bearing keystone — and it is the same keystone both routes converged on** (round-10's "finite product-state exhaustion" / "complete interface descriptors" are Theorem B in the no-automata packaging). So the project has cleanly *identified* the one hard theorem; whether it is *proved* is the open question. GPT-5.5 itself flags the product-state frontier construction and the equality-congruence proof as "the sections most deserving of independent review or mechanization." The repaired proof + ABC paper have **not** been cold-reviewed in turn; by the track record (5 cold reviews, 5 defects), Theorem B is where the next review should aim. Status remains *strongly supported, not certified*. Natural next step: cold-review the repaired proof / Theorem B (the `papers/cold_review_round9/` packet repurposes). On the verification side, WP1 + the SAT/UNSAT oracles + WP7–WP9 (Theorem A stress) stay valid; WP2/WP10–WP12 are historical (no-automata certificate machinery); nothing yet exercises Theorem B — a `wp13` driving the referee's four acceptance tests (`C_force`, `C_split`, `C_recursive`, `C_↑`) through the repaired construction is the natural new artifact.

The no-automata thread (rounds 2–10) is retained as the historical audit trail, **not retracted as wrong** — its repeatedly-rediscovered keystones (finite checkability, simultaneous eventuality fulfillment) are exactly what the automaton discharges by construction. See `OUTDATED.md` ("The no-automata split-forest thread") for the full progression: round-7 incidence-tag fix (the round-6 `L_Q(π,π)=EQ` lap-collapse defect); round-8 saturated side contexts; the cold Opus 4.8 review finding D-1 (the ancestor-tower gap); round-9 forced verticalization closing D-1; the round-9 cold review finding the dual descendant case + the two foundational gaps; round-10's product-state-exhaustion repair. Manuscripts: `papers/gpt5.5_round2/` (rounds 4–6), `papers/gpt5.5_final/repaired_split_forest_all_in_one_round7.*` + `expanded_split_forest_full_details_proof.*` (round 7), `papers/claude_latest_review_gpt5.5_fix/` (round 8), `papers/gpt5.5_round3/` (round 9), `papers/gpt5.5_round4/` (round 10).

**Verification scripts.** Claude's role is verification + audit + documentation. Self-contained Python verification scripts under `verification/python/`:
- `wp7_selfcontained_side_witness.py` -- comparable side witnesses stress
- `wp8_round7_blocking_chain.py` -- blocking-not-equality stress (round-7 central repair, still load-bearing in round-8/9)
- `wp9_round7_split_copies.py` -- split copies for incomparable proper superparts
- `wp10_round9_forced_verticalization.py` -- round-9 forced-verticalization certificate-**emission** test: drives `C0'` end-to-end through DETECT (forced ancestor trace + threshold) → SPLICE (derive, not hand-place, the `E_up` edge) → BUILD (tagged certificate, tower regularized to a request-closed cycle) → VALIDATE (round-9 clauses: converse, V6 composition, universal safety, V9 equality, request discharge, residual-frontier ⊆ {DR,PO}). Emits a VALID certificate for `C0'` and REJECTS the UNSAT sibling (all routings fail). Negative-controlled (the validator catches the D-1 residual-frontier violation when the splice is withheld).
- `wp11_general_forced_verticalization.py` -- **general** forced-verticalization engine + oracle cross-check: generalizes WP10 from the single `C0'` witness to a parameterized family (period-p tower profiles, many side witnesses with arbitrary source relations and negative-literal payloads, universals over {PO,PPI,DR,PP}). For each spec it runs the full DETECT→ROUTE→BUILD→VALIDATE pipeline and cross-checks the emit/REJECT verdict three ways: against a by-construction oracle (`family_status`), against the independent validator on the concrete certificate, and (period-1, finitely encodable, closure ≤ 20) against the cover-tree tableau decision procedure. Result on the current sweep (216 specs): **216/216** engine-vs-by-construction agreement, **0** invalid certificates, **32/32** tableau confirmations — i.e. no round-9 completeness/soundness gap found on this family. Honest scope: it does NOT yet stress the hardest part of obligation D — witnesses that are proper parts of *each other* or that share superparts (overlap amalgams), where simultaneous splices could genuinely interact; the splice pass is written as a fixpoint so that extension is structural. The harness has teeth: it caught a real composition bug in its own inter-witness labeling during development, and the negative control catches D-1.
- `wp12_round10_dual_descendant_verticalization.py` -- machine-checks the round-9 **cold review's Critical-1 dual case** (the descendant PP-tower the ancestor-only round-9 missed) and round-10's dual-splice repair. Mirror of WP10: drives `C = (∃PO.A) ⊓ (∃PPI.⊤) ⊓ ∀PPI.(∃PPI.⊤ ⊓ ∀DR.¬A ⊓ ∀PO.¬A)` through DETECT (descendant trace `comp(PP,·)`, shape DR\*PO\*PP\*, PP absorbing) → SPLICE (splice `w` as the descendant-tower superpart, `d_{k0} PP w`) → BUILD → VALIDATE. Emits VALID for `C`, REJECTs the UNSAT sibling (add `∀PP.B`, `w∈¬B`), negative-controlled (catches the dual-D-1 residual-frontier violation). Confirms Critical-1's repair is sound at the emission level — but says nothing about round-10's two unproven keystones (product exhaustion, complete-interface), which are not machine-checkable this way.

NOTE: WP10–WP12 verify the *no-automata* thread's certificate machinery (now the historical thread). They remain valid corroboration of the split-forest semantic content but are not the canonical decision procedure. If/when the automata route is the working pillar, the analogous artifact is a non-emptiness check of the parity tree automaton; not yet implemented.

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

- `papers/automata_route_repairs/split_forest_automata_repaired_full_proof.tex` + `split_forest_companion_ABC_paper.tex` -- **the canonical decidability statement** (repaired split-forest automata proof, 19pp, + A/B/C companion isolating Theorem A normal form / Theorem B finite-abstraction keystone / Theorem C automaton, 18pp). See "Current Decidability Argument" above. NOT cold-reviewed in turn; Theorem B is the load-bearing keystone. `papers/automata_route_repairs/rcc5_split_forest_referee_report.tex` is the 5th cold review (found the keystone gap); `formal_response_automata_referee_repair.tex` is GPT-5.5's response.
- `papers/gpt5.5_final/split_forest_automata_decidability_proof_detailed.tex` -- the earlier (21-page) automata proof, **superseded** by the repaired version after the 5th cold review found its `Patch` invariant assumed-not-constructed.
- `papers/overview_ALCIRCC5.tex` -- Self-contained overview paper. Primary entry point for the argument; cites the v1 split-forest paper and (as of 2026-05-29) the automata proof as the core decidability pillar, with the cover-tree tableau papers as the operational layer.
- `papers/dl2026_abstract_ALCIRCC5.tex` -- DL 2026 abstract, parallel content to the overview.
- `papers/gpt5.5_round4/` -- round-10 no-automata manuscripts + the round-9 cold-review referee report (`referee_response_alci_rcc5.*`) + GPT-5.5's response (`formal_response_referee_round10.*`). Historical thread; `expanded_split_forest_full_details_round10_merged.*` is the full round-10 expanded proof (the `_corrected` files are a lossy delta).
- `papers/cold_review_round9/` -- drag-and-drop cold-review packet (neutralized PDFs + prompt + withhold-list). Repurposable for cold-reviewing the automata proof.
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
