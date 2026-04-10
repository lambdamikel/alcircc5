# On the Decidability of ALCI\_RCC5 and ALCI\_RCC8

**Quasimodels Meet the Patchwork Property**

> **Disclaimer.** The papers and code in this repository were produced by AI assistants (Claude/Anthropic and GPT-5.4/OpenAI), prompted by Michael Wessel. The results and proofs presented here have **not been peer-reviewed or verified by human domain experts**. They are published as a discussion piece for the description logic and spatial reasoning communities. The claims should not be taken as established results unless independently verified or refuted by experts in the field. We invite scrutiny, corrections, and feedback.

> **Status (April 2026).** Eleven approaches to ALCI\_RCC5 decidability have been attempted. The **most promising** is the [cover-tree tableau](https://github.com/lambdamikel/alcircc5/blob/master/cover_tree_tableau_ALCIRCC5.pdf) (Wessel/GPT-5.4/Claude): decompose models into PPI-oriented cover trees where only {DR, PO} remain as open cross-edges (DR rigidity), making sibling constraints trivially arc-consistent. A [working implementation](https://github.com/lambdamikel/alcircc5/blob/master/cover_tree_tableau.py) agrees with an independent [quasimodel reasoner](https://github.com/lambdamikel/alcircc5/blob/master/alcircc5_reasoner.py) on **902 test concepts with zero mismatches**. A [two-tier quotient paper](https://github.com/lambdamikel/alcircc5/blob/master/two_tier_quotient_ALCIRCC5.pdf) (Claude, reviewed by GPT-5.4) proves decidability for the **PO-coherent fragment**. The decidability of full ALCI\_RCC5 and ALCI\_RCC8 remains **open**. See the [conversation log](https://github.com/lambdamikel/alcircc5/blob/master/CONVERSATION.md) for the full history.

## Why this problem is still open: Lutz & Wolter (2006) does not settle it

Readers familiar with Lutz and Wolter's "Modal Logics of Topological Relations" (LMCS 2006) may wonder whether their undecidability results already resolve the decidability of ALCI\_RCC5 and ALCI\_RCC8. **They do not.** The Lutz-Wolter results concern logics with *topological* semantics (L\_RCC8, L\_RCC5(RS^∃)), which are different from the *abstract composition-table* semantics of the ALCI\_RCC family introduced by Wessel (2002/2003).

- **L\_RCC8 is undecidable** (domino tiling via TPP/NTPP chains). This does **not** transfer to ALCI\_RCC8 because the reduction requires a *grid coincidence condition* (east-of-north = north-of-east) that topological geometry forces but the composition table does not. This **coincidence obstruction** was first identified by Wessel in 2002/2003 ([report7.pdf](https://github.com/lambdamikel/alcircc5/blob/master/report7.pdf), Section 4.4.3, Figure 11). See the [full analysis (PDF)](https://github.com/lambdamikel/alcircc5/blob/master/LRCC8_vs_ALCIRCC8.pdf) and the [detailed discussion below](#why-lutz--wolters-rcc8-undecidability-proof-doesnt-transfer-to-alci_rcc8-either).

- **L\_RCC5(RS^∃) is undecidable** (S5³ via supremum regions). This does **not** transfer to ALCI\_RCC5 = L\_RCC5(RS) because abstract models lack supremum closure. Lutz & Wolter themselves explicitly state (p. 31): *"Perhaps the most interesting candidate is L\_RCC5(RS) [...] to which the reduction exhibited in Section 8 does not apply."* See the [detailed discussion below](#why-lutz--wolters-rcc5-undecidability-proof-doesnt-transfer).

Both problems — ALCI\_RCC5 and ALCI\_RCC8 satisfiability — have been **open for over 20 years** (Wessel 2002/2003, Lutz-Wolter 2006). No known undecidability reduction applies to the abstract composition-table semantics. This repository documents multiple approaches toward settling them.

## Current Status of the Proof

### Status (April 2026): Strong computational evidence for decidability

**UPDATE (April 2026): Split-tree model-based tableau — most promising approach.** The [cover-tree tableau](https://github.com/lambdamikel/alcircc5/blob/master/cover_tree_tableau.py) decomposes ALCI\_RCC5 models into **PPI-oriented cover trees** with only {DR, PO} as open cross-edges between sibling subtrees. The key insight (Wessel) is that DR propagates rigidly downward — comp(PP,DR) = {DR}, comp(DR,PPI) = {DR} — leaving only {DR, PO} open after EQ-splitting, and {DR, PO} networks are **trivially arc-consistent**. GPT-5.4 Pro formalized the [split-forest semantics](https://github.com/lambdamikel/alcircc5/blob/master/trees/sibling_interface_descriptors_ALCIRCC5_completed_eqsync_canonical_patched.pdf) and [tableau calculus](https://github.com/lambdamikel/alcircc5/blob/master/trees/alcircc5_cover_tree_tableau_needslots_patched.pdf); Claude implemented and [cross-validated](https://github.com/lambdamikel/alcircc5/blob/master/stress_test_cover_tree.py) against the quasimodel reasoner on **902 test concepts with zero mismatches**. This approach correctly handles all 7 cyclic-model concepts (which lack tree models) and all cross-role UNSAT patterns. The soundness direction is convincing (patchwork property of RCC5); the completeness direction (model → quotient extraction) has a condensed gap. See the [implementation paper (PDF)](https://github.com/lambdamikel/alcircc5/blob/master/cover_tree_tableau_ALCIRCC5.pdf) and the [eleventh approach section](#eleventh-approach-cover-tree-tableau--most-promising-wesselgptclaude) for full details.

**Earlier: Quadruple-type candidate decision procedure.** A [constructive quasimodel search](https://github.com/lambdamikel/alcircc5/blob/master/alcircc5_reasoner.py) using three necessary conditions — disjunctive path-consistency, sibling compatibility, and role-path compatibility — correctly classifies all **713 concepts** in a comprehensive [stress test](https://github.com/lambdamikel/alcircc5/blob/master/stress_test.py) with **zero correctness errors**. UNSAT answers are **provably sound** (all three checks are extractable from any model). SAT answers have strong computational evidence but lack a formal sufficiency proof. See the [quadruple-type paper](https://github.com/lambdamikel/alcircc5/blob/master/decidability_via_quadruples_ALCIRCC5.pdf) for details.

**PO-coherent fragment decidable.** A [two-tier quotient paper](https://github.com/lambdamikel/alcircc5/blob/master/two_tier_quotient_ALCIRCC5.pdf) (three rounds of GPT-5.4 Pro review) proves decidability for the **PO-coherent fragment** of ALCI\_RCC5. The remaining PO gap — PO has neither backward forcing (comp(PP,PO)={DR,PO,PP}) nor forward absorption (comp(PPI,PO)={PO,PPI}) — remains open.

### Discussion of failed and incomplete approaches

The following approaches have been **disproved, retracted, or shown incomplete**. They are documented here for transparency and because several contribute useful technical observations. See the [summary table](#summary-eleven-approaches) for a compact overview.

**1. Original quasimodel paper (Claude): DISPROVED.** The paper presents two procedures — a type elimination algorithm (Section 6) and a tableau calculus (Section 7) — and claims both decide ALCI\_RCC5 satisfiability in EXPTIME. Both claims are wrong:

- **Type elimination algorithm (Section 6): UNSOUND.** The algorithm **rejects satisfiable concepts**. The concept C₁ = ∃PO.D ⊓ ∃DR.(B ⊓ ∀PO.¬D) ⊓ ∀DR.¬D ⊓ ∀PP.¬D ⊓ ∀PPI.¬D has a valid 3-element model but the algorithm eliminates all 128 types to 0. Root cause: Q3's anti-monotonicity causes cascade elimination. Theorem 6.1 is **retracted**. See ["type elimination algorithm is unsound"](#computational-discovery-the-type-elimination-algorithm-is-unsound-rejects-satisfiable-concepts) below.

- **Tableau calculus (Section 7): SOUNDNESS UNPROVEN.** The soundness proof invokes the Henkin construction, which has the **extension gap** — 1,911 counterexamples to pairwise-implies-global solvability at m=3. Corollary 7.11 is **not established**.

- **RCC8 results: RETRACTED.** Depend on the unsound type elimination algorithm.

**2. Contextual tableau (GPT-5.4): INCOMPLETE.** Proves full soundness but reduces completeness to the finite-width conjecture FW(C,N), which is **false** — C∞ = (∃PP.⊤) ⊓ (∀PP.∃PP.⊤) requires infinite models but FW fails for every N. See [FW counterexample](#the-contextual-tableau-approach-and-the-fwcn-counterexample) below.

**3. Direct model construction (Claude): RETRACTED.** [Closing the Extension Gap (PDF)](https://github.com/lambdamikel/alcircc5/blob/master/closing_extension_gap_ALCIRCC5.pdf) attempted to resolve the extension gap. GPT-5.4's [review](https://github.com/lambdamikel/alcircc5/blob/master/review/review_closing_extension_gap_ALCIRCC5.pdf) found two errors: algebraic error in Lemma 3.2 (comp(DR,PP) = {DR,PO,PP}, not {DR}) and Theorem 5.5 is false (DN\_safe domains too coarse). Both [computationally verified](https://github.com/lambdamikel/alcircc5/blob/master/response_to_gpt_review.pdf) and accepted.

**4–5. Profile-cached blocking and meet-based replay (GPT-5.4): INCOMPLETE.** Both fail at the unraveling step where the color structure changes. Develop correct local machinery (coherent predecessor blocks, depth-indexed signatures) but cannot handle global edge assignment.

**6. Triangle-type blocking (Claude): CONDITIONAL.** Yields decidability conditional on the Extension Solvability Conjecture. The chain T-closed solution → arc-consistency → path-consistency → model is rigorous, but the conjecture is unproven. See [triangle-type section](#sixth-approach-triangle-type-blocking--conditional-decidability) below.

**7. Tri-neighborhood tableau (Claude): TERMINATION DISPROVED.** A [full implementation](https://github.com/lambdamikel/alcircc5/blob/master/triangle_calculus.py) reveals **genuine non-termination** via unbounded frontier advancement. The concept `A ⊓ ∃PP.A ⊓ ∀PP.(∃PP.A ⊓ ∃DR.B)` forces an infinite PP-chain; frontier nodes have Tri ⊂ interior Tri and are never blocked. The blocking dilemma (soundness requires Tri-matching; termination requires ignoring Tri) remains open. See [Tri-neighborhood details](#eighth-approach-tri-neighborhood-tableau--termination-disproved) below.

**8. MSO encoding (Claude): ONE GAP.** Reduces ALCI\_RCC5 to Shelah's decidable MSO(R,<) via interval semantics, but MSO-definability of Dyck matching in the ambient structure is unresolved.

**The structural wall (approaches 1–5).** All five approaches fail at the same point: assigning globally consistent edges in a complete-graph model. Type-based quotients are too coarse to preserve relational information needed for path-consistency across the full unraveling. The root cause is the combination of (i) transitivity of PP, (ii) universal propagation along PP-chains, and (iii) the complete-graph requirement. The cover-tree tableau (eleventh approach) avoids this wall by decomposing complete-graph models into trees with {DR,PO}-only cross-edges.

**What survives from failed approaches.** The unique self-absorption failure PPI ∉ comp(DR, PPI) = {DR} (containment collapse) is the algebraic source of difficulty. The forced DR edge (Lemma 4.1) and self-safety theorem (S ∈ comp(S,S) for all S) are correct and reused in later approaches.

### The contextual tableau approach and the FW(C,N) counterexample

A companion note by GPT-5.4 Pro ([A Contextual Tableau Calculus for ALCI\_RCC5 (PDF)](https://github.com/lambdamikel/alcircc5/blob/master/ALCI_RCC5_contextual_tableau_draft.pdf)) proposed a different framework: a **contextual tableau calculus** where each tableau node is a finite local state — a bounded-width atomic RCC5 network with witness assignments and recentering maps. That paper is the starting point for the FW(C,N) discussion below. It proves full **soundness** (every open tableau graph unfolds into a genuine model) but reduces completeness to the **finite-width extraction conjecture FW(C,N)**: every satisfiable concept admits a closed family of local states of bounded width N(C).

**FW(C,N) is false.** The counterexample is the concept already noted in Wessel (2003) and in our paper (Remark 2.5):

> C∞ = (∃PP.⊤) ⊓ (∀PP.∃PP.⊤)

This concept is satisfiable only in infinite models. The proof that FW(C∞, N) fails for **every** N is elementary:

1. Transitive propagation (L2) forces every PP-descendant to have ∃PP.⊤ in its type — each needs a PP-successor.
2. The recentering axiom (R3) forces the PP-witness in any successor state to map to a PP-successor of the corresponding item **in the parent state**.
3. Iterating this produces an infinite PP-chain inside a single finite-width state.
4. But PP is a **strict partial order** (irreflexive + transitive). Every finite strict partial order has maximal elements. Maximal elements have no PP-successor. Contradiction.

See the [full counterexample proof (PDF)](https://github.com/lambdamikel/alcircc5/blob/master/FW_proof_ALCIRCC5.pdf) for details. The same argument applies to ALCI\_RCC8 using NTPP in place of PP.

### Summary: eleven approaches

| | Quasimodel (Claude) | Contextual tableau (GPT) | Direct construction (Claude) | Profile-cached blocking (GPT) | Meet-based replay (GPT) | Triangle-type (Claude) | Two-tier quotient (Claude) | Tri-nbr tableau (Claude) | MSO encoding (Claude) | Quadruple-type (Claude) | Cover-tree tableau (Wessel/GPT/Claude) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Key idea | Type elimination | Local states + recentering | Tree unraveling + DN\_safe | Coherent predecessor blocks | Meet-semilattice on labels | Triangle-filtered arc-consistency | Period descriptors + PP-kernels + full RCC5 tractability | Tri-neighborhood blocking + filtered unraveling | Reduce to Borel-MSO(R,<) via interval semantics | 4-element star path-consistency for cross-branch edges | PPI-tree + EQ-splitting + {DR,PO}-only cross-edges + patchwork |
| Gap | **Algorithm unsound** (rejects satisfiable concepts); **tableau soundness unproven** (extension gap in Henkin construction); Q3 soundness bug | FW(C,N) false | Theorem 5.5 false (DN\_safe too coarse) | Color structure changes in unraveling | Same unraveling gap | Extension Solvability Conjecture | **PO gap** (exact-relation extraction fails for PO) | See honest assessment (4 specific points) | MSO-definability of Dyck matching in ambient (R,<) | Q4 gap fixed; formal sufficiency proof pending | Completeness direction condensed (model→quotient extraction) |
| Status | **Algorithm disproved; tableau not established** | Incomplete | **Retracted** | Incomplete | Incomplete | Conditional | **PO-coherent fragment decidable** | **Termination disproved; soundness has formal gap** (completeness valid) | **Encoding complete, one technical gap** (HS route blocked) | **Strong evidence: 3-check algorithm, 713 concepts, 0 errors** | **Most promising: 902 concepts, 0 errors, theoretically grounded** |

See the [discussion of failed and incomplete approaches](#discussion-of-failed-and-incomplete-approaches) above for a narrative summary of each approach's status.

### Sixth approach: triangle-type blocking — conditional decidability

A refined approach uses **triangle types** — tuples (τ₁, R₁₂, τ₂, R₂₃, τ₃, R₁₃) recording three Hintikka types and three pairwise RCC5 relations — to filter edge domains in the model construction. This replaces the coarse endpoint-type domains (DN\_safe) from the retracted paper with a finer filtering that requires every triple's configuration to be witnessed in the completion graph.

The approach yields a **conditional decidability result**: if the *Extension Solvability Conjecture* holds (the tree unraveling admits a T-closed solution), then ALCI\_RCC5 is decidable in EXPTIME. The conditional chain is rigorously proved:

> T-closed solution exists → arc-consistency preserves it → domains non-empty → network path-consistent → full RCC5 tractability → model exists

See [**Triangle Types and the Extension Gap (PDF)**](https://github.com/lambdamikel/alcircc5/blob/master/triangle_blocking_ALCIRCC5.pdf) for the full paper.

**Computational verification** ([`triangle_closure_check.py`](https://github.com/lambdamikel/alcircc5/blob/master/triangle_closure_check.py)) on 68,276 models (3–4 elements, 2–3 types):

| Test | Result |
|---|---|
| Strong triangle closure (STC) | Fails 100% — too strong, not needed |
| T-filtered extension CSP (all demands) | Fails 67.1% |
| T-filtered extension CSP (unsatisfied demands only) | Fails 36.3% |
| **Genuine failures** (T-closed extension exists but CSP rejects) | **0 (zero)** |
| Cross-context failures (union T, foreign model) | **0 (zero)** |

The key finding: **every extension CSP failure corresponds to a case where the extension creates new triangle types** — meaning the node would NOT be blocked. When a T-closed extension exists, the T-filtered arc-consistency enforcement always finds it.

**What is proved:**
- The conditional theorem (Theorem 4.5 in the paper): T-closed solution ⟹ decidability
- Correction of the algebraic error: only ONE self-absorption failure (PPI ∉ comp(DR, PPI) = {DR}), not two
- Partial result: for non-DR witnesses, a T-closed solution always exists (Proposition 7.4)

**What remains open (the Extension Solvability Conjecture):**
The tree unraveling creates copies of the same node with different parent contexts. Showing the needed triangle types are always present requires new ideas beyond what endpoint-type domains provide. Three suggested approaches: direct combinatorial argument, enriched blocking, or quasimodel-level patchwork.

**Why the two proven results don't compose.** A natural question is whether the two proven directions — (1) satisfiable → quasimodel exists (Claude) and (2) open contextual tableau → model exists (GPT-5.4) — can be chained into a decision procedure. They cannot. The chain would require a bridge step: quasimodel → open contextual tableau. But the FW counterexample proves this bridge cannot exist in general. Consider C∞ = (∃PP.⊤) ⊓ (∀PP.∃PP.⊤): it is satisfiable, so a quasimodel for it exists (by Claude's proven soundness), but NO finite-width contextual tableau for it exists (FW refuted for every N). The two proven results operate on **different intermediate representations** with gaps on **opposite sides** — if they were opposite sides of the *same* representation they would compose, but as it stands, neither formalism serves as a bridge to the other.

### What the papers contribute

Despite the gaps, the papers introduce proof machinery that narrows the open problem:
- The quasimodel method + patchwork property identifies the extension gap as a specific constraint-satisfaction question about RCC5 disjunctive networks. The type elimination algorithm is **disproved** (rejects the satisfiable concept C₁ = ∃PO.D ⊓ ∃DR.(B ⊓ ∀PO.¬D) ⊓ ∀DR.¬D ⊓ ∀PP.¬D ⊓ ∀PPI.¬D), revealing that the greatest-fixpoint approach is fundamentally incompatible with Q3's anti-monotonicity.
- The contextual tableau (GPT) cleanly separates the soundness (unfolding) argument from the completeness (extraction) argument. The FW counterexample shows that the extraction problem is fundamentally hard: infinite PP-chains cannot be finitely represented in the recentering framework.
- The profile-cached blocking series (GPT) develops correct local machinery — coherent predecessor blocks, depth-indexed signatures, meet-semilattice on labels — that may be useful components for a future proof. The gap is specifically in the unraveling step where the color structure changes.
- The direct construction attempt (Claude) correctly identifies the forced DR edge phenomenon (Lemma 4.1) and the self-safety theorem, but its global step (DN\_safe-based edge domains) is too coarse, as GPT's counterexample shows.
- **Computational verification** (see "Computational investigation of the extension gap" below) pinpoints the gap precisely: condition Q3s (arc-consistency) would suffice but is not extractable from models. The verification confirms this is a **structural impossibility**, not a proof artifact — 11.1% of concrete models produce DN networks violating Q3s.
- The root cause is the combination of (i) transitivity of PP, (ii) universal propagation of ∀PP along PP-chains, and (iii) the complete-graph requirement. The two-tier quotient (seventh approach) engages with this combination by representing PP-chains as period descriptors and using the full tractability of RCC5 to bridge local and global consistency.

### Eleventh approach: cover-tree tableau — MOST PROMISING (Wessel/GPT/Claude)

The eleventh approach decomposes ALCI\_RCC5 models into **cover trees** (oriented by immediate PPI-steps downward) with **finite cross-edge descriptors** for the remaining DR/PO relations. This is the **most theoretically grounded** approach attempted and the only one with a plausible path to both soundness and completeness.

**Intellectual origin.** The key ideas were proposed by **Michael Wessel**:
1. **PPI-tree model**: Orient the proper-part order as a tree (cover tree), with PPI = immediate child, PP = immediate parent, and transitive PP/PPI recovered from the ancestor relation.
2. **DAG-node splitting via weak EQ semantics**: In a model, the PP/PPI order is a DAG (a node can have multiple PP-predecessors). Split join-nodes into EQ-copies to obtain a tree. This gives a weak-EQ split-tree presentation.
3. **Restoring strong EQ via congruence quotient**: Use the typed EQ-congruence relation (from [report7.pdf](https://github.com/lambdamikel/alcircc5/blob/master/report7.pdf), Section 4.4.3) to quotient the weak-EQ model back to a strong-EQ model.
4. **DR propagates rigidly downward**: The critical observation that comp(PP,DR) = {DR} and comp(DR,PPI) = {DR} means DR is **rigid** — once a node is DR to some sibling subtree root, ALL its descendants are also DR. This leaves only {DR,PO} as open choices for sibling cross-edges, dramatically simplifying the constraint problem.

**Formalization by GPT-5.4 Pro.** GPT-5.4, prompted by Wessel, formalized these ideas into two papers:
- [Split-forest paper](https://github.com/lambdamikel/alcircc5/blob/master/trees/sibling_interface_descriptors_ALCIRCC5_completed_eqsync_canonical_patched.pdf): Defines the three-way status partition (Core/Out/Front), rank-k descriptors with local coherence axioms, proves finite-index lemma, finite-prefix arc-consistency theorem, and constructs models via canonical refinements + Konig's lemma.
- [Cover-tree tableau paper](https://github.com/lambdamikel/alcircc5/blob/master/trees/alcircc5_cover_tree_tableau_needslots_patched.pdf): Packages the split-forest approach as a hybrid tableau calculus — local tree expansion for PP/PPI eventualities, global side-checker for DR/PO, blocking via rank-d signatures.

**Corrections by Wessel.** GPT's initial formalization incorrectly included PP as an open sibling cross-edge value. Wessel corrected this: after EQ-splitting, if x PP y then x lies below y in the tree, placing x in the Core of the sibling pair — PP is NOT an open cross-edge. This correction is essential; without it, the open domain would be {DR,PO,PP} and the arc-consistency argument breaks down. With it, the open domain is just {DR,PO}, and the {DR,PO} network is trivially arc-consistent (comp(R,S) ∩ {DR,PO} ≠ ∅ for all R,S ∈ {DR,PO}).

**Implementation by Claude (Opus 4).** Claude implemented the algorithm as a type-set search with cover-tree constraint structure ([`cover_tree_tableau.py`](https://github.com/lambdamikel/alcircc5/blob/master/cover_tree_tableau.py)), capturing four key checks:
1. **Demand closure**: every ∃R.C has an R-safe witness.
2. **Cross-edge consistency**: all type pairs have non-empty Safe\_{DR/PO} or can be tree-related.
3. **Cover-tree sibling compatibility**: only DR/PO witness pairs face sibling constraints (not mixed PP/DR).
4. **Singleton-composition propagation**: when comp(INV[R₁], R₂) is a singleton, the forced relation must be type-safe. Catches cross-role UNSAT patterns (e.g., ∃PPI.(∀DR.A) ⊓ ∃DR.¬A is UNSAT because comp(PP,DR) = {DR} forces the PPI-child's ∀DR.A to fire on the DR-witness).

**Results**: Cross-validated on [**902 test concepts**](https://github.com/lambdamikel/alcircc5/blob/master/stress_test_cover_tree.py) against the quasimodel reasoner with **zero mismatches**: 50 known SAT, 13 known UNSAT, 27 adversarial (including all 7 cyclic-model concepts), 512 systematic triples, 200 random depth-2, 100 random depth-3.

**Why this handles the cyclic-model concepts.** The 7 concepts that lack tree models (e.g., ∃PO.A ⊓ ∃PP.¬B ⊓ ∀DR.A) work naturally: the PP-witness is an ancestor in the cover tree, the PO-witness is a cross-edge in a sibling subtree. The ∀DR.A universal fires only on DR-related nodes — the ancestor is PP-related (not DR), so no conflict. The cover tree separates these two witnesses into different mechanisms (tree vs. cross-edge), avoiding the problematic mixed compositions.

**Remaining gap.** The completeness direction (model → quotient extraction) is condensed in GPT's split-forest paper. Specifically, extracting locally coherent support-closed descriptor tables from an arbitrary model is claimed but not fully detailed. The soundness direction (quotient → model) is convincing: the finite-prefix arc-consistency theorem and canonical refinement via Konig's lemma are well-argued. No complexity bound (EXPTIME or otherwise) is established. See the [implementation paper (PDF)](https://github.com/lambdamikel/alcircc5/blob/master/cover_tree_tableau_ALCIRCC5.pdf) for full documentation.

**Key files:**
- [`trees/sibling_interface_descriptors_ALCIRCC5_completed_eqsync_canonical_patched.tex`](https://github.com/lambdamikel/alcircc5/blob/master/trees/sibling_interface_descriptors_ALCIRCC5_completed_eqsync_canonical_patched.tex) — GPT-5.4's split-forest paper (the semantic foundation)
- [`trees/alcircc5_cover_tree_tableau_needslots_patched.tex`](https://github.com/lambdamikel/alcircc5/blob/master/trees/alcircc5_cover_tree_tableau_needslots_patched.tex) — GPT-5.4's cover-tree tableau paper (the algorithmic layer)
- [`cover_tree_tableau.py`](https://github.com/lambdamikel/alcircc5/blob/master/cover_tree_tableau.py) — Claude's implementation (≈350 lines Python)
- [`stress_test_cover_tree.py`](https://github.com/lambdamikel/alcircc5/blob/master/stress_test_cover_tree.py) — Cross-validation script (902 tests)
- [`cover_tree_tableau_ALCIRCC5.tex`](https://github.com/lambdamikel/alcircc5/blob/master/cover_tree_tableau_ALCIRCC5.tex) — Claude's implementation paper (9 pages)

### Ongoing discussion: the omega-model direction

After the FW(C,N) counterexample, GPT-5.4 proposed a [status assessment](https://github.com/lambdamikel/alcircc5/blob/master/ALCI_RCC5_status_after_FW.pdf) distinguishing two levels of finiteness:
- **(A) Strong finiteness** (exact local-state closure with recentering) — **refuted** by the FW counterexample.
- **(B) Weak finiteness** (bounded local descriptors around a finite core) — possibly still true and useful as a finite alphabet for a future decision procedure.

GPT proposes a **regular omega-model theorem** as the missing ingredient: a representation of models using finitely many local interface signatures, finitely many PP/PPI thread control states, and a Buchi/parity-style acceptance condition for infinite proper-part chains. This is analogous to how mu-calculus extensions of DLs handle infinite paths via automata.

Claude's [formal response](https://github.com/lambdamikel/alcircc5/blob/master/response_to_status_note.pdf) agrees with the (A)/(B) distinction and the omega-model direction but notes that: (1) the quasimodel work's soundness is fully proven (not merely a "setup"), (2) the patchwork property is used correctly (the extension gap is an honestly documented open problem, not a misuse), (3) the omega-model proposal identifies the right architecture but provides no proofs — each of its four tasks (interface transfer, omega-acceptance, regular extraction, realization) is a non-trivial research problem, and (4) the feasibility hinges on a concrete sub-question:

> **Is the sequence of Hintikka types along an infinite PP-chain eventually periodic?** If yes, the omega-model route is viable. If no, even the type sequence is irregular, pointing toward undecidability.

### Why standard undecidability reductions fail for ALCI\_RCC5

Every known undecidability proof for description logics ultimately encodes a **two-dimensional grid** (the Z×Z domino tiling problem). Grid encoding requires either functional roles, number restrictions, role intersection, or role value maps. ALCI\_RCC5 has **none of these**. Moreover, the patchwork property — local consistency implies global consistency — actively resists grid encoding, since tiling reductions need rigid global constraints that go beyond local consistency.

**Lutz & Wolter (LMCS 2006) explicitly left L\_RCC5(RS) open.** In their comprehensive study of modal logics of topological relations, Lutz and Wolter proved L\_RCC8 undecidable (via domino tiling using the TPP/NTPP distinction) and L\_RCC5 undecidable over RS^∃ (supremum-closed structures, via reduction from S5³). But they explicitly stated (p. 31): "Perhaps the most interesting candidate is L\_RCC5(RS) [...] to which the reduction exhibited in Section 8 does not apply." ALCI\_RCC5 satisfiability is exactly L\_RCC5(RS) — arbitrary complete-graph models. This problem has been recognized as open by leading researchers since 2006.

The following table surveys all standard candidate reductions:

| Candidate Problem | Reduction Technique | Key Feature Missing in ALCI\_RCC5 | Verdict |
|---|---|---|---|
| Z×Z Domino Tiling (Berger 1966) | Grid via graded modalities + transitivity + converse | Number restrictions (counting) | Blocked |
| ALC\_RA⊖ undecidability (Wessel 2000) | CFG intersection via Post Correspondence Problem | Arbitrary role box (fixed in RCC5) | Blocked |
| ALCN\_RASG undecidability (Wessel 2000) | Grid via domino + number restrictions on admissible role box | Number restrictions (counting) | Blocked |
| ALCF⁻ (features + inverse) | Grid via functional roles | Functional roles | Blocked |
| Unrestricted SIQ / GrIK4 (Zolin 2015) | Grid via counting + transitivity + converse | Number restrictions | Blocked |
| Role value maps (Schmidt-Schauß 1989) | PCP via path equality | Role value map constructor | Blocked |
| SHIN⁺ (transitive closure in concepts) | Grid via closure + role hierarchy | Transitive closure operator | Blocked |
| FO² + two orders (Schwentick-Zeume 2012) | Grid via two successor functions | Second independent order relation | Blocked |
| ALC + role intersection | Various | Roles are JEPD (intersection always empty) | Blocked |
| L\_RCC8 undecidability (Lutz-Wolter 2006) | Domino tiling via discrete TPP-chains | TPP/NTPP distinction (RCC5 has only PP) | Blocked |
| L\_RCC8 → ALCI\_RCC8 transfer | Same domino reduction over abstract models | Grid coincidence (topological rigidity, not in composition table) | Blocked |
| L\_RCC5(RS^∃) undecidability (Lutz-Wolter 2006) | S5³ satisfiability via supremum regions | Supremum closure (not guaranteed in RS) | Blocked |
| BD fragment of HS (Bresolin et al. 2010) | Tiling via begins + during modalities | B modality has no RCC5 counterpart; D ≈ NTPP ≠ PP | Blocked |

**Why Wessel's ALC\_RA⊖ proof doesn't transfer.** Wessel proved ALC\_RA⊖ undecidable by reducing from PCP: arbitrary role axioms encode context-free grammar productions, and satisfiability corresponds to non-intersection of the generated languages. This fails for ALCI\_RCC5 because the role box is *fixed* by the RCC5 composition table — it is not part of the input. With only 5 base relations and their predetermined compositions, one cannot encode arbitrary grammar productions.

**Why Wessel's ALCN\_RASG proof doesn't transfer.** Wessel proved ALCN\_RASG undecidable by a direct reduction from the N×N domino tiling problem. The proof uses an admissible (deterministic, functional, associative) role box with four roles — R\_X (horizontal), R\_Y (vertical), R\_Z (diagonal = R\_X∘R\_Y), R\_U (everything else) — and number restrictions (≥ R\_X 1) ⊓ (≤ R\_X 1) ⊓ (≥ R\_Y 1) ⊓ (≤ R\_Y 1) to enforce that each element has *exactly one* horizontal and *exactly one* vertical successor, yielding a well-defined grid. Tile types are concept names; matching is enforced by ∀R\_X and ∀R\_Y. This proof is essentially the same mechanism as Zolin's GrIK4 proof — both encode a grid via counting — but Wessel's version is simpler because separate roles serve as separate grid directions, whereas Zolin must encode both directions within a single transitive relation using propositional type labels. Neither proof requires inverse roles or transitivity; both *fundamentally* require number restrictions. ALCI\_RCC5 has no number restrictions, so the grid cannot be enforced.

**What ALCI\_RCC5 does have.** The logic possesses two of the three ingredients of Zolin's GrIK4 undecidability proof: transitivity (PP∘PP ⊆ PP) and inverse roles (PPI = PP⁻). But the third — number restrictions — is entirely absent. Without counting, there is no way to enforce that a role has exactly one filler, which is essential for the commuting-square property of grid encoding. The complete-graph semantics compounds this: every element is PP/PO/DR/PPI-related to every other, so there is no way to isolate a unique "successor" among all neighbors. Notably, Wessel's ALCN\_RASG proof does *not* use inverse roles, and he conjectured (report5.pdf, p. 38) that ALCI\_RASG — adding inverse but not counting — might still be decidable. This supports the hypothesis that counting, not inverse roles or transitivity, is the critical dividing line.

<a id="why-lutz--wolters-rcc5-undecidability-proof-doesnt-transfer"></a>
**Why Lutz & Wolter's RCC5 undecidability proof doesn't transfer.** Lutz and Wolter (LMCS 2006) proved L\_RCC5(RS^∃) undecidable by reducing from S5³ (the 3-dimensional product of S5, undecidable by Maddux 1980). The reduction encodes three families of regions (a₁, a₂, a₃) pairwise DR-separated, with "diagonal" regions d representing triples (w₁,w₂,w₃) constructed as **suprema** Sup({w₁,w₂,w₃}) — the smallest region containing all three. The S5³ modalities are simulated by navigating from d up to pair-regions d\_{ij} = Sup({w\_i,w\_j}) and back down to d-regions. This reduction *requires* RS^∃ — the existence of supremum regions for every 2- or 3-element set. In an arbitrary ALCI\_RCC5 model (i.e., RS = complete graph with composition table), such suprema need not exist. The reduction therefore does not apply to L\_RCC5(RS) = ALCI\_RCC5 satisfiability.

**Why Lutz & Wolter's RCC8 undecidability proof doesn't transfer to ALCI\_RCC5.** The RCC8 undecidability uses the **alternating-type trick** (Section "The alternating-type trick" above) to create discrete TPP-chains via concept constraints. The formula forces a-regions to be PP-related only to other a-regions, then uses alternating b/¬b labels with ∀TPP constraints to ensure TPP holds only between adjacent chain elements and NTPP for all others. This creates a discrete linear ordering — the "cells" of a tiling grid. RCC5 cannot do this because PP = TPP ∪ NTPP is undifferentiated; there is no way to distinguish immediate from non-immediate proper parts.

<a id="why-lutz--wolters-rcc8-undecidability-proof-doesnt-transfer-to-alci_rcc8-either"></a>
**Why Lutz & Wolter's RCC8 undecidability proof doesn't transfer to ALCI\_RCC8 either.** Even for ALCI\_RCC8 (which *has* the TPP/NTPP distinction), the L\_RCC8 reduction fails. L\_RCC8 is interpreted over *topological* models (regular closed sets in R²), while ALCI\_RCC8 uses *abstract* composition-table models. The reduction requires a **grid coincidence condition** (east-of-north = north-of-east), which the topological geometry of R² forces but the composition table does not. In abstract models, the "diagonal" nodes z (reached via east-then-north) and z' (reached via north-then-east) can have any relation in {PO, EQ, TPP, NTPP, TPPI, NTPPI} — there is no way to force z = z'. This **coincidence obstruction** was first identified by Wessel in 2002/2003 ([report7.pdf](https://github.com/lambdamikel/alcircc5/blob/master/report7.pdf), Section 4.4.3, Figure 11), who constructed explicit RCC8 grid networks (Figure 10) but showed no concept term can enforce the grid structure at the model level. See [**L\_RCC8 vs ALCI\_RCC8 (PDF)**](https://github.com/lambdamikel/alcircc5/blob/master/LRCC8_vs_ALCIRCC8.pdf) for the full analysis, including a citation comparison showing that Wessel's even-odd chain, grid construction, and coincidence obstruction predate Lutz-Wolter by 3-4 years.

**Possible novel attack vectors.** Standard reductions are blocked, but undecidability is not ruled out. A proof would require a genuinely new technique, possibly exploiting:

1. **Infinite PP-chains + universal propagation**: ∀PP propagates concepts transitively along the entire chain. If sufficiently complex patterns can be forced, this gives a 1D computation model. The question is whether the complete-graph cross-links (PO/DR edges between chain elements) can provide a second dimension.
2. **Cross-chain synchronization**: In a model with multiple interacting PP-chains, the JEPD constraint forces relations between elements of different chains. The composition table constrains these cross-links. If two PP-chains can be forced to "synchronize" — one acting as the horizontal axis, another as the vertical — this could encode grid-like structure without explicit number restrictions.
3. **Non-periodicity of type sequences**: If type sequences along infinite PP-chains can be non-periodic/non-regular, the logic has enough power to encode non-regular computation, suggesting undecidability. This connects to the periodicity sub-question above.

The fact that every standard technique is blocked is evidence *for* decidability — ALCI\_RCC5 sits below the known undecidability boundary. But it sits above the known decidable fragments (ALCI\_RCC1/2/3, ALC\_RA\_SG), making the question genuinely open from both directions.

### The alternating-type trick: ALCI\_RCC8 may be structurally stronger than ALCI\_RCC5

In RCC5, PP is a single undifferentiated "proper part" relation — there is no way to distinguish immediate from non-immediate successors on a PP-chain. In RCC8, PP splits into **TPP** (tangential proper part) and **NTPP** (non-tangential proper part), and concept-level constraints can force TPP to act as an **immediate-successor relation**.

**The trick.** Consider a TPP-chain x₀ TPP x₁ TPP x₂ TPP ... with alternating concepts A, B (where A ⊓ B ⊑ ⊥):

- x₀ satisfies A ⊓ ∀TPP.B
- x₁ satisfies B ⊓ ∀TPP.A
- x₂ satisfies A ⊓ ∀TPP.B, ...

Now suppose TPP(x₀, x₂). Then x₂ must satisfy B (from x₀'s ∀TPP.B). But x₂ satisfies A, and A ⊓ B = ⊥. Contradiction. So **NTPP(x₀, x₂) is forced**. The same argument applies to any pair k ≥ 2 apart. The composition table allows TPP∘TPP ∈ {TPP, NTPP}, but the concept constraints eliminate the TPP option for non-adjacent pairs.

**Consequence.** On the chain, each element's TPP-successors are **exactly its immediate neighbors**. This is effectively functionality of TPP on the chain — achieved purely by concept-level constraints, without number restrictions. RCC5 cannot do this because PP has no finer subdivision.

**What this enables.** With TPP as "next cell" and TPPI = TPP⁻ as "previous cell":
- Tape symbols can be encoded as mutually exclusive concept names at each chain element
- Head position and machine state can be encoded as concept markers
- Local transition rules can be expressed via ∀TPP constraints
- Backward navigation is available via TPPI (inverse)

**What still blocks a full TM encoding.** A Turing machine encoding needs **two dimensions** (time × space). One TPP-chain gives only one dimension. Linking corresponding tape cells across time steps requires either a second independent chain (with enforced cross-links) or row-major interleaving (requiring a "jump" of W positions, which needs counting). Both routes remain blocked without number restrictions.

Counter machine (Minsky machine) encodings face the same obstacle: linking "the chain at time t has length n" to "the chain at time t+1 has length n±1" requires establishing a bijection between consecutive chain elements — counting in disguise.

**The omega-regularity question.** The alternating-type trick also sharpens the decidability question. A TPP-chain with Hintikka types is an omega-word over a finite alphabet. In RCC5, ∀PP propagates to all proper parts uniformly — a "global" constraint that stays within omega-regular expressiveness. In RCC8, the trick **separates** the constraints: ∀TPP.C applies only to the immediate successor, while ∀NTPP.C applies to all elements from 2 steps onward. This separation is more expressive. The critical question:

> Can the interaction of ∀TPP and ∀NTPP constraints, combined with the RCC8 composition table constraints on cross-links, force **non-regular** patterns in the type sequence? If yes, ALCI\_RCC8 may be undecidable even if ALCI\_RCC5 is decidable. If no, the omega-model approach (Büchi automata) should work for both.

This observation suggests that **ALCI\_RCC5 and ALCI\_RCC8 may have different decidability status** — a possibility not previously considered.

### Intricacies of blocking in complete-graph semantics

In standard DL tableaux with tree-shaped models, blocking is straightforward: a blocked node x has the same type as an earlier node y, and unraveling works because the only connection between a subtree and the rest of the model is the single parent edge. In ALCI\_RCC5, the model is a complete graph — every element is related to every other — and this fundamentally changes the blocking/unraveling dynamic.

**The naive expectation.** If x is blocked by y (same concept label), no new ∀-qualifications fire at x, and all triangles in the completion graph are already consistent. One might expect that copying y's witness structure for x produces only triangles already observed — so unraveling should succeed without introducing new triangle types.

**Where this breaks down: a concrete trace.** Consider a PP-chain with alternating types:

d₀(τ\_A) PP d₁(τ\_B) PP d₂(τ\_A) PP d₃(τ\_B) PP d₄(τ\_A) PP ...

where ∃PO.A ∈ τ\_A and ∀PO.¬A ∈ τ\_B.

d₀ needs a PO-witness w₀ for ∃PO.A: ρ(d₀, w₀) = PO, A ∈ tp(w₀).

**Can d₂ reuse w₀?** Trace composition forward:

- ρ(d₁, w₀) ∈ comp(PPI, PO) = {PO, PPI}. But ∀PO.¬A ∈ τ\_B and A ∈ tp(w₀) exclude PO. So **ρ(d₁, w₀) = PPI**.
- ρ(d₂, w₀) ∈ comp(PPI, PPI) = {PPI}. So **ρ(d₂, w₀) = PPI**.

Since ρ(d₂, w₀) = PPI ≠ PO, w₀ does not satisfy d₂'s ∃PO.A demand.

**w₁ must exist as d₂'s PO-witness.** ρ(d₂, w₁) = PO, A ∈ tp(w₁). Its relations:

Forward from d₂:
- ρ(d₃, w₁) ∈ comp(PPI, PO) = {PO, PPI}. ∀PO.¬A excludes PO → **ρ(d₃, w₁) = PPI**.
- ρ(d₄, w₁) ∈ comp(PPI, PPI) = {PPI}. **PPI forever after.**

Backward from d₂:
- ρ(d₁, w₁) ∈ comp(PP, PO) = {DR, PO, PP}. ∀PO.¬A excludes PO → **ρ(d₁, w₁) ∈ {DR, PP}**.
- Taking DR: ρ(d₀, w₁) ∈ comp(PP, DR) = {DR} → **ρ(d₀, w₁) = DR**.

Similarly, **w₂ is d₄'s PO-witness** (same pattern shifted by 2), and so on. The full relation table:

| | w₀ | w₁ | w₂ |
|---|---|---|---|
| d₀ | **PO** | DR | DR |
| d₁ | PPI | DR | DR |
| d₂ | PPI | **PO** | DR |
| d₃ | PPI | PPI | DR |
| d₄ | PPI | PPI | **PO** |
| d₅ | PPI | PPI | PPI |

Each wₖ is PO to exactly one chain element (d₂ₖ), DR to all earlier ones, and PPI to all later ones. Every ∀PO.¬A at τ\_B positions is vacuously satisfied — no element is PO to any τ\_B position.

**What happens in the tableau with type-equality blocking.** The finite completion graph has d₀(τ\_A), d₁(τ\_B), d₂(τ\_A) — blocked by d₀. Witness w₀ exists with ρ(d₀, w₀) = PO. Composition forces ρ(d₂, w₀) = PPI.

During unraveling, we create w₀' (a copy of w₀) for d₂ with ρ(d₂, w₀') = PO (copying the demanded relation). Composition then forces:

- ρ(d₁, w₀') ∈ comp(PP, PO) = {DR, PO, PP}; ∀PO.¬A excludes PO → ρ(d₁, w₀') ∈ {DR, PP}
- ρ(d₀, w₀') ∈ {DR, PP} (not PO)

So d₀ is DR or PP to the copy w₀' — but in the completion graph, d₀ was PO to w₀. **The triangle (d₀, w₀', d₂) has a shape that may not appear in the finite completion graph**, because d₀ was never DR-related to a tp(w₀)-type node. This is a potentially new triangle type.

**Can stronger blocking fix this?** If we require that x is only blocked by y when all triangle-type profiles match (not just the concept label), then d₂ is NOT blocked by d₀ — their profiles differ because ρ(d₂, w₀) = PPI ≠ PO = ρ(d₀, w₀). With this stronger blocking, unraveling would be locally correct: every triangle produced during unraveling is already in T.

**But stronger blocking prevents termination.** The tableau creates w₁ for d₂. Then d₄(τ\_A) isn't blocked either — it's PPI to both w₀ and w₁, while d₀ is PO to w₀ and DR to w₁. Different profile. Creates w₂. Each τ\_A-node at position d₂ₖ has a unique relational profile: PO to its own witness wₖ, DR to all earlier witnesses, PPI to all later ones. No two τ\_A-nodes ever match. **The completion graph grows forever on a satisfiable input.**

**The blocking dilemma.** This reveals a fundamental tension:

| Blocking condition | Termination | Unraveling |
|---|---|---|
| Type-equality (weak) | Always terminates | May produce new triangle types |
| Triangle-profile (strong) | May not terminate (PO-incoherent case) | Always locally correct |

This is the tableau-theoretic manifestation of the **PO gap** from the two-tier quotient paper. The constant-interface quotient (one kernel per descriptor) is analogous to "universal profile blocking" — one representative stands for all nodes of the same type. It works when the relational profile stabilizes: DR (backward forcing: comp(PP,DR)={DR}), PP (backward forcing: comp(PP,PP)={PP}), PPI (forward absorption: comp(PPI,PPI)={PPI}). It fails for PO because the profile never stabilizes — no single element has a permanent PO relation to the chain.

The **Extension Solvability Conjecture** asks whether the weak (type-equality) blocking, which guarantees termination, also happens to support correct unraveling. Computational evidence (zero genuine failures across 68,276 tested models) suggests yes, but no proof exists. The **PO-coherent fragment** is precisely the fragment where this dilemma does not arise: the relational profiles stabilize, both blocking conditions agree, and everything works.

### Observation: abstract triangle-type sets stabilize for interior nodes

The blocking dilemma above appears to force a choice between termination and correct unraveling. The abstract-triangle-type approach was motivated by a subtle observation: the non-termination argument uses **node-identity profiles** (which specific witnesses a node is related to), while the correctness argument only needs **abstract triangle-type sets** (which abstract relational patterns a node participates in). The abstract version stabilizes for **interior** chain nodes — but as the full implementation later revealed, **frontier nodes never stabilize** because they lack successor-edge triangles (see "CRITICAL UPDATE" above).

**The key distinction.** A node-identity profile records, for each pair of neighbors (b, c), the concrete identity of b and c together with the RCC5 relation. An abstract triangle type is a tuple (τ₁, R₁₂, τ₂, R₂₃, τ₃, R₁₃) — three Hintikka types and three pairwise RCC5 relations, with no node identities. The abstract triangle-type set of a node d is the set of all abstract triangle types that d participates in.

**Why node-identity profiles never match.** In the PO-incoherent chain, each τ\_A node d₂ₖ has a unique concrete relational context: PO to its own witness wₖ, DR to all earlier witnesses w₀,...,wₖ₋₁, and PPI to all later witnesses. Since k increases without bound, every d₂ₖ sees a different number of DR-related witnesses. The node-identity profile grows monotonically and never repeats.

**Why abstract triangle-type sets DO match.** The abstract triangle-type set strips away node identities and retains only the relational pattern. Even though d₄ is DR to {w₀, w₁} while d₆ is DR to {w₀, w₁, w₂}, both see the same *abstract patterns*: both participate in triangles of the form (τ\_A, DR, σ, DR, σ, PPI), (τ\_A, PO, σ, DR, τ\_B, PPI), etc. The additional concrete witness at d₆ contributes only triangle types that d₄ already has via its own witnesses.

**Computational verification** ([`triangle_type_saturation_check.py`](https://github.com/lambdamikel/alcircc5/blob/master/triangle_type_saturation_check.py)). The script builds the full PO-incoherent model (24-element PP-chain with 12 PO-witnesses), verifies composition consistency, and computes abstract triangle-type sets for every node. Results for the all-DR-backward branch:

| Node type | Stabilizes at | Interior range (all identical) | Set size |
|---|---|---|---|
| τ\_A | d₄ (k=2) | d₄ = d₆ = d₈ = d₁₀ = d₁₂ = d₁₄ = d₁₆ = d₁₈ | 68 types |
| τ\_B | d₅ (k=2) | d₅ = d₇ = d₉ = d₁₁ = d₁₃ = d₁₅ = d₁₇ = d₁₉ | 56 types |
| σ | w₂ (k=2) | w₂ = w₃ = w₄ = w₅ = w₆ = w₇ = w₈ = w₉ | 57 types |

The growth phase (d₀ → d₂ → d₄: 25 → 55 → 68 types for τ\_A) reflects the start boundary where early nodes have fewer backward neighbors. Nodes near the end of the finite model (d₂₀, d₂₂) have fewer types due to the end boundary — an artifact that would not exist in the infinite tableau construction. All interior nodes are **exactly identical**.

The same stabilization holds for the all-PP-backward branch (verified in the script). This is not branch-dependent.

**The full comparison matrix** (= means identical abstract triangle-type sets, numbers show symmetric-difference size):

```
τ_A:     d0    d2    d4    d6    d8   d10   d12   d14   d16   d18   d20   d22
  d0      ·    30    43    43    43    43    43    43    43    43    50    54
  d2     30     ·    13    13    13    13    13    13    13    13    20    48
  d4     43    13     ·     =     =     =     =     =     =     =     7    35
  d6     43    13     =     ·     =     =     =     =     =     =     7    35
  d8     43    13     =     =     ·     =     =     =     =     =     7    35
  ...    ...   ...    =     =     =     =     =     =     =     =    ...   ...
  d18    43    13     =     =     =     =     =     =     =     ·     7    35
```

**Why stabilization occurs.** The abstract triangle-type set of a node depends on the menu of Hintikka types and RCC5 relations available among its neighbors — not on the number of neighbors of each kind. Once d₄ has at least one predecessor of each relevant type at each relevant relation (PPI to τ\_B, DR to σ, PPI to σ, etc.) and at least one successor of each relevant type at each relevant relation, its abstract triangle-type menu is complete. Additional predecessors or successors of the same abstract kind contribute no new triangle types. The transient phase (d₀ through d₂) simply reflects the time needed for the backward neighborhood to include all relevant abstract patterns.

**Implication for the blocking dilemma.** The interior-node stabilization suggests that abstract-triangle-type matching is the right level of abstraction for correct unraveling. However, a full implementation ([`triangle_calculus.py`](https://github.com/lambdamikel/alcircc5/blob/master/triangle_calculus.py)) revealed that **stabilization of interior nodes is insufficient for termination**: frontier nodes (chain endpoints without successors) always have a strictly smaller Tri (|Tri|=8 vs 16), so they are never blocked. The blocking dilemma remains open:

| Blocking condition | Terminates? | Correct unraveling? |
|---|---|---|
| Type-equality (LL only) | Yes | Not always (novel triangles risk) |
| LL + Tri | **No** (frontier advancement) | Yes |
| LL + Tri + TNbr | **No** (frontier advancement) | Yes |

Any blocking condition using Tri inherits the frontier problem. Resolving the dilemma requires a mechanism that handles the PP/PPI asymmetry at chain endpoints (see conjectured directions in the [tableau paper](https://github.com/lambdamikel/alcircc5/blob/master/tableau_ALCIRCC5.pdf), Section 7.1).

**Strengthened condition: Tri-neighborhood equivalence.** Michael Wessel proposed strengthening the blocking condition to require not only Tri(x) = Tri(y), but also that for each (relation, type) pair, the *set of Tri-values among neighbors* matches:

> For each pair-type (L(x), R, τ), {Tri(b) : E(x,b)=R, L(b)=τ} = {Tri(b') : E(y,b')=R, L(b')=τ}

This ensures the copy is faithful not just from x/y's perspective but from **every neighbor's perspective**. Computational verification ([`tri_neighborhood_check.py`](https://github.com/lambdamikel/alcircc5/blob/master/tri_neighborhood_check.py)) confirms this stronger condition also stabilizes, at a slightly later point:

| Node type | Basic Tri stabilizes | Tri-nbr stabilizes |
|---|---|---|
| τ\_A | d₄ (k=2) | **d₆ (k=3)** |
| τ\_B | d₅ (k=2) | **d₇ (k=3)** |
| σ | w₂ (k=2) | **w₃ (k=3)** |

The one-step delay occurs because d₄'s PPI-neighbors include boundary nodes (d₂, w₁) with different Tri sets than the corresponding PPI-neighbors of d₆ (which are all interior). Once all neighbors are also in the stabilized interior (at d₆), full Tri-neighborhood equivalence holds. The comparison matrix shows the pattern clearly (= means full Tri-nbr equivalence, T means Tri-only match):

```
τ_A:     d4    d6    d8   d10   d12   d14   d16   d18
  d4      ·     T     T     T     T     T     T     T
  d6      T     ·     =     =     =     =     =     T
  d8      T     =     ·     =     =     =     =     T
  ...     T     =     =     =     =     =     =     T
  d16     T     =     =     =     =     =     ·     T
  d18     T     T     T     T     T     T     T     ·
```

The strengthened condition makes the soundness proof (specifically the T-closure argument in Lemma 5.5) substantially more robust: triangles are guaranteed to be in T from **every participating node's perspective**, not just the blocked/blocker pair. This directly addresses scrutiny point 1 (intra-subtree T-closure) from the tableau paper.

### Eighth approach: Tri-neighborhood tableau — TERMINATION DISPROVED

Building on the saturation finding above, a complete tableau calculus with Tri-neighborhood blocking is presented in [**A Tableau Calculus for ALCI\_RCC5 with Tri-Neighborhood Blocking (PDF)**](https://github.com/lambdamikel/alcircc5/blob/master/tableau_ALCIRCC5.pdf) (16 pages, third revision, two rounds of GPT-5.4 Pro review).

**The blocking condition.** A node x is blocked by an earlier node y when three conditions hold: (i) L(x) = L(y) (same concept label), (ii) Tri(x) = Tri(y) (same abstract triangle-type set), and (iii) TNbr(x) = TNbr(y) (same Tri-neighborhood signature — for each (relation R, type τ) pair, the set of Tri-values among R-neighbors of type τ matches). This is strictly between type-equality blocking (condition (i) alone) and node-identity profile blocking (which requires matching concrete relational contexts). Condition (ii) ensures first-person perspective equivalence; condition (iii) ensures third-person perspective equivalence.

**The proof structure:**
- **Termination** (Theorem 4.1): **FALSE.** A [full implementation](https://github.com/lambdamikel/alcircc5/blob/master/triangle_calculus.py) demonstrates non-termination on `A ⊓ ∃PP.A ⊓ ∀PP.(∃PP.A ⊓ ∃DR.B)` via frontier advancement (see the "CRITICAL UPDATE" section above for the full mechanism). 18/20 test concepts show non-termination. The local per-node bounds (bounded branching, permanent demand satisfaction, monotone Tri-growth) are individually correct but insufficient.
- **Soundness** (Theorem 5.8): **NOT FULLY PROVEN.** The model construction goes via tree unraveling + triangle-type-filtered disjunctive constraint network. The critical step is Lemma 5.5 (non-empty domains after T-filtering and arc-consistency), which the paper's own honest assessment (Section 7.2, item 1) acknowledges is "supported by computational verification on completion graphs of size 8, 10, and 12, but not by a general formal argument." This is structurally the same issue as the extension gap: a disjunctive constraint network must be shown solvable. The mechanism differs (triangle-type filtering rather than Henkin/Q3), and the computational evidence is stronger (zero failures found), but a complete formal proof is missing.
- **Completeness** (Theorem 6.1): **Valid.** A model guides all nondeterministic choices, maintaining invariants that the labels are subsets of model types and edges match model relations.

**The mirror triangle issue and its resolution.** An earlier version of the soundness proof used a map-based assignment ρ(d₁,d₂) = E(map(d₁), map(d₂)). Computational investigation ([`intra_subtree_tclosure_check.py`](https://github.com/lambdamikel/alcircc5/blob/master/intra_subtree_tclosure_check.py)) revealed that this assignment is NOT T-closed: when two elements both map to the same node (a "same-map pair"), they both carry the same PO relation to a shared witness, creating "mirror triangles" like (τ\_A, R, τ\_A, PO, σ, PO) that never appear in T(G) — because each σ witness is PO to exactly one τ\_A node. An earlier revision fixes this by working with disjunctive domains throughout: the constraint network's arc-consistency step removes the problematic PO from cross-subtree edges and replaces it with DR or PPI (which are type-safe alternatives from P(G)). Computational verification confirms all domains remain non-empty for completion graphs of size 8, 10, and 12.

**Honest assessment.** The paper identifies four specific points:
1. **Intra-subtree T-closure (Lemma 5.5)**: **Formal gap.** The proof that arc-consistency preserves non-empty domains is supported by computational verification on completion graphs of size 8, 10, and 12, but not by a general formal argument. The paper's own honest assessment says: "A fully formal proof that domains remain non-empty after T-filtering and arc-consistency for *arbitrary* open completion graphs would close this gap." This is structurally analogous to the extension gap in the main paper — a disjunctive constraint network must be shown solvable. The triangle-type filtering is a more refined mechanism than the Henkin/Q3 approach, and zero failures have been found computationally, but the proof is incomplete.
2. **Initial domains for same-map pairs**: GPT's [second review](https://github.com/lambdamikel/alcircc5/blob/master/review6/response_to_tableau_ALCIRCC5_second_revision.pdf) identified that the P(G)-only domain is empty when two unraveling elements both map to the sole node of a given type. Fixed by extending D₀ with Safe(τ₁,τ₂). The degenerate case Safe(τ,τ)=∅ is handled by identifying same-map copies.
3. **Termination**: **Disproved.** The concept `A ⊓ ∃PP.A ⊓ ∀PP.(∃PP.A ⊓ ∃DR.B)` causes unbounded node creation. The mechanism is frontier advancement, not oscillation: the frontier node's Tri is always strictly smaller than interior nodes' Tri (|Tri|=8 vs 16) because it lacks PP-successor triangles. Two reviewers correctly predicted this gap.
4. **Stabilization depth**: The earlier computational evidence remains correct for interior nodes. The issue is that frontier nodes never stabilize before their ∃-demands fire.

**Complexity.** Since the calculus does not terminate, complexity analysis is moot. A terminating variant would need separate analysis.

### Ninth approach: MSO encoding via interval semantics — FUNDAMENTALLY DIFFERENT DIRECTION

After the Tri-neighborhood tableau's termination was disproved (and the T-closure proof remains incomplete), we pursue a fundamentally different approach: reduce ALCI\_RCC5 satisfiability to the **Borel monadic second-order theory of (R, <)**, which is decidable by Manthe's theorem (2024). (Note: the *full* MSO theory of (R, <) with unrestricted set quantifiers is undecidable (Gurevich-Shelah 1982); only the Borel-restricted version is decidable.)

**The key observation.** RCC5 has a faithful interpretation over open intervals on the real line: PP = proper containment, PPI = proper contains, PO = overlap (neither contains the other), DR = disjoint, EQ = identical. In this representation, **composition consistency is free** — any set of open intervals automatically satisfies the RCC5 composition table. This eliminates the central difficulty (T-closure, extension gap, arc-consistency) of all previous approaches.

**The encoding.** An ALCI\_RCC5 interpretation becomes a set of open intervals on R, each carrying a Hintikka type. For each type τ\_i, we introduce MSO set variables L\_i (left endpoints) and R\_i (right endpoints). The ALCI\_RCC5 concept constructors translate to MSO formulas: existential witnesses become existential quantification over intervals; universal constraints become universal quantification; concept names are tracked by the type variables.

**What works:**
- RCC5 relations between pairs of open intervals are MSO-definable from endpoint positions
- Concept translation (Boolean, existential, universal) is straightforward
- Countable model property holds (Löwenheim-Skolem), so we can restrict to countable endpoint sets
- Composition consistency is **automatic** — no constraint filtering needed

**The remaining gap: endpoint pairing.** To compute the RCC5 relation between two intervals, we need both their left and right endpoints. Pairing left endpoints with right endpoints requires a **Dyck matching** (balanced parenthesization) over the endpoint set. Over discrete orders (N, <), this is handled by Büchi automata. Over dense orders (R, <), the encoding requires that the endpoint set is **scattered** (contains no dense sub-order). This is achievable for countable models, but the formal MSO-definability of the Dyck matching over scattered subsets of R needs verification.

**Complexity.** Even if correct, the resulting decision procedure has **non-elementary** complexity (from Shelah's procedure). This yields decidability but not EXPTIME. Whether a tighter bound can be obtained is a separate question.

**Interval temporal logics are blocked.** Literature research reveals that the HS route is closed: the BD fragment (begins + during) of Halpern-Shoham logic is already **undecidable** (Bresolin et al. 2010). Since PP corresponds to "during," any HS fragment capturing ALCI\_RCC5 is undecidable. Similarly, Kontchakov, Wolter, and Zakharyaschev (2010) showed modal logics of RCC relations are undecidable over the real line. The Borel-MSO encoding avoids these barriers by reducing each satisfiability instance to a single sentence in the decidable Borel theory of (R, <) — what modal logics cannot decide efficiently, Borel-MSO can decide with brute-force model theory (at non-elementary cost).

**Critical subtlety: Borel restriction.** Full MSO over (R, <) with unrestricted set quantifiers is **undecidable** (Gurevich-Shelah 1982). Only **Borel-MSO** — with set quantifiers restricted to Borel sets — is decidable (Manthe 2024). We verify that our encoding uses only Borel quantification: open intervals are open (Borel), countable endpoint sets are F\_sigma (Borel), and subsets of countable sets are countable (Borel). The Borel restriction is harmless.

**Scattered endpoint representation.** We prove that countable ALCI\_RCC5 models can always be represented with **scattered** endpoint sets (order type ≤ ω^ω). This makes the Dyck matching well-defined and unique, reducing the technical gap to: is the Dyck matching Borel-MSO-definable within the ambient (R, <) structure?

See [**MSO Encoding (PDF)**](https://github.com/lambdamikel/alcircc5/blob/master/MSO_encoding_ALCIRCC5.pdf) for the full paper (16 pages). ([source](https://github.com/lambdamikel/alcircc5/blob/master/MSO_encoding_ALCIRCC5.tex))

### Seventh approach: two-tier quotient — PO-COHERENT FRAGMENT DECIDABLE

A model-theoretic approach that **proves decidability of the PO-coherent fragment** of ALCI\_RCC5 by directly addressing the source of infinity: infinite PP-chains. The key insight is that PP-chains have **regular structure** — the sequence of Hintikka types along any infinite PP-chain is eventually periodic — and the **full tractability of RCC5** (Renz 1999: path-consistent disjunctive RCC5 networks are satisfiable) bridges local consistency to global consistency.

The approach works in two tiers:

**Tier 1 (within-chain): Period descriptors.** Each infinite PP-chain's periodic tail is represented by a finite cyclic word (τ₁, ..., τ_p) of Hintikka types. This is a *word*, not an RCC5 graph — it circumvents the impossibility of PP-cycles among distinct nodes.

**Tier 2 (between-chain): PP-kernel nodes.** Each chain is represented by a single kernel node with a reflexive PP-loop. Cross-chain interactions use atomic RCC5 edges between kernel nodes and regular (non-chain) nodes.

**The decidability proof has two directions:**

**Completeness (model → quotient):** Given any model, extract a finite quotient. The T∞ argument (the set of infinitely-recurring types on a PP-chain's stabilized tail) yields valid period descriptors. The model's global consistency guarantees the extension condition V6: the model's actual off-chain relations survive arc-consistency enforcement (a value satisfying all composition constraints is never removed by AC). The quotient size is bounded by D(1+|cl(C₀)|), where D ≤ 2^{2^{|cl(C₀)|}} is the number of descriptors — a constructive, non-circular bound.

**Soundness (quotient → model):** Given a valid quotient, unfold it into a model. Period descriptors become infinite PP-chains. Off-chain witnesses are added via the extension procedure. V6 ensures the resulting disjunctive network is path-consistent. By **full RCC5 tractability** (Renz 1999), the path-consistent network is satisfiable — a consistent atomic refinement exists. The patchwork property gives global consistency.

**Key insight closing the extension gap:** The Q3s condition (type-level arc-consistency) from the quasimodel approach failed because 11.1% of model-derived type-level networks violate Q3s. V6 operates on *instance-level* networks with specific atomic relations, not abstract type-level domains. The model provides actual relations for each witness that satisfy *all* composition constraints simultaneously, so arc-consistency cannot eliminate them.

**Decision procedure:** Enumerate all quotient structures up to the computable size bound, check V1–V6 and V\_safe for each, accept iff any is valid.

**The PO gap.** Exact-relation extraction works for DR (backward forcing: comp(PP,DR)={DR}), PP (backward forcing: comp(PP,PP)={PP}), and PPI (forward absorption: comp(PPI,PPI)={PPI}), but **fails for PO**. PO has neither backward forcing (comp(PP,PO)={DR,PO,PP}) nor forward absorption (comp(PPI,PO)={PO,PPI}). A concrete counterexample (Proposition 9.1 in the paper) exhibits a PO-incoherent descriptor — ∃PO.A ∈ τ\_A, ∀PO.¬A ∈ τ\_B — that is realizable in infinite models but cannot be captured by constant-interface quotients, because no element has a stabilized PO relation to the chain. The paper defines **PO-coherent descriptors** (those where every PO-demand has an all-phase-safe witness type) and proves decidability for the PO-coherent fragment.

See [**Decidability of ALCI\_RCC5 via Two-Tier Quotient Construction (PDF)**](https://github.com/lambdamikel/alcircc5/blob/master/two_tier_quotient_ALCIRCC5.pdf) for the full fourth revision (12 pages).

**Three rounds of GPT-5.4 Pro review.**

*First review.* GPT-5.4 Pro [reviewed](https://github.com/lambdamikel/alcircc5/blob/master/review2/response_to_two_tier_quotient_ALCIRCC5.pdf) the original version and raised five objections: (1) Core(Desc) loses phase-specific obligations, (2) V6 lacks type-safety filter, (3) reflexive PP self-loops, (4) blocking under-specified, (5) descriptor alone doesn't determine external behavior. Claude's [response](https://github.com/lambdamikel/alcircc5/blob/master/review2/response_to_gpt_review.pdf) accepts (1), (2), (5) as valid and (3), (4) as partially valid. The second revision incorporates all five fixes.

*Second review.* GPT [reviewed](https://github.com/lambdamikel/alcircc5/blob/master/review3/response_to_revised_two_tier_quotient_ALCIRCC5.pdf) the second revision and raised four objections: (i) phase-specific off-period PP demands, (ii) constant interfaces too coarse for phase universals, (iii) blocking claim unproved for regular nodes, (iv) quotient-to-model lift missing. Claude's [response](https://github.com/lambdamikel/alcircc5/blob/master/review3/response_to_gpt_second_review.pdf) added all-phase safety (Lemma 4.7), the chain-unfolding lift lemma (Lemma 8.1), Union(Desc) for PP demands, and strengthened T4/V6. The third revision addresses all four points.

*Third review.* GPT [reviewed](https://github.com/lambdamikel/alcircc5/blob/master/review4/response_to_latest_two_tier_revision.tex) the third revision and raised four objections: (i) phasewise safety of arbitrary kernel interfaces, (ii) exact-relation witness extraction, (iii) circular size bound, (iv) regular-node blocking. Claude's [response](https://github.com/lambdamikel/alcircc5/blob/master/review4/response_to_gpt_third_review.pdf) resolves (i) via V\_safe, (iii) via constructive quotient (one kernel per descriptor, K ≤ D), and (iv) by eliminating blocking entirely. For (ii), Claude discovers that backward forcing works for DR/PP and forward absorption for PPI, but PO has a genuine gap (concrete counterexample). The fourth revision proves decidability for the PO-coherent fragment and honestly documents the PO gap.

**Algebraic foundations (fully proven):**
- Reflexive PP is **universally self-absorbing**: R ∈ comp(PP, R) and R ∈ comp(R, PP) for every base relation R, and PP ∈ comp(R, inv(R)) for all R. Therefore reflexive PP(k,k) is composition-consistent with all external edges.
- **PP-transitivity** (comp(PP,PP) = {PP}) forces a strict linear order on distinct nodes, ruling out PP-cycles. Multi-type periodic chains *cannot* be represented as kernel-node graphs.
- **External relation stabilization**: relations from external elements to PP-chain elements stabilize monotonically, with PP as the unique absorbing state.
- **PPI dual absorption**: R ∈ comp(PPI, R) and R ∈ comp(R, PPI) for all R — ensures stabilized chain relations are self-consistent.

**Computational verification** ([`pp_kernel_analysis.py`](https://github.com/lambdamikel/alcircc5/blob/master/pp_kernel_analysis.py), [`pp_kernel_quotient.py`](https://github.com/lambdamikel/alcircc5/blob/master/pp_kernel_quotient.py), [`pp_kernel_cycle_analysis.py`](https://github.com/lambdamikel/alcircc5/blob/master/pp_kernel_cycle_analysis.py), [`gap_closing_verification.py`](https://github.com/lambdamikel/alcircc5/blob/master/gap_closing_verification.py)):

| Test | Result |
|---|---|
| Reflexive PP composition-consistency | All 12 checks pass |
| PP/PPI dual absorption | All 16 checks pass |
| Composition table non-emptiness | All 16 entries non-empty |
| PP-cycle among 3 distinct nodes | 0 out of 8 configurations — impossible |
| Single-type PP-chain collapse | Perfect — one kernel node suffices |
| One-step AC extension (2 existing elements) | 0 failures out of 164 |
| Full AC extension (3 existing elements) | 0 failures out of 128 |

**What remains open:** (1) The **blocking dilemma** — Tri-based blocking ensures sound unraveling but does not terminate (frontier advancement); type-equality blocking terminates but risks unsound unraveling. Resolving this is the central obstacle to full decidability. (2) The exact complexity (EXPTIME membership) — the quotient size bound is computable but possibly non-elementary. (3) The decidability of ALCI\_RCC8 (RCC8 lacks full tractability).

### The two-chain construction: a 2×∞ ladder with functional operators

The alternating-type trick gives one functional chain (TPP as immediate successor). For undecidability reductions, we typically need **two dimensions**. A natural construction uses two parallel TPP-chains connected by PO rungs.

**Geometric motivation.** Start with a parent region containing two overlapping TPP-children (their overlap makes them PO to each other). Each child is again the parent of one TPP-child, placed so that the grandchildren are NTPP to the grandparent and PO to each other. Iterating gives:

```
Chain A:  a₀ —TPP→ a₁ —TPP→ a₂ —TPP→ a₃ —TPP→ ...
           |         |         |         |
          PO        PO        PO        PO
           |         |         |         |
Chain B:  b₀ —TPP→ b₁ —TPP→ b₂ —TPP→ b₃ —TPP→ ...
```

**The coloring trick for PO-functionality.** Without additional constraints, PO could connect elements at different depths. To enforce PO only between same-level elements, use an offset color scheme:

- Chain A: Red, Blue, Red, Blue, ... (a₀ is Red, a₁ is Blue, ...)
- Chain B: Blue, Red, Blue, Red, ... (b₀ is Blue, b₁ is Red, ...)

Where Red ⊓ Blue ⊑ ⊥. Then ∀PO constraints from a Red element reach only Blue PO-neighbors. On chain A, a Red element's TPP-successor is Blue (same chain), but via PO, the same-level partner on chain B is also Blue (offset coloring). Elements at other levels on chain B have the *wrong* color for the constraint to propagate usefully. Combined with the alternating-type trick on each chain, this makes PO effectively connect only same-level pairs.

**The three functional operators.** On this 2×∞ ladder:

| Operator | Reaches | Functionality mechanism |
|---|---|---|
| ∀TPP | Immediate successor on same chain | Alternating-type trick |
| ∀PO | Same-level element on other chain | Coloring trick |
| ∀NTPP | ALL elements ≥ 2 steps deeper (both chains) | Broadcast (not functional) |

This gives two functional "axes" (∀TPP = horizontal, ∀PO = vertical in the ladder) plus a broadcast channel (∀NTPP = "all future").

**Counter encoding.** Each chain independently supports a binary counter using the alternating-type trick: concept markers at each depth encode counter bits, with ∀TPP enforcing the increment rule. This shows that each chain can track an unbounded integer — but the two counters are **independent**. Synchronizing them (e.g., ensuring both chains have the same counter value at some depth) requires cross-chain communication beyond what ∀PO provides.

### PCP encoding attempt on the two-chain structure

The **Post Correspondence Problem** (PCP) is a natural undecidability candidate for this structure: it requires matching two sequences symbol-by-symbol, which is exactly what the PO rungs provide.

**Setup.** Given a PCP instance with pairs (u₁, v₁), ..., (uₚ, vₚ) over alphabet Σ, encode:
- Chain A writes the u-components: u_{i₁}u_{i₂}u_{i₃}...
- Chain B writes the v-components: v_{i₁}v_{i₂}v_{i₃}...
- PO rungs enforce symbol-by-symbol equality (∀PO.σ for each symbol σ ∈ Σ)

**What works:**
- **Symbol matching**: PO at each depth forces the same symbol on both chains. ✓
- **Pair decomposition**: local ∀TPP constraints on each chain enforce valid pair structure (each segment is a valid u_i or v_j). ✓
- **String equality**: if both chains terminate at the same depth, the PO-enforced symbol equality gives u_{i₁}...u_{iₙ} = v_{j₁}...v_{jₘ}. ✓

**What fails — pair-index synchronization:**

PCP requires both chains to use the **same** sequence of pair indices. But |u_i| ≠ |v_i| in general, so the chains advance through pairs at different rates. After processing pair i₁:
- Chain A has consumed |u_{i₁}| cells
- Chain B has consumed |v_{i₁}| cells

The pair boundaries are **misaligned**. Chain A might be starting pair i₃ while chain B is still in the middle of pair i₂. Synchronizing pair indices requires tracking the **lag** — the running difference Σ(|u_{iₖ}| - |v_{iₖ}|) — which can grow unboundedly.

### The ∀NTPP queue investigation

The most promising idea for synchronization: use ∀NTPP broadcasts from different depths as a "queue" of pair-index announcements.

**Mechanism.** When chain A starts pair iₖ at depth d, it broadcasts via ∀NTPP from a_d. Since NTPP reaches all elements ≥ 2 steps deeper on both chains, this announcement becomes visible to all future elements. Multiple announcements from depths d₁ < d₂ < d₃ create **nested scopes**:

| Depth range | Visible announcements |
|---|---|
| d₁+2 to d₂+1 | {i₁} |
| d₂+2 to d₃+1 | {i₁, i₂} |
| d₃+2 onward | {i₁, i₂, i₃} |

The set of visible announcements **grows monotonically** with depth. An element can detect the *arrival* of each new announcement (the first depth where it becomes visible, detectable by a type change at the transition point).

**Why this is NOT a queue.** A FIFO queue supports two operations: enqueue (add to back) and dequeue (remove from front). The ∀NTPP mechanism supports only enqueue — announcements accumulate but are **never consumed**. Once an ∀NTPP-propagated concept becomes visible, it remains visible at all greater depths. This is a **broadcast log**, not a consumable queue.

For chain B to "process" announcements in order, it would need to track "which announcements I've already consumed" in its Hintikka type. But the Hintikka type is drawn from a finite set (bounded by 2^{|cl(C)|}). By pigeonhole: if the number of outstanding (unprocessed) announcements exceeds the number of distinct types, two chain B elements at different queue positions must have the **same type**, meaning they react identically to all constraints — they cannot distinguish their positions.

**Formal argument.** Let K = |cl(C)| be the closure size (fixed for a given PCP reduction). The number of "queue state" concepts expressible in cl(C) is at most K. For a PCP instance whose shortest solution has n pairs with maximum running lag L, we need L distinct queue states. If L > 2^K, the types cannot distinguish all queue positions. Since L is unbounded across PCP instances (and even within solutions of a single instance), no fixed K suffices.

**The bounded-lag special case.** For PCP instances where every solution has running lag bounded by L, the queue depth is ≤ L, and a concept vocabulary of size O(L) suffices. But **bounded-lag PCP is decidable** (it reduces to a finite-state reachability problem), so reducing from it yields no undecidability result.

**Conclusion.** The ∀NTPP broadcast mechanism is fundamentally monotonic: announcements accumulate but cannot be consumed. This makes it insufficient for the unbounded synchronization required by general PCP. The two-chain construction with PO rungs can enforce symbol-by-symbol string equality, but cannot enforce pair-index synchronization — the step that makes PCP undecidable.

### Assessment of the two-chain approach

The 2×∞ ladder construction is the strongest encoding framework discovered so far for ALCI\_RCC8. It provides:

1. **One-dimensional computation** on each chain (counters, finite automata, local transition rules) ✓
2. **Cross-chain symbol matching** at each depth via PO ✓
3. **Monotonic broadcast** to all future elements via ∀NTPP ✓

But it **lacks**:

4. **Cross-chain synchronization** of non-aligned boundaries ✗
5. **Consumable communication** (queue, stack, or channel) ✗
6. **Counting** (exactly n successors) ✗

The missing capabilities (4–6) are precisely what undecidable problems require. This provides further evidence — though not proof — that ALCI\_RCC8 may be decidable: even the most favorable encoding structure (functional TPP chains with PO cross-links) falls short of the computational power needed for standard undecidability reductions.

However, this analysis does NOT rule out undecidability via a non-standard reduction. The specific gap between "what the ladder provides" and "what undecidability requires" is instructive: any undecidability proof would need to either (a) find a way to implement consumable communication without counting, or (b) exploit some feature of the complete-graph semantics not captured by the two-chain analysis.

### Ramsey theory and graph-theoretic undecidability: the complete-graph connection

ALCI\_RCC5 models are edge-colored complete graphs (4 colors: DR, PO, PP, PPI for distinct pairs) subject to the RCC5 composition table. This is natural Ramsey territory — Ramsey theory studies what patterns must appear in edge-colored complete graphs. Could undecidable Ramsey-type or graph-theoretic problems be reduced to ALCI\_RCC5 satisfiability?

**The Bodirsky-Bodor dichotomy (2020/2024).** Bodirsky and Bodor proved a complete complexity dichotomy for constraint satisfaction problems (CSPs) of first-order expansions of the RCC5 basic relations, using Ramsey theory. **Every such CSP is either in P or NP-complete — never undecidable.** The proof exploits the fact that finite RCC5 models form a **Ramsey class** (via the Nešetřil-Rödl theorem and the KPT correspondence between the Ramsey property and extreme amenability of automorphism groups).

This means the constraint layer of ALCI\_RCC5 — the RCC5 network consistency problem — is inherently tractable. The Ramsey property is the tool that *proves* tractability, not a source of undecidability.

**Why Ramsey theory favors decidability.** Ramsey's theorem guarantees that any infinite ALCI\_RCC5 model must contain large monochromatic substructures: an infinite PP-chain, or an infinite PPI-chain, or an infinite pairwise-PO set, or an infinite pairwise-DR set. This forces **uniformity** in infinite models — exactly the opposite of the **positional diversity** needed for encoding computation. Undecidability reductions require that each cell/step in a computation has a distinct state; Ramsey uniformity forces large subsets to look alike.

The patchwork property reinforces this: local (triple-wise) consistency implies global consistency, meaning long-range rigid constraints that depend on absolute position — the hallmark of grid/tiling encodings — cannot arise from local concept constraints.

**Survey of graph-theoretic undecidability candidates:**

| Problem | Why undecidable | Encoding in ALCI\_RCC5? |
|---|---|---|
| Edge-coloring extension on periodic graphs (Burr 1984) | Doubly-periodic structure encodes a grid | **Blocked**: ALCI\_RCC5 has complete graphs, no geometric/grid structure |
| Product modal logics K×K (Gabbay-Shehtman) | Product frame creates a grid from two independent relations | **Blocked**: ALCI\_RCC5 has 4 relations on a single frame, not a product |
| Interval temporal logic HS (Halpern-Shoham) | Rigid interval compositions enforce grid structure | **Blocked**: RCC5 composition is non-deterministic with patchwork; no rigid grid |
| First-order modal logic ∀□ bundle | FO quantifiers + modal necessity | **Blocked**: ALCI has propositional modalities, no FO quantifiers |
| MSO theory of the Rado graph | MSO can quantify over sets of vertices | **Blocked**: ALCI is much weaker than MSO |
| Diophantine equations as CSP | Unbounded arithmetic constraints | **Blocked**: RCC5 CSP is P/NP-complete (Bodirsky-Bodor) |

**The Fraïssé-theoretic perspective.** The class of finite RCC5 models is a Fraïssé class (amalgamation = patchwork property). Its Fraïssé limit — the **generic RCC5 model** — is a countable homogeneous relational structure analogous to the Rado graph. The theory of this structure admits quantifier elimination and is omega-categorical. The Ramsey property of the age enables the Bodirsky-Pinsker classification of all CSP reducts.

The key remaining question: **does adding modal operators (∀R.C, ∃R.C) to this tractable CSP layer push into undecidability?** The evidence suggests not:
- The modal operators are propositional (no FO quantifiers over domain elements)
- The frame is a single complete graph (no product structure for grid encoding)
- The composition table is non-deterministic with patchwork (no rigid composition for interval-style encoding)

**Conclusion.** The Ramsey-theoretic analysis provides the strongest evidence yet for decidability of ALCI\_RCC5. At the constraint level, Ramsey theory proves tractability (Bodirsky-Bodor). At the model level, Ramsey uniformity opposes computation encoding. No known undecidable graph-coloring, Ramsey, or CSP problem has a plausible reduction to ALCI\_RCC5 satisfiability. The logic sits in a "tractability island" where the patchwork property prevents the rigid global constraints that undecidable problems require.

---

This repository contains a proof attempt for concept satisfiability in the description logics ALCI\_RCC5 and ALCI\_RCC8, targeting open problems from Wessel (2002/2003).

- **ALCI\_RCC5**: decidability **open**; PSPACE-hard lower bound (Wessel), EXPTIME upper bound if decidable
- **ALCI\_RCC8**: decidability **open**; EXPTIME-hard lower bound (Wessel), EXPTIME upper bound if decidable

Two procedures are given: a type-elimination algorithm (now **disproved** — rejects satisfiable concepts) and a tableau calculus with blocking.

**[Read the full paper (PDF)](https://github.com/lambdamikel/alcircc5/blob/master/decidability_ALCIRCC5.pdf)**

## Background

The ALCI\_RCC family extends the description logic ALCI (ALC with inverse roles) with **role boxes derived from RCC composition tables**. The base relations of RCC5 ({DR, PO, EQ, PP, PPI}) serve as the role names, and interpretations are constrained to be **complete graphs** where every pair of domain elements is related by exactly one base relation, subject to the RCC5 composition table.

These logics were introduced by Michael Wessel in his doctoral work at the University of Hamburg. He classified most of the family (ALCI\_RCC1 through ALCI\_RCC3) but left the decidability of ALCI\_RCC5 and ALCI\_RCC8 as open problems.

### Key Difficulties

- **No tree model property**: models are complete graphs (K\_n or K\_omega)
- **No finite model property**: some satisfiable concepts require infinite models
- **Non-deterministic role box**: the RCC5 composition table has multi-valued entries, ruling out reduction to ALCRA\_SG

### Key Enablers: Patchwork Property and Full RCC5 Tractability

The proof exploits two results from qualitative constraint reasoning (Renz & Nebel, 1999; Renz, 1999):

> **Patchwork property.** For RCC5 (and RCC8), an atomic constraint network is consistent if and only if it is path-consistent.

> **Full RCC5 tractability.** The entire RCC5 algebra is tractable: a *disjunctive* RCC5 constraint network is consistent if and only if it is path-consistent.

The patchwork property means **local (triple-wise) consistency implies global consistency** for atomic networks. Full RCC5 tractability is strictly stronger: it extends this to disjunctive networks (where each edge has a *set* of possible relations). The Henkin model construction relies on the stronger result to solve disjunctive constraint networks arising at each extension step.

## The RCC5 Composition Table

Reading: row = S(b,c), column = R(a,b), entry = possible relations for (a,c). The symbol \* means all five relations are possible.

|  comp   | DR(a,b) | PO(a,b)     | EQ(a,b) | PPI(a,b)       | PP(a,b)     |
|---------|---------|-------------|---------|----------------|-------------|
| DR(b,c) | \*      | DR,PO,PPI   | DR      | DR,PO,PPI      | DR          |
| PO(b,c) | DR,PO,PP| \*          | PO      | PO,PPI         | DR,PO,PP    |
| EQ(b,c) | DR      | PO          | EQ      | PPI            | PP          |
| PP(b,c) | DR,PO,PP| PO,PP       | PP      | PO,EQ,PP,PPI   | PP          |
| PPI(b,c)| DR      | DR,PO,PPI   | PPI     | PPI            | \*          |

## Results

### Main Result

The [fourth-revision two-tier quotient paper](https://github.com/lambdamikel/alcircc5/blob/master/two_tier_quotient_ALCIRCC5.pdf) proves **decidability of the PO-coherent fragment** of ALCI\_RCC5 via a finite quotient construction (12 pages, fourth revision after three rounds of GPT-5.4 Pro review). Full decidability remains open due to the PO gap. The result is **unverified** by human experts.

### Known complexity bounds

| Logic      | Lower Bound          | Upper Bound | Status       |
|------------|----------------------|-------------|--------------|
| ALCI\_RCC5 | PSPACE-hard (Wessel) | PO-coherent fragment decidable (computable, non-elementary) | **PO-coherent fragment decidable** (unverified); full decidability **open** |
| ALCI\_RCC8 | EXPTIME-hard (Wessel)| EXPTIME (if decidable) | **Open** |

---

## A Tableau Calculus for ALCI\_RCC5

### Overview

The tableau constructs a finite **completion graph** --- a complete graph where every pair of nodes has a base relation label, and every node has a concept label (a subset of the Fischer-Ladner closure of the input concept). Unlike tree-based DL tableaux, creating a new node requires assigning it a role to **every** existing node.

### Completion Graphs

A **completion graph** for a concept C\_0 is a tuple G = (V, L, E, <) where:

- V is a finite set of nodes
- L: V -> 2^{cl(C\_0)} assigns concept labels
- E: {(x,y) | x != y} -> {DR, PO, PP, PPI} assigns a base relation to every pair of distinct nodes, respecting converse (E(y,x) = inv(E(x,y)))
- < is a strict total order (creation order)

The **initial completion graph** has a single node x\_0 with L(x\_0) = {C\_0}.

### Blocking Condition

A node x is **blocked** if there exists y < x such that y is not blocked and L(x) = L(y).

This is **equality anywhere-blocking**: the blocker need only precede x in creation order and carry the same label. No pairwise matching (as in standard ALCI tree tableaux) is needed. The simplicity of this condition is made possible by the patchwork property, which decouples type-level structure from specific relational neighborhoods.

### Expansion Rules

**Propositional rules** (deterministic):

- **(and-rule)**: If D1 and D2 in L(x) and D1 or D2 missing: add both to L(x).
- **(or-rule)**: If D1 or D2 in L(x) and neither present: nondeterministically add D1 or D2. *(branching point)*

**Propagation rule** (deterministic):

- **(forall-rule)**: If (forall R.D) in L(x) and E(x,y) = R and D not in L(y): add D to L(y).

**Generating rule** (nondeterministic):

- **(exists-rule)**: If (exists R.D) in L(x), x is active (not blocked), and no y exists with E(x,y) = R and D in L(y):
  1. Create a fresh node y (greatest in creation order).
  2. Set L(y) := {D}.
  3. Set E(x,y) := R.
  4. For each existing node z != x,y: **nondeterministically choose** S\_z in {DR, PO, PP, PPI} and set E(z,y) := S\_z. *(branching point, with constraint filtering)*

### Constraint Filtering

After creating a new node y with edges to all existing nodes, **composition consistency** must hold for every triple of distinct nodes (u,v,w) involving y:

> E(u,w) in comp(E(u,v), E(v,w))

If no assignment of the S\_z values satisfies this for all triples simultaneously, the branch **closes** (clash).

By the patchwork property (Theorem of Renz & Nebel), a simultaneous satisfying assignment exists if and only if every triple involving y is individually satisfiable, i.e., the constraint network is path-consistent. Path consistency can be checked in O(|V|^3).

### Rule Application Strategy

1. Apply (and-rule), (or-rule), and (forall-rule) exhaustively to all nodes.
2. Re-evaluate blocking.
3. Apply one instance of (exists-rule) for an active node with an unsatisfied demand.
4. After adding the new node and its edges, apply (forall-rule) exhaustively (new edges may trigger propagations in both directions, cascading to other nodes).
5. Re-evaluate blocking (label changes may affect blocking status).
6. Repeat from step 1 until no rule applies or a clash is detected.

### Clash Conditions

A completion graph has a **clash** if:

- **(C1)** Some node has {A, not A} in its label for a concept name A.
- **(C2)** Composition consistency is violated for some triple.

A completion graph that is **saturated** (no rule applicable) and **clash-free** is called **open**.

### Termination

Every sequence of rule applications terminates. The final completion graph has at most **2^{O(|C\_0|)}** nodes.

**Argument**:
- Active (non-blocked) nodes have pairwise distinct labels, so there are at most 2^{|cl(C\_0)|} active nodes.
- Labels grow monotonically (rules only add concepts), so each label changes at most |cl(C\_0)| times.
- Each active node has at most |cl(C\_0)| existential demands, each generating at most one witness.
- Total nodes: at most 2^{|cl(C\_0)|} * |cl(C\_0)| = 2^{O(|C\_0|)}.

### Soundness (NOT ESTABLISHED)

**Claimed theorem**: If the tableau produces an open completion graph for C\_0, then C\_0 is satisfiable.

**Status: NOT PROVEN.** The proof sketch below extracts a quasimodel and invokes the Henkin construction, which has the **extension gap** (see below). The quasimodel extraction is correct, but converting the quasimodel to an actual model requires solving a disjunctive constraint network at each Henkin step, and global solvability is not guaranteed (1,911 counterexamples at m=3).

**Proof sketch**: Extract a quasimodel from the open completion graph:
- T = {L(x) | x active}
- P = {(L(x), E(x,y), L(y)) | x != y}
- tau\_0 = L(x\_0)

The quasimodel conditions are verified:
- **(Q1) Existential witness**: Each existential demand exists R.D in a type tau is witnessed by saturation --- there exists a node y with E(x,y) = R and D in L(y).
- **(Q2) Non-emptiness**: DN(tau\_1, tau\_2) != {} for all distinct type pairs, since the completion graph is a complete graph with an edge between every pair.
- **(Q3) Algebraic closure**: For any types tau\_1, tau\_2, tau\_3 and R\_12 in DN(tau\_1, tau\_2), the completion graph's composition consistency (CF) on the witnessing triple gives R\_13 in comp(R\_12, R\_23) with R\_13 in DN(tau\_1, tau\_3) and R\_23 in DN(tau\_2, tau\_3).

By the soundness direction of the main theorem, C\_0 is satisfiable. The quasimodel extracted from the completion graph is "model-like" (all pair-types realized by concrete node pairs), so the Henkin construction succeeds. See the discussion of the **extension gap** below for the subtlety with abstract quasimodels.

### Model Construction: Unfolding the Quasimodel

The quasimodel (or blocked completion graph) is a finite structure. The actual model may be infinite (e.g., when infinite PP-chains are required). The Henkin construction builds this infinite model incrementally, one element at a time. The critical concern is: **can edge assignments to newly created elements trigger "dormant" universal restrictions on existing elements, introducing concepts not present in their types and causing clashes?**

The answer is no. The proof relies on three layers of guarantees:

#### Construction Invariant

At every stage n of the Henkin construction, the partial model maintains:

- **(I1) Type membership**: every element e has tau(e) in T.
- **(I2) Pair-type membership**: for every distinct e\_i, e\_j: (tau(e\_i), R(e\_i,e\_j), tau(e\_j)) in P.
- **(I3) Composition consistency**: every triple satisfies the composition table.
- **(I4) Type permanence**: the type tau(e) is assigned at creation and **never subsequently modified**.

**Proof**: By induction on stages. At stage n+1, the new element e\_{m+1} gets type tau' in T (I1). The edge assignments S\_1,...,S\_m from Claim 5.2 (formulated as a disjunctive constraint network solved via full RCC5 tractability) satisfy (tau(e\_i), S\_i, tau') in P for all i (I2), and all new triples are composition-consistent (I3). No existing type changes (I4).

#### No Dormant Activation (Lemma 5.4 in the paper)

Let e\_i be an existing element with `forall S.D` in tau(e\_i), and let e\_{m+1} be newly created with type tau' and edge R(e\_i, e\_{m+1}) = S\_i. Then:

- **If S\_i = S** (the restriction matches the new edge): then D is already in tau', guaranteed by R-compatibility (condition P1). The concept was placed in tau' at creation. **No propagation occurs.**
- **If S\_i != S**: the restriction does not apply. No issue.

Symmetrically: if `forall inv(S\_i).D` is in tau', then D is already in tau(e\_i) by R-compatibility (P2). Since tau(e\_i) was fixed at an earlier stage (I4), D was already there. **No concept is added to any existing type.**

#### Why Composition Cannot Force Unexpected Propagation (Remark 5.5)

One might worry: what if R(e\_a, e\_b) = U and R(e\_b, e\_{m+1}) = T force R(e\_a, e\_{m+1}) = S where S is the unique element of comp(U, T), and `forall S.D` is in tau(e\_a) but D is not in tau'?

This cannot happen. The extension is formulated as a **disjunctive constraint network** where the domain for each edge (e\_a, e\_{m+1}) is D\_a = {S | (tau(e\_a), S, tau') in P}. Path-consistency enforcement refines these domains, and full RCC5 tractability guarantees a consistent atomic refinement exists. Every S\_a in the solution satisfies (tau(e\_a), S\_a, tau') in P, which by R-compatibility implies D in tau' whenever `forall S\_a.D` is in tau(e\_a). The composition constraints and pair-compatibility constraints are solved **jointly**.

#### Concept Truth (Lemma 5.6 in the paper)

**Lemma**: In the limit model, for every element e and every D in cl(C\_0): D in tau(e) implies e in D^I.

**Proof by structural induction on D**:

- **D = A** (concept name): A^I = {e | A in tau(e)} by construction.
- **D = not A**: not A in tau(e) implies A not in tau(e) (clash-freeness), so e not in A^I, hence e in (not A)^I.
- **D = D1 and D2**: by type condition T1, both D1, D2 in tau(e); by induction, both hold.
- **D = D1 or D2**: by type condition T2, at least one in tau(e); by induction, at least one holds.
- **D = forall R.E**: if forall R.E in tau(e) and (e,e') in R^I, then (tau(e), R, tau(e')) in P by (I2). R-compatibility gives E in tau(e'). By induction, e' in E^I. This holds for **every** R-neighbor, so e in (forall R.E)^I. **This is where Lemma 5.4 applies**: E was already in tau(e') at creation, not propagated.
- **D = exists R.E**: the Henkin construction (fair enumeration) eventually creates a witness e' with R(e,e') = R and E in tau(e'). By induction, e' in E^I.

#### The Role of Monotonicity Along PP-Chains

The model may contain infinite PP-chains: e\_0 PP e\_1 PP e\_2 PP ... For any external element x, Lemma 3.1 (upward monotonicity) constrains the progression of R(x, e\_i):

| R(x, e\_i) | Possible R(x, e\_{i+1}) |
|---|---|
| PP | PP (absorbing) |
| PO | PO, PP (can strengthen, never weaken) |
| DR | DR, PO, PP (can strengthen, never weaken) |
| PPI | PO, EQ, PP, PPI (can transition, never to DR) |

After at most 3 transitions (e.g., DR -> PO -> PP), the relation **stabilizes**. By Lemma 3.3 (downward persistence), DR and PPI are **permanent downward**: once R(x, e\_k) = DR, then R(x, e\_i) = DR for all i <= k.

This has three consequences:

1. **Bounded type variation**: along the chain, only finitely many distinct pair-types (tau(x), S, tau(e\_i)) arise (since S takes at most 4 values and stabilizes). All are in P.

2. **Uniform universal propagation**: once R(x, e\_i) stabilizes to S, the same set of concepts {E | forall S.E in tau(x)} applies to all subsequent chain elements. **No new concept** enters any tau(e\_i) from x's perspective beyond stabilization.

3. **Finite representability**: the types along the chain cycle through finitely many values from T. The monotonicity ensures the "relational profile" eventually becomes periodic. The quasimodel captures all relevant information; the infinite chain is fully determined by its finite abstraction.

Without monotonicity, relations could oscillate (e.g., DR -> PO -> DR -> PO -> ...), generating unbounded pair-type variety. The monotonicity lemmas rule this out.

#### The Extension Gap

The Henkin construction (Claim 5.2) solves a disjunctive constraint network at each step: edges among existing elements are fixed (singletons), and edges to the new element have disjunctive domains D\_i = DN(tau(e\_i), tau'). After path-consistency enforcement, full RCC5 tractability gives a consistent atomic refinement.

However, the enforcement step may **empty** a domain D\_i. Condition (Q3) guarantees that every three-node sub-network is satisfiable, but cascading refinements across multiple triples can remove values needed elsewhere — even when starting from a path-consistent type-level network.

#### Computational investigation of the extension gap

A suite of exhaustive checkers (`extension_gap_checker.py`, `extension_gap_checker_v2.py`, `q3_implies_q3s_check.py`, `model_derived_q3s_fast.py`) systematically tests the extension gap over all small RCC5 configurations. The checkers encode the full RCC5 composition table for the 4 base relations {DR, PO, PP, PPI} (EQ excluded for distinct elements) and enumerate all composition-consistent atomic networks, domain assignments, and type-assignment models.

**Result 1: Q3 (existential) is insufficient.** The extension CSP (arc-consistency enforcement) empties domains for Q3-satisfying configurations. Failures grow rapidly:

| Existing elements m | Configurations tested | Failures (Q3 passes, AC empties domain) |
|---|---|---|
| 2 | 960 | 61 |
| 3 | 319,200 | 1,575 |
| 4 | 21,547,500 | 806,094 |

**Result 2: Q3s (strong/universal) eliminates ALL failures.** Q3s requires: for all R₁₂ ∈ DN(τ₁,τ₂) and **all** R₁₃ ∈ DN(τ₁,τ₃), there exists R₂₃ ∈ DN(τ₂,τ₃) with R₁₃ ∈ comp(R₁₂, R₂₃). This is equivalent to arc-consistency of the extension CSP. Computationally verified: **zero** failures through m=4 (21.5 million configurations).

**Result 3: Q3s is genuinely not extractable from models.** The "representative mismatch" problem identified in the paper's Remark after Q3 is confirmed by exhaustive search. Model-derived DN networks (extracted from concrete, composition-consistent RCC5 models with type assignments) can violate Q3s:

| Model elements | Models tested | Models where DN violates Q3s |
|---|---|---|
| 3 | 492 | 0 |
| 4 | 68,276 | 7,560 (11.1%) |

Violations require ≥ 2 elements of the same type with different relational profiles. Concrete counterexample: 4 elements d₁(A), d₁'(A), d₂(B), d₃(C) with relations d₁-d₂=PP, d₁-d₃=PP, d₁'-d₂=DR, d₁'-d₃=DR, d₂-d₃=PP, d₁-d₁'=DR. The model is composition-consistent, but DN(A,B)={PP,DR}, DN(A,C)={PP,DR}, DN(B,C)={PP}, and Q3s fails: for R₁₂=PP and R₁₃=DR, comp(PP,PP)={PP} which does not contain DR.

**Summary:**

| Property | Sufficient for extension? | Extractable from models? |
|---|---|---|
| Q3 (existential) | **No** (1,575 failures at m=3) | **Yes** |
| Q3s (strong/universal) | **Yes** (0 failures through m=4) | **No** (7,560 model-derived violations) |

The extension gap is **genuine and unavoidable** within the quasimodel framework as formulated. No condition on the DN sets is simultaneously sufficient for the Henkin construction and extractable from models. Moreover, the type elimination algorithm is **unsound** even before the extension gap is reached — see the next section.

#### Computational discovery: the type elimination algorithm is unsound (rejects satisfiable concepts)

A systematic computational investigation ([`extension_gap_concrete.py`](https://github.com/lambdamikel/alcircc5/blob/master/extension_gap_concrete.py)) reveals that the type elimination algorithm described in Section 6 of the paper is **unsound** — it can reject satisfiable concepts (false negatives). This is a stronger result than the extension gap: the algorithm itself is broken, not just the Henkin construction.

**Concrete counterexample.** The concept

> C₁ = ∃PO.D ⊓ ∃DR.(B ⊓ ∀PO.¬D) ⊓ ∀DR.¬D ⊓ ∀PP.¬D ⊓ ∀PPI.¬D

is satisfiable with 3 elements:

| Element | Atoms | Role to e₀ | Role to e₁ | Role to e₂ |
|---|---|---|---|---|
| e₀ (root) | ∅ | — | DR | PO |
| e₁ (B-filler) | {B} | DR | — | DR |
| e₂ (D-element) | {D} | PO | DR | — |

Composition consistency verified for all 6 directed triples. C₁ satisfaction at e₀ verified. Yet the type elimination algorithm rejects C₁: **0 types survive** from the initial 128.

**Root cause: Q2 + Q3 cascade elimination.** The algorithm starts with all 128 valid Hintikka types for cl(C₁) and applies three conditions:
- **(Q1)** existential witnesses — every ∃R.D in a type has a witness type reachable via R
- **(Q2)** completeness — every pair of distinct types in the surviving set has non-empty DN
- **(Q3)** algebraic closure — every triple of types has a composition-consistent extension

The cascade:
1. **Q3 is anti-monotone in T**: the condition "for EVERY τ₃ ∈ T" becomes harder to satisfy as T grows. Starting with 128 types, Q3 aggressively prunes DN entries because many type pairs have incompatible ∀-constraints (e.g., types with D and ∀DR.¬D have DN=∅ with other D-types).
2. **Q3 kills valid pairs**: the model pair (τ₀, DR, τ₁) is pruned because some type τ₃ ∉ {τ₀,τ₁,τ₂} has DN(τ₁,τ₃)=∅, failing Q3's universal requirement.
3. **Q1 cascades**: types that lose their Q1 witnesses (due to Q3 pruning DN entries) are eliminated.
4. **Q2 cascades**: types eliminated by Q1 cause Q2 failures for types that depended on them.
5. **Result**: the greatest fixpoint converges to the empty set.

**The model types form a valid quasimodel among themselves.** When the type elimination is restricted to just the 3 model-extracted types {τ₀, τ₁, τ₂} with compatible DN:

| Pair | DN |
|---|---|
| DN(τ₀, τ₁) | {DR, PO, PPI} (after Q3 prunes PP) |
| DN(τ₀, τ₂) | {PO} |
| DN(τ₁, τ₂) | {DR} |

All conditions pass: Q1 ✓ (witnesses exist), Q2 ✓ (all pairs non-empty), Q3 ✓ (pairwise-distinct triples consistent). **The algorithm cannot find this valid subset because the greatest fixpoint approach starts with all types and Q3's anti-monotonicity poisons the elimination.**

**The fundamental algorithmic flaw.** For standard ALCI (without spatial constraints), type elimination uses only Q1 (existential witnesses). Q1 is anti-monotone (removing types hurts Q1), so the greatest fixpoint correctly finds the largest self-sustaining type set. For ALCI\_RCC5, Q3 adds a cross-cutting condition: larger T makes Q3 harder (more types to satisfy universally), but Q1 still needs more types for witnesses. These opposing forces make the greatest fixpoint approach incorrect:

- A valid quasimodel S ⊆ Tp(C₀) exists (the model types)
- S satisfies Q1+Q2+Q3 internally
- But the greatest fixpoint starting from Tp(C₀) ⊋ S eliminates all of S
- Because Q3 with types from Tp(C₀) \ S kills DN entries needed by S

A correct algorithm would need **subset search** (find S ⊆ Tp(C₀) where Q1+Q2+Q3 hold internally), which is computationally harder than greatest-fixpoint elimination and unlikely to be EXPTIME.

**Additional bug: Q3 soundness proof (lines 882-888 of the paper).** The proof of Q3 for the case τ₂ = τ₃ with a unique element uses R₂₃ = EQ, asserting that comp(R₁₂, EQ) = {R₁₂}. But DN is defined over NR \ {EQ}, so EQ ∉ DN(τ₂, τ₂). The proof silently places EQ in DN, contradicting the definition. This means the soundness direction (model → quasimodel) also has a gap for Q3 with "not necessarily distinct" types when a type has singleton multiplicity.

**Computational verification** ([`extension_gap_concrete.py`](https://github.com/lambdamikel/alcircc5/blob/master/extension_gap_concrete.py), [`quasimodel_debug.py`](https://github.com/lambdamikel/alcircc5/blob/master/quasimodel_debug.py)):

| Test | Result |
|---|---|
| Model validity (3 elements, composition consistency) | ✓ All 6 triples consistent |
| C₁ satisfaction at e₀ | ✓ |
| Q1-only elimination (128 types, no Q2/Q3) | 128 types survive, 4 root types |
| Q1+Q2 elimination (no Q3) | 0 types survive (Q2 cascade) |
| Q1+Q2+Q3 elimination (paper's algorithm) | 0 types survive |
| Model types only, Q1+Q2+Q3 (restricted) | **3 types survive, 1 root type** ✓ |

**Impact on the paper's claims:**
- **Theorem 5.1 (quasimodel characterization)**: Both directions have gaps. Soundness: Q3 with "not necessarily distinct" fails for singleton-multiplicity types. Completeness: extension gap (Remark 5.4).
- **Theorem 6.1 (EXPTIME decidability via type elimination)**: **Wrong.** The algorithm rejects the satisfiable concept C₁.
- **Decidability of ALCI\_RCC5**: **Remains genuinely open.** The type elimination approach is broken. A correct decision procedure would require either subset search (expensive), an entirely different algorithmic framework, or a new quasimodel formulation that avoids the Q2/Q3 anti-monotonicity trap.

#### Earlier implications (extension gap only)

The extension gap results (prior to the type elimination unsoundness discovery) showed:
- The characterization theorem is established as an **if**: every satisfiable concept has a quasimodel (soundness — modulo the Q3 bug for singleton-multiplicity types).
- The **only-if** direction (every quasimodel gives a model) holds for model-derived quasimodels but remains open for abstract quasimodels.
- The tableau's soundness proof extracts a quasimodel from a completion graph — a "model-like" structure where all pair-types are realized — but the subsequent Henkin construction has the extension gap (global solvability of the disjunctive constraint network is not guaranteed).

#### Possible paths forward

1. **Strategic Henkin construction**: instead of proving the extension CSP is always solvable, show that with careful ordering of element creation and relation assignment, unsolvable CSPs can always be avoided. This would be a game-theoretic argument.
2. **Model saturation**: enrich the type system so that every element realizes all pair-types of its type (condition "Q4"), making Q3s extractable at the cost of (doubly) exponentially more types.
3. **Compactness + patchwork**: argue model existence without explicit construction, using the fact that every finite sub-problem of the Henkin construction is satisfiable.
4. **Alternative proof architecture**: the contextual tableau approach (GPT-5.4) avoids the extension gap entirely, with the gap on the other side (completeness/extraction).

### Completeness

**Theorem**: If C\_0 is satisfiable, then there exists a sequence of nondeterministic choices yielding an open completion graph.

**Proof sketch**: Given a model I with d\_0 in C\_0^I, maintain a guide function pi: V -> Delta^I mapping tableau nodes to model elements, with invariants:
- L(x) is a subset of the type of pi(x) in I
- E(x,y) equals the actual relation between pi(x) and pi(y) in I

The model guides all nondeterministic choices:
- **(or-rule)**: choose the disjunct true at pi(x)
- **(exists-rule)**: set pi(y) = d' where d' witnesses the demand in I; choose S\_z = relation between pi(z) and d' in I

Clash-freeness follows from the model satisfying composition and type consistency. Blocked nodes' demands need not be directly satisfied in the completion graph --- they are satisfied in the infinite model constructed from the extracted quasimodel.

### Comparison with Tree-Based DL Tableaux

| Feature | Standard ALCI Tableau | ALCI\_RCC5 Tableau |
|---------|----------------------|-------------------|
| Structure | Forest (tree per root) | **Complete graph** |
| New node edges | Single edge to parent | **Edge to every existing node** |
| Structural invariant | Tree shape | **Composition consistency (CF)** |
| Blocking | Pairwise (node + parent match) | **Simple type equality** |
| Soundness | Direct model readoff | **Indirect: quasimodel extraction + Henkin** |
| Key enabler | Tree model property | **Patchwork property** |

---

## Concrete Domains vs. Composition-Based Role Boxes

An important distinction must be drawn between two fundamentally different approaches to combining description logics with spatial reasoning. Several decidability results exist for DLs with RCC constraints, but they all use the **concrete domain** formalism, which is expressively incomparable with the composition-based role box approach of ALCI\_RCC.

| Approach | Spatial constraints via | Can express ∀PP.C ? | Can express ∃DR.D ? | Quantify over spatial relations? |
|---|---|---|---|---|
| **Concrete domains** (ALC(RCC8)) | Functional roles to concrete values | No | No | No |
| **Composition-based role boxes** (ALCI\_RCC5) | Spatial relations serve as roles directly | **Yes** | **Yes** | **Yes** |

### Prior decidability results (concrete domain approach)

- **Lutz & Milicic (2007)**: ALC with omega-admissible concrete domains (including RCC5, RCC8) is decidable. No inverse roles.
- **Borgwardt, De Bortoli & Koopmann (2024)**: ALC(D) ontology consistency is EXPTIME-complete for omega-admissible D. ALC only, no inverse roles.
- **Baader & Rydval (2020)**: Strengthened undecidability results and generalized omega-admissibility conditions for DLs with concrete domains and GCIs. Refines the decidability boundary within the concrete domain paradigm.
- **Demri & Gu (CSL 2026)**: Extended the automata-based approach to handle **inverse roles**, functional role names, and constraint assertions, establishing EXPTIME membership. This is the closest published result to ALCI\_RCC, as it combines inverse roles with RCC-like spatial constraints. However, it still operates within the concrete domain formalism.

### Why the gap remained open

None of these results settle the decidability of ALCI\_RCC5 or ALCI\_RCC8, because the composition-based role box approach allows **quantification over spatial relations** --- concepts like ∀PP.C ("all proper parts satisfy C") and ∃DR.D ("some disconnected region satisfies D") --- which are inexpressible in the concrete domain setting. The two formalisms are complementary: concrete domains reason about spatial *attributes* of elements; ALCI\_RCC captures direct spatial *relationships* between elements.

A key insight explored in these papers is the **patchwork property** from qualitative constraint reasoning (Renz & Nebel 1999), which was known contemporaneously with Wessel's original work but had not been connected to the description logic decidability question. The patchwork property (local consistency implies global consistency for atomic RCC5 networks) and full RCC5 tractability (extending this to disjunctive networks) are central tools in all proof attempts. However, applying them at the global level — assigning consistent edges across the entire unraveled complete-graph model — remains the unsolved step.

---

## Files

- [**`direct_soundness_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/direct_soundness_ALCIRCC5.pdf) -- **Direct soundness without Henkin construction** (eleventh approach): analyzes demand satisfaction in tableau completion graphs. Identifies unique algebraic obstruction (PPI ∉ comp(DR,PPI)), classifies relations as rigid vs diluting, establishes a trichotomy. Cross-chain edge assignment remains conjectural. (8 pages) ([source](https://github.com/lambdamikel/alcircc5/blob/master/direct_soundness_ALCIRCC5.tex))
- [**`LRCC8_vs_ALCIRCC8.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/LRCC8_vs_ALCIRCC8.pdf) -- **Why L\_RCC8 undecidability does not transfer to ALCI\_RCC8** (tenth approach/analysis): proves the Lutz-Wolter domino reduction fails for abstract models due to the coincidence obstruction first identified by Wessel (2002/2003). Documents technical priority: Wessel's even-odd chain, grid construction (Figure 10), and coincidence gap (Figure 11) predate Lutz-Wolter by 3-4 years. (11 pages) ([source](https://github.com/lambdamikel/alcircc5/blob/master/LRCC8_vs_ALCIRCC8.tex))
- [**`MSO_encoding_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/MSO_encoding_ALCIRCC5.pdf) -- **Borel-MSO encoding via interval semantics** (ninth approach): reduces ALCI\_RCC5 satisfiability to Borel-MSO over (R, <) using the interval representation of RCC5. Composition consistency is automatic. Full MSO is undecidable; Borel-MSO is decidable (Manthe 2024). One technical gap: Dyck-matching endpoint pairing. (16 pages) ([source](https://github.com/lambdamikel/alcircc5/blob/master/MSO_encoding_ALCIRCC5.tex))
- [**`tableau_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/tableau_ALCIRCC5.pdf) -- **Tableau calculus with Tri-neighborhood blocking** (third revision): soundness and completeness proved, but **termination disproved** via frontier-advancement counterexample. Three-part blocking condition: (i) same label, (ii) same Tri set, (iii) same TNbr signature. (16 pages) ([source](https://github.com/lambdamikel/alcircc5/blob/master/tableau_ALCIRCC5.tex))
- [**`decidability_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/decidability_ALCIRCC5.pdf) -- Main paper: quasimodel approach (22 pages, revised)
- [**`decidability_ALCIRCC5.tex`**](https://github.com/lambdamikel/alcircc5/blob/master/decidability_ALCIRCC5.tex) -- LaTeX source for main paper
- [**`ALCI_RCC5_contextual_tableau_draft.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/ALCI_RCC5_contextual_tableau_draft.pdf) -- Contextual tableau paper by GPT-5.4 Pro; starting point for the FW(C,N) discussion ([source](https://github.com/lambdamikel/alcircc5/blob/master/ALCI_RCC5_contextual_tableau_draft.tex))
- [**`FW_proof_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/FW_proof_ALCIRCC5.pdf) -- Counterexample to FW(C,N): the contextual tableau's completeness conjecture is false (7 pages)
- [**`FW_proof_ALCIRCC5.tex`**](https://github.com/lambdamikel/alcircc5/blob/master/FW_proof_ALCIRCC5.tex) -- LaTeX source for FW counterexample
- [**`ALCI_RCC5_status_after_FW.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/ALCI_RCC5_status_after_FW.pdf) -- GPT-5.4's status assessment after FW failure; proposes omega-model direction ([source](https://github.com/lambdamikel/alcircc5/blob/master/ALCI_RCC5_status_after_FW.tex))
- [**`triangle_blocking_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/triangle_blocking_ALCIRCC5.pdf) -- Triangle-type approach: conditional decidability of ALCI\_RCC5 via triangle-filtered model construction. Supersedes the retracted paper below. (12 pages) ([source](https://github.com/lambdamikel/alcircc5/blob/master/triangle_blocking_ALCIRCC5.tex))
- [**`two_tier_quotient_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/two_tier_quotient_ALCIRCC5.pdf) -- Two-tier quotient: period descriptors + PP-kernel nodes. Fourth revision (April 2026) after three rounds of GPT-5.4 review. Proves decidability of PO-coherent fragment; documents PO gap with counterexample (12 pages) ([source](https://github.com/lambdamikel/alcircc5/blob/master/two_tier_quotient_ALCIRCC5.tex))
- [**`closing_extension_gap_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/closing_extension_gap_ALCIRCC5.pdf) -- Companion paper: identifies root cause of extension gap (self-absorption failure) and attempts decidability via direct model construction. **Retracted**: Theorem 5.5 is false (10 pages) ([source](https://github.com/lambdamikel/alcircc5/blob/master/closing_extension_gap_ALCIRCC5.tex))
- [**`response_to_status_note.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/response_to_status_note.pdf) -- Claude's response to GPT's status assessment: corrections, evaluation, and a concrete sub-question ([source](https://github.com/lambdamikel/alcircc5/blob/master/response_to_status_note.tex))
- [**`response_to_gpt_blocking.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/response_to_gpt_blocking.pdf) -- Claude's assessment of GPT's 4-paper blocking series: verifies local results, identifies unraveling gap (9 pages) ([source](https://github.com/lambdamikel/alcircc5/blob/master/response_to_gpt_blocking.tex))
- [**`response_to_gpt_review.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/response_to_gpt_review.pdf) -- Claude's response to GPT's review: accepts both criticisms, retracts decidability claim, analyzes convergence (5 pages) ([source](https://github.com/lambdamikel/alcircc5/blob/master/response_to_gpt_review.tex))
- [**`decidability_proof_ALCIRCC5.md`**](https://github.com/lambdamikel/alcircc5/blob/master/decidability_proof_ALCIRCC5.md) -- Earlier proof sketch (quasimodel method only)
- [**`CONVERSATION.md`**](https://github.com/lambdamikel/alcircc5/blob/master/CONVERSATION.md) -- Full conversation log between Michael Wessel and Claude

### GPT-5.4 Pro papers (profile-cached blocking series)

- [**`gpt/alcircc5_blocking_draft.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/gpt/alcircc5_blocking_draft.pdf) -- Paper 1: Profile-cached global blocking, conditional on classwise normalization lemma ([source](https://github.com/lambdamikel/alcircc5/blob/master/gpt/alcircc5_blocking_draft.tex))
- [**`gpt/alcircc5_blocking_revised.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/gpt/alcircc5_blocking_revised.pdf) -- Paper 2: Self-correction — flat normalization false, introduces coherent predecessor blocks ([source](https://github.com/lambdamikel/alcircc5/blob/master/gpt/alcircc5_blocking_revised.tex))
- [**`gpt/alcircc5_blocking_explicit_signatures.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/gpt/alcircc5_blocking_explicit_signatures.pdf) -- Paper 3: Explicit depth-indexed signature construction, proves finite-index lemma (PDF only)
- [**`gpt/alcircc5_blocking_replay_final.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/gpt/alcircc5_blocking_replay_final.pdf) -- Paper 4: Meet-semilattice approach, robust colorwise normalization — gap in blocked unraveling theorem ([source](https://github.com/lambdamikel/alcircc5/blob/master/gpt/alcircc5_blocking_replay_final.tex))

### GPT-5.4 Pro reviews

- [**`review/review_closing_extension_gap_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/review/review_closing_extension_gap_ALCIRCC5.pdf) -- GPT's review of Claude's companion paper: identifies algebraic error in Lemma 3.2 and counterexample to Theorem 5.5 ([source](https://github.com/lambdamikel/alcircc5/blob/master/review/review_closing_extension_gap_ALCIRCC5.tex))
- [**`review2/response_to_two_tier_quotient_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/review2/response_to_two_tier_quotient_ALCIRCC5.pdf) -- GPT's review of Claude's two-tier quotient paper: five objections against the decidability claim ([source](https://github.com/lambdamikel/alcircc5/blob/master/review2/response_to_two_tier_quotient_ALCIRCC5.tex))
- [**`review2/response_to_gpt_review.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/review2/response_to_gpt_review.pdf) -- Claude's response to GPT's first review: accepts 3 objections as valid (fixable), 2 as partially valid; provides concrete fixes (8 pages) ([source](https://github.com/lambdamikel/alcircc5/blob/master/review2/response_to_gpt_review.tex))
- [**`review3/response_to_revised_two_tier_quotient_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/review3/response_to_revised_two_tier_quotient_ALCIRCC5.pdf) -- GPT's second review of two-tier quotient: four objections (off-period PP demands, constant interfaces, blocking claim, lift lemma) ([source](https://github.com/lambdamikel/alcircc5/blob/master/review3/response_to_revised_two_tier_quotient_ALCIRCC5.tex))
- [**`review3/response_to_gpt_second_review.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/review3/response_to_gpt_second_review.pdf) -- Claude's response to GPT's second review: adds all-phase safety lemma, chain-unfolding lift, strengthened T4/V6 ([source](https://github.com/lambdamikel/alcircc5/blob/master/review3/response_to_gpt_second_review.tex))
- [**`review4/response_to_latest_two_tier_revision.tex`**](https://github.com/lambdamikel/alcircc5/blob/master/review4/response_to_latest_two_tier_revision.tex) -- GPT's third review of two-tier quotient: four objections (phasewise safety, exact-relation extraction, circular size bound, regular-node blocking)
- [**`review4/response_to_gpt_third_review.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/review4/response_to_gpt_third_review.pdf) -- Claude's response to GPT's third review: resolves 3 of 4 objections, discovers genuine PO gap with counterexample (7 pages) ([source](https://github.com/lambdamikel/alcircc5/blob/master/review4/response_to_gpt_third_review.tex))

### Computational verification scripts

- [**`extension_gap_checker.py`**](https://github.com/lambdamikel/alcircc5/blob/master/extension_gap_checker.py) -- Exhaustive extension gap checker. Encodes the full RCC5 composition table for base relations {DR, PO, PP, PPI}. Enumerates all composition-consistent atomic networks on m nodes (`enumerate_consistent_networks`), then for each network and all possible domain assignments D\_i ⊆ {DR,PO,PP,PPI}, runs arc-consistency enforcement (`run_path_consistency`) on the extension CSP. Phase 1 tests all domain assignments; Phase 2 filters by existential Q3 compatibility. Confirmed: Q3-compatible configurations can fail (1,575 at m=3, 806,094 at m=4).
- [**`extension_gap_checker_v2.py`**](https://github.com/lambdamikel/alcircc5/blob/master/extension_gap_checker_v2.py) -- Tests existential Q3 vs universal Q3 (= Q3s = arc-consistency). For each configuration that fails arc-consistency enforcement, checks whether existential Q3 or universal Q3 was satisfied on the initial domains. Key finding: universal Q3 eliminates **all** failures (0 through m=4).
- [**`q3_implies_q3s_check.py`**](https://github.com/lambdamikel/alcircc5/blob/master/q3_implies_q3s_check.py) -- Tests two questions on abstract DN networks over 2-3 types: (1) does Q3 imply Q3s? (No: 1,803 counterexamples at 3 types.) (2) Does satisfiable DN imply Q3s? (No: 2,697 counterexamples.) Operates on the type-level DN constraint network (not individual models).
- [**`model_derived_q3s_fast.py`**](https://github.com/lambdamikel/alcircc5/blob/master/model_derived_q3s_fast.py) -- The definitive test: enumerates all concrete, composition-consistent RCC5 models with 3-4 elements and 2-3 types, extracts model-derived DN sets, and checks Q3s. Includes a hand-verified counterexample (4 elements, 3 types). Result: 7,560 out of 68,276 models (11.1%) produce DN networks violating Q3s. Confirms that Q3s is genuinely not extractable from models.

### PP-kernel quotient investigation

- [**`pp_kernel_analysis.py`**](https://github.com/lambdamikel/alcircc5/blob/master/pp_kernel_analysis.py) -- Tests reflexive PP composition-consistency (universal self-absorption), determines which relations allow safe reflexive loops (DR fails, PP/PPI pass), analyzes PP-chain monotonicity and stabilization, and checks collapsing safety for all base relations.
- [**`pp_kernel_quotient.py`**](https://github.com/lambdamikel/alcircc5/blob/master/pp_kernel_quotient.py) -- Tests the disjunctive {PP,PPI} quotient approach: path-consistency of disjunctive edges, ∀-safety in periodic tails, ∃-satisfaction analysis. Key finding: PP-transitivity forces linear order, preventing PP-cycles needed for multi-type periodic chains. 6/15 two-type demand patterns are satisfiable; bidirectional demands fail.
- [**`pp_kernel_cycle_analysis.py`**](https://github.com/lambdamikel/alcircc5/blob/master/pp_kernel_cycle_analysis.py) -- Analyzes PP-cycle obstruction: exhaustive 3-node check (no PP-cycles possible), demand satisfaction analysis (only ∃PP stays in-chain), period descriptor approach (finite word representation), and the two-tier hybrid architecture. Generates and validates 56 toy 2-type period descriptors.
- [**`gap_closing_verification.py`**](https://github.com/lambdamikel/alcircc5/blob/master/gap_closing_verification.py) -- Verifies all algebraic facts needed for the decidability proof: composition table non-emptiness, PP/PPI dual absorption, stabilized relation consistency, T∞ witness property, and extension arc-consistency (0 failures across 164 two-element and 128 three-element configurations).

### Extension gap root cause investigation scripts

- [**`self_absorption_analysis.py`**](https://github.com/lambdamikel/alcircc5/blob/master/self_absorption_analysis.py) -- Root cause analysis: maps all self-absorption failures in the RCC5 composition table, identifies comp(DR,PPI)={DR} as the unique asymmetric failure, analyzes containment collapse (comp(DR,PPI)^k = {DR} for all k), and verifies the resolution via forced DR edge enrichment.
- [**`cross_subtree_investigation.py`**](https://github.com/lambdamikel/alcircc5/blob/master/cross_subtree_investigation.py) -- Investigates ancestor projection strategy for boundary handling, proves self-safety theorem (S ∈ comp(S,S) for all S), analyzes PPI-chain propagation and mixed chains.
- [**`drpp_deep_analysis.py`**](https://github.com/lambdamikel/alcircc5/blob/master/drpp_deep_analysis.py) -- Deep analysis of DR+PP problematic case: modified profile-copy approach, ∀-constraint mismatch detection, enrichment cascade analysis.
- [**`drpp_extension_investigation.py`**](https://github.com/lambdamikel/alcircc5/blob/master/drpp_extension_investigation.py) -- One-step extension solvability verification (45,528/45,528 pass) and PP-avoidability analysis (0 forced PP assignments).
- [**`profile_blocking_drpp.py`**](https://github.com/lambdamikel/alcircc5/blob/master/profile_blocking_drpp.py) -- Initial investigation of DR+PP case for profile-based blocking strategy.

### Triangle-type blocking investigation

- [**`triangle_closure_check.py`**](https://github.com/lambdamikel/alcircc5/blob/master/triangle_closure_check.py) -- Tests the triangle-type blocking approach on 68,276 models. Four-part check: (1) GPT counterexample handling, (2) systematic STC/extension CSP, (3) failure classification (all failures are would-be-expanded), (4) cross-context robustness. Key result: zero genuine failures — when T-closed extensions exist, T-filtered arc-consistency always finds them.
- [**`triangle_type_saturation_check.py`**](https://github.com/lambdamikel/alcircc5/blob/master/triangle_type_saturation_check.py) -- Tests whether abstract triangle-type sets stabilize for the PO-incoherent counterexample. Builds a 24-element PP-chain with 12 PO-witnesses, verifies composition consistency, computes abstract triangle-type sets for every node, and generates comparison matrices. Key result: **all three node types stabilize at k=2** (τ\_A: 68 types, τ\_B: 56 types, σ: 57 types). Interior nodes have exactly identical abstract triangle-type sets. Verified for both DR-backward and PP-backward branches.
- [**`profile_blocking_check.py`**](https://github.com/lambdamikel/alcircc5/blob/master/profile_blocking_check.py) -- Verifies that node-identity-based profile blocking does NOT terminate: enumerates all valid RCC5 assignments for chains of length 4/6/8 via arc-consistency propagation, confirms the sliding PO diagonal pattern, and shows that no two τ\_A nodes ever have matching node-identity profiles.
- [**`tri_neighborhood_check.py`**](https://github.com/lambdamikel/alcircc5/blob/master/tri_neighborhood_check.py) -- Tests Wessel's strengthened blocking condition: Tri-neighborhood equivalence requires not only Tri(x) = Tri(y) but also that neighbors' Tri sets match per (relation, type) pair. Key result: the strengthened condition **also stabilizes**, at k=3 (one step later than basic Tri at k=2). Interior nodes d₆–d₁₆ (τ\_A), d₇–d₁₇ (τ\_B), w₃–w₈ (σ) are fully Tri-neighborhood equivalent.

## Implementation: ALCI\_RCC5 Concept Satisfiability Reasoner

[**`alcircc5_reasoner.py`**](https://github.com/lambdamikel/alcircc5/blob/master/alcircc5_reasoner.py) is a working implementation of a concept satisfiability checker for ALCI\_RCC5. It implements a **constructive quasimodel search** that builds candidate quasimodels bottom-up and verifies them using disjunctive path-consistency of RCC5 constraint networks.

### Algorithm

1. Parse input concept in negation normal form (NNF)
2. Compute Fischer-Ladner closure
3. Enumerate all Hintikka types over the closure
4. Compute SAFE relations between all type pairs (relations R such that all ∀R.C constraints in both types are satisfied)
5. **Bottom-up quasimodel construction:**
   - Start from each root type (containing the input concept)
   - Add witness types for unsatisfied existential demands (∃R.C)
   - After each addition, verify that the SAFE constraint network over the current type set is **disjunctive path-consistent**: for each pair of types, the domain is the SAFE set; arc-consistency propagation removes relations that have no support through intermediate types
   - By the **RCC5 patchwork property** (Renz & Nebel 1999), path-consistent disjunctive networks are globally satisfiable, making this check both **sound** (rejects only genuinely unsatisfiable configurations) and **complete** (accepts all satisfiable ones)
   - Backtrack if path-consistency fails; try alternative witness types
   - **Sibling compatibility check**: for each type with multiple demands (R₁,D₁),...,(Rₖ,Dₖ), verify that witnesses j₁,...,jₖ can be chosen jointly such that comp(INV[Rₘ], Rₘ') ∩ SAFE(jₘ, jₘ') ≠ ∅ for all pairs. When Rₘ ≠ Rₘ', the witnesses must be distinct elements even if they share the same type — the pairwise check is required. Same-type bypass is valid only when Rₘ = Rₘ' (one element serves both demands). Uses CSP with arc-consistency + backtracking.
6. Accept iff some root type leads to a valid quasimodel

### Key design decisions

- **Three necessary conditions replace Q3/Q4.** The original conditions Q3/Q4 universally quantify over all safe relations, which is too strict. The replacement is three necessary conditions: (1) **disjunctive path-consistency** of the SAFE network; (2) **sibling compatibility** — joint witness assignment for co-demanded roles via CSP; (3) **role-path compatibility** — grandchild-grandparent connectivity through composition chains with iterative witness pruning. All three are extractable from any model, making UNSAT provably sound.

- **Deterministic type enumeration.** Closure concepts are sorted by string representation before building atoms. All frozenset iterations in the search use `sorted()`. This ensures the reasoner always produces the same type set regardless of Python's hash randomization.

- **Bottom-up construction avoids GFP non-monotonicity.** The original greatest-fixpoint type elimination is non-monotone: removing one type can make another supportable. This caused the algorithm to reject satisfiable concepts (e.g., C₁ from the paper). The constructive approach only checks consistency of types actually in the candidate quasimodel.

### Test results

```
python3 alcircc5_reasoner.py
```

18 basic test cases plus a comprehensive stress test of **713 concepts** across seven categories (known SAT, known UNSAT, adversarial cross-role universals, systematic role-atom combinations, and random concepts of depths 2-4). **Zero correctness errors.** The sibling check correctly catches cross-role universal contradictions like ∃PP.(∀PPI.A) ⊓ ∃PPI.¬A (UNSAT: comp(PPI,PPI) = {PPI} forces the universal to fire on the sibling).

### Henkin tree extension test

[**`henkin_extension_test.py`**](https://github.com/lambdamikel/alcircc5/blob/master/henkin_extension_test.py) validates the Henkin construction by building actual tree models from quasimodel type sets. For each SAT concept, it:

1. Gets the quasimodel type set T from the reasoner
2. Builds a depth-4 Henkin tree, adding witnesses level by level
3. At each extension, computes the star network D(new, x) = comp(INV[R], ρ(parent, x)) ∩ SAFE(new_type, x_type) for all existing nodes x
4. Runs star arc-consistency and finds a consistent atomic assignment
5. Uses a **precomputed witness plan** (sibling-compatible assignment per type) with limited backtracking over alternative witnesses

**Result: zero failures for all basic tests across 12 hash seeds.** The future-flexibility ordering (PO > DR > PP > PPI) ensures cross-relations keep compositions wide at deeper tree levels. In the stress test, 8 Henkin failures occur at depths 2-3 for concepts that are satisfiable in cyclic models but whose tree unfoldings have cross-level composition conflicts — these are tree-model limitations, not reasoner bugs.

### Limitations

- Exponential in closure size (enumerates all Hintikka types)
- Not optimized for large concepts; designed as a proof-of-concept
- The constructive search uses backtracking with depth bound, so may not find all satisfying quasimodels

## References

1. M. Wessel. ["Qualitative Spatial Reasoning with the ALCI\_RCC Family -- First Results and Unanswered Questions."](https://github.com/lambdamikel/alcircc5/blob/master/report7.pdf) Technical Report FBI-HH-M-324/03, University of Hamburg, 2002/2003.

2. M. Wessel. ["Decidable and Undecidable Extensions of ALC with Composition-Based Role Inclusion Axioms."](https://github.com/lambdamikel/alcircc5/blob/master/report5.pdf) Technical Report FBI-HH-M-301/01, University of Hamburg, 2000.

3. M. Wessel. ["Undecidability of ALC\_RA."](https://github.com/lambdamikel/alcircc5/blob/master/report6.pdf) Technical Report FBI-HH-M-302/01, University of Hamburg, 2001.

4. M. Wessel. ["Obstacles on the Way to Spatial Reasoning with Description Logics: Undecidability of ALC\_RA⊖."](https://github.com/lambdamikel/alcircc5/blob/master/report4.pdf) Technical Report FBI-HH-M-297/00, University of Hamburg, 2000.

5. J. Renz and B. Nebel. "On the Complexity of Qualitative Spatial Reasoning: A Maximal Tractable Fragment of the Region Connection Calculus." Artificial Intelligence, 108(1-2):69-123, 1999.

6. J. Renz. "Maximal Tractable Fragments of the Region Connection Calculus: A Complete Analysis." IJCAI 1999.

7. C. Lutz and F. Wolter. "Modal Logics of Topological Relations." Logical Methods in Computer Science, 2(2), 2006. **Key result: L\_RCC8 undecidable (domino tiling via TPP/NTPP); L\_RCC5(RS^∃) undecidable (S5³ via supremum closure); L\_RCC5(RS) = ALCI\_RCC5 satisfiability explicitly left open (p. 31).**

8. C. Lutz and M. Milicic. "A Tableau Algorithm for Description Logics with Concrete Domains and General TBoxes." Journal of Automated Reasoning, 38:227-259, 2007.

9. S. Borgwardt, F. De Bortoli, P. Koopmann. "The Precise Complexity of Reasoning in ALC with omega-Admissible Concrete Domains." KR 2024.

10. F. Baader and M. Rydval. "Description Logics with Concrete Domains and General Concept Inclusions Revisited." IJCAR 2020, LNCS 12166, pp. 413-431.

11. S. Demri and T. Gu. "Robustness of Constraint Automata for Description Logics with Concrete Domains." CSL 2026, LIPIcs Vol. 363.

12. M. Bodirsky and V. Bodor. "A Complexity Dichotomy in Spatial Reasoning via Ramsey Theory." ACM Transactions on Computational Logic (TOCL), 25(2), 2024. (Earlier version: arXiv:2008.10261, 2020.)

13. M. Bodirsky. *Complexity of Infinite-Domain Constraint Satisfaction.* Lecture Notes in Logic, vol. 52, Cambridge University Press, 2021.

14. S. Shelah. "The Monadic Theory of Order." Annals of Mathematics, 102(3):379-419, 1975. (Proved undecidability of full MSO over (R, <); decidability for countable ordinals.)

15a. Y. Gurevich and S. Shelah. "Monadic Theory of Order and Topology in ZFC." Annals of Mathematical Logic, 23(2-3):179-198, 1982. (Removed CH assumption from Shelah's undecidability result.)

15b. U. Manthe. "The Borel Monadic Theory of Order is Decidable." arXiv:2410.00887, October 2024. (Proved decidability of Borel-MSO over (R, <); the key result enabling our ninth approach.)

15. D. Bresolin, D. Della Monica, V. Goranko, A. Montanari, G. Sala. "The Dark Side of Interval Temporal Logic: Marking the Undecidability Border." Annals of Mathematics and AI, 71(1-3):41-83, 2014. (Conference version: "B and D Are Enough to Make the Halpern-Shoham Logic Undecidable," ICALP 2010.)

16. R. Kontchakov, F. Wolter, M. Zakharyaschev. "Logic of Metric Spaces and LS-Spaces." Logical Methods in Computer Science, 6(3), 2010. (See also: "Modal Logics of Topological Relations.")

17. J. Halpern and Y. Shoham. "A Propositional Modal Logic of Time Intervals." J. ACM, 38(4):935-962, 1991.

## Acknowledgments

This research was prompted by Michael Wessel (miacwess@gmail.com), who introduced the ALCI\_RCC family in his doctoral work at the University of Hamburg under the DFG project "Description Logics and Spatial Reasoning" (grant NE 279/8-1).

The revised version of the paper addresses issues identified in a technical review. We are grateful for the detailed and constructive feedback.
