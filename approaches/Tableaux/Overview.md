# Approach: Tableaux and blocking

**Idea.** The default DL decision method — a tableau that builds a model and
*blocks* to terminate.

**Why it fails here.** ALCI_RCC5 models are complete graphs (no tree-model
property), so ordinary blocking is unsound. Every rung of the blocking
ladder we tried — subset / equality / pairwise / triangle-type, and
"anywhere" blocking with extra context (triangle types, etc.) — is either
unsound or incomplete for a total-relation logic. The operational
descendant that *does* work in practice is the **cover-tree tableau**
(PPI-oriented cover trees with {DR, PO}-only sibling cross-edges),
empirically validated — and, since 2026-11-11, **known to be incomplete**: it
answers UNSAT on the satisfiable concept
`K2 = ∃PO.(A ⊓ ∀PO.¬B ⊓ ∀DR.¬B) ⊓ ∃PO.(B ⊓ ¬A)`, whose two overlap-witnesses
must be nested. Treating two `DR`/`PO` witnesses of one node as siblings is the
step that loses models. No wrong SAT answer is known.

Full treatment: overview paper, §"Naive tableaux and blocking" and
§"Current implementation: reasoners".

**Manuscripts**
- [Cover-tree tableau paper](../../papers/cover_tree_tableau_ALCIRCC5.pdf)
- [GPT-5.4 cover-tree tableau (v1 theory)](../../papers/trees/alcircc5_cover_tree_tableau_needall_patched.pdf)

**Code**
- [`src/cover_tree_tableau.py`](../../src/cover_tree_tableau.py) — the reasoner
- [`src/stress_test_cover_tree.py`](../../src/stress_test_cover_tree.py) — 911-concept cross-validation

**Result.** The most promising *operational* procedure — cross-validated
with zero mismatches on its 911-case suite and reproducing the 2003 GIS
taxonomy — but **not complete** (`K2` above; Lean-checked satisfiable,
`formal/PosetBridge.lean`, and outside the suite) and with no elementary
complexity bound. Its UNSAT answers, and so its subsumption verdicts, are
therefore evidence only where something independent agrees. The strong-EQ
PO-loop, by contrast, is a blind spot of the quasimodel cross-check *oracle*,
which the tableau decides correctly; it is discussed in the paper.
