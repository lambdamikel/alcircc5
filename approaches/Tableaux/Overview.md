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
empirically validated but not proved complete.

Full treatment: overview paper, §"Naive tableaux and blocking" and
§"Current implementation: reasoners".

**Manuscripts**
- [Cover-tree tableau paper](../../papers/cover_tree_tableau_ALCIRCC5.pdf)
- [GPT-5.4 cover-tree tableau (v1 theory)](../../papers/trees/alcircc5_cover_tree_tableau_needall_patched.pdf)

**Code**
- [`src/cover_tree_tableau.py`](../../src/cover_tree_tableau.py) — the reasoner
- [`src/stress_test_cover_tree.py`](../../src/stress_test_cover_tree.py) — 911-concept cross-validation

**Result.** The most promising *operational* procedure — cross-validated
with zero mismatches and reproducing the 2003 GIS taxonomy — but with no
completeness proof and no elementary complexity bound. Its one known blind
spot (the strong-EQ PO-loop of the quasimodel cross-check oracle) is
discussed in the paper.
