# Approach: Tableaux and blocking

**Idea.** The default DL decision method — a tableau that builds a model and
*blocks* to terminate.

**Why it fails here.** ALCI_RCC5 models are complete graphs (no tree-model
property), so ordinary blocking is unsound. Every rung of the blocking
ladder we tried — subset / equality / pairwise / triangle-type, and
"anywhere" blocking with extra context (triangle types, etc.) — is either
unsound or incomplete for a total-relation logic. The operational
descendant that runs and terminates is the **cover-tree tableau**
(PPI-oriented cover trees with {DR, PO}-only sibling cross-edges),
tested on a 911-case suite — and, since 2026-11-11, **known to be incomplete**: it
answers UNSAT on the satisfiable concept
`K2 = ∃PO.(A ⊓ ∀PO.¬B ⊓ ∀DR.¬B) ⊓ ∃PO.(B ⊓ ¬A)`, whose two overlap-witnesses
must be nested. Treating two `DR`/`PO` witnesses of one node as siblings is the
step that loses models. Since its repair of 18 April 2026 — before which a review had shown it accepting twelve unsatisfiable concepts (`ERRATA.md`, E3) — no wrong SAT answer is known. An experimental repair
(`nested_witnesses=True`, off by default; `wp138`) lets such witnesses be nested
and checks the witnesses of each node jointly.

Full treatment: overview paper, §"Naive tableaux and blocking" and
§"Current implementation: reasoners".

**A tableau that is sound and complete, and does not terminate (2026-11-11).**
Dropping termination, the default method does work: the complete-graph ABox
tableau of Wessel's MiDeLoRa — every two nodes related, the table checked on
every triangle, witnesses reusable, no blocking — is sound and complete under
strong EQ (a paper proof, unreviewed; the Python re-implementation is tested,
not verified; MiDeLoRa itself was read, not run:
[`papers/midelora_calculus/`](../../papers/midelora_calculus/README.md),
[`src/midelora_tableau.py`](../../src/midelora_tableau.py), `wp139`). By that
proof it answers on every unsatisfiable concept and on every concept with a
finite model, given enough time and memory. What
blocking would have to add is termination on the rest, and that is the open
problem.

**Manuscripts**
- [Cover-tree tableau paper](../../papers/cover_tree_tableau_ALCIRCC5.pdf)
- [GPT-5.4 cover-tree tableau (v1 theory)](../../papers/trees/alcircc5_cover_tree_tableau_needall_patched.pdf)
- [The MiDeLoRa calculus: sound, complete, not terminating (note)](../../papers/midelora_calculus/README.md)
- [The April 2026 review that found the tableau unsound, and its reassessment](../../review_paper/review_cover_tree_tableau.pdf)

**Code**
- [`src/cover_tree_tableau.py`](../../src/cover_tree_tableau.py) — the reasoner
- [`src/midelora_tableau.py`](../../src/midelora_tableau.py) — the reference reasoner (probes `wp138`, `wp139` in `verification/python/`)
- [`src/stress_test_cover_tree.py`](../../src/stress_test_cover_tree.py) — 911-concept cross-validation

**Result.** The most promising *operational* procedure — cross-validated
with zero mismatches on its 911-case suite and reproducing the 2003 GIS
taxonomy — but **not complete** (`K2` above; Lean-checked satisfiable,
`formal/PosetBridge.lean`, and outside the suite) and with no elementary
complexity bound. Its UNSAT answers, and so its subsumption verdicts, are
therefore evidence only where something independent agrees. The strong-EQ
PO-loop, by contrast, is a blind spot of the quasimodel cross-check *oracle*,
which the tableau decides correctly; it is discussed in the paper.
