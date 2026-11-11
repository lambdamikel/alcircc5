# Errata

Corrections to statements this repository has published. Newest first.

History is not rewritten: `CONVERSATION.md`, the dated status paragraphs of
`CLAUDE.md`, archived reviews and frozen submissions keep their text and are
corrected by later entries. Live documents (the README, the two papers, the
slides, the explainers, the approach pages) are corrected in place.

---

## 2026-11-11

Found in one outside session (Claude Fable 5.2, at Michael Wessel's request).
Details and machine checks: [`papers/poset_bridge/`](papers/poset_bridge/README.md).
**No Lean-certified result is affected by either item.**

### E1. "Two-variable logic with one transitive relation is decidable" — a withdrawn theorem, cited as standing

**What we said.** That FO² with one transitive relation is decidable
(Szwast & Tendera, STACS 2013), so that a two-copy encoding of the full logic
"lands near a decidable logic".

**What is true.** The authors withdrew the 2013 claim in 2018
(arXiv:1804.09447). Decided are only the fragment whose existential quantifiers
are guarded by the transitive relation (2-NExpTime) and *finite* satisfiability
(Pratt-Hartmann, Math. Log. Quart. 2018). General satisfiability is open, also
for a single partial order, where it is conjectured decidable (Marzec & Tendera,
J. Logic Comput. 2026).

**Where it stood.**

| place | state |
|---|---|
| `papers/overview_arxiv.tex`, conclusion | corrected |
| `papers/pofree_fragment_arxiv.tex`, related work and discussion | corrected |
| `CONVERSATION.md`, closing entry of 2026-09-14 | history; corrected by the 2026-11-11 entry |
| `papers/gpt-5.6-latest-overview-paper-review-and-recommendation/` (where the sentence came from) | archived unmodified; erratum in that folder's README |
| the PDFs inside tag `release-2026-09-14` | **not corrected** — the tag predates this |

**What it changes.** No theorem used it. It was offered as a lead for future
work, and as a lead it is withdrawn. The actual relationship runs the other
way: a syntactic fragment of ALCI_RCC5 *is* two-variable logic over strict
partial orders with unary predicates (`poset_bridge`, `patsys_to_rcc5` in
`formal/PosetBridge.lean`), so the full logic contains the unary case of that
open problem.

### E2. "No verdict of the cover-tree tableau has ever been shown wrong" — false; the tableau is incomplete

**What we said.** That no verdict of `src/cover_tree_tableau.py` had been shown
wrong; and, in the tableau paper, that its "key insight" justifies checking only
`DR`/`PO` between two horizontal witnesses of one node.

**What is true.** The concept

```
K2 = ∃PO.(A ⊓ ∀PO.¬B ⊓ ∀DR.¬B) ⊓ ∃PO.(B ⊓ ¬A)
```

is satisfiable (`r = {1,3}`, `a = {1,4}`, `b = {1,4,5}`; `k2_sat`, Lean-checked)
and the tableau answers **UNSAT**. Two `DR`/`PO` witnesses of one node need not
be siblings of each other; they can be nested, and `K2` forces that. The
tableau is **incomplete**. No wrong SAT answer is known.

**Where it stood.**

| place | state |
|---|---|
| `README.md` (status entry of 2026-09-14; reasoner section) | corrected / marked superseded |
| `papers/overview_arxiv.tex` (five places) | corrected |
| `papers/talk_ALCIRCC5.tex` (one slide) | corrected |
| `papers/cover_tree_tableau_ALCIRCC5.tex` (abstract's "key insight"; the sibling check) | erratum box on page 1 and a note at the step |
| `papers/why_po_free_decidable.tex` ("two independent decision procedures") | corrected to "reasoners" |
| `approaches/Tableaux/Overview.md` | corrected |
| `src/cover_tree_tableau.py` | **not fixed**; the defect is documented in its header |
| `CLAUDE.md`, status paragraph of 2026-09-14 | history; superseded by the 2026-11-11 paragraph |
| the PDFs inside tag `release-2026-09-14` | **not corrected** — the tag predates this |

**What it changes.**

* The wrong direction is UNSAT. Subsumption is tested as unsatisfiability, so a
  subsumption verdict of the tableau is evidence only where something
  independent agrees with it.
* Wherever the tableau served as the reference verdict in a probe, agreement on
  UNSAT cases weighs less than it was taken to.
* These statements remain true **as stated**: the 911-case suite has zero
  mismatches with the oracle (the suite does not contain the pattern); the
  tableau reproduces the 2003 GIS taxonomy edge for edge; `wp87`'s 244
  ∀PO-free concepts show zero mismatches. The last is also unaffected in
  substance: this failure needs a `∀PO` between the two witnesses, and without
  one `PO` is always admissible between them.
* Admitting `PP`/`PPI` in the pairwise check would not repair the tableau:
  three witnesses can be forced into a cycle `a ⊂ b ⊂ c ⊂ a` that no pairwise
  test sees (`ccyc_unsat` is the vertical version).

### Checked and found not to need correction

* **The certified results.** The ∀PO-free fragment, the PO-erasure fragment 𝒟,
  the RCC5 normal form, the set-semantics equivalence, the soundness pipeline
  and the conditional reduction are Lean theorems. `formal/PosetBridge.lean`
  imports the certified artifact and builds against it.
* **F6 and the conditional reduction for the full logic.** Untouched. Not
  tested: whether the certificate format of `formal/Round19Transport.lean`
  admits a certificate for the new infinity axiom (`spiralConcept`), whose
  models are infinite without any `∃PP`/`∃PPI`. That is a natural next test, and
  it is open.
* **The claims about infinity.** "No finite model property" is stated with a
  `PP`-tower as its example, never as the only source. The spiral is a second
  source; nothing published excluded it.
* **The design record's own retractions** (`ASSEMBLY_DESIGN.md` §67–§68, from the
  cold review of the mixed quadrant) were already made. One in-place marker was
  missing, at §51.1, and has been added.

### Not in the repository's hands

* Nothing here has been posted to arXiv, and the DL 2026 abstract was rejected;
  it is archived as submitted.
* Tag `release-2026-09-14` still points at the uncorrected papers. Moving it, or
  cutting a new tag, is Michael's decision.
