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
| `papers/talk_ALCIRCC5.tex`, the first-order-fragments slide ("FO² + 1 transitive rel.: decidable") | corrected in the re-sync of the same day; the first pass had missed it |
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
tableau is **incomplete**. No wrong SAT answer is known for the code as
repaired on 18 April 2026 (see E3 for what was shown before that).

**Where it stood.**

| place | state |
|---|---|
| `README.md` (status entry of 2026-09-14; reasoner section) | corrected / marked superseded |
| `papers/overview_arxiv.tex` (five places) | corrected |
| `papers/talk_ALCIRCC5.tex` (one slide) | corrected |
| `papers/cover_tree_tableau_ALCIRCC5.tex` (abstract's "key insight"; the sibling check) | erratum box on page 1 and a note at the step |
| `papers/why_po_free_decidable.tex` ("two independent decision procedures") | corrected to "reasoners" |
| `approaches/Tableaux/Overview.md` | corrected |
| `approaches/FiniteModel_TwoTier/Overview.md` and `papers/overview_arxiv.tex` §"finite models" ("two independent decision procedures"); the docstring of `wp87` | corrected in the re-sync of the same day; the first pass had missed them |
| `src/cover_tree_tableau.py` | **default not changed**; the defect is documented in its header. An experimental repair is behind `check_satisfiability(C, nested_witnesses=True)` (`wp138`) |
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
  test sees (`ccyc_unsat` is the vertical version). The experimental repair
  therefore checks the witnesses of each node jointly. It removes this wrong
  verdict and changes no verdict of the 35 built-in tests or the 911-case
  suite; that is evidence, not a proof. A terminating procedure that is sound
  and complete for the full logic would decide the open problem of E1, so no
  patch makes the tableau a decision procedure.

### E3. "Until November 2026 no verdict of the tableau had been shown wrong" — false; wrong SAT answers were shown in April 2026

*Found the same day, while the documents were being re-read after E2. It
corrects E2's own correction.*

**What we said.** From 2026-09-14: that no verdict the cover-tree tableau has
returned, "before or after the fix", has ever been shown wrong, and that its
April gap was latent, found by code review, and "changed no verdict". On
2026-11-11, in correcting E2: that "until November 2026 no verdict of the
tableau had been shown wrong", and that its SAT answers "remain unrefuted".

**What is true.** There were two events in April 2026, and those sentences
describe only the first.

* **11 April.** The cross-interaction check was generalized from singleton
  compositions to all compositions. It changed none of the 911 verdicts. This
  is the "latent gap".
* **18 April.** A review by Claude Opus 4.7
  ([`review_paper/`](review_paper/review_cover_tree_tableau.pdf)) showed that
  the tableau as then committed answered **SAT on twelve unsatisfiable
  concepts**: `∃R₁.∃R₂.A ⊓ ⨅ { ∀R.¬A : R ∈ comp(R₁,R₂) }` for every pair with
  `R₂ ≠ inv(R₁)`, the simplest being `∃PP.∃PP.A ⊓ ∀PP.¬A`. It was repaired the
  same day (the role-path check CT5), the reviewer attacked the repair and
  withdrew the claim for the repaired code. The 911-case suite showed zero
  mismatches before and after.

So the tableau has been shown wrong in **both** directions: wrong SAT answers in
April (repaired), a wrong UNSAT answer in November (`K2`; not repaired by
default). The accurate sentence is: *since the repair of 18 April 2026 no wrong
SAT answer is known.*

The April review was recorded when it happened — in `CONVERSATION.md`
(18 April), in `OUTDATED.md`, and in the tableau paper itself (§3.6). The
September sentence was written from the 11 April entry alone, and the November
correction repeated it.

**Where it stood.**

| place | state |
|---|---|
| `papers/overview_arxiv.tex` (§ reasoners; status section; conclusion; the record of errors in § agentic) | corrected |
| `papers/talk_ALCIRCC5.tex` ("fixed without changing a verdict") | corrected |
| `papers/why_po_free_decidable.tex` (the cross-validation paragraph) | corrected |
| `README.md` (reasoner section; status entry of 2026-11-11) | corrected |
| `ERRATA.md`, E2 ("No wrong SAT answer is known") | qualified in place |
| `papers/cover_tree_tableau_ALCIRCC5.tex`, erratum box | qualified |
| `approaches/Tableaux/Overview.md`; `papers/poset_bridge/README.md` §6 | corrected |
| `README.md` (status entry of 2026-09-14); `CLAUDE.md` (paragraph of 2026-09-14); `CONVERSATION.md` | history; superseded by this entry |
| the PDFs inside tag `release-2026-09-14` | **not corrected** — the tag predates this |

**What it changes.** No theorem. It changes how much the tableau's agreement
with anything is worth: twice now a suite with zero mismatches has missed a
defect of the tableau, once an unsoundness and once an incompleteness. For a
verdict that has to be trusted, use the reference reasoner
(`src/midelora_tableau.py`), whose SAT answers come with a checkable model and
whose UNSAT answers rest on a completeness proof — a paper proof, unreviewed.

### E4. "The known infinity axioms all ask for a proper part or a proper superpart" — false since 2003

*Pointed out by Michael Wessel on the evening of the same day, on reading the
re-synced documents.*

**What we said.** In the note on the poset bridge, and from there in the
overview, the slides, the explainer, `WHY_ITS_HARD.md`, the README and the open
letter: that the spiral is the first infinity axiom for this logic that asks
for no proper part and no proper superpart, or that the possibility was new in
November 2026.

**What is true.** Wessel's 2003 report (report7, §5.2 and Figure 12) gives

```
∃DR.⊤ ⊓ ∀DR.( ∃PO.∃DR.C ⊓ ∀PO.¬C ⊓ ∀DR.¬C )
```

which mentions neither `PP` nor `PPI`, in existentials or universals, and has
only infinite models; the report says so in as many words, against its own
earlier conjecture. The mechanism is the one the spiral uses: where
composition leaves a choice, here `comp(PO,DR) = {DR,PO,PPI}`, universals
exclude all but the nested option, and `comp(DR,PPI) = {DR}` makes the pattern
repeat. The reference reasoner finds no model of this concept on up to seven
nodes.

What is new about the spiral is narrower: it lies inside the fragment L∥, so it
never separates `PO` from `DR` and does not use the downward closure of `DR`;
the direction of the nesting it forces is not fixed by the table; and its
infiniteness is checked in Lean.

**Where it stood.**

| place | state |
|---|---|
| `papers/overview_arxiv.tex` (§7.8 and four other places) | corrected; the 2003 concept is now stated and credited, and the spiral has a figure |
| `papers/pofree_fragment_arxiv.tex` §7.5; `papers/talk_ALCIRCC5.tex` (the November slide); `papers/why_po_free_decidable.tex` | corrected |
| `WHY_ITS_HARD.md`, `README.md` | corrected |
| `outreach/open_letter_two_variable_logic_2026-11-11.md` ("Until now every infinity axiom I knew …") | corrected |
| `papers/poset_bridge/README.md` §5 | marked in place |

**What it changes.** No theorem. It removes a novelty claim, and it is the
second time in one day that a statement about this project's own record was
written without reading the record: the report is in the repository.

**A credit corrected at the same time.** The documents credited the spiral to
Marzec & Tendera alone. The five-predicate infinity axiom at its core is
already in Szwast & Tendera (J. Log. Comput. 2019, Section 5, Corollary 5.2);
Marzec & Tendera name it and build on it. Neither the spiral nor that axiom is
a concept of this project: the project's own contribution is the reading in
RCC5 and the Lean proof.

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
  `PP`-tower as its example, never as the only source. *(This entry called the
  spiral "a second source". The 2003 report already had one without `PP` or
  `PPI`; see E4.)*
* **The design record's own retractions** (`ASSEMBLY_DESIGN.md` §67–§68, from the
  cold review of the mixed quadrant) were already made. One in-place marker was
  missing, at §51.1, and has been added.

### Not in the repository's hands

* Nothing here has been posted to arXiv, and the DL 2026 abstract was rejected;
  it is archived as submitted.
* Tag `release-2026-09-14` still points at the uncorrected papers, and is left
  there. The corrected documents carry the new tag `release-2026-11-11`
  (Michael's decision, 2026-11-11).
