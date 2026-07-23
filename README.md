# ALCI_RCC5 Decidability — an AI-assisted attack on a 20-year-old open problem

Is concept satisfiability in **ALCI_RCC5** (the description logic *ALCI* with
the RCC5 spatial relations as roles, under abstract composition-table
semantics) decidable? The question has been open since Wessel's 2002/2003
work ([report7.pdf](papers/report7.pdf); the family is defined and the open
problem stated there, alongside the earlier
[report4](papers/report4.pdf)–[report6](papers/report6.pdf)). This
repository documents a sustained, adversarially-reviewed, partly
machine-checked attack on it, conducted by AI assistants under human
direction.

<p align="center">
  <img src="papers/report7_figure10_grid.png" width="760" alt="An RCC8 network isomorphic to a 3x3 grid (Wessel 2002/2003, report7 Figure 10)">
</p>

<p align="center"><em>Wessel's 2002/2003 construction of an RCC8 network isomorphic to an n×n grid (<a href="papers/report7.pdf">report7</a>, Fig. 10) — found by a Lisp enumerator program and rendered with CLIM (MCL), not drawn by hand. Such grid models <strong>exist</strong> — yet no concept term can <strong>force</strong> one. That gap (the "coincidence obstruction") is exactly why the problem has resisted both a decidability and an undecidability proof for two decades.</em></p>

> **Disclaimer.** The papers and code here were produced by AI assistants
> (Claude / Anthropic and GPT-5.4 / GPT-5.5 / OpenAI), prompted and directed
> by Michael Wessel. They have **not** been peer-reviewed or verified by
> human domain experts, and are offered as a **discussion piece**. Standing
> label: **strongly supported, not certified** (with three machine-certified
> exceptions, below).

## Read this first: the paper

**Everything of substance is in the overview paper** —
[**PDF**](papers/overview_arxiv.pdf) · [source](papers/overview_arxiv.tex).
It is self-contained: the history (Cohn 1993, Wessel 2002/2003, Lutz &
Wolter 2006), why every known undecidability reduction fails, why concrete
domains do not settle it, the approaches tried route by route, the
machine-checked reduction to a single keystone, the decidable fragment, the
reasoners, and an honest account of the AI-assisted methodology.

**Prefer slides?** A talk version of the same material is in
[**`papers/talk_ALCIRCC5.pdf`**](papers/talk_ALCIRCC5.pdf) ·
[source](papers/talk_ALCIRCC5.tex) — a ~40-minute deck covering the problem,
why it is hard (the two axes and the coincidence obstruction), the routes
tried, what is certified, the $\Pi^0_1$ observation, the reasoner, and the
lessons on working with frontier AI.

**Want the positive result explained?** The project's strongest
unconditional theorem — decidability of the **∀PO-free fragment** — has a
dedicated explainer:
[**`papers/why_po_free_decidable.pdf`**](papers/why_po_free_decidable.pdf) ·
[TeX](papers/why_po_free_decidable.tex) ·
[Markdown](papers/WHY_PO_FREE_IS_DECIDABLE.md). It is the technical sibling
of the non-technical
[`WHY_ITS_HARD.md`](papers/cold_review_f6_w2prime/WHY_ITS_HARD.md): written
for a reader who knows description logics, tableaux, and blocking (but not
automata or model theory), it explains the finite-certificate architecture,
the handful of composition-table facts everything rides on (four
deterministic cells; PO forced by nothing yet available wherever anything
is), and **both independent proof routes** — the two-tier quotient
(chain-and-phase) and the ordered-disjoint normal form (structural) —
at "yes, I believe that" depth rather than full-proof depth, with an
honest per-claim status table (what is Lean-certified vs. machine-checked
vs. theorem-level).

The rest of this README is just a map. To avoid duplicated, drifting prose,
the detailed narrative lives in **one** place — the paper — with the full
dated audit trail in [CONVERSATION.md](CONVERSATION.md), the Lean history in
[LEAN.md](LEAN.md), and the superseded threads in [OUTDATED.md](OUTDATED.md).

## Status (2026-07-18): a local optimum, paused here

Decidability of ALCI_RCC5 (and ALCI_RCC8) **remains open**. After ~30 repair
rounds and 17 adversarial reviews the project has reached a genuine local
optimum: the local algebra is exhausted, the soundness side is
machine-checked, and the entire remaining difficulty *of the present
certificate architecture* compresses into one well-posed lemma. Work is **paused** at this state (git tag
`arxiv-candidate-2026-07-18`); what a future attack needs is recorded in the
paper's concluding section and in
[`papers/cold_review_f6_w2prime/`](papers/cold_review_f6_w2prime/).

> **16th review (2026-07-18):** a cold review of the overview paper
> ([`papers/final_gpt_review_overview_paper/`](papers/final_gpt_review_overview_paper/))
> found a **definite error** — a broken one-point-extension example, rooted
> in an overstated "PO is never forced" intuition (in truth, no *single*
> composition step forces PO, but the *intersection* of several can). The
> certified Lean core was unaffected. The error and the overstatements have
> been corrected, and many claims qualified (Π⁰₁ = membership not hardness;
> "prototype reasoner" not "decision procedure"; forward-direction-certified
> normal form). The reviewer's larger call — full self-contained proofs and a
> narrower theorem paper — is the standing open work, exactly what the
> "not certified" label denotes.

> **17th review (2026-07-20):** a **cold, scope-aware** review of the
> overview paper by GPT-5.6 Pro
> ([`papers/really_final_gpt_5.6_review/`](papers/really_final_gpt_5.6_review/)),
> told explicitly that this is an *overview*. Verdict: **accept as an
> overview after a focused calibration pass**, and a companion
> recommendation to **post to arXiv** as a status report and research
> handoff (not a claimed solution). It found **no new counterexample** to
> the normal form, the conditional soundness theorem, or the ∀PO-free
> result. The calibration fixes — all now applied — separate static F6
> (which controls *this* certificate route) from an undecidability theorem
> and from decidability by *some* other presentation; sync the normal-form
> status to **both directions**; add GPT-5.6 Pro to the attribution; keep
> "prototype reasoner" (not "decision procedure"); add a four-level status
> table and a result-to-artifact map; and drop "new" from the title
> (novelty vs. the prior literature is unvetted). The certified Lean core
> was unaffected (prose/calibration only). Paper now 42pp.

- **Certified** (Lean 4, zero `sorry`; see [LEAN.md](LEAN.md)): the
  **soundness** pipeline (a valid finite certificate unfolds to a genuine
  RCC5 model); the **faithfulness** of the Hintikka abstraction; the
  **RCC5 normal form** — now **both directions** on arbitrary domains
  (forward: every strong-EQ RCC5 network is an ordered-disjoint structure,
  `propext` only; converse: GPT-5.6 Pro's canonical set representation,
  `sub_iff_le`/`eta_injective` zero-axiom, verified in
  [`wp88`](verification/python/wp88_canonical_representation.py)).
- **The positive result** is a *conditional* decidability theorem: **if** the
  *live* (non-shadow) width of models is bounded by a computable function of
  the concept — property **F6** — **then** satisfiability is decidable, and
  the soundness half of that reduction is machine-checked.
- **Open (the keystone):** F6 itself — equivalently, that every satisfiable
  concept admits a *bounded* finite certificate. This is the standing open
  mathematics.
- **The problem is Π⁰₁ (a later observation).** Satisfiability is finitely
  first-order axiomatizable, so by Gödel completeness its complement is
  recursively enumerable and SAT sits at **Π⁰₁** — the domino problem's own
  level. Decidability therefore needs only *qualitative* F6 (every satisfiable
  concept has *some* finite certificate — **no computable bound**): dovetail a
  certificate enumeration against an FO-refutation enumeration. The reduction
  is machine-checked ([`formal/SemiDecidability.lean`](formal/SemiDecidability.lean)),
  and the bound returns for free a posteriori. This *reshapes* the keystone —
  retiring the width-accounting burden — but does **not** settle it: qualitative
  F6 is untouched.
- **The knife's edge:** F6 is the *same* looseness that blocks a proof of
  *undecidability*. Bound it ⇒ decidability; circumvent it to force a grid ⇒
  undecidability. Two sides of one question — why neither has moved in 20+
  years.
- **Unconditional win:** the **∀PO-free fragment** is decidable (a genuinely
  expressive spatial fragment — it keeps ∃PO, ∀DR, ∃DR, and all part-of
  modalities), via the two-tier quotient route (not the split-forest models).
  Re-examined after the 16th review and strengthened: its **soundness core is
  now machine-certified** ([`formal/POFreeLift.lean`](formal/POFreeLift.lean)
  — the chain-unfolding lift; the unfolding is a genuine RCC5 frame), and two
  independent decision procedures agree on it with **zero mismatches**
  ([`wp86`](verification/python/wp86_two_tier_lift_check.py),
  [`wp87`](verification/python/wp87_po_free_end_to_end.py)). The reviewer's
  "PO is never forced" concern is closed: the construction enforces full
  composition-consistency, which subsumes multi-path PO forcing. (Full
  end-to-end certification — the model-of-C₀ layer and the completeness
  extraction — remains open.)

## Complexity landscape

RCC*k* relation sets coarsen as *k* decreases; RCC1–3 are decidable
(Wessel), RCC5/RCC8 are the open cases. (Full detail: Table 1 of the paper.)

| Logic | Base relations | Concept satisfiability |
|---|---|---|
| ALCI (no RCC) | arbitrary roles | ExpTime-complete (known) |
| ALCI_RCC1 | {SR} | decidable; NP-complete (≡ S5) |
| ALCI_RCC2 | {DR, O} | decidable; NP-hard, in PSpace |
| ALCI_RCC3 | {DR, ONE, EQ} | decidable; NP-hard |
| ALCI_RCC5, ∀PO-free | RCC5 without ∀PO | **decidable** (this project) |
| ALCI_RCC5 (full) | {DR, PO, EQ, PP, PPI} | **open**; PSpace-hard |
| ALCI_RCC8 | eight RCC8 relations | **open**; ExpTime-hard |

Both directions rely on the **patchwork property** of RCC5/RCC8 (Renz &
Nebel 1999): path-consistent atomic networks are globally consistent.

## The reasoner, and a GIS example spanning 23 years

Alongside the theory, the project ships a working **cover-tree tableau
reasoner** ([`src/cover_tree_tableau.py`](src/cover_tree_tableau.py)) —
cross-validated on 911 concepts against an independent oracle with **zero
mismatches**, and never once contradicted anywhere in the campaign. Its most
satisfying test spans 23 years: it recomputes, in 2026, the exact GIS
concept taxonomy that a **prototype reasoner** computed in Wessel's 2003
report (report7, §4.3.1: "actually computed by a working prototype system")
— all **21/21** subsumptions, multiple inheritance and all. Two reasoners,
23 years apart, agreeing edge for edge.

The 2003 original ([report7](papers/report7.pdf), Figure 6):

<p align="center">
  <img src="papers/report7_figure6_taxonomy.png" width="600" alt="GIS taxonomy, 2003 original (report7 Figure 6)">
</p>

The same taxonomy recomputed in 2026 by the reasoner (green = individuals;
note that *Hamburg* and *Alster* each have **two** parents — the taxonomy is
a DAG, not a tree, which is exactly the multiple-inheritance the reasoner has
to get right):

<p align="center">
  <img src="papers/gis_taxonomy_reasoner_2026.png" width="760" alt="GIS taxonomy recomputed by the cover-tree tableau reasoner, 2026">
</p>

## Approaches, by technique

The routes tried are organized under [`approaches/`](approaches/), each with
a short hub (`Overview.md`) linking to that route's manuscripts, probes, and
the relevant section of the paper (no files are moved — the hubs link to
canonical locations):

- [`Tableaux/`](approaches/Tableaux/Overview.md) — naive tableau + blocking; the cover-tree tableau.
- [`FiniteModel_TwoTier/`](approaches/FiniteModel_TwoTier/Overview.md) — finite-model attempts; the two-tier quotient; the **∀PO-free decidable fragment**.
- [`SplitForest/`](approaches/SplitForest/Overview.md) — the split-forest normal form (the sound semantic foundation).
- [`NoAutomataCertificate/`](approaches/NoAutomataCertificate/Overview.md) — the rounds-2–10 hand certificate.
- [`Automata_Parity/`](approaches/Automata_Parity/Overview.md) — the two-way parity tree-automaton route.
- [`Lean_F6/`](approaches/Lean_F6/Overview.md) — the Lean formalization and the reduction to F6.
- [`RegularCovers/`](approaches/RegularCovers/Overview.md) — the regular-cover pivot and the certified RCC5 normal form.

## Build & run

Compile the paper (three passes resolve refs; the bibliography is inline):

```
cd papers
pdflatex overview_arxiv.tex && pdflatex overview_arxiv.tex && pdflatex overview_arxiv.tex
```

Run the reasoners (Python 3, no dependencies):

```
cd src
python3 cover_tree_tableau.py        # cover-tree tableau (built-in tests)
python3 stress_test_cover_tree.py    # cross-validation vs the quasimodel oracle (911 concepts)
python3 gis_taxonomy.py              # reproduces the 2003 GIS taxonomy (21/21)
```

Check the Lean development (Lean 4.32.0 via `elan`; no mathlib):

```
cd formal && lean Round19Transport.lean   # see LEAN.md for all artifacts
```

The self-contained verification probes are in
[`verification/python/`](verification/python/) (WP1–WP88; the latest —
wp84 Π⁰₁ transcription, wp85 multi-path forcing, wp86 two-tier lift,
wp87 ∀PO-free end-to-end cross-check).

## Repository map

- [`papers/`](papers/) — LaTeX sources and PDFs. **`overview_arxiv.*` is the
  primary deliverable**; other papers are per-approach manuscripts (linked
  from the hubs).
- [`src/`](src/) — the reasoners (cover-tree tableau, quasimodel oracle,
  model verifier).
- [`formal/`](formal/) — the Lean 4 development (`Round19Transport.lean`,
  `RCC5NormalForm.lean`, `ForcingReduction.lean`); history in
  [LEAN.md](LEAN.md).
- [`verification/python/`](verification/python/) — the WP probe ledger.
- [`approaches/`](approaches/) — per-technique hubs.
- [CONVERSATION.md](CONVERSATION.md) — the full, dated audit trail (who
  contributed what). [OUTDATED.md](OUTDATED.md) — superseded manuscripts and
  the historical no-automata thread.

## Author

Michael Wessel (miacwess@gmail.com), who introduced the ALCI_RCC family in
his doctoral work at the University of Hamburg (DFG project "Description
Logics and Spatial Reasoning", grant NE 279/8-1). The mathematical
development was carried out by the AI assistants named above under his
direction; the division of labour is auditable in
[CONVERSATION.md](CONVERSATION.md).
