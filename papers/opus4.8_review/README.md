# review3 — Independent review of the round-8 saturated-side-context proof

This folder contains an independent review of GPT-5.5's **round-8** split-forest
decidability proof for `ALCI_RCC5`, the current canonical no-automata statement
per the project README/CLAUDE.md (entry dated 2026-05-28, evening):

- `alcircc5/papers/claude_latest_review_gpt5.5_fix/repaired_split_forest_abstract_round8_repaired.tex` (15-page sketch)
- `alcircc5/papers/claude_latest_review_gpt5.5_fix/expanded_split_forest_full_details_round8_full.tex` (30-page companion)

Round-8 was written to close three defects of round-7 that an earlier cold
review (see `review2/`) had identified. This review asks whether the
saturated-side-context repair actually closes the side/tree gap.

## Files

**The review (finds the defect):**
- `review_round8_split_forest.tex` / `.pdf` — the review (9 pages).
- `rcc5_compose.py` — RCC5 composition table (transcribed verbatim from the
  round-8 companion, Section 2.1) plus a forced-label-propagation check that
  grounds the central concern. Output: `compose_output.txt`.

**The repair (fixes the defect):**
- `repair_completeness_round8.tex` / `.pdf` — formal repair note (8 pages): a
  corrected completeness construction that closes D-1 via composition-forced
  verticalization (splice into `E_up`). States and proves the monotone-threshold
  lemma, the bounded-threshold lemma, acyclicity, inherited consistency, and
  descriptor finiteness; restores the completeness theorem; lists the remaining
  bookkeeping obligations O1–O4.
- `fix_feasibility.py` — machine-checks the linchpin (forced label is monotone
  `DR* PO* PPI*`, PPI absorbing, threshold bounded). Output: `fix_feasibility_output.txt`.
- `repaired_certificate.py` — builds the explicit *valid repaired certificate*
  for `C0'` (verifies RCC5 frame axioms, `Reach_PP` vertical tags, concept
  truth) and confirms the UNSAT sibling is still correctly rejected. Output:
  `repaired_certificate_output.txt`.

## Headline finding

**The round-8 repair does not close the side/tree gap; it relocates it.**

The saturated side context `S_k(u)` is finite (bounded by `m_*(C0)`), and the
"cross side/tree exhaustion" lemma verticalizes only pairs inside the
**depth-bounded boundary** `B_k(u)`. The genuinely hard case is a `DR/PO`
witness that RCC5 composition forces to be a proper part of an **infinite pumped
tower**.

Concrete satisfiable witness:

```
G   := (∀PO.X) ⊓ (∃PP.G)
C0' := (∃PP.G) ⊓ (∃PO.¬X)
```

`G` generates an infinite ascending PP-tower `a_1 PP a_2 PP …`, each with
`∀PO.X`. The root `u` has a PO-witness `w ∈ ¬X`. Because
`comp(PPI,PO) = {PO,PPI}` and `∀PO.X` at `a_1` kills the `PO` option, `w PP a_1`
is forced; `comp(PPI,PPI) = {PPI}` then forces `w PP a_m` for **all** `m`. The
side witness `w` is a proper part of every tower node.

Only finitely many tower nodes fit in `S_k(u)`. For the tail (`m > K`) the pair
`(a_m, w)` must carry the forced label `PPI`, but the constructed pair-shape
catalogue offers no admissible shape:

- `side_PPI` — needs co-residence in one finite side context (unavailable);
- `down` — needs an `E_up` cover path `w → … → a_m`, which the construction
  never creates for a side witness (unavailable);
- `front_DR` — `DR ∉ comp(PPI,·)`, rejected by (V8) composition;
- `front_PO` — rejected by (V12) `∀PO.X` universal safety since `w ∈ ¬X`.

So the certificate produced by the stated completeness construction is
**invalid** for a satisfiable concept ⇒ the completeness proof has a genuine
hole (severity: medium–high).

## The repair

`repair_completeness_round8.{tex,pdf}` supplies the fix. **Principle:** the
vertical backbone must present the *full* generated containment order, not just
the selected-witness edges. **Mechanism:** when composition forces a `DR/PO`
witness `w` to be a proper part of an ancestor, splice an `E_up` cover edge so
that `Reach_PP` carries the correct `PP/PPI` label to the entire (infinite)
tail.

Why it stays finite, and why it's clean:

- **Monotone threshold (Lemma 4.1, machine-checked):** climbing the tower, the
  forced label `ρ(a_m,w)` is non-increasing in `DR ≻ PO ≻ PPI` and PPI is
  absorbing — so it is `DR* PO* PPI*`, eventually constant.
- **Bounded threshold (Lemma 4.3):** each constant-label stretch is shortened to
  `≤ N` checkpoints by the existing replacement/blocking lemma, so the splice
  height is `≤ 3N` — finiteness preserved.
- **Consistency inherited (Lemma 5.2):** the construction *presents a fixed
  consistent model* `J`; the splice changes which device carries a pair's label,
  never the label. So RCC5 composition and universal safety are inherited from
  `J`, not re-derived. Acyclicity is free (`Reach_PP ⊆ <`, a strict partial
  order).

`repaired_certificate.py` builds the valid repaired certificate for `C0'`
explicitly and checks the UNSAT sibling is still rejected (the splice makes `w`
a PPI-successor, firing `∀PPI.Y` on it). Remaining bookkeeping obligations
(O1–O4) are listed honestly in §10 of the note — chief among them, confirming
the boundary descriptor licenses the excision in the presence of splices.

## Rebuild

```
cd review3
python3 rcc5_compose.py
python3 fix_feasibility.py
python3 repaired_certificate.py
pdflatex -interaction=nonstopmode review_round8_split_forest.tex
pdflatex -interaction=nonstopmode review_round8_split_forest.tex   # refs/TOC
pdflatex -interaction=nonstopmode repair_completeness_round8.tex
pdflatex -interaction=nonstopmode repair_completeness_round8.tex   # refs/TOC
```

## Disclaimer

Drafted by Claude (Anthropic, Opus 4.8), prompted by Michael Wessel. Not
independently verified by human experts. The reviewed manuscripts are
AI-drafted (GPT-5.5). The composition arithmetic is machine-checked; the
structural arguments are not formally verified.
