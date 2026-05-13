# Verification of GPT-5.5's Repaired Split-Forest Decidability Proof

This directory contains computational cross-checks of the finite combinatorial content of GPT-5.5's [repaired split-forest decidability proof](../papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.pdf) (May 2026, 16 pages, no-automata route).

The work-package mapping follows GPT-5.5's [verification recommendations document](../papers/gpt5.5_round2/verification_recommendations_for_claude.pdf). Six work packages WP1–WP6 are scoped; WP4 (multiple-superpart $C_{AB}$ stress) and WP5 (request-closed blocking-cycle tests) are folded into WP2 and WP3 respectively, so four Python scripts cover all six work packages.

**Status: All four scripts PASS. No counterexample found.**

The Lean targets L1–L7 from GPT-5.5's verification recommendations are not yet attempted.

## Layout

- [`python/`](python/) — verification scripts (one per work package or work-package group)
- [`reports/`](reports/) — captured `stdout` from each script

## Scripts

### `python/rcc5_composition_check.py` — WP1: RCC5 composition table

Computes the RCC5 composition table by exhaustive enumeration over non-empty subsets of a finite universe $U$ with $|U| = 5$, and compares against:

1. GPT-5.5's claimed table (lines 99–114 of the repaired proof);
2. the COMP table in the in-repo quasimodel reasoner (`src/alcircc5_reasoner.py`).

Result: **all 25/25 cells match GPT-5.5's table exactly.** The reasoner's table differs only by the four documented EQ-omission cells `(DR, DR)`, `(PO, PO)`, `(PP, PPI)`, `(PPI, PP)` — a convention (the reasoner models edges between distinct nodes only), not a bug.

Stability of the enumeration across $|U| \in \{2, 3, 4, 5\}$ is also reported.

Run: `python3 python/rcc5_composition_check.py`
Report: [`reports/rcc5_composition_table.txt`](reports/rcc5_composition_table.txt)

### `python/certificate_checker.py` — WP2 + WP4 + WP5: certificate-soundness fuzzer (vertical fragment)

Checks validity conditions (V1), (V3), (V4), (V5), (V9), (V10) of Definition 4.5 of the repaired proof on a corpus of generated split-forest certificates. The fuzzer exercises the three load-bearing round-2 fixes:

- **G1 (occurrence-level equality).** Self-loop on $C_{\mathrm{up}} \equiv \exists \mathrm{PP}.\top \sqcap \forall \mathrm{PP}.\exists \mathrm{PP}.\top$ is **consistent under occurrence-level equality** $u \equiv_{EQ} v \Leftrightarrow \mathrm{orig}(u) = \mathrm{orig}(v)$, but contradictory under the old profile-port equality that the round-2 review refuted.
- **G3 (mates with different parents).** $C_{AB}$ (two equality-mates at the same rank-$d$ profile, with two distinct upward witnesses) is **accepted** when the two mate occurrences are allowed to have different parents, and rejected when forced into a single parent.
- **G4 (rootless orientation).** Parent self-loops are permitted; no ambient root is required.

Run: `python3 python/certificate_checker.py`
Report: [`reports/certificate_checker.txt`](reports/certificate_checker.txt)

### `python/small_model_oracle.py` — WP3: small-model SAT/UNSAT oracle

Brute-force enumeration of complete RCC5 Kripke labelings over domain sizes $n \in \{2, 3, 4\}$ satisfying:

- (J1) reflexivity: $\rho(x, x) = \mathrm{EQ}$
- (J2) inverse: $\rho(y, x) = \mathrm{INV}[\rho(x, y)]$
- (J3) triple composition: $\rho(x, z) \in \mathrm{comp}(\rho(x, y), \rho(y, z))$

For each labeling and each atomic assignment, the oracle checks concept satisfaction at the declared root. Cross-corroborates WP2:

- $C_{AB}$ is realised at $n = 3$ — consistent with WP2 accepting its certificate.
- Infinite-model-only concepts (e.g., $\exists \mathrm{PP}.\top \sqcap \forall \mathrm{PP}.\exists \mathrm{PP}.\top$) correctly report *no finite model up to $n = 4$* — consistent with SAT in an infinite frame and with WP2 accepting the certificate (a parent self-loop on the rank-$d$ quotient unfolds to fresh occurrences).
- Genuine UNSAT concepts (e.g., $\exists \mathrm{PP}.A \sqcap \forall \mathrm{PP}.\neg A$) yield *no model up to $n = 4$* **and** the WP2 fuzzer rejects the corresponding certificate.

Run: `python3 python/small_model_oracle.py`
Report: [`reports/small_model_oracle.txt`](reports/small_model_oracle.txt)

### `python/mosaic_closure_search.py` — WP6: mosaic closure / patchwork lemma counterexample search

Empirically verifies Lemma 4.6 of the repaired proof (patchwork, citing Renz & Nebel 1999): support-closed mosaics — closed under the local axioms (M1)–(M5) at every position and under the support-closure operations (SC1)–(SC4) at every context — yield globally consistent atomic RCC5 networks on triples.

No counterexample to the patchwork lemma was found on the tested mosaic families.

Run: `python3 python/mosaic_closure_search.py`
Report: [`reports/mosaic_closure_search.txt`](reports/mosaic_closure_search.txt)

## Reproducing the reports

```
cd verification/python
python3 rcc5_composition_check.py    > ../reports/rcc5_composition_table.txt
python3 certificate_checker.py       > ../reports/certificate_checker.txt
python3 small_model_oracle.py        > ../reports/small_model_oracle.txt
python3 mosaic_closure_search.py     > ../reports/mosaic_closure_search.txt
```

Each script exits with code `0` on PASS and `1` on any mismatch / counterexample. The four current reports all end with `VERDICT: PASS`.
