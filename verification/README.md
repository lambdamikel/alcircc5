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

### `python/certificate_checker.py` — WP2 + WP4 + WP5: certificate-soundness fuzzer

Checks validity conditions (V1), (V2), (V3), (V4), (V5), (V6), (V7), (V8) basic, (V9) Ea/Eb, (V10) of Definition 4.5 of the repaired proof on a corpus of 24 generated split-forest certificates (the full (V8) triple-support search and the patchwork closure of (V2)/(V6)/(V7) are stress-tested separately by WP6). The fuzzer exercises the three load-bearing round-2 fixes plus the two cheap-win cases and four occurrence-level distinction certs added after the GPT-5.5 verification.zip review (May 2026):

- **G1 (occurrence-level equality).** Self-loop on $C_{\mathrm{up}} \equiv \exists \mathrm{PP}.\top \sqcap \forall \mathrm{PP}.\exists \mathrm{PP}.\top$ is **consistent under occurrence-level equality** $u \equiv_{EQ} v \Leftrightarrow \mathrm{orig}(u) = \mathrm{orig}(v)$, but contradictory under the old profile-port equality that the round-2 review refuted. Occurrence-level distinction is exercised by four additional certs (two-state PP cycle with/without cross-cycle eq-ports; PP-chain sharing $\lambda$; eq across distinct $\lambda$).
- **G3 (mates with different parents).** $C_{AB}$ (two equality-mates at the same rank-$d$ profile, with two distinct upward witnesses) is **accepted** when the two mate occurrences are allowed to have different parents, and rejected when forced into a single parent. The strengthened variant $C_{AB}^{\mathrm{inc}}$ (cheap-win #1) confirms both verdicts on a concept with no DAG model.
- **G4 (rootless orientation).** Parent self-loops are permitted; no ambient root is required. The pure request-closure cheap-win #2 (self-loop carrying $\neg A \sqcap \exists \mathrm{PP}.A$, no $\forall \mathrm{PP}.\neg A$) is rejected by V4 alone (V1 stays clean).
- **DR/PO mosaic fragment (V2/V6/V7/V8 basic).** Six certs exercising DR/PO existential discharge by typed RCC5 networks, universal propagation through DR/PO edges, and M3 triple consistency.

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

Empirically verifies Lemma 4.6 of the repaired proof (patchwork, citing Renz & Nebel 1999): support-closed mosaics — closed under the local axioms (M1)–(M5) at every position and under the support-closure operations (SC1)–(SC4) at every context — yield globally consistent atomic RCC5 networks. Seven tests: (A) triangle (M3)-partition (41/64 consistent, 23/64 rejected, all 41 realizable for $n \le 5$); (B) Renz–Nebel realizability of every (M3)-consistent triangle; (C) DR/PO side-witness insertion respecting (M4); (D) universal propagation through PP-chains; (E) sibling branching $L(c, s_2)$ matching $\mathrm{comp}(\mathrm{PP}, \mathrm{PO})$ exactly; (F) atomic arity-4 enumeration — 916/4096 (M3)-consistent 4-networks, of which 7 require $n \ge 6$ (pattern: three pairwise-DR positions all PO a fourth), all 916 realize at $n \le 6$; (G) overlap amalgamation of two arity-3 mosaics sharing an edge — 427/427 overlap-compatible pairs amalgamate.

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
