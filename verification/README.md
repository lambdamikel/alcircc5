# Verification of GPT-5.5's Repaired Split-Forest Decidability Proof

This directory contains computational cross-checks of the finite combinatorial content of GPT-5.5's [repaired split-forest decidability proof](../papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.pdf) (May 2026, 16 pages, no-automata route).

The work-package mapping follows GPT-5.5's [verification recommendations document](../papers/gpt5.5_round2/verification_recommendations_for_claude.pdf). Six work packages WP1–WP6 are scoped; WP4 (multiple-superpart $C_{AB}$ stress) and WP5 (request-closed blocking-cycle tests) are folded into WP2 and WP3 respectively, so four Python scripts cover all six work packages.

**Status: All four scripts PASS. No counterexample found.** *(July 2026: three further scripts WP14–WP16 target the round-12 patchwork-bag proof — see below; all PASS, where WP15's PASS deliberately confirms a defect in round-12's Truth Lemma as written, plus its repair map.)*

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

### `python/wp14_patchwork_property_check.py` — WP14: the round-12 patchwork theorem (Thm 2.5 / App A), direct verification

Added by the **seventh review** (July 2026, Claude Fable 5), targeting the **round-12 patchwork-bag proof** (`papers/automata_route_repairs/split_forest_automata_with_appendices.tex`). For the abstract composition-table semantics, a finite complete atomic network is satisfiable iff it is composition-closed — the network *is* a frame — so round-12's central external dependency (its Theorem 2.5) is a purely combinatorial statement, verified here directly: T0 composition table re-derived from set semantics; T1 two-bag patchwork **exhaustive** at 1+1 fresh variables, shared parts of size 0–3 (21,538 agreeing pairs); T2 two-bag at 2+2 fresh variables (41,681 pairs); T3 **300 random tree-shaped bag families amalgamated leaf-by-leaf, literally executing App A's induction**; T4 EQ-forcing impossibility (every nontrivial composition cell containing EQ also contains PP, PPI, PO — backing App G's strong-equality claim). **All PASS, zero failures.** A failure here would have invalidated the proof (its own App U, failure point F1).

Run: `python3 python/wp14_patchwork_property_check.py`
Report: [`reports/wp14_patchwork_property_check.txt`](reports/wp14_patchwork_property_check.txt)

### `python/wp15_shadow_row_realizability.py` — WP15: the Shadow Amalgamation gap (7th review, finding F1), machine-checked

An **attack harness, not a proof check**: a passing run *confirms a defect* in round-12's Truth Lemma as written, together with its repair map. Models the shadow legality tests literally (per-bag one-point closure, boundary rigidity on continued ports, non-EQ entries) and shows the Truth Lemma's implicit assumption — *bag networks + all declared shadow rows are jointly realizable in one frame* — is **false**: P1, a minimal 3-bag configuration (declared entries `x1–x2: DR`, `x1–p: PP`, `x2–p: PPI`; `comp(PP,PP) = {PP}` forces `x1 PP x2`) passes every listed test with no realizing frame; P2, exhaustively 23/64 row assignments on the pattern fail. Repair map corroborated: P3 single-shadow always realizable (250/250 — provable: the bag+row family is an agreeing tree family, so Theorem 2.5 applies to it); P4 multi-shadow with DR/PO-only entries (the *vertical-liveness* discipline) 358/358 clean; P5 extended-bag discipline (shadow-shadow entries checked per bag) 200/200 clean.

Run: `python3 python/wp15_shadow_row_realizability.py`
Report: [`reports/wp15_shadow_row_realizability.txt`](reports/wp15_shadow_row_realizability.txt)

### `python/wp16_round12_bag_acceptance.py` — WP16: acceptance-level patchwork-bag mechanism check vs the cover-tree tableau

A finite-occurrence rendering of round-12's acceptance semantics (Hintikka types; declared witness edges with exact-occurrence-identity reuse; request-closed regularity for vertical eventualities; patchwork completion of undeclared pairs), run in two modes and cross-checked against `src/cover_tree_tableau.py`. **Repaired mode** (obligations enforced on actual completed relations; no EQ shadow entries; mandatory propagation): agrees with the tableau on all ten referee diagnostics — `C_force`, `C_split`, `C_2hop`, `C_3hop` UNSAT; `C_recursive`, `C_↑`, the round-10 dual-descendant tower, and the strong-EQ **PO-loop** SAT (the quasimodel oracle's blind spot, decided correctly here by design) — plus a 148-concept random sweep with **zero disagreements**. **Literal mode** (either of the 7th review's spec loopholes active: EQ-valued shadow entries, or droppable shadow scope): **wrongly accepts all four forced-composition UNSAT concepts**, machine-proving both loopholes are load-bearing. Bounded probe (occurrence budget; blocking requires request-closed laps — naive same-type blocking was observed to reproduce the round-6/7 lap-collapse false-SAT on `C_3hop`).

Run: `python3 python/wp16_round12_bag_acceptance.py`
Report: [`reports/wp16_round12_bag_acceptance.txt`](reports/wp16_round12_bag_acceptance.txt)

### `python/wp17_round13_discipline_check.py` — WP17: the round-13 Shadow Amalgamation repair, machine-checked

Companion to the **round-13 repair manuscript** ([`papers/fable5_round13/`](../papers/fable5_round13/)), which repairs the seventh review's critical finding F1 by the *D-discipline* (shadow entries restricted to {DR, PO}; vertical/EQ pairs co-bagged; mandatory propagation with verticalization fallback; type-propagation of transitive vertical universals; request-source liveness; pair coherence D5). Part A verifies the four finite composition facts the Shadow Amalgamation Lemma cites, exhaustively against an independently re-derived table (A1 horizontal absorption `{DR,PO} ⊆ Comp(a,b)`; A2 vertical transitivity; A3 no horizontal dead ends; A4 EQ never forced). Part B builds the lemma's constructive assignment (bag values + live rows + shadow rows + unique pair values + DR-default) on 400 random **tree-shaped** configurations under the discipline and asserts both B1 (every shadow-extended bag is a closed complete atomic network — the finite-facts step of the proof) and B2 (global joint realizability — what patchwork + compactness guarantee): **400/400 both**. Part C is the negative control: re-admitting vertical entries (violating D1) makes 151/300 configurations fail — the WP15 defect the discipline excludes. Historical note: an earlier draft of Part B failed B1 in 143/400 cases because the generator let two shadows co-locate without declaring their mutual value — exactly the omission that motivated the manuscript's pair-coherence rule (D5).

Run: `python3 python/wp17_round13_discipline_check.py`
Report: [`reports/wp17_round13_discipline_check.txt`](reports/wp17_round13_discipline_check.txt)


### `python/wp26_round15_cluster_quasimodels.py` — WP26: the round-15 cluster-quasimodel decision layer (no automaton)

Companion to [`papers/fable5_round15/`](../papers/fable5_round15/), the round-15 replacement for Theorem C after the ninth review (taking its R2 alternative: mosaic-style decision layer instead of a tree automaton). Part A establishes the **fold lattice** (new load-bearing finite fact): exactly **10** sets arise as compositions of atomic RCC5 words; every non-singleton fold contains a horizontal atom; the three DR-free folds all contain PO, so the canonical selector (forced value / DR / PO) is total — plus the steering toolkit (DR-column absorption, horizontal absorption, vertical transitivity, EQ-never-forced), all exhaustive against a set-semantics-derived table. Part B probes the **steering keystone (W1)**: 250 random realized cluster-tree frames, each glued with a fresh pattern, cross-pair domains = true separator-mediated feasible sets ∩ safety-like restrictions containing the canonical selector — **250/250 jointly realizable**; negative control (horizontals stripped): 245/249 fail (the F1.3/WP15 genus the certificate conditions exclude). Part C cross-validates the acceptance semantics (witness graphs with reuse, obligations on actual completed relations, request-closed repetition) against the cover-tree tableau on **all eleven diagnostics** — including the eighth review's `C_G2a` tower and the ninth review's p4 shared-unique-witness tower — **plus a 200-concept random sweep: zero disagreements, zero timeouts**.

Run: `python3 python/wp26_round15_cluster_quasimodels.py`
Report: [`reports/wp26_round15_cluster_quasimodels.txt`](reports/wp26_round15_cluster_quasimodels.txt)

**Post-10th-review update.** The tenth review exposed a spec-vs-test mismatch in Part B: it hard-wired the canonical selector into every positive domain, testing the *stronger* condition `sel(F) ∈ Safe` rather than the manuscript's (Q4)(b) disjunction. Part **B2** (added 2026-07-13) tests (Q4)(b) as written: the review's minimal W1a witness is confirmed (pairwise passes, joint completion impossible) and a randomized disjunction-branch sweep finds **95/250** glue steps jointly unrealizable — a passing B2 run *confirms defect #10*. The review's own witness script ships as [`python/wp27_round15_w1a_counterexample.py`](python/wp27_round15_w1a_counterexample.py) (reproduced byte-identical; report: [`reports/wp27_round15_w1a_counterexample.txt`](reports/wp27_round15_w1a_counterexample.txt)).

### `python/wp18…wp25` — the eighth review and the round-14 active-virtual-bag repair (GPT-5.5, July 2026; reproduced locally)

`wp18_g2a_verticalization_width_counter.py` and `wp19_g3_mixed_orientation_probe.py` are the **eighth review's** counterexample checks against round-13 (the `C_G2a` tower's unbounded root-bag width under literal D2; the mixed `PP/PPI` closed path whose vertical endpoint D3 never reaches). `wp21_twin_blowup_facts.py`, `wp22_g2a_profile_bound.py`, `wp23_active_closure_regressions.py`, `wp24_vertical_walk_facts.py`, and `wp25_active_virtual_bag_repair.py` check the **round-14** repair: same-profile copy chain/clique facts, G2a profile boundedness, no-DR-default and shadow-shadow-triangle regressions, uniform-vs-mixed vertical walk facts, and the main AV check (G2a absorbed at 2 live ports + virtual shadows; WP15/WP20-style triangles rejected by active closure; random active restrictions closed). All PASS; reports under [`reports/`](reports/).




## Reproducing the reports

```
cd verification/python
python3 rcc5_composition_check.py    > ../reports/rcc5_composition_table.txt
python3 certificate_checker.py       > ../reports/certificate_checker.txt
python3 small_model_oracle.py        > ../reports/small_model_oracle.txt
python3 mosaic_closure_search.py     > ../reports/mosaic_closure_search.txt
python3 wp14_patchwork_property_check.py > ../reports/wp14_patchwork_property_check.txt
python3 wp15_shadow_row_realizability.py > ../reports/wp15_shadow_row_realizability.txt
python3 -u wp16_round12_bag_acceptance.py > ../reports/wp16_round12_bag_acceptance.txt
python3 wp17_round13_discipline_check.py > ../reports/wp17_round13_discipline_check.txt
```

Each script exits with code `0` on PASS and `1` on any mismatch / counterexample. The four round-2-era reports all end with `VERDICT: PASS`; the four July-2026 reports (WP14–WP17) all end with their `OVERALL: PASS` lines (for WP15, PASS means *the defect and its repair map are confirmed* — it is an attack harness).
