# Review paper — test harness

Adversarial test scripts accompanying the Opus 4.7 independent review
of the cover-tree tableau (`../review_cover_tree_tableau.pdf`).

All scripts import the reasoners from `../../src/` directly. Run them
from this directory or any directory — they adjust `sys.path`
internally.

## Round-1 regression: the twelve counterexamples

`verify_twelve_counterexamples.py` — runs the 4×4 grid of concepts
\(
  \exists R_1.\exists R_2.A \sqcap \bigsqcap_{R \in \mathrm{comp}(R_1, R_2)} \forall R.\lnot A
  \qquad (R_2 \neq R_1^{-1})
\)
and verifies that the cover-tree tableau agrees with the cycle-aware
quasimodel reasoner (QMc) on all 12 cells (all UNSAT in the
post-fix repository). Usage:

```
python3 verify_twelve_counterexamples.py
```

## Round-2 targeted attacks

`round2_targeted_and_random.py` — 9 targeted attack families (G/H/I/J
plus a quick random probe) designed to stress the new
`check_role_path_compatibility` (CT5) and the tightened
`compute_safe`.

`round2_sibling_stress.py` — simpler sibling-universal and
non-singleton-composition attacks (O/Q families) that complete
quickly.

`round2_per_test.py` — per-test driver with a command-line test index
(`python3 round2_per_test.py 0` for L1, etc.), useful when one
concept has a large closure.

## Random cross-validation

`round2_random.py` — pseudo-random ALCI\_RCC5 concept generator
cross-validating CT vs QMc with an optional per-test time budget:

```
python3 round2_random.py <seed> <n_tests> <max_per_test_seconds>
```

300 random tests across seeds 1 and 7 (depth 3–4, 2–3 atoms) reported
zero mismatches during review; see `../review_cover_tree_tableau.pdf`
§10 for details.

## Dependencies

Python 3.8+. No third-party packages. The scripts `import` the
repository's own `cover_tree_tableau` and `alcircc5_reasoner` modules,
so they must be run with the repository's `src/` on the Python path
(all scripts arrange this automatically).
