# Added probes

All scripts use only the Python standard library.

- `target_d1_multigroup_cycle.py`: exact 14-point principal-ideal set model
  with two locally safe fallback groups and a global alternating cycle.
- `target_d2_mixed_counterexample.py`: compact genuinely mixed D2
  counterexample and fixed-point gate run.
- `target_d2_exhaustive_countermodel.py`: bounded exhaustive core search,
  formula-realized model, and nonempty-lower-spectrum strengthening.
- `target_e_anchor_compatibility.py`: symmetric two-component kernel-anchor
  clash for the current borrowing policy.
- `target_e_finite_key_anchor_counterexample.py`: symbolic `A_n/B_m`
  source-anchor calculation separating finite keys from anchor completion.
- `wp131_refined_key_audit.py`: corrected wp131 sweep using the refined key,
  a role-sensitive child cache, and group-level fallback counting.
- `probe_audit_r2.py`: reproduces the omitted wp131 predicates, imports the
  corrected sweep above, checks the D2 witness defect, tests wp132's
  `fresh_sat` abstraction and route split, and confirms that the supplied
  wrapper masks nonzero exits.

Run the package-level `run_new_probes.sh`. It executes every exact
countermodel and then the combined audit; the combined audit imports and runs
`wp131_refined_key_audit.py`.

