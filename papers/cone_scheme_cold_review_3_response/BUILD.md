# Building and running

```sh
~/.elan/bin/lean POFreeLift.lean      # Lean 4.32.0 core, no mathlib
```

Measured 2026-08-29: **exit 0, ~40 s, 0 errors, 0 warnings, 0 `sorry`.** The file
ends in `#print axioms` on the capstones; all report
`[propext, Classical.choice, Quot.sound]`, except `cpo_unsat` (none) and
`erase_cpo_satisfiable` (`propext`).

`RCC5NormalForm.lean` builds independently. Note it is **imported nowhere** — it
is the raw material for a concrete-set semantics that has never been wired in.

Append your own audits:

```lean
#print axioms POFreeLift.unf_truth
#print axioms POFreeLift.coneScheme_sound
```

## Probes (Python 3, standard library only)

```sh
python3 wp133_cone_scheme_unfolding.py   # SOUNDNESS side -- most relevant here
python3 wp134_cone_scheme_prune.py       # the elimination
python3 wp135_cone_completeness_attack.py # completeness side (round 2)
```

**`wp133` does not come out clean, and that is deliberate information for you.**
It builds the fresh-occurrence unfolding directly and checks frame + truth
conditions. Frame violations: 0. Truth violations: **4 at depth 2, 5 at depth 3,
and we have not eliminated them.** Our reading is that they need the DR cone
condition, which lives in the control layer the probe does not model — i.e. that
they are artifacts of the probe rather than the architecture. That reading has
never been independently checked. **Checking it is one of the concrete tasks in
§3.** If instead they localise a real hole in `unf_truth`, that is the finding
this review exists to produce.

All probes re-derive the RCC5 composition table from finite set semantics. They
are our code and are in scope.
