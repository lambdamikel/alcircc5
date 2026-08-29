# Building and running

```sh
~/.elan/bin/lean POFreeLift.lean       # Lean 4.32.0 core, no mathlib
```

Measured on the authors' machine 2026-08-29: **exit 0, 1m14s, 0 errors,
0 warnings, 0 `sorry`**. The file ends in `#print axioms` on the capstones; all
of them report

```
[propext, Classical.choice, Quot.sound]
```

`Classical.choice` enters through `mty`/`dspec`/`modelSigs`, which are
`noncomputable` and used only inside proofs; the executable `Decidable` instance
does not depend on them at runtime. Verifying that separation is a fair target.

`RCC5NormalForm.lean` is a separate smaller file and builds independently.

To audit anything, append your own line:

```lean
#print axioms POFreeLift.modelSigs_survives
```

## Probes (Python 3, standard library only)

```sh
python3 wp135_cone_completeness_attack.py    # completeness side -- new, this round
python3 wp134_cone_scheme_prune.py           # soundness side -- shipped in round 1
```

Both re-derive the RCC5 composition table from finite set semantics. They are
independent re-implementations and could be wrong in the same direction as the
Lean; treat them as cross-checks, not as evidence about the Lean. **`wp135` is
the authors' own code and is itself in scope for this review** — if its
transcription of `compatB`/`sigOkB`/`dspec` does not match the Lean, its PASS
means nothing.
