# Building the artifact

```sh
~/.elan/bin/lean POFreeLift.lean          # Lean 4.32.0 core, no mathlib, ~4 min
```

Expect exit 0 and no errors or warnings. The file ends with `#print axioms` on
the capstone declarations; their output is the axiom footprint you should record
in the review.

`RCC5NormalForm.lean` is a separate, smaller file (the ordered-disjoint normal
form) and builds independently.

To audit anything else, append your own line, e.g.

```lean
#print axioms POFreeLift.unf_truth
```

`wp134_cone_scheme_prune.py` is a self-contained Python transcription of the
control layer that checks the elimination rejects the standard
forced-composition UNSAT concepts. It re-derives the RCC5 table from finite set
semantics. Treat it as a cross-check on the Lean, not as evidence about it —
it is a separate implementation and could be wrong in the same direction.
