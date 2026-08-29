# Audit summary

## Qualified verdict

The supplied source contains the capstone chain ending in:

```lean
def decidableSat_cone (C0 : Concept) (hpo : POFree C0) :
    Decidable (Satisfiable C0)
```

No counterexample was found for the exact abstract semantics. Static source scans
found no declaration-form axiom, `sorry`, `sorryAx`, `opaque`, or `unsafe` in the
two Lean files. The present environment had no Lean executable, so the claimed
Lean 4.32.0 build and axiom footprint were not independently reproduced.

## Capstone chain

| Layer | Declarations | Lines in `POFreeLift.lean` |
|---|---|---:|
| Syntax/semantics | `Concept`, `Interp`, `sat`, `RCC5Interp`, `Satisfiable` | 378-420 |
| Fragment | `POFree`, `pofreeB`, `pofreeB_iff` | 1143-1177 |
| Controls | `Sig`, `supportB`, `sigOkB`, `sigStatic`, `compatB`, `sigDemands` | 41861-41936 |
| GFP | `pruneSig`, `pruneSig_red`, `pruneSig_mono`, `coneScheme_gfp` | 41937-41976 |
| Model signatures | `dkey_sigOk`, `dkey_compat`, `modelSigs_survives`, `modelSigs_in_gfp` | 42067-42269 |
| Completeness | `coneScheme_complete` | 42272 |
| Geometry | `Occ`, `ostep`, `unfLt`, `unfDisj`, `gOD` | 42308-42903 |
| Strategy | `pickTarget`, `pickTarget_some`, `pickTarget_closed`, `osig`, `Gen` | 42506-42689 |
| Propagation | `allPP_gLt`, `allPPI_gLt`, `allEQ_local`, `allDR_gDisj`, `gchild_serves` | 42918-43079 |
| Interpretation | `unfInterp`, `unfInterp_rcc5` | 43907-43914 |
| Truth | `unf_truth` | 43937-44011 |
| Soundness | `coneScheme_sound` | 44024 |
| Characterization | `coneScheme_correct`, `coneScheme_correct_at` | 44038, 44110 |
| Decision | `gfpIter_bound_fixed`, `decidableSat_cone` | 44092, 44127 |

## Most important certification gaps

1. No pinned Lean toolchain or clean-build transcript.
2. No capstone `#print axioms` outputs, despite 883 prints for mostly earlier declarations.
3. Already-NNF syntax only; no raw normalization/preservation theorem.
4. Abstract composition-table semantics only; the separate canonical-set file does
   not yet prove an end-to-end region-semantics and satisfaction bridge.
5. No proved closed signature/complexity bound.
6. No public Boolean core, out-of-scope wrapper, or extracted execution test.
7. The prior Lean regression suite and release/dependency audit are absent.
8. `wp133` exits nonzero and is not suitable as a green release gate in its current form.

See the PDF for the full O00-O23 ledger and release plan.
