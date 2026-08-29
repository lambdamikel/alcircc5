# How to check this

## Build

```sh
cd lean && lean POFreeLift.lean          # Lean 4.32.0 core, no mathlib, ~4 min
```

Expect: exit 0, no output. The file ends with a block of `#print axioms` lines;
add your own for anything you want to audit.

## The three things worth checking first

**1. Zero sorries, and the axiom footprint.**

```sh
grep -c "sorry" POFreeLift.lean          # expect 0 outside comments
```
```lean
#print axioms POFreeLift.decidableSat_cone
```
Expect `propext`, `Classical.choice`, `Quot.sound`. `Classical.choice` should be
reachable only through the correctness proof; the decision itself is a `def`, not
`noncomputable`.

**2. That the claim says what the prompt says.** The chain is:

| theorem | claim |
|---|---|
| `decidableSat_cone` | `POFree C0 → Decidable (Satisfiable C0)` |
| `coneScheme_correct_at` | `Satisfiable C0 ↔ ∃ q ∈ gfpIter … , C0 ∈ q.1` |
| `coneScheme_sound` | a surviving signature carrying `C0` ⟹ `Satisfiable C0` |
| `coneScheme_complete` | `Satisfiable C0` ⟹ a survivor carries `C0` |
| `unf_truth` | every concept in an occurrence's label holds there |
| `unfInterp_rcc5` | the unfolding IS an `RCC5Interp` |
| `pruneSig_mono` | the elimination is MONOTONE (the retracted route's failure) |

Read `Satisfiable`, `sat`, `RCC5Interp`, `POFree` and `comp` yourself before
believing any of it — that is finding class A in the prompt.

**3. Non-vacuity.** Nothing above is useful if the objects are empty. Suggested
checks: is `sigStatic C0` inhabited for a concrete `C0`; does `gfpIter` actually
remove anything (`wp134` says yes: 930 → 237 on one diagnostic); is `Gen` ever
true beyond the root.

## Probes

```sh
python3 probes/wp134_cone_scheme_prune.py     # prune vs the UNSAT diagnostics
python3 probes/wp133_cone_scheme_unfolding.py # the unfolding's frame
```

Both are self-contained Python 3 and re-derive the RCC5 table from finite set
semantics. `wp133`'s truth-lemma column is NOT a check of the plan — it is a
transcription that deliberately omits conditions the plan states; read its
docstring before drawing conclusions from it.
