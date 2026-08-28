# What is machine-certified, obligation by obligation

Lean 4 core (no mathlib), ~42,700 lines, 0 sorries / 0 warnings / 0 `sorryAx`;
axioms `propext`, `Quot.sound`, `Classical.choice` only. **Unreviewed.**

The certificate is a `MultiTier`: finite externals with labels, plus finitely many
kernels (periodic towers with finite phase labels), over a declared
ordered-disjoint frame. `swCert_ok` reduces its 19 obligations to 11 hypotheses.

| hypothesis | status |
|---|---|
| `hlab`, `hplab` | free — labels are the normalised full model type (`mtyLab`, `kLab`), `SupportOk` by `normL_supportOk ∘ mty_supportOk` |
| `hp` | free — `KernelData.ppos` |
| `hkpp`, `hkppi` | **certified.** Both vertical universals reach every phase of a kernel of either direction; half is the chain order, half is one use of `KernelData.cty`, in opposite directions |
| `hke`, `hek` | **certified given `KernelRows`**, which is achievable: `externals_stabilize` folded into the segment selection gives a constant row to a finite external list fixed in advance |
| `hkq` | **certified** (`fused_kq_all`) — round 1's Target B, formalized |
| `hee` | **certified** on model-agreeing edges, and on borrowed edges: vertical (`borrowed_ee_all`) and horizontal (`borrowed_dr_ok`, including the cone obligations that disjointness's downward closure creates) |
| `hex` | node set **certified** finite, bounded, reached and covered (`ptIterD_phase1`); every case has its edge |
| `hkex` | reduced to placement — **Target E** |

## Phase 1, at the down-spectrum gate

`ptIterD_phase1`: from a duplicate-free seed, the node set closes within
`|ns₀| + |keyEnum C₀|·|cl C₀|` rounds, at a set no larger, and every existential
of every node is served by a kernel or inside the set. `keyEnum C₀ = typeEnum ×
sublists typeEnum`, of size `N·2^N` — the refinement's price, made explicit.

The chain is stated over an ABSTRACT gate (`ptKidsG`/`ptExtendG`/`ptIterG`), which
needs exactly four properties of it: selects from the list, monotone under append,
bounded, covers every node with a same-key representative. Every proof went
through unchanged when the gate was swapped, which is why round 1's refutation
cost a change of instance rather than a rewrite.

## The Target-B chain, for reference

* `atom_seq_stabilizes` (+ descending dual) — any atom sequence with
  `f(n+1) ∈ comp ppi (f n)` is eventually constant. This is the abstract core that
  `external_stabilizes` had proved inline; extracting it is what allows the rank
  argument to run a second time, on objects that are not relations to a point.
* `two_tower_rectangle_gen` — direction-generic. Row stabilization depends on the
  second tower's direction; row-limit stabilization only on the first's.
* `finite_fusion_recurrent` — pairs handled in INDEX ORDER (the rectangle fixes the
  first tower's segment and pushes the second out, so the reverse direction must
  come from `conv`), and the period chosen DURING the induction, because the
  rectangle's threshold depends on the earlier segment's length while equal-type
  endpoints determine that length.
* `two_tower_segment_ne_eq` (axiom-free) — a length-2 segment forces the rectangle
  atom `≠ EQ`, preserving strong equality at the macro level.

## The Target-A repair, for reference

* `shared_top_reaches_cone` / `shared_top_forces_both_cones` (both **axiom-free**)
  — the reusable content of round 1's counterexample, with no reference to its
  eight points.
* `cone_agreement_of_spectrum` — a body's truth is fixed by the point's model
  type, so equal lower spectra make "holds across my cone" agree.
* `union_cone_body`, `dkey_union_serves` — one member's `DR`-witness carries its
  `∀DR` bodies across every member's cone. This is what `wp132` measures at 0
  failures on 7,525 non-vacuous groups; the measurement is now a regression.

## Not certified

* **Global acyclicity of the declared order** in the non-agreeing case, and the
  `ltNotDj` clause on a `DR`-incomparable witness — **Target D**.
* `hkex` placement — **Target E**.
* Packaging: rebuilding `KernelData` from the fused segments (needs `ccovers` at
  the chosen period), the `Fin` reindex, `encodeMT`/`hcompl`, and the final
  assembly into `MergedExtractionAt`. We call this bookkeeping; this project has
  misjudged that word before.
