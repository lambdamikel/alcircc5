# What is claimed, precisely

Every row names a Lean declaration in `lean/POFreeLift.lean`. Nothing here is
reviewed; the status column says what the ARTIFACT establishes, not what is true.

## The fragment's four quadrants

| quadrant | declaration | status |
|---|---|---|
| horizontal (∃DR/PO/EQ, ∀ non-PO) | `decidableSat_hfrag` | general `Decidable` |
| ascending vertical (∃PP) | `decidableSat_vtower` / `…G` / `…RR` | general `Decidable` |
| descending vertical (∃PPI) | `decidableSat_vtowerRRI` | general `Decidable` |
| mixed (∃PO + ∃PP) | `decidableSat_Cmix` | **witness only** — one concept |

## The pipeline statement

| | |
|---|---|
| `decidableSat_pofree (C0) (h : MixedCompleteness C0)` | `Decidable (Satisfiable C0)`; axioms `propext`, `Quot.sound` only |
| `MixedCompleteness C0` | `Satisfiable C0 → ∃ p ∈ codesM C0 (mixKT C0)³, (p.1).mtAcceptB p.2 C0 = true` |
| `mtAcceptB_sound` | soundness, unconditional |
| `mixedCompleteness_of_code` | one accepted code discharges the premise |

**Claim:** completeness for the fragment is reduced to `MixedCompleteness`, and
nothing else in the pipeline is open. **Not claimed:** that
`MixedCompleteness` holds.

## The mixed quadrant's machinery (§§49–60)

| group | declarations | claim |
|---|---|---|
| the trichotomy | `above_cofinal_is_above_all`, `witness_bounded_or_all`, `finite_pool_gives_cofinal_witness`, `finite_pool_all_or_nothing` | a cofinally recurring one-shot vertical demand is served in-kernel, or by ONE external, or by no finite set |
| the cut | `layer_cut`, `layer_recursion_terminates`, `layer_stack_bounded` | the cap stack is bounded by `typeEnum C0` |
| the cap structure | `odAmalg`, `odFan`, `odTower`, `odSeedCap`, `odSeedCap_frame` | adjoining a cap above a downward-closed set stays ordered-disjoint |
| the transfer | `odSeedCap_old` | on old nodes the capped net = the uncapped net, edge for edge |
| new edges | `cap_above_U`, `cap_po_outside`, `cap_above_kernel`, `cap_pp_cap`, `cap_po_cap`, `cap_not_disj`, `cap_no_dr_edge` | the four new edge classes |
| cap `∀` obligations | `cap_ee_all_pp`, `cap_stab_exists`, `cap_ee_all_ppi`, `cap_reaches`, `cap_stab_up` | both directions discharged |
| sub-labels | `SubLabel`, `subLabel_*`, `cap_required_in_mty`, `cap_ppi_required_in_mty` | cap labels may be sub-types; the required content lies inside the witness's type |

## Known open, stated by the author

1. **`e_ex` ROUTING for cap nodes.** All five relation cases now have their edge
   (§61.2); what is missing is showing the extraction's data supplies a TARGET
   for each demand. (§58.2's `dseed` gap is now implemented — see §61.)
2. **Assembling `MultiTierOk`** for the capped certificate, instantiating
   `M`/`U`/`P`/`capOver`, and the reindex/encode tail.
3. Therefore `MixedCompleteness` itself.

## SCOPE (added after the cold review, F4)

`Satisfiable` quantifies over `Interp` with `RCC5Interp` = reflexive-EQ,
strong-EQ, converse coherence and composition closure — the **abstract
composition-table semantics**. Nothing in the artifact bridges to regions or to a
topological/spatial semantics. So "the ∀PO-free fragment's decision pipeline is
machine-checked end to end" means *for that semantics*, and is **not** a
decidability claim for RCC5 over spatial models.

## Self-corrections already made (check they are complete)

- §46.27 → §46.28: an "unbounded regress" claim withdrawn.
- §47.5: a construction withdrawn — its accumulator pointed the wrong way.
- §55: "apply the nine lemma-ready rows" withdrawn — the extraction consumer
  requires model-realized nodes, which a cap has not.
- §49.4 / §51.4: four probe measurements found to be artifacts — **now SIX; see
  §67.1. `wp101`'s in-kernel rate is RETRACTED: its population was 100% models
  containing the maximal region ℕ, i.e. `wp100`'s artifact reintroduced.**
- §54 → §55: the effort estimate revised from 2–4 sessions to 4–8.
