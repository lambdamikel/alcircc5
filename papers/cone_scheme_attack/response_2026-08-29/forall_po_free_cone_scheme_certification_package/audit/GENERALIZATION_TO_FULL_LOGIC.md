# Generalization to full ALCI_RCC5

## Exact current boundary

`POFree` is used at one Lean truth-lemma branch: `all po D`. That use is
mathematically global, not a local missing lemma. In the ordered-disjoint unfolding,
every distinct pair that is incomparable and not disjoint is residual PO. A universal
PO box at one endpoint therefore constrains arbitrary cousins and descendants born
by unrelated transitions.

Everything else is already fragment-independent. In particular,
`coneScheme_complete` has no `POFree` hypothesis. Consequently the finite scheme is
a certified one-sided refuter for arbitrary already-NNF concepts under the abstract
semantics:

- no accepting survivor implies UNSAT;
- an accepting survivor is conclusive only for the no-universal-PO fragment.

## Boundary formulas

Direct failure:

```text
C_dir = (forall PO.A) and (exists PO.not A)
```

This is unsatisfiable, but the PO-blind control layer has an accepting post-fixed set.

Joint cross-branch failure:

```text
Y       = (forall PPI.A) and (forall PO.A)
C_joint = (exists PP.Y) and (exists PO.not A)
```

If `x PP y` and `x PO z`, then `y PPI x` and `x PO z`; the composition table gives
`rho(y,z)` in `{PPI, PO}`. Either box at `y` forces `A(z)`, contradicting `not A`.
The current local scheme nevertheless serves the PP and PO births independently.

A global all-pairs PO-safety patch is incomplete. The satisfiable formula

```text
C_sat = (exists PP.(forall PO.A)) and (exists PP.not A)
```

has a chain model `x PP z PP y`, where the PO box at `y` is vacuous. The current
unfolding births `y` and `z` as siblings and makes them residual PO. Full logic must
select cross-order/disjointness guards between branches, not merely reject unsafe
residual pairs.

Run `../probes/wp_full_logic_boundary.py` for the two unsatisfiable cases and their
explicit post-fixed controls.

## Proposed research route

1. Formalize the three boundary formulas as Lean regressions.
2. Refactor a conditional `unf_truth_full` under an exact generated-pair
   `POClosed`/PO-Hintikka invariant.
3. Replace independent target signatures by finite rooted RCC5 mosaics containing
   one designated witness per demand and a complete atom matrix among all bag points.
4. Use positive existential continuation interfaces so GFP pruning remains monotone.
5. Prove source-model mosaics form a post-fixed set.
6. Prove the go/no-go theorem: every model admits computably bounded interfaces and
   compatible surviving mosaics amalgamate into a total RCC5 frame without unsafe
   unrecorded PO pairs.
7. Only after that theorem survives attack, formalize full soundness, fixed-round
   correctness, and the `Decidable` wrapper.
8. Finish raw NNF and concrete-region adequacy, reproducible builds, axiom auditing,
   complexity, extraction, and regressions.

The bounded-interface amalgamation theorem is currently unproved. There is no present
basis to claim full decidability. If bounded interfaces fail, the definable universal
modality supplied by all five boxes is a natural ingredient for an undecidability attack.
