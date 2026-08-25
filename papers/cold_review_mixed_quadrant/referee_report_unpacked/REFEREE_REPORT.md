# Cold review — ALCI_RCC5 ∀PO-free fragment, mixed quadrant (§§43–60)

Route (a), then (b). All claims below were re-run locally: Lean 4.32.0 downloaded
fresh, `lean POFreeLift.lean` clean in 51 s (exit 0, 0 errors, 0 warnings,
0 `sorryAx` anywhere in the 537 `#print axioms` lines). `decidableSat_pofree`
depends on `propext, Quot.sound` only, as claimed. The build claims are true.

**Verdict: one substantive defect (F1), one false argument with a machine-checked
counter-witness (F2), one gap opened by §58.1 and not recorded (F3). None of them
touches soundness. F1 is the one I would lead with.**

---

## F1 — `wp101`'s in-kernel rate is not ~90%; its measured population is 100 % artifact

This is the T5 target, and it is worse than the prompt anticipates.

`wp101` exists because `wp100` was invalid: finite models have a maximal element,
which satisfies no `∃PP.X`, so every node below it fails `∀PP.∃PP.X` and 100 % of
demands read as one-shot. §49.4 records this and asserts *"the probe class is
sound."*

**`wp101` reintroduces the same maximum.** `build_model`'s cofinite branch is

```python
Reg(True, rng.sample(range(6), rng.randint(0, 3)))
```

and `randint(0, 3)` returns `0` with probability ¼, yielding `Reg(True, ∅)` = **ℕ,
the whole universe**. ℕ is PP-above every chain node `a_i = {0..i}` and above every
other region the class can generate, and nothing is above ℕ — so ℕ ⊭ `∃PP.X` for
every `X`, and every chain node below it fails the `∀PP` guard vacuously.
Verified directly against the probe's own `sat_side`.

Measured (`rev2`, `rev3`, `rev4`; all import `wp101` unmodified and change only
which sides are drawn):

| | |
|---|---|
| P(ℕ among the 6 sides) | **37.8 %** (1511/4000) |
| part A one-shot rate **inside** ℕ-models | **100.0 %** — `wp100`'s number, verbatim |
| part A one-shot rate in models without ℕ | 88.6 % |
| part **B** population drawn from ℕ-models | 67 % |
| part **C** population drawn from ℕ-models | 70 % |
| part **D** population drawn from ℕ-models | **173 / 173 = 100 %** |
| part **E** population drawn from ℕ-models | **208 / 208 = 100 %** |

And the decisive decomposition (`rev3`): of part D's 173 cases,

| | in-kernel | external | total |
|---|---|---|---|
| still one-shot with ℕ deleted | 0 | 0 | **0** |
| **not** one-shot with ℕ deleted | 158 | 15 | 173 |

**Every single case part D counts is one-shot only because ℕ sits on top.** Delete
ℕ and all 173 are persistent — which is precisely why "`X` recurs on the chain"
and why they score in-kernel. The 91.3 % is a measurement of *persistence*. Run
part D over ℕ-free models and the qualifying population is **empty**.

Three consequences:

1. §49.4's *"Only the IN-KERNEL rate is stable across all four model-class
   variants (89.2 / 90.2 / 83.5 / 91.3 %)"* has its explanation reversed. The
   three recorded fixes all touched the bounded-segment generator and the window
   widths; none touched the cofinite branch, so all four variants carry the same
   maximum with the same ~38 % frequency. **Stability across variants is evidence
   of a shared artifact, not of robustness.** It is stable for the same reason
   `wp100`'s 100 % was stable.
2. §49.2's *"the load is carried by … the 89.2 % in-kernel rate, which is not
   [model-independent]"* and §49.5's *"chain recurrence → served in-kernel, cost 0
   (~90 % measured)"* have no measurement behind them.
3. §49's *validity check itself* (part A: "persistent demands appear at all")
   passes only because 62 % of models happen to lack ℕ. The probe never sees that
   38 % of its own sample is the artifact it was built to escape.

The probe's own docstring says the domain is *"a genuinely infinite ascending
PP-chain with NO maximal element, plus sides"* — true of the chain, false of the
domain once ℕ is a side.

**Secondary artifact, same file.** `m._stab = 11`, commented *"above this index
every side's relation to the chain has stabilised"*, and `sat_chain_res` evaluates
the whole chain-facing quantifier at indices 11…11+p−1 on that basis. But the
bounded-segment generator draws `M ∈ [stab+1, stab+5p]` **by design**, so those
sides change their relation to the chain *above* `_stab`. Measured: **295/300
models** have a side/chain relation still changing above index 11; the highest
such index observed is **65**. So the "exact, boundary-free" closed form is
evaluated inside the unstable zone, while part D tests cofinality out to 11+64p.
That is artifact #6, independent of ℕ.

*What this does not touch:* nothing in `POFreeLift.lean`. §49's ten theorems are
correct (see F5). The design record's own hedge — "the load is on the theorems" —
holds. But CLAIMS.md's self-correction list ("§49.4/§51.4: four probe measurements
found to be artifacts") should read six, and the ~90 % should be struck from
§49.1/§49.2/§49.5 rather than re-qualified.

Reproduce: `python3 rev2_wp101_top_region.py`, `rev3_wp101_partD_decomposed.py`,
`rev4_wp101_other_parts.py` (drop them in `probes/`).

---

## F2 — §51.1's "forced, not chosen" is false, and the §58.2 gap is self-inflicted

T3 asks whether `capSeed`'s "cap disjoint from nothing" is forced. **It is not.**

The argument, in the `amLt` docstring and in design-record §51.1, is:

> Two cap nodes both sit above the whole closure `U`, so `djDown` would push their
> disjointness down onto `U`'s elements and make them disjoint from *themselves*.
> So a cap is always a POSET-shaped structure: `PP`/`PPI`/`PO`/`EQ` only.

The premise is correct and establishes exactly one thing: **no cap↔cap `DR`**
(and only when `U` is nonempty). The conclusion generalises it to *every* edge at
a cap. `amDisj` and `capSeed` implement the general version via a catch-all
(`| _, _ => False`), and that catch-all — not any structural necessity — is what
makes `∃DR` at a cap unservable (`cap_no_dr_edge`), i.e. known-open item #1.

The same docstring then says a cap's `∃DR` *"must therefore be served from the
BASE, by a node disjoint from the entire closure"* — a base↔cap `DR` edge that
the definition it is attached to forbids. So the docstring does not mean what it
says relative to its own definition, and §58.2 later contradicts §51.1's
conclusion without withdrawing it.

**Machine-checked counter-witness** (`referee_appendix.lean`, appended to
`POFreeLift.lean`; compiles clean, `RefereeCapDR.odAmalgDR` **depends on no
axioms at all**):

* `odAmalgDR` — `odAmalg` generalised with a cap↔base disjointness `B : M → N → Prop`,
  still an `ODStruct`. Side conditions:

  | | |
  |---|---|
  | `hBnotU` | a cap is not disjoint from anything it is above |
  | `hBdown` / `hBP` | `B` downward closed in the base and along `P` |
  | `hBU` | the cap's `DR` partner is base-disjoint from the **whole** closure |

  `hBU` is literally §58.2's `hdbase`, and §51.2's `cofinal_dr_all` is what
  supplies it on the model side. `B = fun _ _ => False` recovers `odAmalg`
  exactly, so this is a strict generalisation.
* `odAmalgDR_frame` — `odNet_frame` applies unchanged: composition closure still
  free, no cell checked by hand.
* `witnessStruct` / `witness_pp` / `witness_dr` / `witness_frame` — a concrete
  three-element instance in which a cap is `PP`-above a downward-closed `U`
  **and** `DR` to a base node, and the induced net is a genuine `Frame`.

So `cap_no_dr_edge` is a theorem about `odSeedCap`, not about caps.
"A cap is always poset-shaped (`PP`/`PPI`/`PO`/`EQ` only)" is false as stated, and
`amDisj` **is** a simplification. The corrections I would make: §51.1's heading
and conclusion restricted to cap↔cap; the `amLt` docstring likewise; and
`odAmalgDR` dropped in as the structural half of §58.2 (the remaining work there
really is the mechanical `capSeed_sym`/`_sep`/`_old` rework).

---

## F3 — §58.1's fix opened a third gap, in a row §57.2 still records as vacuous

T4 asks whether any `MultiTierOk` row is missed, and whether `e_ex` has more than
two gaps. The answer is yes, and the new one is not in `e_ex`.

§58.1 closed `e_ex` at `r = pp` for cap nodes by giving `capElt` a cap-internal
order `P`, so that `cap_pp_cap : P m m' → odNet (OC) (inl (inr m)) (inl (inr m')) = pp`.

That new `PP` edge creates `MultiTierOk` obligations that did not exist before:

* `ee_all` at `r = pp` from cap `m` to cap `m'`: `∀PP.X ∈ tauE (inr m) → X ∈ tauE (inr m')`;
* `ee_all` at `r = ppi` back from `m'` to `m`.

**No lemma in the file discharges either.** The complete inventory of cap `∀`
lemmas is `cap_ee_all_pp`, `cap_stab_exists`, `cap_stab_up`, `cap_reaches`,
`cap_ee_all_ppi`, `cap_required_in_mty`, `cap_ppi_required_in_mty`. Every one of
them requires the node on the closure side to satisfy `I.rho e (c j) = pp ∨ e = c j`
(or `hz` in the same shape) — *at or below a chain node*. A cap's witness `w m`
is by construction **above** `c i₀`, so none of them applies to a cap↔cap edge.

Meanwhile §57.2's row still reads

| `ee_all` cap↔cap (`PO`) | `cap_po_cap` + `mty_no_all_po` |

which was correct for §51.5's antichain (`P = ∅`) and is stale for `P ≠ ∅` — and
`cap_po_cap` now carries the hypotheses `¬ P m m'`, `¬ P m' m` that say so.
§57.3 (*"Every `∀`-propagation obligation the cap creates is now certified, in
both directions"*) and §59.1 (*"both `∀` directions … done"*) both post-date §58.1
and are, as written, overclaims. §59.2 half-notices this — "a label must still
absorb … the `∀PPI` consequents of any higher cap" — but the status tables were
not revised.

**Why it is a real obligation, not bookkeeping.** `cap_pp_cap` derives the `PP`
edge from the *abstract* order `P` alone, with no model-side counterpart demanded,
while the caps' labels are *model* types `mtk C0 I (w m) (cbud m)`. Nothing in
`odSeedCap` or its companions ties `P m m'` to `I.rho (w m) (w m') = pp`.
Concrete falsifier: take `M = Bool`, `P = {(false, true)}`, and `w false = w true`
(the same model node — permitted, since `w` is unconstrained). Then
`ee_all` demands `X ∈ mty C0 I (w true) = mty C0 I (w false)` whenever
`∀PP.X ∈ mty C0 I (w false)`, i.e. that `∀PP.X → X`, which fails for any `X` false
at `w false`. The missing side condition is roughly

```
hPmodel : ∀ m m', P m m' → I.rho (w m) (w m') = pp
```

plus, for the `∀PPI` direction, that everything `P`-below `m'` is `PP`-below
`w m'` in the model. With `hPmodel`, `cap_ee_all_pp`'s proof shape transfers
(`sat_all_pp_up` does the work); it is the same argument, but it is an argument
that has not been made, and §52's layer stack is what generates the `P`s.

**Answer to "are there more than two?"** In `e_ex` itself I found no third gap —
`eq`/`pp`/`ppi`/`po`/`dr` is the complete case split and §58.3's table is right.
The third gap is that closing gap 1 moved work into the `ee_all` rows.

---

## F4 — T1: the pipeline is honest. Three checks, all pass; one cosmetic nit

**(i) Is `mtAcceptB_sound` really unconditional?** Yes.
`(F : FinMT) (root : Nat) (C0 : Concept) (h : F.mtAcceptB root C0 = true) : Satisfiable C0`.
`FinMT` is plain list data with no `Prop` fields; there is no side hypothesis and
no `Interp` in sight. Axioms `propext, Quot.sound`.

**(ii) Oracle-inhabitable?** No. `MixedCompleteness C0` is
`Satisfiable C0 → ∃ p ∈ codesM …, mtAcceptB … = true`, whose consequent is a
*decidable, bounded* existential over a computed list. A `Satisfiable` proof does
not discharge it; you must exhibit an accepting code, or refute satisfiability
(`mixedCompleteness_of_unsat`, correctly flagged). This is the right premise
shape and it is not the round-26 failure.

*Nit:* `mixedCompleteness_of_code` is `:= h` — `MixedCompleteness C0` is
*definitionally* its hypothesis, so the theorem is `id` and carries no content.
Its docstring's conclusion ("never oracle-inhabitable by a `Satisfiable` proof")
is true but is not established by it. Either delete it or restate it as the
documentation it is.

**(iii) Is `codesM C0 (mixKT C0)³` a fixed enumeration computed from `C₀`?** Yes.
`mixKT C0 = mixBound C0 (typeEnum C0).length (mdepth C0)`; `typeEnum C0 =
allListsLe (cl C0) (cl C0).length`; `mixBound`, `mtkBound`, `mdepth`, `cl` all
take `Concept` only — no `Interp`, no `α`, anywhere in the chain. `codesM` is a
pure `flatMap` over `allListsLe`. Independent corroboration: `decidableSat_pofree`'s
axiom profile *excludes* `Classical.choice`, which it would necessarily inherit
from any model-side ingredient (every model-side lemma in the file carries it).
The `def` is not marked `noncomputable`, so it is genuinely a program.

**Scope note (the largest gap between artifact and headline).** `Satisfiable` is
`∃ α, ∃ I : Interp α, RCC5Interp I ∧ …`, and `RCC5Interp` is reflexive-EQ,
strong-EQ, converse-coherence and *composition closure* — the abstract
composition-table semantics. Nothing in the file bridges to regions or to a
topological/spatial semantics; the header's own hedge is "modulo compactness",
and line 233 takes the definitional stance that a composition-closed net *is* an
ALCI_RCC5 frame. CLAIMS.md is precise because it names the Lean declaration, but
"the ∀PO-free fragment's decision pipeline is machine-checked end to end" will be
read by a referee as decidability for RCC5, and it is not that yet. I would say
so in one sentence in CLAIMS.md.

I re-derived the composition and converse tables from finite-set semantics
(non-empty subsets of an *n*-set, `comp(R,S) = {rel(x,z) : R(x,y), S(y,z)}`;
the table is stable from n = 4). **0 mismatches in 25 of 25 cells, 0 in converse**
against `POFreeLift.lean` lines 51–71. No table-input defect.
(`rev1_comp_table.py`.)

---

## F5 — T2: the §49 trichotomy says what the prose says

I checked all four statements against their docstrings and found no hidden
hypothesis doing the work.

* `above_cofinal_is_above_all` — hypotheses `hasc : ∀ i j, i < j → I.rho (c i) (c j) = pp`
  and `hcof : ∀ N, ∃ i, N < i ∧ I.rho (c i) w = pp`; conclusion `∀ j, I.rho (c j) w = pp`.
  That is exactly "above cofinally many is above all". `hasc` is the full
  order, not just successor steps, but it is *derivable* from successor steps by
  `comp(PP,PP) = {PP}` (verified in F4), so it is not doing illegitimate work.
  Axiom-free, and the proof is the one-liner the docstring describes.
* `witness_bounded_or_all` — excluded middle over `above_cofinal_is_above_all`. Fine.
* `finite_pool_gives_cofinal_witness` — `recurrent_tail`'s statement
  (`∃ M, ∀ j ≥ M, ∀ N, ∃ i ≥ N, f i = f j`) is used correctly at `N + 1`, so `hcof`'s
  strict `N < i` really is obtained. Fine.
* `finite_pool_all_or_nothing` — correct, and the "never 2 or 3 partial servers"
  reading is right: a second server that covers a cofinal tail is above the whole
  chain by transitivity, so it subsumes the first.

**One precision point.** The docstring of `finite_pool_gives_cofinal_witness`
says: *"the certificate's external set is finite BY CONSTRUCTION — so this is not
a hypothesis about models, it is a property of the object being built."* That is
a category slip at the one place it matters. `hpool` quantifies over witnesses in
the **model**, and the extraction runs *from* a model: at extraction time you do
not yet have a finite external set, you are trying to produce one. The lemma is
about a fixed finite pool of model elements; it does not say a model's witnesses
come from one. §49.5's case 3 is precisely the case where they do not, so the
docstring's framing understates what is open. The theorem is right; the gloss
should be trimmed.

Minor completeness observation on the trichotomy itself: cases 1–3 are stated
over "in-kernel / one external / no finite external set", but the certificate's
`e_ex` has a *third* service route — `∃ k, conv (T.K k e) = r ∧ …`, i.e. service
by another kernel, which is an infinite set of model nodes and not a finite pool.
Neither `oneshot_in_kernel` (same chain) nor `finite_pool_*` (finite pool of
elements) covers it. It is probably subsumable — a kernel with constant interface
above `c i` for all `i` behaves like a cofinal server — but the trichotomy as
written does not say so.

---

## F6 — T6: withdrawn claims still asserted

Two, both already named above:

1. **§51.1's conclusion**, superseded in substance by §58.2 and never withdrawn.
   §51.1 heading, §51.1 body ("`amDisj` is not a simplification"), and the `amLt`
   docstring in the artifact all still assert it. (F2.)
2. **§57.2's cap↔cap row and §57.3 / §59.1's "both `∀` directions done"**,
   invalidated by §58.1's introduction of `P`. (F3.)

I checked the four self-corrections CLAIMS.md lists and did not find any of *those*
re-asserted: §46.28's withdrawal is clean, §47.5's construction does not reappear,
§55's "nine lemma-ready rows" is not applied anywhere (§56 rebuilds at the label
level as stated), and the §54→§55 estimate revision is consistent.

---

## The strongest statement I am willing to make about what IS established

* **Soundness is real and unconditional.** `mtAcceptB_sound` is a genuine
  certificate→model theorem with no premise, on `propext`/`Quot.sound`, and
  `cboth_satisfiable_exec` shows the checker runs in the kernel. I found nothing
  wrong with it.
* **The reduction is real.** `decidableSat_of_codes` + `codesM` + `mixKT` is a
  correct decision reduction against a fixed, `C₀`-computed enumeration, and
  `MixedCompleteness` is the right premise: not oracle-inhabitable, and
  discharged by exhibiting one accepting code. Naming it was the right move.
* **`odNet_frame` is the load-bearing brick and it holds.** Any ordered-disjoint
  structure induces a composition-closed RCC5 net, with the table verified
  independently. Everything built on it (`odTop`, `odAmalg`, `odSeedCap`,
  `odTower`, `odFan`, and my `odAmalgDR`) gets composition closure for free.
* **`odSeedCap_old` is correct.** I read the proof line by line: `capMixLt_old`
  reflects the order, `capSeed_old` + `capMixLe_*` reflect the downward-closed
  disjointness, and the five-way case split on `odNet` is exhaustive. The transfer
  theorem does hold, edge for edge, on embedded old nodes. **But its docstring
  overreaches**: "every obligation already certified for the extraction's
  structure carries over to the capped one unchanged" is only true because
  `MultiTierOk`'s `∀` rows happen to be stated per *edge class*; a `∀`-obligation
  is not an edge-local object in general, and the new base→cap edges are exactly
  where the work is. Say "every obligation on old×old edges".
* **§49's ten theorems are correct** and are, as the design record says, the part
  carrying the load. After F1, they are the *only* part carrying it.

## Where I would attack next, in order

1. **The cap↔cap `∀` rows (F3).** This is the live gap and it is where a fourth
   first-contact failure would show. Write `hPmodel` and see whether §52's layer
   stack can actually supply it — the layers are generated by the regress, and it
   is not obvious the regress produces model witnesses in `PP` order rather than
   merely in `P` order.
2. **Rebuild `wp101` over a class with no maximum** (drop `Reg(True, ∅)`; or
   better, use regions with an infinite complement so no element is a top) and
   re-measure. My `rev3` says the qualifying population is then *empty* on the
   shipped generator. That is itself interesting: if genuinely cofinal one-shot
   demands cannot be *reached* in a top-free finite/cofinite class, the class is
   too poor to answer §49.5's residual question either way, and a different class
   is needed before any rate is quoted.
3. **`e_ex` at `r = dr`.** `odAmalgDR` (F2) is the structural half, checked; the
   `capSeed`/`capSeed_sym`/`capSeed_sep`/`capSeed_old`/`odSeedCap_old` rework is
   mechanical as §58.2 says.
4. **The multi-kernel instantiation of `cap_ee_all_pp`.** Its `hej` hypothesis
   ties the closure node to *one* chain `c`. §57.2's "`ek_all`/`ke_all` kernel↔cap
   — same two lemmas" is fine for kernels drawn from the cap's own chain; for a
   cap covering several kernels (`capOver` is not `m`-indexed, so every cap sits
   above every covered kernel) the consumer has to produce `hej` for each covered
   kernel's phase representatives. That is unwritten work, not an error, but it
   belongs in the §59.1 "not started" row rather than the "done" row.

---

### Files

| | |
|---|---|
| `referee_appendix.lean` | append to `POFreeLift.lean`; compiles clean, no `sorryAx`. `odAmalgDR` axiom-free. |
| `rev1_comp_table.py` | re-derives RCC5 comp/conv from finite sets; 0/25 mismatches |
| `rev2_wp101_top_region.py` | ℕ frequency; part-D split by ℕ; `_stab` check |
| `rev3_wp101_partD_decomposed.py` | the 173/173 result |
| `rev4_wp101_other_parts.py` | parts A/B/C/E contamination |

The three `rev*` scripts import `wp101_periodic_oneshot_vertical` unmodified and
must sit in `probes/`.
