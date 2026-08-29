# Cold review — `decidableSat_cone`, POFreeLift.lean

**Verdict: SOUND on the claim, with two scope gaps that are understated and one
piece of in-file prose that is flatly wrong about the architecture. No
counterexample; no defect found in `decidableSat_cone` or its supporting chain.**

I read `COLD_PROMPT.md`, `BUILD.md`, the three source files, and nothing else.
Phase 2 was read only after the Phase 1 pass below was complete.

---

## 1. The build

```
elan run leanprover/lean4:v4.32.0 lean POFreeLift.lean
  → exit 0, 37 s wall (4 cores), 44 430 lines / 2 302 declarations
  → zero errors, zero warnings, zero `sorry`
elan run leanprover/lean4:v4.33.1 lean POFreeLift.lean   → exit 0 as well
lean RCC5NormalForm.lean                                  → exit 0, 0.3 s
python3 wp134_cone_scheme_prune.py                        → exit 0, all 7 verdicts as predicted
```

Static audit of the source: **no** `axiom`, **no** `sorry`, **no** `native_decide`,
**no** `set_option` of any kind, **no** `implemented_by` / `unsafe` / `opaque` /
`partial`, no `macro`/`elab`. So there is no place to hide a hole outside the
kernel, and no weakened checking.

The file's 815 `#print axioms` lines partition into exactly four footprints:
`[propext, Classical.choice, Quot.sound]` (625), `[propext, Quot.sound]` (106),
`[propext]` (78), plus a handful smaller. Nothing else appears. The named
capstones:

| declaration | axioms |
|---|---|
| `decidableSat_cone` | propext, Classical.choice, Quot.sound |
| `coneScheme_correct_at` | propext, Classical.choice, Quot.sound |
| `coneScheme_sound` | propext, Classical.choice, Quot.sound |
| `coneScheme_complete` | propext, Classical.choice, Quot.sound |
| `unf_truth` | propext, Classical.choice, Quot.sound |
| `unfInterp_rcc5` | propext, Classical.choice, Quot.sound |
| `pruneSig_mono` | propext, Quot.sound |
| `coneScheme_unsat_full` | propext, Classical.choice, Quot.sound |

---

## 2. Phase 1

### 2.1 Does `Satisfiable` mean what a description logician would mean? — Yes.

The trusted base of the capstone's *statement* is small and I audited all of it:
`Atom`, `conv` (:50), `comp` (:54), `Concept` (:378), `Interp` (:390),
`sat` (:397), `RCC5Interp` (:410), `Satisfiable` (:419), `POFree` (:1143).

* **The composition table is RCC5's, exactly.** I re-derived the table from
  finite set semantics (regions = non-empty subsets of an *n*-set, `PP` = proper
  ⊂, `DR` = disjoint, `PO` = otherwise-intersecting) for n = 4, 5, 6 and diffed
  all 25 cells against the transcription in `comp`. **Zero mismatches at every
  n** — and the match is *exact*, not a safe over-approximation: every cell is
  the achievable set. `conv` is correct and `conv_invol` holds.
* **Strong EQ is really identity.** `refl_eq` + `eq_id` give
  `rho x y = eq ↔ x = y` on the domain. This is not decorative: I ran the
  procedure on `∀EQ.⊥` and got UNSAT (needs `refl_eq`) and on `∃EQ.⊥` and got
  UNSAT.
* **`sat`'s `∀` clause is right**: `∀ y, I.dom y → I.rho x y = r → sat I y c`,
  properly relativised to `dom`, mirroring the `∃` clause. `rho` is total but
  every constraint and every quantifier is `dom`-relative, consistently.
* **The semantics is carrier-polymorphic**: `∃ (α : Type), ∃ I : Interp α, …`.
  Not fixed, not finite, not decidable-domain. `dom : α → Prop` may be a proper
  subset, and `∃ x, I.dom x` forces non-emptiness, so it is not vacuous.
* Roles are the five base atoms only. That is *not* a restriction: the atoms are
  JEPD and finite, so `∃(R∪S).C = ∃R.C ⊔ ∃S.C` and `∀(R∪S).C = ∀R.C ⊓ ∀S.C`.
  See §4.4 for the one place this interacts badly with `POFree`.

### 2.2 Does `POFree` exclude exactly `∀PO`, in the right closure? — Yes.

`POFree` (:1143) is structural over every constructor and recurses through
`ex _ c` as well, so it forbids `all po _` anywhere in the syntax tree while
leaving `∃PO` completely free (`pofreeB (∃PO.(A ⊓ ∃PO.⊤)) = true`, checked).
The closure used for labels is `cl` (:2932), which is transitively closed
(`cl_trans`), all label concepts come from `typeEnum C₀ = allListsLe (cl C₀) _`,
and `pofree_cl_all` (:3346) discharges `∀ r E, all r E ∈ cl e → r ≠ po`. So no
`∀PO` can appear in any signature type of any surviving signature. Right closure.

### 2.3 Is the `Decidable` real? — Yes, genuinely executable. Verified two ways.

`decidableSat_cone` is a plain `def` (not `noncomputable`) that the compiler
accepted, which already rules out `Classical.propDecidable` in the data. I
confirmed it operationally:

* **Compiled evaluation.** Compiling the file to an olean and `#eval`-ing
  `@decide (Satisfiable C) (decidableSat_cone C h)` returns values on 15
  concepts (§2.6).
* **Kernel evaluation.** Stronger: `by rfl` closes
  `decide (Satisfiable ⊤) = true` and `decide (Satisfiable ⊥) = false` at the
  *kernel*, giving `Satisfiable Concept.top` and `¬ Satisfiable Concept.bot`
  as `#print axioms`-clean theorems *obtained through the capstone*. A classical
  instance cannot reduce; this one does.

**Where `Classical.choice` enters** — three places, none of them in the data:

1. `anti_mono_stalls` / `gfpIter_stabilizes` use `Classical.byContradiction`
   (pure `Prop`);
2. the completeness side — `mty`, `dspec`, `dkey`, `modelSigs` are
   `open Classical in noncomputable def`s, because reading a model's type off an
   arbitrary interpretation needs classical decidability of semantic predicates;
3. the soundness side, via `odNet` (:20026), an `open Classical in noncomputable
   def` that branches on `lt`/`disj` — so the *model* is noncomputable, which is
   fine, it is a mathematical object, not a computation.

The §286.3 docstring's "no choice, no oracle" is true of the *computation* but
not of the *term*: `#print axioms decidableSat_cone` does list `Classical.choice`.
Worth one qualifying clause in that comment, since a reader will diff the two.

### 2.4 Is anything vacuous? — No, and I checked each candidate.

* `sigStatic ⊤` has 8 members and all 8 survive; `sigStatic ⊥` has 2 survivors,
  neither carrying `⊥`. So the elimination neither empties nor no-ops.
* `Satisfiable` is inhabited both ways as kernel theorems (§2.3), so it is
  neither always-true nor always-false.
* `coneScheme_sound`'s hypotheses are inhabitable: the `⊤` run goes *through*
  `coneScheme_sound` (it is the ⇐ half of `coneScheme_correct_at`), so the
  unfolding path is exercised, not just stated.
* The `Decidable` is used — by me, at the kernel, above.
* Independent sanity that `sat`/`RCC5Interp` have content: I built an explicit
  three-point RCC5 model by hand (`{1}⊂{1,2}`, `{1}⊂{1,3}`, `{1,2}` PO `{1,3}`)
  and used it to prove a satisfiability, and separately proved a
  composition-forced unsatisfiability from `conv_` + `comp_` alone (§2.6).

### 2.5 Is the claim what the theorem says? — Almost; one hypothesis is missing from the table.

`decidableSat_cone (C0 : Concept) (hpo : POFree C0) : Decidable (Satisfiable C0)`
is exactly as advertised: one hypothesis, no premise, no oracle.

The one mismatch is in the supporting table:

> `coneScheme_sound` | a surviving signature carrying `C0` gives a model

**`coneScheme_sound` (:44024) also takes `hpo : POFree C0`.** That is not a
technicality — it is the *whole* location of the fragment restriction, and the
file's own prose gets it backwards in two places (§4.1).

Everything else on the table matches:
`coneScheme_correct_at` (:44110) is the stated `↔` at the named round
`(sigStatic C₀).length`; `coneScheme_complete` (:42272) genuinely takes no
`POFree`; `pruneSig_mono` (:41947) is the stated monotonicity, choice-free;
`coneScheme_unsat_full` (:44148) is genuinely hypothesis-free in the concept and
correctly described as one-sided.

### 2.6 The counterexample hunt

Because the whole chain is kernel-checked, a wrong answer is only reachable
through a wrong *definition*. I attacked from both ends.

**(a) Running the procedure.** 15 concepts with `|cl C₀| ≤ 2` (the ceiling — see
§4.2). Every answer is correct:

| concept | procedure | correct |
|---|---|---|
| `⊤` / `⊥` | SAT / UNSAT | ✓ |
| `A₀` / `¬A₀` | SAT / SAT | ✓ |
| `∃PP.⊤`, `∃PPI.⊤`, `∃DR.⊤`, `∃PO.⊤` | SAT | ✓ |
| `∃PP.⊥`, `∃DR.⊥`, `∃PO.⊥` | UNSAT | ✓ |
| `∀PP.⊥`, `∀DR.⊥` | SAT (vacuous) | ✓ |
| `∃EQ.⊥` | UNSAT | ✓ (strong EQ, local clause) |
| `∀EQ.⊥` | UNSAT | ✓ (reflexivity — a real test) |

**(b) Composition-forced unsatisfiability, proved independently.** For
`CB = ∃PPI.(∀DR.A₀) ⊓ ∃DR.(¬A₀)` I proved `¬ Satisfiable CB` in Lean directly
from `conv_` and `comp_` (`rho y x = pp`, `rho y z ∈ comp pp dr = [dr]`, so
`∀DR.A₀` at `y` kills `¬A₀` at `z`). It goes through, on `[propext]` alone. So
`RCC5Interp` is doing real work and `Satisfiable` is not a permissive stub. I
then hand-traced the control layer on `CB` and it rejects for the right reason:
the `∃PPI` transition forces `T_y ∈ S(q_x)`, so the cone-wide `∀DR` condition in
`compatB` puts `A₀` into `T_z`, and `supportB`'s clash clause kills it.

**(c) Differential testing.** 4 000 random `∀PO`-free concepts (depth ≤ 3, two
atoms), running the *uncapped* control layer — all support types × **all**
predecessor-sets, no `|S|` truncation (a further 3 098 candidates were skipped as
too large to enumerate uncapped) — against brute-force search over every strong-EQ,
converse-closed, composition-closed labelling on ≤ 3 points with every valuation,
and re-checking any "accepted, no small model" hit at 4 points:

```
control layer REJECTED a concept with a real model:   0
control layer ACCEPTED with no model up to 4 points:  0
```

**(d) The artifact's own probe.** `wp134` reproduces: 180 cap-free DR walls with
0 breaches, all three UNSAT diagnostics rejected, all four SAT ones accepted,
elimination non-vacuous.

I could not construct a counterexample, and after auditing the trusted base I do
not think one exists at the level of the stated theorem.

---

## 3. Phase 2 — the authors' four worries

### 3.1 Adequacy

I checked the geometry independently rather than trusting `odNet_frame`. Given a
strict order `<` and a symmetric, irreflexive, `<`-downward-closed disjointness
`⊥` never meeting comparability, `odNet` (EQ diagonal / PP-PPI comparable /
DR disjoint / **PO residual**) is composition-closed. I verified all sixteen
non-degenerate `(x?y, y?z)` cases by hand against the table; each one turns on
exactly one ODStruct axiom, and `djDown` + `djIrr` is what rules out the two
dangerous cells (`ppi;pp` must avoid `DR`; `ppi;dr` and `po;pp` must avoid the
wrong side). It holds. This is the load-bearing piece and it is correct.

I also checked what the unfolding does to *pairs it never explicitly declares*.
Distinct children of one occurrence are `PO` — except a `PP`-birth and a
`PPI`-birth of the same parent, where the order forces `PP` through the parent,
and that is exactly what `comp pp pp = [pp]` demands. Every case I checked lands
in the right cell.

### 3.2 `prune`'s balance

Monotone: yes, and for the stated reason — `pruneSig` (:41937) asks only that
each demand *have* a target in `X`, an `∃` over `X`, so growing `X` can only
help. `pruneSig_mono` is choice-free.

Strong enough: the pairing that carries it is
`compatB pp/ppi` (:41912) pushing `sigCone q ⊆ q'.2` along every order edge, plus
`sigOkB` (:41880) requiring `allBodies pp U ⊆ T` and `allBodies ppi T ⊆ U` for
every `U ∈ S`. Composed along `tcl ostep` these give: *the type of every
occurrence strictly below `a` is in `S(q_a)`*, in both of `ostep`'s directions.
That invariant is what makes `allPP_gLt`, `allPPI_gLt` and the cone×cone `∀DR`
condition work. I checked the model side of the same conditions by hand — for
`r = pp`, `t ∈ dspec x` and `rho x y = pp` gives `rho z y ∈ comp pp pp = [pp]`,
so `dspec x ⊆ dspec y`; for `r = dr`, `u ≤ x`, `x DR z`, `v ≤ z` gives
`rho u v ∈ comp dr ppi = [dr]` — so the `compatB` conditions are exactly the
forced closure, neither weaker nor stronger. That is why the two directions meet.

### 3.3 The unfolding's geometry / the vertical base

`vbase` (:42359) strips leading `pp`/`ppi` births and stops at the first
`dr`/`po`/`eq` one. `ostep` preserves it (`rfl`, both cases); a `DR` birth
changes it on a length count. `ltNotDj` then falls out. I checked the one case
this argument does *not* obviously cover — that a `PO` birth is genuinely
residual, i.e. neither comparable nor disjoint — and `unf_po_not_disj` gets it
right: the only surviving orientation is killed by
`|vbase b| ≤ |b| ≤ |u| − 1 < |u| + 1`. Note `vbase` treats `po` like `dr` (a
`PO` birth starts a fresh component too), which is what makes that count work.
Good.

### 3.4 "Completeness went through in one attempt — check what moved where"

It moved into **soundness, and specifically into `POFree`**. Concretely:

* `pruneSig` is a very weak condition — per-demand existence of a target, with
  no joint-realisability requirement across a signature's several demands. That
  weakness is exactly what makes it monotone, and it is why
  `coneScheme_complete` needs nothing but "a model realises its own signatures".
  One attempt is the honest cost of a one-line condition.
* All the weight lands on `coneScheme_sound`, and it is paid by the
  fresh-occurrence unfolding: because every demand gets its *own* fresh child,
  no joint constraint is ever needed — and the price is that all the
  cross-relations between different children come out as the **residual `PO`**.
  Those `PO` edges are composition-legal for free (`PO` is in every cell of the
  `PO` row and column), but they would carry label obligations if `∀PO` existed.
  It doesn't. That is the single `∀PO` case in `unf_truth` (:43937), discharged
  by `pofree_cl_all`.

So the difficulty did not vanish; it was pushed into the fragment restriction.
That is a legitimate architecture, and the file's §284 docstring says so
correctly — but see §4.1.

**A witness that this is real, not rhetorical.** Both halves kernel-checked here
on `[propext]`:

```lean
CPOfree = ∃PPI.(∃PP.A₀) ⊓ ∀PP.¬A₀ ⊓ ∀PPI.¬A₀ ⊓ ¬A₀              -- SATISFIABLE
CPO     = CPOfree ⊓ ∀PO.¬A₀                                       -- UNSATISFIABLE
```

`CPOfree` is satisfied by the 3-point model `y={1} ⊂ x={1,2}`, `y ⊂ z={1,3}`,
`x PO z`, `A₀` at `z` only. `CPO` is unsatisfiable because
`rho x z ∈ comp ppi pp = [eq,pp,ppi,po]` and all four are killed (`eq` by
`eq_id` + `¬A₀` at `x`, the other three by the three universals).

And the control layer **accepts `CPO`**: a three-signature set
`q_x = (T_x, {T_y})`, `q_y = ({∃PP.A₀, ¬A₀}, ∅)`, `q_z = ({A₀}, {T_y})` passes
`sigOkB` and is closed under `pruneSig` (checked against the shipped
transcription), so by `gfp_greatest` it sits inside the greatest fixed point and
carries `CPO`. Consequences, both worth recording:

1. dropping `hpo` from `coneScheme_sound` would make it **false**, with this
   concept as the countermodel — the hypothesis is exactly load-bearing;
2. `coneScheme_unsat_full` is not merely "one-sided in principle": here is a
   concrete, small, genuinely unsatisfiable concept it provably cannot refute.
   That is a fair thing to state next to the Π⁰₁ remark in §287.

---

## 4. Findings

### 4.1 DEFECT (documentation, but it inverts the architecture) — lines 366 and 1137–1140

> `/-! ### The fragment predicate` … *"Soundness above is fragment-agnostic (the
> checker verifies ALL universals on all edge classes). `POFree` is where the
> fragment enters: the COMPLETENESS side (round D) …"*

and line 366, *"…the completeness extraction …, which is where `POFree` does its
work."*

For the shipped route this is **exactly inverted**: `coneScheme_complete`
(:42272) takes no `POFree` at all, and `coneScheme_sound` (:44024) requires it.
The file contradicts itself — §284 and §287 state it correctly. This is
Round-A/Round-D-era prose that survived the pivot, and it has already propagated:
`COLD_PROMPT.md`'s own claim table lists `coneScheme_sound` without the
hypothesis. Fix the two comments; they are the ones a reader will hit first.

### 4.2 GAP (understated scope) — the complexity limit is not "no proved bound"

The recorded limit is *"there is no proved closed complexity bound"*. That reads
as an open question. It is not: the definition carries a **proved lower bound**
on its own work, and it is triple-exponential.

With `n = |cl C₀|`:
`typeEnum C₀ = allListsLe (cl C₀) n` (:11703) is **all lists** over `cl C₀` of
length ≤ n, so `|typeEnum C₀| = Σ_{k≤n} n^k ≈ n^n`; and
`keyEnum C₀ = typeEnum × sublists typeEnum` (:41210), so
`|sigStatic C₀| ≤ |typeEnum| · 2^|typeEnum|`. Measured:

| `C₀` | `n` | `|typeEnum|` | `|keyEnum|` |
|---|---|---|---|
| `⊤` | 1 | 2 | 8 |
| `∃PP.⊤` | 2 | 7 | 896 |
| any 3-node concept | 3 | 40 | 40·2⁴⁰ ≈ 4·10¹³ |
| `Cinf` (the file's own showcase) | 6 | 55 987 | 55 987 · 2^55987 |

Empirically: the *compiled* procedure runs at `n ≤ 2` (~30 s per call) and cannot
be started at `n ≥ 3` — `sigStatic` cannot be materialised, so even
`(sigStatic C₀).length`, which the named round needs, is uncomputable in
practice. **`decidableSat_cone` cannot be evaluated on `Cinf`, `Cboth`, `CB`,
`CPOfree`, or any other concept the paper discusses.** I would say so in the
scope note, in those words.

The *kernel* is a step behind the compiler again: `decide (Satisfiable ⊤) = true`
closes by `rfl` in under a second, but the same `rfl` for `∃PP.⊤` (`n = 2`,
`|keyEnum| = 896`) ran 27 minutes to 13.3 GB resident and was OOM-killed. So
`decide`-style *proofs* through the capstone are available only at `n ≤ 1`; at
`n = 2` you get answers from `#eval` but cannot turn them into theorems.

A cheap and safe improvement, using material already in the file: every model
type is `mty C₀ I x = (cl C₀).filter …`, a *sublist* of `cl C₀`, and
`filter_mem_sublists` (:4214) is already proved. So `typeEnum` can be
`sublists (cl C₀)` — 2ⁿ instead of ≈ nⁿ — with `mty_mem_typeEnum` becoming a
one-liner. For `Cinf` that is 64 instead of 55 987, i.e. `|keyEnum|` drops from
`2^55987` to `≈ 2^64`. Still doubly exponential and still unrunnable, but it
removes an entire exponential that buys nothing. (It touches every
`typeEnum`-based pigeonhole bound, which only gets better.)

### 4.3 GAP that is smaller than recorded — the "abstract composition-table semantics"

Recorded as a limit: *"the semantics is the abstract composition-table one."*
For the **soundness** direction that gap is already closed by material in this
archive, and nobody seems to have noticed.

Every model `coneScheme_sound` produces is `odNet` of an `ODStruct`. And
`RCC5NormalForm.lean`'s `eta` (`eta x = {p : ¬disj p.1 p.2 ∧ (p.1 ≤ x ∨ p.2 ≤ x)}`)
realises *any* ordered-disjoint structure as a family of non-empty sets under
literal set-`RCC5`, with no finiteness assumption: `sub_iff_le` gives `PP`,
`disj_iff_eta_disjoint` gives `DR`, `eta_injective` gives strong EQ, and `PO`
follows by residue. So the models this artifact builds are genuinely
set-realisable, and since real models are also abstract models, the
characterisation transfers: for `∀PO`-free `C₀`,
`Satisfiable_abstract C₀ ↔ Satisfiable_set C₀`. Wiring `eta` in (it is ~40 lines
already proved, in a file that is currently not imported anywhere) would let the
scope note be deleted rather than repeated.

Two stale headers to fix while you are there:
`RCC5NormalForm.lean` says the converse — ordered-disjoint ⟹ RCC5-closed — is
*"exhaustively machine-checked by wp47 up to n=4 and is a natural follow-up"*,
but `POFreeLift.odNet_frame` (:20140) proves it for arbitrary carriers.
And `POFreeLift.lean:9` calls `cinf_satisfiable` *"the no-finite-model witness"*
while `cinf_satisfiable` (:1337) is only `Satisfiable Cinf`; nothing in the file
proves `Cinf` has no finite model. (It doesn't — `∀PP.∃PP.⊤` propagates up a
`comp pp pp = [pp]` chain — but that is a comment-level overclaim as written.)

### 4.4 Worth stating: what `∀PO`-free costs in expressivity

Because the five atoms are JEPD and finite, role unions are definable by
distributing `⊔`/`⊓`. So the fragment is not "no `∀PO`" but **"no `∀` over any
role set containing PO"**. `∀P.C` (part-of), `∀Pi.C`, `∀DR.C` survive; `∀O.C`
("everything I overlap") and `∀¬DR.C` do not. That is a sharper and more honest
statement of the boundary than "`∀PO`-free", and it is the boundary §3.4's
witness sits on.

### 4.5 Minor

`wp134_cone_scheme_prune.py`'s `po_free()` raises `IndexError` on `("bot",)` —
it falls through to `po_free(c[2])`. None of its own cases use `⊥`, so the
shipped run is unaffected, but it bites the first person who extends the probe
(it bit me).

---

## 5. What I checked and could not break

Since every step is kernel-checked, a wrong answer can only come from a wrong
definition, so I spent the effort on the trusted base and on execution:

* the full 25-cell composition table, re-derived from set semantics at three
  domain sizes — exact match;
* `conv`, `Concept`, `Interp`, `sat`, `RCC5Interp`, `Satisfiable`, `POFree`,
  read line by line, plus `cl`'s transitive closedness and `pofree_cl_all`;
* the ODStruct → RCC5 frame argument re-derived by hand, all sixteen cases;
* the cone invariant (`compatB pp/ppi` + `sigOkB` ⟹ every strictly-lower type is
  in `S`) re-derived in both directions, and the model-side `dkey_compat`
  conditions checked against the forced closure;
* the `PO`-birth residuality argument (`vbase` length count) re-derived;
* `decidableSat_cone` evaluated — compiled (15 concepts) and at the **kernel**
  (`⊤`, `⊥`), which is what rules out a classical instance;
* 4 000 random `∀PO`-free concepts, uncapped control layer vs. exhaustive
  finite-model search — no disagreement in either direction;
* two independent hand proofs in Lean (`¬ Satisfiable CB` from `comp_`/`conv_`;
  `Satisfiable CPOfree` from an explicit 3-point model) plus the `CPO` boundary
  witness;
* the shipped Python probe re-run, and its `dr_wall` argument checked for
  cap-independence on `U1` (it is: `T_x ∈ S(q_y)` is forced by `compatB ppi`).

What I did **not** do, and where residual risk sits: I did not re-verify the
44 000 lines of proof (the kernel did that), and I did not exercise the
procedure above `|cl C₀| = 2`, because it cannot be exercised there (§4.2). If
something is still wrong, it is not in the statement of `decidableSat_cone` and
it is not reachable by running it.
