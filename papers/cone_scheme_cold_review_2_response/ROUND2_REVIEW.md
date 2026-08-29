# Cold review #2 — the completeness half, and `coneScheme_unsat_full`

**Verdict: both theorems are correct. `coneScheme_complete` is complete and
takes no fragment hypothesis; `coneScheme_unsat_full` is a sound full-logic
UNSAT test. I found no counterexample to either, and I do not think one exists.**

**The defect is in `compatB`, and it is an under-strength definition, not an
error.** `compatB` drops a `∀PO` propagation that is valid at every model edge.
Restoring it is one clause, keeps completeness *and* soundness, and strictly
increases what the full-logic test can refute. §4 proves all four of those in
the kernel, in your file.

**And the honest statement of §287's strength is stronger than "blind to `∀PO`":**
on 3 000 measured instances the shipped test's verdict is *invariant* under
replacing every `∀PO.D` by `⊤`. The erasure is always `POFree`. So as shipped,
the full-logic bonus theorem refutes **nothing** that `coneScheme_correct`
does not already refute on a syntactic weakening of the same concept. That is
the plain statement §4 of the prompt asked for. With the missing clause
restored, that barrier is provably crossed (§4.6).

Everything I ran is reproducible: `ROUND2_ADDENDUM.lean` (append to
`POFreeLift.lean`, 34 s, exit 0) and the probes described in §6.

---

## 1. The build, and §4's measurements

```
~/.elan/bin/lean POFreeLift.lean   → exit 0, 34 s wall, Lean 4.33.1
                                     891 #print axioms lines, and NOTHING else
                                     on stdout: 0 errors, 0 warnings, 0 sorry
```

Static audit agrees with round 1: no `axiom`, `sorry`, `native_decide`,
`set_option`, `implemented_by`, `unsafe`, `partial`, `macro`/`elab`. Axiom
footprints partition into `[propext, Classical.choice, Quot.sound]` (625),
`[propext, Quot.sound]` (106), `[propext]` (78), `[Classical.choice]` (3),
`[Quot.sound]` (2), `[propext, Classical.choice]` (1). Both capstones report the
standard three. (BUILD.md pins 4.32.0; 4.33.1 also builds clean, as round 1 said.)

`python3 wp135_cone_completeness_attack.py` reproduces §4's table **exactly** —
2 415 / 2 431 instances, 12.4 % containing `∀PO`, mutations breaking 908 / 960 /
701 / 986 of 1 443, and PP 44.9 % / PPI 40.5 % / DR 1.9 % / **PO 0.0 %**.
Verified, not redone.

---

## 2. Phase 1 — the prompt's five questions

**§3.1 Is `coneScheme_unsat_full` really full-logic? — Yes. No leak.**
I read every definition the statement transitively depends on: `cl` (:2944),
`typeEnum = sublists (cl C₀)` (:11737), `sublists` (:4222), `keyEnum` (:41241),
`appendNew` (:39051, a dedup that loses nothing — `appendNew_covers`),
`supportB` (:41899), `sigOkB` (:41911), `sigStatic` (:41918), `compatB` (:41943),
`sigDemands` (:41954), `pruneSig` (:41968), `gfpIter` (:41775). None mentions
`POFree`, `pofreeB`, or `po` in a restricting position. The risky direction —
`sigStatic` being *too small*, so a real model's key falls outside it and the
test rejects a satisfiable concept — is closed by `dkey_mem_keyEnum` +
`dkey_sigOk` + `mem_sigStatic`, and none of those three mentions the fragment
either. The claim is genuinely full-language.

**§3.2 Is `modelSigs_survives` complete? — Yes.** `sigDemands q` emits exactly
the non-`EQ` existentials of `q.1` (`mem_sigDemands` / `mem_sigDemands_mk` are
an iff in the pieces that matter), and each is discharged by `mty_ex` + the
model's own witness. Dropping `∃EQ` is correct and is *not* a hole: `eq_id`
forces the `EQ`-witness to be `x` itself, so `supportB`'s `ex eq D → D ∈ T`
clause (proved for a real type by `supportB_mty` via `sat_of_ex_eq`) is the
whole obligation. `∀EQ` is the same via `refl_eq`. Nothing is dropped.

**§3.3 Is `dkey_compat` right at every relation? — Yes, and I checked the
arithmetic against `comp`.** With `x r y`, `u ∈ cone(x)` (`u = x` or `u PP x`),
`v ∈ cone(y)`, the composition table forces a *single* value in exactly these
cells (✓ = the artifact captures it):

| `r` | `(x,y)` | `(u,y)` | `(x,v)` | `(u,v)` |
|---|---|---|---|---|
| `PP` | `PP` ✓ | `comp(pp,pp)={PP}` ✓ | `comp(pp,ppi)` = all — | all — |
| `PPI` | `PPI` ✓ | mirror ✓ | — | — |
| `DR` | `DR` ✓ | `comp(pp,dr)={DR}` ✓ | `comp(dr,ppi)={DR}` ✓ | `{DR}` ✓ |
| `PO` | `PO` **✗ dropped** | `comp(pp,po)={PP,PO,DR}` — | `comp(po,ppi)={PPI,PO,DR}` — | — |

`PP`/`PPI` are captured indirectly (`compatB` puts `cone(q)` into `q'.2`, then
`sigOkB q'` — available because `q' ∈ X ⊆ sigStatic` — moves `∀PP` bodies up and
`∀PPI` bodies down). `DR` is captured directly, cone × cone, and is *maximal*.
`PO` is captured **not at all**: a `PO` edge puts nothing in any cone, and
`compatB`'s `PO` clause is literally `true`. That single ✗ is §3.

**§3.4 Is anything vacuous? — No, but one case is worse than round 1's.**
`modelSigs` is never empty for a satisfiable concept (`mem_modelSigs` at the
witness). `sigStatic` is never empty. The elimination genuinely fires: I ran the
full fixpoint on ~6 000 concepts, and it rejects `∃PP.⊤ ⊓ ∀PP.⊥`,
`∃PPI.⊤ ⊓ ∀PPI.⊥`, `∃DR.⊤ ⊓ ∀DR.⊥`, `∃r.⊥`, `⊥`, and every literal clash.
**But on `∃PO.⊤ ⊓ ∀PO.⊥` the elimination is a total no-op**: `|sigStatic| =
|gfp| = 10 240`, not one signature removed, at any round. That is §3.

**§3.5 The best outcomes.** I have an unsatisfiable concept the procedure
accepts (§3). It does **not** refute soundness — `coneScheme_sound` takes
`POFree` and my concept has `∀PO` — and it does not refute
`coneScheme_unsat_full`, which is one-sided. It refutes the *significance*
claim in §287's prose.

---

## 3. THE FINDING — `compatB`'s `PO` clause drops a sound constraint

`compatB` (:41943):

```lean
   | Atom.po => true
   | Atom.eq => true)
```

and `dkey_compat`'s docstring (:42156): *"`PO` and `EQ` impose nothing."*

**`EQ` imposes nothing. `PO` does.** `conv PO = PO`, so a `PO` edge is symmetric,
and `mty_all` applies in both directions:

* `x PO y` and `∀PO.E ∈ mty x` ⟹ `E ∈ mty y` (`mty_all _ hy hr`);
* `y PO x` and `∀PO.E ∈ mty y` ⟹ `E ∈ mty x` (`mty_all _ hx hyx`, `hyx` from `conv_`).

This is the same one-line argument the `DR` case already makes, minus the cones
(which are not forced at `PO` — see the table in §2.3). The missing clause is:

```lean
   | Atom.po => subB (allBodies po q.1) q'.1 && subB (allBodies po q'.1) q.1
```

**The consequence, measured.** Take the four minimal probes `∃r.⊤ ⊓ ∀r.⊥`, each
unsatisfiable for the same one-line reason. Running the actual fixpoint:

| `C₀` | UNSAT | shipped `pruneSig` | with the `PO` clause |
|---|---|---|---|
| `∃PP.⊤ ⊓ ∀PP.⊥` | yes | **REJECT** | REJECT |
| `∃PPI.⊤ ⊓ ∀PPI.⊥` | yes | **REJECT** | REJECT |
| `∃DR.⊤ ⊓ ∀DR.⊥` | yes | **REJECT** | REJECT |
| `∃PO.⊤ ⊓ ∀PO.⊥` | yes | **ACCEPT** — `gfp` = all 10 240 signatures | **REJECT**, round 1 |

`PO` is the only one of the four that gets through, and it gets through because
of the dropped clause, not because of anything about `PO`.

**Your own probe says the clause is sound.** I added it to `wp135`'s Part C as a
fifth mutation, changing nothing else:

```
    strengthen PP  cone equality     :   908 / 1443   breaks completeness
    strengthen PPI cone equality     :   960 / 1443   breaks completeness
    strengthen DR  cone equality     :   701 / 1443   breaks completeness
    strengthen server dominates type :   986 / 1443   breaks completeness
    strengthen PO forall-propagation :     0 / 1443   <-- valid, not over-strong
```

and Part D's `PO` row moves `0/526 = 0.0 %` → `8/526 = 1.5 %`.

Part C prints `NO EFFECT -- test is weak` for that row. **That label is
miscalibrated, and it is why your probe could not find this.** Part C's four
mutations are all *semantically invalid* strengthenings, so the control can only
ever demonstrate that the obligations detect **over**-strength. It contains no
sound-but-stronger member, so it is structurally incapable of detecting
**under**-strength — which is the failure mode `compatB` actually has. A "0
breakages" row in Part C is the signature of a *correct* strengthening, i.e. of
a missed constraint; it should be read as a finding, not as a weak test.

---

## 4. The finding, kernel-checked — `ROUND2_ADDENDUM.lean`

280 lines, appended verbatim to `POFreeLift.lean`; `lean` exits 0 in 34 s with
zero errors, warnings or `sorry`, and every new declaration lands on the
artifact's own axiom base.

| theorem | statement | axioms |
|---|---|---|
| `cpo_unsat` | `¬ Satisfiable (∃PO.⊤ ⊓ ∀PO.⊥)` | *none* |
| `cpo_not_pofree` | it is outside `coneScheme_correct`'s fragment | *none* |
| `cpo_never_refuted (n)` | `∃ q ∈ gfpIter pruneSig (sigStatic Cpo) n, Cpo ∈ q.1` — **at every `n`** | propext, Quot.sound |
| `dkey_compat'` | the strengthened relation still holds at every real model edge | the standard three |
| `coneScheme_complete'` | completeness, verbatim, for `pruneSig'` | the standard three |
| `coneScheme_unsat_full'` | the full-logic UNSAT test, verbatim, for `pruneSig'` | the standard three |
| `pruneSig'_sub_pruneSig`, `coneScheme_sound'` | a `pruneSig'`-fixed point is a `pruneSig`-fixed point, so **soundness and the fragment decision procedure survive unchanged** | the standard three |
| `cpo_refuted_at_one` | `∀ q ∈ gfpIter pruneSig' (sigStatic Cpo) 1, Cpo ∉ q.1` | propext, Quot.sound |
| `erase_cpo_satisfiable` | `Satisfiable (∃PO.⊤ ⊓ ⊤)`, in a 2-point all-`PO` model | propext |

Three things are worth pulling out.

**`cpo_never_refuted` is not a "the test happens to be silent" observation — it
is a proof that the test can never fire on this concept.** The witness is
`Qpo = ([Cpo, ∃PO.⊤, ⊤, ∀PO.⊥], [])`, which is in `sigStatic Cpo`, serves its own
`∃PO.⊤` demand *from itself* (`compatB po ⊤ Qpo Qpo = Qpo.1.contains ⊤ = true`),
and therefore sits inside the greatest fixed point by `gfp_greatest` at every
round. So `coneScheme_unsat_full`'s hypothesis is unreachable for `Cpo`: sound,
and permanently vacuous here.

**`cpo_refuted_at_one` enumerates nothing.** Any signature carrying `Cpo` carries
both conjuncts (`supportB_sound`'s `∧` clause), so it has demand `(PO, ⊤)`; the
strengthened clause forces `⊥ ∈ q'.1` for any target; no support type contains
`⊥`. One round, no search. The doubly-exponential `sigStatic` never has to be
touched.

**`coneScheme_sound'` is the part that makes this a repair rather than a
trade-off.** Strengthening `compatB` shrinks the fixed point, and
`coneScheme_sound` *consumes* fixed-point membership, so it applies verbatim.
The clause costs nothing anywhere.

---

## 5. How strong `coneScheme_unsat_full` actually is

You asked for a second opinion on Part D and for the position to be said
plainly. Part D's reading — *sound but blind to `∀PO`* — is **correct about the
shipped code**, and the sharper form is:

> **Measured: on 3 000 `∀PO`-containing concepts, the shipped test's verdict is
> identical on `C₀` and on `C₀` with every `∀PO.D` replaced by `⊤`. 3 000 / 3 000.**

That erasure is always `POFree`, and `C₀ ⊨ erase(C₀)` (NNF has no negation, so
every position is positive and `⊤` is a weakening) — so `erase(C₀)` unsat ⟹ `C₀`
unsat, provably. Combining with `coneScheme_correct`, the shipped full-logic
test appears to be **exactly** the fragment decision procedure run on
`erase(C₀)`: it adds no refutation power at all beyond the fragment. I did not
prove the invariance — it is a measurement over concepts with `|cl C₀| ≤ 7` — so
state it as such, but I would state it, because it is what "blind to `∀PO`"
actually amounts to.

Two things follow for §287's prose.

1. *"this is a concrete, kernel-checked refutation certificate"* for the open
   problem is the sentence to soften. As shipped it certifies no refutation that
   the fragment procedure does not already certify. `compatB'` changes that:
   `cpo_refuted_at_one` + `erase_cpo_satisfiable` are a kernel-checked pair
   showing the strengthened test refuting a concept whose erasure is
   satisfiable — the erasure barrier, provably crossed.
2. *"the project's Π⁰₁ observation says UNSAT is r.e., and this is a … certificate
   for it"* conflates two things. A decidable **sufficient** condition for UNSAT
   is a decidable under-approximation; it is not what witnesses r.e.-ness, and it
   does not become one by being kernel-checked. The theorem is fine; the sentence
   claims more than the theorem.

**There is a second `∀PO` gap, and it is not fixable this way.** Round 1's `CPO`
(§3.4 there) is unsatisfiable because `rho x z ∈ comp(ppi,pp) = {EQ,PP,PPI,PO}`
and all four are killed — a `PO` obligation arising from a *non-singleton*
composition, on a pair the control graph never declares. `CPO` contains no `∃PO`
subformula at all (checked: `|cl CPO| = 11`, no `ex PO` in the closure), so
`sigDemands` never emits a `PO` pair and `compatB'` leaves it exactly where it
was. The two gaps are independent: mine is a dropped clause and closes in one
line; round 1's is structural — the scheme only ever exploits compositions that
are forced to a **singleton**, and no local clause of this shape reaches
disjunctive entailments. Say both, and say which is which.

---

## 6. What I ran, and what I could not break

An independent re-implementation of `cl` / `sublists` / `typeEnum` / `supportB` /
`sigOkB` / `sigStatic` / `sigDemands` / `compatB` / `pruneSig` / `gfpIter`, plus
an `RCC5Interp` model enumerator built from the four axioms directly. Unlike
`wp135` this **runs the certificate**, not just its model-side obligations. A
bitmask fixpoint was cross-validated against a literal line-by-line
transcription of `pruneSig`: 40 concepts × 2 variants, **0 mismatches**.

* **6 268 concepts driven through the full fixpoint** (`|cl C₀| ≤ 8`,
  `|sigStatic|` up to 106 496), against exhaustive finite-model search:
  **0 satisfiable concepts rejected**, by the shipped operator or by either
  strengthening. Completeness is not just kernel-checked, it is exercised.
* **3 849 instances of the three model-side obligations over abstract
  `RCC5Interp` frames** (`wp135` draws only set models): **0 failures**.
  Reassuring for `wp135`: at `n ≤ 4` the two model classes coincide exactly —
  41/41 abstract frames at `n = 3` and 916/916 at `n = 4` are set-representable
  (universe of 6) — so its set-model restriction costs nothing at the sizes it
  explores.
* A second candidate strengthening — requiring each `U ∈ q.2` to be *realised*
  by some `q'' ∈ X` with `q''.1 = U` and `cone(q'') ⊆ q.2`, which is monotone and
  which the model supplies — is also sound (0/3 849 breakages) but **adds nothing**
  (0 extra refutations in 2 500 concepts). Worth recording as checked-and-not-needed:
  the `PO` clause is the only gap in `compatB` that pays.
* Fixpoint rounds: **max 4, mean 1.19**, against Lean's `(sigStatic C₀).length`
  bound. `gfpIter_stabilizes` already licenses "iterate until stable"; the named
  round in `decidableSat_cone` is what makes the shipped instance quadratic in a
  doubly-exponential quantity for no reason.

**`wp135` itself (in scope).** Its transcription of `supportB`, `sigOkB`,
`sigCone`, `sigDemands`, `compatB`, `pruneSig`, `dspec`, `dkey` matches the Lean
clause for clause; the frozenset-for-list representation is faithful because
every operation is membership-based; its check (iii) is *stronger* than
`dkey_compat` (it quantifies over all of `mty y`, not just demanded bodies); and
round 1's `po_free` crash on `("bot",)` is fixed here. Two notes: the concept
grammar has no `⊤`, and Part C is one-sided (§3).

---

## 7. Findings

1. **DEFECT (under-strength definition), `compatB` :41950 and its docstring
   :42156.** The `PO` clause drops `∀PO` propagation, which is sound at every
   model edge and is the only such omission in `compatB`. Fix is one clause;
   `ROUND2_ADDENDUM.lean` proves the fix keeps completeness (`dkey_compat'`,
   `coneScheme_complete'`), keeps soundness (`coneScheme_sound'`), and strictly
   increases refutation power (`cpo_refuted_at_one` vs `cpo_never_refuted`).
   Delete *"`PO` and `EQ` impose nothing"* — `EQ` imposes nothing; `PO` does.

2. **OVERCLAIM (prose), §287.** *"a concrete, kernel-checked refutation
   certificate"* for an open problem: as shipped the test refutes nothing the
   fragment procedure does not already refute on the `∀PO`-erasure (3 000/3 000
   measured). Also, a decidable sufficient condition is not a witness of
   r.e.-ness. Both sentences should be qualified; both become defensible once
   the `PO` clause is restored.

3. **PROBE DEFECT, `wp135` Part C.** All four controls are semantically invalid
   strengthenings, so the probe can detect over-strength and structurally cannot
   detect under-strength. Add at least one sound-but-stronger control; a `0 /
   1443` row means *valid constraint found*, not *test is weak*, and the printed
   label says the opposite.

4. **Round 1's §3.2 is wrong on one word** (`ROUND1_REVIEW.md`:232). *"the `compatB` conditions are
   exactly the forced closure, neither weaker nor stronger"* — they are weaker,
   at `PO`, and that sentence is probably why the gap survived a review.

5. **Refinement of known limit #2 (not a new finding).** `sigStatic` is defined
   as a *filter of* `keyEnum`, so evaluating it materialises
   `2^|cl| · 2^(2^|cl|)` pairs. Generating the admissible signatures directly —
   `T` over support types, `S` over the vertically-compatible ones — gives the
   same set exponentially cheaper (median `|sigStatic|`: 384 at `|cl| = 3`,
   10 240 at 4, 4.7 · 10⁶ at 5). That moves the practical ceiling from
   `|cl C₀| ≤ 2` to about 4–5; it does **not** remove the double exponential
   (median 1.3 · 10¹³ at `|cl| = 7`), so the limit as stated stands.

Nothing here touches the correctness of `coneScheme_complete`,
`coneScheme_unsat_full`, `coneScheme_correct_at` or `decidableSat_cone`. I
attacked completeness from the model side, the syntax side, and by running the
certificate, and it held every time.
