# Attack request — a claimed decision procedure for the ∀PO-free fragment

**This packet contains the Lean source.** Round 2's report noted that our
certification claims could not be rebuilt because we shipped none; that is fixed.
Everything below is checkable by `lean lean/POFreeLift.lean` (Lean 4.32.0 core,
**no mathlib**, ~4 minutes).

## 0. What is claimed, exactly

```lean
def decidableSat_cone (C0 : Concept) (hpo : POFree C0) : Decidable (Satisfiable C0)
```

`Satisfiable` is carrier-polymorphic — `∃ α, ∃ I : Interp α, RCC5Interp I ∧ ∃ x,
I.dom x ∧ sat I x C0` — over arbitrary domains, with abstract composition-table
semantics and strong EQ. `POFree C0` says no `∀PO` occurs in the positive
closure. **`hpo` is the only hypothesis.** There is no unproved premise, no
oracle, no appeal to a model.

The route: signatures `(type, lower-type-spectrum)` form a finite static set; a
**monotone, reductive** `prune` eliminates signatures whose demands lose their
targets; the greatest fixed point is reached within `|sigStatic C₀|` rounds; and
a surviving signature carrying `C₀` is unfolded into a model by giving every
non-EQ demand a FRESH occurrence (nothing is ever reused).

**Scope: this covers the WHOLE fragment, mixed quadrant included** — the case
that was open, and that your two previous reports attacked. Nothing in the
construction is quadrant-restricted.

## 1. Why we are asking you to attack rather than confirm

This landed in one working session, immediately after a period in which four
successive extraction disciplines were refuted (two by you) and a paper that had
survived four rounds of adversarial review turned out to contain a real gap. The
project ledger records a defect or overclaim in all but two of seventeen reviews.

A result arriving this cleanly on a problem open since 2002 deserves suspicion,
and we would rather you find the defect than we announce one that isn't there.

## 2. Where we think it is most likely wrong

Ranked by our own suspicion, highest first.

**A. ADEQUACY — do the statements mean what we think?** The mathematics can be
right while the formalization is not about ALCI_RCC5. Specifically worth
checking:
  - `sat`, `Interp`, `RCC5Interp`, `Satisfiable` (all near the top of the file);
    is `sat`'s `∀`/`∃` clause right, is strong EQ really identity, is the
    composition table the RCC5 one;
  - `POFree` — does it exclude exactly `∀PO`, in the right (positive) closure?
  - `cl` — is the closure the right one (does it include what the type system
    needs)?
  - is `Decidable` here genuine, or does it secretly carry proof data that makes
    it non-executable? (`decidableSat_cone` is a plain `def`, not
    `noncomputable`; we believe the algorithm is a `List` fold, and
    `Classical.choice` enters only through the erased correctness proof.)
  This is the class of finding your 14th-review predecessor made against the old
  artifact, and it is the one we can least self-check.

**B. IS `prune` TOO WEAK?** Soundness is proved (`coneScheme_sound` builds a
model), so a weakness here would have to be a defect in that proof rather than a
counterexample. But the balance is delicate and worth probing: `prune` must stay
MONOTONE (or completeness dies — this is exactly how this project's FIRST
type-elimination route died, its `(Q3)` being anti-monotone) and be STRONG enough
that survivors are realizable. `wp134` (included) checks it rejects the standing
forced-composition UNSAT diagnostics; that is evidence, not proof.

**C. THE UNFOLDING'S GEOMETRY.** `unfOD`/`gOD` claim the fresh-occurrence
unfolding is an ordered-disjoint structure, hence (via `odNet_frame`) a
composition-closed RCC5 network. The load-bearing invariant is the VERTICAL BASE
(§276): order edges preserve it, `DR` births change it. `ltNotDj` — the clause
your round-2 D2 used to kill the previous architecture — is claimed to be
structural here. If that invariant has a hole, the frame is not a frame.

**D. COMPLETENESS.** `modelSigs_survives` (§273) claims a model's own signatures
survive their own elimination, because the model supplies each witness. It went
through in one attempt, which we read as the architecture having MOVED the
difficulty rather than beaten it — the finite object is now the signature set,
finite by construction, and nothing is extracted. Check whether something was
lost in that move.

**E. VACUITY.** Is any of it empty? Does `sigStatic C₀` contain anything? Can
`gfpIter` return everything (prune never firing) or nothing? Are there generated
occurrences beyond the root?

## 3. What would count

A concrete `∀PO`-free `C₀` where the procedure gives the wrong answer, with the
model or the impossibility argument. Or a Lean-level defect: a statement that
does not mean what §0 says, a definition that is degenerate, a proof that uses a
hypothesis vacuously. Or "I could not break it, and here is what I checked" —
which after this project's history is genuinely informative.

## 4. Contents

```
lean/POFreeLift.lean        the artifact (44,375 lines, 0 sorries/warnings)
lean/RCC5NormalForm.lean    the ordered-disjoint normal form, separately certified
design/DESIGN_266_286.md    the construction's design log, §§266-286
probes/wp134_*.py           does `prune` reject the UNSAT diagnostics?
probes/wp133_*.py           does the unfolding produce a valid frame?
VERIFY.md                   how to rebuild and what to check
```

## 5. Scope honesty

The artifact is **unreviewed**. Everything above is machine-checked in the sense
that Lean accepts it with zero sorries and zero axioms beyond `propext`,
`Quot.sound` and `Classical.choice` — and that is exactly the thing that does not
protect against A. Decidability of FULL ALCI_RCC5 is a separate, older open
problem and is not claimed here.
