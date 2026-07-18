/-
  SemiDecidability.lean                              (2026-07-17, DRAFT —
                                                      not yet in the repo)

  THE OBSERVATION (new to the project record; nothing in papers/, the
  review ledger, or the status docs discusses semi-decidability or the
  arithmetical level of the problem):

  Concept satisfiability of ALCI_RCC5 under abstract composition-table
  semantics is Π⁰₁ — its complement is recursively enumerable. The model
  class is finitely first-order axiomatizable: five binary predicates
  with (i) exactly-one-atom on each pair of distinct elements,
  (ii) EQ = identity (strong EQ), (iii) converse coherence, and
  (iv) composition-table closure — all universal FO sentences over a
  finite table — and ALCI embeds by the standard translation, over
  arbitrary carriers (matching the round-27 carrier-polymorphic
  `Satisfiable`). So `Satisfiable C` iff the FO theory
  T_RCC5 ∪ {∃x. ST_C(x)} has a model, and by GÖDEL COMPLETENESS its
  unsatisfiability is r.e. (enumerate FO proofs).

  CONSEQUENCE. Decidability ⟺ the SAT side is also r.e. ⟺ every
  satisfiable concept admits SOME finite certificate — with NO computable
  bound demanded. Dovetail the certificate enumeration (its checker
  `finAcceptB` and soundness `finAccept_sound` are already kernel-checked
  in Round19Transport.lean) against an FO-refutation enumeration; one
  side must terminate. The keystone F6 accordingly WEAKENS from

      "live width bounded by a COMPUTABLE FUNCTION of the concept,
       with K(C₀) budget accounting"                       (quantitative)
  to
      "every satisfiable concept has SOME model of finite live width
       / some finite passing certificate"                  (qualitative),

  and the quantitative form is recovered FOR FREE a posteriori
  (`quantitative_free` below). The entire genus of width-budget
  accounting that produced several review findings (the round-13 §8
  recurrence, the 9th review's F3, F4's budgets, W3's cascades, the 14th
  review's "bounded by a computable function of C₀") is thereby retired
  FROM THE DECIDABILITY QUESTION — it remains relevant only to
  complexity bounds.

  THIS FILE is the dovetailing schema, in the ForcingReduction.lean
  style: Concept and Sat are PARAMETERS; the four mathematical inputs are
  HYPOTHESIS FIELDS, visible in the statement, never axiomatized:

    cert_sound     — the checker accepts only satisfiable concepts
                     (ALREADY CERTIFIED for the project's `finAcceptB`);
    ref_sound      — refutations refute (FO soundness; routine);
    cert_complete  — THE QUALITATIVE KEYSTONE (F6/W2′ minus budgets);
    ref_complete   — Gödel completeness (standard, external — same
                     ledger status as patchwork and Vardi emptiness).

  The decision program `decideB` is a genuinely executable unbounded
  search (Markov's principle realized by `Acc.rec`): the ONLY classical
  step is the excluded middle on `Sat C` inside the TERMINATION
  CERTIFICATE, which is a `Prop` and is erased by the compiler. The
  search core itself (`firstHit`/`firstHit_spec`) is axiom-clean
  (propext + Quot.sound only); `Classical.choice` enters exactly at
  `race_fires`, and `native_decide` (Lean.ofReduceBool) only in the
  standalone toy witnesses.

  Build (Lean 4 core, no mathlib):  lean SemiDecidability.lean
-/

namespace SemiDecidability

/-! ### Part 1: the Markov search

An unbounded search extracting a hit index from a bare Prop-level
existence proof. `Acc.rec` eliminates `Acc` into `Type` (small
elimination is special-cased for `Acc`), which is exactly the
constructive content of Markov's principle in type theory: the
existence proof certifies termination, the compiled code is a plain
loop. -/

/-- One upward search step, taken while `g` has not fired. -/
def SearchRel (g : Nat → Bool) (m n : Nat) : Prop := m = n + 1 ∧ g n = false

/-- The search loop, by recursion on the accessibility certificate. -/
def findLoop (g : Nat → Bool) {n : Nat} (a : Acc (SearchRel g) n) :
    { m // g m = true } :=
  a.rec (motive := fun _ _ => { m // g m = true })
    (fun k _ ih =>
      match hg : g k with
      | true  => ⟨k, hg⟩
      | false => ih (k + 1) ⟨rfl, hg⟩)

/-- `0` is accessible for the search as soon as SOME hit exists:
descending induction from the (Prop-level) witness. -/
theorem acc_zero (g : Nat → Bool) (h : ∃ n, g n = true) :
    Acc (SearchRel g) 0 := by
  obtain ⟨k, hk⟩ := h
  have aux : ∀ j n, n + j = k → Acc (SearchRel g) n := by
    intro j
    induction j with
    | zero =>
      intro n hn
      have hnk : n = k := by omega
      subst hnk
      exact Acc.intro n (fun m hm => absurd hk (by simp [hm.2]))
    | succ j ih =>
      intro n hn
      refine Acc.intro n (fun m hm => ?_)
      have hm1 : m = n + 1 := hm.1
      subst hm1
      exact ih (n + 1) (by omega)
  exact aux k 0 (by omega)

/-- First hit of `g`, computed by the loop. COMPUTABLE: the existence
proof participates only through `acc_zero`, a `Prop`, erased at
compile time. -/
def firstHit (g : Nat → Bool) (h : ∃ n, g n = true) : Nat :=
  (findLoop g (acc_zero g h)).1

theorem firstHit_spec (g : Nat → Bool) (h : ∃ n, g n = true) :
    g (firstHit g h) = true :=
  (findLoop g (acc_zero g h)).2

/-! ### Part 2: the dovetailing scheme -/

/-- The abstract data of the semi-decidability route. For ALCI_RCC5 the
intended reading is: `certB C n` decodes `n` as a finite certificate
code and runs the fixed non-oracular checker (`finAcceptB`); `refB C n`
checks whether `n` codes an FO proof of the unsatisfiability of
T_RCC5 ∪ {∃x. ST_C(x)}. The four fields are the four mathematical
inputs; NONE is axiomatized. -/
structure DovetailScheme where
  Concept : Type
  Sat : Concept → Prop
  /-- Certificate side: run the fixed Boolean checker on code `n`. -/
  certB : Concept → Nat → Bool
  /-- Refutation side: check candidate refutation `n`. -/
  refB : Concept → Nat → Bool
  /-- Checker soundness — for the project's `finAcceptB` this is
      `finAccept_sound`, ALREADY kernel-checked. -/
  cert_sound : ∀ C n, certB C n = true → Sat C
  /-- Refutation soundness — FO soundness; routine. -/
  ref_sound : ∀ C n, refB C n = true → ¬ Sat C
  /-- THE QUALITATIVE KEYSTONE (F6/W2′ stripped of budgets): every
      satisfiable concept has SOME passing certificate. No bound. -/
  cert_complete : ∀ C, Sat C → ∃ n, certB C n = true
  /-- The Gödel side: every unsatisfiable concept has a refutation.
      Standard external theorem (FO completeness). -/
  ref_complete : ∀ C, ¬ Sat C → ∃ n, refB C n = true

variable (S : DovetailScheme)

/-- The race: at index `n`, has either side fired? -/
def raceB (C : S.Concept) (n : Nat) : Bool := S.certB C n || S.refB C n

/-- The race terminates. THE ONE CLASSICAL STEP: excluded middle on
`Sat C` routes to one of the two completeness fields. A `Prop` — erased
at compile time, so the program below stays a plain loop. -/
theorem race_fires (C : S.Concept) : ∃ n, raceB S C n = true := by
  cases Classical.em (S.Sat C) with
  | inl hs =>
    obtain ⟨n, hn⟩ := S.cert_complete C hs
    exact ⟨n, by simp [raceB, hn]⟩
  | inr hu =>
    obtain ⟨n, hn⟩ := S.ref_complete C hu
    exact ⟨n, by simp [raceB, hn]⟩

/-- The winning index of the dovetailed run. -/
def raceIdx (C : S.Concept) : Nat := firstHit (raceB S C) (race_fires S C)

/-- THE DECISION PROGRAM: dovetail the two enumerations, answer with
the certificate side at the winning index. -/
def decideB (C : S.Concept) : Bool := S.certB C (raceIdx S C)

/-- Correctness: `decideB` answers `true` exactly on the satisfiable
concepts. -/
theorem decideB_correct (C : S.Concept) : decideB S C = true ↔ S.Sat C := by
  have hr : raceB S C (raceIdx S C) = true := firstHit_spec _ _
  constructor
  · intro h
    exact S.cert_sound C (raceIdx S C) h
  · intro hs
    cases hc : S.certB C (raceIdx S C) with
    | true  => exact hc
    | false =>
      have hf : S.refB C (raceIdx S C) = true := by
        simpa [raceB, hc] using hr
      exact absurd hs (S.ref_sound C (raceIdx S C) hf)

/-- DECIDABILITY, from the scheme: for every concept, `Sat C` is
decidable — by an actual program, not an oracle. -/
def decidableSat (C : S.Concept) : Decidable (S.Sat C) :=
  if h : decideB S C = true then .isTrue ((decideB_correct S C).mp h)
  else .isFalse (fun hs => h ((decideB_correct S C).mpr hs))

/-! ### Part 3: the quantitative bound is free a posteriori -/

/-- A certificate-index bound, read off the dovetailed run itself. -/
def certBound (C : S.Concept) : Nat := raceIdx S C

/-- On a satisfiable concept the refutation side can never fire
(`ref_sound`), so the winning index IS a passing certificate. -/
theorem cert_at_bound (C : S.Concept) (hs : S.Sat C) :
    S.certB C (certBound S C) = true := by
  have hr : raceB S C (raceIdx S C) = true := firstHit_spec _ _
  cases hc : S.certB C (raceIdx S C) with
  | true  => exact hc
  | false =>
    have hf : S.refB C (raceIdx S C) = true := by
      simpa [raceB, hc] using hr
    exact absurd hs (S.ref_sound C (raceIdx S C) hf)

/-- QUANTITATIVE F6 IS FREE A POSTERIORI: once the scheme is inhabited,
a certificate-size bound `B` exists as a function of the concept. The
computable budget the reviews kept demanding was never needed as an
INPUT to decidability — it falls out as an OUTPUT. -/
theorem quantitative_free :
    ∃ B : S.Concept → Nat, ∀ C, S.Sat C → ∃ n, n ≤ B C ∧ S.certB C n = true :=
  ⟨certBound S, fun C hs =>
    ⟨certBound S C, Nat.le_refl _, cert_at_bound S C hs⟩⟩

/-! ### Part 4: non-vacuity

A two-concept toy scheme — one satisfiable concept whose certificate
sits at index 3, one unsatisfiable concept whose refutation sits at
index 5 — exercising the actual search on both sides. -/

def toyScheme : DovetailScheme where
  Concept := Bool
  Sat := fun C => C = true
  certB := fun C n => C && decide (n = 3)
  refB := fun C n => !C && decide (n = 5)
  cert_sound := by
    intro C n h
    simp at h
    exact h.1
  ref_sound := by
    intro C n h hs
    simp [hs] at h
  cert_complete := by
    intro C hs
    exact ⟨3, by simp [hs]⟩
  ref_complete := by
    intro C hu
    refine ⟨5, ?_⟩
    cases C with
    | true  => exact absurd rfl hu
    | false => simp

#eval decideB toyScheme true    -- true  (certificate found at index 3)
#eval decideB toyScheme false   -- false (refutation found at index 5)

/-- The dovetailed program really runs: the satisfiable toy concept is
answered `true`. -/
theorem toy_sat : decideB toyScheme true = true := by native_decide

/-- ... and the unsatisfiable one `false`. -/
theorem toy_unsat : decideB toyScheme false = false := by native_decide

/-! ### Axiom audit -/

#print axioms firstHit_spec      -- propext, Quot.sound (search core: classical-free)
#print axioms decideB_correct    -- + Classical.choice (via race_fires only)
#print axioms quantitative_free  -- + Classical.choice
#print axioms toy_sat            -- + Lean.ofReduceBool (native_decide, witness only)

end SemiDecidability
