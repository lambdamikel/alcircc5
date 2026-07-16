/-
  ForcingReduction.lean

  A formalization of the width-barrier report's Observation 7.5 (the
  "forcing reduction"), i.e. Target D of the F6/W2' cold attack
  (GPT-5.5, `papers/cold_review_f6_w2prime`): the statement that

      F6 fails  iff  some satisfiable ALCI_RCC5 concept FORCES an
                     unbounded rigid horizontal crowd.

  The content is abstract order theory. Concept, Presentation, the
  live-width predicate, and the horizontal-crowd-width predicate are
  PARAMETERS; all RCC5-specific mathematics is isolated into a single
  hypothesis field, the width-crowd adequacy lemma

      lw(P) <= B(P) + hcw(P)      (and  hcw(P) <= lw(P)).

  That lemma is carried as a STRUCTURE FIELD, not an axiom: the RCC5
  content it abstracts remains an open mathematical obligation, visible
  in the statement rather than smuggled in. No `sorry` and no
  problem-specific axiom is added; the two reduction theorems use only
  the standard classical logic axioms (propext, Quot.sound,
  Classical.choice, the last via `Classical.byContradiction` on the
  negations). The theorem then is elementary: unbounded live width is
  equivalent to an unbounded forced crowd, hence F6_fin is equivalent to
  "no concept forces an unbounded crowd".

  Build (Lean 4 core, no mathlib):  lean ForcingReduction.lean
-/

namespace ForcingReduction

/-- The abstract data of the forcing reduction. `liveWidthGe P n` reads
    "presentation `P` has live width at least `n`"; `hCrowdGe P n` reads
    "P has a rigid horizontal crowd of size at least `n`". The last three
    fields are the only mathematics: crowd sizes are downward closed, a
    crowd of size `n` is itself live width `>= n`, and the width-crowd
    ADEQUACY lemma bounds live width by a computable vertical residue
    `B P` above the crowd width. -/
structure ForcingSetup where
  Concept : Type
  Presentation : Type
  Realizes : Presentation → Concept → Prop
  liveWidthGe : Presentation → Nat → Prop
  hCrowdGe : Presentation → Nat → Prop
  /-- Crowd size is downward closed. -/
  hCrowd_down : ∀ P n k, k ≤ n → hCrowdGe P n → hCrowdGe P k
  /-- A rigid horizontal crowd of size `n` contributes `n` to live width. -/
  crowd_le_width : ∀ P n, hCrowdGe P n → liveWidthGe P n
  /-- WIDTH-CROWD ADEQUACY (the one open bridge): live width `n` forces a
      crowd of size `n - B P`, for a computable vertical residue `B P`. -/
  adequacy : ∀ P, ∃ B, ∀ n, liveWidthGe P n → hCrowdGe P (n - B)

variable (S : ForcingSetup)

/-- A concept is satisfiable if some presentation realizes it. -/
def Satisfiable (C : S.Concept) : Prop := ∃ P, S.Realizes P C

/-- A presentation has finite live width. -/
def FiniteWidth (P : S.Presentation) : Prop :=
  ∃ B, ∀ n, S.liveWidthGe P n → n ≤ B

/-- Effective F6 (structural form): every satisfiable concept has a
    finite-live-width presentation. -/
def F6fin : Prop :=
  ∀ C, Satisfiable S C → ∃ P, S.Realizes P C ∧ FiniteWidth S P

/-- `C` forces an unbounded rigid horizontal crowd: every presentation
    realizing `C` has a crowd of every size. -/
def ForcesUnbCrowd (C : S.Concept) : Prop :=
  ∀ n, ∀ P, S.Realizes P C → S.hCrowdGe P n

/-- The heart: a presentation has finite live width iff its crowd width
    is bounded (misses some size). Uses only the three structure fields.
    `→` is the singleton-shadow direction (a crowd is live width, so
    bounded width bounds crowds); `←` is adequacy (bounded crowd bounds
    width above the vertical residue). -/
theorem finiteWidth_iff (P : S.Presentation) :
    FiniteWidth S P ↔ ∃ n, ¬ S.hCrowdGe P n := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B + 1, ?_⟩
    intro hc
    have := hB (B + 1) (S.crowd_le_width P (B + 1) hc)
    omega
  · rintro ⟨n0, hn0⟩
    obtain ⟨B, hadeq⟩ := S.adequacy P
    refine ⟨B + n0, ?_⟩
    intro n hlw
    refine Classical.byContradiction (fun hcon => ?_)
    have hc := hadeq n hlw
    have hle : n0 ≤ n - B := by omega
    exact hn0 (S.hCrowd_down P (n - B) n0 hle hc)

/-- THE FORCING REDUCTION (formal Observation 7.5). Effective F6 holds
    iff no satisfiable concept forces an unbounded rigid horizontal
    crowd. Elementary given `finiteWidth_iff`. -/
theorem forcing_reduction :
    F6fin S ↔ ∀ C, Satisfiable S C → ¬ ForcesUnbCrowd S C := by
  constructor
  · intro hF6 C hsat hforce
    obtain ⟨P, hR, hFW⟩ := hF6 C hsat
    obtain ⟨n, hnc⟩ := (finiteWidth_iff S P).mp hFW
    exact hnc (hforce n P hR)
  · intro hno C hsat
    have hnf := hno C hsat
    refine Classical.byContradiction (fun hgoal => ?_)
    apply hnf
    intro n P hR
    refine Classical.byContradiction (fun hnc => ?_)
    exact hgoal ⟨P, hR, (finiteWidth_iff S P).mpr ⟨n, hnc⟩⟩

/-- The "one fact, two faces" form: F6 fails iff some satisfiable concept
    forces an unbounded rigid horizontal crowd. -/
theorem f6_fails_iff_forces :
    ¬ F6fin S ↔ ∃ C, Satisfiable S C ∧ ForcesUnbCrowd S C := by
  rw [forcing_reduction]
  constructor
  · intro h
    refine Classical.byContradiction (fun hcon => ?_)
    exact h (fun C hsat hforce => hcon ⟨C, hsat, hforce⟩)
  · rintro ⟨C, hsat, hforce⟩ hall
    exact hall C hsat hforce

/-! ### Non-vacuity: the framework is inhabitable -/

/-- A trivial setup (width = crowd, one concept) inhabiting
    `ForcingSetup`, so the reduction is not vacuous. -/
def trivialSetup : ForcingSetup where
  Concept := Unit
  Presentation := Nat
  Realizes := fun _ _ => True
  liveWidthGe := fun P n => n ≤ P
  hCrowdGe := fun P n => n ≤ P
  hCrowd_down := fun _ _ _ hkn hn => Nat.le_trans hkn hn
  crowd_le_width := fun _ _ h => h
  adequacy := fun _ => ⟨0, fun n h => by rw [Nat.sub_zero]; exact h⟩

/-- In the trivial setup nothing forces an unbounded crowd, so F6 holds
    — a concrete instance of `forcing_reduction`. -/
theorem trivial_f6fin : F6fin trivialSetup := by
  intro _ _
  exact ⟨(0 : Nat), trivial, 0, fun _ h => h⟩

end ForcingReduction
