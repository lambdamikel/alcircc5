/-
  RCC5NormalForm.lean

  The RCC5 NORMAL FORM (harvested from the regular-cover pivot, Theorem 8;
  machine-checked at small n by wp47, here PROVED for all domains):

     a strong-EQ atomic RCC5 network IS an ordered-disjoint structure
     -- PP is a strict partial order `<`, DR is a symmetric, irreflexive,
     downward-closed disjointness `#`, and comparable pairs are never
     disjoint.

  This is the certified LOCAL algebra: it is independent of F6, and it is
  the clean structural fact both the split-forest and regular-cover
  routes rely on. This file proves the FORWARD direction (every RCC5
  network is ordered-disjoint) for arbitrary domains; the converse
  (ordered-disjoint structures realize RCC5 closure) is exhaustively
  machine-checked by wp47 up to n=4 and is a natural follow-up.

  The composition/converse tables are copied verbatim from the certified
  artifact `Round19Transport.lean` (the same table used and cross-checked
  across the whole development), so there is no table-input risk.

  Build (Lean 4 core, no mathlib):  lean RCC5NormalForm.lean
-/

namespace RCC5NormalForm

/-- The five RCC5 base relations (EQ = identity; the four proper atoms
    between distinct elements). -/
inductive Atom | eq | pp | ppi | po | dr
deriving DecidableEq, Repr

open Atom

/-- Converse (from the certified artifact). -/
def conv : Atom → Atom
  | eq => eq | pp => ppi | ppi => pp | po => po | dr => dr

/-- The RCC5 composition table (verbatim from the certified artifact). -/
def comp : Atom → Atom → List Atom
  | eq, b => [b]
  | a, eq => [a]
  | pp, pp => [pp]
  | pp, ppi => [eq, pp, ppi, po, dr]
  | pp, po => [pp, po, dr]
  | pp, dr => [dr]
  | ppi, pp => [eq, pp, ppi, po]
  | ppi, ppi => [ppi]
  | ppi, po => [ppi, po]
  | ppi, dr => [ppi, po, dr]
  | po, pp => [pp, po]
  | po, ppi => [ppi, po, dr]
  | po, po => [eq, pp, ppi, po, dr]
  | po, dr => [ppi, po, dr]
  | dr, pp => [pp, po, dr]
  | dr, ppi => [dr]
  | dr, po => [pp, po, dr]
  | dr, dr => [eq, pp, ppi, po, dr]

/-- A strong-EQ atomic RCC5 network on a domain `α`: a total labelling of
    ordered pairs by atoms that is reflexively `EQ`, has `EQ` only on the
    diagonal (strong-EQ), is converse-closed, and composition-closed. -/
structure RCC5Net (α : Type) where
  rho : α → α → Atom
  refl_eq : ∀ x, rho x x = eq
  eq_id : ∀ x y, rho x y = eq → x = y
  conv_ : ∀ x y, rho y x = conv (rho x y)
  comp_ : ∀ x y z, rho x z ∈ comp (rho x y) (rho y z)

/-- An ordered-disjoint structure: a strict partial order `lt` and a
    symmetric, irreflexive, downward-closed disjointness `disj`, with
    comparable pairs never disjoint. This is the target normal form. -/
structure OrderedDisjoint (α : Type) where
  lt : α → α → Prop
  disj : α → α → Prop
  lt_irrefl : ∀ x, ¬ lt x x
  lt_trans : ∀ x y z, lt x y → lt y z → lt x z
  disj_symm : ∀ x y, disj x y → disj y x
  disj_irrefl : ∀ x, ¬ disj x x
  comp_not_disj : ∀ x y, lt x y → ¬ disj x y
  disj_down : ∀ x y x' y', disj x y →
    (x' = x ∨ lt x' x) → (y' = y ∨ lt y' y) → disj x' y'

variable {α : Type}

/-! ### The three composition facts the normal form rests on -/

/-- `PP;PP = {PP}` gives transitivity of the order. -/
theorem step_pp_pp (N : RCC5Net α) {a b c} (h1 : N.rho a b = pp)
    (h2 : N.rho b c = pp) : N.rho a c = pp := by
  have h := N.comp_ a b c
  rw [h1, h2] at h
  exact List.mem_singleton.mp h

/-- `PP;DR = {DR}` propagates disjointness down on the left. -/
theorem step_pp_dr (N : RCC5Net α) {a b c} (h1 : N.rho a b = pp)
    (h2 : N.rho b c = dr) : N.rho a c = dr := by
  have h := N.comp_ a b c
  rw [h1, h2] at h
  exact List.mem_singleton.mp h

/-- `DR;PPI = {DR}` (via converse of PP) propagates disjointness down on
    the right. -/
theorem step_dr_pp (N : RCC5Net α) {a b c} (h1 : N.rho a b = dr)
    (h2 : N.rho c b = pp) : N.rho a c = dr := by
  have hbc : N.rho b c = ppi := by rw [N.conv_ c b, h2]; rfl
  have h := N.comp_ a b c
  rw [h1, hbc] at h
  exact List.mem_singleton.mp h

/-! ### The normal form (forward direction) -/

/-- THE RCC5 NORMAL FORM (forward): the PP/DR read-off of any strong-EQ
    RCC5 network is an ordered-disjoint structure. So every RCC5 network
    is, structurally, a strict partial order together with a
    downward-closed disjointness relation — the local algebra the whole
    project rests on, now certified for arbitrary domains. -/
def toOrderedDisjoint (N : RCC5Net α) : OrderedDisjoint α where
  lt := fun a b => N.rho a b = pp
  disj := fun a b => N.rho a b = dr
  lt_irrefl := fun x h => by rw [N.refl_eq x] at h; exact absurd h (by decide)
  lt_trans := fun _ _ _ hxy hyz => step_pp_pp N hxy hyz
  disj_symm := fun x y h => by rw [N.conv_ x y, h]; rfl
  disj_irrefl := fun x h => by rw [N.refl_eq x] at h; exact absurd h (by decide)
  comp_not_disj := fun _ _ hlt hdr => by rw [hlt] at hdr; exact absurd hdr (by decide)
  disj_down := by
    intro x y x' y' hd hx' hy'
    have hxy' : N.rho x' y = dr := by
      rcases hx' with rfl | hlt
      · exact hd
      · exact step_pp_dr N hlt hd
    rcases hy' with rfl | hlt
    · exact hxy'
    · exact step_dr_pp N hxy' hlt

/-! ### Corollaries: the order and disjointness structure, spelled out -/

/-- The order is a strict partial order (irreflexive + transitive). -/
theorem pp_strict_order (N : RCC5Net α) :
    (∀ x, N.rho x x ≠ pp) ∧
    (∀ x y z, N.rho x y = pp → N.rho y z = pp → N.rho x z = pp) :=
  ⟨(toOrderedDisjoint N).lt_irrefl, (toOrderedDisjoint N).lt_trans⟩

/-- Disjointness is downward closed along the order (the load-bearing
    fact for guard reasoning). -/
theorem dr_downward_closed (N : RCC5Net α) :
    ∀ x y x' y', N.rho x y = dr →
      (x' = x ∨ N.rho x' x = pp) → (y' = y ∨ N.rho y' y = pp) →
      N.rho x' y' = dr :=
  (toOrderedDisjoint N).disj_down

end RCC5NormalForm
