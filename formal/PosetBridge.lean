/-
  PosetBridge.lean  (2026-11-11)

  THE POSET BRIDGE: two-variable logic over strict partial orders lives inside
  ALCI_RCC5, and an infinity axiom that needs no vertical witness.

  What is proved here (Lean 4 core, no mathlib; imports the certified artifact
  `POFreeLift.lean`, so `Concept`, `sat`, `RCC5Interp` and `Satisfiable` are
  LITERALLY the ones the fragment's decision procedure is stated for):

  §1  The tense logic of strict partial orders with an INCOMPARABILITY
      modality (`PConcept`: roles `=`, `<`, `>`, `∥`), plus two harmless extras
      (`xpo` = a bare `∃PO`, `adr` = a bare `∀DR`).

  §2  `poset_bridge : PSatisfiable c ↔ Satisfiable (emb c)`, where `emb` reads
      `∃∥.C` as `∃PO.C ⊔ ∃DR.C` and `∀∥.C` as `∀PO.C ⊓ ∀DR.C`.
        →  a strict partial order IS an ordered-disjoint structure with EMPTY
           disjointness, so `odNet_frame` makes it an RCC5 frame;
        ←  the `PP`-reduct of any RCC5 model is a strict partial order whose
           incomparable pairs are exactly its `PO ∪ DR` pairs.
      No fragment hypothesis. The carrier is preserved (up to the domain
      predicate), so the equivalence also holds for FINITE satisfiability
      (`poset_bridge_fin`).

  §3  Decidability transfers DOWNWARD: a decision procedure for full ALCI_RCC5
      yields one for the poset logic (`decidablePSat_of_full`). And the
      certified `∀PO`-free procedure already decides the `∀∥`-free part
      (`decidablePSat_noAllInc`).

  §4  The first-order face. `PatSys` is a two-variable sentence over a strict
      partial order with unary predicates, in type-expanded Scott normal form:
      forbidden patterns  ∀x∀y ¬(τ(x) ∧ r(x,y) ∧ τ'(y))  and requirements
      ∀x (τ(x) → ⋁ ∃y (r(x,y) ∧ τ'(y))),  r ∈ {=,<,>,∥}.  Marzec & Tendera's
      "basic normal form" (B1)–(B10) for FO²_u1PO is of this shape, once its
      unary conditions are written as disjunctions of literal conjunctions.
      `patsys_to_rcc5 : S.Sat ↔ Satisfiable (emb S.toConcept)`.

  §5  Marzec & Tendera's spiral, as a `PatSys`: five predicates, the
      entanglements `A_i ◁▷ A_{i+2}`, and incomparable witnesses in `A_{i±1}`.
      `spiral_sat` (the ℤ-spiral) and `spiral_infinite` (every model contains
      an injective ω-sequence).

  §6  The same for ALCI_RCC5: `spiralConcept` is satisfiable, every RCC5 model
      of it is infinite, and it contains NO `∃PP` and NO `∃PPI`
      (`spiralConcept_noExVert`). Infinity is forced by `∃PO`/`∃DR` and
      `∀PO`/`∀DR` alone: two witnesses that may be neither `PO` nor `DR` must
      be NESTED, and five colours make the nesting run forever.

  §7  `K2 = ∃PO.(A ⊓ ∀PO.¬B ⊓ ∀DR.¬B) ⊓ ∃PO.(B ⊓ ¬A)` is satisfiable
      (`k2_sat`, a three-point model) and its two witnesses are nested in
      every model (`k2_witnesses_nested`). The cover-tree tableau answers
      UNSAT on it (`wp137`, part E).

  §8  `C_cyc`: three proper superparts forced into a cycle `a ⊂ b ⊂ c ⊂ a`.
      Unsatisfiable (`ccyc_unsat`), satisfiable once its `∀PO` conjuncts are
      erased (`ccycErased_sat`), and free of `∃PO`/`∃DR` -- so in the
      vertical-witness slice of the fragment a `∀PO` constraint is NOT
      erasable.

  WHY IT MATTERS. General satisfiability for two-variable logic with one
  transitive relation -- equivalently, with one strict partial order -- is an
  OPEN problem of the FO² literature (the STACS 2013 decidability claim was
  withdrawn by its authors; Marzec & Tendera, J. Logic Comput. 36(2), 2026,
  still conjecture it). §§2-4 show its unary-signature case is a syntactic
  fragment of ALCI_RCC5. So a decision procedure for the full logic would
  settle that case; and an undecidability proof for it would settle the full
  logic negatively.

  Build (two steps, because this file imports the artifact):
      lean -o POFreeLift.olean POFreeLift.lean
      LEAN_PATH=. lean PosetBridge.lean
  Pinned toolchain: Lean 4.33.1, as for `POFreeLift.lean`.
-/

import POFreeLift

namespace POFreeLift
namespace PosetBridge

open Atom

/-! ## §1  Strict partial orders and their tense logic with incomparability -/

/-- A strict partial order. -/
structure SPO (α : Type) where
  lt : α → α → Prop
  irr : ∀ x, ¬ lt x x
  tr : ∀ x y z, lt x y → lt y z → lt x z

/-- Incomparability: distinct, and related neither way. -/
@[reducible] def SPO.inc {α : Type} (P : SPO α) (x y : α) : Prop :=
  x ≠ y ∧ ¬ P.lt x y ∧ ¬ P.lt y x

theorem SPO.inc_symm {α : Type} (P : SPO α) {x y : α} (h : P.inc x y) :
    P.inc y x :=
  ⟨fun e => h.1 e.symm, h.2.2, h.2.1⟩

/-- The four mutually exclusive, jointly exhaustive relations of a strict
    partial order. -/
inductive PRole | eq | lt | gt | inc
deriving DecidableEq, Repr

def SPO.rel {α : Type} (P : SPO α) : PRole → α → α → Prop
  | .eq, x, y => x = y
  | .lt, x, y => P.lt x y
  | .gt, x, y => P.lt y x
  | .inc, x, y => P.inc x y

/-- NNF concepts of the tense logic of strict partial orders with an
    incomparability modality.  `xpo` and `adr` are the two RCC5 constructors
    that can be added for free: a bare `∃PO` (read as `∃∥`) and a bare `∀DR`
    (read as `⊤`). -/
inductive PConcept
  | top | bot
  | atom (a : Nat)
  | natom (a : Nat)
  | and (c d : PConcept)
  | or (c d : PConcept)
  | ex (r : PRole) (c : PConcept)
  | all (r : PRole) (c : PConcept)
  | xpo (c : PConcept)
  | adr (c : PConcept)
deriving DecidableEq, Repr

/-- Satisfaction over a strict partial order. -/
def psat {α : Type} (P : SPO α) (val : Nat → α → Prop) : α → PConcept → Prop
  | _, .top => True
  | _, .bot => False
  | x, .atom a => val a x
  | x, .natom a => ¬ val a x
  | x, .and c d => psat P val x c ∧ psat P val x d
  | x, .or c d => psat P val x c ∨ psat P val x d
  | x, .ex r c => ∃ y, P.rel r x y ∧ psat P val y c
  | x, .all r c => ∀ y, P.rel r x y → psat P val y c
  | x, .xpo c => ∃ y, P.inc x y ∧ psat P val y c
  | _, .adr _ => True

/-- Satisfiability over strict partial orders. -/
def PSatisfiable (c : PConcept) : Prop :=
  ∃ (α : Type) (P : SPO α) (val : Nat → α → Prop) (x : α), psat P val x c

/-! ## §2  The embedding into ALCI_RCC5 and the bridge theorem -/

/-- `∃∥` is `∃PO ⊔ ∃DR`; `∀∥` is `∀PO ⊓ ∀DR`; the vertical roles are `PP`/`PPI`. -/
def emb : PConcept → Concept
  | .top => .top
  | .bot => .bot
  | .atom a => .atom a
  | .natom a => .natom a
  | .and c d => .and (emb c) (emb d)
  | .or c d => .or (emb c) (emb d)
  | .ex .eq c => .ex eq (emb c)
  | .ex .lt c => .ex pp (emb c)
  | .ex .gt c => .ex ppi (emb c)
  | .ex .inc c => .or (.ex po (emb c)) (.ex dr (emb c))
  | .all .eq c => .all eq (emb c)
  | .all .lt c => .all pp (emb c)
  | .all .gt c => .all ppi (emb c)
  | .all .inc c => .and (.all po (emb c)) (.all dr (emb c))
  | .xpo c => .ex po (emb c)
  | .adr c => .all dr (emb c)

section Up

variable {α : Type} (P : SPO α) (val : Nat → α → Prop)

/-- A strict partial order as an ordered-disjoint structure with EMPTY
    disjointness: every incomparable pair is an overlap. -/
def odOf : ODStruct α where
  lt := P.lt
  disj := fun _ _ => False
  ltIrr := P.irr
  ltTr := P.tr
  djSym := fun _ _ h => h
  djIrr := fun _ h => h
  ltNotDj := fun _ _ _ h => h
  djDown := fun _ _ _ _ h _ _ => h

/-- The RCC5 interpretation of a strict partial order: `PP` is the order, `PO`
    is incomparability, `DR` is empty. -/
noncomputable def interpOf : Interp α :=
  ⟨fun _ => True, odNet (odOf P), val⟩

theorem interpOf_rcc5 : RCC5Interp (interpOf P val) :=
  frame_rcc5 (odNet (odOf P)) (odNet_frame (odOf P)) val

theorem net_po_of_inc {x y : α} (h : P.inc x y) : odNet (odOf P) x y = po :=
  odNet_po (odOf P) h.1 h.2.1 h.2.2 (fun h => h)

theorem inc_of_net_po {x y : α} (h : odNet (odOf P) x y = po) : P.inc x y := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    subst e
    rw [odNet_self] at h
    exact absurd h (by decide)
  · intro hl
    rw [odNet_lt (odOf P) hl] at h
    exact absurd h (by decide)
  · intro hl
    rw [odNet_gt (odOf P) hl] at h
    exact absurd h (by decide)

theorem net_ne_dr {x y : α} : odNet (odOf P) x y ≠ dr :=
  fun h => odNet_dr_inv (odOf P) h

/-- Truth is preserved from the poset to its RCC5 interpretation. -/
theorem truth_up : ∀ (c : PConcept) (x : α),
    psat P val x c → sat (interpOf P val) x (emb c) := by
  intro c
  induction c with
  | top => intro x _; exact True.intro
  | bot => intro x h; exact h
  | atom a => intro x h; exact h
  | natom a => intro x h; exact h
  | and c d ihc ihd => intro x h; exact ⟨ihc x h.1, ihd x h.2⟩
  | or c d ihc ihd =>
    intro x h
    rcases h with h | h
    · exact Or.inl (ihc x h)
    · exact Or.inr (ihd x h)
  | ex r c ih =>
    intro x h
    obtain ⟨y, hr, hy⟩ := h
    cases r with
    | eq =>
      have e : x = y := hr
      subst e
      exact ⟨x, True.intro, odNet_self (odOf P) x, ih x hy⟩
    | lt => exact ⟨y, True.intro, odNet_lt (odOf P) hr, ih y hy⟩
    | gt => exact ⟨y, True.intro, odNet_gt (odOf P) hr, ih y hy⟩
    | inc => exact Or.inl ⟨y, True.intro, net_po_of_inc P hr, ih y hy⟩
  | all r c ih =>
    intro x h
    cases r with
    | eq => intro y _ hr; exact ih y (h y (odNet_eq_inv (odOf P) hr))
    | lt => intro y _ hr; exact ih y (h y (odNet_pp_inv (odOf P) hr))
    | gt => intro y _ hr; exact ih y (h y (odNet_ppi_inv (odOf P) hr))
    | inc =>
      refine ⟨?_, ?_⟩
      · intro y _ hr; exact ih y (h y (inc_of_net_po P hr))
      · intro y _ hr; exact absurd hr (net_ne_dr P)
  | xpo c ih =>
    intro x h
    obtain ⟨y, hr, hy⟩ := h
    exact ⟨y, True.intro, net_po_of_inc P hr, ih y hy⟩
  | adr c _ =>
    intro x _ y _ hr
    exact absurd hr (net_ne_dr P)

end Up

section Down

variable {α : Type} (I : Interp α) (hI : RCC5Interp I)

/-- The `PP`-reduct of an RCC5 model, on its domain: a strict partial order.
    Irreflexivity is reflexive-`EQ`; transitivity is the cell
    `comp(PP,PP) = {PP}`. -/
def spoOf : SPO {x : α // I.dom x} where
  lt := fun a b => I.rho a.1 b.1 = pp
  irr := by
    intro a h
    rw [hI.refl_eq a.1 a.2] at h
    exact absurd h (by decide)
  tr := by
    intro a b c h1 h2
    have h := hI.comp_ a.1 b.1 c.1 a.2 b.2 c.2
    rw [h1, h2] at h
    rw [show comp pp pp = [pp] from rfl] at h
    exact List.mem_singleton.mp h

/-- An overlap or a disjointness is an incomparability of the reduct ... -/
theorem inc_of_po_or_dr {a b : {x : α // I.dom x}}
    (h : I.rho a.1 b.1 = po ∨ I.rho a.1 b.1 = dr) : (spoOf I hI).inc a b := by
  have hc := hI.conv_ a.1 b.1 a.2 b.2
  refine ⟨?_, ?_, ?_⟩
  · intro e
    subst e
    have h0 := hI.refl_eq a.1 a.2
    rcases h with h | h <;> (rw [h0] at h; exact absurd h (by decide))
  · intro hl
    have hl' : I.rho a.1 b.1 = pp := hl
    rcases h with h | h <;> (rw [hl'] at h; exact absurd h (by decide))
  · intro hl
    have hl' : I.rho b.1 a.1 = pp := hl
    rw [hc] at hl'
    rcases h with h | h <;> (rw [h] at hl'; exact absurd hl' (by decide))

/-- ... and conversely: the incomparable pairs are EXACTLY the `PO ∪ DR` pairs. -/
theorem po_or_dr_of_inc {a b : {x : α // I.dom x}}
    (h : (spoOf I hI).inc a b) :
    I.rho a.1 b.1 = po ∨ I.rho a.1 b.1 = dr := by
  have hc := hI.conv_ a.1 b.1 a.2 b.2
  have h1 : a ≠ b := h.1
  have h2 : ¬ I.rho a.1 b.1 = pp := h.2.1
  have h3 : ¬ I.rho b.1 a.1 = pp := h.2.2
  cases hr : I.rho a.1 b.1 with
  | eq => exact absurd (Subtype.ext (hI.eq_id a.1 b.1 a.2 b.2 hr)) h1
  | pp => exact absurd hr h2
  | ppi =>
    rw [hr] at hc
    exact absurd hc h3
  | po => exact Or.inl rfl
  | dr => exact Or.inr rfl

/-- Truth is preserved from an RCC5 model to its `PP`-reduct. -/
theorem truth_down : ∀ (c : PConcept) (a : {x : α // I.dom x}),
    sat I a.1 (emb c) →
      psat (spoOf I hI) (fun n b => I.val n b.1) a c := by
  intro c
  induction c with
  | top => intro a _; exact True.intro
  | bot => intro a h; exact h
  | atom n => intro a h; exact h
  | natom n => intro a h; exact h
  | and c d ihc ihd => intro a h; exact ⟨ihc a h.1, ihd a h.2⟩
  | or c d ihc ihd =>
    intro a h
    rcases h with h | h
    · exact Or.inl (ihc a h)
    · exact Or.inr (ihd a h)
  | ex r c ih =>
    intro a h
    cases r with
    | eq =>
      obtain ⟨y, hy, hr, hs⟩ := h
      have e : a.1 = y := hI.eq_id a.1 y a.2 hy hr
      exact ⟨⟨y, hy⟩, Subtype.ext e, ih ⟨y, hy⟩ hs⟩
    | lt =>
      obtain ⟨y, hy, hr, hs⟩ := h
      exact ⟨⟨y, hy⟩, hr, ih ⟨y, hy⟩ hs⟩
    | gt =>
      obtain ⟨y, hy, hr, hs⟩ := h
      refine ⟨⟨y, hy⟩, ?_, ih ⟨y, hy⟩ hs⟩
      show I.rho y a.1 = pp
      rw [hI.conv_ a.1 y a.2 hy, hr]
      rfl
    | inc =>
      rcases h with ⟨y, hy, hr, hs⟩ | ⟨y, hy, hr, hs⟩
      · exact ⟨⟨y, hy⟩, inc_of_po_or_dr I hI (Or.inl hr), ih ⟨y, hy⟩ hs⟩
      · exact ⟨⟨y, hy⟩, inc_of_po_or_dr I hI (Or.inr hr), ih ⟨y, hy⟩ hs⟩
  | all r c ih =>
    intro a h
    cases r with
    | eq =>
      intro b hr
      have e : a = b := hr
      subst e
      exact ih a (h a.1 a.2 (hI.refl_eq a.1 a.2))
    | lt => intro b hr; exact ih b (h b.1 b.2 hr)
    | gt =>
      intro b hr
      have hr' : I.rho b.1 a.1 = pp := hr
      have hab : I.rho a.1 b.1 = ppi := by
        rw [hI.conv_ b.1 a.1 b.2 a.2, hr']
        rfl
      exact ih b (h b.1 b.2 hab)
    | inc =>
      intro b hr
      rcases po_or_dr_of_inc I hI hr with hp | hd
      · exact ih b (h.1 b.1 b.2 hp)
      · exact ih b (h.2 b.1 b.2 hd)
  | xpo c ih =>
    intro a h
    obtain ⟨y, hy, hr, hs⟩ := h
    exact ⟨⟨y, hy⟩, inc_of_po_or_dr I hI (Or.inl hr), ih ⟨y, hy⟩ hs⟩
  | adr c _ => intro a _; exact True.intro

end Down

/-- **THE POSET BRIDGE.**  A concept of the tense logic of strict partial
    orders with incomparability is satisfiable over a strict partial order iff
    its embedding is satisfiable in ALCI_RCC5.  No fragment hypothesis; both
    directions keep the carrier (the second restricts it to the domain). -/
theorem poset_bridge (c : PConcept) : PSatisfiable c ↔ Satisfiable (emb c) := by
  constructor
  · rintro ⟨α, P, val, x, h⟩
    exact ⟨α, interpOf P val, interpOf_rcc5 P val, x, True.intro,
      truth_up P val c x h⟩
  · rintro ⟨α, I, hI, x, hx, h⟩
    exact ⟨{x : α // I.dom x}, spoOf I hI, fun n b => I.val n b.1, ⟨x, hx⟩,
      truth_down I hI c ⟨x, hx⟩ h⟩

/-! ### Finite satisfiability transfers too

Both model transformations keep the carrier -- the first literally, the second
up to restriction to the domain predicate. So the bridge is also a bridge for
FINITE satisfiability (Lutz & Wolter's "finite companions"). -/

/-- A type all of whose elements appear in one list. -/
def Enumerated (α : Type) : Prop := ∃ l : List α, ∀ x : α, x ∈ l

/-- Satisfiability over a FINITE strict partial order. -/
def PFinSatisfiable (c : PConcept) : Prop :=
  ∃ (α : Type) (P : SPO α) (val : Nat → α → Prop) (x : α),
    Enumerated α ∧ psat P val x c

/-- Satisfiability in an RCC5 model with a FINITE domain. -/
def FinSatisfiable (C0 : Concept) : Prop :=
  ∃ (α : Type) (I : Interp α), RCC5Interp I ∧
    (∃ l : List α, ∀ x, I.dom x → x ∈ l) ∧ ∃ x, I.dom x ∧ sat I x C0

theorem enum_sub {α : Type} (p : α → Prop) :
    ∀ l : List α, ∃ l' : List {x : α // p x},
      ∀ (x : α) (hx : p x), x ∈ l → (⟨x, hx⟩ : {x : α // p x}) ∈ l'
  | [] => ⟨[], fun _ _ h => nomatch h⟩
  | a :: as => by
    obtain ⟨l', hl'⟩ := enum_sub p as
    rcases Classical.em (p a) with ha | ha
    · refine ⟨⟨a, ha⟩ :: l', ?_⟩
      intro x hx hmem
      cases hmem with
      | head => exact .head _
      | tail _ h => exact .tail _ (hl' x hx h)
    · refine ⟨l', ?_⟩
      intro x hx hmem
      cases hmem with
      | head => exact absurd hx ha
      | tail _ h => exact hl' x hx h

/-- **THE BRIDGE, FOR FINITE MODELS.** -/
theorem poset_bridge_fin (c : PConcept) :
    PFinSatisfiable c ↔ FinSatisfiable (emb c) := by
  constructor
  · rintro ⟨α, P, val, x, ⟨l, hl⟩, h⟩
    exact ⟨α, interpOf P val, interpOf_rcc5 P val, ⟨l, fun y _ => hl y⟩, x,
      True.intro, truth_up P val c x h⟩
  · rintro ⟨α, I, hI, ⟨l, hl⟩, x, hx, h⟩
    obtain ⟨l', hl'⟩ := enum_sub I.dom l
    exact ⟨{x : α // I.dom x}, spoOf I hI, fun n b => I.val n b.1, ⟨x, hx⟩,
      ⟨l', fun y => hl' y.1 y.2 (hl y.1 y.2)⟩, truth_down I hI c ⟨x, hx⟩ h⟩

/-! ## §3  Decidability transfers downward -/

/-- **A DECISION PROCEDURE FOR FULL ALCI_RCC5 WOULD DECIDE THE POSET LOGIC.**
    The reduction is the computable map `emb`. -/
def decidablePSat_of_full (h : ∀ C : Concept, Decidable (Satisfiable C))
    (c : PConcept) : Decidable (PSatisfiable c) :=
  @decidable_of_iff _ _ (poset_bridge c).symm (h (emb c))

/-- No `∀∥`: the image then contains no `∀PO`. -/
def NoAllInc : PConcept → Prop
  | .top => True
  | .bot => True
  | .atom _ => True
  | .natom _ => True
  | .and c d => NoAllInc c ∧ NoAllInc d
  | .or c d => NoAllInc c ∧ NoAllInc d
  | .ex _ c => NoAllInc c
  | .all r c => r ≠ .inc ∧ NoAllInc c
  | .xpo c => NoAllInc c
  | .adr c => NoAllInc c

theorem pofree_emb : ∀ c : PConcept, NoAllInc c → POFree (emb c) := by
  intro c
  induction c with
  | top => intro _; exact True.intro
  | bot => intro _; exact True.intro
  | atom a => intro _; exact True.intro
  | natom a => intro _; exact True.intro
  | and c d ihc ihd => intro h; exact ⟨ihc h.1, ihd h.2⟩
  | or c d ihc ihd => intro h; exact ⟨ihc h.1, ihd h.2⟩
  | ex r c ih =>
    intro h
    cases r with
    | eq => exact ih h
    | lt => exact ih h
    | gt => exact ih h
    | inc => exact ⟨ih h, ih h⟩
  | all r c ih =>
    intro h
    cases r with
    | eq => exact ⟨by decide, ih h.2⟩
    | lt => exact ⟨by decide, ih h.2⟩
    | gt => exact ⟨by decide, ih h.2⟩
    | inc => exact absurd rfl h.1
  | xpo c ih => intro h; exact ih h
  | adr c ih => intro h; exact ⟨by decide, ih h⟩

/-- The certified `∀PO`-free procedure already decides the `∀∥`-free part of
    the poset logic. -/
def decidablePSat_noAllInc (c : PConcept) (h : NoAllInc c) :
    Decidable (PSatisfiable c) :=
  @decidable_of_iff _ _ (poset_bridge c).symm
    (decidableSat_cone (emb c) (pofree_emb c h))

/-! ## §4  The first-order face: two-variable pattern systems -/

/-- A literal: a unary predicate with a polarity. -/
abbrev Lit := Nat × Bool

def litHolds {α : Type} (val : Nat → α → Prop) (x : α) : Lit → Prop
  | (a, true) => val a x
  | (a, false) => ¬ val a x

/-- A conjunction of literals -- a (partial) 1-type. -/
def litsHold {α : Type} (val : Nat → α → Prop) (x : α) (ls : List Lit) : Prop :=
  ∀ l, l ∈ ls → litHolds val x l

/-- A two-variable sentence over a strict partial order with unary predicates,
    in type-expanded Scott normal form.

    * `forb` : forbidden patterns  `∀x∀y ¬(τ(x) ∧ r(x,y) ∧ τ'(y))`;
    * `req`  : requirements        `∀x (τ(x) → ⋁ₒ ∃y (rₒ(x,y) ∧ τₒ(y)))`,

    with `r ∈ {=, <, >, ∥}`.  Every `FO²[<, unary]` sentence is equisatisfiable
    with one (Scott normal form, then expansion over 1-types -- standard, and
    NOT formalized here); Marzec & Tendera's basic normal form (B1)–(B10) is of
    this shape once its unary conditions are in disjunctive normal form. -/
structure PatSys where
  forb : List (List Lit × PRole × List Lit)
  req : List (List Lit × List (PRole × List Lit))

def PatSys.Holds (S : PatSys) {α : Type} (P : SPO α)
    (val : Nat → α → Prop) : Prop :=
  (∀ f, f ∈ S.forb → ∀ x y, litsHold val x f.1 → P.rel f.2.1 x y →
      ¬ litsHold val y f.2.2) ∧
  (∀ q, q ∈ S.req → ∀ x, litsHold val x q.1 →
      ∃ o, o ∈ q.2 ∧ ∃ y, P.rel o.1 x y ∧ litsHold val y o.2)

/-- Satisfiability of a pattern system: a NON-EMPTY strict partial order. -/
def PatSys.Sat (S : PatSys) : Prop :=
  ∃ (α : Type) (P : SPO α) (val : Nat → α → Prop), Nonempty α ∧ S.Holds P val

def litC : Lit → PConcept
  | (a, true) => .atom a
  | (a, false) => .natom a

def nlitC : Lit → PConcept
  | (a, true) => .natom a
  | (a, false) => .atom a

def conjL : List PConcept → PConcept
  | [] => .top
  | c :: cs => .and c (conjL cs)

def disjL : List PConcept → PConcept
  | [] => .bot
  | c :: cs => .or c (disjL cs)

/-- `τ` as a concept. -/
def litsC (ls : List Lit) : PConcept := conjL (ls.map litC)

/-- `¬τ` as a concept. -/
def nlitsC (ls : List Lit) : PConcept := disjL (ls.map nlitC)

def forbC (f : List Lit × PRole × List Lit) : PConcept :=
  .or (nlitsC f.1) (.all f.2.1 (nlitsC f.2.2))

def optC (o : PRole × List Lit) : PConcept := .ex o.1 (litsC o.2)

def reqC (q : List Lit × List (PRole × List Lit)) : PConcept :=
  .or (nlitsC q.1) (disjL (q.2.map optC))

def bodyC (S : PatSys) : PConcept :=
  .and (conjL (S.forb.map forbC)) (conjL (S.req.map reqC))

/-- The universal modality of a strict partial order: here, `<`, `>`, `∥`. -/
def univC (g : PConcept) : PConcept :=
  .and g (.and (.all .lt g) (.and (.all .gt g) (.all .inc g)))

/-- The concept of a pattern system: its body, everywhere. -/
def PatSys.toConcept (S : PatSys) : PConcept := univC (bodyC S)

section PatSem

variable {α : Type} (P : SPO α) (val : Nat → α → Prop)

theorem psat_litC (x : α) (l : Lit) :
    psat P val x (litC l) ↔ litHolds val x l := by
  obtain ⟨a, b⟩ := l
  cases b <;> exact Iff.rfl

theorem psat_nlitC (x : α) (l : Lit) :
    psat P val x (nlitC l) ↔ ¬ litHolds val x l := by
  obtain ⟨a, b⟩ := l
  cases b
  · exact ⟨fun h hn => hn h, fun h => Classical.byContradiction h⟩
  · exact Iff.rfl

theorem psat_conjL_map {β : Type} (f : β → PConcept) (x : α) :
    ∀ bs : List β, psat P val x (conjL (bs.map f)) ↔
      ∀ b, b ∈ bs → psat P val x (f b)
  | [] => ⟨fun _ b hb => (nomatch hb), fun _ => True.intro⟩
  | b :: bs => by
    show (psat P val x (f b) ∧ psat P val x (conjL (bs.map f))) ↔ _
    rw [psat_conjL_map f x bs]
    constructor
    · rintro ⟨h1, h2⟩ d hd
      cases hd with
      | head => exact h1
      | tail _ hd => exact h2 d hd
    · intro h
      exact ⟨h b (.head _), fun d hd => h d (.tail _ hd)⟩

theorem psat_disjL_map {β : Type} (f : β → PConcept) (x : α) :
    ∀ bs : List β, psat P val x (disjL (bs.map f)) ↔
      ∃ b, b ∈ bs ∧ psat P val x (f b)
  | [] => by
    constructor
    · intro h; exact h.elim
    · rintro ⟨_, hb, _⟩; exact nomatch hb
  | b :: bs => by
    show (psat P val x (f b) ∨ psat P val x (disjL (bs.map f))) ↔ _
    rw [psat_disjL_map f x bs]
    constructor
    · rintro (h | ⟨d, hd, h⟩)
      · exact ⟨b, .head _, h⟩
      · exact ⟨d, .tail _ hd, h⟩
    · rintro ⟨d, hd, h⟩
      cases hd with
      | head => exact Or.inl h
      | tail _ hd => exact Or.inr ⟨d, hd, h⟩

theorem psat_litsC (x : α) (ls : List Lit) :
    psat P val x (litsC ls) ↔ litsHold val x ls := by
  show psat P val x (conjL (ls.map litC)) ↔ _
  rw [psat_conjL_map]
  exact ⟨fun h l hl => (psat_litC P val x l).mp (h l hl),
    fun h l hl => (psat_litC P val x l).mpr (h l hl)⟩

theorem psat_nlitsC (x : α) (ls : List Lit) :
    psat P val x (nlitsC ls) ↔ ¬ litsHold val x ls := by
  show psat P val x (disjL (ls.map nlitC)) ↔ _
  rw [psat_disjL_map]
  constructor
  · rintro ⟨l, hl, h⟩ hall
    exact (psat_nlitC P val x l).mp h (hall l hl)
  · intro h
    apply Classical.byContradiction
    intro hno
    apply h
    intro l hl
    apply Classical.byContradiction
    intro hn
    exact hno ⟨l, hl, (psat_nlitC P val x l).mpr hn⟩

theorem psat_forbC (x : α) (f : List Lit × PRole × List Lit) :
    psat P val x (forbC f) ↔
      (litsHold val x f.1 → ∀ y, P.rel f.2.1 x y → ¬ litsHold val y f.2.2) := by
  show (psat P val x (nlitsC f.1) ∨
      ∀ y, P.rel f.2.1 x y → psat P val y (nlitsC f.2.2)) ↔ _
  rw [psat_nlitsC]
  constructor
  · rintro (h | h) hx y hr
    · exact absurd hx h
    · exact (psat_nlitsC P val y f.2.2).mp (h y hr)
  · intro h
    rcases Classical.em (litsHold val x f.1) with hx | hx
    · exact Or.inr (fun y hr => (psat_nlitsC P val y f.2.2).mpr (h hx y hr))
    · exact Or.inl hx

theorem psat_reqC (x : α) (q : List Lit × List (PRole × List Lit)) :
    psat P val x (reqC q) ↔
      (litsHold val x q.1 →
        ∃ o, o ∈ q.2 ∧ ∃ y, P.rel o.1 x y ∧ litsHold val y o.2) := by
  show (psat P val x (nlitsC q.1) ∨ psat P val x (disjL (q.2.map optC))) ↔ _
  rw [psat_nlitsC, psat_disjL_map]
  constructor
  · rintro (h | ⟨o, ho, y, hr, hy⟩) hx
    · exact absurd hx h
    · exact ⟨o, ho, y, hr, (psat_litsC P val y o.2).mp hy⟩
  · intro h
    rcases Classical.em (litsHold val x q.1) with hx | hx
    · obtain ⟨o, ho, y, hr, hy⟩ := h hx
      exact Or.inr ⟨o, ho, y, hr, (psat_litsC P val y o.2).mpr hy⟩
    · exact Or.inl hx

/-- The universal modality really is universal: `=`, `<`, `>`, `∥` exhaust all
    pairs. -/
theorem psat_univC (x : α) (g : PConcept) :
    psat P val x (univC g) ↔ ∀ y, psat P val y g := by
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ y
    rcases Classical.em (x = y) with e | e
    · subst e; exact h0
    · rcases Classical.em (P.lt x y) with l | l
      · exact h1 y l
      · rcases Classical.em (P.lt y x) with g' | g'
        · exact h2 y g'
        · exact h3 y ⟨e, l, g'⟩
  · intro h
    exact ⟨h x, fun y _ => h y, fun y _ => h y, fun y _ => h y⟩

theorem holds_iff_body (S : PatSys) :
    S.Holds P val ↔ ∀ x, psat P val x (bodyC S) := by
  constructor
  · rintro ⟨hf, hq⟩ x
    refine ⟨?_, ?_⟩
    · rw [psat_conjL_map]
      intro f hfm
      exact (psat_forbC P val x f).mpr (fun hx y hr => hf f hfm x y hx hr)
    · rw [psat_conjL_map]
      intro q hqm
      exact (psat_reqC P val x q).mpr (fun hx => hq q hqm x hx)
  · intro h
    refine ⟨?_, ?_⟩
    · intro f hfm x y hx hr
      have h1 := (h x).1
      rw [psat_conjL_map] at h1
      exact (psat_forbC P val x f).mp (h1 f hfm) hx y hr
    · intro q hqm x hx
      have h2 := (h x).2
      rw [psat_conjL_map] at h2
      exact (psat_reqC P val x q).mp (h2 q hqm) hx

end PatSem

/-- A pattern system is satisfiable iff its concept is. -/
theorem patsys_bridge (S : PatSys) : S.Sat ↔ PSatisfiable S.toConcept := by
  constructor
  · rintro ⟨α, P, val, ⟨x⟩, h⟩
    exact ⟨α, P, val, x,
      (psat_univC P val x (bodyC S)).mpr ((holds_iff_body P val S).mp h)⟩
  · rintro ⟨α, P, val, x, h⟩
    exact ⟨α, P, val, ⟨x⟩,
      (holds_iff_body P val S).mpr ((psat_univC P val x (bodyC S)).mp h)⟩

/-- **TWO-VARIABLE LOGIC OVER STRICT PARTIAL ORDERS REDUCES TO ALCI_RCC5.** -/
theorem patsys_to_rcc5 (S : PatSys) :
    S.Sat ↔ Satisfiable (emb S.toConcept) :=
  (patsys_bridge S).trans (poset_bridge S.toConcept)

/-- Hence a decision procedure for the full logic decides it. -/
def decidablePatSat_of_full (h : ∀ C : Concept, Decidable (Satisfiable C))
    (S : PatSys) : Decidable S.Sat :=
  @decidable_of_iff _ _ (patsys_to_rcc5 S).symm (h (emb S.toConcept))

/-! ## §5  The spiral: an infinity axiom with incomparable witnesses only -/

/-- Marzec & Tendera's `Φ_spiral`: five predicates; every element carries one;
    `A_i ◁▷ A_{i+2}` (no `A_i` is incomparable to an `A_{i+2}`); and every
    `A_i` has an incomparable `A_{i+1}` and an incomparable `A_{i-1}`. -/
def spiralSys : PatSys where
  forb := (List.range 5).map fun i =>
    ([(i, true)], PRole.inc, [((i + 2) % 5, true)])
  req :=
    ([], (List.range 5).map fun i => (PRole.eq, [(i, true)])) ::
    (((List.range 5).map fun i =>
        ([(i, true)], [(PRole.inc, [((i + 1) % 5, true)])])) ++
     ((List.range 5).map fun i =>
        ([(i, true)], [(PRole.inc, [((i + 4) % 5, true)])])))

theorem litsHold_single {α : Type} (val : Nat → α → Prop) (x : α) (a : Nat) :
    litsHold val x [(a, true)] ↔ val a x := by
  constructor
  · intro h; exact h (a, true) (.head _)
  · intro h l hl
    cases hl with
    | head => exact h
    | tail _ hl => exact nomatch hl

theorem litsHold_nil {α : Type} (val : Nat → α → Prop) (x : α) :
    litsHold val x [] := fun _ hl => nomatch hl

section SpiralFacts

variable {α : Type} (P : SPO α) (val : Nat → α → Prop)
  (h : spiralSys.Holds P val)

include h

theorem spiral_exh (x : α) : ∃ i, i < 5 ∧ val i x := by
  have hq := h.2 ([], (List.range 5).map fun i => (PRole.eq, [(i, true)]))
    (.head _) x (litsHold_nil val x)
  obtain ⟨o, ho, y, hr, hy⟩ := hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ho
  have e : x = y := hr
  subst e
  exact ⟨i, List.mem_range.mp hi, (litsHold_single val x i).mp hy⟩

theorem spiral_ent (i : Nat) (hi : i < 5) (x y : α) (hx : val i x)
    (hxy : P.inc x y) : ¬ val ((i + 2) % 5) y := by
  have hf := h.1 ([(i, true)], PRole.inc, [((i + 2) % 5, true)])
    (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩) x y
    ((litsHold_single val x i).mpr hx) hxy
  exact fun hy => hf ((litsHold_single val y _).mpr hy)

theorem spiral_next (i : Nat) (hi : i < 5) (x : α) (hx : val i x) :
    ∃ y, P.inc x y ∧ val ((i + 1) % 5) y := by
  have hq := h.2 ([(i, true)], [(PRole.inc, [((i + 1) % 5, true)])])
    (.tail _ (List.mem_append.mpr (Or.inl
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))) x
    ((litsHold_single val x i).mpr hx)
  obtain ⟨o, ho, y, hr, hy⟩ := hq
  cases ho with
  | head => exact ⟨y, hr, (litsHold_single val y _).mp hy⟩
  | tail _ ho => exact nomatch ho

theorem spiral_prev (i : Nat) (hi : i < 5) (x : α) (hx : val i x) :
    ∃ y, P.inc x y ∧ val ((i + 4) % 5) y := by
  have hq := h.2 ([(i, true)], [(PRole.inc, [((i + 4) % 5, true)])])
    (.tail _ (List.mem_append.mpr (Or.inr
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))) x
    ((litsHold_single val x i).mpr hx)
  obtain ⟨o, ho, y, hr, hy⟩ := hq
  cases ho with
  | head => exact ⟨y, hr, (litsHold_single val y _).mp hy⟩
  | tail _ ho => exact nomatch ho

/-- No element carries both `A_i` and `A_{i+2}`: the first needs an
    incomparable `A_{i+4}`, the second forbids one. -/
theorem spiral_no_two (i : Nat) (hi : i < 5) (x : α) (hx : val i x)
    (hx2 : val ((i + 2) % 5) x) : False := by
  obtain ⟨y, hxy, hy⟩ := spiral_prev P val h i hi x hx
  have hn := spiral_ent P val h ((i + 2) % 5) (Nat.mod_lt _ (by decide)) x y
    hx2 hxy
  have e : ((i + 2) % 5 + 2) % 5 = (i + 4) % 5 := by omega
  rw [e] at hn
  exact hn hy

end SpiralFacts

/-! ### The order-theoretic core: a walk that must run upward forever -/

section Walk

variable {α : Type} (P : SPO α) (w : Nat → α)
  (hinc : ∀ k, P.inc (w k) (w (k + 1)))
  (hc2 : ∀ k, P.lt (w k) (w (k + 2)) ∨ P.lt (w (k + 2)) (w k))
  (hc3 : ∀ k, P.lt (w k) (w (k + 3)) ∨ P.lt (w (k + 3)) (w k))

include hinc hc2 hc3 in
/-- The direction of the first comparable pair propagates along the walk. -/
theorem walk_dir (h0 : P.lt (w 0) (w 2)) : ∀ k, P.lt (w k) (w (k + 2)) := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    rcases hc2 (k + 1) with h | h
    · exact h
    · exfalso
      have h' : P.lt (w (k + 3)) (w (k + 1)) := h
      rcases hc3 k with h3 | h3
      · exact (hinc k).2.1 (P.tr _ _ _ h3 h')
      · exact (hinc (k + 2)).2.2 (P.tr _ _ _ h3 ih)

include hinc hc3 in
theorem walk_dir3 (h2 : ∀ k, P.lt (w k) (w (k + 2))) :
    ∀ k, P.lt (w k) (w (k + 3)) := by
  intro k
  rcases hc3 k with h | h
  · exact h
  · exfalso
    have h21 : P.lt (w (k + 1)) (w (k + 3)) := h2 (k + 1)
    exact (hinc k).2.2 (P.tr _ _ _ h21 h)

/-- Steps of two and three reach every distance `≥ 2`. -/
theorem walk_far (h2 : ∀ k, P.lt (w k) (w (k + 2)))
    (h3 : ∀ k, P.lt (w k) (w (k + 3))) :
    ∀ d k, P.lt (w k) (w (k + (d + 2))) := by
  have key : ∀ d, (∀ k, P.lt (w k) (w (k + (d + 2)))) ∧
      (∀ k, P.lt (w k) (w (k + (d + 3)))) := by
    intro d
    induction d with
    | zero => exact ⟨h2, h3⟩
    | succ d ih =>
      refine ⟨ih.2, ?_⟩
      intro k
      have a := ih.1 k
      have b := h2 (k + (d + 2))
      have e : k + (d + 2) + 2 = k + (d + 1 + 3) := by omega
      rw [e] at b
      exact P.tr _ _ _ a b
  intro d
  exact (key d).1

include hinc in
theorem walk_inj_of_dir (h2 : ∀ k, P.lt (w k) (w (k + 2)))
    (h3 : ∀ k, P.lt (w k) (w (k + 3))) :
    ∀ m n, m < n → w m ≠ w n := by
  intro m n hmn e
  rcases Nat.lt_or_ge n (m + 2) with hlt | hge
  · have e1 : n = m + 1 := by omega
    subst e1
    exact (hinc m).1 e
  · obtain ⟨d, rfl⟩ : ∃ d, n = m + (d + 2) := ⟨n - m - 2, by omega⟩
    have hfar := walk_far P w h2 h3 d m
    rw [← e] at hfar
    exact P.irr _ hfar

end Walk

/-- The dual order. -/
def SPO.dual {α : Type} (P : SPO α) : SPO α where
  lt := fun a b => P.lt b a
  irr := P.irr
  tr := fun x y z h1 h2 => P.tr z y x h2 h1

/-- **THE WALK LEMMA.**  In a strict partial order, a sequence whose
    consecutive members are incomparable and whose members at distance two and
    three are comparable is injective. -/
theorem walk_inj {α : Type} (P : SPO α) (w : Nat → α)
    (hinc : ∀ k, P.inc (w k) (w (k + 1)))
    (hc2 : ∀ k, P.lt (w k) (w (k + 2)) ∨ P.lt (w (k + 2)) (w k))
    (hc3 : ∀ k, P.lt (w k) (w (k + 3)) ∨ P.lt (w (k + 3)) (w k)) :
    ∀ m n, m < n → w m ≠ w n := by
  rcases hc2 0 with h0 | h0
  · have h2 := walk_dir P w hinc hc2 hc3 h0
    have h3 := walk_dir3 P w hinc hc3 h2
    exact walk_inj_of_dir P w hinc h2 h3
  · have hinc' : ∀ k, P.dual.inc (w k) (w (k + 1)) :=
      fun k => ⟨(hinc k).1, (hinc k).2.2, (hinc k).2.1⟩
    have hc2' : ∀ k, P.dual.lt (w k) (w (k + 2)) ∨ P.dual.lt (w (k + 2)) (w k) :=
      fun k => (hc2 k).symm
    have hc3' : ∀ k, P.dual.lt (w k) (w (k + 3)) ∨ P.dual.lt (w (k + 3)) (w k) :=
      fun k => (hc3 k).symm
    have h2 := walk_dir P.dual w hinc' hc2' hc3' h0
    have h3 := walk_dir3 P.dual w hinc' hc3' h2
    exact walk_inj_of_dir P.dual w hinc' h2 h3

section SpiralInfinite

variable {α : Type} (P : SPO α) (val : Nat → α → Prop)
  (h : spiralSys.Holds P val)

/-- A point together with one of its colours. -/
def SpSt (val : Nat → α → Prop) : Type :=
  {p : α × Nat // p.2 < 5 ∧ val p.2 p.1}

/-- One step along the spiral: an incomparable point of the next colour. -/
noncomputable def spStep (s : SpSt val) : SpSt val :=
  ⟨(Classical.choose (spiral_next P val h s.1.2 s.2.1 s.1.1 s.2.2),
      (s.1.2 + 1) % 5),
    Nat.mod_lt _ (by decide),
    (Classical.choose_spec (spiral_next P val h s.1.2 s.2.1 s.1.1 s.2.2)).2⟩

theorem spStep_inc (s : SpSt val) : P.inc s.1.1 (spStep P val h s).1.1 :=
  (Classical.choose_spec (spiral_next P val h s.1.2 s.2.1 s.1.1 s.2.2)).1

noncomputable def spWalk (s0 : SpSt val) : Nat → SpSt val
  | 0 => s0
  | k + 1 => spStep P val h (spWalk s0 k)

theorem spWalk_ty (s0 : SpSt val) (k : Nat) :
    (spWalk P val h s0 (k + 1)).1.2 = ((spWalk P val h s0 k).1.2 + 1) % 5 := rfl

include h in
/-- **EVERY MODEL OF THE SPIRAL IS INFINITE.** -/
theorem spiral_infinite (hne : Nonempty α) :
    ∃ f : Nat → α, ∀ m n, m < n → f m ≠ f n := by
  obtain ⟨x0⟩ := hne
  obtain ⟨i0, hi0, hv0⟩ := spiral_exh P val h x0
  let s0 : SpSt val := ⟨(x0, i0), hi0, hv0⟩
  let st : Nat → SpSt val := spWalk P val h s0
  let w : Nat → α := fun k => (st k).1.1
  let ty : Nat → Nat := fun k => (st k).1.2
  have hty : ∀ k, ty k < 5 := fun k => (st k).2.1
  have hval : ∀ k, val (ty k) (w k) := fun k => (st k).2.2
  have hstep : ∀ k, ty (k + 1) = (ty k + 1) % 5 := fun k => rfl
  have hinc : ∀ k, P.inc (w k) (w (k + 1)) := fun k => spStep_inc P val h (st k)
  have hty2 : ∀ k, ty (k + 2) = (ty k + 2) % 5 := by
    intro k
    have a : ty (k + 1) = (ty k + 1) % 5 := hstep k
    have b : ty (k + 2) = (ty (k + 1) + 1) % 5 := hstep (k + 1)
    have c := hty k
    omega
  have hty3 : ∀ k, (ty (k + 3) + 2) % 5 = ty k := by
    intro k
    have a := hty2 k
    have b : ty (k + 3) = (ty (k + 2) + 1) % 5 := hstep (k + 2)
    have c := hty k
    omega
  -- distance two: comparable
  have hc2 : ∀ k, P.lt (w k) (w (k + 2)) ∨ P.lt (w (k + 2)) (w k) := by
    intro k
    have hv2 : val ((ty k + 2) % 5) (w (k + 2)) := by
      have := hval (k + 2)
      rw [hty2 k] at this
      exact this
    have hne : w k ≠ w (k + 2) := by
      intro e
      rw [← e] at hv2
      exact spiral_no_two P val h (ty k) (hty k) (w k) (hval k) hv2
    apply Classical.byContradiction
    intro hno
    have hi : P.inc (w k) (w (k + 2)) :=
      ⟨hne, fun l => hno (Or.inl l), fun l => hno (Or.inr l)⟩
    exact spiral_ent P val h (ty k) (hty k) (w k) (w (k + 2)) (hval k) hi hv2
  -- distance three: comparable
  have hc3 : ∀ k, P.lt (w k) (w (k + 3)) ∨ P.lt (w (k + 3)) (w k) := by
    intro k
    have hvk : val ((ty (k + 3) + 2) % 5) (w k) := by
      rw [hty3 k]
      exact hval k
    have hne : w k ≠ w (k + 3) := by
      intro e
      rw [e] at hvk
      exact spiral_no_two P val h (ty (k + 3)) (hty (k + 3)) (w (k + 3))
        (hval (k + 3)) hvk
    apply Classical.byContradiction
    intro hno
    have hi : P.inc (w (k + 3)) (w k) :=
      ⟨fun e => hne e.symm, fun l => hno (Or.inr l), fun l => hno (Or.inl l)⟩
    exact spiral_ent P val h (ty (k + 3)) (hty (k + 3)) (w (k + 3)) (w k)
      (hval (k + 3)) hi hvk
  exact ⟨w, walk_inj P w hinc hc2 hc3⟩

end SpiralInfinite

/-! ### The ℤ-spiral is a model -/

/-- `a < b` iff `b` is at least two steps on: consecutive integers are
    incomparable. -/
def zSpiral : SPO Int where
  lt := fun a b => a + 2 ≤ b
  irr := by intro x h; omega
  tr := by intro x y z h1 h2; omega

def zVal : Nat → Int → Prop := fun a n => n % 5 = (a : Int)

theorem zSpiral_holds : spiralSys.Holds zSpiral zVal := by
  refine ⟨?_, ?_⟩
  · intro f hf x y hx hr hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    have hi' : i < 5 := List.mem_range.mp hi
    have hx' : x % 5 = (i : Int) := (litsHold_single zVal x i).mp hx
    have hy' : y % 5 = (((i + 2) % 5 : Nat) : Int) :=
      (litsHold_single zVal y _).mp hy
    have h1 : x ≠ y := hr.1
    have h2 : ¬ x + 2 ≤ y := hr.2.1
    have h3 : ¬ y + 2 ≤ x := hr.2.2
    omega
  · intro q hq x hx
    cases hq with
    | head =>
      have hcase : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
        omega
      have key : ∀ i : Nat, i < 5 → x % 5 = (i : Int) →
          ∃ o, o ∈ (List.range 5).map (fun i => (PRole.eq, [(i, true)])) ∧
            ∃ y, zSpiral.rel o.1 x y ∧ litsHold zVal y o.2 := by
        intro i hi hxi
        exact ⟨(PRole.eq, [(i, true)]),
          List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, x, rfl,
          (litsHold_single zVal x i).mpr hxi⟩
      rcases hcase with e | e | e | e | e
      · exact key 0 (by decide) e
      · exact key 1 (by decide) e
      · exact key 2 (by decide) e
      · exact key 3 (by decide) e
      · exact key 4 (by decide) e
    | tail _ hq =>
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
        have hi' : i < 5 := List.mem_range.mp hi
        have hx' : x % 5 = (i : Int) := (litsHold_single zVal x i).mp hx
        refine ⟨(PRole.inc, [((i + 1) % 5, true)]), .head _, x + 1, ?_, ?_⟩
        · show x ≠ x + 1 ∧ ¬ x + 2 ≤ x + 1 ∧ ¬ x + 1 + 2 ≤ x
          omega
        · apply (litsHold_single zVal (x + 1) _).mpr
          show (x + 1) % 5 = (((i + 1) % 5 : Nat) : Int)
          omega
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
        have hi' : i < 5 := List.mem_range.mp hi
        have hx' : x % 5 = (i : Int) := (litsHold_single zVal x i).mp hx
        refine ⟨(PRole.inc, [((i + 4) % 5, true)]), .head _, x - 1, ?_, ?_⟩
        · show x ≠ x - 1 ∧ ¬ x + 2 ≤ x - 1 ∧ ¬ x - 1 + 2 ≤ x
          omega
        · apply (litsHold_single zVal (x - 1) _).mpr
          show (x - 1) % 5 = (((i + 4) % 5 : Nat) : Int)
          omega

/-- **THE SPIRAL IS SATISFIABLE.** -/
theorem spiral_sat : spiralSys.Sat :=
  ⟨Int, zSpiral, zVal, ⟨0⟩, zSpiral_holds⟩

/-! ## §6  The same, inside ALCI_RCC5 -/

/-- The spiral as an ALCI_RCC5 concept. -/
def spiralConcept : Concept := emb spiralSys.toConcept

/-- No `∃PP` and no `∃PPI`. -/
def noExVertB : Concept → Bool
  | .top => true
  | .bot => true
  | .atom _ => true
  | .natom _ => true
  | .and c d => noExVertB c && noExVertB d
  | .or c d => noExVertB c && noExVertB d
  | .ex r c => decide (r ≠ pp) && decide (r ≠ ppi) && noExVertB c
  | .all _ c => noExVertB c

/-- The spiral concept has no vertical existential: its only witnesses are
    `∃PO`, `∃DR` and the trivial `∃EQ`. -/
theorem spiralConcept_noExVert : noExVertB spiralConcept = true := by decide

/-- **THE SPIRAL CONCEPT IS SATISFIABLE.** -/
theorem spiralConcept_sat : Satisfiable spiralConcept :=
  (patsys_to_rcc5 spiralSys).mp spiral_sat

/-- **EVERY RCC5 MODEL OF THE SPIRAL CONCEPT IS INFINITE** -- an infinity axiom
    of ALCI_RCC5 that asks for no proper part and no proper superpart. -/
theorem spiralConcept_infinite {α : Type} (I : Interp α) (hI : RCC5Interp I)
    (x : α) (hx : I.dom x) (h : sat I x spiralConcept) :
    ∃ f : Nat → α, (∀ n, I.dom (f n)) ∧ ∀ m n, m < n → f m ≠ f n := by
  have hp := truth_down I hI spiralSys.toConcept ⟨x, hx⟩ h
  have hb := (psat_univC (spoOf I hI) (fun n b => I.val n b.1) ⟨x, hx⟩
    (bodyC spiralSys)).mp hp
  have hh := (holds_iff_body (spoOf I hI) (fun n b => I.val n b.1)
    spiralSys).mpr hb
  obtain ⟨f, hf⟩ := spiral_infinite (spoOf I hI) (fun n b => I.val n b.1) hh
    ⟨⟨x, hx⟩⟩
  exact ⟨fun n => (f n).1, fun n => (f n).2,
    fun m n hmn e => hf m n hmn (Subtype.ext e)⟩

/-! ## §7  K2: two overlap-witnesses that must be nested

`K2 = ∃PO.(A ⊓ ∀PO.¬B ⊓ ∀DR.¬B) ⊓ ∃PO.(B ⊓ ¬A)`.

The first witness forbids a `B` among the regions it overlaps and among the
regions it is disjoint from; the second witness is a `B` and a different
region. So the two witnesses can be neither `PO` nor `DR` to each other: they
are NESTED. A three-point model exists (`r`, and `a ⊂ b`, both overlapping
`r`), so `K2` is satisfiable.

This is the horizontal sibling of the overview's `C_sat` (whose two witnesses
are `PP`-witnesses). It matters for the prototype reasoner: the cover-tree
tableau (`src/cover_tree_tableau.py`, `check_cover_tree_siblings`) requires any
two `DR`/`PO` witnesses of one node to be related by `DR` or `PO`, and therefore
answers UNSAT on `K2` (`wp137`, part E). `k2_sat` is the kernel-checked other
half of that disagreement. -/

/-- `K2` in the poset logic: both witnesses via a bare `∃PO`. -/
def k2p : PConcept :=
  .and (.xpo (.and (.atom 0) (.all .inc (.natom 1))))
       (.xpo (.and (.atom 1) (.natom 0)))

/-- `K2` as an ALCI_RCC5 concept. -/
def k2 : Concept := emb k2p

/-- Its shape, spelled out. -/
theorem k2_shape :
    k2 = .and
      (.ex po (.and (.atom 0) (.and (.all po (.natom 1)) (.all dr (.natom 1)))))
      (.ex po (.and (.atom 1) (.natom 0))) := rfl

/-- Three points: a root `r`, and `a` below `b`. -/
inductive V3 | r | a | b
deriving DecidableEq

def v3 : SPO V3 where
  lt := fun x y => x = V3.a ∧ y = V3.b
  irr := by
    intro x h
    have h1 := h.1
    have h2 := h.2
    rw [h1] at h2
    exact V3.noConfusion h2
  tr := by
    intro x y z h1 h2
    have e1 := h1.2
    have e2 := h2.1
    rw [e1] at e2
    exact V3.noConfusion e2

def v3val : Nat → V3 → Prop :=
  fun n x => (n = 0 ∧ x = V3.a) ∨ (n = 1 ∧ x = V3.b)

theorem k2p_sat : PSatisfiable k2p := by
  refine ⟨V3, v3, v3val, V3.r, ?_, ?_⟩
  · refine ⟨V3.a, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact fun e => V3.noConfusion e
    · exact fun h => V3.noConfusion h.1
    · exact fun h => V3.noConfusion h.2
    · exact Or.inl ⟨rfl, rfl⟩
    · intro z hz hv
      rcases hv with ⟨h0, _⟩ | ⟨_, hb⟩
      · exact absurd h0 (by decide)
      · exact hz.2.1 ⟨rfl, hb⟩
  · refine ⟨V3.b, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact fun e => V3.noConfusion e
    · exact fun h => V3.noConfusion h.1
    · exact fun h => V3.noConfusion h.1
    · exact Or.inr ⟨rfl, rfl⟩
    · intro hv
      rcases hv with ⟨_, hb⟩ | ⟨h1, _⟩
      · exact V3.noConfusion hb
      · exact absurd h1 (by decide)

/-- **`K2` IS SATISFIABLE** -- in the artifact's own `Satisfiable`. -/
theorem k2_sat : Satisfiable k2 := (poset_bridge k2p).mp k2p_sat

/-- And in every model its two witnesses are nested: a region satisfying the
    first witness concept is never `PO` and never `DR` to a `B`-region. -/
theorem k2_witnesses_nested {α : Type} (I : Interp α) (a b : α)
    (hb : I.dom b)
    (ha : sat I a (.and (.atom 0) (.and (.all po (.natom 1)) (.all dr (.natom 1)))))
    (hB : sat I b (.and (.atom 1) (.natom 0))) :
    I.rho a b ≠ po ∧ I.rho a b ≠ dr :=
  ⟨fun h => ha.2.1 b hb h hB.1, fun h => ha.2.2 b hb h hB.1⟩

/-! ## §8  `C_cyc`: in the vertical-witness slice a `∀PO` conjunct can decide

Three proper superparts `a ∈ A`, `b ∈ B`, `c ∈ C` of one region.  `a` allows no
`B` beside it and none below it, so `a ⊂ b`; likewise `b ⊂ c` and `c ⊂ a`.
Each pair is fine on its own; the three together are a cycle.  So `C_cyc` is
UNSATISFIABLE -- and it becomes satisfiable as soon as its three `∀PO`
conjuncts are erased, because the three witnesses may then overlap pairwise.

`C_cyc` has no `∃PO` and no `∃DR`: it lies in the slice of the incomparability
fragment that Szwast & Tendera's theorem decides (through `poset_bridge`), and
it shows that in that slice a `∀PO` constraint is not erasable -- unlike in the
fragment `𝒟` of §299 of the artifact. -/

/-- "I am a `p`, not a `q`, and every `q` is strictly above me." -/
def wit (p q : Nat) : PConcept :=
  .and (.atom p) (.and (.natom q)
    (.and (.all .inc (.natom q)) (.all .gt (.natom q))))

/-- The same with the `∀PO` conjunct erased: `∀∥` becomes a bare `∀DR`. -/
def witE (p q : Nat) : PConcept :=
  .and (.atom p) (.and (.natom q)
    (.and (.adr (.natom q)) (.all .gt (.natom q))))

def ccycP : PConcept :=
  .and (.ex .lt (wit 0 1)) (.and (.ex .lt (wit 1 2)) (.ex .lt (wit 2 0)))

def ccycE : PConcept :=
  .and (.ex .lt (witE 0 1)) (.and (.ex .lt (witE 1 2)) (.ex .lt (witE 2 0)))

/-- `C_cyc` as an ALCI_RCC5 concept, and its `∀PO`-erasure. -/
def ccyc : Concept := emb ccycP
def ccycErased : Concept := emb ccycE

theorem ccyc_shape :
    ccyc = .and
      (.ex pp (.and (.atom 0) (.and (.natom 1)
        (.and (.and (.all po (.natom 1)) (.all dr (.natom 1)))
          (.all ppi (.natom 1))))))
      (.and
        (.ex pp (.and (.atom 1) (.and (.natom 2)
          (.and (.and (.all po (.natom 2)) (.all dr (.natom 2)))
            (.all ppi (.natom 2))))))
        (.ex pp (.and (.atom 2) (.and (.natom 0)
          (.and (.and (.all po (.natom 0)) (.all dr (.natom 0)))
            (.all ppi (.natom 0))))))) := rfl

theorem ccycErased_shape :
    ccycErased = .and
      (.ex pp (.and (.atom 0) (.and (.natom 1)
        (.and (.all dr (.natom 1)) (.all ppi (.natom 1))))))
      (.and
        (.ex pp (.and (.atom 1) (.and (.natom 2)
          (.and (.all dr (.natom 2)) (.all ppi (.natom 2))))))
        (.ex pp (.and (.atom 2) (.and (.natom 0)
          (.and (.all dr (.natom 0)) (.all ppi (.natom 0))))))) := rfl

/-- A witness of `wit p q` lies strictly below every OTHER region that is a `q`. -/
theorem wit_below {α : Type} (P : SPO α) (val : Nat → α → Prop) {p q : Nat}
    {x y : α} (hx : psat P val x (wit p q)) (hy : val q y) : P.lt x y := by
  obtain ⟨_, hnq, hinc, hgt⟩ := hx
  have hne : x ≠ y := by
    intro e
    rw [e] at hnq
    exact hnq hy
  apply Classical.byContradiction
  intro hlt
  rcases Classical.em (P.lt y x) with hyx | hyx
  · exact hgt y hyx hy
  · exact hinc y ⟨hne, hlt, hyx⟩ hy

theorem ccycP_unsat : ¬ PSatisfiable ccycP := by
  rintro ⟨α, P, val, r, ⟨a, _, ha⟩, ⟨b, _, hb⟩, ⟨c, _, hc⟩⟩
  have hab : P.lt a b := wit_below P val ha hb.1
  have hbc : P.lt b c := wit_below P val hb hc.1
  have hca : P.lt c a := wit_below P val hc ha.1
  exact P.irr a (P.tr _ _ _ (P.tr _ _ _ hab hbc) hca)

/-- **`C_cyc` IS UNSATISFIABLE.** -/
theorem ccyc_unsat : ¬ Satisfiable ccyc :=
  fun h => ccycP_unsat ((poset_bridge ccycP).mpr h)

/-- A root with three pairwise incomparable regions above it. -/
inductive V4 | r | a | b | c
deriving DecidableEq

def v4 : SPO V4 where
  lt := fun x y => x = V4.r ∧ y ≠ V4.r
  irr := by
    intro x h
    exact h.2 h.1
  tr := by
    intro x y z h1 h2
    exact absurd h2.1 h1.2

def v4val : Nat → V4 → Prop :=
  fun n x => (n = 0 ∧ x = V4.a) ∨ (n = 1 ∧ x = V4.b) ∨ (n = 2 ∧ x = V4.c)

theorem ccycE_psat : PSatisfiable ccycE := by
  refine ⟨V4, v4, v4val, V4.r, ⟨V4.a, ?_, ?_, ?_, True.intro, ?_⟩,
    ⟨V4.b, ?_, ?_, ?_, True.intro, ?_⟩, ⟨V4.c, ?_, ?_, ?_, True.intro, ?_⟩⟩
  -- witness a : an A, not a B, no B below
  · exact ⟨rfl, fun e => V4.noConfusion e⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩)
    · exact absurd h (by decide)
    · exact V4.noConfusion h
    · exact absurd h (by decide)
  · rintro y hy (⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩)
    · exact absurd h (by decide)
    · have e : y = V4.r := hy.1
      rw [e] at h
      exact V4.noConfusion h
    · exact absurd h (by decide)
  -- witness b : a B, not a C, no C below
  · exact ⟨rfl, fun e => V4.noConfusion e⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact V4.noConfusion h
  · rintro y hy (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · have e : y = V4.r := hy.1
      rw [e] at h
      exact V4.noConfusion h
  -- witness c : a C, not an A, no A below
  · exact ⟨rfl, fun e => V4.noConfusion e⟩
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
    · exact V4.noConfusion h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · rintro y hy (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
    · have e : y = V4.r := hy.1
      rw [e] at h
      exact V4.noConfusion h
    · exact absurd h (by decide)
    · exact absurd h (by decide)

/-- **ERASE ITS `∀PO` CONJUNCTS AND `C_cyc` IS SATISFIABLE.** -/
theorem ccycErased_sat : Satisfiable ccycErased :=
  (poset_bridge ccycE).mp ccycE_psat

end PosetBridge
end POFreeLift

#print axioms POFreeLift.PosetBridge.poset_bridge
#print axioms POFreeLift.PosetBridge.poset_bridge_fin
#print axioms POFreeLift.PosetBridge.decidablePSat_of_full
#print axioms POFreeLift.PosetBridge.decidablePSat_noAllInc
#print axioms POFreeLift.PosetBridge.patsys_to_rcc5
#print axioms POFreeLift.PosetBridge.decidablePatSat_of_full
#print axioms POFreeLift.PosetBridge.walk_inj
#print axioms POFreeLift.PosetBridge.spiral_sat
#print axioms POFreeLift.PosetBridge.spiral_infinite
#print axioms POFreeLift.PosetBridge.spiralConcept_noExVert
#print axioms POFreeLift.PosetBridge.spiralConcept_sat
#print axioms POFreeLift.PosetBridge.spiralConcept_infinite
#print axioms POFreeLift.PosetBridge.k2_sat
#print axioms POFreeLift.PosetBridge.k2_witnesses_nested
#print axioms POFreeLift.PosetBridge.ccyc_unsat
#print axioms POFreeLift.PosetBridge.ccycErased_sat
