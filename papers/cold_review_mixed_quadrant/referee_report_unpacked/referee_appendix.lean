/-! ############################################################################
    REFEREE APPENDIX — attached to POFreeLift.lean for checking only.

    TARGET: the §51.1 claim, asserted in the docstring of `amLt`
    ("WHY THE CAP CARRIES NO DISJOINTNESS — forced, not chosen … So a cap is
    always a POSET-shaped structure: PP/PPI/PO/EQ only") and in
    ASSEMBLY_DESIGN_43_60.md §51.1 ("`amDisj` is not a simplification: a cap is
    always poset-shaped").

    The argument given supports only CAP↔CAP: two caps above a common nonempty
    `U` cannot be disjoint, because `djDown` would make a member of `U`
    disjoint from itself.  It says nothing about CAP↔BASE.  `amDisj` /
    `capSeed` nevertheless send EVERY cap-involving pair to `False`.

    Part 1 below generalises `odAmalg` to carry a cap↔base disjointness `B`
    and proves the result is still an `ODStruct` — so `odNet_frame` still
    applies and no composition cell is checked by hand.  The side conditions
    are exactly §58.2's `hdbase` and §51.2's `cofinal_dr_all`.

    Part 2 exhibits a concrete instance in which a cap sits PP-above a
    downward-closed `U` and carries a genuine `DR` edge to a base node — the
    edge `cap_no_dr_edge` proves cannot exist in the shipped construction.
############################################################################ -/

namespace RefereeCapDR

open POFreeLift
open Atom

variable {N : Type}

/-- The order: `odAmalg`'s `amLt`, restated locally so this appendix is
    self-contained. -/
def amLtR (S : ODStruct N) (U : N → Prop) {M : Type} (P : M → M → Prop) :
    N ⊕ M → N ⊕ M → Prop
  | .inl x, .inl y => S.lt x y
  | .inl x, .inr _ => U x
  | .inr a, .inr b => P a b
  | .inr _, .inl _ => False

/-- Disjointness: the base's, PLUS declared cap↔base pairs `B`.  Cap↔cap stays
    empty — THAT part §51.1 really does force. -/
def amDisjR (S : ODStruct N) {M : Type} (B : M → N → Prop) :
    N ⊕ M → N ⊕ M → Prop
  | .inl x, .inl y => S.disj x y
  | .inl x, .inr m => B m x
  | .inr m, .inl x => B m x
  | .inr _, .inr _ => False

/-- **THE CAP MAY CARRY BASE DISJOINTNESS.**  `odAmalg` with a cap↔base
    disjointness relation `B`, still ordered-disjoint.

    Side conditions, all of them §51.2's own statement of what a cap's `DR`
    partner must be:

    * `hBnotU` — a cap is not disjoint from anything it is above;
    * `hBdown` / `hBP` — `B` is downward closed in the base and along `P`;
    * `hBU`   — a cap's `DR` partner is base-disjoint from the WHOLE closure.
      This is §58.2's `hdbase`, and `cofinal_dr_all` supplies it on the model
      side.

    `B = fun _ _ => False` recovers `odAmalg` exactly, so this is a strict
    generalisation, not a replacement. -/
def odAmalgDR (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) {M : Type} (P : M → M → Prop)
    (hPirr : ∀ a, ¬ P a a) (hPtr : ∀ a b c, P a b → P b c → P a c)
    (B : M → N → Prop)
    (hBnotU : ∀ m x, B m x → ¬ U x)
    (hBdown : ∀ m x x', B m x → S.lt x' x → B m x')
    (hBP : ∀ m m' x, B m x → P m' m → B m' x)
    (hBU : ∀ m x u, B m x → U u → S.disj x u) :
    ODStruct (N ⊕ M) where
  lt := amLtR S U P
  disj := amDisjR S B
  ltIrr := by
    rintro (a | a)
    · exact S.ltIrr a
    · exact hPirr a
  ltTr := by
    rintro (a | a) (b | b) (c | c) h1 h2
    · exact S.ltTr a b c h1 h2
    · exact hdown a b h1 h2
    · exact h2.elim
    · exact h1
    · exact h1.elim
    · exact h1.elim
    · exact h2.elim
    · exact hPtr a b c h1 h2
  djSym := by
    rintro (x | m) (y | m') h
    · exact S.djSym x y h
    · exact h
    · exact h
    · exact h
  djIrr := by
    rintro (x | m) h
    · exact S.djIrr x h
    · exact h
  ltNotDj := by
    rintro (x | m) (y | m') hlt hdj
    · exact S.ltNotDj x y hlt hdj
    · exact hBnotU m' x hdj hlt
    · exact hlt.elim
    · exact hdj
  djDown := by
    rintro (x | m) (y | m') (x' | n) (y' | n') hdj hx hy
    -- 1  base,base,base,base
    · refine S.djDown x y x' y' hdj ?_ ?_
      · rcases hx with h | h
        · exact Or.inl (Sum.inl.inj h)
        · exact Or.inr h
      · rcases hy with h | h
        · exact Or.inl (Sum.inl.inj h)
        · exact Or.inr h
    -- 2  y' a cap under a base y : impossible
    · rcases hy with h | h
      · exact absurd h (inr_ne_inl _ _)
      · exact h.elim
    -- 3, 4  x' a cap under a base x : impossible
    · rcases hx with h | h
      · exact absurd h (inr_ne_inl _ _)
      · exact h.elim
    · rcases hx with h | h
      · exact absurd h (inr_ne_inl _ _)
      · exact h.elim
    -- 5  hdj : B m' x ; x' base, y' base with U y'
    · have hx' : B m' x' := by
        rcases hx with h | h
        · rw [Sum.inl.inj h]; exact hdj
        · exact hBdown m' x x' hdj h
      have hUy' : U y' := by
        rcases hy with h | h
        · exact absurd h.symm (inr_ne_inl _ _)
        · exact h
      exact hBU m' x' y' hx' hUy'
    -- 6  x' base, y' a cap at or under m'
    · have hx' : B m' x' := by
        rcases hx with h | h
        · rw [Sum.inl.inj h]; exact hdj
        · exact hBdown m' x x' hdj h
      rcases hy with h | h
      · rw [← Sum.inr.inj h] at hx'; exact hx'
      · exact hBP m' n' x' hx' h
    -- 7, 8  x' a cap under a base x : impossible
    · rcases hx with h | h
      · exact absurd h (inr_ne_inl _ _)
      · exact h.elim
    · rcases hx with h | h
      · exact absurd h (inr_ne_inl _ _)
      · exact h.elim
    -- 9  hdj : B m y ; x' base with U x', y' base under y
    · have hy' : B m y' := by
        rcases hy with h | h
        · rw [Sum.inl.inj h]; exact hdj
        · exact hBdown m y y' hdj h
      have hUx' : U x' := by
        rcases hx with h | h
        · exact absurd h.symm (inr_ne_inl _ _)
        · exact h
      exact S.djSym _ _ (hBU m y' x' hy' hUx')
    -- 10  y' a cap under a base y : impossible
    · rcases hy with h | h
      · exact absurd h (inr_ne_inl _ _)
      · exact h.elim
    -- 11  x' a cap at or under m, y' base under y
    · have hy' : B m y' := by
        rcases hy with h | h
        · rw [Sum.inl.inj h]; exact hdj
        · exact hBdown m y y' hdj h
      rcases hx with h | h
      · rw [← Sum.inr.inj h] at hy'; exact hy'
      · exact hBP m n y' hy' h
    -- 12  y' a cap under a base y : impossible
    · rcases hy with h | h
      · exact absurd h (inr_ne_inl _ _)
      · exact h.elim
    -- 13-16  cap,cap : hdj is False
    · exact hdj.elim
    · exact hdj.elim
    · exact hdj.elim
    · exact hdj.elim

/-- `odNet_frame` applies unchanged: composition closure for free, exactly as
    for `odAmalg`. -/
theorem odAmalgDR_frame (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) {M : Type} (P : M → M → Prop)
    (hPirr : ∀ a, ¬ P a a) (hPtr : ∀ a b c, P a b → P b c → P a c)
    (B : M → N → Prop)
    (hBnotU : ∀ m x, B m x → ¬ U x)
    (hBdown : ∀ m x x', B m x → S.lt x' x → B m x')
    (hBP : ∀ m m' x, B m x → P m' m → B m' x)
    (hBU : ∀ m x u, B m x → U u → S.disj x u) :
    Frame (odNet (odAmalgDR S U hdown P hPirr hPtr B hBnotU hBdown hBP hBU)) :=
  odNet_frame _

/-- The cap really does get a `DR` edge. -/
theorem odAmalgDR_dr (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) {M : Type} (P : M → M → Prop)
    (hPirr : ∀ a, ¬ P a a) (hPtr : ∀ a b c, P a b → P b c → P a c)
    (B : M → N → Prop)
    (hBnotU : ∀ m x, B m x → ¬ U x)
    (hBdown : ∀ m x x', B m x → S.lt x' x → B m x')
    (hBP : ∀ m m' x, B m x → P m' m → B m' x)
    (hBU : ∀ m x u, B m x → U u → S.disj x u)
    {m : M} {f : N} (h : B m f) :
    odNet (odAmalgDR S U hdown P hPirr hPtr B hBnotU hBdown hBP hBU)
      (Sum.inr m) (Sum.inl f) = dr :=
  odNet_dj _ h

/-- And it is still above the closure. -/
theorem odAmalgDR_pp (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) {M : Type} (P : M → M → Prop)
    (hPirr : ∀ a, ¬ P a a) (hPtr : ∀ a b c, P a b → P b c → P a c)
    (B : M → N → Prop)
    (hBnotU : ∀ m x, B m x → ¬ U x)
    (hBdown : ∀ m x x', B m x → S.lt x' x → B m x')
    (hBP : ∀ m m' x, B m x → P m' m → B m' x)
    (hBU : ∀ m x u, B m x → U u → S.disj x u)
    {m : M} {e : N} (h : U e) :
    odNet (odAmalgDR S U hdown P hPirr hPtr B hBnotU hBdown hBP hBU)
      (Sum.inl e) (Sum.inr m) = pp :=
  odNet_lt _ h

/-! ### Part 2 — a concrete cap with a `DR` edge

Base = `Bool`.  `true` is the closure `U`; `false` is a base node disjoint from
everything in `U` (`S.disj x y := x ≠ y`).  One cap.  The cap is `PP`-above
`true` and `DR` from `false`. -/

def baseS : ODStruct Bool where
  lt := fun _ _ => False
  disj := fun x y => x ≠ y
  ltIrr := fun _ h => h
  ltTr := fun _ _ _ h _ => h.elim
  djSym := fun _ _ h => fun hh => h hh.symm
  djIrr := fun _ h => h rfl
  ltNotDj := fun _ _ h => h.elim
  djDown := by
    intro x y x' y' hd hx hy
    rcases hx with rfl | h
    · rcases hy with rfl | h'
      · exact hd
      · exact h'.elim
    · exact h.elim

def capU : Bool → Prop := fun x => x = true

def capB : Unit → Bool → Prop := fun _ x => x = false

def witnessStruct : ODStruct (Bool ⊕ Unit) :=
  odAmalgDR baseS capU (fun _ _ h _ => h.elim) (fun _ _ : Unit => False)
    (fun _ h => h) (fun _ _ _ h _ => h.elim) capB
    (by
      intro m x h
      rw [show x = false from h]
      exact fun hh => Bool.noConfusion hh)
    (by intro m x x' _ hlt; exact hlt.elim)
    (by intro m m' x _ hP; exact hP.elim)
    (by
      intro m x u h hu
      show x ≠ u
      rw [show x = false from h, show u = true from hu]
      exact fun hh => Bool.noConfusion hh)

/-- The cap is `PP`-above the closure … -/
theorem witness_pp :
    odNet witnessStruct (Sum.inl true) (Sum.inr ()) = pp :=
  odNet_lt _ (show witnessStruct.lt (Sum.inl true) (Sum.inr ()) from rfl)

/-- … and `DR` from a base node.  `cap_no_dr_edge` proves this edge is
    impossible in `odSeedCap`; it is not impossible in an `ODStruct`. -/
theorem witness_dr :
    odNet witnessStruct (Sum.inr ()) (Sum.inl false) = dr :=
  odNet_dj _ (show witnessStruct.disj (Sum.inr ()) (Sum.inl false) from rfl)

/-- The whole thing is a genuine RCC5 frame. -/
theorem witness_frame : Frame (odNet witnessStruct) := odNet_frame _

end RefereeCapDR

#print axioms RefereeCapDR.odAmalgDR
#print axioms RefereeCapDR.odAmalgDR_frame
#print axioms RefereeCapDR.witness_dr
#print axioms RefereeCapDR.witness_frame
