/-
  POFreeLift.lean  (2026-07-18)

  The two-tier "chain-unfolding lift" lemma, certified in Lean 4 core.

  This is the SOUNDNESS CRUX of the two-tier quotient decidability argument
  for the PO-coherent (hence ∀PO-free) fragment of ALCI_RCC5
  (papers/two_tier_quotient_ALCIRCC5.tex, Lemma "Chain-unfolding lift").
  It was machine-stress-tested in verification/python/wp86; here it is a
  kernel-checked theorem.

  Statement.  Let `E : β → β → Atom` be the external-external RCC5 labelling
  and `K : β → Atom` the kernel's constant interface row (K e = ρ(kernel, e)).
  Form the augmented one-point network `aug` on `Option β` (none = kernel).
  If `aug` is composition-consistent (CC = every ordered triple closed under
  the RCC5 table) and the kernel is distinct from every external (strong-EQ:
  K e ≠ EQ), then replacing the kernel by an infinite PP-chain (ℕ) under the
  constant interface -- the network `unf` on `β ⊕ ℕ` -- is STILL CC.

  Since CC atomic RCC5 networks are globally consistent (patchwork / Renz &
  Nebel) modulo compactness, a CC unfolding is a genuine model witness, so
  this is exactly the step that turns a finite valid quotient into an
  (infinite) model.

  Crucially, CC here means EVERY ordered triple is closed, which SUBSUMES
  multi-path (joint) PO forcing -- so the argument does NOT assume "PO edges
  are free" (the 16th review's concern); it enforces full composition
  closure, and the lift preserves it.

  The composition/converse tables are copied verbatim from the certified
  artifact `RCC5NormalForm.lean` (no table-input risk).

  Build (Lean 4 core, no mathlib):  lean POFreeLift.lean
-/

namespace POFreeLift

/-- The five RCC5 base relations. -/
inductive Atom | eq | pp | ppi | po | dr
deriving DecidableEq, Repr

open Atom

/-- Converse (verbatim from the certified artifact). -/
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

/-! ### Algebraic facts used by the lift (finite, `decide`-checked) -/

/-- Right self-absorption for a PROPER `S` (needed since `comp EQ pp = [pp]`
    would fail for `S = EQ`): `S ∈ comp S c` for `c ∈ {PP,EQ,PPI}`. -/
theorem self_right (S c : Atom) (hS : S ≠ eq)
    (h : c = pp ∨ c = eq ∨ c = ppi) : S ∈ comp S c := by
  cases S with
  | eq => exact absurd rfl hS
  | pp => rcases h with h | h | h <;> subst h <;> decide
  | ppi => rcases h with h | h | h <;> subst h <;> decide
  | po => rcases h with h | h | h <;> subst h <;> decide
  | dr => rcases h with h | h | h <;> subst h <;> decide

/-- Left self-absorption for a proper `S`: `S ∈ comp c S`. -/
theorem self_left (S c : Atom) (hS : S ≠ eq)
    (h : c = pp ∨ c = eq ∨ c = ppi) : S ∈ comp c S := by
  cases S with
  | eq => exact absurd rfl hS
  | pp => rcases h with h | h | h <;> subst h <;> decide
  | ppi => rcases h with h | h | h <;> subst h <;> decide
  | po => rcases h with h | h | h <;> subst h <;> decide
  | dr => rcases h with h | h | h <;> subst h <;> decide

/-- For a proper (non-`EQ`) `S`, `comp S (conv S)` contains all of `PP`, `EQ`,
    `PPI`. Backs the "external between two chain elements" triple; this is
    where strong-EQ (`S ≠ EQ`) is needed (`comp EQ EQ = {EQ}` would fail). -/
theorem conv_super (S : Atom) (h : S ≠ eq) :
    pp ∈ comp S (conv S) ∧ eq ∈ comp S (conv S) ∧ ppi ∈ comp S (conv S) := by
  cases S with
  | eq => exact absurd rfl h
  | pp => decide
  | ppi => decide
  | po => decide
  | dr => decide

/-- Converse preserves properness. -/
theorem conv_ne_eq (S : Atom) (h : S ≠ eq) : conv S ≠ eq := by
  cases S with
  | eq => exact absurd rfl h
  | pp => decide
  | ppi => decide
  | po => decide
  | dr => decide

/-- Converse is an involution. -/
theorem conv_invol (S : Atom) : conv (conv S) = S := by cases S <;> rfl

/-! ### The chain interface -/

/-- The within-chain relation: strictly earlier is `PP`, equal is `EQ`,
    later is `PPI`. -/
def chain (i j : Nat) : Atom := if i < j then pp else if i = j then eq else ppi

theorem chain_lt {i j : Nat} (h : i < j) : chain i j = pp := by
  unfold chain; rw [if_pos h]

theorem chain_self (i : Nat) : chain i i = eq := by
  unfold chain; rw [if_neg (by omega : ¬ i < i), if_pos rfl]

theorem chain_gt {i j : Nat} (h : j < i) : chain i j = ppi := by
  unfold chain; rw [if_neg (by omega : ¬ i < j), if_neg (by omega : ¬ i = j)]

theorem chain_vals (i j : Nat) :
    chain i j = pp ∨ chain i j = eq ∨ chain i j = ppi := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact Or.inl (chain_lt h)
  · subst h; exact Or.inr (Or.inl (chain_self i))
  · exact Or.inr (Or.inr (chain_gt h))

/-- The chain is composition-consistent within itself:
    `chain i k ∈ comp (chain i j) (chain j k)` for all positions. -/
theorem chain_cc (i j k : Nat) :
    chain i k ∈ comp (chain i j) (chain j k) := by
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
    · simp only [chain_lt hij, chain_lt hjk, chain_lt (Nat.lt_trans hij hjk)]; decide
    · subst hjk; simp only [chain_lt hij, chain_self]; decide
    · simp only [chain_lt hij, chain_gt hjk]
      rcases chain_vals i k with h | h | h <;> simp only [h] <;> decide
  · subst hij
    simp only [chain_self]
    rcases chain_vals i k with h | h | h <;> simp only [h] <;> decide
  · rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
    · simp only [chain_gt hij, chain_lt hjk]
      rcases chain_vals i k with h | h | h <;> simp only [h] <;> decide
    · subst hjk; simp only [chain_gt hij, chain_self]; decide
    · simp only [chain_gt hij, chain_gt hjk, chain_gt (Nat.lt_trans hjk hij)]; decide

/-- The chain is converse-coherent: `chain j i = conv (chain i j)`. -/
theorem chain_conv (i j : Nat) : chain j i = conv (chain i j) := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · rw [chain_lt h, chain_gt h]; rfl
  · subst h; rw [chain_self]; rfl
  · rw [chain_gt h, chain_lt h]; rfl

/-- The chain is strong-EQ: `chain i j = EQ` only on the diagonal. -/
theorem chain_eq_imp {i j : Nat} (h : chain i j = eq) : i = j := by
  rcases Nat.lt_trichotomy i j with hlt | he | hgt
  · rw [chain_lt hlt] at h; exact absurd h (by decide)
  · exact he
  · rw [chain_gt hgt] at h; exact absurd h (by decide)

/-! ### The augmented one-point network and its unfolding -/

variable {β : Type}

/-- The augmented network on `Option β`: `none` is the kernel, `some e` an
    external node. `aug` being CC is the "valid quotient at this kernel"
    hypothesis. -/
def aug (E : β → β → Atom) (K : β → Atom) : Option β → Option β → Atom
  | none, none => eq
  | none, some e => K e
  | some e, none => conv (K e)
  | some e, some f => E e f

/-- The unfolded network on `β ⊕ ℕ`: externals keep `E`; the kernel is
    replaced by the ℕ-indexed PP-chain under the CONSTANT interface
    (`ρ(d_i, e) = K e`). -/
def unf (E : β → β → Atom) (K : β → Atom) : (β ⊕ Nat) → (β ⊕ Nat) → Atom
  | Sum.inl e, Sum.inl f => E e f
  | Sum.inl e, Sum.inr _ => conv (K e)
  | Sum.inr _, Sum.inl f => K f
  | Sum.inr i, Sum.inr j => chain i j

/-- THE CHAIN-UNFOLDING LIFT: if the augmented one-point network is CC and
    the kernel is distinct from every external (`K e ≠ EQ`), then the
    unfolded network is CC. Proof is the eight-case ordered-triple analysis:
    the four externals-and-kernel cases reduce to the CC hypothesis; the four
    cases touching two chain elements reduce to the algebraic facts above. -/
theorem lift_cc (E : β → β → Atom) (K : β → Atom)
    (Hcc : ∀ x y z, aug E K x z ∈ comp (aug E K x y) (aug E K y z))
    (Kproper : ∀ e, K e ≠ eq) :
    ∀ x y z, unf E K x z ∈ comp (unf E K x y) (unf E K y z) := by
  intro x y z
  rcases x with e | i <;> rcases y with f | j <;> rcases z with g | k <;>
    simp only [unf]
  · -- (ext e, ext f, ext g)
    simpa only [aug] using Hcc (some e) (some f) (some g)
  · -- (ext e, ext f, chain k)
    simpa only [aug] using Hcc (some e) (some f) none
  · -- (ext e, chain j, ext g)
    simpa only [aug] using Hcc (some e) none (some g)
  · -- (ext e, chain j, chain k)
    exact self_right (conv (K e)) (chain j k)
      (conv_ne_eq (K e) (Kproper e)) (chain_vals j k)
  · -- (chain i, ext f, ext g)
    simpa only [aug] using Hcc none (some f) (some g)
  · -- (chain i, ext f, chain k): external between two chain elements
    obtain ⟨hpp, heq, hppi⟩ := conv_super (K f) (Kproper f)
    rcases chain_vals i k with hc | hc | hc <;> rw [hc] <;> assumption
  · -- (chain i, chain j, ext g)
    exact self_left (K g) (chain i j) (Kproper g) (chain_vals i j)
  · -- (chain i, chain j, chain k)
    exact chain_cc i j k

/-! ### From lift to a genuine RCC5 frame (abstract semantics)

Under the abstract composition-table semantics a model IS a total labelling
that is reflexive-EQ, strong-EQ (EQ only on the diagonal), converse-coherent,
and composition-closed (CC).  So no patchwork/compactness is needed for the
CORE unfolded network: once we show the unfolding satisfies all four frame
conditions, it *is* an ALCI_RCC5 frame.  (Patchwork enters only for the
off-chain-witness refinement, condition V6, which is separate.) -/

/-- A strong-EQ atomic RCC5 frame: a total labelling that is reflexive-EQ,
    strong-EQ, converse-coherent, and composition-closed. This is exactly the
    frame part of `RCC5Interp` in the normative artifact. -/
structure Frame {V : Type} (N : V → V → Atom) : Prop where
  refl_eq : ∀ x, N x x = eq
  eq_id : ∀ x y, N x y = eq → x = y
  conv_ : ∀ x y, N y x = conv (N x y)
  comp_ : ∀ x y z, N x z ∈ comp (N x y) (N y z)

/-- THE FRAME LIFT: if the augmented one-point network is a genuine RCC5 frame
    (finite valid atomic quotient) and the kernel is distinct from every
    external, then the infinite chain-unfolding is a genuine RCC5 frame. So a
    valid atomic quotient unfolds to an actual model of the abstract semantics
    — with no patchwork/compactness required for the core network. -/
theorem unf_is_frame (E : β → β → Atom) (K : β → Atom)
    (h : Frame (aug E K)) (Kproper : ∀ e, K e ≠ eq) :
    Frame (unf E K) where
  refl_eq := by
    intro x
    rcases x with e | i
    · simpa only [unf, aug] using h.refl_eq (some e)
    · simp only [unf]; exact chain_self i
  eq_id := by
    intro x y hxy
    rcases x with e | i <;> rcases y with f | j
    · -- inl e, inl f
      simp only [unf] at hxy
      have hae : aug E K (some e) (some f) = eq := by simpa only [aug] using hxy
      exact congrArg Sum.inl (Option.some.inj (h.eq_id (some e) (some f) hae))
    · -- inl e, inr j: conv (K e) = eq is impossible
      simp only [unf] at hxy
      exact absurd hxy (conv_ne_eq (K e) (Kproper e))
    · -- inr i, inl f: K f = eq is impossible
      simp only [unf] at hxy
      exact absurd hxy (Kproper f)
    · -- inr i, inr j
      simp only [unf] at hxy
      rw [chain_eq_imp hxy]
  conv_ := by
    intro x y
    rcases x with e | i <;> rcases y with f | j
    · simpa only [unf, aug] using h.conv_ (some e) (some f)
    · simp only [unf, conv_invol]
    · simp only [unf]
    · simp only [unf]; exact chain_conv i j
  comp_ := lift_cc E K h.comp_ Kproper

/-! ### Non-vacuity: the hypotheses are inhabitable

With `β = Empty` (no external nodes), `aug` is trivially CC and the kernel
condition is vacuous, so the lift applies and the unfolded network (a pure
PP-chain) is CC. -/

theorem lift_nonvacuous :
    ∀ x y z,
      unf (β := Empty) (fun e _ => e.elim) (fun e => e.elim) x z
        ∈ comp (unf (fun e _ => e.elim) (fun e => e.elim) x y)
               (unf (fun e _ => e.elim) (fun e => e.elim) y z) := by
  apply lift_cc
  · intro x y z
    cases x with
    | some e => exact e.elim
    | none =>
      cases y with
      | some e => exact e.elim
      | none =>
        cases z with
        | some e => exact e.elim
        | none => decide
  · intro e; exact e.elim

/-- Frame-level non-vacuity: the empty external world unfolds to a pure
    PP-chain, which is a genuine RCC5 frame. -/
theorem frame_nonvacuous :
    Frame (unf (β := Empty) (fun e _ => e.elim) (fun e => e.elim)) := by
  apply unf_is_frame
  · exact
      { refl_eq := by intro x; cases x with
          | some e => exact e.elim
          | none => rfl
        eq_id := by intro x y hxy; cases x with
          | some e => exact e.elim
          | none => cases y with
            | some e => exact e.elim
            | none => rfl
        conv_ := by intro x y; cases x with
          | some e => exact e.elim
          | none => cases y with
            | some e => exact e.elim
            | none => rfl
        comp_ := by intro x y z; cases x with
          | some e => exact e.elim
          | none => cases y with
            | some e => exact e.elim
            | none => cases z with
              | some e => exact e.elim
              | none => decide }
  · intro e; exact e.elim

#print axioms lift_cc
#print axioms unf_is_frame

end POFreeLift
