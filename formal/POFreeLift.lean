/-
  POFreeLift.lean  (2026-07-18; extended 2026-07-22)

  The two-tier "chain-unfolding lift" lemma, certified in Lean 4 core —
  and (2026-07-22, fragment-certification ROUND A, see the section
  header further down) the logic layer over the unfolding: the two-tier
  single-kernel certificate, its Hintikka labelling, the truth lemma,
  and the capstone `twoTier_sound` (valid certificate ⟹ Satisfiable),
  with the no-finite-model witness `cinf_satisfiable`.

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

/-! ## Round A of the fragment certification (2026-07-22): the logic layer

The sections below extend the certified lift toward an END-TO-END
kernel-checked decidability theorem for the ∀PO-free fragment, along the
established two-tier route (papers/two_tier_quotient_ALCIRCC5.tex;
explainer papers/WHY_PO_FREE_IS_DECIDABLE.md).

Round A = SOUNDNESS through the logic: a two-tier single-kernel
certificate (finite external part + one kernel with cyclic phase types +
constant interfaces), stated as propositional validity conditions, yields
an actual RCC5 model of the concept — via a Hintikka labelling on the
`unf` unfolding and a truth lemma.  The definitions of `Concept`,
`Interp`, `sat`, `Hintikka`, `truth_lemma`, `RCC5Interp`, `Satisfiable`
MIRROR the normative artifact `Round19Transport.lean` (same constructor
set, same satisfaction clauses, same satisfiability shape), so a future
bridge between the two files is transcription.

Deliberately NOT in round A (the roadmap, in order):
  B. multi-kernel certificates (iterate the lift: `Frame N` on `V` +
     a designated node ⟹ `Frame` on `{x // x ≠ v} ⊕ ℕ`), descending
     (PPI) kernels by converse symmetry;
  C. an executable Boolean checker + `Decidable` instances for the
     validity conditions (the round-29 `finAcceptB` pattern);
  D. the completeness extraction: every satisfiable ∀PO-free concept
     admits a valid certificate within K(C₀) — the two-tier paper's
     extraction (period descriptors, stabilization, backward forcing /
     forward absorption, automatic PO-coherence), which is where
     `POFree` does its work.  Note the PO-padding fact proved useful
     here: a constant-PO kernel interface is ALWAYS frame-valid (PO is
     in every cell of the PO row/column), so the mandatory kernel is no
     obstruction to presenting finite models — the "escape valve" of
     the explainer, doing formal work.
-/

/-! ### Concepts and satisfaction (mirroring the normative artifact) -/

/-- ALCI_RCC5 concepts in NNF; inverse roles absorbed (roles are the five
    RCC5 atoms). Same constructors as the normative artifact. -/
inductive Concept
  | top | bot
  | atom (a : Nat)
  | natom (a : Nat)
  | and (c d : Concept)
  | or (c d : Concept)
  | ex (r : Atom) (c : Concept)
  | all (r : Atom) (c : Concept)
deriving DecidableEq, Repr

/-- An interpretation: a domain predicate, the atomic RCC5 relation, and
    an atomic-concept extension. Mirrors the normative artifact. -/
structure Interp (α : Type) where
  dom : α → Prop
  rho : α → α → Atom
  val : Nat → α → Prop

/-- Satisfaction, structural on the concept. Mirrors the normative
    artifact clause for clause. -/
def sat {α : Type} (I : Interp α) : α → Concept → Prop
  | _, .top => True
  | _, .bot => False
  | x, .atom a => I.val a x
  | x, .natom a => ¬ I.val a x
  | x, .and c d => sat I x c ∧ sat I x d
  | x, .or c d => sat I x c ∨ sat I x d
  | x, .ex r c => ∃ y, I.dom y ∧ I.rho x y = r ∧ sat I y c
  | x, .all r c => ∀ y, I.dom y → I.rho x y = r → sat I y c

/-- What makes an interpretation a legitimate ALCI_RCC5 model (mirrors
    the normative `RCC5Interp`): reflexive-EQ, strong-EQ = identity,
    converse-coherent, composition-closed — relative to the domain. -/
structure RCC5Interp {α : Type} (I : Interp α) : Prop where
  refl_eq : ∀ x, I.dom x → I.rho x x = eq
  eq_id : ∀ x y, I.dom x → I.dom y → I.rho x y = eq → x = y
  conv_ : ∀ x y, I.dom x → I.dom y → I.rho y x = conv (I.rho x y)
  comp_ : ∀ x y z, I.dom x → I.dom y → I.dom z →
    I.rho x z ∈ comp (I.rho x y) (I.rho y z)

/-- Concept satisfiability over an RCC5 frame (carrier-polymorphic;
    mirrors the normative artifact). -/
def Satisfiable (C0 : Concept) : Prop :=
  ∃ (α : Type), ∃ I : Interp α, RCC5Interp I ∧ ∃ x, I.dom x ∧ sat I x C0

/-- A total `Frame` is an `RCC5Interp` with full domain (bridge from the
    lift layer to the logic layer). -/
theorem frame_rcc5 {V : Type} (N : V → V → Atom) (h : Frame N)
    (val : Nat → V → Prop) :
    RCC5Interp ⟨fun _ => True, N, val⟩ where
  refl_eq := fun x _ => h.refl_eq x
  eq_id := fun x y _ _ hxy => h.eq_id x y hxy
  conv_ := fun x y _ _ => h.conv_ x y
  comp_ := fun x y z _ _ _ => h.comp_ x y z

/-! ### Hintikka labellings and the truth lemma -/

/-- The canonical interpretation induced by a type labelling: an atom
    holds exactly where its concept is in the type. -/
def typeInterp {α : Type} (dom : α → Prop) (rho : α → α → Atom)
    (τ : α → List Concept) : Interp α :=
  ⟨dom, rho, fun a x => Concept.atom a ∈ τ x⟩

/-- A Hintikka system: a locally coherent type labelling (clash-free and
    bot-free literals; ∧/∨ decomposed; ∀ propagated to r-neighbours; ∃
    fulfilled by an actual r-neighbour = one-step fulfilment). Mirrors
    the normative artifact, generalized to an arbitrary carrier. -/
structure Hintikka {α : Type} (dom : α → Prop) (rho : α → α → Atom)
    (τ : α → List Concept) : Prop where
  clashfree : ∀ x a, dom x → Concept.atom a ∈ τ x → Concept.natom a ∉ τ x
  nobot : ∀ x, dom x → Concept.bot ∉ τ x
  and_c : ∀ x c d, dom x → Concept.and c d ∈ τ x → c ∈ τ x ∧ d ∈ τ x
  or_c : ∀ x c d, dom x → Concept.or c d ∈ τ x → c ∈ τ x ∨ d ∈ τ x
  all_c : ∀ x r c, dom x → Concept.all r c ∈ τ x →
    ∀ y, dom y → rho x y = r → c ∈ τ y
  ex_f : ∀ x r c, dom x → Concept.ex r c ∈ τ x →
    ∃ y, dom y ∧ rho x y = r ∧ c ∈ τ y

/-- THE TRUTH LEMMA: every concept in a node's type is satisfied there,
    under the canonical interpretation. Structural induction; each case
    is one Hintikka clause plus the induction hypotheses. Mirrors the
    normative artifact. -/
theorem truth_lemma {α : Type} (dom : α → Prop) (rho : α → α → Atom)
    (τ : α → List Concept) (H : Hintikka dom rho τ) :
    ∀ C x, dom x → C ∈ τ x → sat (typeInterp dom rho τ) x C := by
  intro C
  induction C with
  | top => intro x _ _; exact True.intro
  | bot => intro x hx hmem; exact absurd hmem (H.nobot x hx)
  | atom a => intro x _ hmem; exact hmem
  | natom a => intro x hx hmem hval; exact H.clashfree x a hx hval hmem
  | and c d ihc ihd =>
    intro x hx hmem
    obtain ⟨hc, hd⟩ := H.and_c x c d hx hmem
    exact ⟨ihc x hx hc, ihd x hx hd⟩
  | or c d ihc ihd =>
    intro x hx hmem
    cases H.or_c x c d hx hmem with
    | inl h => exact Or.inl (ihc x hx h)
    | inr h => exact Or.inr (ihd x hx h)
  | ex r c ihc =>
    intro x hx hmem
    obtain ⟨y, hy, hr, hcy⟩ := H.ex_f x r c hx hmem
    exact ⟨y, hy, hr, ihc y hy hcy⟩
  | all r c ihc =>
    intro x hx hmem y hy hr
    exact ihc y hy (H.all_c x r c hx hmem y hy hr)

/-- Any total frame carrying a Hintikka labelling with `C0` at some node
    is a model of `C0`: frame conditions + truth lemma. Works for ANY
    carrier — a finite network directly, or the `unf` unfolding. -/
theorem sat_from_hintikka_frame {V : Type} (N : V → V → Atom)
    (hf : Frame N) (τ : V → List Concept)
    (H : Hintikka (fun _ => True) N τ)
    (root : V) (C0 : Concept) (hC0 : C0 ∈ τ root) :
    Satisfiable C0 :=
  ⟨V, typeInterp (fun _ => True) N τ,
    frame_rcc5 N hf _,
    root, True.intro,
    truth_lemma _ N τ H C0 root True.intro hC0⟩

/-! ### The two-tier single-kernel certificate

Data: a finite-in-spirit external part (`E`, `K`, external types `tauE` —
stated over an arbitrary carrier `β`; the finite/decidable instantiation
is round C) plus ONE ascending kernel with `p` cyclic phase types.  The
generated structure is the `unf` unfolding: externals keep `E`, the
kernel becomes the ℕ-chain, every chain node relates to external `e` by
the CONSTANT interface `conv (K e)` / `K e`, and chain node `i` carries
phase type `phase (i % p)`.

The validity conditions (`TwoTierOk`) are exactly the Hintikka
obligations of the unfolding, quotiented by its finitely many EDGE
CLASSES: ext–ext edges carry `E`; ext–chain edges carry the constant
interface against EVERY phase (each phase occurs at infinitely many
rungs); chain–chain edges carry `PP` upward / `PPI` downward between
EVERY ordered pair of phases (any two residues occur in either order),
and `EQ` on the diagonal.  Existential demands are fulfilled by
designated external witnesses, chain-internally upward (`PP`, at any
phase — a later rung of every residue exists), or reflexively (`EQ`).
Round-A restriction, by design: no chain-internal `PPI` fulfilment
(rung 0 has no chain predecessor); the extraction (round D) uses
stabilized external `PPI`-witnesses instead, per the two-tier paper's
forward-absorption discipline. -/

structure TwoTier (β : Type) where
  E : β → β → Atom
  K : β → Atom
  tauE : β → List Concept
  p : Nat
  phase : Nat → List Concept

/-- The type labelling of the unfolding. -/
def ttLabel (T : TwoTier β) : (β ⊕ Nat) → List Concept
  | Sum.inl e => T.tauE e
  | Sum.inr i => T.phase (i % T.p)

/-- Validity of a two-tier certificate: the frame hypotheses of the
    certified lift + the Hintikka obligations per edge class. -/
structure TwoTierOk (T : TwoTier β) : Prop where
  hp : 0 < T.p
  frame_aug : Frame (aug T.E T.K)
  kproper : ∀ e, T.K e ≠ eq
  -- propositional coherence, externals
  e_clash : ∀ e a, Concept.atom a ∈ T.tauE e → Concept.natom a ∉ T.tauE e
  e_nobot : ∀ e, Concept.bot ∉ T.tauE e
  e_and : ∀ e c d, Concept.and c d ∈ T.tauE e → c ∈ T.tauE e ∧ d ∈ T.tauE e
  e_or : ∀ e c d, Concept.or c d ∈ T.tauE e → c ∈ T.tauE e ∨ d ∈ T.tauE e
  -- propositional coherence, phases
  k_clash : ∀ a, a < T.p → ∀ n, Concept.atom n ∈ T.phase a →
    Concept.natom n ∉ T.phase a
  k_nobot : ∀ a, a < T.p → Concept.bot ∉ T.phase a
  k_and : ∀ a, a < T.p → ∀ c d, Concept.and c d ∈ T.phase a →
    c ∈ T.phase a ∧ d ∈ T.phase a
  k_or : ∀ a, a < T.p → ∀ c d, Concept.or c d ∈ T.phase a →
    c ∈ T.phase a ∨ d ∈ T.phase a
  -- universal propagation, per edge class of the unfolding
  ee_all : ∀ e f r c, Concept.all r c ∈ T.tauE e → T.E e f = r →
    c ∈ T.tauE f
  ek_all : ∀ e r c, Concept.all r c ∈ T.tauE e → conv (T.K e) = r →
    ∀ a, a < T.p → c ∈ T.phase a
  ke_all : ∀ a, a < T.p → ∀ r c, Concept.all r c ∈ T.phase a →
    ∀ f, T.K f = r → c ∈ T.tauE f
  kk_pp : ∀ a, a < T.p → ∀ c, Concept.all pp c ∈ T.phase a →
    ∀ b, b < T.p → c ∈ T.phase b
  kk_ppi : ∀ a, a < T.p → ∀ c, Concept.all ppi c ∈ T.phase a →
    ∀ b, b < T.p → c ∈ T.phase b
  kk_eq : ∀ a, a < T.p → ∀ c, Concept.all eq c ∈ T.phase a →
    c ∈ T.phase a
  -- existential fulfilment, per node class
  e_ex : ∀ e r c, Concept.ex r c ∈ T.tauE e →
    (∃ f, T.E e f = r ∧ c ∈ T.tauE f) ∨
    (conv (T.K e) = r ∧ ∃ a, a < T.p ∧ c ∈ T.phase a)
  k_ex : ∀ a, a < T.p → ∀ r c, Concept.ex r c ∈ T.phase a →
    (∃ f, T.K f = r ∧ c ∈ T.tauE f) ∨
    (r = pp ∧ ∃ b, b < T.p ∧ c ∈ T.phase b) ∨
    (r = eq ∧ c ∈ T.phase a)

/-- Arithmetic for chain-internal `PP` fulfilment: above any rung `i`
    there is a rung of every phase residue `b < p`. -/
theorem exists_later_phase (p : Nat) (hp : 0 < p) (i b : Nat)
    (hb : b < p) : ∃ j, i < j ∧ j % p = b := by
  refine ⟨p * (i / p + 1) + b, ?_, ?_⟩
  · have h1 := Nat.div_add_mod i p
    have h2 := Nat.mod_lt i hp
    have h3 : p * (i / p + 1) = p * (i / p) + p := Nat.mul_succ p (i / p)
    omega
  · rw [Nat.add_comm (p * (i / p + 1)) b, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hb

/-- ROUND-A CENTRAL LEMMA: a valid two-tier certificate's labelling is a
    Hintikka labelling of the unfolding.  Each Hintikka clause reduces to
    the edge-class condition covering the node/edge class at hand; the
    chain-side arithmetic is `Nat.mod_lt` (every rung has a phase) and
    `exists_later_phase` (every phase recurs above every rung). -/
theorem twoTier_hintikka (T : TwoTier β) (h : TwoTierOk T) :
    Hintikka (fun _ => True) (unf T.E T.K) (ttLabel T) where
  clashfree := by
    intro x a _ hmem
    rcases x with e | i
    · exact h.e_clash e a hmem
    · exact h.k_clash (i % T.p) (Nat.mod_lt i h.hp) a hmem
  nobot := by
    intro x _
    rcases x with e | i
    · exact h.e_nobot e
    · exact h.k_nobot (i % T.p) (Nat.mod_lt i h.hp)
  and_c := by
    intro x c d _ hmem
    rcases x with e | i
    · exact h.e_and e c d hmem
    · exact h.k_and (i % T.p) (Nat.mod_lt i h.hp) c d hmem
  or_c := by
    intro x c d _ hmem
    rcases x with e | i
    · exact h.e_or e c d hmem
    · exact h.k_or (i % T.p) (Nat.mod_lt i h.hp) c d hmem
  all_c := by
    intro x r c _ hmem y _ hr
    rcases x with e | i <;> rcases y with f | j
    · -- ext → ext
      exact h.ee_all e f r c hmem hr
    · -- ext → chain: constant interface, every phase occurs
      exact h.ek_all e r c hmem hr (j % T.p) (Nat.mod_lt j h.hp)
    · -- chain → ext: constant interface
      exact h.ke_all (i % T.p) (Nat.mod_lt i h.hp) r c hmem f hr
    · -- chain → chain: PP upward / EQ diagonal / PPI downward
      have hr' : chain i j = r := hr
      have hm' : Concept.all r c ∈ T.phase (i % T.p) := hmem
      rcases Nat.lt_trichotomy i j with hij | hij | hij
      · rw [chain_lt hij] at hr'; subst hr'
        exact h.kk_pp (i % T.p) (Nat.mod_lt i h.hp) c hm'
          (j % T.p) (Nat.mod_lt j h.hp)
      · subst hij
        rw [chain_self] at hr'; subst hr'
        exact h.kk_eq (i % T.p) (Nat.mod_lt i h.hp) c hm'
      · rw [chain_gt hij] at hr'; subst hr'
        exact h.kk_ppi (i % T.p) (Nat.mod_lt i h.hp) c hm'
          (j % T.p) (Nat.mod_lt j h.hp)
  ex_f := by
    intro x r c _ hmem
    rcases x with e | i
    · rcases h.e_ex e r c hmem with ⟨f, hEf, hcf⟩ | ⟨hK, a, ha, hca⟩
      · exact ⟨Sum.inl f, True.intro, hEf, hcf⟩
      · refine ⟨Sum.inr a, True.intro, hK, ?_⟩
        show c ∈ T.phase (a % T.p)
        rw [Nat.mod_eq_of_lt ha]
        exact hca
    · have hm' : Concept.ex r c ∈ T.phase (i % T.p) := hmem
      rcases h.k_ex (i % T.p) (Nat.mod_lt i h.hp) r c hm' with
        ⟨f, hKf, hcf⟩ | ⟨hrpp, b, hb, hcb⟩ | ⟨hreq, hc⟩
      · exact ⟨Sum.inl f, True.intro, hKf, hcf⟩
      · obtain ⟨j, hij, hjb⟩ := exists_later_phase T.p h.hp i b hb
        refine ⟨Sum.inr j, True.intro, ?_, ?_⟩
        · show chain i j = r
          rw [chain_lt hij, hrpp]
        · show c ∈ T.phase (j % T.p)
          rw [hjb]
          exact hcb
      · refine ⟨Sum.inr i, True.intro, ?_, ?_⟩
        · show chain i i = r
          rw [chain_self, hreq]
        · exact hc

/-- ROUND-A CAPSTONE: a valid two-tier certificate with the target
    concept at some node yields an actual RCC5 model — soundness of the
    certificate through the LOGIC, end to end: certified lift
    (`unf_is_frame`) + Hintikka construction + truth lemma. -/
theorem twoTier_sound (T : TwoTier β) (h : TwoTierOk T)
    (root : β ⊕ Nat) (C0 : Concept) (hC0 : C0 ∈ ttLabel T root) :
    Satisfiable C0 :=
  sat_from_hintikka_frame (unf T.E T.K)
    (unf_is_frame T.E T.K h.frame_aug h.kproper)
    (ttLabel T) (twoTier_hintikka T h) root C0 hC0

/-! ## Round B (2026-07-22): the multi-kernel unfolding

Round A supports ONE ascending kernel.  Round B generalizes to any
family of kernels indexed by a type `κ`, each ascending or descending,
with constant kernel–kernel interfaces: the certificate's finite
quotient is `qnet` on `β ⊕ κ` (externals + one node per kernel), the
generated structure is `munf` on `β ⊕ κ × ℕ` (externals + one ℕ-chain
per kernel).  Within a kernel the chain runs upward (`chain`) or
downward (its mirror `desc`); across kernels and to externals every
rung carries the kernel's constant row.  `munf_is_frame` is the
multi-kernel lift: `Frame qnet ⟹ Frame munf` — with NO extra
properness hypotheses (they all follow from `qnet`'s own strong-EQ
condition).  Needed for concepts forcing several independent towers,
e.g. an ascending and a descending tower linked by `DR`. -/

/-- The mirrored (descending) chain is composition-consistent: the
    descending triangle fact, proved like `chain_cc`. -/
theorem desc_cc (i j k : Nat) :
    chain k i ∈ comp (chain j i) (chain k j) := by
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
    · simp only [chain_gt hij, chain_gt hjk,
        chain_gt (Nat.lt_trans hij hjk)]
      decide
    · subst hjk
      simp only [chain_self]
      rcases chain_vals j i with h | h | h <;> simp only [h] <;> decide
    · rcases chain_vals k i with h | h | h <;>
        simp only [chain_gt hij, chain_lt hjk, h] <;> decide
  · subst hij
    simp only [chain_self]
    rcases chain_vals k i with h | h | h <;> simp only [h] <;> decide
  · rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
    · rcases chain_vals k i with h | h | h <;>
        simp only [chain_lt hij, chain_gt hjk, h] <;> decide
    · subst hjk
      simp only [chain_self]
      rcases chain_vals j i with h | h | h <;> simp only [h] <;> decide
    · simp only [chain_lt hij, chain_lt hjk,
        chain_lt (Nat.lt_trans hjk hij)]
      decide

/-- A directed chain: `true` = ascending (rung `i` inside rung `j` for
    `i < j`), `false` = descending (the mirror). -/
def cchain : Bool → Nat → Nat → Atom
  | true, i, j => chain i j
  | false, i, j => chain j i

/-- The forward step relation of a directed chain: `PP` ascending,
    `PPI` descending. -/
def cdir : Bool → Atom
  | true => pp
  | false => ppi

theorem cchain_self (b : Bool) (i : Nat) : cchain b i i = eq := by
  cases b with
  | true => exact chain_self i
  | false => exact chain_self i

theorem cchain_vals (b : Bool) (i j : Nat) :
    cchain b i j = pp ∨ cchain b i j = eq ∨ cchain b i j = ppi := by
  cases b with
  | true => exact chain_vals i j
  | false => exact chain_vals j i

theorem cchain_conv (b : Bool) (i j : Nat) :
    cchain b j i = conv (cchain b i j) := by
  cases b with
  | true => exact chain_conv i j
  | false => exact chain_conv j i

theorem cchain_eq_imp {b : Bool} {i j : Nat} (h : cchain b i j = eq) :
    i = j := by
  cases b with
  | true => exact chain_eq_imp h
  | false => exact (chain_eq_imp h).symm

theorem cchain_lt (b : Bool) {i j : Nat} (h : i < j) :
    cchain b i j = cdir b := by
  cases b with
  | true => exact chain_lt h
  | false => exact chain_gt h

theorem cchain_cc (b : Bool) (i j k : Nat) :
    cchain b i k ∈ comp (cchain b i j) (cchain b j k) := by
  cases b with
  | true => exact chain_cc i j k
  | false => exact desc_cc i j k

variable {κ : Type}

/-- The finite quotient network: externals + ONE node per kernel.
    `Frame qnet` is the "valid multi-kernel quotient" hypothesis. -/
def qnet [DecidableEq κ] (E : β → β → Atom) (K : κ → β → Atom)
    (Q : κ → κ → Atom) : (β ⊕ κ) → (β ⊕ κ) → Atom
  | .inl e, .inl f => E e f
  | .inl e, .inr k => conv (K k e)
  | .inr k, .inl f => K k f
  | .inr k, .inr k' => if k = k' then eq else Q k k'

/-- The multi-kernel unfolding: one directed ℕ-chain per kernel, all
    interfaces constant. -/
def munf [DecidableEq κ] (E : β → β → Atom) (K : κ → β → Atom)
    (Q : κ → κ → Atom) (up : κ → Bool) :
    (β ⊕ κ × Nat) → (β ⊕ κ × Nat) → Atom
  | .inl e, .inl f => E e f
  | .inl e, .inr (k, _) => conv (K k e)
  | .inr (k, _), .inl f => K k f
  | .inr (k, i), .inr (k', j) =>
      if k = k' then cchain (up k) i j else Q k k'

section MultiKernel

variable [DecidableEq κ] {E : β → β → Atom} {K : κ → β → Atom}
  {Q : κ → κ → Atom} {up : κ → Bool}

/-- Kernel rows are proper — derived from the quotient frame's own
    strong-EQ condition, no extra hypothesis. -/
theorem qnet_K_proper (h : Frame (qnet E K Q)) :
    ∀ k e, K k e ≠ eq := by
  intro k e heq
  have h2 : qnet E K Q (.inr k) (.inl e) = eq := heq
  have h3 := h.eq_id _ _ h2
  cases h3

/-- Distinct-kernel values are proper — likewise derived. -/
theorem qnet_Q_proper (h : Frame (qnet E K Q)) :
    ∀ k k', k ≠ k' → Q k k' ≠ eq := by
  intro k k' hne heq
  have h2 : qnet E K Q (.inr k) (.inr k') = eq := by
    show (if k = k' then eq else Q k k') = eq
    rw [if_neg hne]
    exact heq
  exact hne (Sum.inr.inj (h.eq_id _ _ h2))

/-- Kernel–kernel values are converse-coherent — derived. -/
theorem qnet_Q_conv (h : Frame (qnet E K Q)) :
    ∀ k k', k ≠ k' → Q k' k = conv (Q k k') := by
  intro k k' hne
  have h2 := h.conv_ (.inr k) (.inr k')
  have e1 : qnet E K Q (.inr k') (.inr k) = Q k' k := by
    show (if k' = k then eq else Q k' k) = _
    rw [if_neg (fun hh => hne hh.symm)]
  have e2 : qnet E K Q (.inr k) (.inr k') = Q k k' := by
    show (if k = k' then eq else Q k k') = _
    rw [if_neg hne]
  rw [e1, e2] at h2
  exact h2

/-- THE MULTI-KERNEL LIFT: a valid finite quotient (externals + one
    node per kernel) unfolds to a genuine RCC5 frame with one directed
    infinite chain per kernel.  Generalizes `unf_is_frame`; the new
    triple cases are the same-kernel-pair configurations, discharged by
    the self-absorption/`conv_super` toolkit with the chain value in
    `{PP, EQ, PPI}`, and the all-distinct configurations, which project
    onto quotient triples. -/
theorem munf_is_frame (h : Frame (qnet E K Q)) :
    Frame (munf E K Q up) where
  refl_eq := by
    intro x
    rcases x with e | ⟨k, i⟩
    · exact h.refl_eq (.inl e)
    · show (if k = k then cchain (up k) i i else Q k k) = eq
      rw [if_pos rfl]
      exact cchain_self _ _
  eq_id := by
    intro x y hxy
    rcases x with e | ⟨k, i⟩ <;> rcases y with f | ⟨k', j⟩
    · have h2 := h.eq_id (.inl e) (.inl f) hxy
      injection h2 with h3
      exact congrArg Sum.inl h3
    · exact absurd hxy (conv_ne_eq _ (qnet_K_proper h k' e))
    · exact absurd hxy (qnet_K_proper h k f)
    · have hxy' : (if k = k' then cchain (up k) i j else Q k k') = eq :=
        hxy
      by_cases hk : k = k'
      · subst hk
        rw [if_pos rfl] at hxy'
        rw [cchain_eq_imp hxy']
      · rw [if_neg hk] at hxy'
        exact absurd hxy' (qnet_Q_proper h k k' hk)
  conv_ := by
    intro x y
    rcases x with e | ⟨k, i⟩ <;> rcases y with f | ⟨k', j⟩
    · exact h.conv_ (.inl e) (.inl f)
    · exact (conv_invol _).symm
    · rfl
    · show (if k' = k then cchain (up k') j i else Q k' k)
        = conv (if k = k' then cchain (up k) i j else Q k k')
      by_cases hk : k = k'
      · subst hk
        rw [if_pos rfl, if_pos rfl]
        exact cchain_conv _ _ _
      · rw [if_neg (fun hh => hk hh.symm), if_neg hk]
        exact qnet_Q_conv h k k' hk
  comp_ := by
    intro x y z
    rcases x with e | ⟨k1, i1⟩ <;> rcases y with f | ⟨k2, i2⟩ <;>
      rcases z with g | ⟨k3, i3⟩
    · -- (ext, ext, ext)
      exact h.comp_ (.inl e) (.inl f) (.inl g)
    · -- (ext, ext, chain)
      exact h.comp_ (.inl e) (.inl f) (.inr k3)
    · -- (ext, chain, ext)
      exact h.comp_ (.inl e) (.inr k2) (.inl g)
    · -- (ext, chain, chain)
      show conv (K k3 e) ∈ comp (conv (K k2 e))
        (if k2 = k3 then cchain (up k2) i2 i3 else Q k2 k3)
      by_cases hk : k2 = k3
      · subst hk
        rw [if_pos rfl]
        exact self_right _ _ (conv_ne_eq _ (qnet_K_proper h k2 e))
          (cchain_vals _ _ _)
      · rw [if_neg hk]
        have h2 := h.comp_ (.inl e) (.inr k2) (.inr k3)
        have e2 : qnet E K Q (.inr k2) (.inr k3) = Q k2 k3 := by
          show (if k2 = k3 then eq else Q k2 k3) = _
          rw [if_neg hk]
        rw [e2] at h2
        exact h2
    · -- (chain, ext, ext)
      exact h.comp_ (.inr k1) (.inl f) (.inl g)
    · -- (chain, ext, chain)
      show (if k1 = k3 then cchain (up k1) i1 i3 else Q k1 k3)
        ∈ comp (K k1 f) (conv (K k3 f))
      by_cases hk : k1 = k3
      · subst hk
        rw [if_pos rfl]
        obtain ⟨hpp, heq, hppi⟩ :=
          conv_super (K k1 f) (qnet_K_proper h k1 f)
        rcases cchain_vals (up k1) i1 i3 with hc | hc | hc <;>
          rw [hc] <;> assumption
      · rw [if_neg hk]
        have h2 := h.comp_ (.inr k1) (.inl f) (.inr k3)
        have e2 : qnet E K Q (.inr k1) (.inr k3) = Q k1 k3 := by
          show (if k1 = k3 then eq else Q k1 k3) = _
          rw [if_neg hk]
        rw [e2] at h2
        exact h2
    · -- (chain, chain, ext)
      show K k1 g ∈ comp
        (if k1 = k2 then cchain (up k1) i1 i2 else Q k1 k2) (K k2 g)

      by_cases hk : k1 = k2
      · subst hk
        rw [if_pos rfl]
        exact self_left _ _ (qnet_K_proper h k1 g) (cchain_vals _ _ _)
      · rw [if_neg hk]
        have h2 := h.comp_ (.inr k1) (.inr k2) (.inl g)
        have e2 : qnet E K Q (.inr k1) (.inr k2) = Q k1 k2 := by
          show (if k1 = k2 then eq else Q k1 k2) = _
          rw [if_neg hk]
        rw [e2] at h2
        exact h2
    · -- (chain, chain, chain)
      show (if k1 = k3 then cchain (up k1) i1 i3 else Q k1 k3) ∈
        comp (if k1 = k2 then cchain (up k1) i1 i2 else Q k1 k2)
             (if k2 = k3 then cchain (up k2) i2 i3 else Q k2 k3)
      by_cases h12 : k1 = k2
      · subst h12
        by_cases h13 : k1 = k3
        · subst h13
          rw [if_pos rfl, if_pos rfl, if_pos rfl]
          exact cchain_cc _ i1 i2 i3
        · rw [if_neg h13, if_pos rfl, if_neg h13]
          exact self_left _ _ (qnet_Q_proper h k1 k3 h13)
            (cchain_vals _ _ _)
      · by_cases h23 : k2 = k3
        · subst h23
          rw [if_neg h12, if_neg h12, if_pos rfl]
          exact self_right _ _ (qnet_Q_proper h k1 k2 h12)
            (cchain_vals _ _ _)
        · by_cases h13 : k1 = k3
          · subst h13
            rw [if_pos rfl, if_neg h12, if_neg h23]
            rw [show Q k2 k1 = conv (Q k1 k2) from
              qnet_Q_conv h k1 k2 h12]
            obtain ⟨hpp, heq, hppi⟩ :=
              conv_super (Q k1 k2) (qnet_Q_proper h k1 k2 h12)
            rcases cchain_vals (up k1) i1 i3 with hc | hc | hc <;>
              rw [hc] <;> assumption
          · rw [if_neg h13, if_neg h12, if_neg h23]
            have h2 := h.comp_ (.inr k1) (.inr k2) (.inr k3)
            have e13 : qnet E K Q (.inr k1) (.inr k3) = Q k1 k3 := by
              show (if k1 = k3 then eq else Q k1 k3) = _
              rw [if_neg h13]
            have e12 : qnet E K Q (.inr k1) (.inr k2) = Q k1 k2 := by
              show (if k1 = k2 then eq else Q k1 k2) = _
              rw [if_neg h12]
            have e23 : qnet E K Q (.inr k2) (.inr k3) = Q k2 k3 := by
              show (if k2 = k3 then eq else Q k2 k3) = _
              rw [if_neg h23]
            rw [e13, e12, e23] at h2
            exact h2

end MultiKernel

/-! ### The multi-tier certificate

The round-B generalization of `TwoTier`: any family of directed kernels
over an index type `κ`, kernel–kernel interfaces constant (`Q`), each
kernel ascending or descending (`up`).  Chain-internal fulfilment runs
in each kernel's own direction (`cdir`): ascending kernels discharge
`∃PP` demands rung-to-rung, descending kernels `∃PPI` — the descending
tower `∃PPI.⊤ ⊓ ∀PPI.∃PPI.⊤` becomes presentable. -/

structure MultiTier (β κ : Type) where
  E : β → β → Atom
  K : κ → β → Atom
  Q : κ → κ → Atom
  up : κ → Bool
  tauE : β → List Concept
  p : κ → Nat
  phase : κ → Nat → List Concept

/-- The type labelling of the multi-kernel unfolding. -/
def mtLabel (T : MultiTier β κ) : (β ⊕ κ × Nat) → List Concept
  | .inl e => T.tauE e
  | .inr (k, i) => T.phase k (i % T.p k)

/-- Validity of a multi-tier certificate: the quotient-frame hypothesis
    + the Hintikka obligations per edge class (now including the
    cross-kernel classes `kq_all` and the cross-kernel fulfilment branch
    of `k_ex`). -/
structure MultiTierOk [DecidableEq κ] (T : MultiTier β κ) : Prop where
  hp : ∀ k, 0 < T.p k
  frame_q : Frame (qnet T.E T.K T.Q)
  -- propositional coherence, externals
  e_clash : ∀ e a, Concept.atom a ∈ T.tauE e → Concept.natom a ∉ T.tauE e
  e_nobot : ∀ e, Concept.bot ∉ T.tauE e
  e_and : ∀ e c d, Concept.and c d ∈ T.tauE e → c ∈ T.tauE e ∧ d ∈ T.tauE e
  e_or : ∀ e c d, Concept.or c d ∈ T.tauE e → c ∈ T.tauE e ∨ d ∈ T.tauE e
  -- propositional coherence, phases
  k_clash : ∀ k a, a < T.p k → ∀ n, Concept.atom n ∈ T.phase k a →
    Concept.natom n ∉ T.phase k a
  k_nobot : ∀ k a, a < T.p k → Concept.bot ∉ T.phase k a
  k_and : ∀ k a, a < T.p k → ∀ c d, Concept.and c d ∈ T.phase k a →
    c ∈ T.phase k a ∧ d ∈ T.phase k a
  k_or : ∀ k a, a < T.p k → ∀ c d, Concept.or c d ∈ T.phase k a →
    c ∈ T.phase k a ∨ d ∈ T.phase k a
  -- universal propagation, per edge class
  ee_all : ∀ e f r c, Concept.all r c ∈ T.tauE e → T.E e f = r →
    c ∈ T.tauE f
  ek_all : ∀ e r c, Concept.all r c ∈ T.tauE e →
    ∀ k, conv (T.K k e) = r → ∀ a, a < T.p k → c ∈ T.phase k a
  ke_all : ∀ k a, a < T.p k → ∀ r c, Concept.all r c ∈ T.phase k a →
    ∀ f, T.K k f = r → c ∈ T.tauE f
  kk_pp : ∀ k a, a < T.p k → ∀ c, Concept.all pp c ∈ T.phase k a →
    ∀ b, b < T.p k → c ∈ T.phase k b
  kk_ppi : ∀ k a, a < T.p k → ∀ c, Concept.all ppi c ∈ T.phase k a →
    ∀ b, b < T.p k → c ∈ T.phase k b
  kk_eq : ∀ k a, a < T.p k → ∀ c, Concept.all eq c ∈ T.phase k a →
    c ∈ T.phase k a
  kq_all : ∀ k k', k ≠ k' → ∀ a, a < T.p k → ∀ r c,
    Concept.all r c ∈ T.phase k a → T.Q k k' = r →
    ∀ b, b < T.p k' → c ∈ T.phase k' b
  -- existential fulfilment, per node class
  e_ex : ∀ e r c, Concept.ex r c ∈ T.tauE e →
    (∃ f, T.E e f = r ∧ c ∈ T.tauE f) ∨
    (∃ k, conv (T.K k e) = r ∧ ∃ a, a < T.p k ∧ c ∈ T.phase k a)
  k_ex : ∀ k a, a < T.p k → ∀ r c, Concept.ex r c ∈ T.phase k a →
    (∃ f, T.K k f = r ∧ c ∈ T.tauE f) ∨
    (r = cdir (T.up k) ∧ ∃ b, b < T.p k ∧ c ∈ T.phase k b) ∨
    (r = eq ∧ c ∈ T.phase k a) ∨
    (∃ k', k ≠ k' ∧ T.Q k k' = r ∧ ∃ b, b < T.p k' ∧ c ∈ T.phase k' b)

/-- ROUND-B CENTRAL LEMMA: a valid multi-tier certificate's labelling is
    a Hintikka labelling of the multi-kernel unfolding. -/
theorem multiTier_hintikka [DecidableEq κ] (T : MultiTier β κ)
    (h : MultiTierOk T) :
    Hintikka (fun _ => True) (munf T.E T.K T.Q T.up) (mtLabel T) where
  clashfree := by
    intro x a _ hmem
    rcases x with e | ⟨k, i⟩
    · exact h.e_clash e a hmem
    · exact h.k_clash k (i % T.p k) (Nat.mod_lt i (h.hp k)) a hmem
  nobot := by
    intro x _
    rcases x with e | ⟨k, i⟩
    · exact h.e_nobot e
    · exact h.k_nobot k (i % T.p k) (Nat.mod_lt i (h.hp k))
  and_c := by
    intro x c d _ hmem
    rcases x with e | ⟨k, i⟩
    · exact h.e_and e c d hmem
    · exact h.k_and k (i % T.p k) (Nat.mod_lt i (h.hp k)) c d hmem
  or_c := by
    intro x c d _ hmem
    rcases x with e | ⟨k, i⟩
    · exact h.e_or e c d hmem
    · exact h.k_or k (i % T.p k) (Nat.mod_lt i (h.hp k)) c d hmem
  all_c := by
    intro x r c _ hmem y _ hr
    rcases x with e | ⟨k, i⟩ <;> rcases y with f | ⟨k', j⟩
    · exact h.ee_all e f r c hmem hr
    · exact h.ek_all e r c hmem k' hr (j % T.p k')
        (Nat.mod_lt j (h.hp k'))
    · exact h.ke_all k (i % T.p k) (Nat.mod_lt i (h.hp k)) r c hmem f hr
    · have hr' : (if k = k' then cchain (T.up k) i j else T.Q k k') = r :=
        hr
      have hm' : Concept.all r c ∈ T.phase k (i % T.p k) := hmem
      by_cases hk : k = k'
      · subst hk
        rw [if_pos rfl] at hr'
        rcases cchain_vals (T.up k) i j with hc | hc | hc
        · rw [hc] at hr'
          subst hr'
          exact h.kk_pp k (i % T.p k) (Nat.mod_lt i (h.hp k)) c hm'
            (j % T.p k) (Nat.mod_lt j (h.hp k))
        · rw [hc] at hr'
          subst hr'
          have hij := cchain_eq_imp hc
          subst hij
          exact h.kk_eq k (i % T.p k) (Nat.mod_lt i (h.hp k)) c hm'
        · rw [hc] at hr'
          subst hr'
          exact h.kk_ppi k (i % T.p k) (Nat.mod_lt i (h.hp k)) c hm'
            (j % T.p k) (Nat.mod_lt j (h.hp k))
      · rw [if_neg hk] at hr'
        exact h.kq_all k k' hk (i % T.p k) (Nat.mod_lt i (h.hp k)) r c
          hm' hr' (j % T.p k') (Nat.mod_lt j (h.hp k'))
  ex_f := by
    intro x r c _ hmem
    rcases x with e | ⟨k, i⟩
    · rcases h.e_ex e r c hmem with ⟨f, hEf, hcf⟩ | ⟨k, hK, a, ha, hca⟩
      · exact ⟨.inl f, True.intro, hEf, hcf⟩
      · refine ⟨.inr (k, a), True.intro, hK, ?_⟩
        show c ∈ T.phase k (a % T.p k)
        rw [Nat.mod_eq_of_lt ha]
        exact hca
    · have hm' : Concept.ex r c ∈ T.phase k (i % T.p k) := hmem
      rcases h.k_ex k (i % T.p k) (Nat.mod_lt i (h.hp k)) r c hm' with
        ⟨f, hKf, hcf⟩ | ⟨hrd, b, hb, hcb⟩ | ⟨hreq, hc⟩ |
        ⟨k', hne, hQ, b, hb, hcb⟩
      · exact ⟨.inl f, True.intro, hKf, hcf⟩
      · obtain ⟨j, hij, hjb⟩ := exists_later_phase (T.p k) (h.hp k) i b hb
        refine ⟨.inr (k, j), True.intro, ?_, ?_⟩
        · show (if k = k then cchain (T.up k) i j else T.Q k k) = r
          rw [if_pos rfl, cchain_lt _ hij, hrd]
        · show c ∈ T.phase k (j % T.p k)
          rw [hjb]
          exact hcb
      · refine ⟨.inr (k, i), True.intro, ?_, ?_⟩
        · show (if k = k then cchain (T.up k) i i else T.Q k k) = r
          rw [if_pos rfl, cchain_self, hreq]
        · exact hc
      · refine ⟨.inr (k', b), True.intro, ?_, ?_⟩
        · show (if k = k' then cchain (T.up k) i b else T.Q k k') = r
          rw [if_neg hne]
          exact hQ
        · show c ∈ T.phase k' (b % T.p k')
          rw [Nat.mod_eq_of_lt hb]
          exact hcb

/-- ROUND-B CAPSTONE: a valid multi-tier certificate with the target
    concept at some node yields an actual RCC5 model. -/
theorem multiTier_sound [DecidableEq κ] (T : MultiTier β κ)
    (h : MultiTierOk T) (root : β ⊕ κ × Nat) (C0 : Concept)
    (hC0 : C0 ∈ mtLabel T root) : Satisfiable C0 :=
  sat_from_hintikka_frame (munf T.E T.K T.Q T.up)
    (munf_is_frame h.frame_q)
    (mtLabel T) (multiTier_hintikka T h) root C0 hC0

/-! ### The fragment predicate

Soundness above is fragment-agnostic (the checker verifies ALL
universals on all edge classes).  `POFree` is where the fragment enters:
the COMPLETENESS side (round D) claims every satisfiable ∀PO-free
concept admits a valid certificate — the two-tier extraction. -/

/-- The ∀PO-free fragment: no subformula `∀PO.D`. -/
def POFree : Concept → Prop
  | .top => True
  | .bot => True
  | .atom _ => True
  | .natom _ => True
  | .and c d => POFree c ∧ POFree d
  | .or c d => POFree c ∧ POFree d
  | .ex _ c => POFree c
  | .all r c => r ≠ po ∧ POFree c

/-! ### Non-vacuity: an infinite-model concept, certified satisfiable

`Cinf = ∃PP.⊤ ⊓ ∀PP.∃PP.⊤` has NO finite model (it forces an infinite
ascending PP-chain), and it is ∀PO-free.  A two-tier certificate with an
empty external part and one phase carries it, so the round-A pipeline
produces an actual infinite model end-to-end — the certificate machinery
is exercised exactly where finite-model methods cannot go. -/

def Cinf : Concept := .and (.ex pp .top) (.all pp (.ex pp .top))

theorem cinf_pofree : POFree Cinf :=
  ⟨trivial, by decide, trivial⟩

/-- The empty-external augmented network is a frame (as inside
    `frame_nonvacuous`, restated standalone for reuse). -/
theorem aug_empty_frame :
    Frame (aug (β := Empty) (fun e _ => e.elim) (fun e => e.elim)) where
  refl_eq := by
    intro x
    cases x with
    | some e => exact e.elim
    | none => rfl
  eq_id := by
    intro x y hxy
    cases x with
    | some e => exact e.elim
    | none =>
      cases y with
      | some e => exact e.elim
      | none => rfl
  conv_ := by
    intro x y
    cases x with
    | some e => exact e.elim
    | none =>
      cases y with
      | some e => exact e.elim
      | none => rfl
  comp_ := by
    intro x y z
    cases x with
    | some e => exact e.elim
    | none =>
      cases y with
      | some e => exact e.elim
      | none =>
        cases z with
        | some e => exact e.elim
        | none => decide

/-- The phase type for the `Cinf` certificate. -/
def cinfPhase : List Concept :=
  [Cinf, .ex pp .top, .all pp (.ex pp .top), .top]

/-- The one-phase certificate for `Cinf`: no externals, phase type
    `{Cinf, ∃PP.⊤, ∀PP.∃PP.⊤, ⊤}`. -/
def cinfTT : TwoTier Empty where
  E := fun e _ => e.elim
  K := fun e => e.elim
  tauE := fun e => e.elim
  p := 1
  phase := fun _ => cinfPhase

theorem cinfTT_ok : TwoTierOk cinfTT where
  hp := Nat.one_pos
  frame_aug := aug_empty_frame
  kproper := fun e => e.elim
  e_clash := fun e => e.elim
  e_nobot := fun e => e.elim
  e_and := fun e => e.elim
  e_or := fun e => e.elim
  k_clash := by
    intro a _ n hmem
    simp only [cinfTT, cinfPhase, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h | h | h
    · simp only [Cinf] at h; exact Concept.noConfusion h
    · exact Concept.noConfusion h
    · exact Concept.noConfusion h
    · exact Concept.noConfusion h
  k_nobot := by
    intro a _
    show Concept.bot ∉ cinfPhase
    decide
  k_and := by
    intro a _ c d hmem
    simp only [cinfTT, cinfPhase, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h | h | h
    · simp only [Cinf] at h
      injection h with h1 h2
      subst h1; subst h2
      show Concept.ex pp Concept.top ∈ cinfPhase ∧
        Concept.all pp (Concept.ex pp Concept.top) ∈ cinfPhase
      decide
    · exact Concept.noConfusion h
    · exact Concept.noConfusion h
    · exact Concept.noConfusion h
  k_or := by
    intro a _ c d hmem
    simp only [cinfTT, cinfPhase, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h | h | h
    · simp only [Cinf] at h; exact Concept.noConfusion h
    · exact Concept.noConfusion h
    · exact Concept.noConfusion h
    · exact Concept.noConfusion h
  ee_all := fun e => e.elim
  ek_all := fun e => e.elim
  ke_all := by
    intro a _ r c _ f
    exact f.elim
  kk_pp := by
    intro a _ c hmem b _
    simp only [cinfTT, cinfPhase, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h | h | h
    · simp only [Cinf] at h; exact Concept.noConfusion h
    · exact Concept.noConfusion h
    · injection h with h1 h2
      subst h2
      show Concept.ex pp Concept.top ∈ cinfPhase
      decide
    · exact Concept.noConfusion h
  kk_ppi := by
    intro a _ c hmem b _
    simp only [cinfTT, cinfPhase, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h | h | h
    · simp only [Cinf] at h; exact Concept.noConfusion h
    · exact Concept.noConfusion h
    · injection h with h1 h2
      exact Atom.noConfusion h1
    · exact Concept.noConfusion h
  kk_eq := by
    intro a _ c hmem
    simp only [cinfTT, cinfPhase, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h | h | h
    · simp only [Cinf] at h; exact Concept.noConfusion h
    · exact Concept.noConfusion h
    · injection h with h1 h2
      exact Atom.noConfusion h1
    · exact Concept.noConfusion h
  e_ex := fun e => e.elim
  k_ex := by
    intro a _ r c hmem
    simp only [cinfTT, cinfPhase, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h | h | h
    · simp only [Cinf] at h; exact Concept.noConfusion h
    · injection h with h1 h2
      subst h1; subst h2
      exact Or.inr (Or.inl ⟨rfl, 0, Nat.one_pos, by decide⟩)
    · exact Concept.noConfusion h
    · exact Concept.noConfusion h

/-- `Cinf` — satisfiable only in infinite models — is `Satisfiable`,
    through the full round-A pipeline. -/
theorem cinf_satisfiable : Satisfiable Cinf :=
  twoTier_sound cinfTT cinfTT_ok (Sum.inr 0) Cinf (by decide)

/-! ### Round-B non-vacuity: two towers, both directions, DR-linked

`Cboth = Cinf ⊓ ∃DR.Dinf` where `Dinf = ∃PPI.⊤ ⊓ ∀PPI.∃PPI.⊤`: an
ascending infinite tower whose root is disjoint from the head of an
infinite DESCENDING tower.  Any model needs two independent infinite
chains of opposite orientation — beyond the single-ascending-kernel
format (with finite external part).  The multi-tier certificate: two
kernels (`κ = Bool`; `true` ascending, `false` descending), one phase
each, all cross-kernel values `DR`. -/

def Dinf : Concept := .and (.ex ppi .top) (.all ppi (.ex ppi .top))

def Cboth : Concept := .and Cinf (.ex dr Dinf)

theorem cboth_pofree : POFree Cboth :=
  ⟨⟨trivial, by decide, trivial⟩, trivial, by decide, trivial⟩

def upList : List Concept :=
  [Cboth, Cinf, .ex pp .top, .all pp (.ex pp .top), .ex dr Dinf, .top]

def dnList : List Concept :=
  [Dinf, .ex ppi .top, .all ppi (.ex ppi .top), .top]

def bothPhase : Bool → List Concept
  | true => upList
  | false => dnList

def cbothMT : MultiTier Empty Bool where
  E := fun e _ => e.elim
  K := fun _ e => e.elim
  Q := fun _ _ => dr
  up := fun k => k
  tauE := fun e => e.elim
  p := fun _ => 1
  phase := fun k _ => bothPhase k

/-- The two-kernel quotient (no externals, cross value `DR`) is a
    frame. -/
theorem cboth_qnet_frame :
    Frame (qnet (β := Empty) (κ := Bool) (fun e _ => e.elim)
      (fun _ e => e.elim) (fun _ _ => dr)) where
  refl_eq := by
    intro x
    rcases x with e | k
    · exact e.elim
    · show (if k = k then eq else dr) = eq
      rw [if_pos rfl]
  eq_id := by
    intro x y hxy
    rcases x with e | k
    · exact e.elim
    · rcases y with f | k'
      · exact f.elim
      · have hxy' : (if k = k' then eq else dr) = eq := hxy
        by_cases hk : k = k'
        · subst hk; rfl
        · rw [if_neg hk] at hxy'
          exact absurd hxy' (by decide)
  conv_ := by
    intro x y
    rcases x with e | k
    · exact e.elim
    · rcases y with f | k'
      · exact f.elim
      · show (if k' = k then eq else dr) = conv (if k = k' then eq else dr)
        by_cases hk : k = k'
        · subst hk
          rw [if_pos rfl]
          rfl
        · rw [if_neg (fun hh => hk hh.symm), if_neg hk]
          rfl
  comp_ := by
    intro x y z
    rcases x with e | k1
    · exact e.elim
    · rcases y with f | k2
      · exact f.elim
      · rcases z with g | k3
        · exact g.elim
        · show (if k1 = k3 then eq else dr) ∈
            comp (if k1 = k2 then eq else dr) (if k2 = k3 then eq else dr)
          cases k1 <;> cases k2 <;> cases k3 <;> decide

theorem cbothMT_ok : MultiTierOk cbothMT where
  hp := fun _ => Nat.one_pos
  frame_q := cboth_qnet_frame
  e_clash := fun e => e.elim
  e_nobot := fun e => e.elim
  e_and := fun e => e.elim
  e_or := fun e => e.elim
  k_clash := by
    intro k a _ n hmem
    cases k with
    | true =>
      have hm : Concept.atom n ∈ upList := hmem
      simp only [upList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h | h
      · simp only [Cboth] at h; exact Concept.noConfusion h
      · simp only [Cinf] at h; exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
    | false =>
      have hm : Concept.atom n ∈ dnList := hmem
      simp only [dnList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h
      · simp only [Dinf] at h; exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
  k_nobot := by
    intro k a _
    cases k with
    | true => show Concept.bot ∉ upList; decide
    | false => show Concept.bot ∉ dnList; decide
  k_and := by
    intro k a _ c d hmem
    cases k with
    | true =>
      have hm : Concept.and c d ∈ upList := hmem
      simp only [upList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h | h
      · simp only [Cboth] at h
        injection h with h1 h2
        subst h1; subst h2
        show Cinf ∈ upList ∧ Concept.ex dr Dinf ∈ upList
        decide
      · simp only [Cinf] at h
        injection h with h1 h2
        subst h1; subst h2
        show Concept.ex pp Concept.top ∈ upList ∧
          Concept.all pp (Concept.ex pp Concept.top) ∈ upList
        decide
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
    | false =>
      have hm : Concept.and c d ∈ dnList := hmem
      simp only [dnList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h
      · simp only [Dinf] at h
        injection h with h1 h2
        subst h1; subst h2
        show Concept.ex ppi Concept.top ∈ dnList ∧
          Concept.all ppi (Concept.ex ppi Concept.top) ∈ dnList
        decide
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
  k_or := by
    intro k a _ c d hmem
    cases k with
    | true =>
      have hm : Concept.or c d ∈ upList := hmem
      simp only [upList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h | h
      · simp only [Cboth] at h; exact Concept.noConfusion h
      · simp only [Cinf] at h; exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
    | false =>
      have hm : Concept.or c d ∈ dnList := hmem
      simp only [dnList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h
      · simp only [Dinf] at h; exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
  ee_all := fun e => e.elim
  ek_all := fun e => e.elim
  ke_all := by
    intro k a _ r c _ f
    exact f.elim
  kk_pp := by
    intro k a _ c hmem b _
    cases k with
    | true =>
      have hm : Concept.all pp c ∈ upList := hmem
      simp only [upList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h | h
      · simp only [Cboth] at h; exact Concept.noConfusion h
      · simp only [Cinf] at h; exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · injection h with h1 h2
        subst h2
        show Concept.ex pp Concept.top ∈ upList
        decide
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
    | false =>
      have hm : Concept.all pp c ∈ dnList := hmem
      simp only [dnList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h
      · simp only [Dinf] at h; exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · injection h with h1 h2
        exact Atom.noConfusion h1
      · exact Concept.noConfusion h
  kk_ppi := by
    intro k a _ c hmem b _
    cases k with
    | true =>
      have hm : Concept.all ppi c ∈ upList := hmem
      simp only [upList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h | h
      · simp only [Cboth] at h; exact Concept.noConfusion h
      · simp only [Cinf] at h; exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · injection h with h1 h2
        exact Atom.noConfusion h1
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
    | false =>
      have hm : Concept.all ppi c ∈ dnList := hmem
      simp only [dnList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h
      · simp only [Dinf] at h; exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · injection h with h1 h2
        subst h2
        show Concept.ex ppi Concept.top ∈ dnList
        decide
      · exact Concept.noConfusion h
  kk_eq := by
    intro k a _ c hmem
    cases k with
    | true =>
      have hm : Concept.all eq c ∈ upList := hmem
      simp only [upList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h | h
      · simp only [Cboth] at h; exact Concept.noConfusion h
      · simp only [Cinf] at h; exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · injection h with h1 h2
        exact Atom.noConfusion h1
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h
    | false =>
      have hm : Concept.all eq c ∈ dnList := hmem
      simp only [dnList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h
      · simp only [Dinf] at h; exact Concept.noConfusion h
      · exact Concept.noConfusion h
      · injection h with h1 h2
        exact Atom.noConfusion h1
      · exact Concept.noConfusion h
  kq_all := by
    intro k k' hne a _ r c hmem hQ b _
    cases k with
    | true =>
      cases k' with
      | true => exact absurd rfl hne
      | false =>
        have hm : Concept.all r c ∈ upList := hmem
        simp only [upList, List.mem_cons, List.not_mem_nil, or_false]
          at hm
        rcases hm with h | h | h | h | h | h
        · simp only [Cboth] at h; exact Concept.noConfusion h
        · simp only [Cinf] at h; exact Concept.noConfusion h
        · exact Concept.noConfusion h
        · injection h with h1 h2
          subst h1
          exact Atom.noConfusion hQ
        · exact Concept.noConfusion h
        · exact Concept.noConfusion h
    | false =>
      cases k' with
      | false => exact absurd rfl hne
      | true =>
        have hm : Concept.all r c ∈ dnList := hmem
        simp only [dnList, List.mem_cons, List.not_mem_nil, or_false]
          at hm
        rcases hm with h | h | h | h
        · simp only [Dinf] at h; exact Concept.noConfusion h
        · exact Concept.noConfusion h
        · injection h with h1 h2
          subst h1
          exact Atom.noConfusion hQ
        · exact Concept.noConfusion h
  e_ex := fun e => e.elim
  k_ex := by
    intro k a _ r c hmem
    cases k with
    | true =>
      have hm : Concept.ex r c ∈ upList := hmem
      simp only [upList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h | h
      · simp only [Cboth] at h; exact Concept.noConfusion h
      · simp only [Cinf] at h; exact Concept.noConfusion h
      · injection h with h1 h2
        subst h1; subst h2
        exact Or.inr (Or.inl ⟨rfl, 0, Nat.one_pos,
          by show Concept.top ∈ upList; decide⟩)
      · exact Concept.noConfusion h
      · injection h with h1 h2
        subst h1; subst h2
        exact Or.inr (Or.inr (Or.inr ⟨false, by decide, rfl, 0,
          Nat.one_pos, by show Dinf ∈ dnList; decide⟩))
      · exact Concept.noConfusion h
    | false =>
      have hm : Concept.ex r c ∈ dnList := hmem
      simp only [dnList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h
      · simp only [Dinf] at h; exact Concept.noConfusion h
      · injection h with h1 h2
        subst h1; subst h2
        exact Or.inr (Or.inl ⟨rfl, 0, Nat.one_pos,
          by show Concept.top ∈ dnList; decide⟩)
      · exact Concept.noConfusion h
      · exact Concept.noConfusion h

/-- `Cboth` — needing an ascending AND a descending infinite tower,
    DR-linked — is `Satisfiable`, through the full round-B pipeline. -/
theorem cboth_satisfiable : Satisfiable Cboth :=
  multiTier_sound cbothMT cbothMT_ok (Sum.inr (true, 0)) Cboth
    (by show Cboth ∈ upList; decide)

/-! ## Round C (2026-07-22): the executable first-order checker

The rounds-A/B certificates carry FUNCTION fields, adequate for
soundness but not enumerable data.  Round C makes them first-order (the
15th-review standard, the round-29 `finAcceptB` pattern): `FinMT` is
pure list data (lists of atoms, concepts, booleans — Gödel-numerable),
`decodeMT` a TOTAL decoder into a `MultiTier` over `Fin` index types,
and `mtOkB`/`mtAcceptB` a computable Boolean checker whose acceptance
is proved to yield a model (`mtAcceptB_sound`).  The checker mentions
no oracle: it folds over index ranges and type lists.  A future
enumeration of `FinMT` codes + the round-D completeness argument then
give `Decidable (Satisfiable C0)` for ∀PO-free `C0`. -/

/-- The first-order multi-tier certificate: pure list data.
    `tauE.length` = number of externals; `phases.length` = number of
    kernels; `phases[k]` = kernel `k`'s phase-type list (its length =
    the period).  `E`/`K`/`Q` are atom tables (external×external,
    kernel×external, kernel×kernel); `up` the direction flags.
    Out-of-range reads default (`DR`, `[]`, `true`) — the checker and
    decoder read the SAME accessors, so defaults are never a soundness
    concern. -/
structure FinMT where
  tauE : List (List Concept)
  E : List (List Atom)
  K : List (List Atom)
  Q : List (List Atom)
  up : List Bool
  phases : List (List (List Concept))

namespace FinMT

def nE (F : FinMT) : Nat := F.tauE.length
def nK (F : FinMT) : Nat := F.phases.length
def tE (F : FinMT) (i : Nat) : List Concept := F.tauE.getD i []
def ph (F : FinMT) (k : Nat) : List (List Concept) := F.phases.getD k []
def pk (F : FinMT) (k : Nat) : Nat := (F.ph k).length
def phase (F : FinMT) (k a : Nat) : List Concept := (F.ph k).getD a []
def Ea (F : FinMT) (i j : Nat) : Atom := (F.E.getD i []).getD j dr
def Ka (F : FinMT) (k e : Nat) : Atom := (F.K.getD k []).getD e dr
def Qa (F : FinMT) (k k' : Nat) : Atom := (F.Q.getD k []).getD k' dr
def upa (F : FinMT) (k : Nat) : Bool := F.up.getD k true

/-- The raw quotient network on `Nat` indices (`< nE` = external,
    `nE ≤ · < nE + nK` = kernel), mirroring `qnet`. -/
def qraw (F : FinMT) (x y : Nat) : Atom :=
  if x < F.nE then
    (if y < F.nE then F.Ea x y else conv (F.Ka (y - F.nE) x))
  else
    (if y < F.nE then F.Ka (x - F.nE) y
     else (if x = y then eq else F.Qa (x - F.nE) (y - F.nE)))

end FinMT

/-- The total decoder: a `MultiTier` over `Fin` index types, reading
    exactly the raw accessors. -/
def decodeMT (F : FinMT) : MultiTier (Fin F.nE) (Fin F.nK) where
  E := fun e f => F.Ea e.val f.val
  K := fun k e => F.Ka k.val e.val
  Q := fun k k' => F.Qa k.val k'.val
  up := fun k => F.upa k.val
  tauE := fun e => F.tE e.val
  p := fun k => F.pk k.val
  phase := fun k a => F.phase k.val a

/-! ### Bool-level helpers -/

/-- Bounded Boolean ∀. -/
def ballB (n : Nat) (f : Nat → Bool) : Bool := (List.range n).all f

/-- Bounded Boolean ∃. -/
def bexB (n : Nat) (f : Nat → Bool) : Bool := (List.range n).any f

/-- Boolean implication. -/
def impB (a b : Bool) : Bool := !a || b

theorem ballB_true {n : Nat} {f : Nat → Bool} (h : ballB n f = true) :
    ∀ i, i < n → f i = true := by
  intro i hi
  exact List.all_eq_true.mp h i (List.mem_range.mpr hi)

theorem bexB_true {n : Nat} {f : Nat → Bool} (h : bexB n f = true) :
    ∃ i, i < n ∧ f i = true := by
  obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp h
  exact ⟨x, List.mem_range.mp hx, hfx⟩

theorem impB_true {a b : Bool} (h : impB a b = true) (ha : a = true) :
    b = true := by
  subst ha
  simpa [impB] using h

theorem notB_true {b : Bool} (h : (!b) = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd h (by decide)

theorem andB_split {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> first
    | exact ⟨rfl, rfl⟩
    | exact absurd h (by decide)

theorem orB_split {a b : Bool} (h : (a || b) = true) :
    a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false =>
    cases b with
    | true => exact Or.inr rfl
    | false => exact absurd h (by decide)

/-! ### The executable checker -/

namespace FinMT

/-- Frame checks on the raw quotient network (uniform over the encoded
    index range `nE + nK`). -/
def frameB (F : FinMT) : Bool :=
  ballB (F.nE + F.nK) (fun x => decide (F.qraw x x = eq)) &&
  ballB (F.nE + F.nK) (fun x => ballB (F.nE + F.nK) (fun y =>
    impB (decide (F.qraw x y = eq)) (decide (x = y)))) &&
  ballB (F.nE + F.nK) (fun x => ballB (F.nE + F.nK) (fun y =>
    decide (F.qraw y x = conv (F.qraw x y)))) &&
  ballB (F.nE + F.nK) (fun x => ballB (F.nE + F.nK) (fun y =>
    ballB (F.nE + F.nK) (fun z =>
      decide (F.qraw x z ∈ comp (F.qraw x y) (F.qraw y z)))))

/-- Propositional coherence of one type list, in-list. -/
def propB (L : List Concept) : Bool :=
  (!decide (Concept.bot ∈ L)) &&
  L.all (fun D => match D with
    | .atom a => !decide (Concept.natom a ∈ L)
    | .and c d => decide (c ∈ L) && decide (d ∈ L)
    | .or c d => decide (c ∈ L) || decide (d ∈ L)
    | _ => true)

/-- Universal-propagation checks for one external type list. -/
def eAllB (F : FinMT) (e : Nat) : Bool :=
  (F.tE e).all (fun D => match D with
    | .all r c =>
      ballB F.nE (fun f =>
        impB (decide (F.Ea e f = r)) (decide (c ∈ F.tE f))) &&
      ballB F.nK (fun k =>
        impB (decide (conv (F.Ka k e) = r))
          (ballB (F.pk k) (fun a => decide (c ∈ F.phase k a))))
    | _ => true)

/-- Universal-propagation checks for one kernel phase. -/
def kAllB (F : FinMT) (k a : Nat) : Bool :=
  (F.phase k a).all (fun D => match D with
    | .all r c =>
      ballB F.nE (fun f =>
        impB (decide (F.Ka k f = r)) (decide (c ∈ F.tE f))) &&
      ballB F.nK (fun k' =>
        impB ((!decide (k = k')) && decide (F.Qa k k' = r))
          (ballB (F.pk k') (fun b => decide (c ∈ F.phase k' b)))) &&
      (match r with
        | .pp => ballB (F.pk k) (fun b => decide (c ∈ F.phase k b))
        | .ppi => ballB (F.pk k) (fun b => decide (c ∈ F.phase k b))
        | .eq => decide (c ∈ F.phase k a)
        | _ => true)
    | _ => true)

/-- Fulfilment checks for one external type list. -/
def eExB (F : FinMT) (e : Nat) : Bool :=
  (F.tE e).all (fun D => match D with
    | .ex r c =>
      bexB F.nE (fun f =>
        decide (F.Ea e f = r) && decide (c ∈ F.tE f)) ||
      bexB F.nK (fun k =>
        decide (conv (F.Ka k e) = r) &&
        bexB (F.pk k) (fun a => decide (c ∈ F.phase k a)))
    | _ => true)

/-- Fulfilment checks for one kernel phase. -/
def kExB (F : FinMT) (k a : Nat) : Bool :=
  (F.phase k a).all (fun D => match D with
    | .ex r c =>
      bexB F.nE (fun f =>
        decide (F.Ka k f = r) && decide (c ∈ F.tE f)) ||
      (decide (r = cdir (F.upa k)) &&
        bexB (F.pk k) (fun b => decide (c ∈ F.phase k b))) ||
      (decide (r = eq) && decide (c ∈ F.phase k a)) ||
      bexB F.nK (fun k' =>
        (!decide (k = k')) && decide (F.Qa k k' = r) &&
        bexB (F.pk k') (fun b => decide (c ∈ F.phase k' b)))
    | _ => true)

/-- THE CHECKER: total, computable, oracle-free. -/
def mtOkB (F : FinMT) : Bool :=
  ballB F.nK (fun k => decide (0 < F.pk k)) &&
  F.frameB &&
  ballB F.nE (fun e => propB (F.tE e)) &&
  ballB F.nK (fun k => ballB (F.pk k) (fun a => propB (F.phase k a))) &&
  ballB F.nE (fun e => F.eAllB e) &&
  ballB F.nK (fun k => ballB (F.pk k) (fun a => F.kAllB k a)) &&
  ballB F.nE (fun e => F.eExB e) &&
  ballB F.nK (fun k => ballB (F.pk k) (fun a => F.kExB k a))

/-- Root acceptance: `root < nE` names an external; otherwise a kernel,
    accepted if `C0` sits at ANY of its phases (rung `a` realizes phase
    `a`). -/
def rootB (F : FinMT) (root : Nat) (C0 : Concept) : Bool :=
  if root < F.nE then decide (C0 ∈ F.tE root)
  else decide (root < F.nE + F.nK) &&
    bexB (F.pk (root - F.nE))
      (fun a => decide (C0 ∈ F.phase (root - F.nE) a))

/-- The acceptance predicate: certificate checks + root carries `C0`. -/
def mtAcceptB (F : FinMT) (root : Nat) (C0 : Concept) : Bool :=
  F.mtOkB && F.rootB root C0

end FinMT

/-! ### Soundness of the checker -/

/-- Encode the decoded certificate's carrier indices into the raw
    range: externals first, then kernels. -/
def encIdx (F : FinMT) : (Fin F.nE ⊕ Fin F.nK) → Nat
  | .inl e => e.val
  | .inr k => F.nE + k.val

theorem encIdx_lt (F : FinMT) (x : Fin F.nE ⊕ Fin F.nK) :
    encIdx F x < F.nE + F.nK := by
  rcases x with e | k
  · have := e.isLt
    show e.val < F.nE + F.nK
    omega
  · have := k.isLt
    show F.nE + k.val < F.nE + F.nK
    omega

theorem encIdx_inj (F : FinMT) {x y : Fin F.nE ⊕ Fin F.nK}
    (h : encIdx F x = encIdx F y) : x = y := by
  rcases x with e | k <;> rcases y with f | k'
  · exact congrArg Sum.inl (Fin.ext h)
  · exfalso
    have h1 : e.val = F.nE + k'.val := h
    have := e.isLt
    omega
  · exfalso
    have h1 : F.nE + k.val = f.val := h
    have := f.isLt
    omega
  · have h1 : F.nE + k.val = F.nE + k'.val := h
    exact congrArg Sum.inr (Fin.ext (by omega))

/-- The raw network at encoded indices IS the decoded quotient
    network. -/
theorem qraw_corr (F : FinMT) (x y : Fin F.nE ⊕ Fin F.nK) :
    F.qraw (encIdx F x) (encIdx F y)
      = qnet (decodeMT F).E (decodeMT F).K (decodeMT F).Q x y := by
  rcases x with e | k <;> rcases y with f | k'
  · show F.qraw e.val f.val = F.Ea e.val f.val
    unfold FinMT.qraw
    rw [if_pos e.isLt, if_pos f.isLt]
  · show F.qraw e.val (F.nE + k'.val) = conv (F.Ka k'.val e.val)
    unfold FinMT.qraw
    rw [if_pos e.isLt, if_neg (by omega : ¬ F.nE + k'.val < F.nE),
      Nat.add_sub_cancel_left]
  · show F.qraw (F.nE + k.val) f.val = F.Ka k.val f.val
    unfold FinMT.qraw
    rw [if_neg (by omega : ¬ F.nE + k.val < F.nE), if_pos f.isLt,
      Nat.add_sub_cancel_left]
  · show F.qraw (F.nE + k.val) (F.nE + k'.val)
      = (if k = k' then eq else F.Qa k.val k'.val)
    unfold FinMT.qraw
    rw [if_neg (by omega : ¬ F.nE + k.val < F.nE),
      if_neg (by omega : ¬ F.nE + k'.val < F.nE)]
    by_cases hk : k = k'
    · subst hk
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun hh => hk (Fin.ext (Nat.add_left_cancel hh))),
        if_neg hk, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]

/-- The frame checks certify the decoded quotient frame. -/
theorem frameB_sound (F : FinMT) (h : F.frameB = true) :
    Frame (qnet (decodeMT F).E (decodeMT F).K (decodeMT F).Q) := by
  simp only [FinMT.frameB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hrefl, heqid⟩, hconv⟩, hcomp⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    have h1 := of_decide_eq_true
      (ballB_true hrefl (encIdx F x) (encIdx_lt F x))
    rw [qraw_corr F x x] at h1
    exact h1
  · intro x y hxy
    have h1 := ballB_true (ballB_true heqid (encIdx F x) (encIdx_lt F x))
      (encIdx F y) (encIdx_lt F y)
    have hq : F.qraw (encIdx F x) (encIdx F y) = eq := by
      rw [qraw_corr F x y]
      exact hxy
    exact encIdx_inj F (of_decide_eq_true (impB_true h1 (decide_eq_true hq)))
  · intro x y
    have h1 := of_decide_eq_true
      (ballB_true (ballB_true hconv (encIdx F x) (encIdx_lt F x))
        (encIdx F y) (encIdx_lt F y))
    rw [qraw_corr F y x, qraw_corr F x y] at h1
    exact h1
  · intro x y z
    have h1 := of_decide_eq_true
      (ballB_true (ballB_true (ballB_true hcomp (encIdx F x)
        (encIdx_lt F x)) (encIdx F y) (encIdx_lt F y))
        (encIdx F z) (encIdx_lt F z))
    rw [qraw_corr F x z, qraw_corr F x y, qraw_corr F y z] at h1
    exact h1

/-- Split the per-phase universal checks at a member. -/
theorem kAllB_split (F : FinMT) {k a : Nat} (hk : k < F.nK)
    (ha : a < F.pk k)
    (h : ballB F.nK (fun k => ballB (F.pk k) (fun a => F.kAllB k a))
      = true)
    {r : Atom} {c : Concept} (hmem : Concept.all r c ∈ F.phase k a) :
    ballB F.nE (fun f => impB (decide (F.Ka k f = r))
      (decide (c ∈ F.tE f))) = true ∧
    ballB F.nK (fun k' => impB ((!decide (k = k')) &&
      decide (F.Qa k k' = r))
      (ballB (F.pk k') (fun b => decide (c ∈ F.phase k' b)))) = true ∧
    (r = pp →
      ballB (F.pk k) (fun b => decide (c ∈ F.phase k b)) = true) ∧
    (r = ppi →
      ballB (F.pk k) (fun b => decide (c ∈ F.phase k b)) = true) ∧
    (r = eq → decide (c ∈ F.phase k a) = true) := by
  have h1 := ballB_true (ballB_true h k hk) a ha
  simp only [FinMT.kAllB] at h1
  have h2 := List.all_eq_true.mp h1 _ hmem
  have h3 := andB_split h2
  have h4 := andB_split h3.1
  refine ⟨h4.1, h4.2, ?_, ?_, ?_⟩ <;>
    (intro hr; subst hr; exact h3.2)

/-- Split the per-external universal checks at a member. -/
theorem eAllB_split (F : FinMT) {e : Nat} (he : e < F.nE)
    (h : ballB F.nE (fun e => F.eAllB e) = true)
    {r : Atom} {c : Concept} (hmem : Concept.all r c ∈ F.tE e) :
    ballB F.nE (fun f => impB (decide (F.Ea e f = r))
      (decide (c ∈ F.tE f))) = true ∧
    ballB F.nK (fun k => impB (decide (conv (F.Ka k e) = r))
      (ballB (F.pk k) (fun a => decide (c ∈ F.phase k a)))) = true := by
  have h1 := ballB_true h e he
  simp only [FinMT.eAllB] at h1
  exact andB_split (List.all_eq_true.mp h1 _ hmem)

/-- Split the propositional checks. -/
theorem propB_parts {L : List Concept} (h : FinMT.propB L = true) :
    Concept.bot ∉ L ∧
    (∀ D ∈ L, (match D with
      | Concept.atom a => !decide (Concept.natom a ∈ L)
      | Concept.and c d => decide (c ∈ L) && decide (d ∈ L)
      | Concept.or c d => decide (c ∈ L) || decide (d ∈ L)
      | _ => true) = true) := by
  simp only [FinMT.propB, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_false (notB_true h.1), List.all_eq_true.mp h.2⟩

/-- ROUND-C SOUNDNESS: the Boolean checker certifies a valid decoded
    certificate. -/
theorem mtOkB_sound (F : FinMT) (h : F.mtOkB = true) :
    MultiTierOk (decodeMT F) := by
  simp only [FinMT.mtOkB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hhp, hframe⟩, hpropE⟩, hpropK⟩, heall⟩, hkall⟩, heex⟩,
    hkex⟩ := h
  refine
    { hp := ?_, frame_q := ?_, e_clash := ?_, e_nobot := ?_,
      e_and := ?_, e_or := ?_, k_clash := ?_, k_nobot := ?_,
      k_and := ?_, k_or := ?_, ee_all := ?_, ek_all := ?_,
      ke_all := ?_, kk_pp := ?_, kk_ppi := ?_, kk_eq := ?_,
      kq_all := ?_, e_ex := ?_, k_ex := ?_ }
  · intro k
    exact of_decide_eq_true (ballB_true hhp k.val k.isLt)
  · exact frameB_sound F hframe
  · intro e a hmem hn
    obtain ⟨_, hall⟩ := propB_parts (ballB_true hpropE e.val e.isLt)
    exact absurd hn
      (of_decide_eq_false (notB_true (hall _ hmem)))
  · intro e
    exact (propB_parts (ballB_true hpropE e.val e.isLt)).1
  · intro e c d hmem
    obtain ⟨_, hall⟩ := propB_parts (ballB_true hpropE e.val e.isLt)
    have h2 := andB_split (hall _ hmem)
    exact ⟨of_decide_eq_true h2.1, of_decide_eq_true h2.2⟩
  · intro e c d hmem
    obtain ⟨_, hall⟩ := propB_parts (ballB_true hpropE e.val e.isLt)
    rcases orB_split (hall _ hmem) with h2 | h2
    · exact Or.inl (of_decide_eq_true h2)
    · exact Or.inr (of_decide_eq_true h2)
  · intro k a ha n hmem hn
    obtain ⟨_, hall⟩ := propB_parts
      (ballB_true (ballB_true hpropK k.val k.isLt) a ha)
    exact absurd hn
      (of_decide_eq_false (notB_true (hall _ hmem)))
  · intro k a ha
    exact (propB_parts
      (ballB_true (ballB_true hpropK k.val k.isLt) a ha)).1
  · intro k a ha c d hmem
    obtain ⟨_, hall⟩ := propB_parts
      (ballB_true (ballB_true hpropK k.val k.isLt) a ha)
    have h2 := andB_split (hall _ hmem)
    exact ⟨of_decide_eq_true h2.1, of_decide_eq_true h2.2⟩
  · intro k a ha c d hmem
    obtain ⟨_, hall⟩ := propB_parts
      (ballB_true (ballB_true hpropK k.val k.isLt) a ha)
    rcases orB_split (hall _ hmem) with h2 | h2
    · exact Or.inl (of_decide_eq_true h2)
    · exact Or.inr (of_decide_eq_true h2)
  · intro e f r c hmem hEr
    obtain ⟨hee, _⟩ := eAllB_split F e.isLt heall hmem
    exact of_decide_eq_true
      (impB_true (ballB_true hee f.val f.isLt) (decide_eq_true hEr))
  · intro e r c hmem k hKr a ha
    obtain ⟨_, hek⟩ := eAllB_split F e.isLt heall hmem
    exact of_decide_eq_true
      (ballB_true (impB_true (ballB_true hek k.val k.isLt)
        (decide_eq_true hKr)) a ha)
  · intro k a ha r c hmem f hKf
    obtain ⟨hke, _, _⟩ := kAllB_split F k.isLt ha hkall hmem
    exact of_decide_eq_true
      (impB_true (ballB_true hke f.val f.isLt) (decide_eq_true hKf))
  · intro k a ha c hmem b hb
    obtain ⟨_, _, hkk, _, _⟩ := kAllB_split F k.isLt ha hkall hmem
    exact of_decide_eq_true (ballB_true (hkk rfl) b hb)
  · intro k a ha c hmem b hb
    obtain ⟨_, _, _, hkk, _⟩ := kAllB_split F k.isLt ha hkall hmem
    exact of_decide_eq_true (ballB_true (hkk rfl) b hb)
  · intro k a ha c hmem
    obtain ⟨_, _, _, _, hkk⟩ := kAllB_split F k.isLt ha hkall hmem
    exact of_decide_eq_true (hkk rfl)
  · intro k k' hne a ha r c hmem hQ b hb
    obtain ⟨_, hkq, _, _, _⟩ := kAllB_split F k.isLt ha hkall hmem
    have hQ' : F.Qa k.val k'.val = r := hQ
    have hprem : ((!decide (k.val = k'.val)) &&
        decide (F.Qa k.val k'.val = r)) = true := by
      rw [decide_eq_false (fun hh => hne (Fin.ext hh)),
        decide_eq_true hQ']
      rfl
    exact of_decide_eq_true
      (ballB_true (impB_true (ballB_true hkq k'.val k'.isLt) hprem)
        b hb)
  · intro e r c hmem
    have h1 := ballB_true heex e.val e.isLt
    simp only [FinMT.eExB] at h1
    rcases orB_split (List.all_eq_true.mp h1 _ hmem) with
      h2 | h2
    · obtain ⟨f, hf, hb⟩ := bexB_true h2
      have h3 := andB_split hb
      exact Or.inl ⟨⟨f, hf⟩, of_decide_eq_true h3.1,
        of_decide_eq_true h3.2⟩
    · obtain ⟨k, hk, hb⟩ := bexB_true h2
      have h3 := andB_split hb
      obtain ⟨a, ha, hca⟩ := bexB_true h3.2
      exact Or.inr ⟨⟨k, hk⟩, of_decide_eq_true h3.1, a, ha,
        of_decide_eq_true hca⟩
  · intro k a ha r c hmem
    have h1 := ballB_true (ballB_true hkex k.val k.isLt) a ha
    simp only [FinMT.kExB] at h1
    have h2 := List.all_eq_true.mp h1 _ hmem
    rcases orB_split h2 with h3 | hD
    · rcases orB_split h3 with h4 | hC
      · rcases orB_split h4 with hA | hB
        · obtain ⟨f, hf, hb⟩ := bexB_true hA
          have h5 := andB_split hb
          exact Or.inl ⟨⟨f, hf⟩, of_decide_eq_true h5.1,
            of_decide_eq_true h5.2⟩
        · have h5 := andB_split hB
          obtain ⟨b, hb, hcb⟩ := bexB_true h5.2
          exact Or.inr (Or.inl ⟨of_decide_eq_true h5.1, b, hb,
            of_decide_eq_true hcb⟩)
      · have h5 := andB_split hC
        exact Or.inr (Or.inr (Or.inl ⟨of_decide_eq_true h5.1,
          of_decide_eq_true h5.2⟩))
    · obtain ⟨k', hk', hb⟩ := bexB_true hD
      have h5 := andB_split hb
      have h6 := andB_split h5.1
      obtain ⟨b, hb', hcb⟩ := bexB_true h5.2
      refine Or.inr (Or.inr (Or.inr ⟨⟨k', hk'⟩, ?_,
        of_decide_eq_true h6.2, b, hb', of_decide_eq_true hcb⟩))
      intro hh
      exact absurd (congrArg Fin.val hh)
        (of_decide_eq_false (notB_true h6.1))

/-- ROUND-C CAPSTONE: acceptance by the executable checker yields a
    model — first-order certificate to model, end to end. -/
theorem mtAcceptB_sound (F : FinMT) (root : Nat) (C0 : Concept)
    (h : F.mtAcceptB root C0 = true) : Satisfiable C0 := by
  have h' := andB_split h
  have hOk := mtOkB_sound F h'.1
  have hroot := h'.2
  rw [FinMT.rootB] at hroot
  by_cases hr : root < F.nE
  · rw [if_pos hr] at hroot
    exact multiTier_sound (decodeMT F) hOk (Sum.inl ⟨root, hr⟩) C0
      (of_decide_eq_true hroot)
  · rw [if_neg hr] at hroot
    have h2 := andB_split hroot
    have hlt := of_decide_eq_true h2.1
    obtain ⟨a, ha, hca⟩ := bexB_true h2.2
    refine multiTier_sound (decodeMT F) hOk
      (Sum.inr (⟨root - F.nE, by omega⟩, a)) C0 ?_
    show C0 ∈ F.phase (root - F.nE) (a % F.pk (root - F.nE))
    rw [Nat.mod_eq_of_lt ha]
    exact of_decide_eq_true hca

/-! ### Round-C non-vacuity: the two-tower certificate as pure data

`cbothFin` is the `FinMT` encoding of the round-B certificate — plain
lists, no functions.  The executable checker accepts it (`by decide` —
the checker actually runs inside the kernel), giving a second,
fully-computational route to `Satisfiable Cboth`. -/

def cbothFin : FinMT where
  tauE := []
  E := []
  K := [[], []]
  Q := [[dr, dr], [dr, dr]]
  up := [true, false]
  phases := [[upList], [dnList]]

theorem cbothFin_accept : cbothFin.mtAcceptB 0 Cboth = true := by
  decide

theorem cboth_satisfiable_exec : Satisfiable Cboth :=
  mtAcceptB_sound cbothFin 0 Cboth cbothFin_accept

/-! ## Round D1 (2026-07-23): checker completeness + the decision
reduction

The checker so far is SOUND (acceptance ⟹ model).  Round D1 adds the
converse — `mtOkB_iff`: the Boolean checker accepts EXACTLY the valid
decoded certificates — plus acceptance-completeness (a valid
certificate carrying `C0` at any node yields an accepted root index)
and the fragment's decision-grade reduction
`decidableSat_of_codes`: a fixed candidate list + the completeness
premise (exactly the round-D2 extraction: every satisfiable ∀PO-free
concept has an accepted code in the list) decide satisfiability.
This mirrors the normative artifact's `decidableSat_of_finScheme`;
what remains open is solely the premise — the extraction with its
`K(C₀)` bound. -/

/-! ### Intro-direction Bool helpers -/

theorem ballB_intro {n : Nat} {f : Nat → Bool}
    (h : ∀ i, i < n → f i = true) : ballB n f = true :=
  List.all_eq_true.mpr (fun i hi => h i (List.mem_range.mp hi))

theorem bexB_intro {n : Nat} {f : Nat → Bool} (i : Nat) (hi : i < n)
    (hf : f i = true) : bexB n f = true :=
  List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, hf⟩

theorem impB_intro {a b : Bool} (h : a = true → b = true) :
    impB a b = true := by
  cases a with
  | false => rfl
  | true => exact h rfl

theorem andB_intro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  subst ha; subst hb; rfl

theorem orB_inl {a b : Bool} (ha : a = true) : (a || b) = true := by
  subst ha; rfl

theorem orB_inr {a b : Bool} (hb : b = true) : (a || b) = true := by
  subst hb
  cases a <;> rfl

theorem notB_intro {b : Bool} (h : b = false) : (!b) = true := by
  subst h; rfl

/-! ### The inverse index correspondence -/

/-- Decode a raw index into the certificate carrier. -/
def decIdx (F : FinMT) (x : Nat) (hx : x < F.nE + F.nK) :
    Fin F.nE ⊕ Fin F.nK :=
  if h : x < F.nE then .inl ⟨x, h⟩ else .inr ⟨x - F.nE, by omega⟩

theorem encIdx_decIdx (F : FinMT) (x : Nat) (hx : x < F.nE + F.nK) :
    encIdx F (decIdx F x hx) = x := by
  unfold decIdx
  by_cases h : x < F.nE
  · rw [dif_pos h]
    rfl
  · rw [dif_neg h]
    show F.nE + (x - F.nE) = x
    omega

/-- The raw network at arbitrary in-range indices IS the decoded
    quotient network (inverse form of `qraw_corr`). -/
theorem qraw_eq (F : FinMT) (x y : Nat) (hx : x < F.nE + F.nK)
    (hy : y < F.nE + F.nK) :
    F.qraw x y = qnet (decodeMT F).E (decodeMT F).K (decodeMT F).Q
      (decIdx F x hx) (decIdx F y hy) :=
  calc F.qraw x y
      = F.qraw (encIdx F (decIdx F x hx)) (encIdx F (decIdx F y hy)) :=
        by rw [encIdx_decIdx, encIdx_decIdx]
    _ = qnet (decodeMT F).E (decodeMT F).K (decodeMT F).Q
        (decIdx F x hx) (decIdx F y hy) :=
        qraw_corr F (decIdx F x hx) (decIdx F y hy)

/-! ### Completeness of each check group -/

theorem frameB_complete (F : FinMT)
    (h : Frame (qnet (decodeMT F).E (decodeMT F).K (decodeMT F).Q)) :
    F.frameB = true := by
  refine andB_intro (andB_intro (andB_intro ?_ ?_) ?_) ?_
  · exact ballB_intro (fun x hx => decide_eq_true
      (by rw [qraw_eq F x x hx hx]; exact h.refl_eq _))
  · refine ballB_intro (fun x hx => ballB_intro (fun y hy =>
      impB_intro (fun hd => ?_)))
    have hq := of_decide_eq_true hd
    rw [qraw_eq F x y hx hy] at hq
    have h2 := congrArg (encIdx F) (h.eq_id _ _ hq)
    rw [encIdx_decIdx F x hx, encIdx_decIdx F y hy] at h2
    exact decide_eq_true h2
  · exact ballB_intro (fun x hx => ballB_intro (fun y hy =>
      decide_eq_true (by
        rw [qraw_eq F y x hy hx, qraw_eq F x y hx hy]
        exact h.conv_ _ _)))
  · exact ballB_intro (fun x hx => ballB_intro (fun y hy =>
      ballB_intro (fun z hz => decide_eq_true (by
        rw [qraw_eq F x z hx hz, qraw_eq F x y hx hy,
          qraw_eq F y z hy hz]
        exact h.comp_ _ _ _))))

theorem propB_complete {L : List Concept}
    (hnb : Concept.bot ∉ L)
    (hcl : ∀ a, Concept.atom a ∈ L → Concept.natom a ∉ L)
    (hand : ∀ c d, Concept.and c d ∈ L → c ∈ L ∧ d ∈ L)
    (hor : ∀ c d, Concept.or c d ∈ L → c ∈ L ∨ d ∈ L) :
    FinMT.propB L = true := by
  refine andB_intro (notB_intro (decide_eq_false hnb))
    (List.all_eq_true.mpr (fun D hD => ?_))
  cases D with
  | top => rfl
  | bot => rfl
  | atom a => exact notB_intro (decide_eq_false (hcl a hD))
  | natom a => rfl
  | and c d =>
    obtain ⟨hc, hd⟩ := hand c d hD
    exact andB_intro (decide_eq_true hc) (decide_eq_true hd)
  | or c d =>
    rcases hor c d hD with hc | hc
    · exact orB_inl (decide_eq_true hc)
    · exact orB_inr (decide_eq_true hc)
  | ex r c => rfl
  | all r c => rfl

theorem eAllB_complete (F : FinMT) (h : MultiTierOk (decodeMT F))
    {e : Nat} (he : e < F.nE) : F.eAllB e = true := by
  refine List.all_eq_true.mpr (fun D hD => ?_)
  cases D with
  | top => rfl
  | bot => rfl
  | atom a => rfl
  | natom a => rfl
  | and c d => rfl
  | or c d => rfl
  | ex r c => rfl
  | all r c =>
    refine andB_intro ?_ ?_
    · exact ballB_intro (fun f hf => impB_intro (fun hd =>
        decide_eq_true (h.ee_all ⟨e, he⟩ ⟨f, hf⟩ r c hD
          (of_decide_eq_true hd))))
    · exact ballB_intro (fun k hk => impB_intro (fun hd =>
        ballB_intro (fun a ha => decide_eq_true
          (h.ek_all ⟨e, he⟩ r c hD ⟨k, hk⟩
            (of_decide_eq_true hd) a ha))))

theorem kAllB_complete (F : FinMT) (h : MultiTierOk (decodeMT F))
    {k a : Nat} (hk : k < F.nK) (ha : a < F.pk k) :
    F.kAllB k a = true := by
  refine List.all_eq_true.mpr (fun D hD => ?_)
  cases D with
  | top => rfl
  | bot => rfl
  | atom n => rfl
  | natom n => rfl
  | and c d => rfl
  | or c d => rfl
  | ex r c => rfl
  | all r c =>
    refine andB_intro (andB_intro ?_ ?_) ?_
    · exact ballB_intro (fun f hf => impB_intro (fun hd =>
        decide_eq_true (h.ke_all ⟨k, hk⟩ a ha r c hD ⟨f, hf⟩
          (of_decide_eq_true hd))))
    · refine ballB_intro (fun k' hk' => impB_intro (fun hprem => ?_))
      have h2 := andB_split hprem
      have hne : (⟨k, hk⟩ : Fin F.nK) ≠ ⟨k', hk'⟩ := fun heq =>
        (of_decide_eq_false (notB_true h2.1)) (congrArg Fin.val heq)
      exact ballB_intro (fun b hb => decide_eq_true
        (h.kq_all ⟨k, hk⟩ ⟨k', hk'⟩ hne a ha r c hD
          (of_decide_eq_true h2.2) b hb))
    · cases r with
      | pp => exact ballB_intro (fun b hb => decide_eq_true
          (h.kk_pp ⟨k, hk⟩ a ha c hD b hb))
      | ppi => exact ballB_intro (fun b hb => decide_eq_true
          (h.kk_ppi ⟨k, hk⟩ a ha c hD b hb))
      | eq => exact decide_eq_true (h.kk_eq ⟨k, hk⟩ a ha c hD)
      | po => rfl
      | dr => rfl

theorem eExB_complete (F : FinMT) (h : MultiTierOk (decodeMT F))
    {e : Nat} (he : e < F.nE) : F.eExB e = true := by
  refine List.all_eq_true.mpr (fun D hD => ?_)
  cases D with
  | top => rfl
  | bot => rfl
  | atom a => rfl
  | natom a => rfl
  | and c d => rfl
  | or c d => rfl
  | all r c => rfl
  | ex r c =>
    rcases h.e_ex ⟨e, he⟩ r c hD with ⟨f, hEf, hcf⟩ | ⟨k, hK, a, ha, hca⟩
    · exact orB_inl (bexB_intro f.val f.isLt
        (andB_intro (decide_eq_true hEf) (decide_eq_true hcf)))
    · exact orB_inr (bexB_intro k.val k.isLt
        (andB_intro (decide_eq_true hK)
          (bexB_intro a ha (decide_eq_true hca))))

theorem kExB_complete (F : FinMT) (h : MultiTierOk (decodeMT F))
    {k a : Nat} (hk : k < F.nK) (ha : a < F.pk k) :
    F.kExB k a = true := by
  refine List.all_eq_true.mpr (fun D hD => ?_)
  cases D with
  | top => rfl
  | bot => rfl
  | atom n => rfl
  | natom n => rfl
  | and c d => rfl
  | or c d => rfl
  | all r c => rfl
  | ex r c =>
    rcases h.k_ex ⟨k, hk⟩ a ha r c hD with
      ⟨f, hKf, hcf⟩ | ⟨hrd, b, hb, hcb⟩ | ⟨hreq, hc⟩ |
      ⟨k', hne, hQ, b, hb, hcb⟩
    · exact orB_inl (orB_inl (orB_inl (bexB_intro f.val f.isLt
        (andB_intro (decide_eq_true hKf) (decide_eq_true hcf)))))
    · exact orB_inl (orB_inl (orB_inr
        (andB_intro (decide_eq_true hrd)
          (bexB_intro b hb (decide_eq_true hcb)))))
    · exact orB_inl (orB_inr
        (andB_intro (decide_eq_true hreq) (decide_eq_true hc)))
    · refine orB_inr (bexB_intro k'.val k'.isLt
        (andB_intro (andB_intro ?_ (decide_eq_true hQ))
          (bexB_intro b hb (decide_eq_true hcb))))
      exact notB_intro (decide_eq_false (fun hh => hne (Fin.ext hh)))

/-- ROUND-D1 COMPLETENESS: the checker accepts every valid decoded
    certificate. -/
theorem mtOkB_complete (F : FinMT) (h : MultiTierOk (decodeMT F)) :
    F.mtOkB = true := by
  refine andB_intro (andB_intro (andB_intro (andB_intro (andB_intro
    (andB_intro (andB_intro ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact ballB_intro (fun k hk => decide_eq_true (h.hp ⟨k, hk⟩))
  · exact frameB_complete F h.frame_q
  · exact ballB_intro (fun e he => propB_complete
      (h.e_nobot ⟨e, he⟩) (h.e_clash ⟨e, he⟩)
      (h.e_and ⟨e, he⟩) (h.e_or ⟨e, he⟩))
  · exact ballB_intro (fun k hk => ballB_intro (fun a ha =>
      propB_complete (h.k_nobot ⟨k, hk⟩ a ha) (h.k_clash ⟨k, hk⟩ a ha)
        (h.k_and ⟨k, hk⟩ a ha) (h.k_or ⟨k, hk⟩ a ha)))
  · exact ballB_intro (fun e he => eAllB_complete F h he)
  · exact ballB_intro (fun k hk => ballB_intro (fun a ha =>
      kAllB_complete F h hk ha))
  · exact ballB_intro (fun e he => eExB_complete F h he)
  · exact ballB_intro (fun k hk => ballB_intro (fun a ha =>
      kExB_complete F h hk ha))

/-- The checker accepts EXACTLY the valid decoded certificates. -/
theorem mtOkB_iff (F : FinMT) :
    F.mtOkB = true ↔ MultiTierOk (decodeMT F) :=
  ⟨mtOkB_sound F, mtOkB_complete F⟩

/-- ACCEPTANCE COMPLETENESS: a valid certificate carrying `C0` at any
    node of its unfolding yields an accepted root index. -/
theorem mtAcceptB_complete (F : FinMT) (h : MultiTierOk (decodeMT F))
    (x : Fin F.nE ⊕ Fin F.nK × Nat) (C0 : Concept)
    (hC0 : C0 ∈ mtLabel (decodeMT F) x) :
    ∃ root, F.mtAcceptB root C0 = true := by
  rcases x with e | ⟨k, i⟩
  · refine ⟨e.val, andB_intro (mtOkB_complete F h) ?_⟩
    show F.rootB e.val C0 = true
    rw [FinMT.rootB, if_pos e.isLt]
    exact decide_eq_true hC0
  · refine ⟨F.nE + k.val, andB_intro (mtOkB_complete F h) ?_⟩
    show F.rootB (F.nE + k.val) C0 = true
    rw [FinMT.rootB, if_neg (by omega : ¬ F.nE + k.val < F.nE),
      Nat.add_sub_cancel_left]
    refine andB_intro (decide_eq_true (by have := k.isLt; omega)) ?_
    exact bexB_intro (i % F.pk k.val) (Nat.mod_lt i (h.hp k))
      (decide_eq_true hC0)

/-- THE DECISION REDUCTION (the fragment's
    `decidableSat_of_finScheme`): a fixed finite list of candidate
    codes + the completeness premise — every satisfiable concept has an
    accepted code in the list, which is EXACTLY the round-D2 extraction
    with its `K(C₀)` bound — decide satisfiability.  Soundness needs no
    premise: any accepted code yields a model. -/
def decidableSat_of_codes (C0 : Concept) (codes : List (FinMT × Nat))
    (hcompl : Satisfiable C0 →
      ∃ p ∈ codes, (p.1).mtAcceptB p.2 C0 = true) :
    Decidable (Satisfiable C0) :=
  if h : codes.any (fun p => (p.1).mtAcceptB p.2 C0) = true then
    .isTrue (by
      obtain ⟨p, _, hacc⟩ := List.any_eq_true.mp h
      exact mtAcceptB_sound p.1 p.2 C0 hacc)
  else
    .isFalse (fun hsat => by
      obtain ⟨p, hmem, hacc⟩ := hcompl hsat
      exact h (List.any_eq_true.mpr ⟨p, hmem, hacc⟩))

/-! ## Round D2a (2026-07-23): model-side chain analysis —
external-relation stabilization

The first stone of the extraction (round D2): the two-tier paper's
"external-relation stabilization" lemma, kernel-checked.  In any RCC5
interpretation, along an ascending `PP`-chain, the relation of a FIXED
external element to the chain follows the monotone transition order

    {DR, PP}  →  {PO, EQ}  →  {PPI}        (rank 0 → 1 → 2)

(each non-self transition strictly increases the rank; `EQ` cannot even
self-loop), hence STABILIZES: it is eventually constant.  With the two
forcing corollaries — `DR`/`PP` propagate backward to ALL earlier chain
positions (`comp(PP,DR) = {DR}`, `comp(PP,PP) = {PP}`), `PPI` forward
to all later ones (`comp(PPI,PPI) = {PPI}`) — this is exactly what
makes one constant certificate edge an honest summary of infinitely
many model edges, now as theorems about arbitrary models rather than
about the unfolding.

These proofs are CLASSICAL (`by_cases` on undecidable ∃ over ℕ —
inevitable: the stabilization index is not computable from an abstract
model), so this section is the first to add `Classical.choice` to the
axiom profile.  Everything before it stays `propext`/`Quot.sound`. -/

/-- The stabilization rank: `DR`/`PP` can still become anything
    non-`PP`-ward, `PO`/`EQ` only deepen, `PPI` is absorbing. -/
def stabRank : Atom → Nat
  | dr => 0
  | pp => 0
  | eq => 1
  | po => 1
  | ppi => 2

/-- Each upward chain step moves the external relation monotonically in
    rank. -/
theorem stabRank_mono : ∀ a b : Atom, b ∈ comp ppi a →
    stabRank a ≤ stabRank b := by
  intro a b
  cases a <;> cases b <;> decide

/-- A rank-preserving step preserves the value. -/
theorem stabRank_fix : ∀ a b : Atom, b ∈ comp ppi a →
    stabRank a = stabRank b → b = a := by
  intro a b
  cases a <;> cases b <;> decide

theorem stabRank_le_two : ∀ a : Atom, stabRank a ≤ 2 := by
  intro a
  cases a <;> decide

section ModelChain

variable {α : Type} {I : Interp α} (hI : RCC5Interp I)
  {c : Nat → α} (hdom : ∀ i, I.dom (c i))
  (hstep : ∀ i, I.rho (c i) (c (i + 1)) = pp)

include hI hdom hstep

/-- Chain transitivity in the model: strictly earlier is `PP`. -/
theorem chain_model_pp : ∀ i j, i < j → I.rho (c i) (c j) = pp := by
  have aux : ∀ i d, I.rho (c i) (c (i + 1 + d)) = pp := by
    intro i d
    induction d with
    | zero => exact hstep i
    | succ d ih =>
      have h1 := hI.comp_ (c i) (c (i + 1 + d)) (c (i + 1 + d + 1))
        (hdom i) (hdom (i + 1 + d)) (hdom (i + 1 + d + 1))
      rw [ih, hstep (i + 1 + d)] at h1
      rw [show comp pp pp = [pp] from rfl] at h1
      exact List.mem_singleton.mp h1
  intro i j hij
  have hj : j = i + 1 + (j - i - 1) := by omega
  rw [hj]
  exact aux i (j - i - 1)

/-- Chain elements are pairwise distinct (strong EQ). -/
theorem chain_model_distinct : ∀ i j, i < j → c i ≠ c j := by
  intro i j hij heq
  have h1 := chain_model_pp hI hdom hstep i j hij
  rw [heq] at h1
  rw [hI.refl_eq (c j) (hdom j)] at h1
  exact absurd h1 (by decide)

/-- Strictly later is `PPI`. -/
theorem chain_model_ppi : ∀ i j, i < j → I.rho (c j) (c i) = ppi := by
  intro i j hij
  rw [hI.conv_ (c i) (c j) (hdom i) (hdom j),
    chain_model_pp hI hdom hstep i j hij]
  rfl

variable {e : α} (hedom : I.dom e)

include hedom

/-- The step fact for the external-relation sequence. -/
theorem vstep : ∀ j,
    I.rho (c (j + 1)) e ∈ comp ppi (I.rho (c j) e) := by
  intro j
  have h1 := hI.comp_ (c (j + 1)) (c j) e (hdom (j + 1)) (hdom j) hedom
  rw [chain_model_ppi hI hdom hstep j (j + 1) (Nat.lt_succ_self j)]
    at h1
  exact h1

/-- Rank monotonicity along the chain. -/
theorem vrank_mono : ∀ i j, i ≤ j →
    stabRank (I.rho (c i) e) ≤ stabRank (I.rho (c j) e) := by
  have aux : ∀ i d, stabRank (I.rho (c i) e)
      ≤ stabRank (I.rho (c (i + d)) e) := by
    intro i d
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih =>
      exact Nat.le_trans ih
        (stabRank_mono _ _ (vstep hI hdom hstep hedom (i + d)))
  intro i j hij
  have hj : j = i + (j - i) := by omega
  rw [hj]
  exact aux i (j - i)

/-- THE STABILIZATION THEOREM (two-tier, model side): the relation of a
    fixed external element to an ascending chain is eventually
    constant. -/
theorem external_stabilizes :
    ∃ N w, ∀ j, N ≤ j → I.rho (c j) e = w := by
  -- first stabilize the rank, by cases on which ranks are attained
  have hrank : ∃ N, ∀ j, N ≤ j →
      stabRank (I.rho (c j) e) = stabRank (I.rho (c N) e) := by
    by_cases h2 : ∃ i, stabRank (I.rho (c i) e) = 2
    · obtain ⟨i, hi⟩ := h2
      refine ⟨i, fun j hj => ?_⟩
      have h3 := vrank_mono hI hdom hstep hedom i j hj
      have h4 := stabRank_le_two (I.rho (c j) e)
      omega
    · by_cases h1 : ∃ i, stabRank (I.rho (c i) e) = 1
      · obtain ⟨i, hi⟩ := h1
        refine ⟨i, fun j hj => ?_⟩
        have h3 := vrank_mono hI hdom hstep hedom i j hj
        have h4 : stabRank (I.rho (c j) e) ≠ 2 :=
          fun hh => h2 ⟨j, hh⟩
        have h5 := stabRank_le_two (I.rho (c j) e)
        omega
      · refine ⟨0, fun j _ => ?_⟩
        have h4 : stabRank (I.rho (c j) e) ≠ 2 :=
          fun hh => h2 ⟨j, hh⟩
        have h5 : stabRank (I.rho (c j) e) ≠ 1 :=
          fun hh => h1 ⟨j, hh⟩
        have h6 := stabRank_le_two (I.rho (c j) e)
        have h7 : stabRank (I.rho (c 0) e) ≠ 2 :=
          fun hh => h2 ⟨0, hh⟩
        have h8 : stabRank (I.rho (c 0) e) ≠ 1 :=
          fun hh => h1 ⟨0, hh⟩
        have h9 := stabRank_le_two (I.rho (c 0) e)
        omega
  obtain ⟨N, hN⟩ := hrank
  refine ⟨N, I.rho (c N) e, ?_⟩
  have aux : ∀ d, I.rho (c (N + d)) e = I.rho (c N) e := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      have h1 := vstep hI hdom hstep hedom (N + d)
      rw [ih] at h1
      have h2 : stabRank (I.rho (c N) e)
          = stabRank (I.rho (c (N + d + 1)) e) := by
        rw [hN (N + d + 1) (by omega)]
      exact stabRank_fix _ _ h1 h2
  intro j hj
  have hj2 : j = N + (j - N) := by omega
  rw [hj2]
  exact aux (j - N)

/-- BACKWARD FORCING (`DR`): a `DR`-related external is `DR` to ALL
    earlier chain positions — `comp(PP,DR) = {DR}`. -/
theorem backward_forcing_dr {i : Nat} (h : I.rho (c i) e = dr) :
    ∀ j, j ≤ i → I.rho (c j) e = dr := by
  intro j hj
  rcases Nat.lt_or_ge j i with hlt | hge
  · have h1 := hI.comp_ (c j) (c i) e (hdom j) (hdom i) hedom
    rw [chain_model_pp hI hdom hstep j i hlt, h] at h1
    rw [show comp pp dr = [dr] from rfl] at h1
    exact List.mem_singleton.mp h1
  · have hji : j = i := by omega
    rw [hji]
    exact h

/-- BACKWARD FORCING (`PP`): a containing external contains ALL earlier
    chain positions — `comp(PP,PP) = {PP}`. -/
theorem backward_forcing_pp {i : Nat} (h : I.rho (c i) e = pp) :
    ∀ j, j ≤ i → I.rho (c j) e = pp := by
  intro j hj
  rcases Nat.lt_or_ge j i with hlt | hge
  · have h1 := hI.comp_ (c j) (c i) e (hdom j) (hdom i) hedom
    rw [chain_model_pp hI hdom hstep j i hlt, h] at h1
    rw [show comp pp pp = [pp] from rfl] at h1
    exact List.mem_singleton.mp h1
  · have hji : j = i := by omega
    rw [hji]
    exact h

/-- FORWARD ABSORPTION (`PPI`): a contained external stays inside ALL
    later chain positions — `comp(PPI,PPI) = {PPI}`. -/
theorem forward_absorption_ppi {i : Nat} (h : I.rho (c i) e = ppi) :
    ∀ j, i ≤ j → I.rho (c j) e = ppi := by
  intro j hj
  rcases Nat.lt_or_ge i j with hlt | hge
  · have h1 := hI.comp_ (c j) (c i) e (hdom j) (hdom i) hedom
    rw [chain_model_ppi hI hdom hstep i j hlt, h] at h1
    rw [show comp ppi ppi = [ppi] from rfl] at h1
    exact List.mem_singleton.mp h1
  · have hji : j = i := by omega
    rw [hji]
    exact h

end ModelChain

/-! ## Round D2b (2026-07-23): types, pigeonhole, and segment coherence

The combinatorial spine of the extraction. Three packages:

1. **Subformula closure and model types.** `cl C0` (the finite
   subformula list) and `mty C0 I x` (the classical model type: the
   members of `cl C0` satisfied at `x`), with the semantic Hintikka
   facts every certificate condition will be discharged against
   (clash-freeness, ∧/∨ decomposition, ∀-firing along real edges,
   ∃-witnessing).

2. **The infinite pigeonhole.** Along any infinite sequence over a
   finite universe: a recurrent tail exists (`recurrent_tail`: beyond
   some index, every value that occurs recurs infinitely often), and
   equal-typed pairs exist past any bound (`segment_exists`) — the
   classical selection underlying period descriptors.

3. **Segment coherence.** The theorems justifying the two-tier move of
   cycling a chain segment into a kernel: if `mty (c i) = mty (c j)`,
   then the phase types `mty (c i) … mty (c (j-1))` satisfy the
   kernel's `kk` conditions — `∀PP` obligations propagate UP the chain
   and re-enter through the type-equal endpoints (`seg_pp`), `∀PPI`
   dually down (`seg_ppi`), `∀EQ` reflexively (`seg_eq`). -/

/-! ### Subformula closure -/

/-- The subformula closure, as a list (the formula itself included). -/
def cl : Concept → List Concept
  | .and c d => .and c d :: (cl c ++ cl d)
  | .or c d => .or c d :: (cl c ++ cl d)
  | .ex r c => .ex r c :: cl c
  | .all r c => .all r c :: cl c
  | c => [c]

theorem cl_self : ∀ c : Concept, c ∈ cl c := by
  intro c
  cases c <;> exact List.Mem.head _

/-- `cl` is transitively closed. -/
theorem cl_trans : ∀ e x y : Concept, x ∈ cl e → y ∈ cl x → y ∈ cl e := by
  intro e
  induction e with
  | top =>
    intro x y hx hy
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hy
    · exact nomatch hx'
  | bot =>
    intro x y hx hy
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hy
    · exact nomatch hx'
  | atom a =>
    intro x y hx hy
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hy
    · exact nomatch hx'
  | natom a =>
    intro x y hx hy
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hy
    · exact nomatch hx'
  | and c d ihc ihd =>
    intro x y hx hy
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hy
    · rcases List.mem_append.mp hx' with h | h
      · exact List.mem_cons_of_mem _
          (List.mem_append.mpr (Or.inl (ihc x y h hy)))
      · exact List.mem_cons_of_mem _
          (List.mem_append.mpr (Or.inr (ihd x y h hy)))
  | or c d ihc ihd =>
    intro x y hx hy
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hy
    · rcases List.mem_append.mp hx' with h | h
      · exact List.mem_cons_of_mem _
          (List.mem_append.mpr (Or.inl (ihc x y h hy)))
      · exact List.mem_cons_of_mem _
          (List.mem_append.mpr (Or.inr (ihd x y h hy)))
  | ex r c ihc =>
    intro x y hx hy
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hy
    · exact List.mem_cons_of_mem _ (ihc x y hx' hy)
  | all r c ihc =>
    intro x y hx hy
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hy
    · exact List.mem_cons_of_mem _ (ihc x y hx' hy)

theorem cl_and_left {e c d : Concept} (h : Concept.and c d ∈ cl e) :
    c ∈ cl e :=
  cl_trans e _ c h
    (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (cl_self c))))

theorem cl_and_right {e c d : Concept} (h : Concept.and c d ∈ cl e) :
    d ∈ cl e :=
  cl_trans e _ d h
    (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (cl_self d))))

theorem cl_or_left {e c d : Concept} (h : Concept.or c d ∈ cl e) :
    c ∈ cl e :=
  cl_trans e _ c h
    (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (cl_self c))))

theorem cl_or_right {e c d : Concept} (h : Concept.or c d ∈ cl e) :
    d ∈ cl e :=
  cl_trans e _ d h
    (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (cl_self d))))

theorem cl_ex {e : Concept} {r : Atom} {c : Concept}
    (h : Concept.ex r c ∈ cl e) : c ∈ cl e :=
  cl_trans e _ c h (List.mem_cons_of_mem _ (cl_self c))

theorem cl_all {e : Concept} {r : Atom} {c : Concept}
    (h : Concept.all r c ∈ cl e) : c ∈ cl e :=
  cl_trans e _ c h (List.mem_cons_of_mem _ (cl_self c))

/-! ### Model types (classical) -/

open Classical in
/-- The model type of `x`: the subformulas of `C0` satisfied at `x`.
    Classical (satisfaction over an abstract model is undecidable). -/
noncomputable def mty (C0 : Concept) {α : Type} (I : Interp α)
    (x : α) : List Concept :=
  (cl C0).filter (fun D => decide (sat I x D))

open Classical in
theorem mem_mty {C0 : Concept} {α : Type} {I : Interp α} {x : α}
    {D : Concept} : D ∈ mty C0 I x ↔ D ∈ cl C0 ∧ sat I x D := by
  constructor
  · intro h
    have h2 := List.mem_filter.mp h
    exact ⟨h2.1, of_decide_eq_true h2.2⟩
  · intro ⟨h1, h2⟩
    exact List.mem_filter.mpr ⟨h1, decide_eq_true h2⟩

section ModelTypes

variable {C0 : Concept} {α : Type} {I : Interp α}

theorem mty_clash {x : α} {a : Nat}
    (h : Concept.atom a ∈ mty C0 I x) :
    Concept.natom a ∉ mty C0 I x := by
  intro h2
  exact (mem_mty.mp h2).2 (mem_mty.mp h).2

theorem mty_nobot {x : α} : Concept.bot ∉ mty C0 I x := by
  intro h
  exact (mem_mty.mp h).2

theorem mty_and {x : α} {c d : Concept}
    (h : Concept.and c d ∈ mty C0 I x) :
    c ∈ mty C0 I x ∧ d ∈ mty C0 I x := by
  obtain ⟨hcl, hsat⟩ := mem_mty.mp h
  exact ⟨mem_mty.mpr ⟨cl_and_left hcl, hsat.1⟩,
    mem_mty.mpr ⟨cl_and_right hcl, hsat.2⟩⟩

theorem mty_or {x : α} {c d : Concept}
    (h : Concept.or c d ∈ mty C0 I x) :
    c ∈ mty C0 I x ∨ d ∈ mty C0 I x := by
  obtain ⟨hcl, hsat⟩ := mem_mty.mp h
  rcases hsat with hs | hs
  · exact Or.inl (mem_mty.mpr ⟨cl_or_left hcl, hs⟩)
  · exact Or.inr (mem_mty.mpr ⟨cl_or_right hcl, hs⟩)

/-- ∀-firing along a real edge. -/
theorem mty_all {x y : α} {r : Atom} {E : Concept}
    (h : Concept.all r E ∈ mty C0 I x) (hy : I.dom y)
    (hr : I.rho x y = r) : E ∈ mty C0 I y := by
  obtain ⟨hcl, hsat⟩ := mem_mty.mp h
  exact mem_mty.mpr ⟨cl_all hcl, hsat y hy hr⟩

/-- ∃-witnessing in the model. -/
theorem mty_ex {x : α} {r : Atom} {E : Concept}
    (h : Concept.ex r E ∈ mty C0 I x) :
    ∃ y, I.dom y ∧ I.rho x y = r ∧ E ∈ mty C0 I y := by
  obtain ⟨hcl, hsat⟩ := mem_mty.mp h
  obtain ⟨y, hy, hr, hE⟩ := hsat
  exact ⟨y, hy, hr, mem_mty.mpr ⟨cl_ex hcl, hE⟩⟩

/-- `mty` lands in `cl` — the finite type universe. -/
theorem mty_sub {x : α} : ∀ D ∈ mty C0 I x, D ∈ cl C0 :=
  fun _ hD => (mem_mty.mp hD).1

end ModelTypes

/-! ### The infinite pigeonhole (classical) -/

section Pigeonhole

variable {β : Type}

/-- Values that die out have a common horizon: past `M`, only values
    that recur infinitely often occur. -/
theorem tail_aux (univ : List β) (f : Nat → β) :
    ∃ M, ∀ b ∈ univ, (∃ N, ∀ j, N ≤ j → f j ≠ b) →
      ∀ j, M ≤ j → f j ≠ b := by
  induction univ with
  | nil => exact ⟨0, fun b hb => nomatch hb⟩
  | cons b rest ih =>
    obtain ⟨Mr, hMr⟩ := ih
    by_cases hb : ∃ N, ∀ j, N ≤ j → f j ≠ b
    · obtain ⟨N0, hN0⟩ := hb
      refine ⟨max Mr N0, fun b' hb' hex j hj => ?_⟩
      rcases List.mem_cons.mp hb' with rfl | hmem
      · exact hN0 j (Nat.le_trans (Nat.le_max_right Mr N0) hj)
      · exact hMr b' hmem hex j
          (Nat.le_trans (Nat.le_max_left Mr N0) hj)
    · refine ⟨Mr, fun b' hb' hex j hj => ?_⟩
      rcases List.mem_cons.mp hb' with rfl | hmem
      · exact absurd hex hb
      · exact hMr b' hmem hex j hj

/-- THE RECURRENT TAIL: past some index, every occurring value occurs
    infinitely often. -/
theorem recurrent_tail (univ : List β) (f : Nat → β)
    (hf : ∀ i, f i ∈ univ) :
    ∃ M, ∀ j, M ≤ j → ∀ N, ∃ i, N ≤ i ∧ f i = f j := by
  obtain ⟨M, hM⟩ := tail_aux univ f
  refine ⟨M, fun j hj N => Classical.byContradiction (fun hno => ?_)⟩
  exact hM (f j) (hf j) ⟨N, fun i hi heq => hno ⟨i, hi, heq⟩⟩ j hj rfl

/-- Equal values exist past any bound — the segment selector. -/
theorem segment_exists (univ : List β) (f : Nat → β)
    (hf : ∀ i, f i ∈ univ) (L : Nat) :
    ∃ i j, L ≤ i ∧ i < j ∧ f i = f j := by
  obtain ⟨M, hM⟩ := recurrent_tail univ f hf
  obtain ⟨j, hj, heq⟩ := hM (max M L) (Nat.le_max_left M L) (max M L + 1)
  exact ⟨max M L, j, Nat.le_max_right M L, hj, heq.symm⟩

end Pigeonhole

/-! ### Segment coherence -/

section Segment

variable {α : Type} {I : Interp α} (hI : RCC5Interp I)
  {C0 : Concept}

include hI

/-- `∀PP` climbs: it holds at everything above its holder. -/
theorem sat_all_pp_up {x y : α} (hx : I.dom x) (hy : I.dom y)
    (hr : I.rho x y = pp) {E : Concept}
    (h : sat I x (.all pp E)) : sat I y (.all pp E) := by
  intro z hz hrz
  apply h z hz
  have h1 := hI.comp_ x y z hx hy hz
  rw [hr, hrz] at h1
  rw [show comp pp pp = [pp] from rfl] at h1
  exact List.mem_singleton.mp h1

/-- `∀PPI` descends: it holds at everything below its holder. -/
theorem sat_all_ppi_down {x y : α} (hx : I.dom x) (hy : I.dom y)
    (hr : I.rho y x = pp) {E : Concept}
    (h : sat I x (.all ppi E)) : sat I y (.all ppi E) := by
  intro z hz hrz
  apply h z hz
  have hxy : I.rho x y = ppi := by
    have h2 := hI.conv_ y x hy hx
    rw [hr] at h2
    -- h2 : pp = conv (rho x y)  wait: conv_ y x : rho x y = conv (rho y x)
    rw [h2]
    rfl
  have h1 := hI.comp_ x y z hx hy hz
  rw [hxy, hrz] at h1
  rw [show comp ppi ppi = [ppi] from rfl] at h1
  exact List.mem_singleton.mp h1

variable {c : Nat → α} (hdom : ∀ i, I.dom (c i))
  (hstep : ∀ i, I.rho (c i) (c (i + 1)) = pp)

include hdom hstep

/-- SEGMENT COHERENCE, `PP` side: with type-equal endpoints, a `∀PP`
    obligation anywhere in the segment puts its argument in EVERY
    segment type. -/
theorem seg_pp {i j : Nat} (hij : i < j)
    (hty : mty C0 I (c i) = mty C0 I (c j))
    {a : Nat} (hia : i ≤ a) (haj : a < j) {E : Concept}
    (hE : Concept.all pp E ∈ mty C0 I (c a)) :
    ∀ b, i ≤ b → b < j → E ∈ mty C0 I (c b) := by
  -- the obligation climbs to the top endpoint, transfers to the bottom
  have htop : Concept.all pp E ∈ mty C0 I (c j) := by
    rcases Nat.lt_or_ge a j with hlt | hge
    · obtain ⟨hcl, hsat⟩ := mem_mty.mp hE
      exact mem_mty.mpr ⟨hcl, sat_all_pp_up hI (hdom a) (hdom j)
        (chain_model_pp hI hdom hstep a j hlt) hsat⟩
    · omega
  have hbot : Concept.all pp E ∈ mty C0 I (c i) := by
    rw [hty]; exact htop
  intro b hib hbj
  rcases Nat.lt_or_ge i b with hlt | hge
  · exact mty_all hbot (hdom b) (chain_model_pp hI hdom hstep i b hlt)
  · have hbi : b = i := by omega
    subst hbi
    -- E at the bottom endpoint: fire at the top, transfer back
    have hEj : E ∈ mty C0 I (c j) :=
      mty_all hbot (hdom j) (chain_model_pp hI hdom hstep b j (by omega))
    rw [← hty] at hEj
    exact hEj

/-- SEGMENT COHERENCE, `PPI` side (dual). -/
theorem seg_ppi {i j : Nat} (hij : i < j)
    (hty : mty C0 I (c i) = mty C0 I (c j))
    {a : Nat} (hia : i ≤ a) (_haj : a < j) {E : Concept}
    (hE : Concept.all ppi E ∈ mty C0 I (c a)) :
    ∀ b, i ≤ b → b < j → E ∈ mty C0 I (c b) := by
  -- the obligation descends to the bottom endpoint, transfers to the top
  have hbot : Concept.all ppi E ∈ mty C0 I (c i) := by
    rcases Nat.lt_or_ge i a with hlt | hge
    · obtain ⟨hcl, hsat⟩ := mem_mty.mp hE
      exact mem_mty.mpr ⟨hcl, sat_all_ppi_down hI (hdom a) (hdom i)
        (chain_model_pp hI hdom hstep i a hlt) hsat⟩
    · have hai : a = i := by omega
      subst hai
      exact hE
  have htop : Concept.all ppi E ∈ mty C0 I (c j) := by
    rw [← hty]; exact hbot
  intro b hib hbj
  -- every segment rung is below the top endpoint
  have hppi : I.rho (c j) (c b) = ppi :=
    chain_model_ppi hI hdom hstep b j (by omega)
  exact mty_all htop (hdom b) hppi

omit hstep in
/-- SEGMENT COHERENCE, `EQ` side: reflexive firing. -/
theorem seg_eq {a : Nat} {E : Concept}
    (hE : Concept.all eq E ∈ mty C0 I (c a)) : E ∈ mty C0 I (c a) :=
  mty_all hE (hdom a) (hI.refl_eq (c a) (hdom a))

omit hstep in
/-- `∃EQ` demands are reflexively fulfilled in the model. -/
theorem seg_ex_eq {a : Nat} {E : Concept}
    (hE : Concept.ex eq E ∈ mty C0 I (c a)) : E ∈ mty C0 I (c a) := by
  obtain ⟨y, hy, hr, hEy⟩ := mty_ex hE
  have hxy : c a = y := hI.eq_id (c a) y (hdom a) hy hr
  rw [hxy]
  exact hEy

end Segment

/-! ## Round D2c (2026-07-23): witness selection + syntactic vacuity

Two packages, completing the model-side toolkit of the extraction:

1. **The fragment's syntactic vacuity** — `pofree_cl_all`: a ∀PO-free
   concept's closure contains NO `∀PO` subformula, hence
   (`mty_no_all_po`) no model type ever carries a `∀PO` obligation.
   This is the formal escape-valve fact: every certificate condition
   that quantifies over `∀PO` obligations is VACUOUS on the fragment —
   constant-`PO` interfaces are logically unchallengeable.

2. **Witness selection** ("late picking") — for a type `t` recurring
   infinitely often along a chain: a `DR`- or `PP`-demand in `t` has,
   PAST ANY BOUND, a witness with the CONSTANT demanded relation to all
   chain positions up to that bound (`dr_witness_all_below`,
   `pp_witness_all_below` — pick the witness at a late occurrence,
   backward forcing does the rest); a `PPI`-demand has a witness with
   the constant relation to all positions past some anchor
   (`ppi_witness_all_above` — forward absorption).  These are exactly
   the constant-interface rows a segment-kernel's designated witnesses
   need. -/

/-! ### Syntactic vacuity of ∀PO on the fragment -/

/-- A ∀PO-free concept's subformula closure contains no `∀PO`. -/
theorem pofree_cl_all : ∀ e : Concept, POFree e →
    ∀ (r : Atom) (E : Concept), Concept.all r E ∈ cl e → r ≠ po := by
  intro e
  induction e with
  | top =>
    intro _ r E hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact absurd h (by intro hh; exact Concept.noConfusion hh)
    · exact nomatch h
  | bot =>
    intro _ r E hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact absurd h (by intro hh; exact Concept.noConfusion hh)
    · exact nomatch h
  | atom a =>
    intro _ r E hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact absurd h (by intro hh; exact Concept.noConfusion hh)
    · exact nomatch h
  | natom a =>
    intro _ r E hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact absurd h (by intro hh; exact Concept.noConfusion hh)
    · exact nomatch h
  | and c d ihc ihd =>
    intro hpo r E hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact Concept.noConfusion h
    · rcases List.mem_append.mp h with h' | h'
      · exact ihc hpo.1 r E h'
      · exact ihd hpo.2 r E h'
  | or c d ihc ihd =>
    intro hpo r E hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact Concept.noConfusion h
    · rcases List.mem_append.mp h with h' | h'
      · exact ihc hpo.1 r E h'
      · exact ihd hpo.2 r E h'
  | ex r' c ihc =>
    intro hpo r E hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact Concept.noConfusion h
    · exact ihc hpo r E h
  | all r' c ihc =>
    intro hpo r E hmem
    rcases List.mem_cons.mp hmem with h | h
    · injection h with h1 h2
      subst h1
      exact hpo.1
    · exact ihc hpo.2 r E h

/-- No model type of a ∀PO-free concept carries a `∀PO` obligation. -/
theorem mty_no_all_po {C0 : Concept} (hpo : POFree C0) {α : Type}
    {I : Interp α} {x : α} {E : Concept} :
    Concept.all po E ∉ mty C0 I x := by
  intro h
  exact pofree_cl_all C0 hpo po E (mty_sub _ h) rfl

/-! ### Witness selection ("late picking") -/

section WitnessSelection

variable {α : Type} {I : Interp α} (hI : RCC5Interp I)
  {c : Nat → α} (hdom : ∀ i, I.dom (c i))
  (hstep : ∀ i, I.rho (c i) (c (i + 1)) = pp)
  {C0 : Concept} {t : List Concept}
  (hrec : ∀ N, ∃ a, N ≤ a ∧ mty C0 I (c a) = t)

include hI hdom hstep hrec

/-- A recurring `∃DR`-demand has, past any bound, a witness `DR` to ALL
    chain positions up to that bound. -/
theorem dr_witness_all_below {D : Concept}
    (hD : Concept.ex dr D ∈ t) (B : Nat) :
    ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
      ∀ b, b ≤ B → I.rho (c b) w = dr := by
  obtain ⟨a, hBa, hta⟩ := hrec B
  have hDa : Concept.ex dr D ∈ mty C0 I (c a) := by
    rw [hta]; exact hD
  obtain ⟨w, hw, hr, hDw⟩ := mty_ex hDa
  exact ⟨w, hw, hDw, fun b hb =>
    backward_forcing_dr hI hdom hstep hw hr b (Nat.le_trans hb hBa)⟩

/-- A recurring `∃PP`-demand has, past any bound, a witness containing
    ALL chain positions up to that bound. -/
theorem pp_witness_all_below {D : Concept}
    (hD : Concept.ex pp D ∈ t) (B : Nat) :
    ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
      ∀ b, b ≤ B → I.rho (c b) w = pp := by
  obtain ⟨a, hBa, hta⟩ := hrec B
  have hDa : Concept.ex pp D ∈ mty C0 I (c a) := by
    rw [hta]; exact hD
  obtain ⟨w, hw, hr, hDw⟩ := mty_ex hDa
  exact ⟨w, hw, hDw, fun b hb =>
    backward_forcing_pp hI hdom hstep hw hr b (Nat.le_trans hb hBa)⟩

/-- A recurring `∃PPI`-demand has a witness inside ALL chain positions
    past some anchor. -/
theorem ppi_witness_all_above {D : Concept}
    (hD : Concept.ex ppi D ∈ t) :
    ∃ a w, I.dom w ∧ D ∈ mty C0 I w ∧
      ∀ b, a ≤ b → I.rho (c b) w = ppi := by
  obtain ⟨a, _, hta⟩ := hrec 0
  have hDa : Concept.ex ppi D ∈ mty C0 I (c a) := by
    rw [hta]; exact hD
  obtain ⟨w, hw, hr, hDw⟩ := mty_ex hDa
  exact ⟨a, w, hw, hDw, fun b hb =>
    forward_absorption_ppi hI hdom hstep hw hr b hb⟩

end WitnessSelection

/-! ## Round E0 (2026-07-23): the assembly — certificate glue

The compositional backbone of the extraction: the all-cross-`PO`
amalgamation of two valid multi-tier certificates is valid.  This is
the certificate-level form of free amalgamation (wp48) powered by the
fragment's escape valve: cross edges are always frame-safe (`PO`
inhabits every cell of its row and column, and `comp(PO,PO)` is
everything), and — given that no listed type carries a `∀PO`
obligation (`MTNoPo`, discharged in context by `pofree_cl_all`) —
cross edges never fire an obligation.  Kernels never need to talk
across the glue; fulfilment stays within each side.  The assembly will
build one block per demand component and glue. -/

/-- The `PO` row: `PO ∈ comp(PO, a)` for every atom. -/
theorem po_mem_comp_left : ∀ a : Atom, po ∈ comp po a := by
  intro a
  cases a <;> decide

/-- The `PO` column: `PO ∈ comp(a, PO)` for every atom. -/
theorem po_mem_comp_right : ∀ a : Atom, po ∈ comp a po := by
  intro a
  cases a <;> decide

/-- `comp(PO,PO)` is everything. -/
theorem mem_comp_po_po : ∀ a : Atom, a ∈ comp po po := by
  intro a
  cases a <;> decide

/-- No `∀PO` obligation in a type list. -/
def NoPo (L : List Concept) : Prop :=
  ∀ E : Concept, Concept.all po E ∉ L

/-- No `∀PO` obligation anywhere in a certificate — the fragment's
    standing situation (`pofree_cl_all`). -/
structure MTNoPo {β κ : Type} (T : MultiTier β κ) : Prop where
  ext : ∀ e, NoPo (T.tauE e)
  ker : ∀ k a, a < T.p k → NoPo (T.phase k a)

section Glue

variable {β1 κ1 β2 κ2 : Type} [DecidableEq κ1] [DecidableEq κ2]

/-- The all-cross-`PO` glue of two certificates. -/
def glueMT (T1 : MultiTier β1 κ1) (T2 : MultiTier β2 κ2) :
    MultiTier (β1 ⊕ β2) (κ1 ⊕ κ2) where
  E := fun e f => match e, f with
    | .inl e, .inl f => T1.E e f
    | .inr e, .inr f => T2.E e f
    | _, _ => po
  K := fun k e => match k, e with
    | .inl k, .inl e => T1.K k e
    | .inr k, .inr e => T2.K k e
    | _, _ => po
  Q := fun k k' => match k, k' with
    | .inl k, .inl k' => T1.Q k k'
    | .inr k, .inr k' => T2.Q k k'
    | _, _ => po
  up := fun k => match k with
    | .inl k => T1.up k
    | .inr k => T2.up k
  tauE := fun e => match e with
    | .inl e => T1.tauE e
    | .inr e => T2.tauE e
  p := fun k => match k with
    | .inl k => T1.p k
    | .inr k => T2.p k
  phase := fun k a => match k with
    | .inl k => T1.phase k a
    | .inr k => T2.phase k a

variable {T1 : MultiTier β1 κ1} {T2 : MultiTier β2 κ2}

/-- Embed side 1 into the glued quotient carrier. -/
def gembN1 : (β1 ⊕ κ1) → ((β1 ⊕ β2) ⊕ (κ1 ⊕ κ2))
  | .inl e => .inl (.inl e)
  | .inr k => .inr (.inl k)

/-- Embed side 2. -/
def gembN2 : (β2 ⊕ κ2) → ((β1 ⊕ β2) ⊕ (κ1 ⊕ κ2))
  | .inl e => .inl (.inr e)
  | .inr k => .inr (.inr k)

theorem qnet_glue_11 (x y : β1 ⊕ κ1) :
    qnet (glueMT T1 T2).E (glueMT T1 T2).K (glueMT T1 T2).Q
      (gembN1 x) (gembN1 y) = qnet T1.E T1.K T1.Q x y := by
  rcases x with e | k <;> rcases y with f | k'
  · rfl
  · rfl
  · rfl
  · show (if (Sum.inl k : κ1 ⊕ κ2) = Sum.inl k' then eq
        else (glueMT T1 T2).Q (Sum.inl k) (Sum.inl k'))
      = (if k = k' then eq else T1.Q k k')
    by_cases hk : k = k'
    · subst hk
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => hk (Sum.inl.inj h)), if_neg hk]
      rfl

theorem qnet_glue_22 (x y : β2 ⊕ κ2) :
    qnet (glueMT T1 T2).E (glueMT T1 T2).K (glueMT T1 T2).Q
      (gembN2 x) (gembN2 y) = qnet T2.E T2.K T2.Q x y := by
  rcases x with e | k <;> rcases y with f | k'
  · rfl
  · rfl
  · rfl
  · show (if (Sum.inr k : κ1 ⊕ κ2) = Sum.inr k' then eq
        else (glueMT T1 T2).Q (Sum.inr k) (Sum.inr k'))
      = (if k = k' then eq else T2.Q k k')
    by_cases hk : k = k'
    · subst hk
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => hk (Sum.inr.inj h)), if_neg hk]
      rfl

theorem qnet_glue_12 (x : β1 ⊕ κ1) (y : β2 ⊕ κ2) :
    qnet (glueMT T1 T2).E (glueMT T1 T2).K (glueMT T1 T2).Q
      (gembN1 x) (gembN2 y) = po := by
  rcases x with e | k <;> rcases y with f | k'
  · rfl
  · rfl
  · rfl
  · show (if (Sum.inl k : κ1 ⊕ κ2) = Sum.inr k' then eq
        else (glueMT T1 T2).Q (Sum.inl k) (Sum.inr k')) = po
    rw [if_neg (fun h => nomatch h)]
    rfl

theorem qnet_glue_21 (x : β2 ⊕ κ2) (y : β1 ⊕ κ1) :
    qnet (glueMT T1 T2).E (glueMT T1 T2).K (glueMT T1 T2).Q
      (gembN2 x) (gembN1 y) = po := by
  rcases x with e | k <;> rcases y with f | k'
  · rfl
  · rfl
  · rfl
  · show (if (Sum.inr k : κ1 ⊕ κ2) = Sum.inl k' then eq
        else (glueMT T1 T2).Q (Sum.inr k) (Sum.inl k')) = po
    rw [if_neg (fun h => nomatch h)]
    rfl

omit [DecidableEq κ1] [DecidableEq κ2] in
/-- Every glued index comes from one side. -/
theorem glue_rep (z : (β1 ⊕ β2) ⊕ (κ1 ⊕ κ2)) :
    (∃ x, z = gembN1 (β2 := β2) (κ2 := κ2) x) ∨
    (∃ x, z = gembN2 (β1 := β1) (κ1 := κ1) x) := by
  rcases z with (e | e) | (k | k)
  · exact Or.inl ⟨.inl e, rfl⟩
  · exact Or.inr ⟨.inl e, rfl⟩
  · exact Or.inl ⟨.inr k, rfl⟩
  · exact Or.inr ⟨.inr k, rfl⟩

/-- THE GLUE FRAME: the glued quotient network is a frame — cross
    triangles close by the `PO` row/column facts alone. -/
theorem glue_frame (h1 : Frame (qnet T1.E T1.K T1.Q))
    (h2 : Frame (qnet T2.E T2.K T2.Q)) :
    Frame (qnet (glueMT T1 T2).E (glueMT T1 T2).K (glueMT T1 T2).Q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    rcases glue_rep z with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · rw [qnet_glue_11]
      exact h1.refl_eq x
    · rw [qnet_glue_22]
      exact h2.refl_eq x
  · intro z w hzw
    rcases glue_rep z with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
      rcases glue_rep w with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · rw [qnet_glue_11] at hzw
      rw [h1.eq_id x y hzw]
    · rw [qnet_glue_12] at hzw
      exact absurd hzw (by decide)
    · rw [qnet_glue_21] at hzw
      exact absurd hzw (by decide)
    · rw [qnet_glue_22] at hzw
      rw [h2.eq_id x y hzw]
  · intro z w
    rcases glue_rep z with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
      rcases glue_rep w with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · rw [qnet_glue_11, qnet_glue_11]
      exact h1.conv_ x y
    · rw [qnet_glue_21, qnet_glue_12]
      rfl
    · rw [qnet_glue_12, qnet_glue_21]
      rfl
    · rw [qnet_glue_22, qnet_glue_22]
      exact h2.conv_ x y
  · intro z w v
    rcases glue_rep z with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
      rcases glue_rep w with ⟨y, rfl⟩ | ⟨y, rfl⟩ <;>
      rcases glue_rep v with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · rw [qnet_glue_11, qnet_glue_11, qnet_glue_11]
      exact h1.comp_ x y u
    · rw [qnet_glue_12, qnet_glue_11, qnet_glue_12]
      exact po_mem_comp_right _
    · rw [qnet_glue_11, qnet_glue_12, qnet_glue_21]
      exact mem_comp_po_po _
    · rw [qnet_glue_12, qnet_glue_12, qnet_glue_22]
      exact po_mem_comp_left _
    · rw [qnet_glue_21, qnet_glue_21, qnet_glue_11]
      exact po_mem_comp_left _
    · rw [qnet_glue_22, qnet_glue_21, qnet_glue_12]
      exact mem_comp_po_po _
    · rw [qnet_glue_21, qnet_glue_22, qnet_glue_21]
      exact po_mem_comp_right _
    · rw [qnet_glue_22, qnet_glue_22, qnet_glue_22]
      exact h2.comp_ x y u

/-- THE GLUE THEOREM: the all-cross-`PO` amalgamation of two valid,
    `∀PO`-obligation-free certificates is valid. -/
theorem glue_ok (h1 : MultiTierOk T1) (h2 : MultiTierOk T2)
    (n1 : MTNoPo T1) (n2 : MTNoPo T2) :
    MultiTierOk (glueMT T1 T2) := by
  refine
    { hp := ?_, frame_q := glue_frame h1.frame_q h2.frame_q,
      e_clash := ?_, e_nobot := ?_, e_and := ?_, e_or := ?_,
      k_clash := ?_, k_nobot := ?_, k_and := ?_, k_or := ?_,
      ee_all := ?_, ek_all := ?_, ke_all := ?_,
      kk_pp := ?_, kk_ppi := ?_, kk_eq := ?_, kq_all := ?_,
      e_ex := ?_, k_ex := ?_ }
  · intro k
    rcases k with k | k
    · exact h1.hp k
    · exact h2.hp k
  · intro e a hmem
    rcases e with e | e
    · exact h1.e_clash e a hmem
    · exact h2.e_clash e a hmem
  · intro e
    rcases e with e | e
    · exact h1.e_nobot e
    · exact h2.e_nobot e
  · intro e c d hmem
    rcases e with e | e
    · exact h1.e_and e c d hmem
    · exact h2.e_and e c d hmem
  · intro e c d hmem
    rcases e with e | e
    · exact h1.e_or e c d hmem
    · exact h2.e_or e c d hmem
  · intro k a ha n hmem
    rcases k with k | k
    · exact h1.k_clash k a ha n hmem
    · exact h2.k_clash k a ha n hmem
  · intro k a ha
    rcases k with k | k
    · exact h1.k_nobot k a ha
    · exact h2.k_nobot k a ha
  · intro k a ha c d hmem
    rcases k with k | k
    · exact h1.k_and k a ha c d hmem
    · exact h2.k_and k a ha c d hmem
  · intro k a ha c d hmem
    rcases k with k | k
    · exact h1.k_or k a ha c d hmem
    · exact h2.k_or k a ha c d hmem
  · intro e f r c hmem hr
    rcases e with e | e <;> rcases f with f | f
    · exact h1.ee_all e f r c hmem hr
    · have hr' : po = r := hr
      subst hr'
      exact absurd hmem (n1.ext e c)
    · have hr' : po = r := hr
      subst hr'
      exact absurd hmem (n2.ext e c)
    · exact h2.ee_all e f r c hmem hr
  · intro e r c hmem k hr a ha
    rcases e with e | e <;> rcases k with k | k
    · exact h1.ek_all e r c hmem k hr a ha
    · have hr' : po = r := hr
      subst hr'
      exact absurd hmem (n1.ext e c)
    · have hr' : po = r := hr
      subst hr'
      exact absurd hmem (n2.ext e c)
    · exact h2.ek_all e r c hmem k hr a ha
  · intro k a ha r c hmem f hK
    rcases k with k | k <;> rcases f with f | f
    · exact h1.ke_all k a ha r c hmem f hK
    · have hK' : po = r := hK
      subst hK'
      exact absurd hmem (n1.ker k a ha c)
    · have hK' : po = r := hK
      subst hK'
      exact absurd hmem (n2.ker k a ha c)
    · exact h2.ke_all k a ha r c hmem f hK
  · intro k a ha c hmem b hb
    rcases k with k | k
    · exact h1.kk_pp k a ha c hmem b hb
    · exact h2.kk_pp k a ha c hmem b hb
  · intro k a ha c hmem b hb
    rcases k with k | k
    · exact h1.kk_ppi k a ha c hmem b hb
    · exact h2.kk_ppi k a ha c hmem b hb
  · intro k a ha c hmem
    rcases k with k | k
    · exact h1.kk_eq k a ha c hmem
    · exact h2.kk_eq k a ha c hmem
  · intro k k' hne a ha r c hmem hQ b hb
    rcases k with k | k <;> rcases k' with k' | k'
    · exact h1.kq_all k k' (fun h => hne (congrArg Sum.inl h))
        a ha r c hmem hQ b hb
    · have hQ' : po = r := hQ
      subst hQ'
      exact absurd hmem (n1.ker k a ha c)
    · have hQ' : po = r := hQ
      subst hQ'
      exact absurd hmem (n2.ker k a ha c)
    · exact h2.kq_all k k' (fun h => hne (congrArg Sum.inr h))
        a ha r c hmem hQ b hb
  · intro e r c hmem
    rcases e with e | e
    · rcases h1.e_ex e r c hmem with ⟨f, hEf, hcf⟩ | ⟨k, hK, a, ha, hca⟩
      · exact Or.inl ⟨.inl f, hEf, hcf⟩
      · exact Or.inr ⟨.inl k, hK, a, ha, hca⟩
    · rcases h2.e_ex e r c hmem with ⟨f, hEf, hcf⟩ | ⟨k, hK, a, ha, hca⟩
      · exact Or.inl ⟨.inr f, hEf, hcf⟩
      · exact Or.inr ⟨.inr k, hK, a, ha, hca⟩
  · intro k a ha r c hmem
    rcases k with k | k
    · rcases h1.k_ex k a ha r c hmem with
        ⟨f, hKf, hcf⟩ | ⟨hrd, b, hb, hcb⟩ | ⟨hreq, hc⟩ |
        ⟨k', hne, hQ, b, hb, hcb⟩
      · exact Or.inl ⟨.inl f, hKf, hcf⟩
      · exact Or.inr (Or.inl ⟨hrd, b, hb, hcb⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hreq, hc⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨.inl k',
          fun h => hne (Sum.inl.inj h), hQ, b, hb, hcb⟩))
    · rcases h2.k_ex k a ha r c hmem with
        ⟨f, hKf, hcf⟩ | ⟨hrd, b, hb, hcb⟩ | ⟨hreq, hc⟩ |
        ⟨k', hne, hQ, b, hb, hcb⟩
      · exact Or.inl ⟨.inr f, hKf, hcf⟩
      · exact Or.inr (Or.inl ⟨hrd, b, hb, hcb⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hreq, hc⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨.inr k',
          fun h => hne (Sum.inr.inj h), hQ, b, hb, hcb⟩))

omit [DecidableEq κ1] [DecidableEq κ2] in
/-- Gluing preserves `∀PO`-obligation-freeness (for iterated glue). -/
theorem glue_noPo (n1 : MTNoPo T1) (n2 : MTNoPo T2) :
    MTNoPo (glueMT T1 T2) := by
  constructor
  · intro e
    rcases e with e | e
    · exact n1.ext e
    · exact n2.ext e
  · intro k a ha
    rcases k with k | k
    · exact n1.ker k a ha
    · exact n2.ker k a ha

/-- Embed side 1 into the glued unfolding carrier. -/
def gembM1 : (β1 ⊕ κ1 × Nat) → ((β1 ⊕ β2) ⊕ (κ1 ⊕ κ2) × Nat)
  | .inl e => .inl (.inl e)
  | .inr (k, i) => .inr (.inl k, i)

/-- Embed side 2. -/
def gembM2 : (β2 ⊕ κ2 × Nat) → ((β1 ⊕ β2) ⊕ (κ1 ⊕ κ2) × Nat)
  | .inl e => .inl (.inr e)
  | .inr (k, i) => .inr (.inr k, i)

omit [DecidableEq κ1] [DecidableEq κ2] in
/-- Labels are preserved by the side-1 embedding. -/
theorem glue_label_1 (x : β1 ⊕ κ1 × Nat) :
    mtLabel (glueMT T1 T2) (gembM1 x) = mtLabel T1 x := by
  rcases x with e | ⟨k, i⟩
  · rfl
  · rfl

omit [DecidableEq κ1] [DecidableEq κ2] in
/-- Labels are preserved by the side-2 embedding. -/
theorem glue_label_2 (x : β2 ⊕ κ2 × Nat) :
    mtLabel (glueMT T1 T2) (gembM2 x) = mtLabel T2 x := by
  rcases x with e | ⟨k, i⟩
  · rfl
  · rfl

end Glue

#print axioms twoTier_sound
#print axioms cinf_satisfiable
#print axioms multiTier_sound
#print axioms cboth_satisfiable
#print axioms mtAcceptB_sound
#print axioms cboth_satisfiable_exec
#print axioms mtOkB_iff
#print axioms mtAcceptB_complete
#print axioms decidableSat_of_codes
#print axioms external_stabilizes
#print axioms backward_forcing_dr
#print axioms forward_absorption_ppi
#print axioms recurrent_tail
#print axioms segment_exists
#print axioms seg_pp
#print axioms seg_ppi
#print axioms pofree_cl_all
#print axioms mty_no_all_po
#print axioms dr_witness_all_below
#print axioms ppi_witness_all_above
#print axioms glue_ok
#print axioms glue_frame

end POFreeLift
