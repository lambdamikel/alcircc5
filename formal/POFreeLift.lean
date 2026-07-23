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

#print axioms twoTier_sound
#print axioms cinf_satisfiable
#print axioms multiTier_sound
#print axioms cboth_satisfiable

end POFreeLift
