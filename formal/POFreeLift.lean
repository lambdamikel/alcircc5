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

/-- DECIDABLE fragment membership for the FULL ∀PO-free fragment (`MFrag`
    of the mixing design §25.4): `POFree` reduces to a structural Boolean
    check, so `POFree C0` is `by decide`.  The mixing decidability's entry
    point (like `hfragB` for the horizontal fragment). -/
def pofreeB : Concept → Bool
  | .top => true
  | .bot => true
  | .atom _ => true
  | .natom _ => true
  | .and c d => pofreeB c && pofreeB d
  | .or c d => pofreeB c && pofreeB d
  | .ex _ c => pofreeB c
  | .all r c => decide (r ≠ po) && pofreeB c

theorem pofreeB_iff (c : Concept) : pofreeB c = true ↔ POFree c := by
  induction c with
  | top => simp [pofreeB, POFree]
  | bot => simp [pofreeB, POFree]
  | atom => simp [pofreeB, POFree]
  | natom => simp [pofreeB, POFree]
  | and c d hc hd => simp [pofreeB, POFree, hc, hd]
  | or c d hc hd => simp [pofreeB, POFree, hc, hd]
  | ex r c hc => simp [pofreeB, POFree, hc]
  | all r c hc => simp [pofreeB, POFree, hc]

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

/-- **THE ROW NEVER RETURNS** (§39.3) — the engine of the counting proof.  If an
    external's row to the chain takes the SAME value at two positions, it is
    constant on the whole interval between them.  Hence the row is a monotone
    staircase: it changes value at most twice (rank 0 `{DR,PP}` → rank 1
    `{PO,EQ}` → rank 2 `{PPI}`, and within each rank it cannot vary), so a window
    of length `p` fails to be constant only if it STRADDLES one of at most two
    transitions — at most `2(p-1)` bad bases, a bound depending on `p` ALONE.
    That is what makes the union-bound existence proof for the base vector go
    through (probe `wp91` part T: observed ≤2 transitions, and bad-base counts
    2/4/6 against the bound 3/6/9 at `p` = 2/3/4). -/
theorem rank_eq_imp_value_eq {i k : Nat} (hik : i ≤ k)
    (hrank : stabRank (I.rho (c k) e) = stabRank (I.rho (c i) e)) :
    I.rho (c k) e = I.rho (c i) e := by
  -- with equal ranks, the value is pinned in every case
  cases hvi : I.rho (c i) e with
  | dr =>
    cases hvk : I.rho (c k) e with
    | dr => rfl
    | pp => exact absurd (backward_forcing_pp hI hdom hstep hedom hvk i hik)
              (by rw [hvi]; exact by decide)
    | eq => rw [hvi, hvk] at hrank; exact absurd hrank (by decide)
    | po => rw [hvi, hvk] at hrank; exact absurd hrank (by decide)
    | ppi => rw [hvi, hvk] at hrank; exact absurd hrank (by decide)
  | pp =>
    cases hvk : I.rho (c k) e with
    | dr => exact absurd (backward_forcing_dr hI hdom hstep hedom hvk i hik)
              (by rw [hvi]; exact by decide)
    | pp => rfl
    | eq => rw [hvi, hvk] at hrank; exact absurd hrank (by decide)
    | po => rw [hvi, hvk] at hrank; exact absurd hrank (by decide)
    | ppi => rw [hvi, hvk] at hrank; exact absurd hrank (by decide)
  | po =>
    cases hvk : I.rho (c k) e with
    | dr => rw [hvi, hvk] at hrank; exact absurd hrank (by decide)
    | pp => rw [hvi, hvk] at hrank; exact absurd hrank (by decide)
    | eq =>
      -- `c k = e`, so the value at `i ≤ k` would be `PP` (rank 0) or `EQ`
      exfalso
      have hke : c k = e := hI.eq_id (c k) e (hdom k) hedom hvk
      rcases Nat.lt_or_ge i k with hlt | hge
      · have : I.rho (c i) e = pp := by
          rw [← hke]; exact chain_model_pp hI hdom hstep i k hlt
        rw [hvi] at this; exact absurd this (by decide)
      · have hik' : i = k := by omega
        rw [hik'] at hvi; rw [hvi] at hvk; exact absurd hvk (by decide)
    | po => rfl
    | ppi => rw [hvi, hvk] at hrank; exact absurd hrank (by decide)
  | eq =>
    -- `c i = e`; an `i < k` would make `ρ (c k) e = PPI` (rank 2), not rank 1
    have hie : c i = e := hI.eq_id (c i) e (hdom i) hedom hvi
    rcases Nat.lt_or_ge i k with hlt | hge
    · exfalso
      have hik' : I.rho (c i) (c k) = pp := chain_model_pp hI hdom hstep i k hlt
      rw [hie] at hik'
      have hki : I.rho (c k) e = ppi := by
        rw [hI.conv_ e (c k) hedom (hdom k), hik']; rfl
      rw [hki, hvi] at hrank
      exact absurd hrank (by decide)
    · have hki : k = i := by omega
      rw [hki, hvi]
  | ppi =>
    cases hvk : I.rho (c k) e with
    | dr => rw [hvi, hvk] at hrank; exact absurd hrank (by decide)
    | pp => rw [hvi, hvk] at hrank; exact absurd hrank (by decide)
    | eq => rw [hvi, hvk] at hrank; exact absurd hrank (by decide)
    | po => rw [hvi, hvk] at hrank; exact absurd hrank (by decide)
    | ppi => rfl

/-- The staircase form: equal values at two positions ⟹ constant between them.
    Immediate from `rank_eq_imp_value_eq` plus rank monotonicity. -/
theorem row_no_return {i j : Nat} (_hij : i ≤ j)
    (h : I.rho (c i) e = I.rho (c j) e) :
    ∀ k, i ≤ k → k ≤ j → I.rho (c k) e = I.rho (c i) e := by
  intro k hik hkj
  have hr1 : stabRank (I.rho (c i) e) ≤ stabRank (I.rho (c k) e) :=
    vrank_mono hI hdom hstep hedom i k hik
  have hr2 : stabRank (I.rho (c k) e) ≤ stabRank (I.rho (c j) e) :=
    vrank_mono hI hdom hstep hedom k j hkj
  rw [← h] at hr2
  exact rank_eq_imp_value_eq hI hdom hstep hedom hik (by omega)

/-- **A VALUE CHANGE COSTS A RANK** (§39.3) — differing endpoints force a STRICT
    rank increase.  Contrapositive of `rank_eq_imp_value_eq` plus monotonicity;
    this is what bounds the number of transitions by `stabRank`'s ceiling. -/
theorem ends_differ_rank_lt {i j : Nat} (hij : i ≤ j)
    (h : I.rho (c i) e ≠ I.rho (c j) e) :
    stabRank (I.rho (c i) e) < stabRank (I.rho (c j) e) := by
  have hle : stabRank (I.rho (c i) e) ≤ stabRank (I.rho (c j) e) :=
    vrank_mono hI hdom hstep hedom i j hij
  rcases Nat.lt_or_ge (stabRank (I.rho (c i) e)) (stabRank (I.rho (c j) e)) with h1 | h2
  · exact h1
  · exact absurd (rank_eq_imp_value_eq hI hdom hstep hedom hij (by omega)).symm h

/-- **AT MOST TWO SPACED WINDOWS ARE BAD** (§39.3) — the spoil-count lemma, in
    the form the pigeonhole consumes.  Among any THREE candidate bases spaced at
    least `p` apart, at least one has a CONSTANT window: three bad windows would
    be disjoint, each costing a strict rank increase (`ends_differ_rank_lt`)
    while the gaps cost nothing (`vrank_mono`), so the final rank would be ≥ 3 —
    impossible since `stabRank ≤ 2`.  Hence each witness spoils at most 2 spaced
    candidates of each chain, which is the `B` of the counting. -/
theorem three_spaced_not_all_bad (p : Nat) (hp : 0 < p) (i1 i2 i3 : Nat)
    (h12 : i1 + p ≤ i2) (h23 : i2 + p ≤ i3)
    (b1 : I.rho (c i1) e ≠ I.rho (c (i1 + p - 1)) e)
    (b2 : I.rho (c i2) e ≠ I.rho (c (i2 + p - 1)) e)
    (b3 : I.rho (c i3) e ≠ I.rho (c (i3 + p - 1)) e) : False := by
  have r1 := ends_differ_rank_lt hI hdom hstep hedom (by omega : i1 ≤ i1 + p - 1) b1
  have r2 := ends_differ_rank_lt hI hdom hstep hedom (by omega : i2 ≤ i2 + p - 1) b2
  have r3 := ends_differ_rank_lt hI hdom hstep hedom (by omega : i3 ≤ i3 + p - 1) b3
  have m1 : stabRank (I.rho (c (i1 + p - 1)) e) ≤ stabRank (I.rho (c i2) e) :=
    vrank_mono hI hdom hstep hedom _ _ (by omega)
  have m2 : stabRank (I.rho (c (i2 + p - 1)) e) ≤ stabRank (I.rho (c i3) e) :=
    vrank_mono hI hdom hstep hedom _ _ (by omega)
  have hb := stabRank_le_two (I.rho (c (i3 + p - 1)) e)
  omega

/-- **A WINDOW IS CONSTANT IFF ITS ENDPOINTS AGREE** (§39.3) — immediate from
    `row_no_return`, and the form the counting argument uses: to test a window
    one need only compare its two ends. -/
theorem window_const_iff_ends (i p : Nat) (hp : 0 < p) :
    (I.rho (c i) e = I.rho (c (i + p - 1)) e) →
    ∀ b, b < p → I.rho e (c (i + b)) = I.rho e (c i) := by
  intro hends b hb
  have h := row_no_return hI hdom hstep hedom (by omega : i ≤ i + p - 1) hends
    (i + b) (by omega) (by omega)
  rw [hI.conv_ (c (i + b)) e (hdom (i + b)) hedom, h,
    ← hI.conv_ (c i) e (hdom i) hedom]

/-- **`hstab` FOR FREE BELOW A RANK-0 POINT — the "stay low" mechanism**
    (§39.3).  If an external's row to the chain is `DR` at position `m`, then by
    backward forcing it is `DR` at EVERY position `≤ m`; so the row is constant
    on ANY window ending at or below `m`, with NO stabilization horizon
    consulted.  This is the brick the `wp91` part-I diagnosis identified as
    carrying 92.7% of the cross-rows: `hstab` is satisfied by keeping the window
    inside the row's INITIAL rank-0 block, NOT by pushing it past every
    transition (the §39.6 framing, which is exactly what the ordering cycle
    blocks). -/
theorem stab_window_of_dr {m : Nat} (h : I.rho (c m) e = dr) :
    ∀ i a, i + a ≤ m → I.rho e (c (i + a)) = I.rho e (c i) := by
  intro i a hle
  have h1 : I.rho (c (i + a)) e = dr :=
    backward_forcing_dr hI hdom hstep hedom h (i + a) hle
  have h2 : I.rho (c i) e = dr :=
    backward_forcing_dr hI hdom hstep hedom h i (by omega)
  rw [hI.conv_ (c (i + a)) e (hdom (i + a)) hedom, h1,
    hI.conv_ (c i) e (hdom i) hedom, h2]

/-- The `PP` half of the same mechanism (`comp(PP,PP) = {PP}`): rank-0 is the
    `{DR,PP}` block, and it is CONSTANT below any of its points. -/
theorem stab_window_of_pp {m : Nat} (h : I.rho (c m) e = pp) :
    ∀ i a, i + a ≤ m → I.rho e (c (i + a)) = I.rho e (c i) := by
  intro i a hle
  have h1 : I.rho (c (i + a)) e = pp :=
    backward_forcing_pp hI hdom hstep hedom h (i + a) hle
  have h2 : I.rho (c i) e = pp :=
    backward_forcing_pp hI hdom hstep hedom h i (by omega)
  rw [hI.conv_ (c (i + a)) e (hdom (i + a)) hedom, h1,
    hI.conv_ (c i) e (hdom i) hedom, h2]

/-- **THE `hstab` DICHOTOMY** (§39.3): a window satisfies `hstab` for an
    external either because it sits BELOW a rank-0 point of that external's row
    ("stay low", `stab_window_of_dr`/`_pp`) or because it sits ABOVE the row's
    last transition ("push past", `external_stabilizes`).  `wp91` part I measured
    both as necessary — 345 of 2,552 solved configurations needed BOTH — so a
    proof of R6 must be this case split, not either branch alone. -/
theorem stab_window_of_rank0 {m : Nat} (h : I.rho (c m) e = dr ∨ I.rho (c m) e = pp) :
    ∀ i a, i + a ≤ m → I.rho e (c (i + a)) = I.rho e (c i) := by
  rcases h with h | h
  · exact stab_window_of_dr hI hdom hstep hedom h
  · exact stab_window_of_pp hI hdom hstep hedom h

/-- **COFINAL `DR` ⟹ `DR` EVERYWHERE, HORIZON 0** (§39.6).  A node that is `DR`
    from COFINALLY many points of an ascending chain is `DR` from EVERY point:
    `backward_forcing_dr` from an arbitrarily high witness.  Combined with
    `cofinal_dr_stab` below this says such a node satisfies `mixKernels_ok`'s
    `hstab` for that kernel with NO horizon — nothing has to be pushed past it.
    This is what narrows the §39 ordering cycle: it bites ONLY for externals that
    some other kernel eventually overlaps or swallows.  (§39.6.  The two obvious
    ways to exploit the narrowing are both refuted by probe `wp91` part F, and
    what survives is the WINDOW reading of `hstab`, §39.4.) -/
theorem cofinal_dr_all (hcof : ∀ N, ∃ j, N ≤ j ∧ I.rho (c j) e = dr) :
    ∀ n, I.rho (c n) e = dr := by
  intro n
  obtain ⟨j, hj, hdrj⟩ := hcof n
  exact backward_forcing_dr hI hdom hstep hedom hdrj n hj

/-- `hstab` for free: a cofinally-`DR` external's row to the chain is constant
    (value `DR`) from ANY base, so no stabilization horizon is consulted. -/
theorem cofinal_dr_stab (hcof : ∀ N, ∃ j, N ≤ j ∧ I.rho (c j) e = dr) :
    ∀ i a, I.rho e (c (i + a)) = I.rho e (c i) := by
  intro i a
  have h1 : I.rho e (c (i + a)) = dr := by
    rw [hI.conv_ (c (i + a)) e (hdom (i + a)) hedom,
      cofinal_dr_all hI hdom hstep hedom hcof (i + a)]; rfl
  have h2 : I.rho e (c i) = dr := by
    rw [hI.conv_ (c i) e (hdom i) hedom, cofinal_dr_all hI hdom hstep hedom hcof i]; rfl
  rw [h1, h2]

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

/-- A `Nodup` list whose elements all lie in `univ` is no longer than
    `univ` (finite pigeonhole; `eraseP`-based, no `BEq`). -/
theorem nodup_len_le {A : Type} [DecidableEq A] :
    ∀ (l univ : List A), (∀ x ∈ l, x ∈ univ) → l.Nodup → l.length ≤ univ.length := by
  intro l
  induction l with
  | nil => intro univ _ _; exact Nat.zero_le _
  | cons a t ih =>
    intro univ hsub hnd
    have ha : a ∈ univ := hsub a List.mem_cons_self
    have hant : a ∉ t := (List.nodup_cons.mp hnd).1
    have hndt : t.Nodup := (List.nodup_cons.mp hnd).2
    have hsubt : ∀ x ∈ t, x ∈ univ.eraseP (fun y => decide (y = a)) := by
      intro x hx
      have hxa : ¬ ((fun y => decide (y = a)) x = true) := by
        simp only [decide_eq_true_eq]; exact fun h => hant (h ▸ hx)
      exact (List.mem_eraseP_of_neg (p := fun y => decide (y = a)) hxa).mpr
        (hsub x (List.mem_cons_of_mem a hx))
    have hlen := ih (univ.eraseP (fun y => decide (y = a))) hsubt hndt
    rw [List.length_eraseP_of_mem ha (by simp)] at hlen
    have hpos : 0 < univ.length := List.length_pos_of_mem ha
    show t.length + 1 ≤ univ.length
    omega

/-- **BOUNDED PIGEONHOLE**: past any `L`, two of the first `|univ|+1`
    values coincide — so the recurrence period is `≤ |univ|`. -/
theorem segment_exists_bounded {β : Type} [DecidableEq β] (univ : List β)
    (f : Nat → β) (hf : ∀ i, f i ∈ univ) (L : Nat) :
    ∃ i j, L ≤ i ∧ i < j ∧ j ≤ L + univ.length ∧ f i = f j := by
  apply Classical.byContradiction
  intro hno
  have hwnd : ((List.range (univ.length + 1)).map (fun k => f (L + k))).Nodup := by
    show List.Pairwise (· ≠ ·) ((List.range (univ.length + 1)).map (fun k => f (L + k)))
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
    intro a b _ hb hab heq
    have hbn : b ≤ univ.length := by have := List.mem_range.mp hb; omega
    exact hno ⟨L + a, L + b, Nat.le_add_right L a,
      Nat.add_lt_add_left hab L, by omega, heq⟩
  have hwsub : ∀ x ∈ ((List.range (univ.length + 1)).map (fun k => f (L + k))), x ∈ univ := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    exact hf (L + k)
  have hle := nodup_len_le _ univ hwsub hwnd
  rw [List.length_map, List.length_range] at hle
  omega

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

/-! ## Round E1 (2026-07-23): the family glue with pending pools

The n-ary, FLAT form of the glue, shaped for the top-level assembly:
a family of blocks over COMMON index types (`Fin B → MultiTier β κ`),
glued all-cross-`PO`.  Each block may leave `∃PO`-demands PENDING
against a pool `P` of tagged types (`MTOkPool`): a pending demand
`∃PO.c` is admissible if some pool entry with a DIFFERENT tag contains
`c`.  If every pool entry is realized as (a subset of) the label of an
actual node in the block carrying its tag (`hreal`), the glued family
is STRICTLY valid (`glueFam_ok`): the pending demand's realizer sits in
a different block, so the cross edge is `PO` — exactly the demanded
relation — and never fires an obligation.  The intended instantiation:
one block per vertical/DR demand component, one "library" block per
`∃PO`-subformula `D` (tagged, rooted at a type containing `D`);
libraries only demand strictly smaller libraries, so the pool closes. -/

section FamGlue

variable {β κ : Type} [DecidableEq κ] {B : Nat}

/-- The all-cross-`PO` glue of a block family. -/
def glueFam (F : Fin B → MultiTier β κ) :
    MultiTier (Fin B × β) (Fin B × κ) where
  E := fun e f =>
    if e.1 = f.1 then (F e.1).E e.2 f.2 else po
  K := fun k e =>
    if k.1 = e.1 then (F k.1).K k.2 e.2 else po
  Q := fun k k' =>
    if k.1 = k'.1 then (F k.1).Q k.2 k'.2 else po
  up := fun k => (F k.1).up k.2
  tauE := fun e => (F e.1).tauE e.2
  p := fun k => (F k.1).p k.2
  phase := fun k a => (F k.1).phase k.2 a

/-- Validity with pending `∃PO`-demands against a tagged pool: as
    `MultiTierOk`, except `e_ex`/`k_ex` admit a pending branch — the
    demanded relation is `PO` and the demanded concept sits in a pool
    entry with a different tag. -/
structure MTOkPool (T : MultiTier β κ) (myTag : Nat)
    (P : List (Nat × List Concept)) : Prop where
  hp : ∀ k, 0 < T.p k
  frame_q : Frame (qnet T.E T.K T.Q)
  e_clash : ∀ e a, Concept.atom a ∈ T.tauE e → Concept.natom a ∉ T.tauE e
  e_nobot : ∀ e, Concept.bot ∉ T.tauE e
  e_and : ∀ e c d, Concept.and c d ∈ T.tauE e → c ∈ T.tauE e ∧ d ∈ T.tauE e
  e_or : ∀ e c d, Concept.or c d ∈ T.tauE e → c ∈ T.tauE e ∨ d ∈ T.tauE e
  k_clash : ∀ k a, a < T.p k → ∀ n, Concept.atom n ∈ T.phase k a →
    Concept.natom n ∉ T.phase k a
  k_nobot : ∀ k a, a < T.p k → Concept.bot ∉ T.phase k a
  k_and : ∀ k a, a < T.p k → ∀ c d, Concept.and c d ∈ T.phase k a →
    c ∈ T.phase k a ∧ d ∈ T.phase k a
  k_or : ∀ k a, a < T.p k → ∀ c d, Concept.or c d ∈ T.phase k a →
    c ∈ T.phase k a ∨ d ∈ T.phase k a
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
  e_ex : ∀ e r c, Concept.ex r c ∈ T.tauE e →
    (∃ f, T.E e f = r ∧ c ∈ T.tauE f) ∨
    (∃ k, conv (T.K k e) = r ∧ ∃ a, a < T.p k ∧ c ∈ T.phase k a) ∨
    (r = po ∧ ∃ q ∈ P, q.1 ≠ myTag ∧ c ∈ q.2)
  k_ex : ∀ k a, a < T.p k → ∀ r c, Concept.ex r c ∈ T.phase k a →
    (∃ f, T.K k f = r ∧ c ∈ T.tauE f) ∨
    (r = cdir (T.up k) ∧ ∃ b, b < T.p k ∧ c ∈ T.phase k b) ∨
    (r = eq ∧ c ∈ T.phase k a) ∨
    (∃ k', k ≠ k' ∧ T.Q k k' = r ∧ ∃ b, b < T.p k' ∧ c ∈ T.phase k' b) ∨
    (r = po ∧ ∃ q ∈ P, q.1 ≠ myTag ∧ c ∈ q.2)

variable {F : Fin B → MultiTier β κ}

/-- Embed a block's quotient index into the family carrier. -/
def gembF (b : Fin B) : (β ⊕ κ) → ((Fin B × β) ⊕ (Fin B × κ))
  | .inl e => .inl (b, e)
  | .inr k => .inr (b, k)

omit [DecidableEq κ] in
theorem gembF_rep (z : (Fin B × β) ⊕ (Fin B × κ)) :
    ∃ b x, z = gembF b x := by
  rcases z with ⟨b, e⟩ | ⟨b, k⟩
  · exact ⟨b, .inl e, rfl⟩
  · exact ⟨b, .inr k, rfl⟩

theorem qnet_fam_same (b : Fin B) (x y : β ⊕ κ) :
    qnet (glueFam F).E (glueFam F).K (glueFam F).Q (gembF b x) (gembF b y)
      = qnet (F b).E (F b).K (F b).Q x y := by
  rcases x with e | k <;> rcases y with f | k'
  · show (if b = b then (F b).E e f else po) = (F b).E e f
    rw [if_pos rfl]
  · show conv (if b = b then (F b).K k' e else po) = conv ((F b).K k' e)
    rw [if_pos rfl]
  · show (if b = b then (F b).K k f else po) = (F b).K k f
    rw [if_pos rfl]
  · show (if ((b, k) : Fin B × κ) = (b, k') then eq
        else (glueFam F).Q (b, k) (b, k'))
      = (if k = k' then eq else (F b).Q k k')
    by_cases hk : k = k'
    · subst hk
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => hk (congrArg Prod.snd h)), if_neg hk]
      show (if b = b then (F b).Q k k' else po) = (F b).Q k k'
      rw [if_pos rfl]

theorem qnet_fam_cross {b b' : Fin B} (hbb : b ≠ b') (x y : β ⊕ κ) :
    qnet (glueFam F).E (glueFam F).K (glueFam F).Q (gembF b x) (gembF b' y)
      = po := by
  rcases x with e | k <;> rcases y with f | k'
  · show (if b = b' then (F b).E e f else po) = po
    rw [if_neg hbb]
  · show conv (if b' = b then (F b').K k' e else po) = po
    rw [if_neg (fun h => hbb h.symm)]
    rfl
  · show (if b = b' then (F b).K k f else po) = po
    rw [if_neg hbb]
  · show (if ((b, k) : Fin B × κ) = (b', k') then eq
        else (glueFam F).Q (b, k) (b', k')) = po
    rw [if_neg (fun h => hbb (congrArg Prod.fst h))]
    show (if b = b' then (F b).Q k k' else po) = po
    rw [if_neg hbb]

/-- THE FAMILY GLUE FRAME. -/
theorem glueFam_frame (h : ∀ b, Frame (qnet (F b).E (F b).K (F b).Q)) :
    Frame (qnet (glueFam F).E (glueFam F).K (glueFam F).Q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨b, x, rfl⟩ := gembF_rep z
    rw [qnet_fam_same]
    exact (h b).refl_eq x
  · intro z w hzw
    obtain ⟨b, x, rfl⟩ := gembF_rep z
    obtain ⟨b', y, rfl⟩ := gembF_rep w
    by_cases hbb : b = b'
    · subst hbb
      rw [qnet_fam_same] at hzw
      rw [(h b).eq_id x y hzw]
    · rw [qnet_fam_cross hbb] at hzw
      exact absurd hzw (by decide)
  · intro z w
    obtain ⟨b, x, rfl⟩ := gembF_rep z
    obtain ⟨b', y, rfl⟩ := gembF_rep w
    by_cases hbb : b = b'
    · subst hbb
      rw [qnet_fam_same, qnet_fam_same]
      exact (h b).conv_ x y
    · rw [qnet_fam_cross (fun hh => hbb hh.symm),
        qnet_fam_cross hbb]
      rfl
  · intro z w v
    obtain ⟨b1, x, rfl⟩ := gembF_rep z
    obtain ⟨b2, y, rfl⟩ := gembF_rep w
    obtain ⟨b3, u, rfl⟩ := gembF_rep v
    by_cases h12 : b1 = b2
    · subst h12
      by_cases h13 : b1 = b3
      · subst h13
        rw [qnet_fam_same, qnet_fam_same, qnet_fam_same]
        exact (h b1).comp_ x y u
      · rw [qnet_fam_cross h13, qnet_fam_same, qnet_fam_cross h13]
        exact po_mem_comp_right _
    · by_cases h23 : b2 = b3
      · subst h23
        rw [qnet_fam_cross h12, qnet_fam_cross h12, qnet_fam_same]
        exact po_mem_comp_left _
      · by_cases h13 : b1 = b3
        · subst h13
          rw [qnet_fam_same, qnet_fam_cross h12, qnet_fam_cross h23]
          exact mem_comp_po_po _
        · rw [qnet_fam_cross h13, qnet_fam_cross h12,
            qnet_fam_cross h23]
          exact po_mem_comp_left _

/-- THE FAMILY GLUE THEOREM: pooled blocks + pool realization give a
    strictly valid glued certificate. -/
theorem glueFam_ok {P : List (Nat × List Concept)}
    (hpool : ∀ b : Fin B, MTOkPool (F b) b.val P)
    (hnopo : ∀ b : Fin B, MTNoPo (F b))
    (hreal : ∀ q ∈ P, ∃ (b : Fin B) (x : β ⊕ κ × Nat),
      b.val = q.1 ∧ ∀ c ∈ q.2, c ∈ mtLabel (F b) x) :
    MultiTierOk (glueFam F) := by
  refine
    { hp := ?_, frame_q := glueFam_frame (fun b => (hpool b).frame_q),
      e_clash := ?_, e_nobot := ?_, e_and := ?_, e_or := ?_,
      k_clash := ?_, k_nobot := ?_, k_and := ?_, k_or := ?_,
      ee_all := ?_, ek_all := ?_, ke_all := ?_,
      kk_pp := ?_, kk_ppi := ?_, kk_eq := ?_, kq_all := ?_,
      e_ex := ?_, k_ex := ?_ }
  · intro ⟨b, k⟩
    exact (hpool b).hp k
  · intro ⟨b, e⟩ a hmem
    exact (hpool b).e_clash e a hmem
  · intro ⟨b, e⟩
    exact (hpool b).e_nobot e
  · intro ⟨b, e⟩ c d hmem
    exact (hpool b).e_and e c d hmem
  · intro ⟨b, e⟩ c d hmem
    exact (hpool b).e_or e c d hmem
  · intro ⟨b, k⟩ a ha n hmem
    exact (hpool b).k_clash k a ha n hmem
  · intro ⟨b, k⟩ a ha
    exact (hpool b).k_nobot k a ha
  · intro ⟨b, k⟩ a ha c d hmem
    exact (hpool b).k_and k a ha c d hmem
  · intro ⟨b, k⟩ a ha c d hmem
    exact (hpool b).k_or k a ha c d hmem
  · intro ⟨b, e⟩ ⟨b', f⟩ r c hmem hr
    by_cases hbb : b = b'
    · subst hbb
      have hr' : (F b).E e f = r := by
        have h2 : (if b = b then (F b).E e f else po) = r := hr
        rwa [if_pos rfl] at h2
      exact (hpool b).ee_all e f r c hmem hr'
    · have hr' : po = r := by
        have h2 : (if b = b' then (F b).E e f else po) = r := hr
        rwa [if_neg hbb] at h2
      subst hr'
      exact absurd hmem ((hnopo b).ext e c)
  · intro ⟨b, e⟩ r c hmem ⟨b', k⟩ hr a ha
    by_cases hbb : b' = b
    · subst hbb
      have hr' : conv ((F b').K k e) = r := by
        have h2 : conv (if b' = b' then (F b').K k e else po) = r := hr
        rwa [if_pos rfl] at h2
      exact (hpool b').ek_all e r c hmem k hr' a ha
    · have hr' : po = r := by
        have h2 : conv (if b' = b then (F b').K k e else po) = r := hr
        rwa [if_neg hbb] at h2
      subst hr'
      exact absurd hmem ((hnopo b).ext e c)
  · intro ⟨b, k⟩ a ha r c hmem ⟨b', f⟩ hK
    by_cases hbb : b = b'
    · subst hbb
      have hK' : (F b).K k f = r := by
        have h2 : (if b = b then (F b).K k f else po) = r := hK
        rwa [if_pos rfl] at h2
      exact (hpool b).ke_all k a ha r c hmem f hK'
    · have hK' : po = r := by
        have h2 : (if b = b' then (F b).K k f else po) = r := hK
        rwa [if_neg hbb] at h2
      subst hK'
      exact absurd hmem ((hnopo b).ker k a ha c)
  · intro ⟨b, k⟩ a ha c hmem bb hbb
    exact (hpool b).kk_pp k a ha c hmem bb hbb
  · intro ⟨b, k⟩ a ha c hmem bb hbb
    exact (hpool b).kk_ppi k a ha c hmem bb hbb
  · intro ⟨b, k⟩ a ha c hmem
    exact (hpool b).kk_eq k a ha c hmem
  · intro ⟨b, k⟩ ⟨b', k'⟩ hne a ha r c hmem hQ bb hbb
    by_cases hbb' : b = b'
    · subst hbb'
      have hkk : k ≠ k' := fun h => hne (by rw [h])
      have hQ' : (F b).Q k k' = r := by
        have h2 : (if b = b then (F b).Q k k' else po) = r := hQ
        rwa [if_pos rfl] at h2
      exact (hpool b).kq_all k k' hkk a ha r c hmem hQ' bb hbb
    · have hQ' : po = r := by
        have h2 : (if b = b' then (F b).Q k k' else po) = r := hQ
        rwa [if_neg hbb'] at h2
      subst hQ'
      exact absurd hmem ((hnopo b).ker k a ha c)
  · intro ⟨b, e⟩ r c hmem
    rcases (hpool b).e_ex e r c hmem with
      ⟨f, hEf, hcf⟩ | ⟨k, hK, a, ha, hca⟩ | ⟨hrpo, q, hqP, hqt, hqc⟩
    · refine Or.inl ⟨(b, f), ?_, hcf⟩
      show (if b = b then (F b).E e f else po) = r
      rwa [if_pos rfl]
    · refine Or.inr ⟨(b, k), ?_, a, ha, hca⟩
      show conv (if b = b then (F b).K k e else po) = r
      rwa [if_pos rfl]
    · subst hrpo
      obtain ⟨b', x, hb't, hsub⟩ := hreal q hqP
      have hne : b' ≠ b := fun h => hqt (by rw [← hb't, h])
      rcases x with e' | ⟨k', i⟩
      · refine Or.inl ⟨(b', e'), ?_, hsub c hqc⟩
        show (if b = b' then (F b).E e e' else po) = po
        rw [if_neg (fun h => hne h.symm)]
      · refine Or.inr ⟨(b', k'), ?_, i % (F b').p k',
          Nat.mod_lt i ((hpool b').hp k'), hsub c hqc⟩
        show conv (if b' = b then (F b').K k' e else po) = po
        rw [if_neg hne]
        rfl
  · intro ⟨b, k⟩ a ha r c hmem
    rcases (hpool b).k_ex k a ha r c hmem with
      ⟨f, hKf, hcf⟩ | ⟨hrd, bb, hbb, hcb⟩ | ⟨hreq, hc⟩ |
      ⟨k', hne, hQ, bb, hbb, hcb⟩ | ⟨hrpo, q, hqP, hqt, hqc⟩
    · refine Or.inl ⟨(b, f), ?_, hcf⟩
      show (if b = b then (F b).K k f else po) = r
      rwa [if_pos rfl]
    · exact Or.inr (Or.inl ⟨hrd, bb, hbb, hcb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hreq, hc⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨(b, k'),
        fun h => hne (congrArg Prod.snd h), ?_, bb, hbb, hcb⟩))
      show (if b = b then (F b).Q k k' else po) = r
      rwa [if_pos rfl]
    · subst hrpo
      obtain ⟨b', x, hb't, hsub⟩ := hreal q hqP
      have hbne : b' ≠ b := fun h => hqt (by rw [← hb't, h])
      rcases x with e' | ⟨k', i⟩
      · refine Or.inl ⟨(b', e'), ?_, hsub c hqc⟩
        show (if b = b' then (F b).K k e' else po) = po
        rw [if_neg (fun h => hbne h.symm)]
      · refine Or.inr (Or.inr (Or.inr ⟨(b', k'),
          fun h => hbne (congrArg Prod.fst h).symm, ?_,
          i % (F b').p k', Nat.mod_lt i ((hpool b').hp k'),
          hsub c hqc⟩))
        show (if b = b' then (F b).Q k k' else po) = po
        rw [if_neg (fun h => hbne h.symm)]

omit [DecidableEq κ] in
/-- Labels in the family glue: block `b`'s node keeps its label. -/
theorem glueFam_label (b : Fin B) (x : β ⊕ κ × Nat) :
    mtLabel (glueFam F)
      (match x with
        | .inl e => .inl (b, e)
        | .inr (k, i) => .inr ((b, k), i))
      = mtLabel (F b) x := by
  rcases x with e | ⟨k, i⟩
  · rfl
  · rfl

end FamGlue

/-! ## Round E2a (2026-07-23): assembly site preparation — sublist
universes, read-off frames, the chain builder, and segment selection

The first stone of the block construction (the "remaining assembly" of
LEAN.md).  Every block the assembly builds starts from the same moves,
certified here once and for all:

1. **The type universe is finite** (`mty_mem_sublists`): every model
   type is a sublist of `cl C0`, so D2b's pigeonhole machinery applies
   to the type sequence of any model chain.

2. **Read-off frames** (`readoff_frame` / `readoff_qnet_frame`): the
   restriction of a model's atomic relation to ANY family of pairwise
   distinct domain elements is a `Frame`; in particular a quotient
   network whose external values, kernel rows, and kernel–kernel
   values are all read off the model at distinct representative
   elements satisfies `frame_q` FOR FREE.  This is why the assembly
   never re-proves composition closure: wherever a certificate value
   is declared, it is read off the model.

3. **The chain builder** (`buildChain`): from any productive predicate
   (`S x` guarantees a `PP`-successor satisfying `S`), dependent
   choice yields an infinite ascending model chain — the input to the
   whole D2 layer.  This is the only place the extraction's vertical
   recursion needs choice.

4. **Segment selection** (`segment_select`, the capstone): along any
   model chain, past any bound, there is a segment with type-equal
   endpoints (`mty (c i) = mty (c (i+p))`) chosen PAST the recurrent
   tail (every phase type recurs cofinally — exactly the recurrence
   hypothesis of D2c's witness selection) and PAST the stabilization
   horizon of any finite list of externals (their relations to the
   chain are constant from `i` on — the constant-interface rows of the
   kernel).  `segment_kk_pp` / `segment_kk_ppi` re-index D2b's segment
   coherence to the phase-offset form of `MultiTierOk.kk_pp`/`kk_ppi`.

Ascending chains only, mirroring D2a–D2c; the descending duals are the
mirrored round (as round B was to round A). -/

/-! ### The sublist universe -/

section Sublists

variable {γ : Type}

/-- All sublists (in order) of a list — the finite universe every
    `List.filter` of it inhabits. -/
def sublists : List γ → List (List γ)
  | [] => [[]]
  | a :: t => sublists t ++ (sublists t).map (a :: ·)

theorem filter_mem_sublists (p : γ → Bool) :
    ∀ l : List γ, l.filter p ∈ sublists l := by
  intro l
  induction l with
  | nil => exact List.Mem.head _
  | cons a t ih =>
    show List.filter p (a :: t) ∈ sublists t ++ (sublists t).map (a :: ·)
    cases hp : p a with
    | true =>
      have hf : List.filter p (a :: t) = a :: t.filter p := by
        simp only [List.filter, hp]
      rw [hf]
      exact List.mem_append.mpr
        (Or.inr (List.mem_map.mpr ⟨t.filter p, ih, rfl⟩))
    | false =>
      have hf : List.filter p (a :: t) = t.filter p := by
        simp only [List.filter, hp]
      rw [hf]
      exact List.mem_append.mpr (Or.inl ih)

end Sublists

/-- Every model type inhabits the finite sublist universe of the
    closure — the pigeonhole universe of the extraction. -/
theorem mty_mem_sublists {C0 : Concept} {α : Type} {I : Interp α}
    (x : α) : mty C0 I x ∈ sublists (cl C0) :=
  filter_mem_sublists _ (cl C0)

/-! ### Read-off frames -/

/-- Frames transfer along pointwise-equal labellings. -/
theorem frame_ext {V : Type} {N N' : V → V → Atom}
    (hNN : ∀ x y, N x y = N' x y) (h : Frame N) : Frame N' where
  refl_eq := by
    intro x
    rw [← hNN x x]
    exact h.refl_eq x
  eq_id := by
    intro x y hxy
    rw [← hNN x y] at hxy
    exact h.eq_id x y hxy
  conv_ := by
    intro x y
    rw [← hNN y x, ← hNN x y]
    exact h.conv_ x y
  comp_ := by
    intro x y z
    rw [← hNN x z, ← hNN x y, ← hNN y z]
    exact h.comp_ x y z

section ReadOff

variable {α V : Type} {I : Interp α}

/-- THE READ-OFF FRAME: the restriction of a model's atomic relation
    to any family of pairwise distinct domain elements is a frame. -/
theorem readoff_frame (hI : RCC5Interp I) (elt : V → α)
    (hdom : ∀ v, I.dom (elt v))
    (hinj : ∀ v w, elt v = elt w → v = w) :
    Frame (fun v w => I.rho (elt v) (elt w)) where
  refl_eq v := hI.refl_eq (elt v) (hdom v)
  eq_id v w h := hinj v w (hI.eq_id (elt v) (elt w) (hdom v) (hdom w) h)
  conv_ v w := hI.conv_ (elt v) (elt w) (hdom v) (hdom w)
  comp_ v w u :=
    hI.comp_ (elt v) (elt w) (elt u) (hdom v) (hdom w) (hdom u)

end ReadOff

section ReadOffQnet

variable {α : Type} {I : Interp α}

/-- THE READ-OFF QUOTIENT FRAME (`frame_q` for free): a quotient
    network whose external values, kernel rows, and kernel–kernel
    values are all read off a model at pairwise distinct
    representative elements is a frame. -/
theorem readoff_qnet_frame [DecidableEq κ] (hI : RCC5Interp I)
    (eltE : β → α) (eltK : κ → α)
    (hdE : ∀ e, I.dom (eltE e)) (hdK : ∀ k, I.dom (eltK k))
    (hinj : ∀ v w : β ⊕ κ,
      Sum.elim eltE eltK v = Sum.elim eltE eltK w → v = w) :
    Frame (qnet (fun e f => I.rho (eltE e) (eltE f))
      (fun k f => I.rho (eltK k) (eltE f))
      (fun k k' => I.rho (eltK k) (eltK k'))) := by
  refine frame_ext (fun x y => ?_)
    (readoff_frame hI (Sum.elim eltE eltK)
      (fun v => match v with
        | .inl e => hdE e
        | .inr k => hdK k) hinj)
  rcases x with e | k <;> rcases y with f | k'
  · rfl
  · show I.rho (eltE e) (eltK k') = conv (I.rho (eltK k') (eltE e))
    exact hI.conv_ (eltK k') (eltE e) (hdK k') (hdE e)
  · rfl
  · show I.rho (eltK k) (eltK k')
      = if k = k' then eq else I.rho (eltK k) (eltK k')
    by_cases hk : k = k'
    · subst hk
      rw [if_pos rfl]
      exact hI.refl_eq (eltK k) (hdK k)
    · rw [if_neg hk]

end ReadOffQnet

/-! ### The chain builder (dependent choice) -/

section ChainBuilder

variable {α : Type} {I : Interp α} (S : α → Prop)
  (hprod : ∀ x, S x → ∃ y, S y ∧ I.dom y ∧ I.rho x y = pp)

/-- The chain, bundled with its invariant. -/
noncomputable def chainAux (x0 : α) (h0 : S x0) : Nat → {a : α // S a}
  | 0 => ⟨x0, h0⟩
  | n + 1 =>
    ⟨Classical.choose (hprod (chainAux x0 h0 n).1 (chainAux x0 h0 n).2),
     (Classical.choose_spec
       (hprod (chainAux x0 h0 n).1 (chainAux x0 h0 n).2)).1⟩

/-- THE CHAIN BUILDER: from a productive predicate, an infinite
    ascending model chain. -/
noncomputable def buildChain (x0 : α) (h0 : S x0) (n : Nat) : α :=
  (chainAux S hprod x0 h0 n).1

theorem buildChain_zero (x0 : α) (h0 : S x0) :
    buildChain S hprod x0 h0 0 = x0 := rfl

theorem buildChain_prop (x0 : α) (h0 : S x0) (n : Nat) :
    S (buildChain S hprod x0 h0 n) :=
  (chainAux S hprod x0 h0 n).2

theorem buildChain_step (x0 : α) (h0 : S x0) (n : Nat) :
    I.rho (buildChain S hprod x0 h0 n)
      (buildChain S hprod x0 h0 (n + 1)) = pp :=
  (Classical.choose_spec
    (hprod (chainAux S hprod x0 h0 n).1 (chainAux S hprod x0 h0 n).2)).2.2

theorem buildChain_dom (x0 : α) (h0 : S x0) (hd0 : I.dom x0) :
    ∀ n, I.dom (buildChain S hprod x0 h0 n)
  | 0 => hd0
  | n + 1 =>
    (Classical.choose_spec
      (hprod (chainAux S hprod x0 h0 n).1
        (chainAux S hprod x0 h0 n).2)).2.1

end ChainBuilder

/-! ### Segment selection -/

section SegmentSelect

variable {α : Type} {I : Interp α} (hI : RCC5Interp I)
  {c : Nat → α} (hdom : ∀ i, I.dom (c i))
  (hstep : ∀ i, I.rho (c i) (c (i + 1)) = pp)

include hI hdom hstep

/-- THE FINITE STABILIZATION HORIZON: the relations of finitely many
    externals to an ascending chain are jointly eventually constant. -/
theorem externals_stabilize (exts : List α) :
    (∀ e ∈ exts, I.dom e) →
    ∃ N, ∀ e ∈ exts, ∀ m n, N ≤ m → N ≤ n →
      I.rho (c m) e = I.rho (c n) e := by
  induction exts with
  | nil => exact fun _ => ⟨0, fun e he => nomatch he⟩
  | cons e rest ih =>
    intro hexts
    obtain ⟨Nr, hNr⟩ := ih (fun f hf => hexts f (List.mem_cons_of_mem e hf))
    obtain ⟨Ne, w, hNe⟩ :=
      external_stabilizes hI hdom hstep (hexts e (List.Mem.head rest))
    refine ⟨max Ne Nr, fun f hf m n hm hn => ?_⟩
    rcases List.mem_cons.mp hf with rfl | hmem
    · rw [hNe m (Nat.le_trans (Nat.le_max_left Ne Nr) hm),
        hNe n (Nat.le_trans (Nat.le_max_left Ne Nr) hn)]
    · exact hNr f hmem m n (Nat.le_trans (Nat.le_max_right Ne Nr) hm)
        (Nat.le_trans (Nat.le_max_right Ne Nr) hn)

/-- **`hstab` ON A WINDOW, EVENTUALLY — the "push past" branch** (§39.3).  For a
    FINITE list of externals and any window length `p`, all sufficiently high
    bases make every external's row constant across the whole window `[i, i+p)`.
    This is `externals_stabilize` re-expressed in exactly the shape
    `mixKernels_ok`'s (window-form) `hstab` consumes, and it is the second branch
    of the §39.3 dichotomy — the first being `stab_window_of_rank0`, which needs
    no horizon at all.  Together they are the certified toolkit for R6. -/
theorem stab_window_family (exts : List α) (hexts : ∀ e ∈ exts, I.dom e) (p : Nat) :
    ∃ N, ∀ e ∈ exts, ∀ i, N ≤ i → ∀ a, a < p →
      I.rho e (c (i + a)) = I.rho e (c i) := by
  obtain ⟨N, hN⟩ := externals_stabilize hI hdom hstep exts hexts
  refine ⟨N, fun e he i hi a _ => ?_⟩
  have hde : I.dom e := hexts e he
  rw [hI.conv_ (c (i + a)) e (hdom (i + a)) hde,
    hN e he (i + a) i (by omega) hi,
    ← hI.conv_ (c i) e (hdom i) hde]

/-- SEGMENT SELECTION (the round's capstone): past any bound, an
    ascending model chain has a segment with type-equal endpoints,
    every phase type recurring cofinally (the recurrence hypothesis of
    the witness-selection lemmas), and constant relations to any given
    finite list of externals from the segment base on (the constant
    interface rows of the kernel). -/
theorem segment_select (C0 : Concept) (exts : List α)
    (hexts : ∀ e ∈ exts, I.dom e) (L : Nat) :
    ∃ i p, L ≤ i ∧ 0 < p ∧
      mty C0 I (c i) = mty C0 I (c (i + p)) ∧
      (∀ e ∈ exts, ∀ m, i ≤ m → I.rho (c m) e = I.rho (c i) e) ∧
      (∀ a, i ≤ a → ∀ N, ∃ m, N ≤ m ∧
        mty C0 I (c m) = mty C0 I (c a)) := by
  obtain ⟨M, hM⟩ := recurrent_tail (sublists (cl C0))
    (fun m => mty C0 I (c m)) (fun m => mty_mem_sublists (c m))
  obtain ⟨Ns, hNs⟩ := externals_stabilize hI hdom hstep exts hexts
  obtain ⟨i, j, hLi, hij, heq⟩ := segment_exists (sublists (cl C0))
    (fun m => mty C0 I (c m)) (fun m => mty_mem_sublists (c m))
    (max L (max M Ns))
  have hLi' : L ≤ i := Nat.le_trans (Nat.le_max_left L (max M Ns)) hLi
  have hMi : M ≤ i := Nat.le_trans
    (Nat.le_trans (Nat.le_max_left M Ns) (Nat.le_max_right L (max M Ns)))
    hLi
  have hNsi : Ns ≤ i := Nat.le_trans
    (Nat.le_trans (Nat.le_max_right M Ns) (Nat.le_max_right L (max M Ns)))
    hLi
  refine ⟨i, j - i, hLi', by omega, ?_, ?_, ?_⟩
  · have hj : i + (j - i) = j := by omega
    rw [hj]
    exact heq
  · intro e he m him
    exact hNs e he m i (Nat.le_trans hNsi him) hNsi
  · intro a hia N
    exact hM a (Nat.le_trans hMi hia) N

/-- Segment coherence in phase-offset form (the `kk_pp` shape): a
    `∀PP` obligation at any phase offset puts its argument at every
    phase offset. -/
theorem segment_kk_pp {C0 : Concept} {i p : Nat}
    (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    {a : Nat} (ha : a < p) {E : Concept}
    (hE : Concept.all pp E ∈ mty C0 I (c (i + a))) :
    ∀ b, b < p → E ∈ mty C0 I (c (i + b)) := by
  intro b hb
  exact seg_pp hI hdom hstep (show i < i + p by omega) hty
    (show i ≤ i + a by omega) (show i + a < i + p by omega) hE
    (i + b) (by omega) (by omega)

/-- Segment coherence in phase-offset form (the `kk_ppi` shape). -/
theorem segment_kk_ppi {C0 : Concept} {i p : Nat}
    (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    {a : Nat} (ha : a < p) {E : Concept}
    (hE : Concept.all ppi E ∈ mty C0 I (c (i + a))) :
    ∀ b, b < p → E ∈ mty C0 I (c (i + b)) := by
  intro b hb
  exact seg_ppi hI hdom hstep (show i < i + p by omega) hty
    (show i ≤ i + a by omega) (show i + a < i + p by omega) hE
    (i + b) (by omega) (by omega)

end SegmentSelect

/-! ## Round E2a′ (2026-07-23): the descending mirror

The D2a–D2c + E2a toolkit for DESCENDING chains
(`rho (d i) (d (i+1)) = ppi` — each rung properly contains the next),
the model-side counterpart of the descending kernels (`up = false`)
that round B's `munf` already unfolds soundly (witness: `cboth`'s
second tower).  Mirrored DIRECTLY, as round B mirrored round A: a
transpose-duality functor exists in principle (flip `rho`, swap
`PP ↔ PPI` in concepts), but the assembly mixes ascending and
descending kernels over the SAME interpretation and the SAME concept,
so every statement is proved here in the exact shape the block
construction consumes — no transposition layer to thread through.

The mirrored algebra: stepping DOWN the chain is `comp(PP, ·)`, so the
rank order reverses —

    {PPI}  →  {PO, EQ}  →  {DR, PP}     (dstabRank 0 → 1 → 2)

with `comp(PP,DR) = {DR}` and `comp(PP,PP) = {PP}` now the ABSORBING
cells (forward forcing: a `DR`/`PP` external at one position is
`DR`/`PP` at all later, smaller rungs) and `comp(PPI,PPI) = {PPI}` the
backward one (a contained external is inside all earlier, larger
rungs).  Segment coherence swaps roles: `∀PPI` obligations travel down
to the far endpoint and re-enter through the type equality
(`dseg_ppi`, the mirror of `seg_pp`), `∀PP` obligations climb to the
segment base and fire down from the far endpoint (`dseg_pp`, the
mirror of `seg_ppi`).  `seg_eq`/`seg_ex_eq` are direction-agnostic
(they never touch the chain step) and apply to descending chains
verbatim — no duals needed. -/

/-- The descending stabilization rank: `PPI` can still become
    anything, `PO`/`EQ` only sharpen, `DR`/`PP` are absorbing. -/
def dstabRank : Atom → Nat
  | ppi => 0
  | eq => 1
  | po => 1
  | dr => 2
  | pp => 2

/-- Each downward chain step moves the external relation monotonically
    in descending rank. -/
theorem dstabRank_mono : ∀ a b : Atom, b ∈ comp pp a →
    dstabRank a ≤ dstabRank b := by
  intro a b
  cases a <;> cases b <;> decide

/-- A rank-preserving downward step preserves the value. -/
theorem dstabRank_fix : ∀ a b : Atom, b ∈ comp pp a →
    dstabRank a = dstabRank b → b = a := by
  intro a b
  cases a <;> cases b <;> decide

theorem dstabRank_le_two : ∀ a : Atom, dstabRank a ≤ 2 := by
  intro a
  cases a <;> decide

section DescModelChain

variable {α : Type} {I : Interp α} (hI : RCC5Interp I)
  {d : Nat → α} (hdom : ∀ i, I.dom (d i))
  (hstep : ∀ i, I.rho (d i) (d (i + 1)) = ppi)

include hI hdom hstep

/-- Descending chain transitivity: strictly later is `PPI`. -/
theorem dchain_model_ppi : ∀ i j, i < j → I.rho (d i) (d j) = ppi := by
  have aux : ∀ i k, I.rho (d i) (d (i + 1 + k)) = ppi := by
    intro i k
    induction k with
    | zero => exact hstep i
    | succ k ih =>
      have h1 := hI.comp_ (d i) (d (i + 1 + k)) (d (i + 1 + k + 1))
        (hdom i) (hdom (i + 1 + k)) (hdom (i + 1 + k + 1))
      rw [ih, hstep (i + 1 + k)] at h1
      rw [show comp ppi ppi = [ppi] from rfl] at h1
      exact List.mem_singleton.mp h1
  intro i j hij
  have hj : j = i + 1 + (j - i - 1) := by omega
  rw [hj]
  exact aux i (j - i - 1)

/-- Descending chain elements are pairwise distinct (strong EQ). -/
theorem dchain_model_distinct : ∀ i j, i < j → d i ≠ d j := by
  intro i j hij heq
  have h1 := dchain_model_ppi hI hdom hstep i j hij
  rw [heq] at h1
  rw [hI.refl_eq (d j) (hdom j)] at h1
  exact absurd h1 (by decide)

/-- Strictly earlier is `PP` (seen from the later, smaller rung). -/
theorem dchain_model_pp : ∀ i j, i < j → I.rho (d j) (d i) = pp := by
  intro i j hij
  rw [hI.conv_ (d i) (d j) (hdom i) (hdom j),
    dchain_model_ppi hI hdom hstep i j hij]
  rfl

variable {e : α} (hedom : I.dom e)

include hedom

/-- The descending step fact for the external-relation sequence. -/
theorem dvstep : ∀ j,
    I.rho (d (j + 1)) e ∈ comp pp (I.rho (d j) e) := by
  intro j
  have h1 := hI.comp_ (d (j + 1)) (d j) e (hdom (j + 1)) (hdom j) hedom
  rw [dchain_model_pp hI hdom hstep j (j + 1) (Nat.lt_succ_self j)]
    at h1
  exact h1

/-- Rank monotonicity along the descending chain. -/
theorem dvrank_mono : ∀ i j, i ≤ j →
    dstabRank (I.rho (d i) e) ≤ dstabRank (I.rho (d j) e) := by
  have aux : ∀ i k, dstabRank (I.rho (d i) e)
      ≤ dstabRank (I.rho (d (i + k)) e) := by
    intro i k
    induction k with
    | zero => exact Nat.le_refl _
    | succ k ih =>
      exact Nat.le_trans ih
        (dstabRank_mono _ _ (dvstep hI hdom hstep hedom (i + k)))
  intro i j hij
  have hj : j = i + (j - i) := by omega
  rw [hj]
  exact aux i (j - i)

/-- THE DESCENDING STABILIZATION THEOREM: the relation of a fixed
    external element to a descending chain is eventually constant. -/
theorem dexternal_stabilizes :
    ∃ N w, ∀ j, N ≤ j → I.rho (d j) e = w := by
  have hrank : ∃ N, ∀ j, N ≤ j →
      dstabRank (I.rho (d j) e) = dstabRank (I.rho (d N) e) := by
    by_cases h2 : ∃ i, dstabRank (I.rho (d i) e) = 2
    · obtain ⟨i, hi⟩ := h2
      refine ⟨i, fun j hj => ?_⟩
      have h3 := dvrank_mono hI hdom hstep hedom i j hj
      have h4 := dstabRank_le_two (I.rho (d j) e)
      omega
    · by_cases h1 : ∃ i, dstabRank (I.rho (d i) e) = 1
      · obtain ⟨i, hi⟩ := h1
        refine ⟨i, fun j hj => ?_⟩
        have h3 := dvrank_mono hI hdom hstep hedom i j hj
        have h4 : dstabRank (I.rho (d j) e) ≠ 2 :=
          fun hh => h2 ⟨j, hh⟩
        have h5 := dstabRank_le_two (I.rho (d j) e)
        omega
      · refine ⟨0, fun j _ => ?_⟩
        have h4 : dstabRank (I.rho (d j) e) ≠ 2 :=
          fun hh => h2 ⟨j, hh⟩
        have h5 : dstabRank (I.rho (d j) e) ≠ 1 :=
          fun hh => h1 ⟨j, hh⟩
        have h6 := dstabRank_le_two (I.rho (d j) e)
        have h7 : dstabRank (I.rho (d 0) e) ≠ 2 :=
          fun hh => h2 ⟨0, hh⟩
        have h8 : dstabRank (I.rho (d 0) e) ≠ 1 :=
          fun hh => h1 ⟨0, hh⟩
        have h9 := dstabRank_le_two (I.rho (d 0) e)
        omega
  obtain ⟨N, hN⟩ := hrank
  refine ⟨N, I.rho (d N) e, ?_⟩
  have aux : ∀ k, I.rho (d (N + k)) e = I.rho (d N) e := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have h1 := dvstep hI hdom hstep hedom (N + k)
      rw [ih] at h1
      have h2 : dstabRank (I.rho (d N) e)
          = dstabRank (I.rho (d (N + k + 1)) e) := by
        rw [hN (N + k + 1) (by omega)]
      exact dstabRank_fix _ _ h1 h2
  intro j hj
  have hj2 : j = N + (j - N) := by omega
  rw [hj2]
  exact aux (j - N)

/-- FORWARD FORCING (`DR`, descending): a disjoint external is `DR` to
    ALL later (smaller) chain positions — `comp(PP,DR) = {DR}`. -/
theorem dforward_forcing_dr {i : Nat} (h : I.rho (d i) e = dr) :
    ∀ j, i ≤ j → I.rho (d j) e = dr := by
  intro j hj
  rcases Nat.lt_or_ge i j with hlt | hge
  · have h1 := hI.comp_ (d j) (d i) e (hdom j) (hdom i) hedom
    rw [dchain_model_pp hI hdom hstep i j hlt, h] at h1
    rw [show comp pp dr = [dr] from rfl] at h1
    exact List.mem_singleton.mp h1
  · have hji : j = i := by omega
    rw [hji]
    exact h

/-- FORWARD FORCING (`PP`, descending): a containing external contains
    ALL later (smaller) chain positions — `comp(PP,PP) = {PP}`. -/
theorem dforward_forcing_pp {i : Nat} (h : I.rho (d i) e = pp) :
    ∀ j, i ≤ j → I.rho (d j) e = pp := by
  intro j hj
  rcases Nat.lt_or_ge i j with hlt | hge
  · have h1 := hI.comp_ (d j) (d i) e (hdom j) (hdom i) hedom
    rw [dchain_model_pp hI hdom hstep i j hlt, h] at h1
    rw [show comp pp pp = [pp] from rfl] at h1
    exact List.mem_singleton.mp h1
  · have hji : j = i := by omega
    rw [hji]
    exact h

/-- BACKWARD ABSORPTION (`PPI`, descending): a contained external
    stays inside ALL earlier (larger) chain positions —
    `comp(PPI,PPI) = {PPI}`. -/
theorem dbackward_absorption_ppi {i : Nat} (h : I.rho (d i) e = ppi) :
    ∀ j, j ≤ i → I.rho (d j) e = ppi := by
  intro j hj
  rcases Nat.lt_or_ge j i with hlt | hge
  · have h1 := hI.comp_ (d j) (d i) e (hdom j) (hdom i) hedom
    rw [dchain_model_ppi hI hdom hstep j i hlt, h] at h1
    rw [show comp ppi ppi = [ppi] from rfl] at h1
    exact List.mem_singleton.mp h1
  · have hji : j = i := by omega
    rw [hji]
    exact h

end DescModelChain

/-! ### Descending segment coherence -/

section DescSegment

variable {α : Type} {I : Interp α} (hI : RCC5Interp I)
  {C0 : Concept}
  {d : Nat → α} (hdom : ∀ i, I.dom (d i))
  (hstep : ∀ i, I.rho (d i) (d (i + 1)) = ppi)

include hI hdom hstep

/-- SEGMENT COHERENCE, descending `PPI` side (the mirror of `seg_pp`):
    with type-equal endpoints, a `∀PPI` obligation anywhere in the
    segment puts its argument in EVERY segment type. -/
theorem dseg_ppi {i j : Nat} (hij : i < j)
    (hty : mty C0 I (d i) = mty C0 I (d j))
    {a : Nat} (hia : i ≤ a) (haj : a < j) {E : Concept}
    (hE : Concept.all ppi E ∈ mty C0 I (d a)) :
    ∀ b, i ≤ b → b < j → E ∈ mty C0 I (d b) := by
  -- the obligation descends to the far endpoint, transfers to the base
  have htop : Concept.all ppi E ∈ mty C0 I (d j) := by
    obtain ⟨hcl, hsat⟩ := mem_mty.mp hE
    exact mem_mty.mpr ⟨hcl, sat_all_ppi_down hI (hdom a) (hdom j)
      (dchain_model_pp hI hdom hstep a j haj) hsat⟩
  have hbot : Concept.all ppi E ∈ mty C0 I (d i) := by
    rw [hty]; exact htop
  intro b hib hbj
  rcases Nat.lt_or_ge i b with hlt | hge
  · exact mty_all hbot (hdom b) (dchain_model_ppi hI hdom hstep i b hlt)
  · have hbi : b = i := by omega
    subst hbi
    -- E at the base endpoint: fire at the far endpoint, transfer back
    have hEj : E ∈ mty C0 I (d j) :=
      mty_all hbot (hdom j) (dchain_model_ppi hI hdom hstep b j (by omega))
    rw [← hty] at hEj
    exact hEj

/-- SEGMENT COHERENCE, descending `PP` side (the mirror of `seg_ppi`). -/
theorem dseg_pp {i j : Nat} (hij : i < j)
    (hty : mty C0 I (d i) = mty C0 I (d j))
    {a : Nat} (hia : i ≤ a) (_haj : a < j) {E : Concept}
    (hE : Concept.all pp E ∈ mty C0 I (d a)) :
    ∀ b, i ≤ b → b < j → E ∈ mty C0 I (d b) := by
  -- the obligation climbs to the base endpoint, transfers to the far one
  have hbot : Concept.all pp E ∈ mty C0 I (d i) := by
    rcases Nat.lt_or_ge i a with hlt | hge
    · obtain ⟨hcl, hsat⟩ := mem_mty.mp hE
      exact mem_mty.mpr ⟨hcl, sat_all_pp_up hI (hdom a) (hdom i)
        (dchain_model_pp hI hdom hstep i a hlt) hsat⟩
    · have hai : a = i := by omega
      subst hai
      exact hE
  have htop : Concept.all pp E ∈ mty C0 I (d j) := by
    rw [← hty]; exact hbot
  intro b hib hbj
  -- every segment rung contains the far endpoint's view: fire down
  have hpp : I.rho (d j) (d b) = pp :=
    dchain_model_pp hI hdom hstep b j (by omega)
  exact mty_all htop (hdom b) hpp

end DescSegment

/-! ### Descending witness selection -/

section DescWitnessSelection

variable {α : Type} {I : Interp α} (hI : RCC5Interp I)
  {d : Nat → α} (hdom : ∀ i, I.dom (d i))
  (hstep : ∀ i, I.rho (d i) (d (i + 1)) = ppi)
  {C0 : Concept} {t : List Concept}
  (hrec : ∀ N, ∃ a, N ≤ a ∧ mty C0 I (d a) = t)

include hI hdom hstep hrec

/-- A recurring `∃PPI`-demand on a descending chain has, past any
    bound, a witness inside ALL chain positions up to that bound. -/
theorem dppi_witness_all_below {D : Concept}
    (hD : Concept.ex ppi D ∈ t) (B : Nat) :
    ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
      ∀ b, b ≤ B → I.rho (d b) w = ppi := by
  obtain ⟨a, hBa, hta⟩ := hrec B
  have hDa : Concept.ex ppi D ∈ mty C0 I (d a) := by
    rw [hta]; exact hD
  obtain ⟨w, hw, hr, hDw⟩ := mty_ex hDa
  exact ⟨w, hw, hDw, fun b hb =>
    dbackward_absorption_ppi hI hdom hstep hw hr b
      (Nat.le_trans hb hBa)⟩

/-- A recurring `∃DR`-demand on a descending chain has a witness `DR`
    to ALL chain positions past some anchor. -/
theorem ddr_witness_all_above {D : Concept}
    (hD : Concept.ex dr D ∈ t) :
    ∃ a w, I.dom w ∧ D ∈ mty C0 I w ∧
      ∀ b, a ≤ b → I.rho (d b) w = dr := by
  obtain ⟨a, _, hta⟩ := hrec 0
  have hDa : Concept.ex dr D ∈ mty C0 I (d a) := by
    rw [hta]; exact hD
  obtain ⟨w, hw, hr, hDw⟩ := mty_ex hDa
  exact ⟨a, w, hw, hDw, fun b hb =>
    dforward_forcing_dr hI hdom hstep hw hr b hb⟩

/-- A recurring `∃PP`-demand on a descending chain has a witness
    containing ALL chain positions past some anchor. -/
theorem dpp_witness_all_above {D : Concept}
    (hD : Concept.ex pp D ∈ t) :
    ∃ a w, I.dom w ∧ D ∈ mty C0 I w ∧
      ∀ b, a ≤ b → I.rho (d b) w = pp := by
  obtain ⟨a, _, hta⟩ := hrec 0
  have hDa : Concept.ex pp D ∈ mty C0 I (d a) := by
    rw [hta]; exact hD
  obtain ⟨w, hw, hr, hDw⟩ := mty_ex hDa
  exact ⟨a, w, hw, hDw, fun b hb =>
    dforward_forcing_pp hI hdom hstep hw hr b hb⟩

end DescWitnessSelection

/-! ### The descending chain builder -/

section DescChainBuilder

variable {α : Type} {I : Interp α} (S : α → Prop)
  (hprod : ∀ x, S x → ∃ y, S y ∧ I.dom y ∧ I.rho x y = ppi)

/-- The descending chain, bundled with its invariant. -/
noncomputable def dchainAux (x0 : α) (h0 : S x0) :
    Nat → {a : α // S a}
  | 0 => ⟨x0, h0⟩
  | n + 1 =>
    ⟨Classical.choose
       (hprod (dchainAux x0 h0 n).1 (dchainAux x0 h0 n).2),
     (Classical.choose_spec
       (hprod (dchainAux x0 h0 n).1 (dchainAux x0 h0 n).2)).1⟩

/-- THE DESCENDING CHAIN BUILDER: from a productive predicate, an
    infinite descending model chain. -/
noncomputable def dbuildChain (x0 : α) (h0 : S x0) (n : Nat) : α :=
  (dchainAux S hprod x0 h0 n).1

theorem dbuildChain_zero (x0 : α) (h0 : S x0) :
    dbuildChain S hprod x0 h0 0 = x0 := rfl

theorem dbuildChain_prop (x0 : α) (h0 : S x0) (n : Nat) :
    S (dbuildChain S hprod x0 h0 n) :=
  (dchainAux S hprod x0 h0 n).2

theorem dbuildChain_step (x0 : α) (h0 : S x0) (n : Nat) :
    I.rho (dbuildChain S hprod x0 h0 n)
      (dbuildChain S hprod x0 h0 (n + 1)) = ppi :=
  (Classical.choose_spec
    (hprod (dchainAux S hprod x0 h0 n).1
      (dchainAux S hprod x0 h0 n).2)).2.2

theorem dbuildChain_dom (x0 : α) (h0 : S x0) (hd0 : I.dom x0) :
    ∀ n, I.dom (dbuildChain S hprod x0 h0 n)
  | 0 => hd0
  | n + 1 =>
    (Classical.choose_spec
      (hprod (dchainAux S hprod x0 h0 n).1
        (dchainAux S hprod x0 h0 n).2)).2.1

end DescChainBuilder

/-! ### Descending segment selection -/

section DescSegmentSelect

variable {α : Type} {I : Interp α} (hI : RCC5Interp I)
  {d : Nat → α} (hdom : ∀ i, I.dom (d i))
  (hstep : ∀ i, I.rho (d i) (d (i + 1)) = ppi)

include hI hdom hstep

/-- The descending finite stabilization horizon. -/
theorem dexternals_stabilize (exts : List α) :
    (∀ e ∈ exts, I.dom e) →
    ∃ N, ∀ e ∈ exts, ∀ m n, N ≤ m → N ≤ n →
      I.rho (d m) e = I.rho (d n) e := by
  induction exts with
  | nil => exact fun _ => ⟨0, fun e he => nomatch he⟩
  | cons e rest ih =>
    intro hexts
    obtain ⟨Nr, hNr⟩ := ih (fun f hf => hexts f (List.mem_cons_of_mem e hf))
    obtain ⟨Ne, w, hNe⟩ :=
      dexternal_stabilizes hI hdom hstep (hexts e (List.Mem.head rest))
    refine ⟨max Ne Nr, fun f hf m n hm hn => ?_⟩
    rcases List.mem_cons.mp hf with rfl | hmem
    · rw [hNe m (Nat.le_trans (Nat.le_max_left Ne Nr) hm),
        hNe n (Nat.le_trans (Nat.le_max_left Ne Nr) hn)]
    · exact hNr f hmem m n (Nat.le_trans (Nat.le_max_right Ne Nr) hm)
        (Nat.le_trans (Nat.le_max_right Ne Nr) hn)

/-- DESCENDING SEGMENT SELECTION (the mirror capstone). -/
theorem dsegment_select (C0 : Concept) (exts : List α)
    (hexts : ∀ e ∈ exts, I.dom e) (L : Nat) :
    ∃ i p, L ≤ i ∧ 0 < p ∧
      mty C0 I (d i) = mty C0 I (d (i + p)) ∧
      (∀ e ∈ exts, ∀ m, i ≤ m → I.rho (d m) e = I.rho (d i) e) ∧
      (∀ a, i ≤ a → ∀ N, ∃ m, N ≤ m ∧
        mty C0 I (d m) = mty C0 I (d a)) := by
  obtain ⟨M, hM⟩ := recurrent_tail (sublists (cl C0))
    (fun m => mty C0 I (d m)) (fun m => mty_mem_sublists (d m))
  obtain ⟨Ns, hNs⟩ := dexternals_stabilize hI hdom hstep exts hexts
  obtain ⟨i, j, hLi, hij, heq⟩ := segment_exists (sublists (cl C0))
    (fun m => mty C0 I (d m)) (fun m => mty_mem_sublists (d m))
    (max L (max M Ns))
  have hLi' : L ≤ i := Nat.le_trans (Nat.le_max_left L (max M Ns)) hLi
  have hMi : M ≤ i := Nat.le_trans
    (Nat.le_trans (Nat.le_max_left M Ns) (Nat.le_max_right L (max M Ns)))
    hLi
  have hNsi : Ns ≤ i := Nat.le_trans
    (Nat.le_trans (Nat.le_max_right M Ns) (Nat.le_max_right L (max M Ns)))
    hLi
  refine ⟨i, j - i, hLi', by omega, ?_, ?_, ?_⟩
  · have hj : i + (j - i) = j := by omega
    rw [hj]
    exact heq
  · intro e he m him
    exact hNs e he m i (Nat.le_trans hNsi him) hNsi
  · intro a hia N
    exact hM a (Nat.le_trans hMi hia) N

/-- Descending segment coherence in phase-offset form (`kk_ppi`
    shape). -/
theorem dsegment_kk_ppi {C0 : Concept} {i p : Nat}
    (hty : mty C0 I (d i) = mty C0 I (d (i + p)))
    {a : Nat} (ha : a < p) {E : Concept}
    (hE : Concept.all ppi E ∈ mty C0 I (d (i + a))) :
    ∀ b, b < p → E ∈ mty C0 I (d (i + b)) := by
  intro b hb
  exact dseg_ppi hI hdom hstep (show i < i + p by omega) hty
    (show i ≤ i + a by omega) (show i + a < i + p by omega) hE
    (i + b) (by omega) (by omega)

/-- Descending segment coherence in phase-offset form (`kk_pp`
    shape). -/
theorem dsegment_kk_pp {C0 : Concept} {i p : Nat}
    (hty : mty C0 I (d i) = mty C0 I (d (i + p)))
    {a : Nat} (ha : a < p) {E : Concept}
    (hE : Concept.all pp E ∈ mty C0 I (d (i + a))) :
    ∀ b, b < p → E ∈ mty C0 I (d (i + b)) := by
  intro b hb
  exact dseg_pp hI hdom hstep (show i < i + p by omega) hty
    (show i ≤ i + a by omega) (show i + a < i + p by omega) hE
    (i + b) (by omega) (by omega)

end DescSegmentSelect

/-! ## Round E2b (2026-07-23): witness banks + the kernel site

The second stone of the block construction: composing segment selection
(round E2a/E2a′) with witness selection (rounds D2c/E2a′) so that EVERY
`DR`/`PP`/`PPI` demand of a segment-kernel gets a designated witness
whose relation to the WHOLE segment is the constant demanded atom —
the external row `K k w` the certificate kernel will declare.

The selection-order subtlety this round resolves (the first piece of
LEAN.md item 3's circularity): witnesses whose constancy comes from
BACKWARD forcing (`DR`/`PP` on ascending chains, `PPI` on descending
ones) can be picked AFTER the segment — constancy below a late pick
covers any fixed segment below it; witnesses whose constancy comes
from FORWARD absorption (`PPI` ascending, `DR`/`PP` descending) must
be picked BEFORE it — so they are collected into an anchored BANK (one
witness per recurring type and demand, uniform anchor by
`anchored_all`, classical case split on recurrence), and the segment
is then selected past the bank's anchor.

Capstones `kernel_site` / `dkernel_site`: past any bound, a model
chain has a segment with type-equal endpoints, constant context rows,
cofinally recurring phase types, AND a constant-row witness for every
`DR`/`PP`/`PPI` demand of every phase type.  `∃EQ` demands are
fulfilled in-phase (`seg_ex_eq`); `∃PO` demands are the pool's
business (round E1) — neither needs a witness row. -/

/-! ### Anchor uniformization -/

/-- Finitely many anchor-monotone goals admit a uniform anchor. -/
theorem anchored_all {γ : Type} (Φ : γ → Nat → Prop)
    (hmono : ∀ x A A', A ≤ A' → Φ x A → Φ x A') :
    ∀ l : List γ, (∀ x ∈ l, ∃ A, Φ x A) → ∃ A, ∀ x ∈ l, Φ x A := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨0, fun x hx => nomatch hx⟩
  | cons a t ih =>
    intro hex
    obtain ⟨At, hAt⟩ := ih (fun x hx => hex x (List.mem_cons_of_mem a hx))
    obtain ⟨Aa, hAa⟩ := hex a (List.Mem.head t)
    refine ⟨max Aa At, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact hmono x Aa _ (Nat.le_max_left Aa At) hAa
    · exact hmono x At _ (Nat.le_max_right Aa At) (hAt x hmem)

/-! ### The ascending kernel site -/

section KernelSite

variable {α : Type} {I : Interp α} (hI : RCC5Interp I)
  {c : Nat → α} (hdom : ∀ i, I.dom (c i))
  (hstep : ∀ i, I.rho (c i) (c (i + 1)) = pp)

include hI hdom hstep

/-- THE `PPI` WITNESS BANK: one witness per recurring type and
    `∃PPI`-demand, with a UNIFORM anchor past which every bank witness
    contains every chain position.  Collected BEFORE segment selection
    (forward absorption anchors forward). -/
theorem ppi_witness_bank (C0 : Concept) :
    ∃ A : Nat, ∀ t, t ∈ sublists (cl C0) →
      (∀ N, ∃ a, N ≤ a ∧ mty C0 I (c a) = t) →
      ∀ D, Concept.ex ppi D ∈ t →
      ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
        ∀ b, A ≤ b → I.rho (c b) w = ppi := by
  refine anchored_all
    (fun t A => (∀ N, ∃ a, N ≤ a ∧ mty C0 I (c a) = t) →
      ∀ D, Concept.ex ppi D ∈ t →
      ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
        ∀ b, A ≤ b → I.rho (c b) w = ppi)
    ?_ (sublists (cl C0)) ?_
  · intro t A A' hAA h hrec D hD
    obtain ⟨w, hw, hDw, hall⟩ := h hrec D hD
    exact ⟨w, hw, hDw, fun b hb => hall b (Nat.le_trans hAA hb)⟩
  · intro t _
    by_cases hrec : ∀ N, ∃ a, N ≤ a ∧ mty C0 I (c a) = t
    · -- the type recurs: one anchored witness per `∃PPI`-demand,
      -- uniformized over the type's members
      have hex' : ∀ x ∈ t, ∃ A, ∀ D, x = Concept.ex ppi D →
          ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
            ∀ b, A ≤ b → I.rho (c b) w = ppi := by
        intro x hx
        by_cases hsh : ∃ D, x = Concept.ex ppi D
        · obtain ⟨D, rfl⟩ := hsh
          obtain ⟨a, w, hw, hDw, hall⟩ :=
            ppi_witness_all_above hI hdom hstep hrec hx
          refine ⟨a, fun D' hD' => ?_⟩
          injection hD' with hinj1 hinj2
          subst hinj2
          exact ⟨w, hw, hDw, hall⟩
        · exact ⟨0, fun D hxD => absurd ⟨D, hxD⟩ hsh⟩
      have hmono' : ∀ (x : Concept) (A A' : Nat), A ≤ A' →
          (∀ D, x = Concept.ex ppi D →
            ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
              ∀ b, A ≤ b → I.rho (c b) w = ppi) →
          ∀ D, x = Concept.ex ppi D →
            ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
              ∀ b, A' ≤ b → I.rho (c b) w = ppi := by
        intro x A A' hAA h D hxD
        obtain ⟨w, hw, hDw, hall⟩ := h D hxD
        exact ⟨w, hw, hDw, fun b hb => hall b (Nat.le_trans hAA hb)⟩
      obtain ⟨A, hA⟩ := anchored_all
        (fun x A => ∀ D, x = Concept.ex ppi D →
          ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
            ∀ b, A ≤ b → I.rho (c b) w = ppi)
        hmono' t hex'
      exact ⟨A, fun _ D hD => hA (Concept.ex ppi D) hD D rfl⟩
    · exact ⟨0, fun hr => absurd hr hrec⟩

/-- THE KERNEL SITE (the round's ascending capstone): past any bound,
    an ascending model chain has a segment with type-equal endpoints,
    constant rows to the given context, cofinally recurring phase
    types, and — the new content — a designated witness with the
    CONSTANT demanded relation across the whole segment for every
    `DR`/`PP`/`PPI` demand of every phase type.  These constant rows
    are exactly the external rows `K k w` the certificate kernel will
    declare; `∃EQ` demands are in-phase (`seg_ex_eq`) and `∃PO`
    demands pend against the pool (round E1). -/
theorem kernel_site (C0 : Concept) (exts : List α)
    (hexts : ∀ e ∈ exts, I.dom e) (L : Nat) :
    ∃ i p, L ≤ i ∧ 0 < p ∧
      mty C0 I (c i) = mty C0 I (c (i + p)) ∧
      (∀ e ∈ exts, ∀ m, i ≤ m → I.rho (c m) e = I.rho (c i) e) ∧
      (∀ a, i ≤ a → ∀ N, ∃ m, N ≤ m ∧
        mty C0 I (c m) = mty C0 I (c a)) ∧
      (∀ a r D, a ≤ p → (r = dr ∨ r = pp ∨ r = ppi) →
        Concept.ex r D ∈ mty C0 I (c (i + a)) →
        ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
          ∀ b, b ≤ p → I.rho (c (i + b)) w = r) := by
  obtain ⟨A, hA⟩ := ppi_witness_bank hI hdom hstep C0
  obtain ⟨i, p, hLi, hp, hty, hctx, hrec⟩ :=
    segment_select hI hdom hstep C0 exts hexts (max L A)
  have hLi' : L ≤ i := Nat.le_trans (Nat.le_max_left L A) hLi
  have hAi : A ≤ i := Nat.le_trans (Nat.le_max_right L A) hLi
  refine ⟨i, p, hLi', hp, hty, hctx, hrec, ?_⟩
  intro a r D _ hr hD
  have hrecA : ∀ N, ∃ m, N ≤ m ∧
      mty C0 I (c m) = mty C0 I (c (i + a)) :=
    hrec (i + a) (Nat.le_add_right i a)
  rcases hr with rfl | rfl | rfl
  · -- `DR`: pick AFTER the segment, backward forcing covers it
    obtain ⟨w, hw, hDw, hall⟩ :=
      dr_witness_all_below hI hdom hstep hrecA hD (i + p)
    exact ⟨w, hw, hDw, fun b hb => hall (i + b) (by omega)⟩
  · -- `PP`: likewise
    obtain ⟨w, hw, hDw, hall⟩ :=
      pp_witness_all_below hI hdom hstep hrecA hD (i + p)
    exact ⟨w, hw, hDw, fun b hb => hall (i + b) (by omega)⟩
  · -- `PPI`: from the pre-selected bank, anchor below the segment
    obtain ⟨w, hw, hDw, hall⟩ :=
      hA (mty C0 I (c (i + a))) (mty_mem_sublists (c (i + a))) hrecA D hD
    exact ⟨w, hw, hDw, fun b _ => hall (i + b) (by omega)⟩

end KernelSite

/-! ### The descending kernel site -/

section DescKernelSite

variable {α : Type} {I : Interp α} (hI : RCC5Interp I)
  {d : Nat → α} (hdom : ∀ i, I.dom (d i))
  (hstep : ∀ i, I.rho (d i) (d (i + 1)) = ppi)

include hI hdom hstep

/-- THE `DR`/`PP` WITNESS BANK (descending): forward forcing anchors
    forward, so `DR`- and `PP`-demand witnesses are collected before
    segment selection, with a uniform anchor. -/
theorem ddrpp_witness_bank (C0 : Concept) :
    ∃ A : Nat, ∀ t, t ∈ sublists (cl C0) →
      (∀ N, ∃ a, N ≤ a ∧ mty C0 I (d a) = t) →
      ∀ r D, (r = dr ∨ r = pp) → Concept.ex r D ∈ t →
      ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
        ∀ b, A ≤ b → I.rho (d b) w = r := by
  refine anchored_all
    (fun t A => (∀ N, ∃ a, N ≤ a ∧ mty C0 I (d a) = t) →
      ∀ r D, (r = dr ∨ r = pp) → Concept.ex r D ∈ t →
      ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
        ∀ b, A ≤ b → I.rho (d b) w = r)
    ?_ (sublists (cl C0)) ?_
  · intro t A A' hAA h hrec r D hr hD
    obtain ⟨w, hw, hDw, hall⟩ := h hrec r D hr hD
    exact ⟨w, hw, hDw, fun b hb => hall b (Nat.le_trans hAA hb)⟩
  · intro t _
    by_cases hrec : ∀ N, ∃ a, N ≤ a ∧ mty C0 I (d a) = t
    · have hex' : ∀ x ∈ t, ∃ A, ∀ r D, x = Concept.ex r D →
          (r = dr ∨ r = pp) →
          ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
            ∀ b, A ≤ b → I.rho (d b) w = r := by
        intro x hx
        by_cases hdr : ∃ D, x = Concept.ex dr D
        · obtain ⟨D, rfl⟩ := hdr
          obtain ⟨a, w, hw, hDw, hall⟩ :=
            ddr_witness_all_above hI hdom hstep hrec hx
          refine ⟨a, fun r D' heq _ => ?_⟩
          injection heq with hinj1 hinj2
          subst hinj1
          subst hinj2
          exact ⟨w, hw, hDw, hall⟩
        · by_cases hpp : ∃ D, x = Concept.ex pp D
          · obtain ⟨D, rfl⟩ := hpp
            obtain ⟨a, w, hw, hDw, hall⟩ :=
              dpp_witness_all_above hI hdom hstep hrec hx
            refine ⟨a, fun r D' heq _ => ?_⟩
            injection heq with hinj1 hinj2
            subst hinj1
            subst hinj2
            exact ⟨w, hw, hDw, hall⟩
          · refine ⟨0, fun r D' heq hr => ?_⟩
            rcases hr with rfl | rfl
            · exact absurd ⟨D', heq⟩ hdr
            · exact absurd ⟨D', heq⟩ hpp
      have hmono' : ∀ (x : Concept) (A A' : Nat), A ≤ A' →
          (∀ r D, x = Concept.ex r D → (r = dr ∨ r = pp) →
            ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
              ∀ b, A ≤ b → I.rho (d b) w = r) →
          ∀ r D, x = Concept.ex r D → (r = dr ∨ r = pp) →
            ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
              ∀ b, A' ≤ b → I.rho (d b) w = r := by
        intro x A A' hAA h r D hxD hr
        obtain ⟨w, hw, hDw, hall⟩ := h r D hxD hr
        exact ⟨w, hw, hDw, fun b hb => hall b (Nat.le_trans hAA hb)⟩
      obtain ⟨A, hA⟩ := anchored_all
        (fun x A => ∀ r D, x = Concept.ex r D → (r = dr ∨ r = pp) →
          ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
            ∀ b, A ≤ b → I.rho (d b) w = r)
        hmono' t hex'
      exact ⟨A, fun _ r D hr hD => hA (Concept.ex r D) hD r D rfl hr⟩
    · exact ⟨0, fun hr => absurd hr hrec⟩

/-- THE DESCENDING KERNEL SITE (the mirror capstone): `DR`/`PP`
    demands read the pre-selected bank, `PPI` demands are picked after
    the segment (backward absorption). -/
theorem dkernel_site (C0 : Concept) (exts : List α)
    (hexts : ∀ e ∈ exts, I.dom e) (L : Nat) :
    ∃ i p, L ≤ i ∧ 0 < p ∧
      mty C0 I (d i) = mty C0 I (d (i + p)) ∧
      (∀ e ∈ exts, ∀ m, i ≤ m → I.rho (d m) e = I.rho (d i) e) ∧
      (∀ a, i ≤ a → ∀ N, ∃ m, N ≤ m ∧
        mty C0 I (d m) = mty C0 I (d a)) ∧
      (∀ a r D, a ≤ p → (r = dr ∨ r = pp ∨ r = ppi) →
        Concept.ex r D ∈ mty C0 I (d (i + a)) →
        ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
          ∀ b, b ≤ p → I.rho (d (i + b)) w = r) := by
  obtain ⟨A, hA⟩ := ddrpp_witness_bank hI hdom hstep C0
  obtain ⟨i, p, hLi, hp, hty, hctx, hrec⟩ :=
    dsegment_select hI hdom hstep C0 exts hexts (max L A)
  have hLi' : L ≤ i := Nat.le_trans (Nat.le_max_left L A) hLi
  have hAi : A ≤ i := Nat.le_trans (Nat.le_max_right L A) hLi
  refine ⟨i, p, hLi', hp, hty, hctx, hrec, ?_⟩
  intro a r D _ hr hD
  have hrecA : ∀ N, ∃ m, N ≤ m ∧
      mty C0 I (d m) = mty C0 I (d (i + a)) :=
    hrec (i + a) (Nat.le_add_right i a)
  rcases hr with rfl | rfl | rfl
  · -- `DR`: from the bank
    obtain ⟨w, hw, hDw, hall⟩ :=
      hA (mty C0 I (d (i + a))) (mty_mem_sublists (d (i + a))) hrecA
        dr D (Or.inl rfl) hD
    exact ⟨w, hw, hDw, fun b _ => hall (i + b) (by omega)⟩
  · -- `PP`: from the bank
    obtain ⟨w, hw, hDw, hall⟩ :=
      hA (mty C0 I (d (i + a))) (mty_mem_sublists (d (i + a))) hrecA
        pp D (Or.inr rfl) hD
    exact ⟨w, hw, hDw, fun b _ => hall (i + b) (by omega)⟩
  · -- `PPI`: pick AFTER the segment, backward absorption covers it
    obtain ⟨w, hw, hDw, hall⟩ :=
      dppi_witness_all_below hI hdom hstep hrecA hD (i + p)
    exact ⟨w, hw, hDw, fun b hb => hall (i + b) (by omega)⟩

end DescKernelSite

/-! ## Round E3a (2026-07-23): the one-kernel block

The kernel-attachment move certified end-to-end at the CERTIFICATE
level: from a kernel site (round E2b) an actual `MultiTier` certificate
with one kernel, every declared value read off the model, and every
kernel-side validity obligation discharged.

`BlockOk` is `MTOkPool` minus exactly ONE field: the externals' own
fulfilment `e_ex` — the residual the assembly recursion discharges by
growing the block (an external's non-`PO` demands are demands of a
MODEL type, so `mty_ex` applies to them again; its `PO` demands pend
against the pool).  `mtOkPool_of_block` restores the full pooled
validity once the residual is discharged.

The construction (`one_kernel_block`): externals are indexed by the
SUBTYPE of carrier elements that are context elements or designated
witnesses (`Classical.choose` of the site's serving clause) — so the
representative map is injective BY CONSTRUCTION, no deduplication
machinery, and `readoff_qnet_frame` gives `frame_q` for free.  The
kernel representative is the segment base `c i`; no external can
coincide with it (its row to the segment is constant, and an `EQ` row
would identify it with two distinct chain elements).  Phases are the
segment's model types; every propositional/universal field is a `mty`
fact plus row constancy; `k_ex` routes `DR`/`PP`/`PPI` demands to
their designated witnesses (row at offset `0` = the demanded atom),
`EQ` demands in-phase (`seg_ex_eq`), `PO` demands to the pool.
`kernel_block_of_chain` composes the site and the block: EVERY
ascending model chain carries a valid one-kernel block past any bound,
with the pool premise reduced to `PO`-demand coverage over `cl C₀`.
The β index is finitely generated (context list + one witness per
demand triple `(a ≤ p, r, D ∈ cl C₀)`) — its finite enumeration is
D2d's business.  The multi-kernel block (declared `Q` values — the
rectangle problem) is the standing next obstacle, unchanged. -/

/-- Kernel-side validity: every `MTOkPool` field EXCEPT the externals'
    own fulfilment `e_ex` — the residual the assembly recursion
    discharges. -/
structure BlockOk {β κ : Type} [DecidableEq κ] (T : MultiTier β κ)
    (myTag : Nat) (P : List (Nat × List Concept)) : Prop where
  hp : ∀ k, 0 < T.p k
  frame_q : Frame (qnet T.E T.K T.Q)
  e_clash : ∀ e a, Concept.atom a ∈ T.tauE e → Concept.natom a ∉ T.tauE e
  e_nobot : ∀ e, Concept.bot ∉ T.tauE e
  e_and : ∀ e c d, Concept.and c d ∈ T.tauE e → c ∈ T.tauE e ∧ d ∈ T.tauE e
  e_or : ∀ e c d, Concept.or c d ∈ T.tauE e → c ∈ T.tauE e ∨ d ∈ T.tauE e
  k_clash : ∀ k a, a < T.p k → ∀ n, Concept.atom n ∈ T.phase k a →
    Concept.natom n ∉ T.phase k a
  k_nobot : ∀ k a, a < T.p k → Concept.bot ∉ T.phase k a
  k_and : ∀ k a, a < T.p k → ∀ c d, Concept.and c d ∈ T.phase k a →
    c ∈ T.phase k a ∧ d ∈ T.phase k a
  k_or : ∀ k a, a < T.p k → ∀ c d, Concept.or c d ∈ T.phase k a →
    c ∈ T.phase k a ∨ d ∈ T.phase k a
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
  k_ex : ∀ k a, a < T.p k → ∀ r c, Concept.ex r c ∈ T.phase k a →
    (∃ f, T.K k f = r ∧ c ∈ T.tauE f) ∨
    (r = cdir (T.up k) ∧ ∃ b, b < T.p k ∧ c ∈ T.phase k b) ∨
    (r = eq ∧ c ∈ T.phase k a) ∨
    (∃ k', k ≠ k' ∧ T.Q k k' = r ∧ ∃ b, b < T.p k' ∧ c ∈ T.phase k' b) ∨
    (r = po ∧ ∃ q ∈ P, q.1 ≠ myTag ∧ c ∈ q.2)

/-- Discharging the residual `e_ex` restores full pooled validity. -/
theorem mtOkPool_of_block {β κ : Type} [DecidableEq κ]
    {T : MultiTier β κ} {myTag : Nat} {P : List (Nat × List Concept)}
    (h : BlockOk T myTag P)
    (he : ∀ e r c, Concept.ex r c ∈ T.tauE e →
      (∃ f, T.E e f = r ∧ c ∈ T.tauE f) ∨
      (∃ k, conv (T.K k e) = r ∧ ∃ a, a < T.p k ∧ c ∈ T.phase k a) ∨
      (r = po ∧ ∃ q ∈ P, q.1 ≠ myTag ∧ c ∈ q.2)) :
    MTOkPool T myTag P where
  hp := h.hp
  frame_q := h.frame_q
  e_clash := h.e_clash
  e_nobot := h.e_nobot
  e_and := h.e_and
  e_or := h.e_or
  k_clash := h.k_clash
  k_nobot := h.k_nobot
  k_and := h.k_and
  k_or := h.k_or
  ee_all := h.ee_all
  ek_all := h.ek_all
  ke_all := h.ke_all
  kk_pp := h.kk_pp
  kk_ppi := h.kk_ppi
  kk_eq := h.kk_eq
  kq_all := h.kq_all
  e_ex := he
  k_ex := h.k_ex

/-- EMPTY POOL ⟹ PLAIN VALIDITY: a pooled certificate with no pool
    entries (`P = []`) is a full `MultiTierOk` — the `∃PO`-pool disjunct
    of `e_ex`/`k_ex` is vacuous (no `q ∈ []`).  So a kernel block with no
    `∃PO` demands (hence empty pool) is a genuine `MultiTier` certificate;
    the bridge the vertical assembly's pure-kernel clusters use. -/
theorem multiTierOk_of_pool_nil {β κ : Type} [DecidableEq κ]
    {T : MultiTier β κ} {myTag : Nat} (h : MTOkPool T myTag []) :
    MultiTierOk T where
  hp := h.hp
  frame_q := h.frame_q
  e_clash := h.e_clash
  e_nobot := h.e_nobot
  e_and := h.e_and
  e_or := h.e_or
  k_clash := h.k_clash
  k_nobot := h.k_nobot
  k_and := h.k_and
  k_or := h.k_or
  ee_all := h.ee_all
  ek_all := h.ek_all
  ke_all := h.ke_all
  kk_pp := h.kk_pp
  kk_ppi := h.kk_ppi
  kk_eq := h.kk_eq
  kq_all := h.kq_all
  e_ex := by
    intro e r c hmem
    rcases h.e_ex e r c hmem with h1 | h2 | ⟨_, q, hq, _⟩
    · exact Or.inl h1
    · exact Or.inr h2
    · exact absurd hq List.not_mem_nil
  k_ex := by
    intro k a ha r c hmem
    rcases h.k_ex k a ha r c hmem with h1 | h2 | h3 | h4 | ⟨_, q, hq, _⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr h4))
    · exact absurd hq List.not_mem_nil

section OneKernelBlock

variable {α : Type} {I : Interp α} (hI : RCC5Interp I)
  {c : Nat → α} (hdom : ∀ i, I.dom (c i))
  (hstep : ∀ i, I.rho (c i) (c (i + 1)) = pp)

include hI hdom hstep

/-- THE ONE-KERNEL BLOCK: a kernel site yields an actual `MultiTier`
    certificate — externals = context elements + designated witnesses
    (a subtype of the carrier, so representatives are injective by
    construction), one ascending kernel with the segment's model types
    as phases, every declared value read off the model — satisfying
    every `MTOkPool` field except the externals' residual `e_ex`,
    with the fragment's `MTNoPo` for free. -/
theorem one_kernel_block (C0 : Concept) (myTag : Nat)
    (P : List (Nat × List Concept)) (ctx : List α)
    (hctxdom : ∀ e ∈ ctx, I.dom e)
    {i p : Nat} (hp : 0 < p)
    (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    (hctx : ∀ e ∈ ctx, ∀ m, i ≤ m → I.rho (c m) e = I.rho (c i) e)
    (hserve : ∀ a r D, a ≤ p → (r = dr ∨ r = pp ∨ r = ppi) →
      Concept.ex r D ∈ mty C0 I (c (i + a)) →
      ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
        ∀ b, b ≤ p → I.rho (c (i + b)) w = r)
    (hpool : ∀ a, a < p → ∀ D, Concept.ex po D ∈ mty C0 I (c (i + a)) →
      ∃ q ∈ P, q.1 ≠ myTag ∧ D ∈ q.2) :
    ∃ (β : Type) (T : MultiTier β Unit),
      BlockOk T myTag P ∧
      T.p () = p ∧
      (∀ a, T.phase () a = mty C0 I (c (i + a))) ∧
      (∀ e : β, ∃ x, I.dom x ∧ T.tauE e = mty C0 I x) ∧
      (∀ e ∈ ctx, ∃ eb : β, T.tauE eb = mty C0 I e) ∧
      (POFree C0 → MTNoPo T) := by
  classical
  -- the external predicate: context elements and designated witnesses
  let W : α → Prop := fun w => w ∈ ctx ∨
    ∃ a r D, ∃ (ha : a ≤ p) (hr : r = dr ∨ r = pp ∨ r = ppi)
      (hD : Concept.ex r D ∈ mty C0 I (c (i + a))),
      w = Classical.choose (hserve a r D ha hr hD)
  have hWdom : ∀ w, W w → I.dom w := by
    intro w hw
    rcases hw with hctxm | ⟨a, r, D, ha, hr, hD, rfl⟩
    · exact hctxdom w hctxm
    · exact (Classical.choose_spec (hserve a r D ha hr hD)).1
  -- every external's row to the segment is constant
  have hWconst : ∀ w, W w → ∀ b, b ≤ p →
      I.rho (c (i + b)) w = I.rho (c i) w := by
    intro w hw b hb
    rcases hw with hctxm | ⟨a, r, D, ha, hr, hD, rfl⟩
    · exact hctx w hctxm (i + b) (Nat.le_add_right i b)
    · have hspec := (Classical.choose_spec (hserve a r D ha hr hD)).2.2
      have h0 : I.rho (c i)
          (Classical.choose (hserve a r D ha hr hD)) = r := by
        have h1 := hspec 0 (Nat.zero_le p)
        rwa [Nat.add_zero] at h1
      rw [hspec b hb, h0]
  -- no external coincides with the kernel representative
  have hcne : c (i + 1) ≠ c i := by
    intro hcc
    have h1 := hstep i
    rw [hcc] at h1
    have h2 := hI.refl_eq (c i) (hdom i)
    rw [h1] at h2
    exact absurd h2 (by decide)
  have hWne : ∀ w, W w → w ≠ c i := by
    intro w hw heq
    rcases hw with hctxm | ⟨a, r, D, ha, hr, hD, rfl⟩
    · have h1 := hctx w hctxm (i + 1) (Nat.le_add_right i 1)
      rw [heq] at h1
      rw [hI.refl_eq (c i) (hdom i)] at h1
      exact hcne (hI.eq_id (c (i + 1)) (c i) (hdom (i + 1)) (hdom i) h1)
    · have hspec := (Classical.choose_spec (hserve a r D ha hr hD)).2.2
      have h0 := hspec 0 (Nat.zero_le p)
      rw [Nat.add_zero, heq] at h0
      rw [hI.refl_eq (c i) (hdom i)] at h0
      rcases hr with rfl | rfl | rfl
      · exact absurd h0 (by decide)
      · exact absurd h0 (by decide)
      · exact absurd h0 (by decide)
  refine ⟨{w : α // W w},
    { E := fun e f => I.rho e.val f.val
      K := fun _ f => I.rho (c i) f.val
      Q := fun _ _ => I.rho (c i) (c i)
      up := fun _ => true
      tauE := fun e => mty C0 I e.val
      p := fun _ => p
      phase := fun _ a => mty C0 I (c (i + a)) },
    ?_, rfl, fun _ => rfl,
    fun (e : {w : α // W w}) => ⟨e.val, hWdom e.val e.2, rfl⟩,
    fun e he => ⟨⟨e, Or.inl he⟩, rfl⟩,
    fun hpo => ⟨fun _ _ => mty_no_all_po hpo,
      fun _ a _ _ => mty_no_all_po hpo⟩⟩
  refine
    { hp := fun _ => hp
      frame_q := ?_
      e_clash := fun e a h => mty_clash h
      e_nobot := fun e => mty_nobot
      e_and := fun e c d h => mty_and h
      e_or := fun e c d h => mty_or h
      k_clash := fun k a ha n h => mty_clash h
      k_nobot := fun k a ha => mty_nobot
      k_and := fun k a ha c d h => mty_and h
      k_or := fun k a ha c d h => mty_or h
      ee_all := fun e f r E hE hr => mty_all hE (hWdom f.val f.2) hr
      ek_all := ?_
      ke_all := ?_
      kk_pp := fun k a ha E hE b hb =>
        segment_kk_pp hI hdom hstep hty ha hE b hb
      kk_ppi := fun k a ha E hE b hb =>
        segment_kk_ppi hI hdom hstep hty ha hE b hb
      kk_eq := fun k a ha E hE => seg_eq hI hdom hE
      kq_all := fun k k' hne => absurd rfl hne
      k_ex := ?_ }
  · -- frame_q: the read-off quotient frame
    refine readoff_qnet_frame hI
      (fun (e : {w : α // W w}) => e.val) (fun _ => c i)
      (fun (e : {w : α // W w}) => hWdom e.val e.2) (fun _ => hdom i) ?_
    intro v w hvw
    rcases v with e | u <;> rcases w with f | u'
    · exact congrArg Sum.inl (Subtype.ext hvw)
    · exact absurd hvw (hWne e.val e.2)
    · exact absurd hvw.symm (hWne f.val f.2)
    · cases u; cases u'; rfl
  · -- ek_all: an external's obligation fires into every phase
    intro e r E hE k hK a ha
    have h2 : I.rho e.val (c (i + a)) = r := by
      rw [hI.conv_ (c (i + a)) e.val (hdom (i + a)) (hWdom e.val e.2),
        hWconst e.val e.2 a (Nat.le_of_lt ha)]
      exact hK
    exact mty_all hE (hdom (i + a)) h2
  · -- ke_all: a phase obligation fires at every matching external
    intro k a ha r E hE f hK
    have h1 : I.rho (c (i + a)) f.val = r := by
      rw [hWconst f.val f.2 a (Nat.le_of_lt ha)]
      exact hK
    exact mty_all hE (hWdom f.val f.2) h1
  · -- k_ex: demands routed by relation
    intro k a ha r E hE
    cases r with
    | dr =>
      refine Or.inl ⟨⟨Classical.choose
          (hserve a dr E (Nat.le_of_lt ha) (Or.inl rfl) hE),
        Or.inr ⟨a, dr, E, Nat.le_of_lt ha, Or.inl rfl, hE, rfl⟩⟩,
        ?_, ?_⟩
      · have hspec := (Classical.choose_spec
          (hserve a dr E (Nat.le_of_lt ha) (Or.inl rfl) hE)).2.2
        have h1 := hspec 0 (Nat.zero_le p)
        rwa [Nat.add_zero] at h1
      · exact (Classical.choose_spec
          (hserve a dr E (Nat.le_of_lt ha) (Or.inl rfl) hE)).2.1
    | pp =>
      refine Or.inl ⟨⟨Classical.choose
          (hserve a pp E (Nat.le_of_lt ha) (Or.inr (Or.inl rfl)) hE),
        Or.inr ⟨a, pp, E, Nat.le_of_lt ha, Or.inr (Or.inl rfl), hE,
          rfl⟩⟩, ?_, ?_⟩
      · have hspec := (Classical.choose_spec
          (hserve a pp E (Nat.le_of_lt ha) (Or.inr (Or.inl rfl)) hE)).2.2
        have h1 := hspec 0 (Nat.zero_le p)
        rwa [Nat.add_zero] at h1
      · exact (Classical.choose_spec
          (hserve a pp E (Nat.le_of_lt ha) (Or.inr (Or.inl rfl)) hE)).2.1
    | ppi =>
      refine Or.inl ⟨⟨Classical.choose
          (hserve a ppi E (Nat.le_of_lt ha) (Or.inr (Or.inr rfl)) hE),
        Or.inr ⟨a, ppi, E, Nat.le_of_lt ha, Or.inr (Or.inr rfl), hE,
          rfl⟩⟩, ?_, ?_⟩
      · have hspec := (Classical.choose_spec
          (hserve a ppi E (Nat.le_of_lt ha) (Or.inr (Or.inr rfl)) hE)).2.2
        have h1 := hspec 0 (Nat.zero_le p)
        rwa [Nat.add_zero] at h1
      · exact (Classical.choose_spec
          (hserve a ppi E (Nat.le_of_lt ha) (Or.inr (Or.inr rfl)) hE)).2.1
    | eq =>
      exact Or.inr (Or.inr (Or.inl ⟨rfl, seg_ex_eq hI hdom hE⟩))
    | po =>
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hpool a ha E hE⟩)))

/-- THE KERNEL-ATTACHMENT COROLLARY: every ascending model chain
    carries, past any bound, a valid one-kernel block whose phases are
    the model types of a type-equal segment — with the pool premise
    reduced to `PO`-demand coverage over the closure. -/
theorem kernel_block_of_chain (C0 : Concept) (myTag : Nat)
    (P : List (Nat × List Concept)) (ctx : List α)
    (hctxdom : ∀ e ∈ ctx, I.dom e) (L : Nat)
    (hpoolcl : ∀ D, Concept.ex po D ∈ cl C0 →
      ∃ q ∈ P, q.1 ≠ myTag ∧ D ∈ q.2) :
    ∃ i p, L ≤ i ∧ 0 < p ∧
      ∃ (β : Type) (T : MultiTier β Unit),
        BlockOk T myTag P ∧
        T.p () = p ∧
        (∀ a, T.phase () a = mty C0 I (c (i + a))) ∧
        (∀ e : β, ∃ x, I.dom x ∧ T.tauE e = mty C0 I x) ∧
        (∀ e ∈ ctx, ∃ eb : β, T.tauE eb = mty C0 I e) ∧
        (POFree C0 → MTNoPo T) := by
  obtain ⟨i, p, hLi, hp, hty, hctx, _, hserve⟩ :=
    kernel_site hI hdom hstep C0 ctx hctxdom L
  exact ⟨i, p, hLi, hp, one_kernel_block hI hdom hstep C0 myTag P ctx
    hctxdom hp hty hctx hserve
    (fun a _ D hD => hpoolcl D (mty_sub _ hD))⟩

end OneKernelBlock

/-! ## Round E3a′ (2026-07-23): the descending one-kernel block

The mirror of round E3a (as E2a′ was to E2a): a descending kernel
site yields a `MultiTier β Unit` certificate with one DESCENDING
kernel (`up = false`), same external subtype construction, same
read-off discipline, `kk_pp`/`kk_ppi` from the descending segment
coherence duals.  `seg_eq`/`seg_ex_eq` are direction-agnostic and are
reused as-is. -/

section DescOneKernelBlock

variable {α : Type} {I : Interp α} (hI : RCC5Interp I)
  {d : Nat → α} (hdom : ∀ i, I.dom (d i))
  (hstep : ∀ i, I.rho (d i) (d (i + 1)) = ppi)

include hI hdom hstep

/-- THE DESCENDING ONE-KERNEL BLOCK (mirror of `one_kernel_block`). -/
theorem done_kernel_block (C0 : Concept) (myTag : Nat)
    (P : List (Nat × List Concept)) (ctx : List α)
    (hctxdom : ∀ e ∈ ctx, I.dom e)
    {i p : Nat} (hp : 0 < p)
    (hty : mty C0 I (d i) = mty C0 I (d (i + p)))
    (hctx : ∀ e ∈ ctx, ∀ m, i ≤ m → I.rho (d m) e = I.rho (d i) e)
    (hserve : ∀ a r D, a ≤ p → (r = dr ∨ r = pp ∨ r = ppi) →
      Concept.ex r D ∈ mty C0 I (d (i + a)) →
      ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
        ∀ b, b ≤ p → I.rho (d (i + b)) w = r)
    (hpool : ∀ a, a < p → ∀ D, Concept.ex po D ∈ mty C0 I (d (i + a)) →
      ∃ q ∈ P, q.1 ≠ myTag ∧ D ∈ q.2) :
    ∃ (β : Type) (T : MultiTier β Unit),
      BlockOk T myTag P ∧
      T.p () = p ∧
      (∀ a, T.phase () a = mty C0 I (d (i + a))) ∧
      (∀ e : β, ∃ x, I.dom x ∧ T.tauE e = mty C0 I x) ∧
      (∀ e ∈ ctx, ∃ eb : β, T.tauE eb = mty C0 I e) ∧
      (POFree C0 → MTNoPo T) := by
  classical
  let W : α → Prop := fun w => w ∈ ctx ∨
    ∃ a r D, ∃ (ha : a ≤ p) (hr : r = dr ∨ r = pp ∨ r = ppi)
      (hD : Concept.ex r D ∈ mty C0 I (d (i + a))),
      w = Classical.choose (hserve a r D ha hr hD)
  have hWdom : ∀ w, W w → I.dom w := by
    intro w hw
    rcases hw with hctxm | ⟨a, r, D, ha, hr, hD, rfl⟩
    · exact hctxdom w hctxm
    · exact (Classical.choose_spec (hserve a r D ha hr hD)).1
  have hWconst : ∀ w, W w → ∀ b, b ≤ p →
      I.rho (d (i + b)) w = I.rho (d i) w := by
    intro w hw b hb
    rcases hw with hctxm | ⟨a, r, D, ha, hr, hD, rfl⟩
    · exact hctx w hctxm (i + b) (Nat.le_add_right i b)
    · have hspec := (Classical.choose_spec (hserve a r D ha hr hD)).2.2
      have h0 : I.rho (d i)
          (Classical.choose (hserve a r D ha hr hD)) = r := by
        have h1 := hspec 0 (Nat.zero_le p)
        rwa [Nat.add_zero] at h1
      rw [hspec b hb, h0]
  have hcne : d (i + 1) ≠ d i := by
    intro hcc
    have h1 := hstep i
    rw [hcc] at h1
    have h2 := hI.refl_eq (d i) (hdom i)
    rw [h1] at h2
    exact absurd h2 (by decide)
  have hWne : ∀ w, W w → w ≠ d i := by
    intro w hw heq
    rcases hw with hctxm | ⟨a, r, D, ha, hr, hD, rfl⟩
    · have h1 := hctx w hctxm (i + 1) (Nat.le_add_right i 1)
      rw [heq] at h1
      rw [hI.refl_eq (d i) (hdom i)] at h1
      exact hcne (hI.eq_id (d (i + 1)) (d i) (hdom (i + 1)) (hdom i) h1)
    · have hspec := (Classical.choose_spec (hserve a r D ha hr hD)).2.2
      have h0 := hspec 0 (Nat.zero_le p)
      rw [Nat.add_zero, heq] at h0
      rw [hI.refl_eq (d i) (hdom i)] at h0
      rcases hr with rfl | rfl | rfl
      · exact absurd h0 (by decide)
      · exact absurd h0 (by decide)
      · exact absurd h0 (by decide)
  refine ⟨{w : α // W w},
    { E := fun e f => I.rho e.val f.val
      K := fun _ f => I.rho (d i) f.val
      Q := fun _ _ => I.rho (d i) (d i)
      up := fun _ => false
      tauE := fun e => mty C0 I e.val
      p := fun _ => p
      phase := fun _ a => mty C0 I (d (i + a)) },
    ?_, rfl, fun _ => rfl,
    fun (e : {w : α // W w}) => ⟨e.val, hWdom e.val e.2, rfl⟩,
    fun e he => ⟨⟨e, Or.inl he⟩, rfl⟩,
    fun hpo => ⟨fun _ _ => mty_no_all_po hpo,
      fun _ a _ _ => mty_no_all_po hpo⟩⟩
  refine
    { hp := fun _ => hp
      frame_q := ?_
      e_clash := fun e a h => mty_clash h
      e_nobot := fun e => mty_nobot
      e_and := fun e c d h => mty_and h
      e_or := fun e c d h => mty_or h
      k_clash := fun k a ha n h => mty_clash h
      k_nobot := fun k a ha => mty_nobot
      k_and := fun k a ha c d h => mty_and h
      k_or := fun k a ha c d h => mty_or h
      ee_all := fun e f r E hE hr => mty_all hE (hWdom f.val f.2) hr
      ek_all := ?_
      ke_all := ?_
      kk_pp := fun k a ha E hE b hb =>
        dsegment_kk_pp hI hdom hstep hty ha hE b hb
      kk_ppi := fun k a ha E hE b hb =>
        dsegment_kk_ppi hI hdom hstep hty ha hE b hb
      kk_eq := fun k a ha E hE => seg_eq hI hdom hE
      kq_all := fun k k' hne => absurd rfl hne
      k_ex := ?_ }
  · refine readoff_qnet_frame hI
      (fun (e : {w : α // W w}) => e.val) (fun _ => d i)
      (fun (e : {w : α // W w}) => hWdom e.val e.2) (fun _ => hdom i) ?_
    intro v w hvw
    rcases v with e | u <;> rcases w with f | u'
    · exact congrArg Sum.inl (Subtype.ext hvw)
    · exact absurd hvw (hWne e.val e.2)
    · exact absurd hvw.symm (hWne f.val f.2)
    · cases u; cases u'; rfl
  · intro e r E hE k hK a ha
    have h2 : I.rho e.val (d (i + a)) = r := by
      rw [hI.conv_ (d (i + a)) e.val (hdom (i + a)) (hWdom e.val e.2),
        hWconst e.val e.2 a (Nat.le_of_lt ha)]
      exact hK
    exact mty_all hE (hdom (i + a)) h2
  · intro k a ha r E hE f hK
    have h1 : I.rho (d (i + a)) f.val = r := by
      rw [hWconst f.val f.2 a (Nat.le_of_lt ha)]
      exact hK
    exact mty_all hE (hWdom f.val f.2) h1
  · intro k a ha r E hE
    cases r with
    | dr =>
      refine Or.inl ⟨⟨Classical.choose
          (hserve a dr E (Nat.le_of_lt ha) (Or.inl rfl) hE),
        Or.inr ⟨a, dr, E, Nat.le_of_lt ha, Or.inl rfl, hE, rfl⟩⟩,
        ?_, ?_⟩
      · have hspec := (Classical.choose_spec
          (hserve a dr E (Nat.le_of_lt ha) (Or.inl rfl) hE)).2.2
        have h1 := hspec 0 (Nat.zero_le p)
        rwa [Nat.add_zero] at h1
      · exact (Classical.choose_spec
          (hserve a dr E (Nat.le_of_lt ha) (Or.inl rfl) hE)).2.1
    | pp =>
      refine Or.inl ⟨⟨Classical.choose
          (hserve a pp E (Nat.le_of_lt ha) (Or.inr (Or.inl rfl)) hE),
        Or.inr ⟨a, pp, E, Nat.le_of_lt ha, Or.inr (Or.inl rfl), hE,
          rfl⟩⟩, ?_, ?_⟩
      · have hspec := (Classical.choose_spec
          (hserve a pp E (Nat.le_of_lt ha) (Or.inr (Or.inl rfl)) hE)).2.2
        have h1 := hspec 0 (Nat.zero_le p)
        rwa [Nat.add_zero] at h1
      · exact (Classical.choose_spec
          (hserve a pp E (Nat.le_of_lt ha) (Or.inr (Or.inl rfl)) hE)).2.1
    | ppi =>
      refine Or.inl ⟨⟨Classical.choose
          (hserve a ppi E (Nat.le_of_lt ha) (Or.inr (Or.inr rfl)) hE),
        Or.inr ⟨a, ppi, E, Nat.le_of_lt ha, Or.inr (Or.inr rfl), hE,
          rfl⟩⟩, ?_, ?_⟩
      · have hspec := (Classical.choose_spec
          (hserve a ppi E (Nat.le_of_lt ha) (Or.inr (Or.inr rfl)) hE)).2.2
        have h1 := hspec 0 (Nat.zero_le p)
        rwa [Nat.add_zero] at h1
      · exact (Classical.choose_spec
          (hserve a ppi E (Nat.le_of_lt ha) (Or.inr (Or.inr rfl)) hE)).2.1
    | eq =>
      exact Or.inr (Or.inr (Or.inl ⟨rfl, seg_ex_eq hI hdom hE⟩))
    | po =>
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hpool a ha E hE⟩)))

/-- THE DESCENDING KERNEL-ATTACHMENT COROLLARY (mirror of
    `kernel_block_of_chain`). -/
theorem dkernel_block_of_chain (C0 : Concept) (myTag : Nat)
    (P : List (Nat × List Concept)) (ctx : List α)
    (hctxdom : ∀ e ∈ ctx, I.dom e) (L : Nat)
    (hpoolcl : ∀ D, Concept.ex po D ∈ cl C0 →
      ∃ q ∈ P, q.1 ≠ myTag ∧ D ∈ q.2) :
    ∃ i p, L ≤ i ∧ 0 < p ∧
      ∃ (β : Type) (T : MultiTier β Unit),
        BlockOk T myTag P ∧
        T.p () = p ∧
        (∀ a, T.phase () a = mty C0 I (d (i + a))) ∧
        (∀ e : β, ∃ x, I.dom x ∧ T.tauE e = mty C0 I x) ∧
        (∀ e ∈ ctx, ∃ eb : β, T.tauE eb = mty C0 I e) ∧
        (POFree C0 → MTNoPo T) := by
  obtain ⟨i, p, hLi, hp, hty, hctx, _, hserve⟩ :=
    dkernel_site hI hdom hstep C0 ctx hctxdom L
  exact ⟨i, p, hLi, hp, done_kernel_block hI hdom hstep C0 myTag P ctx
    hctxdom hp hty hctx hserve
    (fun a _ D hD => hpoolcl D (mty_sub _ hD))⟩

end DescOneKernelBlock

/-! ## Round E3b (2026-07-23): the ordered-disjoint frame — the mixed
frame argument for multi-kernel blocks

The certified CONVERSE of the RCC5 normal form (wp47's other
direction, at this artifact's composition table; the forward direction
is `formal/RCC5NormalForm.lean` — this closes the follow-up recorded
there): a labelling with reflexive strong `EQ` and coherent converses
whose `PP` is TRANSITIVE and whose `DR` is DOWNWARD-CLOSED along `PP`
is composition-closed — a `Frame`.  Everything else is derived: the 16
non-`EQ` composition cells split into 4 FORCED cells (`pp;pp`,
`pp;dr`, `ppi;ppi`, `dr;ppi` — closed by transitivity/downward closure
directly), 3 unconstrained cells (`pp;ppi`, `po;po`, `dr;dr`), and 9
cells whose exclusions all follow from the same two laws plus converse
coherence and strong `EQ`.

`PO` imposes NO condition — it is the residual value of the normal
form.  This is the mixed frame argument the multi-kernel block needs
(LEAN.md item 3's rectangle problem, restructured): declare TIGHT
values (model-backed, rectangle-constant) on a skeleton that is
transitively closed in `PP` and downward closed in `DR` — both
closures are model-forced through singleton composition cells
(`comp(pp,pp)={pp}`, `comp(pp,dr)={dr}`), hence automatically
rectangle-constant — and declare LOOSE `PO` everywhere else, with NO
model rectangle needed.  Frame closure is then THIS theorem; on the
Hintikka side every loose edge is inert for the fragment
(`mty_no_all_po`: no `∀PO` obligation exists to fire across it, and no
demand is ever routed through it).  The rectangle problem thus
survives only for tight values, where forcing gives constancy. -/

/-- THE ORDERED-DISJOINT FRAME: reflexive strong-`EQ` + coherent
    converses + transitive `PP` + `DR` downward-closed along `PP`
    ⟹ composition closure.  `PO` is residual — no condition. -/
theorem ordered_disjoint_frame {V : Type} (N : V → V → Atom)
    (hrefl : ∀ x, N x x = eq)
    (heqid : ∀ x y, N x y = eq → x = y)
    (hconv : ∀ x y, N y x = conv (N x y))
    (htrans : ∀ x y z, N x y = pp → N y z = pp → N x z = pp)
    (hdown : ∀ x y z, N x y = pp → N y z = dr → N x z = dr) :
    Frame N where
  refl_eq := hrefl
  eq_id := heqid
  conv_ := hconv
  comp_ := by
    intro x y z
    cases hxy : N x y with
    | eq =>
      have h := heqid x y hxy
      subst h
      exact List.Mem.head _
    | pp =>
      cases hyz : N y z with
      | eq =>
        have h := heqid y z hyz
        subst h
        rw [hxy]
        decide
      | pp =>
        rw [htrans x y z hxy hyz]
        decide
      | ppi =>
        cases N x z <;> decide
      | po =>
        cases hxz : N x z with
        | eq =>
          have h := heqid x z hxz
          subst h
          have hyx : N y x = ppi := by rw [hconv x y, hxy]; rfl
          rw [hyx] at hyz
          exact absurd hyz (by decide)
        | pp => decide
        | ppi =>
          have hzx : N z x = pp := by rw [hconv x z, hxz]; rfl
          have hzy := htrans z x y hzx hxy
          have h2 : N y z = ppi := by rw [hconv z y, hzy]; rfl
          rw [h2] at hyz
          exact absurd hyz (by decide)
        | po => decide
        | dr => decide
      | dr =>
        rw [hdown x y z hxy hyz]
        decide
    | ppi =>
      cases hyz : N y z with
      | eq =>
        have h := heqid y z hyz
        subst h
        rw [hxy]
        decide
      | pp =>
        cases hxz : N x z with
        | eq => decide
        | pp => decide
        | ppi => decide
        | po => decide
        | dr =>
          have hyx : N y x = pp := by rw [hconv x y, hxy]; rfl
          have h2 := hdown y x z hyx hxz
          rw [h2] at hyz
          exact absurd hyz (by decide)
      | ppi =>
        have hzy : N z y = pp := by rw [hconv y z, hyz]; rfl
        have hyx : N y x = pp := by rw [hconv x y, hxy]; rfl
        have hzx := htrans z y x hzy hyx
        have h4 : N x z = ppi := by rw [hconv z x, hzx]; rfl
        rw [h4]
        decide
      | po =>
        cases hxz : N x z with
        | eq =>
          have h := heqid x z hxz
          subst h
          have hyx : N y x = pp := by rw [hconv x y, hxy]; rfl
          rw [hyx] at hyz
          exact absurd hyz (by decide)
        | pp =>
          have hyx : N y x = pp := by rw [hconv x y, hxy]; rfl
          have h2 := htrans y x z hyx hxz
          rw [h2] at hyz
          exact absurd hyz (by decide)
        | ppi => decide
        | po => decide
        | dr =>
          have hyx : N y x = pp := by rw [hconv x y, hxy]; rfl
          have h2 := hdown y x z hyx hxz
          rw [h2] at hyz
          exact absurd hyz (by decide)
      | dr =>
        cases hxz : N x z with
        | eq =>
          have h := heqid x z hxz
          subst h
          have hyx : N y x = pp := by rw [hconv x y, hxy]; rfl
          rw [hyx] at hyz
          exact absurd hyz (by decide)
        | pp =>
          have hyx : N y x = pp := by rw [hconv x y, hxy]; rfl
          have h2 := htrans y x z hyx hxz
          rw [h2] at hyz
          exact absurd hyz (by decide)
        | ppi => decide
        | po => decide
        | dr => decide
    | po =>
      cases hyz : N y z with
      | eq =>
        have h := heqid y z hyz
        subst h
        rw [hxy]
        decide
      | pp =>
        cases hxz : N x z with
        | eq =>
          have h := heqid x z hxz
          subst h
          have hyx : N y x = po := by rw [hconv x y, hxy]; rfl
          rw [hyx] at hyz
          exact absurd hyz (by decide)
        | pp => decide
        | ppi =>
          have hzx : N z x = pp := by rw [hconv x z, hxz]; rfl
          have h2 := htrans y z x hyz hzx
          have h3 : N x y = ppi := by rw [hconv y x, h2]; rfl
          rw [h3] at hxy
          exact absurd hxy (by decide)
        | po => decide
        | dr =>
          have hzx : N z x = dr := by rw [hconv x z, hxz]; rfl
          have h2 := hdown y z x hyz hzx
          have h3 : N x y = dr := by rw [hconv y x, h2]; rfl
          rw [h3] at hxy
          exact absurd hxy (by decide)
      | ppi =>
        cases hxz : N x z with
        | eq =>
          have h := heqid x z hxz
          subst h
          have hyx : N y x = po := by rw [hconv x y, hxy]; rfl
          rw [hyx] at hyz
          exact absurd hyz (by decide)
        | pp =>
          have hzy : N z y = pp := by rw [hconv y z, hyz]; rfl
          have h2 := htrans x z y hxz hzy
          rw [h2] at hxy
          exact absurd hxy (by decide)
        | ppi => decide
        | po => decide
        | dr => decide
      | po =>
        cases N x z <;> decide
      | dr =>
        cases hxz : N x z with
        | eq =>
          have h := heqid x z hxz
          subst h
          have hyx : N y x = po := by rw [hconv x y, hxy]; rfl
          rw [hyx] at hyz
          exact absurd hyz (by decide)
        | pp =>
          have hzy : N z y = dr := by rw [hconv y z, hyz]; rfl
          have h2 := hdown x z y hxz hzy
          rw [h2] at hxy
          exact absurd hxy (by decide)
        | ppi => decide
        | po => decide
        | dr => decide
    | dr =>
      cases hyz : N y z with
      | eq =>
        have h := heqid y z hyz
        subst h
        rw [hxy]
        decide
      | pp =>
        cases hxz : N x z with
        | eq =>
          have h := heqid x z hxz
          subst h
          have h2 : N x y = ppi := by rw [hconv y x, hyz]; rfl
          rw [h2] at hxy
          exact absurd hxy (by decide)
        | pp => decide
        | ppi =>
          have hzx : N z x = pp := by rw [hconv x z, hxz]; rfl
          have h2 := htrans y z x hyz hzx
          have h3 : N x y = ppi := by rw [hconv y x, h2]; rfl
          rw [h3] at hxy
          exact absurd hxy (by decide)
        | po => decide
        | dr => decide
      | ppi =>
        have hzy : N z y = pp := by rw [hconv y z, hyz]; rfl
        have hyx : N y x = dr := by rw [hconv x y, hxy]; rfl
        have h3 := hdown z y x hzy hyx
        have h4 : N x z = dr := by rw [hconv z x, h3]; rfl
        rw [h4]
        decide
      | po =>
        cases hxz : N x z with
        | eq =>
          have h := heqid x z hxz
          subst h
          have h2 : N x y = po := by rw [hconv y x, hyz]; rfl
          rw [h2] at hxy
          exact absurd hxy (by decide)
        | pp => decide
        | ppi =>
          have hzx : N z x = pp := by rw [hconv x z, hxz]; rfl
          have h2 := hdown z x y hzx hxy
          have h3 : N y z = dr := by rw [hconv z y, h2]; rfl
          rw [h3] at hyz
          exact absurd hyz (by decide)
        | po => decide
        | dr => decide
      | dr =>
        cases N x z <;> decide

/-! ## Round E3c (2026-07-23): the two-sorted block labelling

`ordered_disjoint_frame` packaged as the exact tool the multi-kernel
block builder calls: a carrier of representatives, a symmetric TIGHT
relation whose model values satisfy the two closure laws, and the
labelling `EQ` on the diagonal / read-off model value on tight pairs /
loose `PO` everywhere else — a `Frame`, with the loose pairs never
consulting the model.  The closure laws' VALUE side is free (the
model's own composition runs through the singleton cells); only the
skeleton's closure under the two forcings is the builder's
obligation. -/

section TwoSorted

variable {α V : Type} {I : Interp α}

open Classical in
/-- The two-sorted block labelling: `EQ` on the diagonal, the model
    value on TIGHT pairs, loose `PO` elsewhere. -/
noncomputable def twoSorted (I : Interp α) (elt : V → α)
    (Tight : V → V → Prop) : V → V → Atom :=
  fun v w => if v = w then eq
    else if Tight v w then I.rho (elt v) (elt w) else po

/-- A non-`EQ`, non-`PO` value can only come from the tight branch. -/
theorem twoSorted_elim {elt : V → α} {Tight : V → V → Prop}
    {x y : V} {a : Atom} (hne : a ≠ eq) (hnpo : a ≠ po)
    (h : twoSorted I elt Tight x y = a) :
    x ≠ y ∧ Tight x y ∧ I.rho (elt x) (elt y) = a := by
  unfold twoSorted at h
  by_cases hxy : x = y
  · rw [if_pos hxy] at h
    exact absurd h.symm hne
  · rw [if_neg hxy] at h
    by_cases ht : Tight x y
    · rw [if_pos ht] at h
      exact ⟨hxy, ht, h⟩
    · rw [if_neg ht] at h
      exact absurd h.symm hnpo

/-- Tight off-diagonal pairs read the model. -/
theorem twoSorted_tight {elt : V → α} {Tight : V → V → Prop}
    {x y : V} (hxy : x ≠ y) (ht : Tight x y) :
    twoSorted I elt Tight x y = I.rho (elt x) (elt y) := by
  unfold twoSorted
  rw [if_neg hxy, if_pos ht]

/-- Loose off-diagonal pairs are `PO`. -/
theorem twoSorted_loose {elt : V → α} {Tight : V → V → Prop}
    {x y : V} (hxy : x ≠ y) (ht : ¬ Tight x y) :
    twoSorted I elt Tight x y = po := by
  unfold twoSorted
  rw [if_neg hxy, if_neg ht]

/-- THE TWO-SORTED FRAME: a symmetric tight skeleton closed under the
    two ordered-disjoint forcings (`PP`-transitivity, `DR` downward
    closure), with values read off the model at injective
    representatives, makes the two-sorted labelling a `Frame` — the
    loose `PO` pairs never consult the model. -/
theorem twoSorted_frame (hI : RCC5Interp I)
    (elt : V → α) (hdom : ∀ v, I.dom (elt v))
    (hinj : ∀ v w, elt v = elt w → v = w)
    (Tight : V → V → Prop)
    (hsymm : ∀ v w, Tight v w → Tight w v)
    (htpp : ∀ v w u, Tight v w → Tight w u →
      I.rho (elt v) (elt w) = pp → I.rho (elt w) (elt u) = pp →
      Tight v u)
    (htdr : ∀ v w u, Tight v w → Tight w u →
      I.rho (elt v) (elt w) = pp → I.rho (elt w) (elt u) = dr →
      Tight v u) :
    Frame (twoSorted I elt Tight) := by
  refine ordered_disjoint_frame _ ?_ ?_ ?_ ?_ ?_
  · -- reflexive EQ
    intro x
    unfold twoSorted
    rw [if_pos rfl]
  · -- strong EQ
    intro x y h
    unfold twoSorted at h
    by_cases hxy : x = y
    · exact hxy
    · rw [if_neg hxy] at h
      by_cases ht : Tight x y
      · rw [if_pos ht] at h
        exact hinj x y (hI.eq_id _ _ (hdom x) (hdom y) h)
      · rw [if_neg ht] at h
        exact absurd h (by decide)
  · -- converse coherence
    intro x y
    unfold twoSorted
    by_cases hxy : x = y
    · rw [if_pos hxy, if_pos hxy.symm]
      rfl
    · rw [if_neg hxy, if_neg (fun hh => hxy hh.symm)]
      by_cases ht : Tight x y
      · rw [if_pos ht, if_pos (hsymm x y ht)]
        exact hI.conv_ _ _ (hdom x) (hdom y)
      · rw [if_neg ht, if_neg (fun hh => ht (hsymm y x hh))]
        rfl
  · -- PP-transitivity
    intro x y z h1 h2
    obtain ⟨hxy, ht1, hr1⟩ := twoSorted_elim (by decide) (by decide) h1
    obtain ⟨hyz, ht2, hr2⟩ := twoSorted_elim (by decide) (by decide) h2
    have hxz : x ≠ z := by
      intro hh
      subst hh
      have hc := hI.conv_ (elt x) (elt y) (hdom x) (hdom y)
      rw [hr1, hr2] at hc
      exact absurd hc (by decide)
    have htz := htpp x y z ht1 ht2 hr1 hr2
    have hval : I.rho (elt x) (elt z) = pp := by
      have hm := hI.comp_ (elt x) (elt y) (elt z) (hdom x) (hdom y)
        (hdom z)
      rw [hr1, hr2] at hm
      exact List.mem_singleton.mp hm
    rw [twoSorted_tight hxz htz, hval]
  · -- DR downward closure
    intro x y z h1 h2
    obtain ⟨hxy, ht1, hr1⟩ := twoSorted_elim (by decide) (by decide) h1
    obtain ⟨hyz, ht2, hr2⟩ := twoSorted_elim (by decide) (by decide) h2
    have hxz : x ≠ z := by
      intro hh
      subst hh
      have hc := hI.conv_ (elt x) (elt y) (hdom x) (hdom y)
      rw [hr1, hr2] at hc
      exact absurd hc (by decide)
    have htz := htdr x y z ht1 ht2 hr1 hr2
    have hval : I.rho (elt x) (elt z) = dr := by
      have hm := hI.comp_ (elt x) (elt y) (elt z) (hdom x) (hdom y)
        (hdom z)
      rw [hr1, hr2] at hm
      exact List.mem_singleton.mp hm
    rw [twoSorted_tight hxz htz, hval]

end TwoSorted

/-! ## Round E3d (2026-07-23): the multi-kernel block

The kernel-attachment layer generalized to ANY family of kernels over
the two-sorted discipline.  `mkBlock` declares every certificate value
through `twoSorted` on `β ⊕ κ` (externals ⊕ kernels, kernel
representative = segment base): `EQ` diagonal, model read-off on the
TIGHT skeleton, loose `PO` elsewhere.  `multi_kernel_block` proves
`BlockOk` from exactly the builder's obligations:

  * the tight skeleton is symmetric and closed under the two
    ordered-disjoint forcings (E3c's `twoSorted_frame` gives
    `frame_q` through the `qnet` bridge `frame_ext`);
  * tight values touching kernels are RECTANGLE-CONSTANT (`hrectK`
    row constancy across the segment, `hrectQ` on kernel pairs) — the
    ∀-side then fires through `mty_all`; LOOSE `PO` edges fire only
    `∀PO` obligations, which the fragment does not have
    (`mty_no_all_po` — this is where `POFree C0` becomes a hypothesis
    of the block layer, unlike the all-read-off one-kernel case);
  * each kernel's `DR`/`PP`/`PPI` demands have TIGHT designated
    witnesses among the externals (`hserve`); `EQ` demands are
    in-phase, `PO` demands pend against the pool.

Chains carry their direction uniformly (`hstep` in `cdir` form);
segment coherence dispatches per direction to the E2a/E2a′ duals. -/

section MultiKernelBlock

variable {α : Type} {I : Interp α} {β κ : Type} [DecidableEq κ]

/-- The block's representative map: externals to their elements,
    kernels to their segment bases. -/
def blockElt (eltE : β → α) (ck : κ → Nat → α) (ik : κ → Nat) :
    (β ⊕ κ) → α :=
  Sum.elim eltE (fun k => ck k (ik k))

/-- Full case analysis of a two-sorted value. -/
theorem twoSorted_cases {V : Type} {elt : V → α} {Tight : V → V → Prop}
    {x y : V} {a : Atom} (h : twoSorted I elt Tight x y = a) :
    (x = y ∧ a = eq) ∨
    (x ≠ y ∧ Tight x y ∧ I.rho (elt x) (elt y) = a) ∨
    (x ≠ y ∧ ¬ Tight x y ∧ a = po) := by
  unfold twoSorted at h
  by_cases hxy : x = y
  · rw [if_pos hxy] at h
    exact Or.inl ⟨hxy, h.symm⟩
  · rw [if_neg hxy] at h
    by_cases ht : Tight x y
    · rw [if_pos ht] at h
      exact Or.inr (Or.inl ⟨hxy, ht, h⟩)
    · rw [if_neg ht] at h
      exact Or.inr (Or.inr ⟨hxy, ht, h.symm⟩)

open Classical in
/-- THE MULTI-KERNEL BLOCK: every value declared through the
    two-sorted labelling over externals ⊕ kernels; phases are the
    segments' model types. -/
noncomputable def mkBlock (I : Interp α) (C0 : Concept) (eltE : β → α)
    (ck : κ → Nat → α) (upf : κ → Bool) (ik pk : κ → Nat)
    (Tight : (β ⊕ κ) → (β ⊕ κ) → Prop) : MultiTier β κ where
  E e f := twoSorted I (blockElt eltE ck ik) Tight (.inl e) (.inl f)
  K k f := twoSorted I (blockElt eltE ck ik) Tight (.inr k) (.inl f)
  Q k k' := twoSorted I (blockElt eltE ck ik) Tight (.inr k) (.inr k')
  up := upf
  tauE e := mty C0 I (eltE e)
  p := pk
  phase k a := mty C0 I (ck k (ik k + a))

omit [DecidableEq κ] in
/-- The fragment's vacuity holds on any `mkBlock`. -/
theorem mkBlock_nopo {C0 : Concept} (hpo : POFree C0) {eltE : β → α}
    {ck : κ → Nat → α} {upf : κ → Bool} {ik pk : κ → Nat}
    {Tight : (β ⊕ κ) → (β ⊕ κ) → Prop} :
    MTNoPo (mkBlock I C0 eltE ck upf ik pk Tight) where
  ext := fun _ _ => mty_no_all_po hpo
  ker := fun _ _ _ _ => mty_no_all_po hpo

/-- THE MULTI-KERNEL BLOCK THEOREM: the two-sorted declaration
    discipline + rectangle constancy of tight kernel values + tight
    designated witnesses + pool coverage give kernel-side validity
    (`BlockOk`) for ANY family of directed kernels. -/
theorem multi_kernel_block (hI : RCC5Interp I) (C0 : Concept)
    (hpo : POFree C0) (myTag : Nat) (P : List (Nat × List Concept))
    (eltE : β → α) (ck : κ → Nat → α) (upf : κ → Bool) (ik pk : κ → Nat)
    (Tight : (β ⊕ κ) → (β ⊕ κ) → Prop)
    (hdomE : ∀ e, I.dom (eltE e))
    (hdomc : ∀ k m, I.dom (ck k m))
    (hstep : ∀ k m, I.rho (ck k m) (ck k (m + 1)) = cdir (upf k))
    (hp : ∀ k, 0 < pk k)
    (hty : ∀ k, mty C0 I (ck k (ik k)) = mty C0 I (ck k (ik k + pk k)))
    (hinj : ∀ v w : β ⊕ κ,
      blockElt eltE ck ik v = blockElt eltE ck ik w → v = w)
    (hsymm : ∀ v w, Tight v w → Tight w v)
    (htpp : ∀ v w u, Tight v w → Tight w u →
      I.rho (blockElt eltE ck ik v) (blockElt eltE ck ik w) = pp →
      I.rho (blockElt eltE ck ik w) (blockElt eltE ck ik u) = pp →
      Tight v u)
    (htdr : ∀ v w u, Tight v w → Tight w u →
      I.rho (blockElt eltE ck ik v) (blockElt eltE ck ik w) = pp →
      I.rho (blockElt eltE ck ik w) (blockElt eltE ck ik u) = dr →
      Tight v u)
    (hrectK : ∀ k e, Tight (.inr k) (.inl e) → ∀ a, a ≤ pk k →
      I.rho (ck k (ik k + a)) (eltE e) = I.rho (ck k (ik k)) (eltE e))
    (hrectQ : ∀ k k', k ≠ k' → Tight (.inr k) (.inr k') →
      ∀ a b, a ≤ pk k → b ≤ pk k' →
      I.rho (ck k (ik k + a)) (ck k' (ik k' + b))
        = I.rho (ck k (ik k)) (ck k' (ik k')))
    (hserve : ∀ k a r D, a < pk k → (r = dr ∨ r = pp ∨ r = ppi) →
      Concept.ex r D ∈ mty C0 I (ck k (ik k + a)) →
      ∃ e : β, Tight (.inr k) (.inl e) ∧
        I.rho (ck k (ik k)) (eltE e) = r ∧ D ∈ mty C0 I (eltE e))
    (hpool : ∀ k a, a < pk k → ∀ D,
      Concept.ex po D ∈ mty C0 I (ck k (ik k + a)) →
      ∃ q ∈ P, q.1 ≠ myTag ∧ D ∈ q.2) :
    BlockOk (mkBlock I C0 eltE ck upf ik pk Tight) myTag P := by
  have hdomV : ∀ v : β ⊕ κ, I.dom (blockElt eltE ck ik v) := by
    intro v
    rcases v with e | k
    · exact hdomE e
    · exact hdomc k (ik k)
  have hF : Frame (twoSorted I (blockElt eltE ck ik) Tight) :=
    twoSorted_frame hI (blockElt eltE ck ik) hdomV hinj Tight
      hsymm htpp htdr
  refine
    { hp := hp
      frame_q := ?_
      e_clash := fun e a h => mty_clash h
      e_nobot := fun e => mty_nobot
      e_and := fun e c d h => mty_and h
      e_or := fun e c d h => mty_or h
      k_clash := fun k a ha n h => mty_clash h
      k_nobot := fun k a ha => mty_nobot
      k_and := fun k a ha c d h => mty_and h
      k_or := fun k a ha c d h => mty_or h
      ee_all := ?_
      ek_all := ?_
      ke_all := ?_
      kk_pp := ?_
      kk_ppi := ?_
      kk_eq := fun k a ha E hE => seg_eq hI (fun m => hdomc k m) hE
      kq_all := ?_
      k_ex := ?_ }
  · -- frame_q: the qnet bridge to the two-sorted frame
    refine frame_ext (fun x y => ?_) hF
    rcases x with e | k <;> rcases y with f | k'
    · rfl
    · exact hF.conv_ (.inr k') (.inl e)
    · rfl
    · by_cases hkk : k = k'
      · subst hkk
        show twoSorted I (blockElt eltE ck ik) Tight (.inr k) (.inr k)
          = if k = k then eq
            else (mkBlock I C0 eltE ck upf ik pk Tight).Q k k
        rw [if_pos rfl]
        unfold twoSorted
        rw [if_pos rfl]
      · show twoSorted I (blockElt eltE ck ik) Tight (.inr k) (.inr k')
          = if k = k' then eq
            else (mkBlock I C0 eltE ck upf ik pk Tight).Q k k'
        rw [if_neg hkk]
        rfl
  · -- ee_all
    intro e f r E hE hr
    have hr' : twoSorted I (blockElt eltE ck ik) Tight
        (.inl e) (.inl f) = r := hr
    rcases twoSorted_cases hr' with ⟨hxy, rfl⟩ | ⟨_, _, hval⟩ |
      ⟨_, _, rfl⟩
    · have hef : e = f := Sum.inl.inj hxy
      subst hef
      exact mty_all hE (hdomE e) (hI.refl_eq (eltE e) (hdomE e))
    · have hval' : I.rho (eltE e) (eltE f) = r := hval
      exact mty_all hE (hdomE f) hval'
    · exact absurd hE (mty_no_all_po hpo)
  · -- ek_all
    intro e r E hE k hK a ha
    have hK2 : twoSorted I (blockElt eltE ck ik) Tight
        (.inr k) (.inl e) = conv r := by
      have hK' : conv (twoSorted I (blockElt eltE ck ik) Tight
          (.inr k) (.inl e)) = r := hK
      rw [← hK']
      exact (conv_invol _).symm
    rcases twoSorted_cases hK2 with ⟨hxy, _⟩ | ⟨_, ht, hval⟩ |
      ⟨_, _, hcr⟩
    · exact nomatch hxy
    · have hval' : I.rho (ck k (ik k)) (eltE e) = conv r := hval
      have hedge : I.rho (eltE e) (ck k (ik k + a)) = r := by
        rw [hI.conv_ (ck k (ik k + a)) (eltE e) (hdomc k _) (hdomE e),
          hrectK k e ht a (Nat.le_of_lt ha), hval']
        exact conv_invol r
      exact mty_all hE (hdomc k (ik k + a)) hedge
    · have hr : r = po := by
        rw [← conv_invol r, hcr]
        rfl
      subst hr
      exact absurd hE (mty_no_all_po hpo)
  · -- ke_all
    intro k a ha r E hE f hK
    have hK' : twoSorted I (blockElt eltE ck ik) Tight
        (.inr k) (.inl f) = r := hK
    rcases twoSorted_cases hK' with ⟨hxy, _⟩ | ⟨_, ht, hval⟩ |
      ⟨_, _, rfl⟩
    · exact nomatch hxy
    · have hval' : I.rho (ck k (ik k)) (eltE f) = r := hval
      have hedge : I.rho (ck k (ik k + a)) (eltE f) = r := by
        rw [hrectK k f ht a (Nat.le_of_lt ha)]
        exact hval'
      exact mty_all hE (hdomE f) hedge
    · exact absurd hE (mty_no_all_po hpo)
  · -- kk_pp: per-direction segment coherence
    intro k a ha E hE b hb
    cases hu : upf k with
    | true =>
      have hstep' : ∀ m, I.rho (ck k m) (ck k (m + 1)) = pp := by
        intro m
        have h := hstep k m
        rw [hu] at h
        exact h
      exact segment_kk_pp hI (fun m => hdomc k m) hstep' (hty k)
        ha hE b hb
    | false =>
      have hstep' : ∀ m, I.rho (ck k m) (ck k (m + 1)) = ppi := by
        intro m
        have h := hstep k m
        rw [hu] at h
        exact h
      exact dsegment_kk_pp hI (fun m => hdomc k m) hstep' (hty k)
        ha hE b hb
  · -- kk_ppi
    intro k a ha E hE b hb
    cases hu : upf k with
    | true =>
      have hstep' : ∀ m, I.rho (ck k m) (ck k (m + 1)) = pp := by
        intro m
        have h := hstep k m
        rw [hu] at h
        exact h
      exact segment_kk_ppi hI (fun m => hdomc k m) hstep' (hty k)
        ha hE b hb
    | false =>
      have hstep' : ∀ m, I.rho (ck k m) (ck k (m + 1)) = ppi := by
        intro m
        have h := hstep k m
        rw [hu] at h
        exact h
      exact dsegment_kk_ppi hI (fun m => hdomc k m) hstep' (hty k)
        ha hE b hb
  · -- kq_all
    intro k k' hkk a ha r E hE hQ b hb
    have hQ' : twoSorted I (blockElt eltE ck ik) Tight
        (.inr k) (.inr k') = r := hQ
    rcases twoSorted_cases hQ' with ⟨hxy, _⟩ | ⟨_, ht, hval⟩ |
      ⟨_, _, rfl⟩
    · exact absurd (Sum.inr.inj hxy) hkk
    · have hval' : I.rho (ck k (ik k)) (ck k' (ik k')) = r := hval
      have hedge : I.rho (ck k (ik k + a)) (ck k' (ik k' + b)) = r := by
        rw [hrectQ k k' hkk ht a b (Nat.le_of_lt ha) (Nat.le_of_lt hb)]
        exact hval'
      exact mty_all hE (hdomc k' (ik k' + b)) hedge
    · exact absurd hE (mty_no_all_po hpo)
  · -- k_ex: demands routed by relation
    intro k a ha r E hE
    cases r with
    | dr =>
      obtain ⟨e, ht, hrow, hD⟩ := hserve k a dr E ha (Or.inl rfl) hE
      refine Or.inl ⟨e, ?_, hD⟩
      have h2 := twoSorted_tight (I := I) (elt := blockElt eltE ck ik)
        (x := Sum.inr k) (y := Sum.inl e)
        nofun ht
      have h3 : I.rho (blockElt eltE ck ik (Sum.inr k))
          (blockElt eltE ck ik (Sum.inl e)) = dr := hrow
      exact h2.trans h3
    | pp =>
      obtain ⟨e, ht, hrow, hD⟩ :=
        hserve k a pp E ha (Or.inr (Or.inl rfl)) hE
      refine Or.inl ⟨e, ?_, hD⟩
      have h2 := twoSorted_tight (I := I) (elt := blockElt eltE ck ik)
        (x := Sum.inr k) (y := Sum.inl e)
        nofun ht
      have h3 : I.rho (blockElt eltE ck ik (Sum.inr k))
          (blockElt eltE ck ik (Sum.inl e)) = pp := hrow
      exact h2.trans h3
    | ppi =>
      obtain ⟨e, ht, hrow, hD⟩ :=
        hserve k a ppi E ha (Or.inr (Or.inr rfl)) hE
      refine Or.inl ⟨e, ?_, hD⟩
      have h2 := twoSorted_tight (I := I) (elt := blockElt eltE ck ik)
        (x := Sum.inr k) (y := Sum.inl e)
        nofun ht
      have h3 : I.rho (blockElt eltE ck ik (Sum.inr k))
          (blockElt eltE ck ik (Sum.inl e)) = ppi := hrow
      exact h2.trans h3
    | eq =>
      exact Or.inr (Or.inr (Or.inl
        ⟨rfl, seg_ex_eq hI (fun m => hdomc k m) hE⟩))
    | po =>
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hpool k a ha E hE⟩)))

end MultiKernelBlock

/-! ## Round E3e (2026-07-23): the maximal read-off tight predicate

The two CLOSURE hypotheses of `multi_kernel_block` (`htpp`/`htdr`) are
dischargeable: for the MAXIMAL tight predicate `Tight v w := ρ ≠ PO`
they follow PURELY from the composition table (`comp(pp,pp)={pp}`,
`comp(pp,dr)={dr}` — the two singleton cells), independent of any
demand structure; `hsymm` is converse coherence + `conv PO = PO`.
Under this predicate the two-sorted labelling COLLAPSES to the plain
read-off (`twoSorted_eq_readoff`): every off-diagonal `PO` pair is
loose (`= PO`), every non-`PO` pair reads the model, and the diagonal
is `EQ` by reflexivity — so `twoSorted I elt (≠PO) = ρ` pointwise.

This isolates the algebraic core every instantiation reuses: the
closure obligation is SATISFIABLE, and the residual work is entirely
the RECTANGLE-CONSTANCY side (`hrectK`/`hrectQ`).  A concrete assembly
uses a SUB-predicate of `≠PO` (to make varying cross-kernel pairs
loose so their rectangle obligation is vacuous), and must re-verify
closure for it — but the comp facts are the same, so this is the
reusable half. -/

section ReadOffTight

variable {α V : Type} (I : Interp α) (elt : V → α)

/-- The maximal tight predicate: every non-`PO` model pair is tight. -/
def tightNePo : V → V → Prop := fun v w => I.rho (elt v) (elt w) ≠ po

/-- `conv` fixes only `PO` — so a non-`PO` value stays non-`PO`. -/
theorem conv_ne_po {a : Atom} (h : a ≠ po) : conv a ≠ po := by
  cases a <;> first | exact absurd rfl h | decide

variable {I elt}

/-- `≠PO` is symmetric (converse coherence + `conv PO = PO`). -/
theorem tightNePo_symm (hI : RCC5Interp I) (hdom : ∀ v, I.dom (elt v))
    (v w : V) (h : tightNePo I elt v w) : tightNePo I elt w v := by
  unfold tightNePo at h ⊢
  rw [hI.conv_ (elt v) (elt w) (hdom v) (hdom w)]
  exact conv_ne_po h

/-- `≠PO` is `PP`-transitively closed: `comp(pp,pp)={pp}`. -/
theorem tightNePo_htpp (hI : RCC5Interp I) (hdom : ∀ v, I.dom (elt v))
    (v w u : V)
    (hr1 : I.rho (elt v) (elt w) = pp) (hr2 : I.rho (elt w) (elt u) = pp) :
    tightNePo I elt v u := by
  unfold tightNePo
  have hm := hI.comp_ (elt v) (elt w) (elt u) (hdom v) (hdom w) (hdom u)
  rw [hr1, hr2] at hm
  rw [List.mem_singleton.mp hm]
  decide

/-- `≠PO` is `DR`-downward closed: `comp(pp,dr)={dr}`. -/
theorem tightNePo_htdr (hI : RCC5Interp I) (hdom : ∀ v, I.dom (elt v))
    (v w u : V)
    (hr1 : I.rho (elt v) (elt w) = pp) (hr2 : I.rho (elt w) (elt u) = dr) :
    tightNePo I elt v u := by
  unfold tightNePo
  have hm := hI.comp_ (elt v) (elt w) (elt u) (hdom v) (hdom w) (hdom u)
  rw [hr1, hr2] at hm
  rw [List.mem_singleton.mp hm]
  decide

/-- Under the maximal tight predicate the two-sorted labelling IS the
    plain read-off. -/
theorem twoSorted_eq_readoff (hI : RCC5Interp I)
    (hdom : ∀ v, I.dom (elt v)) (x y : V) :
    twoSorted I elt (tightNePo I elt) x y = I.rho (elt x) (elt y) := by
  unfold twoSorted tightNePo
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, hI.refl_eq (elt x) (hdom x)]
  · rw [if_neg hxy]
    by_cases hpo : I.rho (elt x) (elt y) = po
    · rw [if_neg (by rw [hpo]; exact fun h => h rfl), hpo]
    · rw [if_pos hpo]

end ReadOffTight

/-! ## Round E3f (2026-07-23): the general block fires from a real chain

The integration checkpoint: `multi_kernel_block` (E3d) instantiated at
`κ = Unit` with the maximal read-off predicate (E3e), fed from an
ascending `kernel_site` (E2b) — every hypothesis of the general
multi-kernel theorem DISCHARGED from an actual model chain.  This
proves the theorem's hypothesis bundle is JOINTLY SATISFIABLE (not
vacuously so — the recurring defect class this project's reviews kept
finding), and gives the `kernel_site ⟹ mkBlock ⟹ BlockOk` bridge the
multi-cluster assembly generalizes.  `hrectQ` is vacuous (no distinct
`Unit` kernels), `htpp`/`htdr`/`hsymm` come from E3e, `hrectK`/`hserve`
from the site's constant witness/context rows. -/

section BlockFromSite

variable {α : Type} {I : Interp α}

/-- THE GENERAL BLOCK FROM A SITE: an ascending kernel site yields a
    `BlockOk` for `mkBlock` at `κ = Unit`, via `multi_kernel_block` —
    the general multi-kernel theorem's first end-to-end instance. -/
theorem multiBlock_of_site (hI : RCC5Interp I)
    {c : Nat → α} (hdom : ∀ i, I.dom (c i))
    (hstep : ∀ i, I.rho (c i) (c (i + 1)) = pp)
    (C0 : Concept) (hpo : POFree C0) (myTag : Nat)
    (P : List (Nat × List Concept)) (ctx : List α)
    (hctxdom : ∀ e ∈ ctx, I.dom e)
    {i p : Nat} (hp : 0 < p)
    (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    (hctx : ∀ e ∈ ctx, ∀ m, i ≤ m → I.rho (c m) e = I.rho (c i) e)
    (hserve : ∀ a r D, a ≤ p → (r = dr ∨ r = pp ∨ r = ppi) →
      Concept.ex r D ∈ mty C0 I (c (i + a)) →
      ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
        ∀ b, b ≤ p → I.rho (c (i + b)) w = r)
    (hpool : ∀ a, a < p → ∀ D, Concept.ex po D ∈ mty C0 I (c (i + a)) →
      ∃ q ∈ P, q.1 ≠ myTag ∧ D ∈ q.2) :
    ∃ (β : Type) (T : MultiTier β Unit),
      BlockOk T myTag P ∧ T.p () = p ∧
      (∀ a, T.phase () a = mty C0 I (c (i + a))) ∧
      (POFree C0 → MTNoPo T) := by
  classical
  -- the external predicate: context elements and designated witnesses
  let W : α → Prop := fun w => w ∈ ctx ∨
    ∃ a r D, ∃ (ha : a ≤ p) (hr : r = dr ∨ r = pp ∨ r = ppi)
      (hD : Concept.ex r D ∈ mty C0 I (c (i + a))),
      w = Classical.choose (hserve a r D ha hr hD)
  have hWdom : ∀ w, W w → I.dom w := by
    intro w hw
    rcases hw with hctxm | ⟨a, r, D, ha, hr, hD, rfl⟩
    · exact hctxdom w hctxm
    · exact (Classical.choose_spec (hserve a r D ha hr hD)).1
  have hWconst : ∀ w, W w → ∀ b, b ≤ p →
      I.rho (c (i + b)) w = I.rho (c i) w := by
    intro w hw b hb
    rcases hw with hctxm | ⟨a, r, D, ha, hr, hD, rfl⟩
    · exact hctx w hctxm (i + b) (Nat.le_add_right i b)
    · have hspec := (Classical.choose_spec (hserve a r D ha hr hD)).2.2
      have h0 : I.rho (c i)
          (Classical.choose (hserve a r D ha hr hD)) = r := by
        have h1 := hspec 0 (Nat.zero_le p)
        rwa [Nat.add_zero] at h1
      rw [hspec b hb, h0]
  have hcne : c (i + 1) ≠ c i := by
    intro hcc
    have h1 := hstep i
    rw [hcc, hI.refl_eq (c i) (hdom i)] at h1
    exact absurd h1 (by decide)
  have hWne : ∀ w, W w → w ≠ c i := by
    intro w hw heq
    rcases hw with hctxm | ⟨a, r, D, ha, hr, hD, rfl⟩
    · have h1 := hctx w hctxm (i + 1) (Nat.le_add_right i 1)
      rw [heq, hI.refl_eq (c i) (hdom i)] at h1
      exact hcne (hI.eq_id (c (i + 1)) (c i) (hdom (i + 1)) (hdom i) h1)
    · have hspec := (Classical.choose_spec (hserve a r D ha hr hD)).2.2
      have h0 := hspec 0 (Nat.zero_le p)
      rw [Nat.add_zero, heq, hI.refl_eq (c i) (hdom i)] at h0
      rcases hr with rfl | rfl | rfl <;> exact absurd h0 (by decide)
  -- the block data
  let β := {w : α // W w}
  let eltE : β → α := Subtype.val
  let ck : Unit → Nat → α := fun _ m => c m
  let ik : Unit → Nat := fun _ => i
  let pk : Unit → Nat := fun _ => p
  let elt : β ⊕ Unit → α := blockElt eltE ck ik
  have heltE : ∀ e : β, elt (.inl e) = e.val := fun _ => rfl
  have heltK : ∀ u : Unit, elt (.inr u) = c i := fun _ => rfl
  have hdomV : ∀ v : β ⊕ Unit, I.dom (elt v) := by
    intro v; rcases v with e | u
    · exact hWdom e.val e.2
    · exact hdom i
  have hinj : ∀ v w : β ⊕ Unit, elt v = elt w → v = w := by
    intro v w hvw
    rcases v with e | u <;> rcases w with f | u'
    · exact congrArg Sum.inl (Subtype.ext hvw)
    · exact absurd hvw (hWne e.val e.2)
    · exact absurd hvw.symm (hWne f.val f.2)
    · cases u; cases u'; rfl
  refine ⟨β, mkBlock I C0 eltE ck (fun _ => true) ik pk
    (tightNePo I elt), ?_, rfl, fun _ => rfl, fun hpo' => mkBlock_nopo hpo'⟩
  refine multi_kernel_block hI C0 hpo myTag P eltE ck (fun _ => true)
    ik pk (tightNePo I elt)
    (fun e => hWdom e.val e.2) (fun _ m => hdom m)
    (fun _ m => hstep m) (fun _ => hp) (fun _ => hty) hinj
    (tightNePo_symm hI hdomV)
    (fun v w u _ _ h1 h2 => tightNePo_htpp hI hdomV v w u h1 h2)
    (fun v w u _ _ h1 h2 => tightNePo_htdr hI hdomV v w u h1 h2)
    -- hrectK: kernel-to-external rows are constant (site)
    (fun _ e _ a ha => hWconst e.val e.2 a ha)
    -- hrectQ: no distinct Unit kernels
    (fun k k' hkk => absurd (by cases k; cases k'; rfl) hkk)
    ?_
    -- hpool: PO demands pend against the pool
    (fun _ a ha D hD => hpool a ha D hD)
  · -- hserve: designated witnesses are tight with the demanded row
    intro _ a r D ha hr hD
    have hchosen : W (Classical.choose (hserve a r D (Nat.le_of_lt ha) hr hD)) :=
      Or.inr ⟨a, r, D, Nat.le_of_lt ha, hr, hD, rfl⟩
    have hspec := (Classical.choose_spec (hserve a r D (Nat.le_of_lt ha) hr hD))
    have hrow : I.rho (c i)
        (Classical.choose (hserve a r D (Nat.le_of_lt ha) hr hD)) = r := by
      have h1 := hspec.2.2 0 (Nat.zero_le p)
      rwa [Nat.add_zero] at h1
    refine ⟨⟨_, hchosen⟩, ?_, hrow, hspec.2.1⟩
    have hedge : I.rho (elt (.inr ()))
        (elt (.inl (⟨_, hchosen⟩ : β))) = r := hrow
    show tightNePo I elt (.inr ()) (.inl ⟨_, hchosen⟩)
    unfold tightNePo
    rw [hedge]
    rcases hr with rfl | rfl | rfl <;> decide

/-- THE GENERAL BLOCK FROM A CHAIN: every ascending model chain
    carries, past any bound, a `BlockOk` built by `mkBlock` through the
    general multi-kernel theorem — the pipeline `chain ⟹ kernel_site
    ⟹ multi_kernel_block` end-to-end. -/
theorem multiBlock_of_chain (hI : RCC5Interp I)
    {c : Nat → α} (hdom : ∀ i, I.dom (c i))
    (hstep : ∀ i, I.rho (c i) (c (i + 1)) = pp)
    (C0 : Concept) (hpo : POFree C0) (myTag : Nat)
    (P : List (Nat × List Concept)) (ctx : List α)
    (hctxdom : ∀ e ∈ ctx, I.dom e) (L : Nat)
    (hpoolcl : ∀ D, Concept.ex po D ∈ cl C0 →
      ∃ q ∈ P, q.1 ≠ myTag ∧ D ∈ q.2) :
    ∃ i p, L ≤ i ∧ 0 < p ∧
      ∃ (β : Type) (T : MultiTier β Unit),
        BlockOk T myTag P ∧ T.p () = p ∧
        (∀ a, T.phase () a = mty C0 I (c (i + a))) ∧
        (POFree C0 → MTNoPo T) := by
  obtain ⟨i, p, hLi, hp, hty, hctx, _, hserve⟩ :=
    kernel_site hI hdom hstep C0 ctx hctxdom L
  exact ⟨i, p, hLi, hp, multiBlock_of_site hI hdom hstep C0 hpo myTag P
    ctx hctxdom hp hty hctx hserve
    (fun a _ D hD => hpoolcl D (mty_sub _ hD))⟩

/-- THE DESCENDING GENERAL BLOCK FROM A SITE (mirror of
    `multiBlock_of_site`): a descending kernel site yields a `BlockOk`
    for `mkBlock` at `κ = Unit`, `up = false`, via `multi_kernel_block`. -/
theorem dmultiBlock_of_site (hI : RCC5Interp I)
    {d : Nat → α} (hdom : ∀ i, I.dom (d i))
    (hstep : ∀ i, I.rho (d i) (d (i + 1)) = ppi)
    (C0 : Concept) (hpo : POFree C0) (myTag : Nat)
    (P : List (Nat × List Concept)) (ctx : List α)
    (hctxdom : ∀ e ∈ ctx, I.dom e)
    {i p : Nat} (hp : 0 < p)
    (hty : mty C0 I (d i) = mty C0 I (d (i + p)))
    (hctx : ∀ e ∈ ctx, ∀ m, i ≤ m → I.rho (d m) e = I.rho (d i) e)
    (hserve : ∀ a r D, a ≤ p → (r = dr ∨ r = pp ∨ r = ppi) →
      Concept.ex r D ∈ mty C0 I (d (i + a)) →
      ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
        ∀ b, b ≤ p → I.rho (d (i + b)) w = r)
    (hpool : ∀ a, a < p → ∀ D, Concept.ex po D ∈ mty C0 I (d (i + a)) →
      ∃ q ∈ P, q.1 ≠ myTag ∧ D ∈ q.2) :
    ∃ (β : Type) (T : MultiTier β Unit),
      BlockOk T myTag P ∧ T.p () = p ∧
      (∀ a, T.phase () a = mty C0 I (d (i + a))) ∧
      (POFree C0 → MTNoPo T) := by
  classical
  let W : α → Prop := fun w => w ∈ ctx ∨
    ∃ a r D, ∃ (ha : a ≤ p) (hr : r = dr ∨ r = pp ∨ r = ppi)
      (hD : Concept.ex r D ∈ mty C0 I (d (i + a))),
      w = Classical.choose (hserve a r D ha hr hD)
  have hWdom : ∀ w, W w → I.dom w := by
    intro w hw
    rcases hw with hctxm | ⟨a, r, D, ha, hr, hD, rfl⟩
    · exact hctxdom w hctxm
    · exact (Classical.choose_spec (hserve a r D ha hr hD)).1
  have hWconst : ∀ w, W w → ∀ b, b ≤ p →
      I.rho (d (i + b)) w = I.rho (d i) w := by
    intro w hw b hb
    rcases hw with hctxm | ⟨a, r, D, ha, hr, hD, rfl⟩
    · exact hctx w hctxm (i + b) (Nat.le_add_right i b)
    · have hspec := (Classical.choose_spec (hserve a r D ha hr hD)).2.2
      have h0 : I.rho (d i)
          (Classical.choose (hserve a r D ha hr hD)) = r := by
        have h1 := hspec 0 (Nat.zero_le p)
        rwa [Nat.add_zero] at h1
      rw [hspec b hb, h0]
  have hcne : d (i + 1) ≠ d i := by
    intro hcc
    have h1 := hstep i
    rw [hcc, hI.refl_eq (d i) (hdom i)] at h1
    exact absurd h1 (by decide)
  have hWne : ∀ w, W w → w ≠ d i := by
    intro w hw heq
    rcases hw with hctxm | ⟨a, r, D, ha, hr, hD, rfl⟩
    · have h1 := hctx w hctxm (i + 1) (Nat.le_add_right i 1)
      rw [heq, hI.refl_eq (d i) (hdom i)] at h1
      exact hcne (hI.eq_id (d (i + 1)) (d i) (hdom (i + 1)) (hdom i) h1)
    · have hspec := (Classical.choose_spec (hserve a r D ha hr hD)).2.2
      have h0 := hspec 0 (Nat.zero_le p)
      rw [Nat.add_zero, heq, hI.refl_eq (d i) (hdom i)] at h0
      rcases hr with rfl | rfl | rfl <;> exact absurd h0 (by decide)
  let β := {w : α // W w}
  let eltE : β → α := Subtype.val
  let ck : Unit → Nat → α := fun _ m => d m
  let ik : Unit → Nat := fun _ => i
  let pk : Unit → Nat := fun _ => p
  let elt : β ⊕ Unit → α := blockElt eltE ck ik
  have hdomV : ∀ v : β ⊕ Unit, I.dom (elt v) := by
    intro v; rcases v with e | u
    · exact hWdom e.val e.2
    · exact hdom i
  have hinj : ∀ v w : β ⊕ Unit, elt v = elt w → v = w := by
    intro v w hvw
    rcases v with e | u <;> rcases w with f | u'
    · exact congrArg Sum.inl (Subtype.ext hvw)
    · exact absurd hvw (hWne e.val e.2)
    · exact absurd hvw.symm (hWne f.val f.2)
    · cases u; cases u'; rfl
  refine ⟨β, mkBlock I C0 eltE ck (fun _ => false) ik pk
    (tightNePo I elt), ?_, rfl, fun _ => rfl, fun hpo' => mkBlock_nopo hpo'⟩
  refine multi_kernel_block hI C0 hpo myTag P eltE ck (fun _ => false)
    ik pk (tightNePo I elt)
    (fun e => hWdom e.val e.2) (fun _ m => hdom m)
    (fun _ m => hstep m) (fun _ => hp) (fun _ => hty) hinj
    (tightNePo_symm hI hdomV)
    (fun v w u _ _ h1 h2 => tightNePo_htpp hI hdomV v w u h1 h2)
    (fun v w u _ _ h1 h2 => tightNePo_htdr hI hdomV v w u h1 h2)
    (fun _ e _ a ha => hWconst e.val e.2 a ha)
    (fun k k' hkk => absurd (by cases k; cases k'; rfl) hkk)
    ?_
    (fun _ a ha D hD => hpool a ha D hD)
  · intro _ a r D ha hr hD
    have hchosen : W (Classical.choose (hserve a r D (Nat.le_of_lt ha) hr hD)) :=
      Or.inr ⟨a, r, D, Nat.le_of_lt ha, hr, hD, rfl⟩
    have hspec := (Classical.choose_spec (hserve a r D (Nat.le_of_lt ha) hr hD))
    have hrow : I.rho (d i)
        (Classical.choose (hserve a r D (Nat.le_of_lt ha) hr hD)) = r := by
      have h1 := hspec.2.2 0 (Nat.zero_le p)
      rwa [Nat.add_zero] at h1
    refine ⟨⟨_, hchosen⟩, ?_, hrow, hspec.2.1⟩
    have hedge : I.rho (elt (.inr ()))
        (elt (.inl (⟨_, hchosen⟩ : β))) = r := hrow
    show tightNePo I elt (.inr ()) (.inl ⟨_, hchosen⟩)
    unfold tightNePo
    rw [hedge]
    rcases hr with rfl | rfl | rfl <;> decide

/-- THE DESCENDING GENERAL BLOCK FROM A CHAIN (mirror of
    `multiBlock_of_chain`): every descending model chain carries, past
    any bound, a `BlockOk` built by `mkBlock`. -/
theorem dmultiBlock_of_chain (hI : RCC5Interp I)
    {d : Nat → α} (hdom : ∀ i, I.dom (d i))
    (hstep : ∀ i, I.rho (d i) (d (i + 1)) = ppi)
    (C0 : Concept) (hpo : POFree C0) (myTag : Nat)
    (P : List (Nat × List Concept)) (ctx : List α)
    (hctxdom : ∀ e ∈ ctx, I.dom e) (L : Nat)
    (hpoolcl : ∀ D, Concept.ex po D ∈ cl C0 →
      ∃ q ∈ P, q.1 ≠ myTag ∧ D ∈ q.2) :
    ∃ i p, L ≤ i ∧ 0 < p ∧
      ∃ (β : Type) (T : MultiTier β Unit),
        BlockOk T myTag P ∧ T.p () = p ∧
        (∀ a, T.phase () a = mty C0 I (d (i + a))) ∧
        (POFree C0 → MTNoPo T) := by
  obtain ⟨i, p, hLi, hp, hty, hctx, _, hserve⟩ :=
    dkernel_site hI hdom hstep C0 ctx hctxdom L
  exact ⟨i, p, hLi, hp, dmultiBlock_of_site hI hdom hstep C0 hpo myTag P
    ctx hctxdom hp hty hctx hserve
    (fun a _ D hD => hpoolcl D (mty_sub _ hD))⟩

end BlockFromSite

/-! ## Round E3g (2026-07-23): kernels from persistent vertical demand

The first stone of the assembly RECURSION (LEAN.md item 1): where do
the kernels come from?  A model element carrying a PERSISTENT `∃PP`
demand — `∃PP.G` together with its guard `∀PP.(∃PP.G)` — is a
PRODUCTIVE predicate for the chain builder: its `∃PP.G` yields a
`PP`-successor `y` that again carries `∃PP.G` (from the guard,
`mty_all`) AND re-establishes the guard (because `∀PP` CLIMBS —
`sat_all_pp_up`, `comp(pp,pp)={pp}`).  So `buildChain` turns any such
element into an infinite ascending model chain, every rung carrying
`∃PP.G` — a genuine kernel.  Composed with `multiBlock_of_chain`
(E3f), a persistent-`∃PP` element yields an actual certificate block:
`block_of_persistent`.  This is the demand → kernel → certificate
link the assembly instantiates once per vertical demand component.

Ascending only (persistent `∃PP`); the descending dual (persistent
`∃PPI` on a `PPI`-chain) is a mirrored round. -/

section PersistentKernel

variable {α : Type} {I : Interp α}

/-- A persistent `∃PP` demand: `∃PP.G` plus its self-reproducing guard
    `∀PP.(∃PP.G)`. -/
def persistPP (I : Interp α) (C0 G : Concept) (x : α) : Prop :=
  I.dom x ∧ Concept.ex pp G ∈ mty C0 I x ∧
  Concept.all pp (Concept.ex pp G) ∈ mty C0 I x

/-- Persistent `∃PP` demand is PRODUCTIVE for the chain builder: a
    `PP`-successor inherits both the demand and its guard. -/
theorem persistPP_productive (hI : RCC5Interp I) {C0 G : Concept}
    (x : α) (hx : persistPP I C0 G x) :
    ∃ y, persistPP I C0 G y ∧ I.dom y ∧ I.rho x y = pp := by
  obtain ⟨hdx, hex, hall⟩ := hx
  obtain ⟨y, hdy, hr, _⟩ := mty_ex hex
  refine ⟨y, ⟨hdy, mty_all hall hdy hr, ?_⟩, hdy, hr⟩
  obtain ⟨hcl, hsat⟩ := mem_mty.mp hall
  exact mem_mty.mpr ⟨hcl, sat_all_pp_up hI hdx hdy hr hsat⟩

/-- MULTI-persistence: every demand in `Ds` is persistent (`∃PP.D` + its
    guard `∀PP.(∃PP.D)`) at `x`.  The foundation for round-robin serving:
    all demands stay live along an ascending chain. -/
def persistAll (I : Interp α) (C0 : Concept) (Ds : List Concept) (x : α) : Prop :=
  I.dom x ∧ ∀ D ∈ Ds, Concept.ex pp D ∈ mty C0 I x ∧
    sat I x (Concept.all pp (Concept.ex pp D))

/-- ROUND-ROBIN PRODUCTIVITY: from a multi-persistent `x`, serving ANY
    chosen demand `D ∈ Ds` gives a `PP`-successor `y` that (i) carries `D`
    and (ii) is STILL multi-persistent — every demand's guard propagates
    up.  So demands can be served one at a time without losing the others. -/
theorem persistAll_productive (hI : RCC5Interp I) {C0 : Concept}
    {Ds : List Concept} (x : α) (hx : persistAll I C0 Ds x)
    {D : Concept} (hD : D ∈ Ds) :
    ∃ y, persistAll I C0 Ds y ∧ I.dom y ∧ I.rho x y = pp ∧ D ∈ mty C0 I y := by
  obtain ⟨hdx, hguards⟩ := hx
  obtain ⟨hex, _⟩ := hguards D hD
  obtain ⟨y, hdy, hr, hDy⟩ := mty_ex hex
  refine ⟨y, ⟨hdy, ?_⟩, hdy, hr, hDy⟩
  intro D' hD'
  obtain ⟨hex', hall'⟩ := hguards D' hD'
  exact ⟨mem_mty.mpr ⟨mty_sub _ hex', hall' y hdy hr⟩,
    sat_all_pp_up hI hdx hdy hr hall'⟩

/-- DESCENDING multi-persistence (mirror of `persistAll`): every demand in
    `Ds` is persistent as `∃PPI.D` with a sat-based `∀PPI` guard. -/
def persistAllI (I : Interp α) (C0 : Concept) (Ds : List Concept) (x : α) : Prop :=
  I.dom x ∧ ∀ D ∈ Ds, Concept.ex ppi D ∈ mty C0 I x ∧
    sat I x (Concept.all ppi (Concept.ex ppi D))

/-- Descending round-robin productivity: serving any `D ∈ Ds` gives a
    `PPI`-successor carrying `D` that stays multi-persistent (the `∀PPI`
    guards descend via `sat_all_ppi_down`). -/
theorem persistAllI_productive (hI : RCC5Interp I) {C0 : Concept}
    {Ds : List Concept} (x : α) (hx : persistAllI I C0 Ds x)
    {D : Concept} (hD : D ∈ Ds) :
    ∃ y, persistAllI I C0 Ds y ∧ I.dom y ∧ I.rho x y = ppi ∧ D ∈ mty C0 I y := by
  obtain ⟨hdx, hguards⟩ := hx
  obtain ⟨hex, _⟩ := hguards D hD
  obtain ⟨y, hdy, hr, hDy⟩ := mty_ex hex
  have hyx : I.rho y x = pp := by rw [hI.conv_ x y hdx hdy, hr]; rfl
  refine ⟨y, ⟨hdy, ?_⟩, hdy, hr, hDy⟩
  intro D' hD'
  obtain ⟨hex', hall'⟩ := hguards D' hD'
  exact ⟨mem_mty.mpr ⟨mty_sub _ hex', hall' y hdy hr⟩,
    sat_all_ppi_down hI hdx hdy hyx hall'⟩

/-- The ROUND-ROBIN chain (subtype-bundled): step `n+1` serves demand
    `Ds[n % L]`, so the chain cycles through ALL demands while every rung
    stays multi-persistent. -/
noncomputable def rrChain (hI : RCC5Interp I) (C0 : Concept) (Ds : List Concept)
    (hL : 0 < Ds.length) (x0 : α) (h0 : persistAll I C0 Ds x0) :
    Nat → {a : α // persistAll I C0 Ds a}
  | 0 => ⟨x0, h0⟩
  | n + 1 =>
    ⟨Classical.choose (persistAll_productive hI (rrChain hI C0 Ds hL x0 h0 n).1
        (rrChain hI C0 Ds hL x0 h0 n).2
        (List.get_mem Ds ⟨n % Ds.length, Nat.mod_lt n hL⟩)),
     (Classical.choose_spec (persistAll_productive hI (rrChain hI C0 Ds hL x0 h0 n).1
        (rrChain hI C0 Ds hL x0 h0 n).2
        (List.get_mem Ds ⟨n % Ds.length, Nat.mod_lt n hL⟩))).1⟩

/-- The round-robin chain points. -/
noncomputable def rrPt (hI : RCC5Interp I) (C0 : Concept) (Ds : List Concept)
    (hL : 0 < Ds.length) (x0 : α) (h0 : persistAll I C0 Ds x0) (n : Nat) : α :=
  (rrChain hI C0 Ds hL x0 h0 n).1

theorem rrPt_prop (hI : RCC5Interp I) (C0 : Concept) (Ds : List Concept)
    (hL : 0 < Ds.length) (x0 : α) (h0 : persistAll I C0 Ds x0) (n : Nat) :
    persistAll I C0 Ds (rrPt hI C0 Ds hL x0 h0 n) :=
  (rrChain hI C0 Ds hL x0 h0 n).2

theorem rrPt_dom (hI : RCC5Interp I) (C0 : Concept) (Ds : List Concept)
    (hL : 0 < Ds.length) (x0 : α) (h0 : persistAll I C0 Ds x0) (n : Nat) :
    I.dom (rrPt hI C0 Ds hL x0 h0 n) :=
  (rrPt_prop hI C0 Ds hL x0 h0 n).1

theorem rrPt_step (hI : RCC5Interp I) (C0 : Concept) (Ds : List Concept)
    (hL : 0 < Ds.length) (x0 : α) (h0 : persistAll I C0 Ds x0) (n : Nat) :
    I.rho (rrPt hI C0 Ds hL x0 h0 n) (rrPt hI C0 Ds hL x0 h0 (n + 1)) = pp :=
  (Classical.choose_spec (persistAll_productive hI (rrChain hI C0 Ds hL x0 h0 n).1
    (rrChain hI C0 Ds hL x0 h0 n).2
    (List.get_mem Ds ⟨n % Ds.length, Nat.mod_lt n hL⟩))).2.2.1

/-- Step `n+1` CARRIES the demand `Ds[n % L]` it served. -/
theorem rrPt_serves (hI : RCC5Interp I) (C0 : Concept) (Ds : List Concept)
    (hL : 0 < Ds.length) (x0 : α) (h0 : persistAll I C0 Ds x0) (n : Nat) :
    Ds.get ⟨n % Ds.length, Nat.mod_lt n hL⟩ ∈
      mty C0 I (rrPt hI C0 Ds hL x0 h0 (n + 1)) :=
  (Classical.choose_spec (persistAll_productive hI (rrChain hI C0 Ds hL x0 h0 n).1
    (rrChain hI C0 Ds hL x0 h0 n).2
    (List.get_mem Ds ⟨n % Ds.length, Nat.mod_lt n hL⟩))).2.2.2

/-- DESCENDING round-robin chain (mirror of `rrChain`): step `n+1` serves
    `Ds[n % L]` DOWN a `PPI`-chain, every rung multi-persistent. -/
noncomputable def rrChainI (hI : RCC5Interp I) (C0 : Concept) (Ds : List Concept)
    (hL : 0 < Ds.length) (x0 : α) (h0 : persistAllI I C0 Ds x0) :
    Nat → {a : α // persistAllI I C0 Ds a}
  | 0 => ⟨x0, h0⟩
  | n + 1 =>
    ⟨Classical.choose (persistAllI_productive hI (rrChainI hI C0 Ds hL x0 h0 n).1
        (rrChainI hI C0 Ds hL x0 h0 n).2
        (List.get_mem Ds ⟨n % Ds.length, Nat.mod_lt n hL⟩)),
     (Classical.choose_spec (persistAllI_productive hI (rrChainI hI C0 Ds hL x0 h0 n).1
        (rrChainI hI C0 Ds hL x0 h0 n).2
        (List.get_mem Ds ⟨n % Ds.length, Nat.mod_lt n hL⟩))).1⟩

noncomputable def rrPtI (hI : RCC5Interp I) (C0 : Concept) (Ds : List Concept)
    (hL : 0 < Ds.length) (x0 : α) (h0 : persistAllI I C0 Ds x0) (n : Nat) : α :=
  (rrChainI hI C0 Ds hL x0 h0 n).1

theorem rrPtI_prop (hI : RCC5Interp I) (C0 : Concept) (Ds : List Concept)
    (hL : 0 < Ds.length) (x0 : α) (h0 : persistAllI I C0 Ds x0) (n : Nat) :
    persistAllI I C0 Ds (rrPtI hI C0 Ds hL x0 h0 n) :=
  (rrChainI hI C0 Ds hL x0 h0 n).2

theorem rrPtI_dom (hI : RCC5Interp I) (C0 : Concept) (Ds : List Concept)
    (hL : 0 < Ds.length) (x0 : α) (h0 : persistAllI I C0 Ds x0) (n : Nat) :
    I.dom (rrPtI hI C0 Ds hL x0 h0 n) :=
  (rrPtI_prop hI C0 Ds hL x0 h0 n).1

theorem rrPtI_step (hI : RCC5Interp I) (C0 : Concept) (Ds : List Concept)
    (hL : 0 < Ds.length) (x0 : α) (h0 : persistAllI I C0 Ds x0) (n : Nat) :
    I.rho (rrPtI hI C0 Ds hL x0 h0 n) (rrPtI hI C0 Ds hL x0 h0 (n + 1)) = ppi :=
  (Classical.choose_spec (persistAllI_productive hI (rrChainI hI C0 Ds hL x0 h0 n).1
    (rrChainI hI C0 Ds hL x0 h0 n).2
    (List.get_mem Ds ⟨n % Ds.length, Nat.mod_lt n hL⟩))).2.2.1

theorem rrPtI_serves (hI : RCC5Interp I) (C0 : Concept) (Ds : List Concept)
    (hL : 0 < Ds.length) (x0 : α) (h0 : persistAllI I C0 Ds x0) (n : Nat) :
    Ds.get ⟨n % Ds.length, Nat.mod_lt n hL⟩ ∈
      mty C0 I (rrPtI hI C0 Ds hL x0 h0 (n + 1)) :=
  (Classical.choose_spec (persistAllI_productive hI (rrChainI hI C0 Ds hL x0 h0 n).1
    (rrChainI hI C0 Ds hL x0 h0 n).2
    (List.get_mem Ds ⟨n % Ds.length, Nat.mod_lt n hL⟩))).2.2.2

/-- THE PERSISTENT KERNEL CHAIN: a persistent-`∃PP` element builds an
    infinite ascending model chain, every rung carrying `∃PP.G`. -/
theorem persistPP_chain (hI : RCC5Interp I) {C0 G : Concept} (x0 : α)
    (h0 : persistPP I C0 G x0) :
    ∃ c : Nat → α, c 0 = x0 ∧ (∀ n, I.dom (c n)) ∧
      (∀ n, I.rho (c n) (c (n + 1)) = pp) ∧
      (∀ n, Concept.ex pp G ∈ mty C0 I (c n)) := by
  refine ⟨buildChain (persistPP I C0 G) (persistPP_productive hI) x0 h0,
    buildChain_zero _ _ x0 h0, ?_, ?_, ?_⟩
  · exact fun n => (buildChain_prop _ _ x0 h0 n).1
  · exact fun n => buildChain_step _ _ x0 h0 n
  · exact fun n => (buildChain_prop _ _ x0 h0 n).2.1

/-- THE DEMAND → CERTIFICATE LINK: a persistent-`∃PP` element yields an
    actual certificate block (via `multiBlock_of_chain`). -/
theorem block_of_persistent (hI : RCC5Interp I) {C0 G : Concept}
    (hpo : POFree C0) (myTag : Nat) (P : List (Nat × List Concept))
    (ctx : List α) (hctxdom : ∀ e ∈ ctx, I.dom e)
    (hpoolcl : ∀ D, Concept.ex po D ∈ cl C0 →
      ∃ q ∈ P, q.1 ≠ myTag ∧ D ∈ q.2)
    (x0 : α) (h0 : persistPP I C0 G x0) (L : Nat) :
    ∃ i p, L ≤ i ∧ 0 < p ∧
      ∃ (β : Type) (T : MultiTier β Unit),
        BlockOk T myTag P ∧ T.p () = p ∧
        (POFree C0 → MTNoPo T) := by
  obtain ⟨c, _, hdom, hstep, _⟩ := persistPP_chain hI x0 h0
  obtain ⟨i, p, hLi, hp, β, T, hBlock, hpT, _, hnopo⟩ :=
    multiBlock_of_chain hI hdom hstep C0 hpo myTag P ctx hctxdom L hpoolcl
  exact ⟨i, p, hLi, hp, β, T, hBlock, hpT, hnopo⟩

end PersistentKernel

/-! ## Round E3g′ (2026-07-23): the descending persistent kernel

The mirror of E3g: a persistent `∃PPI` demand — `∃PPI.G` plus its
guard `∀PPI.(∃PPI.G)` — is productive for the DESCENDING chain builder
(`dbuildChain`).  The guard descends via `sat_all_ppi_down` (`∀PPI`
holds at everything below its holder), the `PP`-below step supplied by
converse coherence (`conv PPI = PP`).  So a persistent-`∃PPI` element
builds an infinite descending model chain — the `up = false` kernel a
mixed assembly consumes alongside ascending ones. -/

section DescPersistentKernel

variable {α : Type} {I : Interp α}

/-- A persistent `∃PPI` demand: `∃PPI.G` plus its self-reproducing
    guard `∀PPI.(∃PPI.G)`. -/
def persistPPI (I : Interp α) (C0 G : Concept) (x : α) : Prop :=
  I.dom x ∧ Concept.ex ppi G ∈ mty C0 I x ∧
  Concept.all ppi (Concept.ex ppi G) ∈ mty C0 I x

/-- Persistent `∃PPI` demand is PRODUCTIVE for the descending chain
    builder: a `PPI`-successor inherits both the demand and its guard
    (the guard descends via `sat_all_ppi_down`). -/
theorem persistPPI_productive (hI : RCC5Interp I) {C0 G : Concept}
    (x : α) (hx : persistPPI I C0 G x) :
    ∃ y, persistPPI I C0 G y ∧ I.dom y ∧ I.rho x y = ppi := by
  obtain ⟨hdx, hex, hall⟩ := hx
  obtain ⟨y, hdy, hr, _⟩ := mty_ex hex
  refine ⟨y, ⟨hdy, mty_all hall hdy hr, ?_⟩, hdy, hr⟩
  obtain ⟨hcl, hsat⟩ := mem_mty.mp hall
  have hyx : I.rho y x = pp := by
    rw [hI.conv_ x y hdx hdy, hr]; rfl
  exact mem_mty.mpr ⟨hcl, sat_all_ppi_down hI hdx hdy hyx hsat⟩

/-- THE DESCENDING PERSISTENT KERNEL CHAIN: a persistent-`∃PPI`
    element builds an infinite descending model chain, every rung
    carrying `∃PPI.G`. -/
theorem persistPPI_chain (hI : RCC5Interp I) {C0 G : Concept} (x0 : α)
    (h0 : persistPPI I C0 G x0) :
    ∃ d : Nat → α, d 0 = x0 ∧ (∀ n, I.dom (d n)) ∧
      (∀ n, I.rho (d n) (d (n + 1)) = ppi) ∧
      (∀ n, Concept.ex ppi G ∈ mty C0 I (d n)) := by
  refine ⟨dbuildChain (persistPPI I C0 G) (persistPPI_productive hI) x0 h0,
    dbuildChain_zero _ _ x0 h0, ?_, ?_, ?_⟩
  · exact fun n => (dbuildChain_prop _ _ x0 h0 n).1
  · exact fun n => dbuildChain_step _ _ x0 h0 n
  · exact fun n => (dbuildChain_prop _ _ x0 h0 n).2.1

/-- THE DESCENDING DEMAND → CERTIFICATE LINK (mirror of
    `block_of_persistent`): a persistent-`∃PPI` element yields an actual
    certificate block (via `dmultiBlock_of_chain`). -/
theorem block_of_persistent_desc (hI : RCC5Interp I) {C0 G : Concept}
    (hpo : POFree C0) (myTag : Nat) (P : List (Nat × List Concept))
    (ctx : List α) (hctxdom : ∀ e ∈ ctx, I.dom e)
    (hpoolcl : ∀ D, Concept.ex po D ∈ cl C0 →
      ∃ q ∈ P, q.1 ≠ myTag ∧ D ∈ q.2)
    (x0 : α) (h0 : persistPPI I C0 G x0) (L : Nat) :
    ∃ i p, L ≤ i ∧ 0 < p ∧
      ∃ (β : Type) (T : MultiTier β Unit),
        BlockOk T myTag P ∧ T.p () = p ∧
        (POFree C0 → MTNoPo T) := by
  obtain ⟨d, _, hdom, hstep, _⟩ := persistPPI_chain hI x0 h0
  obtain ⟨i, p, hLi, hp, β, T, hBlock, hpT, _, hnopo⟩ :=
    dmultiBlock_of_chain hI hdom hstep C0 hpo myTag P ctx hctxdom L hpoolcl
  exact ⟨i, p, hLi, hp, β, T, hBlock, hpT, hnopo⟩

end DescPersistentKernel

/-! ## Round E3i (2026-07-23): the modal-depth termination measure

Design plan (ASSEMBLY_DESIGN.md §§3–4) round 2: the requirement-typing
scaffold, concretely the TERMINATION measure that makes the horizontal
recursion well-founded.  `mdepth C` = the nesting depth of `∃`/`∀` in
`C`.  Every demand step strictly DECREASES it — `mdepth c <
mdepth (∃r.c)` and `mdepth c < mdepth (∀r.c)` — and the subformula
closure never increases it (`cl_mdepth_le`).  So a demand whose
formula lies in `cl C₀` has argument depth `< mdepth C₀`
(`cl_ex_mdepth_lt`/`cl_all_mdepth_lt`): the horizontal unravelling has
depth bounded by `mdepth C₀`.

This is the horizontal half of the termination argument (design §4);
vertical demands (`∃PP`/`∃PPI`) also strictly decrease `mdepth` per
STEP but recur with the SAME formula along a kernel chain (the guard
`∀PP.(∃PP.G)` reproduces `∃PP.G`), so they do not terminate by this
measure — they are absorbed by kernels (E3g/E3g′), not unravelled. -/

section ModalDepth

/-- The `∃`/`∀` nesting depth of a concept. -/
def mdepth : Concept → Nat
  | .and c d => Nat.max (mdepth c) (mdepth d)
  | .or c d => Nat.max (mdepth c) (mdepth d)
  | .ex _ c => mdepth c + 1
  | .all _ c => mdepth c + 1
  | _ => 0

/-- A demand's argument is strictly shallower. -/
theorem mdepth_ex_lt (r : Atom) (c : Concept) : mdepth c < mdepth (.ex r c) :=
  Nat.lt_succ_self _

/-- A universal's argument is strictly shallower. -/
theorem mdepth_all_lt (r : Atom) (c : Concept) :
    mdepth c < mdepth (.all r c) :=
  Nat.lt_succ_self _

/-- The subformula closure never increases modal depth — so the whole
    recursion lives at depth `≤ mdepth C₀`. -/
theorem cl_mdepth_le : ∀ e x : Concept, x ∈ cl e → mdepth x ≤ mdepth e := by
  intro e
  induction e with
  | top =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | h
    · exact Nat.le_refl _
    · exact nomatch h
  | bot =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | h
    · exact Nat.le_refl _
    · exact nomatch h
  | atom a =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | h
    · exact Nat.le_refl _
    · exact nomatch h
  | natom a =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | h
    · exact Nat.le_refl _
    · exact nomatch h
  | and c d ihc ihd =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Nat.le_refl _
    · rcases List.mem_append.mp hx' with h | h
      · exact Nat.le_trans (ihc x h) (Nat.le_max_left _ _)
      · exact Nat.le_trans (ihd x h) (Nat.le_max_right _ _)
  | or c d ihc ihd =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Nat.le_refl _
    · rcases List.mem_append.mp hx' with h | h
      · exact Nat.le_trans (ihc x h) (Nat.le_max_left _ _)
      · exact Nat.le_trans (ihd x h) (Nat.le_max_right _ _)
  | ex r c ihc =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Nat.le_refl _
    · exact Nat.le_trans (ihc x hx') (Nat.le_succ _)
  | all r c ihc =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Nat.le_refl _
    · exact Nat.le_trans (ihc x hx') (Nat.le_succ _)

/-- A demand occurring in the closure has argument depth strictly below
    `mdepth C₀` — the horizontal recursion's decreasing measure. -/
theorem cl_ex_mdepth_lt {C0 : Concept} {r : Atom} {c : Concept}
    (h : Concept.ex r c ∈ cl C0) : mdepth c < mdepth C0 :=
  Nat.lt_of_lt_of_le (mdepth_ex_lt r c) (cl_mdepth_le C0 _ h)

/-- A universal occurring in the closure has argument depth strictly
    below `mdepth C₀`. -/
theorem cl_all_mdepth_lt {C0 : Concept} {r : Atom} {c : Concept}
    (h : Concept.all r c ∈ cl C0) : mdepth c < mdepth C0 :=
  Nat.lt_of_lt_of_le (mdepth_all_lt r c) (cl_mdepth_le C0 _ h)

end ModalDepth

/-! ## Round E3j (2026-07-23): rectangle constancy of forced edges

Design plan (ASSEMBLY_DESIGN.md §5) round 3: the loose-`PO` frame
instance rests on the fact that FORCED tight edges are automatically
rectangle-constant — their value is pinned through a SINGLETON
composition cell, so it cannot vary along a kernel chain.  The two
shapes the assembly declares tight:

- **external below an ASCENDING kernel** (`ext_pp_asc_const`): if `e`
  is `PP`-below the chain base, `comp(pp,pp)={pp}` forces `e PP` the
  WHOLE chain — the constant `PP` row of an external sitting under its
  own kernel (the `∃DR`-witness's ascending demand, design §5).
- **external `DR` to a DESCENDING kernel's top** (`ext_dr_desc_const`):
  if `e DR` the chain base, `comp(dr,ppi)={dr}` forces `e DR` the WHOLE
  descending chain — the constant `DR` row of a `DR`-witness whose
  demand descends (the clean `∃DR`-witness case).

These are the `hrectK`/`hrectQ` inputs for the forced tight edges;
every non-forced cross edge is declared loose `PO` (harmless —
`mty_no_all_po`), so no other rectangle obligation arises.  No joint
(mutual) chain stabilization is needed — the rectangle problem is
carried entirely by these singleton-cell forcings. -/

section ForcedConstancy

variable {α : Type} {I : Interp α}

/-- FORCED `PP` CONSTANCY: an external `PP`-below an ascending kernel's
    base is `PP` to the whole chain (`comp(pp,pp)={pp}`). -/
theorem ext_pp_asc_const (hI : RCC5Interp I)
    {c : Nat → α} (hdom : ∀ i, I.dom (c i))
    (hstep : ∀ i, I.rho (c i) (c (i + 1)) = pp) {e : α} (hde : I.dom e)
    (h0 : I.rho e (c 0) = pp) : ∀ j, I.rho e (c j) = pp := by
  intro j
  cases j with
  | zero => exact h0
  | succ k =>
    have hcc := chain_model_pp hI hdom hstep 0 (k + 1) (Nat.succ_pos k)
    have hm := hI.comp_ e (c 0) (c (k + 1)) hde (hdom 0) (hdom (k + 1))
    rw [h0, hcc] at hm
    exact List.mem_singleton.mp hm

/-- FORCED `DR` CONSTANCY: an external `DR` to a descending kernel's
    top is `DR` to the whole chain (`comp(dr,ppi)={dr}`). -/
theorem ext_dr_desc_const (hI : RCC5Interp I)
    {d : Nat → α} (hdom : ∀ i, I.dom (d i))
    (hstep : ∀ i, I.rho (d i) (d (i + 1)) = ppi) {e : α} (hde : I.dom e)
    (h0 : I.rho e (d 0) = dr) : ∀ j, I.rho e (d j) = dr := by
  intro j
  cases j with
  | zero => exact h0
  | succ k =>
    have hcc := dchain_model_ppi hI hdom hstep 0 (k + 1) (Nat.succ_pos k)
    have hm := hI.comp_ e (d 0) (d (k + 1)) hde (hdom 0) (hdom (k + 1))
    rw [h0, hcc] at hm
    exact List.mem_singleton.mp hm

end ForcedConstancy

/-! ## Round E3k (2026-07-23): the requirement-type generator

Design plan (ASSEMBLY_DESIGN.md §§2–3) round 4, component 1: the node
label of the assembly recursion.  `expand I x F` is the model-GUIDED
propositional expansion of a required formula `F` — its demanded
propositional consequences, with each disjunction resolved by the
guide `x`.  This is a REQUIREMENT type (not a model type): it contains
only SUBFORMULAS of `F` (`expand_sub_cl`), which is exactly what makes
a `∃PO.D` library demand only strict subformulas of `D` — the
well-foundedness of the `∃PO` pool (design §3.1).  Guided by a real
model element it lands inside the model type (`expand_sub_mty`), so
every node is clash-free and model-realizable for free, and it is
propositionally saturated (`expand_and`/`expand_or`) — the
propositional Hintikka conditions of a block node.

This is component 1 of the recursion (round 4); the ∀-firing closure
across the edge structure and the ∃-demand coverage — the coupled hard
core — are the remaining components. -/

section RequirementTypes

variable {α : Type} {I : Interp α}

open Classical in
/-- The model-guided propositional expansion of a required formula:
    its demanded propositional consequences, each disjunction resolved
    by the guide `x`.  A REQUIREMENT type — subformulas only. -/
noncomputable def expand (I : Interp α) (x : α) : Concept → List Concept
  | .and c d => Concept.and c d :: (expand I x c ++ expand I x d)
  | .or c d =>
      Concept.or c d :: (if sat I x c then expand I x c else expand I x d)
  | c => [c]

/-- The seed formula is always in its own expansion. -/
theorem mem_expand_self (I : Interp α) (x : α) (F : Concept) :
    F ∈ expand I x F := by
  cases F <;> exact List.mem_cons_self

/-- REQUIREMENT-TYPING: the expansion contains only subformulas of the
    seed — the key to the `∃PO` pool's well-foundedness (a library for
    `D` demands only strict subformulas of `D`). -/
theorem expand_sub_cl (I : Interp α) (x : α) :
    ∀ F, ∀ G ∈ expand I x F, G ∈ cl F := by
  intro F
  induction F with
  | top =>
    intro G hG
    rcases List.mem_cons.mp hG with rfl | h
    · exact List.mem_cons_self
    · exact nomatch h
  | bot =>
    intro G hG
    rcases List.mem_cons.mp hG with rfl | h
    · exact List.mem_cons_self
    · exact nomatch h
  | atom a =>
    intro G hG
    rcases List.mem_cons.mp hG with rfl | h
    · exact List.mem_cons_self
    · exact nomatch h
  | natom a =>
    intro G hG
    rcases List.mem_cons.mp hG with rfl | h
    · exact List.mem_cons_self
    · exact nomatch h
  | and c d ihc ihd =>
    intro G hG
    rcases List.mem_cons.mp hG with rfl | hG'
    · exact List.mem_cons_self
    · rcases List.mem_append.mp hG' with h | h
      · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (ihc G h)))
      · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (ihd G h)))
  | or c d ihc ihd =>
    intro G hG
    rcases List.mem_cons.mp hG with rfl | hG'
    · exact List.mem_cons_self
    · by_cases hs : sat I x c
      · simp only [if_pos hs] at hG'
        exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (ihc G hG')))
      · simp only [if_neg hs] at hG'
        exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (ihd G hG')))
  | ex r c ihc =>
    intro G hG
    rcases List.mem_cons.mp hG with rfl | h
    · exact List.mem_cons_self
    · exact nomatch h
  | all r c ihc =>
    intro G hG
    rcases List.mem_cons.mp hG with rfl | h
    · exact List.mem_cons_self
    · exact nomatch h

/-- MODEL REALIZABILITY: guided by a model element `x`, the expansion
    of a formula in `x`'s type stays inside `x`'s type — so every
    requirement node is clash-free and demand-witnessed for free. -/
theorem expand_sub_mty {C0 : Concept} {x : α} :
    ∀ F, F ∈ mty C0 I x → ∀ G ∈ expand I x F, G ∈ mty C0 I x := by
  intro F
  induction F with
  | top =>
    intro hF G hG
    rcases List.mem_cons.mp hG with rfl | h
    · exact hF
    · exact nomatch h
  | bot =>
    intro hF G hG
    rcases List.mem_cons.mp hG with rfl | h
    · exact hF
    · exact nomatch h
  | atom a =>
    intro hF G hG
    rcases List.mem_cons.mp hG with rfl | h
    · exact hF
    · exact nomatch h
  | natom a =>
    intro hF G hG
    rcases List.mem_cons.mp hG with rfl | h
    · exact hF
    · exact nomatch h
  | and c d ihc ihd =>
    intro hF G hG
    rcases List.mem_cons.mp hG with rfl | hG'
    · exact hF
    · obtain ⟨hc, hd⟩ := mty_and hF
      rcases List.mem_append.mp hG' with h | h
      · exact ihc hc G h
      · exact ihd hd G h
  | or c d ihc ihd =>
    intro hF G hG
    rcases List.mem_cons.mp hG with rfl | hG'
    · exact hF
    · by_cases hs : sat I x c
      · simp only [if_pos hs] at hG'
        exact ihc (mem_mty.mpr ⟨cl_or_left (mty_sub _ hF), hs⟩) G hG'
      · simp only [if_neg hs] at hG'
        have hd : d ∈ mty C0 I x := by
          rcases mty_or hF with h | h
          · exact absurd (mem_mty.mp h).2 hs
          · exact h
        exact ihd hd G hG'
  | ex r c ihc =>
    intro hF G hG
    rcases List.mem_cons.mp hG with rfl | h
    · exact hF
    · exact nomatch h
  | all r c ihc =>
    intro hF G hG
    rcases List.mem_cons.mp hG with rfl | h
    · exact hF
    · exact nomatch h

/-- PROPOSITIONAL SATURATION (`∧`): the expansion is closed under
    conjunction decomposition. -/
theorem expand_and (I : Interp α) (x : α) :
    ∀ F c d, Concept.and c d ∈ expand I x F →
      c ∈ expand I x F ∧ d ∈ expand I x F := by
  intro F
  induction F with
  | top =>
    intro c d hG
    rcases List.mem_cons.mp hG with h | h
    · exact Concept.noConfusion h
    · exact nomatch h
  | bot =>
    intro c d hG
    rcases List.mem_cons.mp hG with h | h
    · exact Concept.noConfusion h
    · exact nomatch h
  | atom a =>
    intro c d hG
    rcases List.mem_cons.mp hG with h | h
    · exact Concept.noConfusion h
    · exact nomatch h
  | natom a =>
    intro c d hG
    rcases List.mem_cons.mp hG with h | h
    · exact Concept.noConfusion h
    · exact nomatch h
  | and a b iha ihb =>
    intro c d hG
    rcases List.mem_cons.mp hG with heq | hG'
    · injection heq with h1 h2
      subst h1; subst h2
      exact ⟨List.mem_cons_of_mem _
          (List.mem_append.mpr (Or.inl (mem_expand_self I x c))),
        List.mem_cons_of_mem _
          (List.mem_append.mpr (Or.inr (mem_expand_self I x d)))⟩
    · rcases List.mem_append.mp hG' with h | h
      · obtain ⟨hc, hd⟩ := iha c d h
        exact ⟨List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hc)),
          List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hd))⟩
      · obtain ⟨hc, hd⟩ := ihb c d h
        exact ⟨List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hc)),
          List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hd))⟩
  | or a b iha ihb =>
    intro c d hG
    rcases List.mem_cons.mp hG with heq | hG'
    · exact Concept.noConfusion heq
    · by_cases hs : sat I x a
      · simp only [if_pos hs] at hG'
        obtain ⟨hc, hd⟩ := iha c d hG'
        exact ⟨List.mem_cons_of_mem _ (by simp only [if_pos hs]; exact hc),
          List.mem_cons_of_mem _ (by simp only [if_pos hs]; exact hd)⟩
      · simp only [if_neg hs] at hG'
        obtain ⟨hc, hd⟩ := ihb c d hG'
        exact ⟨List.mem_cons_of_mem _ (by simp only [if_neg hs]; exact hc),
          List.mem_cons_of_mem _ (by simp only [if_neg hs]; exact hd)⟩
  | ex r a iha =>
    intro c d hG
    rcases List.mem_cons.mp hG with h | h
    · exact Concept.noConfusion h
    · exact nomatch h
  | all r a iha =>
    intro c d hG
    rcases List.mem_cons.mp hG with h | h
    · exact Concept.noConfusion h
    · exact nomatch h

/-- PROPOSITIONAL SATURATION (`∨`): the expansion resolves every
    disjunction it contains (the guide-chosen branch is present). -/
theorem expand_or (I : Interp α) (x : α) :
    ∀ F c d, Concept.or c d ∈ expand I x F →
      c ∈ expand I x F ∨ d ∈ expand I x F := by
  intro F
  induction F with
  | top =>
    intro c d hG
    rcases List.mem_cons.mp hG with h | h
    · exact Concept.noConfusion h
    · exact nomatch h
  | bot =>
    intro c d hG
    rcases List.mem_cons.mp hG with h | h
    · exact Concept.noConfusion h
    · exact nomatch h
  | atom a =>
    intro c d hG
    rcases List.mem_cons.mp hG with h | h
    · exact Concept.noConfusion h
    · exact nomatch h
  | natom a =>
    intro c d hG
    rcases List.mem_cons.mp hG with h | h
    · exact Concept.noConfusion h
    · exact nomatch h
  | and a b iha ihb =>
    intro c d hG
    rcases List.mem_cons.mp hG with heq | hG'
    · exact Concept.noConfusion heq
    · rcases List.mem_append.mp hG' with h | h
      · rcases iha c d h with hc | hd
        · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hc)))
        · exact Or.inr (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hd)))
      · rcases ihb c d h with hc | hd
        · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hc)))
        · exact Or.inr (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hd)))
  | or a b iha ihb =>
    intro c d hG
    rcases List.mem_cons.mp hG with heq | hG'
    · injection heq with h1 h2
      subst h1; subst h2
      by_cases hs : sat I x c
      · exact Or.inl (List.mem_cons_of_mem _
          (by simp only [if_pos hs]; exact mem_expand_self I x c))
      · exact Or.inr (List.mem_cons_of_mem _
          (by simp only [if_neg hs]; exact mem_expand_self I x d))
    · by_cases hs : sat I x a
      · simp only [if_pos hs] at hG'
        rcases iha c d hG' with hc | hd
        · exact Or.inl (List.mem_cons_of_mem _ (by simp only [if_pos hs]; exact hc))
        · exact Or.inr (List.mem_cons_of_mem _ (by simp only [if_pos hs]; exact hd))
      · simp only [if_neg hs] at hG'
        rcases ihb c d hG' with hc | hd
        · exact Or.inl (List.mem_cons_of_mem _ (by simp only [if_neg hs]; exact hc))
        · exact Or.inr (List.mem_cons_of_mem _ (by simp only [if_neg hs]; exact hd))
  | ex r a iha =>
    intro c d hG
    rcases List.mem_cons.mp hG with h | h
    · exact Concept.noConfusion h
    · exact nomatch h
  | all r a iha =>
    intro c d hG
    rcases List.mem_cons.mp hG with h | h
    · exact Concept.noConfusion h
    · exact nomatch h

/-! ### The node label (round 4, component 2)

A recursion node requires a LIST of formulas — the root `C₀`, plus the
`∀`-consequences fired into it from its parents.  Its label is the
union of their expansions, `reqType I x s`.  The per-formula saturation
(component 1) lifts to the list: the node label is propositionally
Hintikka-saturated, clash-free and model-realizable (inside the guide's
type), contains its seeds, and is finite (a sublist universe of
`⋃ cl F`).  These are exactly the propositional block-node conditions
`e_clash`/`e_nobot`/`e_and`/`e_or` for a requirement-typed node. -/

/-- The node label: the union of the guided expansions of the required
    seed formulas. -/
noncomputable def reqType (I : Interp α) (x : α) (s : List Concept) :
    List Concept :=
  s.flatMap (expand I x)

theorem mem_reqType {I : Interp α} {x : α} {s : List Concept}
    {G : Concept} : G ∈ reqType I x s ↔ ∃ F ∈ s, G ∈ expand I x F :=
  List.mem_flatMap

/-- Seeds are in the label. -/
theorem mem_reqType_of_mem {I : Interp α} {x : α} {s : List Concept}
    {F : Concept} (h : F ∈ s) : F ∈ reqType I x s :=
  mem_reqType.mpr ⟨F, h, mem_expand_self I x F⟩

/-- The label is model-realizable: guided by `x`, with seeds in `x`'s
    type, it stays inside `x`'s type. -/
theorem reqType_sub_mty {C0 : Concept} {I : Interp α} {x : α}
    {s : List Concept} (hs : ∀ F ∈ s, F ∈ mty C0 I x) :
    ∀ G ∈ reqType I x s, G ∈ mty C0 I x := by
  intro G hG
  obtain ⟨F, hF, hGF⟩ := mem_reqType.mp hG
  exact expand_sub_mty F (hs F hF) G hGF

/-- Node condition `e_clash`: clash-free (a subset of a clash-free
    model type). -/
theorem reqType_clash {C0 : Concept} {I : Interp α} {x : α}
    {s : List Concept} (hs : ∀ F ∈ s, F ∈ mty C0 I x) {a : Nat}
    (h : Concept.atom a ∈ reqType I x s) :
    Concept.natom a ∉ reqType I x s :=
  fun h2 => mty_clash (reqType_sub_mty hs _ h) (reqType_sub_mty hs _ h2)

/-- Node condition `e_nobot`: bot-free. -/
theorem reqType_nobot {C0 : Concept} {I : Interp α} {x : α}
    {s : List Concept} (hs : ∀ F ∈ s, F ∈ mty C0 I x) :
    Concept.bot ∉ reqType I x s :=
  fun h => mty_nobot (reqType_sub_mty hs _ h)

/-- Node condition `e_and`: closed under conjunction decomposition. -/
theorem reqType_and {I : Interp α} {x : α} {s : List Concept}
    {c d : Concept} (h : Concept.and c d ∈ reqType I x s) :
    c ∈ reqType I x s ∧ d ∈ reqType I x s := by
  obtain ⟨F, hF, hGF⟩ := mem_reqType.mp h
  obtain ⟨hc, hd⟩ := expand_and I x F c d hGF
  exact ⟨mem_reqType.mpr ⟨F, hF, hc⟩, mem_reqType.mpr ⟨F, hF, hd⟩⟩

/-- Node condition `e_or`: every disjunction resolved. -/
theorem reqType_or {I : Interp α} {x : α} {s : List Concept}
    {c d : Concept} (h : Concept.or c d ∈ reqType I x s) :
    c ∈ reqType I x s ∨ d ∈ reqType I x s := by
  obtain ⟨F, hF, hGF⟩ := mem_reqType.mp h
  rcases expand_or I x F c d hGF with hc | hd
  · exact Or.inl (mem_reqType.mpr ⟨F, hF, hc⟩)
  · exact Or.inr (mem_reqType.mpr ⟨F, hF, hd⟩)

end RequirementTypes

/-! ### The `∀`-firing operation (round 4, component 3)

The primitive that couples node labels across the edge structure: when
the recursion declares an edge `u →r v`, every `∀r.c` in `u`'s label
must be discharged by having `c` in `v`'s SEED.  `fire label r` is that
seed — the `∀r`-consequences of a label.  It is model-SOUND (`fire_sat`:
a label inside `x`'s type fires into any `r`-successor's type, by
`mty_all`) and stays in the closure (`fire_sub_cl`: the fired seed is
finite).  These are the ingredients that make a requirement node's
outgoing seeds close the `ee_all`/`ek_all`/`ke_all`/`kk_*` conditions,
once the recursion threads them along its declared edges. -/

section AllFiring

/-- The formulas fired by a single `∀r`-obligation. -/
def fireOne (r : Atom) : Concept → List Concept
  | .all r' c => if r' = r then [c] else []
  | _ => []

/-- The `∀r`-consequences of a label — the seed fired into an
    `r`-successor. -/
def fire (label : List Concept) (r : Atom) : List Concept :=
  label.flatMap (fireOne r)

theorem mem_fire {label : List Concept} {r : Atom} {c : Concept} :
    c ∈ fire label r ↔ Concept.all r c ∈ label := by
  constructor
  · intro h
    obtain ⟨E, hE, hcE⟩ := List.mem_flatMap.mp h
    cases E with
    | all r' c' =>
      by_cases hr : r' = r
      · simp only [fireOne, if_pos hr, List.mem_singleton] at hcE
        subst hcE; subst hr; exact hE
      · simp only [fireOne, if_neg hr] at hcE
        exact absurd hcE List.not_mem_nil
    | top => simp only [fireOne] at hcE; exact absurd hcE List.not_mem_nil
    | bot => simp only [fireOne] at hcE; exact absurd hcE List.not_mem_nil
    | atom n => simp only [fireOne] at hcE; exact absurd hcE List.not_mem_nil
    | natom n => simp only [fireOne] at hcE; exact absurd hcE List.not_mem_nil
    | and a b => simp only [fireOne] at hcE; exact absurd hcE List.not_mem_nil
    | or a b => simp only [fireOne] at hcE; exact absurd hcE List.not_mem_nil
    | ex r' c' => simp only [fireOne] at hcE; exact absurd hcE List.not_mem_nil
  · intro h
    exact List.mem_flatMap.mpr
      ⟨Concept.all r c, h, by simp only [fireOne, if_pos]; exact List.mem_singleton.mpr rfl⟩

/-- `∀`-firing is model-sound: a label inside `x`'s type fires its
    `∀r`-consequences into any `r`-successor's type. -/
theorem fire_sat {α : Type} {I : Interp α} {C0 : Concept} {x y : α}
    {label : List Concept} {r : Atom}
    (hlab : ∀ E ∈ label, E ∈ mty C0 I x) (hy : I.dom y)
    (hr : I.rho x y = r) : ∀ c ∈ fire label r, c ∈ mty C0 I y := by
  intro c hc
  exact mty_all (hlab _ (mem_fire.mp hc)) hy hr

/-- `∀`-firing stays in the closure — the fired seed is finite. -/
theorem fire_sub_cl {C0 : Concept} {label : List Concept} {r : Atom}
    (hlab : ∀ E ∈ label, E ∈ cl C0) : ∀ c ∈ fire label r, c ∈ cl C0 := by
  intro c hc
  exact cl_all (hlab _ (mem_fire.mp hc))

end AllFiring

/-! ### Per-demand coverage primitives (round 4, component 4)

What the recursion invokes at each `∃`-demand of a node.  A node
labelled `reqType I x s` (seeds inside `x`'s type) has, for every
demand `∃r.c` it carries, a genuine MODEL witness (`reqType_ex_witness`
— `mty_ex` through the label); its argument stays in the closure
(`reqType_sub_cl`, so the node universe is finite); and a HORIZONTAL
demand's argument is strictly shallower (`reqType_ex_mdepth` via
`cl_ex_mdepth_lt`) — the recursion's decreasing measure.  These are the
model-side coverage step; the remaining work is threading them into a
finite closed node set (the fixpoint) and the block assembly. -/

section Coverage

variable {α : Type} {I : Interp α} {C0 : Concept}

/-- A single formula's expansion stays in `cl C₀` when the seed does. -/
theorem expand_sub_cl_of {x : α} {F : Concept} (hF : F ∈ cl C0) :
    ∀ G ∈ expand I x F, G ∈ cl C0 :=
  fun G hG => cl_trans C0 F G hF (expand_sub_cl I x F G hG)

/-- The node label is finite: within `cl C₀` when the seeds are. -/
theorem reqType_sub_cl {x : α} {s : List Concept}
    (hs : ∀ F ∈ s, F ∈ cl C0) : ∀ G ∈ reqType I x s, G ∈ cl C0 := by
  intro G hG
  obtain ⟨F, hF, hGF⟩ := mem_reqType.mp hG
  exact expand_sub_cl_of (hs F hF) G hGF

/-- COVERAGE STEP: every demand a requirement node carries has a
    genuine model witness. -/
theorem reqType_ex_witness {x : α} {s : List Concept}
    (hs : ∀ F ∈ s, F ∈ mty C0 I x) {r : Atom} {c : Concept}
    (h : Concept.ex r c ∈ reqType I x s) :
    ∃ w, I.dom w ∧ I.rho x w = r ∧ c ∈ mty C0 I w :=
  mty_ex (reqType_sub_mty hs _ h)

/-- TERMINATION STEP: a demand a requirement node carries has an
    argument strictly shallower than `C₀` — the horizontal recursion's
    decreasing measure. -/
theorem reqType_ex_mdepth {x : α} {s : List Concept}
    (hs : ∀ F ∈ s, F ∈ cl C0) {r : Atom} {c : Concept}
    (h : Concept.ex r c ∈ reqType I x s) : mdepth c < mdepth C0 :=
  cl_ex_mdepth_lt (reqType_sub_cl hs _ h)

end Coverage

/-! ### The recursion measure (round 4, component 5)

The well-founded measure for the horizontal recursion: `lmd s` = the
maximum modal depth over a seed list.  This is where REQUIREMENT types
earn their keep — a demand step's child seed is `c :: fire(label, r)`,
every formula of which is a strict-subformula consequence of a
formula the node already carried, hence strictly shallower; so the
child's `lmd` is strictly smaller (`child_lmd_lt`).  With full model
types this would fail (a witness can satisfy fresh deep formulas); with
requirement types the measure genuinely descends. -/

section Measure

/-- The maximum modal depth in a seed list. -/
def lmd : List Concept → Nat
  | [] => 0
  | F :: t => Nat.max (mdepth F) (lmd t)

/-- Every seed is no deeper than the list maximum. -/
theorem mem_mdepth_le_lmd : ∀ (s : List Concept) F, F ∈ s → mdepth F ≤ lmd s := by
  intro s
  induction s with
  | nil => intro F hF; exact nomatch hF
  | cons G t ih =>
    intro F hF
    rcases List.mem_cons.mp hF with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih F h) (Nat.le_max_right _ _)

/-- If every seed is shallower than `n > 0`, so is the maximum. -/
theorem lmd_lt {n : Nat} (hn : 0 < n) :
    ∀ (s : List Concept), (∀ F ∈ s, mdepth F < n) → lmd s < n := by
  intro s
  induction s with
  | nil => intro _; exact hn
  | cons G t ih =>
    intro h
    have hG : mdepth G < n := h G (List.mem_cons_self)
    have ht : lmd t < n := ih (fun F hF => h F (List.mem_cons_of_mem G hF))
    exact Nat.max_lt.mpr ⟨hG, ht⟩

/-- The `≤` companion: if every seed is no deeper than `n`, neither is
    the maximum. -/
theorem lmd_le {n : Nat} :
    ∀ (s : List Concept), (∀ F ∈ s, mdepth F ≤ n) → lmd s ≤ n := by
  intro s
  induction s with
  | nil => intro _; exact Nat.zero_le n
  | cons G t ih =>
    intro h
    exact Nat.max_le.mpr ⟨h G List.mem_cons_self,
      ih (fun F hF => h F (List.mem_cons_of_mem G hF))⟩

end Measure

/-! ### The child seed and its measure decrease (round 4, component 6)

At a node labelled `reqType I x s` (seeds in `x`'s type, in `cl C₀`), a
demand `∃r.c` in the label spawns a child whose seed is
`childSeed x s r c = c :: fire (reqType I x s) r` — the demand's
argument plus the `∀r`-consequences fired across the new edge.  The
child seed is model-realizable at the demand's witness `w`
(`childSeed_sub_mty`), stays in the closure (`childSeed_sub_cl`), and —
the well-foundedness crux — has strictly smaller `lmd` than the parent
label (`child_lmd_lt`): every child seed formula is a strict-subformula
consequence of a formula the parent carried. -/

section ChildSeed

variable {α : Type} {I : Interp α} {C0 : Concept}

/-- The child seed spawned by a demand `∃r.c` at a `reqType` node. -/
noncomputable def childSeed (I : Interp α) (x : α) (s : List Concept)
    (r : Atom) (c : Concept) : List Concept :=
  c :: fire (reqType I x s) r

/-- The child seed is realized at the demand's witness `w` (which is an
    `r`-successor carrying `c`). -/
theorem childSeed_sub_mty {x w : α} {s : List Concept} {r : Atom}
    {c : Concept} (hs : ∀ F ∈ s, F ∈ mty C0 I x)
    (hw : I.dom w) (hrw : I.rho x w = r) (hc : c ∈ mty C0 I w) :
    ∀ F ∈ childSeed I x s r c, F ∈ mty C0 I w := by
  intro F hF
  rcases List.mem_cons.mp hF with rfl | h
  · exact hc
  · exact fire_sat (fun E hE => reqType_sub_mty hs E hE) hw hrw F h

/-- The child seed stays in the closure. -/
theorem childSeed_sub_cl {x : α} {s : List Concept} {r : Atom}
    {c : Concept} (hs : ∀ F ∈ s, F ∈ cl C0)
    (hc : c ∈ cl C0) : ∀ F ∈ childSeed I x s r c, F ∈ cl C0 := by
  intro F hF
  rcases List.mem_cons.mp hF with rfl | h
  · exact hc
  · exact fire_sub_cl (fun E hE => reqType_sub_cl hs E hE) F h

/-- THE WELL-FOUNDEDNESS CRUX: the child node's label is strictly
    shallower than the parent's.  Every child seed formula is a
    strict-subformula consequence of a formula the parent label carried,
    so its expansion — hence the child label's `lmd` — drops below the
    parent's. -/
theorem child_lmd_lt {x w : α} {s : List Concept} {r : Atom}
    {c : Concept} (hdem : Concept.ex r c ∈ reqType I x s) :
    lmd (reqType I w (childSeed I x s r c)) < lmd (reqType I x s) := by
  -- the parent label depth is positive (it carries `∃r.c`, depth ≥ 1)
  have hpos : 0 < lmd (reqType I x s) :=
    Nat.lt_of_lt_of_le
      (show 0 < mdepth (Concept.ex r c) from Nat.succ_pos _)
      (mem_mdepth_le_lmd _ _ hdem)
  -- every formula of the child label is strictly shallower than the parent max
  refine lmd_lt hpos _ (fun G hG => ?_)
  obtain ⟨F, hF, hGF⟩ := mem_reqType.mp hG
  -- `G` expands a child seed formula `F`; `mdepth G ≤ mdepth F`
  have hGle : mdepth G ≤ mdepth F :=
    cl_mdepth_le F G (expand_sub_cl I w F G hGF)
  -- and `mdepth F < lmd (reqType I x s)` in both child-seed cases
  have hFlt : mdepth F < lmd (reqType I x s) := by
    rcases List.mem_cons.mp hF with hFeq | hFfire
    · -- F = c : shallower than the demand `∃r.c`, which is in the label
      rw [hFeq]
      exact Nat.lt_of_lt_of_le (mdepth_ex_lt r c)
        (mem_mdepth_le_lmd _ _ hdem)
    · -- F ∈ fire : F = c'' from `∀r.c'' ∈ label`, shallower than it
      have hall : Concept.all r F ∈ reqType I x s := mem_fire.mp hFfire
      exact Nat.lt_of_lt_of_le (mdepth_all_lt r F)
        (mem_mdepth_le_lmd _ _ hall)
  exact Nat.lt_of_le_of_lt hGle hFlt

/-- REVERSE FIRING PRESERVES THE MEASURE (the termination key for the
    `∀DR`-saturation): a formula fired back from a `∃DR`-child's label is
    strictly shallower than the parent's label — it is a `∀DR`-argument
    (one level down) of a formula in the child's label, whose depth is
    already below the parent's (`child_lmd_lt`).  So absorbing the
    reverse `∀DR`-consequences of its children never raises a node's
    `lmd`; the saturation stays inside the same well-founded budget the
    recursion already descends on. -/
theorem revfire_lmd_lt {x w : α} {s : List Concept} {d : Concept}
    (hdem : Concept.ex dr d ∈ reqType I x s) {c : Concept}
    (hc : c ∈ fire (reqType I w (childSeed I x s dr d)) dr) :
    mdepth c < lmd (reqType I x s) := by
  have hall : Concept.all dr c ∈ reqType I w (childSeed I x s dr d) :=
    mem_fire.mp hc
  exact Nat.lt_of_lt_of_le (mdepth_all_lt dr c)
    (Nat.le_trans (mem_mdepth_le_lmd _ _ hall)
      (Nat.le_of_lt (child_lmd_lt hdem)))

end ChildSeed

/-! ### The horizontal recursion (round 4, component 7)

The global fixpoint for the HORIZONTAL part: a well-founded recursion
on `lmd` (component 6) that collects the finite set of requirement
nodes reachable from a root by demand-witnessing.  A node bundles its
model guide with the invariants the coverage step needs (`RNode`); a
demand spawns a child node at the demand's witness (`childNode`); and
`rnodes` unfolds the whole finite tree, terminating because every
child's label is strictly shallower (`child_lmd_lt`).

This is the vertical-free skeleton — no kernels yet; the recursion
descends only through the requirement structure, which is finite by
`lmd`.  Coverage (every demand routed to a node in the set) and the
block assembly are the next components. -/

/-- MODEL-SOUNDNESS OF REVERSE `DR`-FIRING (the safety property of the
    `∀DR`-closure that lifts past ∀-free): if `x DR w` and `∀DR.c` holds
    at `w`, then `c` holds at `x` — because `x` is itself a `DR`-neighbour
    of `w` (`conv DR = DR`).  So the formulas the reverse firing adds to
    a node are genuinely in its model type, keeping labels `⊆ mty`. -/
theorem dr_reverse_sat {α : Type} {I : Interp α} (hI : RCC5Interp I)
    {C0 : Concept} {x w : α} (hx : I.dom x) (hw : I.dom w)
    (hxw : I.rho x w = dr) {c : Concept}
    (h : Concept.all dr c ∈ mty C0 I w) : c ∈ mty C0 I x := by
  have hwx : I.rho w x = dr := by rw [hI.conv_ x w hx hw, hxw]; rfl
  exact mty_all h hx hwx

/-- REVERSE-FIRING PRESERVES `⊆ mty` (the fixpoint's step soundness):
    firing the `∀DR`-consequences of a `DR`-child's label back into the
    parent lands inside the parent's model type — so a label saturated
    under reverse `DR`-firing stays clash-free and model-realizable. -/
theorem fire_dr_reverse {α : Type} {I : Interp α} (hI : RCC5Interp I)
    {C0 : Concept} {x w : α} (hx : I.dom x) (hw : I.dom w)
    (hxw : I.rho x w = dr) {wlabel : List Concept}
    (hwlab : ∀ F ∈ wlabel, F ∈ mty C0 I w) :
    ∀ c ∈ fire wlabel dr, c ∈ mty C0 I x := by
  intro c hc
  exact dr_reverse_sat hI hx hw hxw (hwlab _ (mem_fire.mp hc))

/-- `noDR c`: `c` has no `∀DR` and no `∃DR` subformula.  The
    `∀DR`-arguments of a DR-GUARD-FREE concept satisfy it, which is what
    keeps the `slabel` reverse batch free of new `∀DR`/`∃DR` — so the two
    mosaic halves compose (see `ASSEMBLY_DESIGN.md §10`). -/
def noDR : Concept → Prop
  | .all dr _ => False
  | .ex dr _ => False
  | .all _ c => noDR c
  | .ex _ c => noDR c
  | .and c d => noDR c ∧ noDR d
  | .or c d => noDR c ∧ noDR d
  | _ => True

theorem noDR_cl_ex_aux {a : Concept} {r : Atom}
    (ih : noDR a → ∀ X, Concept.all dr X ∉ cl a ∧ Concept.ex dr X ∉ cl a)
    (hnd : noDR a) (hr : r ≠ dr) :
    ∀ X, Concept.all dr X ∉ cl (Concept.ex r a) ∧
      Concept.ex dr X ∉ cl (Concept.ex r a) := by
  intro X
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases List.mem_cons.mp h with h' | h'
    · exact Concept.noConfusion h'
    · exact (ih hnd X).1 h'
  · rcases List.mem_cons.mp h with h' | h'
    · injection h' with hr' _; exact hr hr'.symm
    · exact (ih hnd X).2 h'

theorem noDR_cl_all_aux {a : Concept} {r : Atom}
    (ih : noDR a → ∀ X, Concept.all dr X ∉ cl a ∧ Concept.ex dr X ∉ cl a)
    (hnd : noDR a) (hr : r ≠ dr) :
    ∀ X, Concept.all dr X ∉ cl (Concept.all r a) ∧
      Concept.ex dr X ∉ cl (Concept.all r a) := by
  intro X
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases List.mem_cons.mp h with h' | h'
    · injection h' with hr' _; exact hr hr'.symm
    · exact (ih hnd X).1 h'
  · rcases List.mem_cons.mp h with h' | h'
    · exact Concept.noConfusion h'
    · exact (ih hnd X).2 h'

/-- A `noDR` concept's subformula closure contains no `∀DR` and no
    `∃DR` — the fact the reconciliation lemmas need once the reverse
    batch is `expand`-closed (`ASSEMBLY_DESIGN.md §12`). -/
theorem noDR_cl : ∀ (e : Concept), noDR e →
    ∀ X, Concept.all dr X ∉ cl e ∧ Concept.ex dr X ∉ cl e := by
  intro e
  induction e with
  | top =>
    intro _ X
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      rcases List.mem_cons.mp h with h' | h' <;>
      first | exact Concept.noConfusion h' | exact nomatch h'
  | bot =>
    intro _ X
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      rcases List.mem_cons.mp h with h' | h' <;>
      first | exact Concept.noConfusion h' | exact nomatch h'
  | atom a =>
    intro _ X
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      rcases List.mem_cons.mp h with h' | h' <;>
      first | exact Concept.noConfusion h' | exact nomatch h'
  | natom a =>
    intro _ X
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      rcases List.mem_cons.mp h with h' | h' <;>
      first | exact Concept.noConfusion h' | exact nomatch h'
  | and a b iha ihb =>
    intro hnd X
    obtain ⟨ha, hb⟩ := hnd
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      rcases List.mem_cons.mp h with h' | h'
    · exact Concept.noConfusion h'
    · rcases List.mem_append.mp h' with hh | hh
      · exact (iha ha X).1 hh
      · exact (ihb hb X).1 hh
    · exact Concept.noConfusion h'
    · rcases List.mem_append.mp h' with hh | hh
      · exact (iha ha X).2 hh
      · exact (ihb hb X).2 hh
  | or a b iha ihb =>
    intro hnd X
    obtain ⟨ha, hb⟩ := hnd
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      rcases List.mem_cons.mp h with h' | h'
    · exact Concept.noConfusion h'
    · rcases List.mem_append.mp h' with hh | hh
      · exact (iha ha X).1 hh
      · exact (ihb hb X).1 hh
    · exact Concept.noConfusion h'
    · rcases List.mem_append.mp h' with hh | hh
      · exact (iha ha X).2 hh
      · exact (ihb hb X).2 hh
  | ex r a ih =>
    intro hnd X
    cases r with
    | dr => exact hnd.elim
    | eq => exact noDR_cl_ex_aux (r := eq) ih hnd (by decide) X
    | pp => exact noDR_cl_ex_aux (r := pp) ih hnd (by decide) X
    | ppi => exact noDR_cl_ex_aux (r := ppi) ih hnd (by decide) X
    | po => exact noDR_cl_ex_aux (r := po) ih hnd (by decide) X
  | all r a ih =>
    intro hnd X
    cases r with
    | dr => exact hnd.elim
    | eq => exact noDR_cl_all_aux (r := eq) ih hnd (by decide) X
    | pp => exact noDR_cl_all_aux (r := pp) ih hnd (by decide) X
    | ppi => exact noDR_cl_all_aux (r := ppi) ih hnd (by decide) X
    | po => exact noDR_cl_all_aux (r := po) ih hnd (by decide) X

section HorizontalRecursion

variable {α : Type} {I : Interp α} {C0 : Concept}

/-- A recursion node: a model guide with the invariants its label
    needs — inside the guide's type, and in the closure. -/
structure RNode (I : Interp α) (C0 : Concept) where
  x : α
  s : List Concept
  hdom : I.dom x
  hmty : ∀ F ∈ s, F ∈ mty C0 I x
  hcl : ∀ F ∈ s, F ∈ cl C0

/-- `RNode` extensionality: nodes are equal once guide and seed agree
    (the remaining fields are `Prop`s). -/
theorem RNode_ext (a b : RNode I C0) (hx : a.x = b.x) (hs : a.s = b.s) :
    a = b := by
  cases a; cases b; cases hx; cases hs; rfl

/-- The child node spawned by a demand `∃r.c` carried at `node`: its
    guide is the demand's model witness, its seed the child seed. -/
noncomputable def childNode (node : RNode I C0) {r : Atom} {c : Concept}
    (hdem : Concept.ex r c ∈ reqType I node.x node.s) : RNode I C0 :=
  let hw := Classical.choose_spec (reqType_ex_witness node.hmty hdem)
  { x := Classical.choose (reqType_ex_witness node.hmty hdem)
    s := childSeed I node.x node.s r c
    hdom := hw.1
    hmty := childSeed_sub_mty node.hmty hw.1 hw.2.1 hw.2.2
    hcl := childSeed_sub_cl node.hcl
      (cl_ex (reqType_sub_cl node.hcl _ hdem)) }

/-- THE HORIZONTAL RECURSION: the finite tree of requirement nodes
    reachable from `node` by demand-witnessing.  Terminates by
    `child_lmd_lt` (every child's label is strictly shallower). -/
noncomputable def rnodes (node : RNode I C0) : List (RNode I C0) :=
  node :: (reqType I node.x node.s).attach.flatMap
    (fun p => match p with
      | ⟨.ex r c, hF⟩ => rnodes (childNode node hF)
      | _ => [])
termination_by lmd (reqType I node.x node.s)
decreasing_by exact child_lmd_lt hF

/-- The root node is in its own reachable set. -/
theorem self_mem_rnodes (node : RNode I C0) : node ∈ rnodes node := by
  rw [rnodes]
  exact List.mem_cons_self

/-- A demand's whole child-subtree sits inside the parent's reachable
    set (from the unfolding — no induction). -/
theorem sub_rnodes_childNode (node : RNode I C0) {r : Atom} {c : Concept}
    (hF : Concept.ex r c ∈ reqType I node.x node.s) :
    ∀ k ∈ rnodes (childNode node hF), k ∈ rnodes node := by
  intro k hk
  rw [rnodes]
  refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr
    ⟨⟨Concept.ex r c, hF⟩, List.mem_attach _ _, ?_⟩)
  exact hk

/-- The child node itself is reachable. -/
theorem childNode_mem (node : RNode I C0) {r : Atom} {c : Concept}
    (hF : Concept.ex r c ∈ reqType I node.x node.s) :
    childNode node hF ∈ rnodes node :=
  sub_rnodes_childNode node hF _ (self_mem_rnodes _)

/-- TRANSITIVITY of reachability: the whole reachable subtree of any
    reachable node is reachable — by well-founded induction on the
    recursion (each child's label is strictly shallower). -/
theorem rnodes_trans (node : RNode I C0) :
    ∀ m ∈ rnodes node, ∀ k ∈ rnodes m, k ∈ rnodes node := by
  induction node using rnodes.induct with
  | _ x ih =>
    intro m hm k hk
    rw [rnodes] at hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact hk
    · obtain ⟨⟨F, hF⟩, _, hmm⟩ := List.mem_flatMap.mp hm'
      cases F with
      | ex r c =>
        exact sub_rnodes_childNode x hF k (ih r c hF m hmm k hk)
      | top => exact absurd hmm List.not_mem_nil
      | bot => exact absurd hmm List.not_mem_nil
      | atom a => exact absurd hmm List.not_mem_nil
      | natom a => exact absurd hmm List.not_mem_nil
      | and a b => exact absurd hmm List.not_mem_nil
      | or a b => exact absurd hmm List.not_mem_nil
      | all r c => exact absurd hmm List.not_mem_nil

/-- COVERAGE (the crux): every demand carried at any reachable node is
    fulfilled by a reachable node — its model witness, which realizes
    the demand's argument in its own label and is `r`-related to the
    demanding node. -/
theorem rnodes_covers (root : RNode I C0) :
    ∀ m ∈ rnodes root, ∀ (r : Atom) (c : Concept),
      Concept.ex r c ∈ reqType I m.x m.s →
      ∃ m' ∈ rnodes root, I.rho m.x m'.x = r ∧ c ∈ reqType I m'.x m'.s := by
  intro m hm r c hF
  refine ⟨childNode m hF, rnodes_trans root m hm _ (childNode_mem m hF),
    (Classical.choose_spec (reqType_ex_witness m.hmty hF)).2.1,
    mem_reqType_of_mem List.mem_cons_self⟩

/-- A demand's child is `r`-related to the demanding node in the model. -/
theorem childNode_rho (node : RNode I C0) {r : Atom} {c : Concept}
    (hF : Concept.ex r c ∈ reqType I node.x node.s) :
    I.rho node.x (childNode node hF).x = r :=
  (Classical.choose_spec (reqType_ex_witness node.hmty hF)).2.1

/-- THE REVERSE-`∀DR`-SATURATED LABEL: a node's requirement type plus
    the `∀DR`-consequences fired back from each of its `∃DR`-children
    (recursively saturated).  Terminates by `child_lmd_lt` (children
    are strictly shallower); by `revfire_lmd_lt` the fired formulas
    themselves stay within the node's `lmd` budget. -/
noncomputable def slabel (node : RNode I C0) : List Concept :=
  reqType I node.x node.s ++
  (reqType I node.x node.s).attach.flatMap
    (fun p => match p with
      | ⟨.ex dr d, hF⟩ =>
          (fire (slabel (childNode node hF)) dr).flatMap (expand I node.x)
      | _ => [])
termination_by lmd (reqType I node.x node.s)
decreasing_by exact child_lmd_lt hF

/-- The requirement type is contained in the saturated label. -/
theorem reqType_sub_slabel (node : RNode I C0) :
    ∀ F ∈ reqType I node.x node.s, F ∈ slabel node := by
  intro F hF
  rw [slabel]
  exact List.mem_append_left _ hF

/-- THE SATURATED LABEL IS MODEL-REALIZABLE: it stays inside the node's
    model type — `reqType` does (`hmty`), and each reverse-fired batch
    does by `fire_dr_reverse` (the child is a `DR`-neighbour), inducting
    on the saturation. -/
theorem slabel_sub_mty (hI : RCC5Interp I) (node : RNode I C0) :
    ∀ F ∈ slabel node, F ∈ mty C0 I node.x := by
  induction node using slabel.induct with
  | _ node ih =>
    intro F hF
    rw [slabel] at hF
    rcases List.mem_append.mp hF with h | h
    · exact reqType_sub_mty node.hmty F h
    · obtain ⟨⟨G, hG⟩, _, hFm⟩ := List.mem_flatMap.mp h
      cases G with
      | ex r d =>
        cases r with
        | dr =>
          obtain ⟨c, hc, hFc⟩ := List.mem_flatMap.mp hFm
          exact expand_sub_mty c
            (fire_dr_reverse hI node.hdom (childNode node hG).hdom
              (childNode_rho node hG) (ih d hG) c hc) F hFc
        | eq => exact absurd hFm List.not_mem_nil
        | pp => exact absurd hFm List.not_mem_nil
        | ppi => exact absurd hFm List.not_mem_nil
        | po => exact absurd hFm List.not_mem_nil
      | top => exact absurd hFm List.not_mem_nil
      | bot => exact absurd hFm List.not_mem_nil
      | atom a => exact absurd hFm List.not_mem_nil
      | natom a => exact absurd hFm List.not_mem_nil
      | and a b => exact absurd hFm List.not_mem_nil
      | or a b => exact absurd hFm List.not_mem_nil
      | all r a => exact absurd hFm List.not_mem_nil

/-- The saturated label stays in the closure — finite. -/
theorem slabel_sub_cl (node : RNode I C0) :
    ∀ F ∈ slabel node, F ∈ cl C0 := by
  induction node using slabel.induct with
  | _ node ih =>
    intro F hF
    rw [slabel] at hF
    rcases List.mem_append.mp hF with h | h
    · exact reqType_sub_cl node.hcl F h
    · obtain ⟨⟨G, hG⟩, _, hFm⟩ := List.mem_flatMap.mp h
      cases G with
      | ex r d =>
        cases r with
        | dr =>
          obtain ⟨c, hc, hFc⟩ := List.mem_flatMap.mp hFm
          exact expand_sub_cl_of (fire_sub_cl (ih d hG) c hc) F hFc
        | eq => exact absurd hFm List.not_mem_nil
        | pp => exact absurd hFm List.not_mem_nil
        | ppi => exact absurd hFm List.not_mem_nil
        | po => exact absurd hFm List.not_mem_nil
      | top => exact absurd hFm List.not_mem_nil
      | bot => exact absurd hFm List.not_mem_nil
      | atom a => exact absurd hFm List.not_mem_nil
      | natom a => exact absurd hFm List.not_mem_nil
      | and a b => exact absurd hFm List.not_mem_nil
      | or a b => exact absurd hFm List.not_mem_nil
      | all r a => exact absurd hFm List.not_mem_nil

/-- REVERSE `∀DR`-FIRING FROM THE SATURATED LABEL (the property `slabel`
    is built to satisfy): a `∀DR.c` obligation in a `∃DR`-child's
    saturated label puts its argument `c` in the PARENT's saturated
    label — the reverse `ee_all` on a `DR` demand edge, discharged by
    construction. -/
theorem slabel_reverse (node : RNode I C0) {d : Concept}
    (hF : Concept.ex dr d ∈ reqType I node.x node.s) {c : Concept}
    (h : Concept.all dr c ∈ slabel (childNode node hF)) :
    c ∈ slabel node := by
  rw [slabel]
  exact List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨⟨Concept.ex dr d, hF⟩, List.mem_attach _ _,
     List.mem_flatMap.mpr ⟨c, mem_fire.mpr h, mem_expand_self I node.x c⟩⟩)

/-- Membership in the reverse batch lands in the saturated label: an
    expansion `F ∈ expand node.x c'` of a reverse-fired formula
    `c' ∈ fire(slabel child, dr)` is a member of `slabel node`.  Factors
    the batch-reconstruction shared by the propositional-saturation
    lemmas below. -/
theorem slabel_batch_mem (node : RNode I C0) {d' : Concept}
    (hG : Concept.ex dr d' ∈ reqType I node.x node.s) {c' F : Concept}
    (hc' : c' ∈ fire (slabel (childNode node hG)) dr)
    (hF : F ∈ expand I node.x c') : F ∈ slabel node := by
  rw [slabel]
  exact List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨⟨Concept.ex dr d', hG⟩, List.mem_attach _ _,
     List.mem_flatMap.mpr ⟨c', hc', hF⟩⟩)

/-- Node condition `e_and` on the saturated label: `slabel` is closed
    under conjuncts.  `reqType` is (`reqType_and`), and each batch entry
    lives in an `expand node.x c'` which is (`expand_and`) — so the whole
    saturated label is propositionally conjunct-closed. -/
theorem slabel_and (node : RNode I C0) {c d : Concept}
    (h : Concept.and c d ∈ slabel node) :
    c ∈ slabel node ∧ d ∈ slabel node := by
  rw [slabel] at h
  rcases List.mem_append.mp h with h1 | h2
  · obtain ⟨hc, hd⟩ := reqType_and h1
    exact ⟨reqType_sub_slabel node c hc, reqType_sub_slabel node d hd⟩
  · obtain ⟨⟨G, hG⟩, _, hFm⟩ := List.mem_flatMap.mp h2
    cases G with
    | ex r d' =>
      cases r with
      | dr =>
        obtain ⟨c', hc', hcc⟩ := List.mem_flatMap.mp hFm
        obtain ⟨hce, hde⟩ := expand_and I node.x c' c d hcc
        exact ⟨slabel_batch_mem node hG hc' hce,
               slabel_batch_mem node hG hc' hde⟩
      | eq => exact absurd hFm List.not_mem_nil
      | pp => exact absurd hFm List.not_mem_nil
      | ppi => exact absurd hFm List.not_mem_nil
      | po => exact absurd hFm List.not_mem_nil
    | top => exact absurd hFm List.not_mem_nil
    | bot => exact absurd hFm List.not_mem_nil
    | atom a => exact absurd hFm List.not_mem_nil
    | natom a => exact absurd hFm List.not_mem_nil
    | and a b => exact absurd hFm List.not_mem_nil
    | or a b => exact absurd hFm List.not_mem_nil
    | all r a => exact absurd hFm List.not_mem_nil

/-- Node condition `e_or` on the saturated label: `slabel` resolves every
    disjunction (some disjunct is present).  `reqType_or` on the type
    part, `expand_or` on each batch entry. -/
theorem slabel_or (node : RNode I C0) {c d : Concept}
    (h : Concept.or c d ∈ slabel node) :
    c ∈ slabel node ∨ d ∈ slabel node := by
  rw [slabel] at h
  rcases List.mem_append.mp h with h1 | h2
  · rcases reqType_or h1 with hc | hd
    · exact Or.inl (reqType_sub_slabel node c hc)
    · exact Or.inr (reqType_sub_slabel node d hd)
  · obtain ⟨⟨G, hG⟩, _, hFm⟩ := List.mem_flatMap.mp h2
    cases G with
    | ex r d' =>
      cases r with
      | dr =>
        obtain ⟨c', hc', hcc⟩ := List.mem_flatMap.mp hFm
        rcases expand_or I node.x c' c d hcc with hce | hde
        · exact Or.inl (slabel_batch_mem node hG hc' hce)
        · exact Or.inr (slabel_batch_mem node hG hc' hde)
      | eq => exact absurd hFm List.not_mem_nil
      | pp => exact absurd hFm List.not_mem_nil
      | ppi => exact absurd hFm List.not_mem_nil
      | po => exact absurd hFm List.not_mem_nil
    | top => exact absurd hFm List.not_mem_nil
    | bot => exact absurd hFm List.not_mem_nil
    | atom a => exact absurd hFm List.not_mem_nil
    | natom a => exact absurd hFm List.not_mem_nil
    | and a b => exact absurd hFm List.not_mem_nil
    | or a b => exact absurd hFm List.not_mem_nil
    | all r a => exact absurd hFm List.not_mem_nil

/-- Node condition `e_clash` on the saturated label: no atom/negated-atom
    clash — inherited from `mty` (`slabel ⊆ mty`, `mty_clash`). -/
theorem slabel_clash (hI : RCC5Interp I) (node : RNode I C0) {a : Nat}
    (h : Concept.atom a ∈ slabel node) :
    Concept.natom a ∉ slabel node :=
  fun h2 => mty_clash (slabel_sub_mty hI node _ h) (slabel_sub_mty hI node _ h2)

/-- Node condition `e_nobot` on the saturated label: `⊥` absent —
    inherited from `mty` (`slabel ⊆ mty`, `mty_nobot`). -/
theorem slabel_nobot (hI : RCC5Interp I) (node : RNode I C0) :
    Concept.bot ∉ slabel node :=
  fun h => mty_nobot (slabel_sub_mty hI node _ h)

/-- FORWARD `∀DR`-FIRING FROM THE REQUIREMENT TYPE: a `∀DR.c` obligation
    in a node's REQUIREMENT type puts its argument into every
    `∃DR`-child's (saturated) label — the forward `ee_all` for the
    directly-required universals (`c` lands in the child's seed via
    `fire`). -/
theorem slabel_forward_reqType (node : RNode I C0) {d : Concept}
    (hF : Concept.ex dr d ∈ reqType I node.x node.s) {c : Concept}
    (h : Concept.all dr c ∈ reqType I node.x node.s) :
    c ∈ slabel (childNode node hF) := by
  have h2 : c ∈ (childNode node hF).s :=
    List.mem_cons_of_mem d (mem_fire.mpr h)
  exact reqType_sub_slabel (childNode node hF) c
    (mem_reqType_of_mem (x := (childNode node hF).x) h2)

/-- Every saturated-label formula is no deeper than the node's
    requirement-type `lmd` — the reverse batch stays shallow
    (`revfire_lmd_lt`, recursively). -/
theorem slabel_mdepth_le (node : RNode I C0) :
    ∀ F ∈ slabel node, mdepth F ≤ lmd (reqType I node.x node.s) := by
  induction node using slabel.induct with
  | _ node ih =>
    intro F hF
    rw [slabel] at hF
    rcases List.mem_append.mp hF with h | h
    · exact mem_mdepth_le_lmd _ _ h
    · obtain ⟨⟨G, hG⟩, _, hFm⟩ := List.mem_flatMap.mp h
      cases G with
      | ex r d =>
        cases r with
        | dr =>
          obtain ⟨c, hc, hFc⟩ := List.mem_flatMap.mp hFm
          have hall : Concept.all dr c ∈ slabel (childNode node hG) :=
            mem_fire.mp hc
          exact Nat.le_of_lt (Nat.lt_of_le_of_lt
            (cl_mdepth_le c F (expand_sub_cl I node.x c F hFc))
            (Nat.lt_of_lt_of_le (mdepth_all_lt dr c)
              (Nat.le_trans (ih d hG _ hall)
                (Nat.le_of_lt (child_lmd_lt hG)))))
        | eq => exact absurd hFm List.not_mem_nil
        | pp => exact absurd hFm List.not_mem_nil
        | ppi => exact absurd hFm List.not_mem_nil
        | po => exact absurd hFm List.not_mem_nil
      | top => exact absurd hFm List.not_mem_nil
      | bot => exact absurd hFm List.not_mem_nil
      | atom a => exact absurd hFm List.not_mem_nil
      | natom a => exact absurd hFm List.not_mem_nil
      | and a b => exact absurd hFm List.not_mem_nil
      | or a b => exact absurd hFm List.not_mem_nil
      | all r a => exact absurd hFm List.not_mem_nil

/-- The saturated label's `lmd` does not exceed the requirement type's —
    saturation stays inside the recursion's well-founded budget. -/
theorem slabel_lmd_le (node : RNode I C0) :
    lmd (slabel node) ≤ lmd (reqType I node.x node.s) :=
  lmd_le (slabel node) (slabel_mdepth_le node)

/-- THE RECONCILIATION LEMMA (`ASSEMBLY_DESIGN.md §10`): in a
    DR-guard-free concept (`∀DR.c ∈ cl C₀ ⟹ noDR c`) the saturated
    label's `∀DR` obligations are exactly the requirement type's — the
    reverse batch carries no `∀DR` (a `∀DR` there would come from
    `∀DR.(∀DR c) ∈ cl C₀`, forbidden).  This is what makes the frame's
    `DR` edges (`schildNode`, firing from `slabel`) coincide with the
    ones `slabel_reverse` fires reverse from (`childNode`, firing from
    `reqType`): `fire(slabel,dr) = fire(reqType,dr)` on members. -/
theorem slabel_alldr_reqType
    (hgf : ∀ c, Concept.all dr c ∈ cl C0 → noDR c)
    (node : RNode I C0) {c : Concept}
    (h : Concept.all dr c ∈ slabel node) :
    Concept.all dr c ∈ reqType I node.x node.s := by
  rw [slabel] at h
  rcases List.mem_append.mp h with h1 | h2
  · exact h1
  · exfalso
    obtain ⟨⟨G, hG⟩, _, hFm⟩ := List.mem_flatMap.mp h2
    cases G with
    | ex r d =>
      cases r with
      | dr =>
        obtain ⟨c', hc', hcc⟩ := List.mem_flatMap.mp hFm
        have hall : Concept.all dr c' ∈ slabel (childNode node hG) :=
          mem_fire.mp hc'
        exact (noDR_cl c' (hgf c' (slabel_sub_cl _ _ hall)) c).1
          (expand_sub_cl I node.x c' _ hcc)
      | eq => exact absurd hFm List.not_mem_nil
      | pp => exact absurd hFm List.not_mem_nil
      | ppi => exact absurd hFm List.not_mem_nil
      | po => exact absurd hFm List.not_mem_nil
    | top => exact absurd hFm List.not_mem_nil
    | bot => exact absurd hFm List.not_mem_nil
    | atom a => exact absurd hFm List.not_mem_nil
    | natom a => exact absurd hFm List.not_mem_nil
    | and a b => exact absurd hFm List.not_mem_nil
    | or a b => exact absurd hFm List.not_mem_nil
    | all r a => exact absurd hFm List.not_mem_nil

/-- The `∃DR` analogue: saturation adds no new `DR` DEMANDS in a
    DR-guard-free concept — so the saturated-label `DR` demands are the
    requirement-type ones, and `snodes`' `DR` children are `rnodes`'
    (`schildNode = childNode`). -/
theorem slabel_exdr_reqType
    (hgf : ∀ c, Concept.all dr c ∈ cl C0 → noDR c)
    (node : RNode I C0) {d : Concept}
    (h : Concept.ex dr d ∈ slabel node) :
    Concept.ex dr d ∈ reqType I node.x node.s := by
  rw [slabel] at h
  rcases List.mem_append.mp h with h1 | h2
  · exact h1
  · exfalso
    obtain ⟨⟨G, hG⟩, _, hFm⟩ := List.mem_flatMap.mp h2
    cases G with
    | ex r d' =>
      cases r with
      | dr =>
        obtain ⟨c', hc', hcc⟩ := List.mem_flatMap.mp hFm
        have hall : Concept.all dr c' ∈ slabel (childNode node hG) :=
          mem_fire.mp hc'
        exact (noDR_cl c' (hgf c' (slabel_sub_cl _ _ hall)) d).2
          (expand_sub_cl I node.x c' _ hcc)
      | eq => exact absurd hFm List.not_mem_nil
      | pp => exact absurd hFm List.not_mem_nil
      | ppi => exact absurd hFm List.not_mem_nil
      | po => exact absurd hFm List.not_mem_nil
    | top => exact absurd hFm List.not_mem_nil
    | bot => exact absurd hFm List.not_mem_nil
    | atom a => exact absurd hFm List.not_mem_nil
    | natom a => exact absurd hFm List.not_mem_nil
    | and a b => exact absurd hFm List.not_mem_nil
    | or a b => exact absurd hFm List.not_mem_nil
    | all r a => exact absurd hFm List.not_mem_nil

/-! ### The saturated-label coverage recursion (`snodes`)

`rnodes` covers the demands of a node's REQUIREMENT type; saturation
(`slabel`) adds `∀DR`-consequences that may themselves be demands, so
the full mosaic needs a recursion covering the demands of the SATURATED
label.  `snodes` is that recursion — a parallel of `rnodes` over
`slabel` instead of `reqType`, terminating by the SAME `lmd` measure
because saturation stays inside the budget (`slabel_lmd_le`,
`schild_lmd_lt`). -/

/-- The child node covering a demand carried in the SATURATED label:
    guide = the demand's model witness (`slabel ⊆ mty`), seed = the
    demand's argument plus the `∀`-consequences fired forward from the
    saturated label. -/
noncomputable def schildNode (hI : RCC5Interp I) (node : RNode I C0)
    {r : Atom} {c : Concept} (hF : Concept.ex r c ∈ slabel node) :
    RNode I C0 :=
  let hw := Classical.choose_spec (mty_ex (slabel_sub_mty hI node _ hF))
  { x := Classical.choose (mty_ex (slabel_sub_mty hI node _ hF))
    s := c :: fire (reqType I node.x node.s) r
    hdom := hw.1
    hmty := by
      intro F hFm
      rcases List.mem_cons.mp hFm with rfl | h
      · exact hw.2.2
      · exact fire_sat (reqType_sub_mty node.hmty) hw.1 hw.2.1 F h
    hcl := by
      intro F hFm
      rcases List.mem_cons.mp hFm with rfl | h
      · exact cl_ex (slabel_sub_cl node _ hF)
      · exact fire_sub_cl (reqType_sub_cl node.hcl) F h }

/-- The saturated-label child is `r`-related to its node in the model. -/
theorem schildNode_rho (hI : RCC5Interp I) (node : RNode I C0)
    {r : Atom} {c : Concept} (hF : Concept.ex r c ∈ slabel node) :
    I.rho node.x (schildNode hI node hF).x = r :=
  (Classical.choose_spec (mty_ex (slabel_sub_mty hI node _ hF))).2.1

/-- The saturated-label child's argument lands in its own label. -/
theorem schildNode_arg (hI : RCC5Interp I) (node : RNode I C0)
    {r : Atom} {c : Concept} (hF : Concept.ex r c ∈ slabel node) :
    c ∈ slabel (schildNode hI node hF) :=
  reqType_sub_slabel _ c
    (mem_reqType_of_mem (x := (schildNode hI node hF).x) List.mem_cons_self)

/-- ON `∃DR` DEMANDS, THE SATURATED-LABEL CHILD IS THE REQUIREMENT-TYPE
    CHILD (under DR-guard-freeness): same seed (`d :: fire(reqType,dr)`,
    since `∃DR.d ∈ slabel ⟹ ∈ reqType` by `slabel_exdr_reqType`) and same
    witness (`Classical.choose` of `mty_ex` of the same proposition, by
    proof irrelevance).  So `slabel_reverse` (about `childNode`) is the
    reverse `ee_all` for the frame's `DR` edges (`schildNode`). -/
theorem schildNode_eq_childNode
    (hgf : ∀ c, Concept.all dr c ∈ cl C0 → noDR c) (hI : RCC5Interp I)
    (node : RNode I C0) {d : Concept}
    (hF : Concept.ex dr d ∈ slabel node) :
    schildNode hI node hF = childNode node (slabel_exdr_reqType hgf node hF) :=
  RNode_ext _ _ (congrArg Classical.choose (proof_irrel _ _)) rfl

/-- FORWARD `ee_all` ON A FRAME `DR` EDGE: `∀DR.c` in a node's saturated
    label puts `c` in its `∃DR`-child's saturated label — via
    `slabel_alldr_reqType` (`slabel`'s `∀DR` = `reqType`'s) then
    `slabel_forward_reqType`, on the `= childNode` frame edge. -/
theorem slabel_dr_forward (hgf : ∀ c, Concept.all dr c ∈ cl C0 → noDR c)
    (hI : RCC5Interp I) (node : RNode I C0) {d : Concept}
    (hF : Concept.ex dr d ∈ slabel node) {c : Concept}
    (h : Concept.all dr c ∈ slabel node) :
    c ∈ slabel (schildNode hI node hF) := by
  rw [schildNode_eq_childNode hgf hI node hF]
  exact slabel_forward_reqType node (slabel_exdr_reqType hgf node hF)
    (slabel_alldr_reqType hgf node h)

/-- REVERSE `ee_all` ON A FRAME `DR` EDGE: `∀DR.c` in an `∃DR`-child's
    saturated label puts `c` in the parent's — `slabel_reverse` on the
    `= childNode` frame edge.  (The hard direction, now for `snodes`.) -/
theorem slabel_dr_reverse (hgf : ∀ c, Concept.all dr c ∈ cl C0 → noDR c)
    (hI : RCC5Interp I) (node : RNode I C0) {d : Concept}
    (hF : Concept.ex dr d ∈ slabel node) {c : Concept}
    (h : Concept.all dr c ∈ slabel (schildNode hI node hF)) :
    c ∈ slabel node := by
  rw [schildNode_eq_childNode hgf hI node hF] at h
  exact slabel_reverse node (slabel_exdr_reqType hgf node hF) h

/-- Termination for `snodes`: the saturated-label child is strictly
    shallower — its argument and forward-fired formulas are below the
    node's `lmd` (`slabel_lmd_le`). -/
theorem schild_lmd_lt (node : RNode I C0) {w : α} {r : Atom} {c : Concept}
    (hdem : Concept.ex r c ∈ slabel node) :
    lmd (reqType I w (c :: fire (reqType I node.x node.s) r)) <
      lmd (reqType I node.x node.s) := by
  have hpos : 0 < lmd (reqType I node.x node.s) :=
    Nat.lt_of_lt_of_le (show 0 < mdepth (Concept.ex r c) from Nat.succ_pos _)
      (Nat.le_trans (mem_mdepth_le_lmd _ _ hdem) (slabel_lmd_le node))
  refine lmd_lt hpos _ (fun G hG => ?_)
  obtain ⟨F, hF, hGF⟩ := mem_reqType.mp hG
  have hGle : mdepth G ≤ mdepth F := cl_mdepth_le F G (expand_sub_cl I w F G hGF)
  have hFlt : mdepth F < lmd (reqType I node.x node.s) := by
    rcases List.mem_cons.mp hF with hFeq | hFfire
    · rw [hFeq]
      exact Nat.lt_of_lt_of_le (mdepth_ex_lt r c)
        (Nat.le_trans (mem_mdepth_le_lmd _ _ hdem) (slabel_lmd_le node))
    · have hall : Concept.all r F ∈ reqType I node.x node.s :=
        mem_fire.mp hFfire
      exact Nat.lt_of_lt_of_le (mdepth_all_lt r F) (mem_mdepth_le_lmd _ _ hall)
  exact Nat.lt_of_le_of_lt hGle hFlt

/-- THE SATURATED-LABEL COVERAGE RECURSION: the finite set of nodes
    reachable by covering the demands of the SATURATED labels. -/
noncomputable def snodes (hI : RCC5Interp I) (node : RNode I C0) :
    List (RNode I C0) :=
  node :: (slabel node).attach.flatMap
    (fun p => match p with
      | ⟨.ex r c, hF⟩ => snodes hI (schildNode hI node hF)
      | _ => [])
termination_by lmd (reqType I node.x node.s)
decreasing_by exact schild_lmd_lt node hF

theorem self_mem_snodes (hI : RCC5Interp I) (node : RNode I C0) :
    node ∈ snodes hI node := by
  rw [snodes]; exact List.mem_cons_self

theorem sub_snodes_schildNode (hI : RCC5Interp I) (node : RNode I C0)
    {r : Atom} {c : Concept} (hF : Concept.ex r c ∈ slabel node) :
    ∀ k ∈ snodes hI (schildNode hI node hF), k ∈ snodes hI node := by
  intro k hk
  rw [snodes]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
    ⟨⟨Concept.ex r c, hF⟩, List.mem_attach _ _, hk⟩)

theorem schildNode_mem (hI : RCC5Interp I) (node : RNode I C0)
    {r : Atom} {c : Concept} (hF : Concept.ex r c ∈ slabel node) :
    schildNode hI node hF ∈ snodes hI node :=
  sub_snodes_schildNode hI node hF _ (self_mem_snodes hI _)

theorem snodes_trans (hI : RCC5Interp I) (node : RNode I C0) :
    ∀ m ∈ snodes hI node, ∀ k ∈ snodes hI m, k ∈ snodes hI node := by
  induction node using snodes.induct (hI := hI) with
  | _ x ih =>
    intro m hm k hk
    rw [snodes] at hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact hk
    · obtain ⟨⟨F, hF⟩, _, hmm⟩ := List.mem_flatMap.mp hm'
      cases F with
      | ex r c =>
        exact sub_snodes_schildNode hI x hF k (ih r c hF m hmm k hk)
      | top => exact absurd hmm List.not_mem_nil
      | bot => exact absurd hmm List.not_mem_nil
      | atom a => exact absurd hmm List.not_mem_nil
      | natom a => exact absurd hmm List.not_mem_nil
      | and a b => exact absurd hmm List.not_mem_nil
      | or a b => exact absurd hmm List.not_mem_nil
      | all r c => exact absurd hmm List.not_mem_nil

/-- SATURATED-LABEL COVERAGE: every demand carried at any reachable
    node's SATURATED label is fulfilled by a reachable node. -/
theorem snodes_covers (hI : RCC5Interp I) (root : RNode I C0) :
    ∀ m ∈ snodes hI root, ∀ (r : Atom) (c : Concept),
      Concept.ex r c ∈ slabel m →
      ∃ m' ∈ snodes hI root, I.rho m.x m'.x = r ∧ c ∈ slabel m' := by
  intro m hm r c hF
  exact ⟨schildNode hI m hF,
    snodes_trans hI root m hm _ (schildNode_mem hI m hF),
    schildNode_rho hI m hF, schildNode_arg hI m hF⟩

end HorizontalRecursion

/-! ### The ∀-free fragment: `∀`-conditions vacuous (round 4, component 9)

For the ∀-FREE sub-fragment (no universal anywhere — a fortiori
∀PO-free), a node's requirement label carries NO `∀` obligation, so
every universal-propagation condition of `MultiTierOk`
(`ee_all`/`ek_all`/`ke_all`/`kk_*`) is VACUOUS.  Combined with the
read-off frame (any relation, valid by `readoff_frame`) and `e_ex` =
coverage, this is the fragment the horizontal recursion assembles into
a certificate with no `∀`-firing bookkeeping and no kernels. -/

section AllFree

/-- No universal subformula.  STRICTLY STRONGER than `POFree` (which
    bans only `∀PO`): `AllFree` bans EVERY universal (`∀PO`/`∀DR`/`∀PP`/
    `∀PPI`/`∀EQ`).  So the ∀-free fragment is a PROPER sub-fragment of
    the ∀PO-free target — see `allfree_imp_pofree`. -/
def AllFree : Concept → Prop
  | .all _ _ => False
  | .and c d => AllFree c ∧ AllFree d
  | .or c d => AllFree c ∧ AllFree d
  | .ex _ c => AllFree c
  | _ => True

/-- The ∀-free fragment is contained in the ∀PO-free fragment
    (∀-free ⟹ ∀PO-free; the converse fails — e.g. `∀DR.A` is ∀PO-free
    but not ∀-free). -/
theorem allfree_imp_pofree : ∀ c : Concept, AllFree c → POFree c := by
  intro c
  induction c with
  | top => intro _; trivial
  | bot => intro _; trivial
  | atom a => intro _; trivial
  | natom a => intro _; trivial
  | and a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
  | or a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
  | ex r a iha => intro h; exact iha h
  | all r a iha => intro h; exact h.elim

/-- A ∀-free concept's closure contains no universal. -/
theorem allfree_cl_no_all : ∀ e : Concept, AllFree e →
    ∀ (r : Atom) (c : Concept), Concept.all r c ∉ cl e := by
  intro e
  induction e with
  | top =>
    intro _ r c hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact Concept.noConfusion h
    · exact nomatch h
  | bot =>
    intro _ r c hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact Concept.noConfusion h
    · exact nomatch h
  | atom a =>
    intro _ r c hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact Concept.noConfusion h
    · exact nomatch h
  | natom a =>
    intro _ r c hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact Concept.noConfusion h
    · exact nomatch h
  | and a b iha ihb =>
    intro haf r c hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact Concept.noConfusion h
    · rcases List.mem_append.mp h with h' | h'
      · exact iha haf.1 r c h'
      · exact ihb haf.2 r c h'
  | or a b iha ihb =>
    intro haf r c hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact Concept.noConfusion h
    · rcases List.mem_append.mp h with h' | h'
      · exact iha haf.1 r c h'
      · exact ihb haf.2 r c h'
  | ex r' a iha =>
    intro haf r c hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact Concept.noConfusion h
    · exact iha haf r c h
  | all r' a iha =>
    intro haf r c hmem
    exact haf

/-- A ∀-free concept's model types carry no universal. -/
theorem allfree_mty_no_all {C0 : Concept} (haf : AllFree C0) {α : Type}
    {I : Interp α} {x : α} {r : Atom} {c : Concept} :
    Concept.all r c ∉ mty C0 I x :=
  fun h => allfree_cl_no_all C0 haf r c (mty_sub _ h)

/-- A ∀-free concept's requirement labels carry no universal. -/
theorem allfree_reqType_no_all {C0 : Concept} (haf : AllFree C0)
    {α : Type} {I : Interp α} {x : α} {s : List Concept}
    (hs : ∀ F ∈ s, F ∈ cl C0) {r : Atom} {c : Concept} :
    Concept.all r c ∉ reqType I x s :=
  fun h => allfree_cl_no_all C0 haf r c (reqType_sub_cl hs _ h)

end AllFree

/-! ### The ∀-free block assembly (round 4, component 10)

Turning the reachable node set into a certificate.  Same-guide nodes
are MERGED (`mlabel` — a guide's label is the union of the requirement
labels of all reachable nodes carrying that guide), so the read-off
frame's strong-EQ holds (distinct guides, never `EQ` off-diagonal).
The merged label inherits every propositional block-node fact from the
per-node requirement labels, and — for the ∀-free fragment — carries no
universal (`mlabel_no_all`), so the universal conditions are vacuous. -/

section AllFreeAssembly

open Classical

variable {α : Type} {I : Interp α} {C0 : Concept}

/-- The guide values of the reachable node set. -/
noncomputable def guides (root : RNode I C0) : List α :=
  (rnodes root).map (·.x)

/-- The merged label of a guide: the union of the requirement labels of
    all reachable nodes carrying it. -/
noncomputable def mlabel (root : RNode I C0) (g : α) : List Concept :=
  (rnodes root).flatMap (fun m => if m.x = g then reqType I m.x m.s else [])

theorem mem_mlabel {root : RNode I C0} {g : α} {F : Concept} :
    F ∈ mlabel root g ↔
      ∃ m ∈ rnodes root, m.x = g ∧ F ∈ reqType I m.x m.s := by
  rw [mlabel, List.mem_flatMap]
  constructor
  · rintro ⟨m, hm, hF⟩
    by_cases h : m.x = g
    · rw [if_pos h] at hF; exact ⟨m, hm, h, hF⟩
    · rw [if_neg h] at hF; exact absurd hF List.not_mem_nil
  · rintro ⟨m, hm, hxg, hF⟩
    exact ⟨m, hm, by rw [if_pos hxg]; exact hF⟩

/-- The merged label is model-realizable at its guide. -/
theorem mlabel_sub_mty {root : RNode I C0} {g : α} :
    ∀ F ∈ mlabel root g, F ∈ mty C0 I g := by
  intro F hF
  obtain ⟨m, _, hxg, hFr⟩ := mem_mlabel.mp hF
  rw [← hxg]
  exact reqType_sub_mty m.hmty F hFr

/-- Node condition `e_clash`. -/
theorem mlabel_clash {root : RNode I C0} {g : α} {a : Nat}
    (h : Concept.atom a ∈ mlabel root g) :
    Concept.natom a ∉ mlabel root g :=
  fun h2 => mty_clash (mlabel_sub_mty _ h) (mlabel_sub_mty _ h2)

/-- Node condition `e_nobot`. -/
theorem mlabel_nobot {root : RNode I C0} {g : α} :
    Concept.bot ∉ mlabel root g :=
  fun h => mty_nobot (mlabel_sub_mty _ h)

/-- Node condition `e_and`. -/
theorem mlabel_and {root : RNode I C0} {g : α} {c d : Concept}
    (h : Concept.and c d ∈ mlabel root g) :
    c ∈ mlabel root g ∧ d ∈ mlabel root g := by
  obtain ⟨m, hm, hxg, hF⟩ := mem_mlabel.mp h
  obtain ⟨hc, hd⟩ := reqType_and hF
  exact ⟨mem_mlabel.mpr ⟨m, hm, hxg, hc⟩, mem_mlabel.mpr ⟨m, hm, hxg, hd⟩⟩

/-- Node condition `e_or`. -/
theorem mlabel_or {root : RNode I C0} {g : α} {c d : Concept}
    (h : Concept.or c d ∈ mlabel root g) :
    c ∈ mlabel root g ∨ d ∈ mlabel root g := by
  obtain ⟨m, hm, hxg, hF⟩ := mem_mlabel.mp h
  rcases reqType_or hF with hc | hd
  · exact Or.inl (mem_mlabel.mpr ⟨m, hm, hxg, hc⟩)
  · exact Or.inr (mem_mlabel.mpr ⟨m, hm, hxg, hd⟩)

/-- For the ∀-free fragment: the merged label carries no universal. -/
theorem mlabel_no_all (haf : AllFree C0) {root : RNode I C0} {g : α}
    {r : Atom} {c : Concept} : Concept.all r c ∉ mlabel root g := by
  intro h
  obtain ⟨m, _, _, hF⟩ := mem_mlabel.mp h
  exact allfree_reqType_no_all haf m.hcl hF

/-- Guides are in the domain. -/
theorem guide_dom {root : RNode I C0} {g : α} (hg : g ∈ guides root) :
    I.dom g := by
  obtain ⟨m, hm, hmx⟩ := List.mem_map.mp hg
  rw [← hmx]; exact m.hdom

/-- The certificate index type: one node per distinct guide. -/
abbrev GB (root : RNode I C0) : Type := { x : α // x ∈ guides root }

/-- THE ∀-FREE CERTIFICATE: externals = distinct guides, read-off
    relations, merged requirement labels; no kernels. -/
noncomputable def mtVF (root : RNode I C0) : MultiTier (GB root) Empty where
  E g g' := I.rho g.val g'.val
  K k _ := k.elim
  Q k _ := k.elim
  up k := k.elim
  tauE g := mlabel root g.val
  p k := k.elim
  phase k _ := k.elim

/-- The certificate's frame is a genuine RCC5 frame (read-off at
    distinct guides). -/
theorem mtVF_frame (hI : RCC5Interp I) (root : RNode I C0) :
    Frame (qnet (mtVF root).E (mtVF root).K (mtVF root).Q) := by
  refine frame_ext (fun x y => ?_)
    (readoff_qnet_frame hI (κ := Empty) (Subtype.val) (fun k => k.elim)
      (fun g => guide_dom g.2) (fun k => k.elim)
      (fun v w hvw => by
        rcases v with g | k
        · rcases w with g' | k'
          · exact congrArg Sum.inl (Subtype.ext hvw)
          · exact k'.elim
        · exact k.elim))
  rcases x with g | k
  · rcases y with g' | k'
    · rfl
    · exact k'.elim
  · exact k.elim

/-- THE ∀-FREE CERTIFICATE IS VALID: `MultiTierOk (mtVF root)`.  The
    universal conditions are vacuous (∀-free); the propositional
    conditions come from the merged label; `e_ex` is exactly coverage
    (`rnodes_covers`). -/
theorem mtVF_ok (hI : RCC5Interp I) (haf : AllFree C0)
    (root : RNode I C0) : MultiTierOk (mtVF root) where
  hp := fun k => k.elim
  frame_q := mtVF_frame hI root
  e_clash := fun _ _ h => mlabel_clash h
  e_nobot := fun _ => mlabel_nobot
  e_and := fun _ c d h => mlabel_and h
  e_or := fun _ c d h => mlabel_or h
  k_clash := fun k => k.elim
  k_nobot := fun k => k.elim
  k_and := fun k => k.elim
  k_or := fun k => k.elim
  ee_all := fun _ _ r c h => absurd h (mlabel_no_all haf)
  ek_all := fun _ r c h => absurd h (mlabel_no_all haf)
  ke_all := fun k => k.elim
  kk_pp := fun k => k.elim
  kk_ppi := fun k => k.elim
  kk_eq := fun k => k.elim
  kq_all := fun k => k.elim
  e_ex := by
    intro g r c hdem
    obtain ⟨m, hm, hxg, hFr⟩ := mem_mlabel.mp hdem
    have hdem' : Concept.ex r c ∈ reqType I m.x m.s := hFr
    obtain ⟨m', hm', hrho, hc⟩ := rnodes_covers root m hm r c hdem'
    refine Or.inl ⟨⟨m'.x, List.mem_map.mpr ⟨m', hm', rfl⟩⟩, ?_, ?_⟩
    · show I.rho g.val m'.x = r
      rw [← hxg]; exact hrho
    · exact mem_mlabel.mpr ⟨m', hm', rfl, hc⟩
  k_ex := fun k => k.elim

end AllFreeAssembly

/-- THE ∀-FREE EXTRACTION (the completeness capstone): every satisfiable
    ∀-free concept has a VALID FINITE multi-tier certificate carrying it
    — built by the horizontal recursion, its `e_ex` discharged by
    coverage.  Together with the certified soundness pipeline
    (`multiTier_sound`) this makes ∀-free satisfiability equivalent to
    the existence of such a certificate. -/
theorem extract_allfree (C0 : Concept) (haf : AllFree C0)
    (hsat : Satisfiable C0) :
    ∃ (β : Type) (T : MultiTier β Empty) (g : β),
      MultiTierOk T ∧ C0 ∈ T.tauE g := by
  obtain ⟨α, I, hI, x0, hdom0, hsat0⟩ := hsat
  let root : RNode I C0 :=
    { x := x0, s := [C0], hdom := hdom0
      hmty := fun F hF => by
        rw [List.mem_singleton.mp hF]
        exact mem_mty.mpr ⟨cl_self C0, hsat0⟩
      hcl := fun F hF => by
        rw [List.mem_singleton.mp hF]
        exact cl_self C0 }
  refine ⟨GB root, mtVF root,
    ⟨x0, List.mem_map.mpr ⟨root, self_mem_rnodes root, rfl⟩⟩,
    mtVF_ok hI haf root, ?_⟩
  show C0 ∈ mlabel root x0
  exact mem_mlabel.mpr
    ⟨root, self_mem_rnodes root, rfl, mem_reqType_of_mem List.mem_cons_self⟩

/-! ### The tree-structural frame (lift Step 1, foundation)

Toward the FULL ∀PO-free fragment (universals allowed).  The merged
read-off frame breaks once universals appear: a real `DR` edge fires
`∀DR` BOTH ways (converse symmetry), so an "accidental" `DR` pair — two
guides that happen to be `DR` in the model but are not a demand edge —
would impose an unmet obligation.  The fix is the TREE-STRUCTURAL frame:
`DR` only on actual tree (demand) edges, `PO` everywhere else (and `PO`
fires NOTHING in the ∀PO-free fragment).  Its frame validity is purely
combinatorial and holds for ANY symmetric `{DR,PO}` off-diagonal
labelling: `comp` of `{DR,PO}` always contains `{DR,PO}`, and `EQ` sits
only on the diagonal.  (Wiring the tree-adjacency `d` and the `∀DR`
fire-threading — the bidirectional `∀DR`-closure — is the remaining
work; this lemma discharges the frame side once and for all.) -/

/-- `{DR,PO}` compositions contain `{DR,PO}`. -/
theorem drpo_closed : ∀ a b : Atom, (a = dr ∨ a = po) → (b = dr ∨ b = po) →
    dr ∈ comp a b ∧ po ∈ comp a b := by
  intro a b ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    exact ⟨by decide, by decide⟩

/-- Self-composition of `DR`/`PO` contains `EQ`. -/
theorem drpo_self_eq : ∀ a : Atom, (a = dr ∨ a = po) → eq ∈ comp a a := by
  intro a ha; rcases ha with rfl | rfl <;> decide

open Classical in
/-- THE TREE-STRUCTURAL FRAME (frame side): any symmetric `{DR,PO}`
    off-diagonal labelling — `EQ` on the diagonal, `DR` where a symmetric
    predicate `d` holds, `PO` elsewhere — is a genuine RCC5 frame.  This
    is the frame the ∀PO-free assembly uses: `d` = "tree (demand)
    adjacent".  (Irreflexivity of `d` is not even needed — the diagonal
    is `EQ` regardless.) -/
theorem symDrPo_frame {V : Type} (d : V → V → Bool)
    (hsym : ∀ v w, d v w = d w v) :
    Frame (fun v w => if v = w then eq else if d v w then dr else po) := by
  have Loff : ∀ v w : V, v ≠ w →
      (if v = w then eq else if d v w then dr else po) = dr ∨
      (if v = w then eq else if d v w then dr else po) = po := by
    intro v w h
    rw [if_neg h]
    cases d v w
    · exact Or.inr rfl
    · exact Or.inl rfl
  have Lsymm : ∀ v w : V,
      (if w = v then eq else if d w v then dr else po) =
      (if v = w then eq else if d v w then dr else po) := by
    intro v w
    by_cases h : v = w
    · subst h; rfl
    · rw [if_neg (Ne.symm h), if_neg h, hsym w v]
  refine ⟨fun v => by simp, ?_, ?_, ?_⟩
  · intro v w h
    by_cases hvw : v = w
    · exact hvw
    · rcases Loff v w hvw with hh | hh <;> rw [hh] at h <;>
        exact absurd h (by decide)
  · intro v w
    rw [Lsymm v w]
    by_cases hvw : v = w
    · subst hvw; rw [if_pos rfl]; rfl
    · rcases Loff v w hvw with hh | hh <;> rw [hh] <;> rfl
  · intro v w u
    by_cases hvu : v = u
    · subst hvu; rw [if_pos rfl]
      by_cases hvw : v = w
      · subst hvw; rw [if_pos rfl]; decide
      · rw [Lsymm v w]
        rcases Loff v w hvw with hh | hh <;> rw [hh] <;> decide
    · by_cases hvw : v = w
      · subst hvw; rw [if_pos rfl]
        rcases Loff v u hvu with hh | hh <;> rw [hh] <;> decide
      · by_cases hwu : w = u
        · subst hwu; rw [if_pos rfl]
          rcases Loff v w hvw with hh | hh <;> rw [hh] <;> decide
        · rcases Loff v u hvu with hu | hu <;>
            rcases Loff v w hvw with h1 | h1 <;>
            rcases Loff w u hwu with h2 | h2 <;>
            rw [hu, h1, h2] <;> decide

/-- The tree-structural labelling only takes values in `{EQ, DR, PO}`,
    so in the ∀PO-free fragment `ee_all` reduces to exactly the `DR`
    edges (the crux: the `∀DR` reverse-firing) and the `EQ` diagonal
    (reflexive) — `PP`/`PPI` never occur, `PO` fires nothing. -/
theorem symDrPo_vals {V : Type} (d : V → V → Bool) [DecidableEq V]
    (v w : V) :
    (if v = w then eq else if d v w then dr else po) = eq ∨
    (if v = w then eq else if d v w then dr else po) = dr ∨
    (if v = w then eq else if d v w then dr else po) = po := by
  by_cases hvw : v = w
  · rw [if_pos hvw]; exact Or.inl rfl
  · rw [if_neg hvw]; cases d v w
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)

/-- Lift a `β`-frame to the `κ = Empty` quotient frame: with no kernels,
    `qnet E _ _` on `β ⊕ Empty` is a frame iff `E` is (the `inr` cases are
    vacuous).  This is `frame_q` for the tree-structural (kernel-free)
    assembly, the analogue of `readoff_qnet_frame` for the read-off one. -/
theorem qnet_empty_frame {β : Type} (E : β → β → Atom) (hE : Frame E) :
    Frame (qnet E (fun (k : Empty) _ => k.elim)
      (fun (k : Empty) _ => k.elim)) where
  refl_eq
    | .inl m => hE.refl_eq m
    | .inr k => k.elim
  eq_id
    | .inl m, .inl m', h => congrArg Sum.inl (hE.eq_id m m' h)
    | .inl _, .inr k, _ => k.elim
    | .inr k, _, _ => k.elim
  conv_
    | .inl m, .inl m' => hE.conv_ m m'
    | .inl _, .inr k => k.elim
    | .inr k, _ => k.elim
  comp_
    | .inl m, .inl m', .inl m'' => hE.comp_ m m' m''
    | .inl _, .inl _, .inr k => k.elim
    | .inl _, .inr k, _ => k.elim
    | .inr k, _, _ => k.elim

/-- `qnet_empty_frame` for ANY empty kernel type (via `hemp : κ → False`),
    not just `Empty` — needed for `decodeMT` of a kernel-free `FinMT`,
    whose kernel type is `Fin 0`. -/
theorem qnet_empty_frame' {β κ : Type} [DecidableEq κ] (E : β → β → Atom)
    (K : κ → β → Atom) (Q : κ → κ → Atom) (hemp : κ → False) (hE : Frame E) :
    Frame (qnet E K Q) where
  refl_eq
    | .inl m => hE.refl_eq m
    | .inr k => (hemp k).elim
  eq_id
    | .inl m, .inl m', h => congrArg Sum.inl (hE.eq_id m m' h)
    | .inl _, .inr k, _ => (hemp k).elim
    | .inr k, _, _ => (hemp k).elim
  conv_
    | .inl m, .inl m' => hE.conv_ m m'
    | .inl _, .inr k => (hemp k).elim
    | .inr k, _ => (hemp k).elim
  comp_
    | .inl m, .inl m', .inl m'' => hE.comp_ m m' m''
    | .inl _, .inl _, .inr k => (hemp k).elim
    | .inl _, .inr k, _ => (hemp k).elim
    | .inr k, _, _ => (hemp k).elim

open Classical in
/-- **PO-DEFAULT ASCENDING-KERNEL FRAME** (mixing extraction, step 1 —
    validated by wp90 as the correct policy for the ascending quadrant).  The
    `qnet` frame of a `symDrPo` external skeleton (`d`) plus ONE ascending
    kernel whose base is `PPI` to its attaching node `v0` and `PO` to every
    other external.  At the `qnet` level (one node per kernel base; the tower
    itself is `munf`-unfolded, not a frame node) every far edge is genuinely
    FREE: externals are `DR/PO/EQ`-only, and `comp(PPI, DR)={PPI,PO,DR}`,
    `comp(PPI, PO)={PPI,PO}` are non-singletons containing `PO`, so
    `PO`-default closes every mixed triangle (the `mtHF` trick, now spanning
    the kernel base).  Descending is the SEPARATE forcing case
    (`comp(PP,DR)={DR}` forces the base's DR-children).  Label-independent, so
    it serves as `frame_q` under any phase truncation. -/
theorem po_default_asc_frame {β : Type}
    (d : β → β → Bool) (hsym : ∀ v w, d v w = d w v) (v0 : β) :
    Frame (qnet
      (fun e f => if e = f then eq else if d e f then dr else po)
      (fun (_ : Unit) e => if e = v0 then ppi else po)
      (fun (_ : Unit) (_ : Unit) => eq)) := by
  have hE := symDrPo_frame d hsym
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- refl_eq
    rintro (e | ⟨⟩)
    · show (if e = e then eq else if d e e then dr else po) = eq
      rw [if_pos rfl]
    · rfl
  · -- eq_id
    rintro (e | ⟨⟩) (f | ⟨⟩) h
    · refine congrArg Sum.inl ?_
      have h' : (if e = f then eq else if d e f then dr else po) = eq := h
      by_cases hef : e = f
      · exact hef
      · rw [if_neg hef] at h'
        by_cases hd : d e f = true
        · rw [if_pos hd] at h'; exact absurd h' (by decide)
        · rw [if_neg hd] at h'; exact absurd h' (by decide)
    · refine absurd (show conv (if e = v0 then ppi else po) = eq from h) ?_
      by_cases he : e = v0
      · rw [if_pos he]; decide
      · rw [if_neg he]; decide
    · refine absurd (show (if f = v0 then ppi else po) = eq from h) ?_
      by_cases hf : f = v0
      · rw [if_pos hf]; decide
      · rw [if_neg hf]; decide
    · rfl
  · -- conv_
    rintro (e | ⟨⟩) (f | ⟨⟩)
    · show (if f = e then eq else if d f e then dr else po)
        = conv (if e = f then eq else if d e f then dr else po)
      exact hE.conv_ e f
    · show (if e = v0 then ppi else po) = conv (conv (if e = v0 then ppi else po))
      by_cases he : e = v0
      · rw [if_pos he]; decide
      · rw [if_neg he]; decide
    · rfl
    · rfl
  · -- comp_
    rintro (e | ⟨⟩) (f | ⟨⟩) (g | ⟨⟩)
    · show (if e = g then eq else if d e g then dr else po)
        ∈ comp (if e = f then eq else if d e f then dr else po)
               (if f = g then eq else if d f g then dr else po)
      exact hE.comp_ e f g
    · -- (b) inl e, inl f, inr(): conv(K e) ∈ comp(E e f, conv(K f))
      show conv (if e = v0 then ppi else po)
        ∈ comp (if e = f then eq else if d e f then dr else po)
               (conv (if f = v0 then ppi else po))
      by_cases hef : e = f
      · subst hef; rw [if_pos rfl]
        by_cases he : e = v0
        · rw [if_pos he]; decide
        · rw [if_neg he]; decide
      · by_cases he : e = v0 <;> by_cases hf : f = v0
        · exact absurd (he.trans hf.symm) hef
        · rw [if_neg hef, if_pos he, if_neg hf]; cases d e f <;> decide
        · rw [if_neg hef, if_neg he, if_pos hf]; cases d e f <;> decide
        · rw [if_neg hef, if_neg he, if_neg hf]; cases d e f <;> decide
    · -- (c) inl e, inr(), inl g: E e g ∈ comp(conv(K e), K g)
      show (if e = g then eq else if d e g then dr else po)
        ∈ comp (conv (if e = v0 then ppi else po))
               (if g = v0 then ppi else po)
      by_cases heg : e = g
      · subst heg; rw [if_pos rfl]
        by_cases he : e = v0
        · rw [if_pos he]; decide
        · rw [if_neg he]; decide
      · by_cases he : e = v0 <;> by_cases hg : g = v0
        · exact absurd (he.trans hg.symm) heg
        · rw [if_neg heg, if_pos he, if_neg hg]; cases d e g <;> decide
        · rw [if_neg heg, if_neg he, if_pos hg]; cases d e g <;> decide
        · rw [if_neg heg, if_neg he, if_neg hg]; cases d e g <;> decide
    · -- (d) inl e, inr(), inr(): conv(K e) ∈ comp(conv(K e), eq)
      show conv (if e = v0 then ppi else po)
        ∈ comp (conv (if e = v0 then ppi else po)) eq
      by_cases he : e = v0
      · rw [if_pos he]; decide
      · rw [if_neg he]; decide
    · -- (e) inr(), inl f, inl g: K g ∈ comp(K f, E f g)
      show (if g = v0 then ppi else po)
        ∈ comp (if f = v0 then ppi else po)
               (if f = g then eq else if d f g then dr else po)
      by_cases hfg : f = g
      · subst hfg; rw [if_pos rfl]
        by_cases hf : f = v0
        · rw [if_pos hf]; decide
        · rw [if_neg hf]; decide
      · by_cases hf : f = v0 <;> by_cases hg : g = v0
        · exact absurd (hf.trans hg.symm) hfg
        · rw [if_pos hf, if_neg hg, if_neg hfg]; cases d f g <;> decide
        · rw [if_neg hf, if_pos hg, if_neg hfg]; cases d f g <;> decide
        · rw [if_neg hf, if_neg hg, if_neg hfg]; cases d f g <;> decide
    · -- (f) inr(), inl f, inr(): eq ∈ comp(K f, conv(K f))
      show eq ∈ comp (if f = v0 then ppi else po)
                     (conv (if f = v0 then ppi else po))
      by_cases hf : f = v0
      · rw [if_pos hf]; decide
      · rw [if_neg hf]; decide
    · -- (g) inr(), inr(), inl g: K g ∈ comp(eq, K g)
      show (if g = v0 then ppi else po)
        ∈ comp eq (if g = v0 then ppi else po)
      by_cases hg : g = v0
      · rw [if_pos hg]; decide
      · rw [if_neg hg]; decide
    · -- (h) inr(), inr(), inr()
      show eq ∈ comp eq eq
      decide

open Classical in
/-- **PP-BELOW-TWIN FRAME** (descending kernel — mixing extraction step 1, the
    FORCING case, validated by wp90).  Given any RCC5 frame `N` and a node
    `v0`, adjoin one node (the descending kernel base `b ⊂ v0`) that is a
    PP-below TWIN of `v0`: `PP` to `v0`, and to every OTHER node the SAME
    relation `v0` has (`N v0 e`).  The result is a frame.  The base's row is
    FORCED to mirror `v0`'s (`comp(PP,DR)={DR}`, ...), so base-triangles reduce
    to `N`'s own closure at `v0` plus finite `comp` facts.  Instantiated with
    the `symDrPo` external network this is the descending quadrant's `frame_q`
    (the base is `DR` to `v0`'s `DR`-children — forced — and `PO` to `v0`'s
    `PO`-neighbours — free). -/
theorem pp_twin_frame {V : Type} (N : V → V → Atom) (hN : Frame N) (v0 : V) :
    Frame (qnet N (fun (_ : Unit) e => if e = v0 then pp else N v0 e)
                  (fun (_ : Unit) (_ : Unit) => eq)) := by
  have hcv : ∀ r : Atom, conv (conv r) = r := by intro r; cases r <;> rfl
  have hce : ∀ r : Atom, conv r = eq → r = eq := by
    intro r h; cases r <;> first | rfl | exact absurd h (by decide)
  have hne : ∀ e, e ≠ v0 → N v0 e ≠ eq := fun e he h => he (hN.eq_id v0 e h).symm
  have hne' : ∀ a, a ≠ v0 → N a v0 ≠ eq := fun a ha h => ha (hN.eq_id a v0 h)
  have f1 : ∀ r : Atom, r ≠ eq → r ∈ comp pp r := by
    intro r hr; cases r <;> first | exact absurd rfl hr | decide
  have f2 : ∀ r : Atom, r ≠ eq → r ∈ comp r pp := by
    intro r hr; cases r <;> first | exact absurd rfl hr | decide
  have f3 : ∀ r : Atom, r ≠ eq → r ∈ comp ppi r := by
    intro r hr; cases r <;> first | exact absurd rfl hr | decide
  have f4 : ∀ r : Atom, r ≠ eq → r ∈ comp r ppi := by
    intro r hr; cases r <;> first | exact absurd rfl hr | decide
  have f5 : ∀ r : Atom, r ≠ eq → pp ∈ comp r (conv r) := by
    intro r hr; cases r <;> first | exact absurd rfl hr | decide
  have f6 : ∀ r : Atom, r ≠ eq → ppi ∈ comp r (conv r) := by
    intro r hr; cases r <;> first | exact absurd rfl hr | decide
  have f7 : ∀ r : Atom, r ∈ comp r eq := by intro r; cases r <;> decide
  have f8 : ∀ r : Atom, r ∈ comp eq r := by intro r; cases r <;> decide
  have f9 : ∀ r : Atom, eq ∈ comp r (conv r) := by intro r; cases r <;> decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- refl_eq
    rintro (a | ⟨⟩)
    · exact hN.refl_eq a
    · rfl
  · -- eq_id
    rintro (a | ⟨⟩) (b | ⟨⟩) h
    · exact congrArg Sum.inl (hN.eq_id a b h)
    · refine absurd (show conv (if a = v0 then pp else N v0 a) = eq from h) ?_
      by_cases ha : a = v0
      · rw [if_pos ha]; decide
      · rw [if_neg ha]; intro hh; exact hne a ha (hce _ hh)
    · refine absurd (show (if b = v0 then pp else N v0 b) = eq from h) ?_
      by_cases hb : b = v0
      · rw [if_pos hb]; decide
      · rw [if_neg hb]; exact hne b hb
    · rfl
  · -- conv_
    rintro (a | ⟨⟩) (b | ⟨⟩)
    · exact hN.conv_ a b
    · show (if a = v0 then pp else N v0 a)
        = conv (conv (if a = v0 then pp else N v0 a))
      rw [hcv]
    · rfl
    · rfl
  · -- comp_
    rintro (a | ⟨⟩) (b | ⟨⟩) (c | ⟨⟩)
    · exact hN.comp_ a b c
    · -- (b) inl a, inl b, inr(): a→base ∈ comp(N a b, b→base)
      show conv (if a = v0 then pp else N v0 a)
        ∈ comp (N a b) (conv (if b = v0 then pp else N v0 b))
      by_cases ha : a = v0 <;> by_cases hb : b = v0
      · rw [ha, hb, if_pos rfl, hN.refl_eq v0]; decide
      · rw [ha, if_pos rfl, if_neg hb]; exact f6 (N v0 b) (hne b hb)
      · rw [hb, if_neg ha, if_pos rfl, ← hN.conv_ v0 a]
        exact f4 (N a v0) (hne' a ha)
      · rw [if_neg ha, if_neg hb, ← hN.conv_ v0 a, ← hN.conv_ v0 b]
        exact hN.comp_ a b v0
    · -- (c) inl a, inr(), inl c: N a c ∈ comp(a→base, base→c)
      show N a c ∈ comp (conv (if a = v0 then pp else N v0 a))
                        (if c = v0 then pp else N v0 c)
      by_cases ha : a = v0 <;> by_cases hc : c = v0
      · rw [ha, hc, if_pos rfl, hN.refl_eq v0]; decide
      · rw [ha, if_pos rfl, if_neg hc]; exact f3 (N v0 c) (hne c hc)
      · rw [hc, if_neg ha, if_pos rfl, ← hN.conv_ v0 a]
        exact f2 (N a v0) (hne' a ha)
      · rw [if_neg ha, if_neg hc, ← hN.conv_ v0 a]; exact hN.comp_ a v0 c
    · -- (d) inl a, inr(), inr(): a→base ∈ comp(a→base, eq)
      exact f7 (conv (if a = v0 then pp else N v0 a))
    · -- (e) inr(), inl b, inl c: base→c ∈ comp(base→b, N b c)
      show (if c = v0 then pp else N v0 c)
        ∈ comp (if b = v0 then pp else N v0 b) (N b c)
      by_cases hb : b = v0 <;> by_cases hc : c = v0
      · rw [hb, hc, if_pos rfl, hN.refl_eq v0]; decide
      · rw [hb, if_pos rfl, if_neg hc]; exact f1 (N v0 c) (hne c hc)
      · rw [hc, if_pos rfl, if_neg hb, hN.conv_ v0 b]
        exact f5 (N v0 b) (hne b hb)
      · rw [if_neg hb, if_neg hc]; exact hN.comp_ v0 b c
    · -- (f) inr(), inl b, inr(): eq ∈ comp(base→b, b→base)
      exact f9 (if b = v0 then pp else N v0 b)
    · -- (g) inr(), inr(), inl c: base→c ∈ comp(eq, base→c)
      exact f8 (if c = v0 then pp else N v0 c)
    · -- (h) inr(), inr(), inr()
      show eq ∈ comp eq eq
      decide

open Classical in
/-- The descending quadrant's `frame_q`: `pp_twin_frame` at the `symDrPo`
    external network.  The base is `PP` to `v0`, `DR` to `v0`'s `DR`-children
    (forced), `PO` to `v0`'s `PO`-neighbours (free). -/
theorem po_default_desc_frame {β : Type} (d : β → β → Bool)
    (hsym : ∀ v w, d v w = d w v) (v0 : β) :
    Frame (qnet
      (fun e f => if e = f then eq else if d e f then dr else po)
      (fun (_ : Unit) e => if e = v0 then pp
        else (if v0 = e then eq else if d v0 e then dr else po))
      (fun (_ : Unit) (_ : Unit) => eq)) :=
  pp_twin_frame _ (symDrPo_frame d hsym) v0

open Classical in
/-- **MULTI-KERNEL PO-DEFAULT FRAME** — the uniform-`β` multi-tower frame.  A
    `symDrPo` external skeleton plus `κ` ascending kernels, each `PPI` to its own
    attach point `v0 k` and `PO` to everything else; cross-kernel `Q`-edges
    `PO`-default (`qnet` supplies the `eq` diagonal).  A frame for ARBITRARY
    `v0 : κ → β` — two kernels MAY even share an attach point (`comp(pp,po) ∋
    pp`).  This is `frame_q` for the mtk-truncated MULTI-kernel certificate: the
    cross-`Q` FORCING that made the full-`mty` multi-kernel frame hard is
    DISSOLVED by PO-default, which `∀PO`-freeness also renders `kq_all`-vacuous.
    Generalises `po_default_asc_frame` (`κ = Unit`). -/
theorem po_default_multi_frame {β κ : Type}
    (d : β → β → Bool) (hsym : ∀ v w, d v w = d w v) (v0 : κ → β) :
    Frame (qnet
      (fun e f => if e = f then eq else if d e f then dr else po)
      (fun k e => if e = v0 k then ppi else po)
      (fun (_ : κ) (_ : κ) => po)) := by
  have hE := symDrPo_frame d hsym
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- refl_eq
    rintro (e | k)
    · show (if e = e then eq else if d e e then dr else po) = eq
      rw [if_pos rfl]
    · show (if k = k then eq else po) = eq
      rw [if_pos rfl]
  · -- eq_id
    rintro (e | k) (f | k') h
    · refine congrArg Sum.inl ?_
      have h' : (if e = f then eq else if d e f then dr else po) = eq := h
      by_cases hef : e = f
      · exact hef
      · rw [if_neg hef] at h'
        by_cases hd : d e f = true
        · rw [if_pos hd] at h'; exact absurd h' (by decide)
        · rw [if_neg hd] at h'; exact absurd h' (by decide)
    · refine absurd (show conv (if e = v0 k' then ppi else po) = eq from h) ?_
      by_cases he : e = v0 k'
      · rw [if_pos he]; decide
      · rw [if_neg he]; decide
    · refine absurd (show (if f = v0 k then ppi else po) = eq from h) ?_
      by_cases hf : f = v0 k
      · rw [if_pos hf]; decide
      · rw [if_neg hf]; decide
    · refine congrArg Sum.inr ?_
      have h' : (if k = k' then eq else po) = eq := h
      by_cases hkk : k = k'
      · exact hkk
      · rw [if_neg hkk] at h'; exact absurd h' (by decide)
  · -- conv_
    rintro (e | k) (f | k')
    · show (if f = e then eq else if d f e then dr else po)
        = conv (if e = f then eq else if d e f then dr else po)
      exact hE.conv_ e f
    · show (if e = v0 k' then ppi else po)
        = conv (conv (if e = v0 k' then ppi else po))
      by_cases he : e = v0 k'
      · rw [if_pos he]; decide
      · rw [if_neg he]; decide
    · rfl
    · show (if k' = k then eq else po) = conv (if k = k' then eq else po)
      by_cases hkk : k = k'
      · rw [if_pos hkk, if_pos hkk.symm]; decide
      · rw [if_neg hkk, if_neg (fun h => hkk h.symm)]; decide
  · -- comp_
    rintro (e | k) (f | k') (g | k'')
    · -- (1) ext, ext, ext
      show (if e = g then eq else if d e g then dr else po)
        ∈ comp (if e = f then eq else if d e f then dr else po)
               (if f = g then eq else if d f g then dr else po)
      exact hE.comp_ e f g
    · -- (2) inl e, inl f, inr k''
      show conv (if e = v0 k'' then ppi else po)
        ∈ comp (if e = f then eq else if d e f then dr else po)
               (conv (if f = v0 k'' then ppi else po))
      by_cases hef : e = f
      · subst hef; rw [if_pos rfl]
        by_cases he : e = v0 k''
        · rw [if_pos he]; decide
        · rw [if_neg he]; decide
      · by_cases he : e = v0 k'' <;> by_cases hf : f = v0 k''
        · exact absurd (he.trans hf.symm) hef
        · rw [if_neg hef, if_pos he, if_neg hf]; cases d e f <;> decide
        · rw [if_neg hef, if_neg he, if_pos hf]; cases d e f <;> decide
        · rw [if_neg hef, if_neg he, if_neg hf]; cases d e f <;> decide
    · -- (3) inl e, inr k', inl g
      show (if e = g then eq else if d e g then dr else po)
        ∈ comp (conv (if e = v0 k' then ppi else po))
               (if g = v0 k' then ppi else po)
      by_cases heg : e = g
      · subst heg; rw [if_pos rfl]
        by_cases he : e = v0 k'
        · rw [if_pos he]; decide
        · rw [if_neg he]; decide
      · by_cases he : e = v0 k' <;> by_cases hg : g = v0 k'
        · exact absurd (he.trans hg.symm) heg
        · rw [if_neg heg, if_pos he, if_neg hg]; cases d e g <;> decide
        · rw [if_neg heg, if_neg he, if_pos hg]; cases d e g <;> decide
        · rw [if_neg heg, if_neg he, if_neg hg]; cases d e g <;> decide
    · -- (4) inl e, inr k', inr k''
      show conv (if e = v0 k'' then ppi else po)
        ∈ comp (conv (if e = v0 k' then ppi else po))
               (if k' = k'' then eq else po)
      by_cases hkk : k' = k''
      · subst hkk; rw [if_pos rfl]
        by_cases he : e = v0 k'
        · rw [if_pos he]; decide
        · rw [if_neg he]; decide
      · rw [if_neg hkk]
        by_cases he'' : e = v0 k'' <;> by_cases he' : e = v0 k'
        · rw [if_pos he'', if_pos he']; decide
        · rw [if_pos he'', if_neg he']; decide
        · rw [if_neg he'', if_pos he']; decide
        · rw [if_neg he'', if_neg he']; decide
    · -- (5) inr k, inl f, inl g
      show (if g = v0 k then ppi else po)
        ∈ comp (if f = v0 k then ppi else po)
               (if f = g then eq else if d f g then dr else po)
      by_cases hfg : f = g
      · subst hfg; rw [if_pos rfl]
        by_cases hf : f = v0 k
        · rw [if_pos hf]; decide
        · rw [if_neg hf]; decide
      · by_cases hf : f = v0 k <;> by_cases hg : g = v0 k
        · exact absurd (hf.trans hg.symm) hfg
        · rw [if_pos hf, if_neg hg, if_neg hfg]; cases d f g <;> decide
        · rw [if_neg hf, if_pos hg, if_neg hfg]; cases d f g <;> decide
        · rw [if_neg hf, if_neg hg, if_neg hfg]; cases d f g <;> decide
    · -- (6) inr k, inl f, inr k''
      show (if k = k'' then eq else po)
        ∈ comp (if f = v0 k then ppi else po)
               (conv (if f = v0 k'' then ppi else po))
      by_cases hkk : k = k''
      · subst hkk; rw [if_pos rfl]
        by_cases hf : f = v0 k
        · rw [if_pos hf]; decide
        · rw [if_neg hf]; decide
      · rw [if_neg hkk]
        by_cases hf : f = v0 k <;> by_cases hf'' : f = v0 k''
        · rw [if_pos hf, if_pos hf'']; decide
        · rw [if_pos hf, if_neg hf'']; decide
        · rw [if_neg hf, if_pos hf'']; decide
        · rw [if_neg hf, if_neg hf'']; decide
    · -- (7) inr k, inr k', inl g
      show (if g = v0 k then ppi else po)
        ∈ comp (if k = k' then eq else po)
               (if g = v0 k' then ppi else po)
      by_cases hkk : k = k'
      · subst hkk; rw [if_pos rfl]
        by_cases hg : g = v0 k
        · rw [if_pos hg]; decide
        · rw [if_neg hg]; decide
      · rw [if_neg hkk]
        by_cases hg : g = v0 k <;> by_cases hg' : g = v0 k'
        · rw [if_pos hg, if_pos hg']; decide
        · rw [if_pos hg, if_neg hg']; decide
        · rw [if_neg hg, if_pos hg']; decide
        · rw [if_neg hg, if_neg hg']; decide
    · -- (8) inr k, inr k', inr k''
      show (if k = k'' then eq else po)
        ∈ comp (if k = k' then eq else po) (if k' = k'' then eq else po)
      by_cases hkk'' : k = k''
      · by_cases hkk' : k = k'
        · have hk'k'' : k' = k'' := hkk'.symm.trans hkk''
          rw [if_pos hkk'', if_pos hkk', if_pos hk'k'']; decide
        · have hk'k'' : k' ≠ k'' := fun h => hkk' (hkk''.trans h.symm)
          rw [if_pos hkk'', if_neg hkk', if_neg hk'k'']; decide
      · rw [if_neg hkk'']
        by_cases hkk' : k = k' <;> by_cases hk'k'' : k' = k''
        · exact absurd (hkk'.trans hk'k'') hkk''
        · rw [if_pos hkk', if_neg hk'k'']; decide
        · rw [if_neg hkk', if_pos hk'k'']; decide
        · rw [if_neg hkk', if_neg hk'k'']; decide

open Classical in
/-- **THE FORCING-COMPLETION FRAME (first brick): one real DR-child.**  A single
    ascending kernel whose `K`-edge is `PPI` to the attach `v0`, a REAL `DR` to
    one child `c0`, and `PO` elsewhere.  The `DR` edge is not free — it FORCES
    (`comp(PP,DR) = comp(DR,PPI) = {DR}`) the child's edge to the attach: `c0`
    must be `DR`-adjacent to `v0` in the skeleton (`hcoh : dadj c0 v0 = true`).
    Given that single coherence condition the whole frame closes — the other
    forced/free edges land in the non-singleton `comp` cells (`comp(DR,PO) ∋
    PP,PO,DR`).  This is `po_default_asc_frame` (no DR-child) upgraded to serve a
    phase-`∃DR` at one adjacency child — the minimal case of §28's
    forcing-completion frame. -/
theorem po_dr_asc_frame {β : Type} (dadj : β → β → Bool)
    (hsym : ∀ v w, dadj v w = dadj w v) (v0 c0 : β)
    (hne : c0 ≠ v0) (hcoh : dadj c0 v0 = true) :
    Frame (qnet
      (fun e f => if e = f then eq else if dadj e f then dr else po)
      (fun (_ : Unit) e => if e = v0 then ppi else if e = c0 then dr else po)
      (fun (_ : Unit) (_ : Unit) => eq)) := by
  have hE := symDrPo_frame dadj hsym
  have hcoh' : dadj v0 c0 = true := by rw [hsym]; exact hcoh
  -- the child↔attach edge is forced to `DR`
  have hEc0v0 : (if c0 = v0 then eq else if dadj c0 v0 then dr else po) = dr := by
    rw [if_neg hne, if_pos hcoh]
  have hEv0c0 : (if v0 = c0 then eq else if dadj v0 c0 then dr else po) = dr := by
    rw [if_neg (fun h => hne h.symm), if_pos hcoh']
  have hce_r : ∀ r : Atom, r ∈ comp r eq := fun r => by cases r <;> decide
  have hce_l : ∀ r : Atom, r ∈ comp eq r := fun r => by cases r <;> decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- refl_eq
    rintro (e | ⟨⟩)
    · show (if e = e then eq else if dadj e e then dr else po) = eq
      rw [if_pos rfl]
    · rfl
  · -- eq_id
    rintro (e | ⟨⟩) (f | ⟨⟩) h
    · refine congrArg Sum.inl ?_
      have h' : (if e = f then eq else if dadj e f then dr else po) = eq := h
      by_cases hef : e = f
      · exact hef
      · rw [if_neg hef] at h'
        by_cases hd : dadj e f = true
        · rw [if_pos hd] at h'; exact absurd h' (by decide)
        · rw [if_neg hd] at h'; exact absurd h' (by decide)
    · refine absurd (show conv (if e = v0 then ppi else if e = c0 then dr else po) = eq
        from h) ?_
      by_cases he : e = v0
      · rw [if_pos he]; decide
      · by_cases he2 : e = c0
        · rw [if_neg he, if_pos he2]; decide
        · rw [if_neg he, if_neg he2]; decide
    · refine absurd (show (if f = v0 then ppi else if f = c0 then dr else po) = eq
        from h) ?_
      by_cases hf : f = v0
      · rw [if_pos hf]; decide
      · by_cases hf2 : f = c0
        · rw [if_neg hf, if_pos hf2]; decide
        · rw [if_neg hf, if_neg hf2]; decide
    · rfl
  · -- conv_
    rintro (e | ⟨⟩) (f | ⟨⟩)
    · show (if f = e then eq else if dadj f e then dr else po)
        = conv (if e = f then eq else if dadj e f then dr else po)
      exact hE.conv_ e f
    · show (if e = v0 then ppi else if e = c0 then dr else po)
        = conv (conv (if e = v0 then ppi else if e = c0 then dr else po))
      by_cases he : e = v0
      · rw [if_pos he]; decide
      · by_cases he2 : e = c0
        · rw [if_neg he, if_pos he2]; decide
        · rw [if_neg he, if_neg he2]; decide
    · rfl
    · rfl
  · -- comp_
    rintro (e | ⟨⟩) (f | ⟨⟩) (g | ⟨⟩)
    · show (if e = g then eq else if dadj e g then dr else po)
        ∈ comp (if e = f then eq else if dadj e f then dr else po)
               (if f = g then eq else if dadj f g then dr else po)
      exact hE.comp_ e f g
    · -- (b) inl e, inl f, inr(): conv(K e) ∈ comp(E e f, conv(K f))
      show conv (if e = v0 then ppi else if e = c0 then dr else po)
        ∈ comp (if e = f then eq else if dadj e f then dr else po)
               (conv (if f = v0 then ppi else if f = c0 then dr else po))
      by_cases hef : e = f
      · subst hef
        by_cases he : e = v0
        · rw [if_pos rfl, if_pos he]; decide
        · by_cases he2 : e = c0
          · rw [if_pos rfl, if_neg he, if_pos he2]; decide
          · rw [if_pos rfl, if_neg he, if_neg he2]; decide
      · rw [if_neg hef]
        by_cases he : e = v0 <;> by_cases he2 : e = c0 <;>
          by_cases hf : f = v0 <;> by_cases hf2 : f = c0
        all_goals first
          | (exact absurd (he2.symm.trans he) hne)
          | (exact absurd (hf2.symm.trans hf) hne)
          | (subst he; subst hf; exact absurd rfl hef)
          | (subst he2; subst hf2; exact absurd rfl hef)
          | (subst he; subst hf2; rw [if_pos rfl, if_pos hcoh', if_neg hne, if_pos rfl]; decide)
          | (subst he2; subst hf; rw [if_neg hne, if_pos rfl, if_pos hcoh, if_pos rfl]; decide)
          | (rw [if_pos he, if_neg hf, if_pos hf2]; cases hd : dadj e f <;> decide)
          | (rw [if_pos he, if_neg hf, if_neg hf2]; cases hd : dadj e f <;> decide)
          | (rw [if_neg he, if_pos he2, if_neg hf, if_neg hf2]; cases hd : dadj e f <;> decide)
          | (rw [if_neg he, if_neg he2, if_pos hf]; cases hd : dadj e f <;> decide)
          | (rw [if_neg he, if_neg he2, if_neg hf, if_pos hf2]; cases hd : dadj e f <;> decide)
          | (rw [if_neg he, if_neg he2, if_neg hf, if_neg hf2]; cases hd : dadj e f <;> decide)
    · -- (c) inl e, inr(), inl g: E e g ∈ comp(conv(K e), K g)
      show (if e = g then eq else if dadj e g then dr else po)
        ∈ comp (conv (if e = v0 then ppi else if e = c0 then dr else po))
               (if g = v0 then ppi else if g = c0 then dr else po)
      by_cases heg : e = g
      · subst heg
        by_cases he : e = v0
        · rw [if_pos rfl, if_pos he]; decide
        · by_cases he2 : e = c0
          · rw [if_pos rfl, if_neg he, if_pos he2]; decide
          · rw [if_pos rfl, if_neg he, if_neg he2]; decide
      · rw [if_neg heg]
        by_cases he : e = v0 <;> by_cases he2 : e = c0 <;>
          by_cases hg : g = v0 <;> by_cases hg2 : g = c0
        all_goals first
          | (exact absurd (he2.symm.trans he) hne)
          | (exact absurd (hg2.symm.trans hg) hne)
          | (subst he; subst hg; exact absurd rfl heg)
          | (subst he2; subst hg2; exact absurd rfl heg)
          | (subst he; subst hg2; rw [if_pos hcoh', if_pos rfl, if_neg hne, if_pos rfl]; decide)
          | (subst he2; subst hg; rw [if_pos hcoh, if_neg hne, if_pos rfl, if_pos rfl]; decide)
          | (rw [if_pos he, if_neg hg, if_pos hg2]; cases hd : dadj e g <;> decide)
          | (rw [if_pos he, if_neg hg, if_neg hg2]; cases hd : dadj e g <;> decide)
          | (rw [if_neg he, if_pos he2, if_neg hg, if_neg hg2]; cases hd : dadj e g <;> decide)
          | (rw [if_neg he, if_neg he2, if_pos hg]; cases hd : dadj e g <;> decide)
          | (rw [if_neg he, if_neg he2, if_neg hg, if_pos hg2]; cases hd : dadj e g <;> decide)
          | (rw [if_neg he, if_neg he2, if_neg hg, if_neg hg2]; cases hd : dadj e g <;> decide)
    · -- (d) inl e, inr(), inr(): conv(K e) ∈ comp(conv(K e), eq)
      exact hce_r _
    · -- (e) inr(), inl f, inl g: K g ∈ comp(K f, E f g)
      show (if g = v0 then ppi else if g = c0 then dr else po)
        ∈ comp (if f = v0 then ppi else if f = c0 then dr else po)
               (if f = g then eq else if dadj f g then dr else po)
      by_cases hfg : f = g
      · subst hfg
        by_cases hf : f = v0
        · rw [if_pos rfl, if_pos hf]; decide
        · by_cases hf2 : f = c0
          · rw [if_pos rfl, if_neg hf, if_pos hf2]; decide
          · rw [if_pos rfl, if_neg hf, if_neg hf2]; decide
      · rw [if_neg hfg]
        by_cases hf : f = v0 <;> by_cases hf2 : f = c0 <;>
          by_cases hg : g = v0 <;> by_cases hg2 : g = c0
        all_goals first
          | (exact absurd (hf2.symm.trans hf) hne)
          | (exact absurd (hg2.symm.trans hg) hne)
          | (subst hf; subst hg; exact absurd rfl hfg)
          | (subst hf2; subst hg2; exact absurd rfl hfg)
          | (subst hf; subst hg2; rw [if_neg hne, if_pos rfl, if_pos rfl, if_pos hcoh']; decide)
          | (subst hf2; subst hg; rw [if_pos rfl, if_neg hne, if_pos rfl, if_pos hcoh]; decide)
          | (rw [if_pos hf, if_neg hg, if_pos hg2]; cases hd : dadj f g <;> decide)
          | (rw [if_pos hf, if_neg hg, if_neg hg2]; cases hd : dadj f g <;> decide)
          | (rw [if_neg hf, if_pos hf2, if_neg hg, if_neg hg2]; cases hd : dadj f g <;> decide)
          | (rw [if_neg hf, if_neg hf2, if_pos hg]; cases hd : dadj f g <;> decide)
          | (rw [if_neg hf, if_neg hf2, if_neg hg, if_pos hg2]; cases hd : dadj f g <;> decide)
          | (rw [if_neg hf, if_neg hf2, if_neg hg, if_neg hg2]; cases hd : dadj f g <;> decide)
    · -- (f) inr(), inl f, inr(): eq ∈ comp(K f, conv(K f))
      show eq ∈ comp (if f = v0 then ppi else if f = c0 then dr else po)
                     (conv (if f = v0 then ppi else if f = c0 then dr else po))
      by_cases hf : f = v0
      · rw [if_pos hf]; decide
      · by_cases hf2 : f = c0
        · rw [if_neg hf, if_pos hf2]; decide
        · rw [if_neg hf, if_neg hf2]; decide
    · -- (g) inr(), inr(), inl g: K g ∈ comp(eq, K g)
      exact hce_l _
    · -- (h)
      show eq ∈ comp eq eq
      decide

open Classical in
/-- **THE FORCING-COMPLETION FRAME (second brick): MANY real DR-children.**
    `po_dr_asc_frame` generalised from one child to a predicate `kdr : β → Bool`
    marking the kernel's `DR`-children — one kernel serving MANY phase-`∃DR`
    demands.  Coherence: every `DR`-child is `DR`-adjacent to the attach `v0`
    (`hcoh`).  The children's mutual relations are FREE (`comp(DR,DR) = all`), so
    only the child↔attach edges are forced.  Generalises `po_dr_asc_frame`
    (`kdr := (· = c0)`). -/
theorem po_dr_multi_child_frame {β : Type} (dadj : β → β → Bool)
    (hsym : ∀ v w, dadj v w = dadj w v) (v0 : β) (kdr : β → Bool)
    (hcoh : ∀ e, kdr e = true → dadj e v0 = true) :
    Frame (qnet
      (fun e f => if e = f then eq else if dadj e f then dr else po)
      (fun (_ : Unit) e => if e = v0 then ppi else if kdr e then dr else po)
      (fun (_ : Unit) (_ : Unit) => eq)) := by
  have hE := symDrPo_frame dadj hsym
  have hce_r : ∀ r : Atom, r ∈ comp r eq := fun r => by cases r <;> decide
  have hce_l : ∀ r : Atom, r ∈ comp eq r := fun r => by cases r <;> decide
  -- child→v0 and v0→child forced to DR
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (e | ⟨⟩)
    · show (if e = e then eq else if dadj e e then dr else po) = eq
      rw [if_pos rfl]
    · rfl
  · rintro (e | ⟨⟩) (f | ⟨⟩) h
    · refine congrArg Sum.inl ?_
      have h' : (if e = f then eq else if dadj e f then dr else po) = eq := h
      by_cases hef : e = f
      · exact hef
      · rw [if_neg hef] at h'
        by_cases hd : dadj e f = true
        · rw [if_pos hd] at h'; exact absurd h' (by decide)
        · rw [if_neg hd] at h'; exact absurd h' (by decide)
    · refine absurd (show conv (if e = v0 then ppi else if kdr e then dr else po) = eq
        from h) ?_
      by_cases he : e = v0
      · rw [if_pos he]; decide
      · by_cases he2 : kdr e = true
        · rw [if_neg he, if_pos he2]; decide
        · rw [if_neg he, if_neg he2]; decide
    · refine absurd (show (if f = v0 then ppi else if kdr f then dr else po) = eq
        from h) ?_
      by_cases hf : f = v0
      · rw [if_pos hf]; decide
      · by_cases hf2 : kdr f = true
        · rw [if_neg hf, if_pos hf2]; decide
        · rw [if_neg hf, if_neg hf2]; decide
    · rfl
  · rintro (e | ⟨⟩) (f | ⟨⟩)
    · show (if f = e then eq else if dadj f e then dr else po)
        = conv (if e = f then eq else if dadj e f then dr else po)
      exact hE.conv_ e f
    · show (if e = v0 then ppi else if kdr e then dr else po)
        = conv (conv (if e = v0 then ppi else if kdr e then dr else po))
      by_cases he : e = v0
      · rw [if_pos he]; decide
      · by_cases he2 : kdr e = true
        · rw [if_neg he, if_pos he2]; decide
        · rw [if_neg he, if_neg he2]; decide
    · rfl
    · rfl
  · rintro (e | ⟨⟩) (f | ⟨⟩) (g | ⟨⟩)
    · show (if e = g then eq else if dadj e g then dr else po)
        ∈ comp (if e = f then eq else if dadj e f then dr else po)
               (if f = g then eq else if dadj f g then dr else po)
      exact hE.comp_ e f g
    · -- (b) inl e, inl f, inr(): conv(K e) ∈ comp(E e f, conv(K f))
      show conv (if e = v0 then ppi else if kdr e then dr else po)
        ∈ comp (if e = f then eq else if dadj e f then dr else po)
               (conv (if f = v0 then ppi else if kdr f then dr else po))
      by_cases hef : e = f
      · subst hef
        by_cases he : e = v0
        · rw [if_pos rfl, if_pos he]; decide
        · by_cases he2 : kdr e = true
          · rw [if_pos rfl, if_neg he, if_pos he2]; decide
          · rw [if_pos rfl, if_neg he, if_neg he2]; decide
      · rw [if_neg hef]
        by_cases he : e = v0 <;> by_cases he2 : kdr e = true <;>
          by_cases hf : f = v0 <;> by_cases hf2 : kdr f = true
        all_goals first
          | (subst he; subst hf; exact absurd rfl hef)
          | (rw [he, if_pos rfl, if_pos (show dadj v0 f = true from by rw [hsym v0 f]; exact hcoh f hf2), if_neg hf, if_pos hf2]; decide)
          | (rw [if_pos he, if_neg hf, if_neg hf2]; cases hd : dadj e f <;> decide)
          | (rw [hf, if_neg he, if_pos he2, if_pos (hcoh e he2), if_pos rfl]; decide)
          | (rw [if_neg he, if_pos he2, if_neg hf, if_pos hf2]; cases hd : dadj e f <;> decide)
          | (rw [if_neg he, if_pos he2, if_neg hf, if_neg hf2]; cases hd : dadj e f <;> decide)
          | (rw [if_neg he, if_neg he2, if_pos hf]; cases hd : dadj e f <;> decide)
          | (rw [if_neg he, if_neg he2, if_neg hf, if_pos hf2]; cases hd : dadj e f <;> decide)
          | (rw [if_neg he, if_neg he2, if_neg hf, if_neg hf2]; cases hd : dadj e f <;> decide)
    · -- (c) inl e, inr(), inl g: E e g ∈ comp(conv(K e), K g)
      show (if e = g then eq else if dadj e g then dr else po)
        ∈ comp (conv (if e = v0 then ppi else if kdr e then dr else po))
               (if g = v0 then ppi else if kdr g then dr else po)
      by_cases heg : e = g
      · subst heg
        by_cases he : e = v0
        · rw [if_pos rfl, if_pos he]; decide
        · by_cases he2 : kdr e = true
          · rw [if_pos rfl, if_neg he, if_pos he2]; decide
          · rw [if_pos rfl, if_neg he, if_neg he2]; decide
      · rw [if_neg heg]
        by_cases he : e = v0 <;> by_cases he2 : kdr e = true <;>
          by_cases hg : g = v0 <;> by_cases hg2 : kdr g = true
        all_goals first
          | (subst he; subst hg; exact absurd rfl heg)
          | (rw [he, if_pos (show dadj v0 g = true from by rw [hsym v0 g]; exact hcoh g hg2), if_pos rfl, if_neg hg, if_pos hg2]; decide)
          | (rw [if_pos he, if_neg hg, if_neg hg2]; cases hd : dadj e g <;> decide)
          | (rw [hg, if_pos (hcoh e he2), if_neg he, if_pos he2, if_pos rfl]; decide)
          | (rw [if_neg he, if_pos he2, if_neg hg, if_pos hg2]; cases hd : dadj e g <;> decide)
          | (rw [if_neg he, if_pos he2, if_neg hg, if_neg hg2]; cases hd : dadj e g <;> decide)
          | (rw [if_neg he, if_neg he2, if_pos hg]; cases hd : dadj e g <;> decide)
          | (rw [if_neg he, if_neg he2, if_neg hg, if_pos hg2]; cases hd : dadj e g <;> decide)
          | (rw [if_neg he, if_neg he2, if_neg hg, if_neg hg2]; cases hd : dadj e g <;> decide)
    · -- (d)
      exact hce_r _
    · -- (e) inr(), inl f, inl g: K g ∈ comp(K f, E f g)
      show (if g = v0 then ppi else if kdr g then dr else po)
        ∈ comp (if f = v0 then ppi else if kdr f then dr else po)
               (if f = g then eq else if dadj f g then dr else po)
      by_cases hfg : f = g
      · subst hfg
        by_cases hf : f = v0
        · rw [if_pos rfl, if_pos hf]; decide
        · by_cases hf2 : kdr f = true
          · rw [if_pos rfl, if_neg hf, if_pos hf2]; decide
          · rw [if_pos rfl, if_neg hf, if_neg hf2]; decide
      · rw [if_neg hfg]
        by_cases hf : f = v0 <;> by_cases hf2 : kdr f = true <;>
          by_cases hg : g = v0 <;> by_cases hg2 : kdr g = true
        all_goals first
          | (subst hf; subst hg; exact absurd rfl hfg)
          | (rw [hf, if_neg hg, if_pos hg2, if_pos rfl, if_pos (show dadj v0 g = true from by rw [hsym v0 g]; exact hcoh g hg2)]; decide)
          | (rw [if_neg hg, if_neg hg2, if_pos hf]; cases hd : dadj f g <;> decide)
          | (rw [hg, if_pos rfl, if_neg hf, if_pos hf2, if_pos (hcoh f hf2)]; decide)
          | (rw [if_neg hg, if_pos hg2, if_neg hf, if_pos hf2]; cases hd : dadj f g <;> decide)
          | (rw [if_neg hg, if_neg hg2, if_neg hf, if_pos hf2]; cases hd : dadj f g <;> decide)
          | (rw [if_pos hg, if_neg hf, if_neg hf2]; cases hd : dadj f g <;> decide)
          | (rw [if_neg hg, if_pos hg2, if_neg hf, if_neg hf2]; cases hd : dadj f g <;> decide)
          | (rw [if_neg hg, if_neg hg2, if_neg hf, if_neg hf2]; cases hd : dadj f g <;> decide)
    · -- (f)
      show eq ∈ comp (if f = v0 then ppi else if kdr f then dr else po)
                     (conv (if f = v0 then ppi else if kdr f then dr else po))
      by_cases hf : f = v0
      · rw [if_pos hf]; decide
      · by_cases hf2 : kdr f = true
        · rw [if_neg hf, if_pos hf2]; decide
        · rw [if_neg hf, if_neg hf2]; decide
    · -- (g)
      exact hce_l _
    · show eq ∈ comp eq eq
      decide

open Classical in
/-- **THE FORCING-COMPLETION FRAME (third brick): MANY kernels, each with its
    DR-children.**  Combines `po_dr_multi_child_frame` (per-kernel forced
    DR-children) with `po_default_multi_frame` (cross-kernel PO-default `Q`).
    `κ` ascending kernels, `K k e` = `PPI` to attach `v0 k` / `DR` to `k`'s
    children (`kdr k e`) / `PO` else; cross-kernel `Q` = `PO`.  Coherence is
    PER-KERNEL: `hcoh k e : kdr k e → dadj e (v0 k) = true`.  The cross-kernel
    triangles ABSORB any `K` values (`PO`-default, `hKrange` + `decide`); the
    ext-ext-through-one-kernel triangles are the multi-child forcing for that
    kernel.  This is the qnet-level forcing-completion frame at full generality
    (arbitrary kernels + arbitrary coherent DR-children). -/
theorem po_dr_multi_kernel_frame {β κ : Type} (dadj : β → β → Bool)
    (hsym : ∀ v w, dadj v w = dadj w v) (v0 : κ → β) (kdr : κ → β → Bool)
    (hcoh : ∀ k e, kdr k e = true → dadj e (v0 k) = true) :
    Frame (qnet
      (fun e f => if e = f then eq else if dadj e f then dr else po)
      (fun k e => if e = v0 k then ppi else if kdr k e then dr else po)
      (fun (_ : κ) (_ : κ) => po)) := by
  have hE := symDrPo_frame dadj hsym
  have hce_r : ∀ r : Atom, r ∈ comp r eq := fun r => by cases r <;> decide
  have hce_l : ∀ r : Atom, r ∈ comp eq r := fun r => by cases r <;> decide
  have hKr : ∀ k e, (if e = v0 k then ppi else if kdr k e then dr else po) = ppi
      ∨ (if e = v0 k then ppi else if kdr k e then dr else po) = dr
      ∨ (if e = v0 k then ppi else if kdr k e then dr else po) = po := by
    intro k e
    by_cases he : e = v0 k
    · exact Or.inl (if_pos he)
    · by_cases hc : kdr k e = true
      · exact Or.inr (Or.inl (by rw [if_neg he, if_pos hc]))
      · exact Or.inr (Or.inr (by rw [if_neg he, if_neg hc]))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (e | k)
    · show (if e = e then eq else if dadj e e then dr else po) = eq; rw [if_pos rfl]
    · show (if k = k then eq else po) = eq; rw [if_pos rfl]
  · rintro (e | k) (f | k') h
    · refine congrArg Sum.inl ?_
      have h' : (if e = f then eq else if dadj e f then dr else po) = eq := h
      by_cases hef : e = f
      · exact hef
      · rw [if_neg hef] at h'
        by_cases hd : dadj e f = true
        · rw [if_pos hd] at h'; exact absurd h' (by decide)
        · rw [if_neg hd] at h'; exact absurd h' (by decide)
    · rcases hKr k' e with hv | hv | hv <;>
        exact absurd ((congrArg conv hv.symm).trans h) (by decide)
    · rcases hKr k f with hv | hv | hv <;> exact absurd (hv.symm.trans h) (by decide)
    · refine congrArg Sum.inr ?_
      by_cases hkk : k = k'
      · exact hkk
      · exact absurd (show (if k = k' then eq else po) = eq from h) (by rw [if_neg hkk]; decide)
  · rintro (e | k) (f | k')
    · show (if f = e then eq else if dadj f e then dr else po)
        = conv (if e = f then eq else if dadj e f then dr else po)
      exact hE.conv_ e f
    · show (if e = v0 k' then ppi else if kdr k' e then dr else po)
        = conv (conv (if e = v0 k' then ppi else if kdr k' e then dr else po))
      rcases hKr k' e with hv | hv | hv <;> rw [hv] <;> decide
    · rfl
    · show (if k' = k then eq else po) = conv (if k = k' then eq else po)
      by_cases hkk : k = k'
      · rw [if_pos hkk, if_pos hkk.symm]; decide
      · rw [if_neg hkk, if_neg (fun h => hkk h.symm)]; decide
  · rintro (e | k) (f | k') (g | k'')
    · show (if e = g then eq else if dadj e g then dr else po)
        ∈ comp (if e = f then eq else if dadj e f then dr else po)
               (if f = g then eq else if dadj f g then dr else po)
      exact hE.comp_ e f g
    · -- (2) inl e, inl f, inr k'': multi-child forcing for kernel k''
      show conv (if e = v0 k'' then ppi else if kdr k'' e then dr else po)
        ∈ comp (if e = f then eq else if dadj e f then dr else po)
               (conv (if f = v0 k'' then ppi else if kdr k'' f then dr else po))
      by_cases hef : e = f
      · subst hef
        by_cases he : e = v0 k''
        · rw [if_pos rfl, if_pos he]; decide
        · by_cases he2 : kdr k'' e = true
          · rw [if_pos rfl, if_neg he, if_pos he2]; decide
          · rw [if_pos rfl, if_neg he, if_neg he2]; decide
      · rw [if_neg hef]
        by_cases he : e = v0 k'' <;> by_cases he2 : kdr k'' e = true <;>
          by_cases hf : f = v0 k'' <;> by_cases hf2 : kdr k'' f = true
        all_goals first
          | (subst he; subst hf; exact absurd rfl hef)
          | (rw [he, if_pos rfl, if_pos (show dadj (v0 k'') f = true from by rw [hsym (v0 k'') f]; exact hcoh k'' f hf2), if_neg hf, if_pos hf2]; decide)
          | (rw [if_pos he, if_neg hf, if_neg hf2]; cases hd : dadj e f <;> decide)
          | (rw [hf, if_neg he, if_pos he2, if_pos (hcoh k'' e he2), if_pos rfl]; decide)
          | (rw [if_neg he, if_pos he2, if_neg hf, if_pos hf2]; cases hd : dadj e f <;> decide)
          | (rw [if_neg he, if_pos he2, if_neg hf, if_neg hf2]; cases hd : dadj e f <;> decide)
          | (rw [if_neg he, if_neg he2, if_pos hf]; cases hd : dadj e f <;> decide)
          | (rw [if_neg he, if_neg he2, if_neg hf, if_pos hf2]; cases hd : dadj e f <;> decide)
          | (rw [if_neg he, if_neg he2, if_neg hf, if_neg hf2]; cases hd : dadj e f <;> decide)
    · -- (3) inl e, inr k', inl g: multi-child forcing for kernel k'
      show (if e = g then eq else if dadj e g then dr else po)
        ∈ comp (conv (if e = v0 k' then ppi else if kdr k' e then dr else po))
               (if g = v0 k' then ppi else if kdr k' g then dr else po)
      by_cases heg : e = g
      · subst heg
        by_cases he : e = v0 k'
        · rw [if_pos rfl, if_pos he]; decide
        · by_cases he2 : kdr k' e = true
          · rw [if_pos rfl, if_neg he, if_pos he2]; decide
          · rw [if_pos rfl, if_neg he, if_neg he2]; decide
      · rw [if_neg heg]
        by_cases he : e = v0 k' <;> by_cases he2 : kdr k' e = true <;>
          by_cases hg : g = v0 k' <;> by_cases hg2 : kdr k' g = true
        all_goals first
          | (subst he; subst hg; exact absurd rfl heg)
          | (rw [he, if_pos (show dadj (v0 k') g = true from by rw [hsym (v0 k') g]; exact hcoh k' g hg2), if_pos rfl, if_neg hg, if_pos hg2]; decide)
          | (rw [if_pos he, if_neg hg, if_neg hg2]; cases hd : dadj e g <;> decide)
          | (rw [hg, if_pos (hcoh k' e he2), if_neg he, if_pos he2, if_pos rfl]; decide)
          | (rw [if_neg he, if_pos he2, if_neg hg, if_pos hg2]; cases hd : dadj e g <;> decide)
          | (rw [if_neg he, if_pos he2, if_neg hg, if_neg hg2]; cases hd : dadj e g <;> decide)
          | (rw [if_neg he, if_neg he2, if_pos hg]; cases hd : dadj e g <;> decide)
          | (rw [if_neg he, if_neg he2, if_neg hg, if_pos hg2]; cases hd : dadj e g <;> decide)
          | (rw [if_neg he, if_neg he2, if_neg hg, if_neg hg2]; cases hd : dadj e g <;> decide)
    · -- (4) inl e, inr k', inr k'': cross-kernel
      show conv (if e = v0 k'' then ppi else if kdr k'' e then dr else po)
        ∈ comp (conv (if e = v0 k' then ppi else if kdr k' e then dr else po))
               (if k' = k'' then eq else po)
      by_cases hkk : k' = k''
      · subst hkk; rw [if_pos rfl]; exact hce_r _
      · rw [if_neg hkk]
        rcases hKr k' e with h | h | h <;> rcases hKr k'' e with h' | h' | h' <;>
          rw [h, h'] <;> decide
    · -- (5) inr k, inl f, inl g: multi-child forcing for kernel k
      show (if g = v0 k then ppi else if kdr k g then dr else po)
        ∈ comp (if f = v0 k then ppi else if kdr k f then dr else po)
               (if f = g then eq else if dadj f g then dr else po)
      by_cases hfg : f = g
      · subst hfg
        by_cases hf : f = v0 k
        · rw [if_pos rfl, if_pos hf]; decide
        · by_cases hf2 : kdr k f = true
          · rw [if_pos rfl, if_neg hf, if_pos hf2]; decide
          · rw [if_pos rfl, if_neg hf, if_neg hf2]; decide
      · rw [if_neg hfg]
        by_cases hf : f = v0 k <;> by_cases hf2 : kdr k f = true <;>
          by_cases hg : g = v0 k <;> by_cases hg2 : kdr k g = true
        all_goals first
          | (subst hf; subst hg; exact absurd rfl hfg)
          | (rw [hf, if_neg hg, if_pos hg2, if_pos rfl, if_pos (show dadj (v0 k) g = true from by rw [hsym (v0 k) g]; exact hcoh k g hg2)]; decide)
          | (rw [if_neg hg, if_neg hg2, if_pos hf]; cases hd : dadj f g <;> decide)
          | (rw [hg, if_pos rfl, if_neg hf, if_pos hf2, if_pos (hcoh k f hf2)]; decide)
          | (rw [if_neg hg, if_pos hg2, if_neg hf, if_pos hf2]; cases hd : dadj f g <;> decide)
          | (rw [if_neg hg, if_neg hg2, if_neg hf, if_pos hf2]; cases hd : dadj f g <;> decide)
          | (rw [if_pos hg, if_neg hf, if_neg hf2]; cases hd : dadj f g <;> decide)
          | (rw [if_neg hg, if_pos hg2, if_neg hf, if_neg hf2]; cases hd : dadj f g <;> decide)
          | (rw [if_neg hg, if_neg hg2, if_neg hf, if_neg hf2]; cases hd : dadj f g <;> decide)
    · -- (6) inr k, inl f, inr k'': cross-kernel
      show (if k = k'' then eq else po)
        ∈ comp (if f = v0 k then ppi else if kdr k f then dr else po)
               (conv (if f = v0 k'' then ppi else if kdr k'' f then dr else po))
      by_cases hkk : k = k''
      · subst hkk; rw [if_pos rfl]
        rcases hKr k f with h | h | h <;> rw [h] <;> decide
      · rw [if_neg hkk]
        rcases hKr k f with h | h | h <;> rcases hKr k'' f with h' | h' | h' <;>
          rw [h, h'] <;> decide
    · -- (7) inr k, inr k', inl g: cross-kernel
      show (if g = v0 k then ppi else if kdr k g then dr else po)
        ∈ comp (if k = k' then eq else po)
               (if g = v0 k' then ppi else if kdr k' g then dr else po)
      by_cases hkk : k = k'
      · subst hkk; rw [if_pos rfl]
        rcases hKr k g with h | h | h <;> rw [h] <;> decide
      · rw [if_neg hkk]
        rcases hKr k g with h | h | h <;> rcases hKr k' g with h' | h' | h' <;>
          rw [h, h'] <;> decide
    · -- (8) inr k, inr k', inr k''
      show (if k = k'' then eq else po)
        ∈ comp (if k = k' then eq else po) (if k' = k'' then eq else po)
      by_cases hkk'' : k = k''
      · by_cases hkk' : k = k'
        · have hk'k'' : k' = k'' := hkk'.symm.trans hkk''
          rw [if_pos hkk'', if_pos hkk', if_pos hk'k'']; decide
        · have hk'k'' : k' ≠ k'' := fun h => hkk' (hkk''.trans h.symm)
          rw [if_pos hkk'', if_neg hkk', if_neg hk'k'']; decide
      · rw [if_neg hkk'']
        by_cases hkk' : k = k' <;> by_cases hk'k'' : k' = k''
        · exact absurd (hkk'.trans hk'k'') hkk''
        · rw [if_pos hkk', if_neg hk'k'']; decide
        · rw [if_neg hkk', if_pos hk'k'']; decide
        · rw [if_neg hkk', if_neg hk'k'']; decide

/-! ### The ∀DR-propagation fragment: tree-structural assembly (lift Step 2)

The first fragment with genuine `∀`-firing certified end-to-end without
kernels: **`∀DR`-propagation over a `DR`/`PO`/`EQ` frame**.  Every
existential is `∃DR` or `∃PO` (horizontal), every universal is `∀DR`
(hence `∀PO`-free), and each `∀DR` guards a `DR`-free (propositional)
body.  Concretely it contains `∀DR.A`, `∀DR.(A ⊔ B)`, `∃DR.(∀DR.A ⊓ C)`,
`∃PO.A` — constraint propagation to all `DR`-neighbours plus `PO`
existentials — the paradigm horizontal `∀DR` usage.

The certificate: `β = snodes root` (the saturated-label coverage nodes),
`tauE = slabel` (saturated so `∀DR` obligations fire reverse), the
tree-structural frame (`symDrPo_frame`, `DR` on `∃DR`-demand edges, `PO`
elsewhere — including `∃PO`-demand children, which `po_not_sAdj` keeps off
the `DR`-adjacency — `EQ` on the diagonal), no kernels.  `ee_all` on `DR`
edges is the `∀DR` reverse-firing (`slabel_dr_forward`/`_reverse`); on
`PO`/`EQ` edges it is vacuous (no `∀PO`, no `∀EQ` in this fragment);
`e_ex` is coverage (`snodes_covers` via the explicit `schildNode`). -/

section PODRAssembly

variable {α : Type} {I : Interp α} {C0 : Concept}

/-- THE ∀DR-PROPAGATION FRAGMENT (assembly hypotheses on the closure):
    every existential horizontal (`∃DR` or `∃PO`), every universal `∀DR`
    (so `∀PO`-free), each `∀DR` DR-guard-free.  A concept satisfying
    `DRFrag` has, at every reachable node, only `DR`/`PO` demands and only
    `∀DR` universals with propositional bodies. -/
structure DRFrag (C0 : Concept) : Prop where
  hex : ∀ r c, Concept.ex r c ∈ cl C0 → r = dr ∨ r = po
  hall : ∀ r c, Concept.all r c ∈ cl C0 → r = dr
  hgf : ∀ c, Concept.all dr c ∈ cl C0 → noDR c

/-- Symmetric `DR`-adjacency of reachable nodes: `m'` is a `∃DR`-child of
    `m`, or vice versa.  The tree-structural frame's `DR` predicate. -/
def sAdj (hI : RCC5Interp I) (m m' : RNode I C0) : Prop :=
  (∃ (c : Concept) (hF : Concept.ex dr c ∈ slabel m), schildNode hI m hF = m') ∨
  (∃ (c : Concept) (hF : Concept.ex dr c ∈ slabel m'), schildNode hI m' hF = m)

theorem sAdj_symm (hI : RCC5Interp I) (m m' : RNode I C0) :
    sAdj hI m m' ↔ sAdj hI m' m :=
  ⟨Or.symm, Or.symm⟩

/-- A child at a non-`EQ` demand is a genuinely fresh model element
    (strong-EQ: `I.rho m.x child.x = r ≠ eq` forces `m.x ≠ child.x`).  So
    a demand child is never the parent — the frame's off-diagonal. -/
theorem schildNode_x_ne (hI : RCC5Interp I) (m : RNode I C0) {r : Atom}
    {c : Concept} (hF : Concept.ex r c ∈ slabel m) (hrne : r ≠ eq) :
    m.x ≠ (schildNode hI m hF).x := by
  intro hx
  have hrho := schildNode_rho hI m hF
  rw [← hx, hI.refl_eq m.x m.hdom] at hrho
  exact hrne hrho.symm

/-- `DR`-adjacent nodes are `DR`-related in the model — either directly
    (`m'` a `∃DR`-child of `m`) or via converse (`conv DR = DR`). -/
theorem sAdj_rho_dr (hI : RCC5Interp I) {m m' : RNode I C0}
    (h : sAdj hI m m') : I.rho m.x m'.x = dr := by
  rcases h with ⟨_, hF, hchild⟩ | ⟨_, hF, hchild⟩
  · have hrho := schildNode_rho hI m hF
    rw [hchild] at hrho; exact hrho
  · have hrho := schildNode_rho hI m' hF
    rw [hchild] at hrho
    have hc := hI.conv_ m'.x m.x m'.hdom m.hdom
    rw [hrho] at hc
    rw [hc]; decide

/-- KEY FOR `∃PO`: a `PO`-child is NEVER `DR`-adjacent to its parent.  A
    `DR`-adjacency would force `I.rho m.x m'.x = dr` (`sAdj_rho_dr`), but a
    `PO`-child has `I.rho m.x m'.x = po` — `PO ≠ DR`, and `conv PO = PO`
    blocks the reverse orientation too.  So `∃PO` demands land on genuine
    `PO` frame edges (which fire nothing, `∀PO`-free). -/
theorem po_not_sAdj (hI : RCC5Interp I) {m m' : RNode I C0}
    (h : I.rho m.x m'.x = po) : ¬ sAdj hI m m' := by
  intro hadj
  rw [sAdj_rho_dr hI hadj] at h
  exact absurd h (by decide)

open Classical in
/-- The frame's `DR`-adjacency as a decidable predicate on the coverage
    nodes (classical, matching the model-side layer). -/
noncomputable def dadjB (hI : RCC5Interp I) (root : RNode I C0)
    (m m' : {m // m ∈ snodes hI root}) : Bool :=
  decide (sAdj hI m.val m'.val)

theorem dadjB_symm (hI : RCC5Interp I) (root : RNode I C0)
    (m m' : {m // m ∈ snodes hI root}) :
    dadjB hI root m m' = dadjB hI root m' m := by
  unfold dadjB
  rw [propext (sAdj_symm hI m.val m'.val)]

open Classical in
/-- THE ∀DR-PROPAGATION CERTIFICATE: coverage nodes, tree-structural
    frame, saturated labels, no kernels. -/
noncomputable def mtDR (hI : RCC5Interp I) (root : RNode I C0) :
    MultiTier {m // m ∈ snodes hI root} Empty where
  E m m' := if m = m' then eq else if dadjB hI root m m' then dr else po
  K k _ := k.elim
  Q k _ := k.elim
  up k := k.elim
  tauE m := slabel m.val
  p k := k.elim
  phase k _ := k.elim

/-- The certificate's frame is a genuine RCC5 frame — the tree-structural
    `{DR,PO,EQ}` labelling (`symDrPo_frame`), lifted through the empty
    kernel quotient (`qnet_empty_frame`). -/
theorem mtDR_frame (hI : RCC5Interp I) (root : RNode I C0) :
    Frame (qnet (mtDR hI root).E (mtDR hI root).K (mtDR hI root).Q) := by
  apply qnet_empty_frame
  refine frame_ext ?_ (symDrPo_frame (dadjB hI root) (dadjB_symm hI root))
  intro v w
  simp only [mtDR]
  by_cases h : v = w
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

open Classical in
/-- THE ∀DR-PROPAGATION CERTIFICATE IS VALID.  Propositional conditions
    from `slabel` saturation; `ee_all` on `DR` edges = the `∀DR`
    reverse-firing, on `PO`/`EQ` edges vacuous (no `∀PO`/`∀EQ`); `e_ex` =
    coverage; kernels vacuous. -/
theorem mtDR_ok (hI : RCC5Interp I) (hfrag : DRFrag C0)
    (root : RNode I C0) : MultiTierOk (mtDR hI root) where
  hp := fun k => k.elim
  frame_q := mtDR_frame hI root
  e_clash := fun e _ h => slabel_clash hI e.val h
  e_nobot := fun e => slabel_nobot hI e.val
  e_and := fun e _ _ h => slabel_and e.val h
  e_or := fun e _ _ h => slabel_or e.val h
  k_clash := fun k => k.elim
  k_nobot := fun k => k.elim
  k_and := fun k => k.elim
  k_or := fun k => k.elim
  ee_all := by
    intro e f r c hallc hEf
    have hr : r = dr := hfrag.hall r c (slabel_sub_cl e.val _ hallc)
    subst hr
    have hEf' : (if e = f then eq
        else if dadjB hI root e f then dr else po) = dr := hEf
    by_cases hef : e = f
    · rw [if_pos hef] at hEf'; exact absurd hEf' (by decide)
    · rw [if_neg hef] at hEf'
      have hd : dadjB hI root e f = true := by
        cases hb : dadjB hI root e f with
        | true => rfl
        | false => rw [hb] at hEf'; exact absurd hEf' (by decide)
      have hadj : sAdj hI e.val f.val := of_decide_eq_true hd
      show c ∈ slabel f.val
      rcases hadj with ⟨_, hF, hchild⟩ | ⟨_, hF, hchild⟩
      · have hc := slabel_dr_forward hfrag.hgf hI e.val hF hallc
        rw [hchild] at hc; exact hc
      · apply slabel_dr_reverse hfrag.hgf hI f.val hF
        rw [hchild]; exact hallc
  ek_all := fun _ _ _ _ k => k.elim
  ke_all := fun k => k.elim
  kk_pp := fun k => k.elim
  kk_ppi := fun k => k.elim
  kk_eq := fun k => k.elim
  kq_all := fun k => k.elim
  e_ex := by
    intro e r c hdem
    have hrne : r ≠ eq := by
      rcases hfrag.hex r c (slabel_sub_cl e.val _ hdem) with h | h <;>
        rw [h] <;> decide
    have hmem : schildNode hI e.val hdem ∈ snodes hI root :=
      snodes_trans hI root e.val e.property _ (schildNode_mem hI e.val hdem)
    have hne : e ≠ ⟨schildNode hI e.val hdem, hmem⟩ := fun heq =>
      schildNode_x_ne hI e.val hdem hrne (congrArg (fun t => t.val.x) heq)
    refine Or.inl ⟨⟨schildNode hI e.val hdem, hmem⟩, ?_,
      schildNode_arg hI e.val hdem⟩
    rcases hfrag.hex r c (slabel_sub_cl e.val _ hdem) with hr | hr
    · -- `∃DR` demand: `DR`-adjacent child, frame edge = `DR`
      subst hr
      have hd : dadjB hI root e ⟨schildNode hI e.val hdem, hmem⟩ = true := by
        show decide (sAdj hI e.val (schildNode hI e.val hdem)) = true
        rw [decide_eq_true_eq]; exact Or.inl ⟨c, hdem, rfl⟩
      show (if e = ⟨schildNode hI e.val hdem, hmem⟩ then eq
        else if dadjB hI root e ⟨schildNode hI e.val hdem, hmem⟩ then dr
          else po) = dr
      rw [if_neg hne]; exact if_pos hd
    · -- `∃PO` demand: `PO`-child is NOT `DR`-adjacent, frame edge = `PO`
      subst hr
      have hd : ¬ dadjB hI root e ⟨schildNode hI e.val hdem, hmem⟩ = true := by
        show ¬ decide (sAdj hI e.val (schildNode hI e.val hdem)) = true
        rw [decide_eq_true_eq]
        exact po_not_sAdj hI (schildNode_rho hI e.val hdem)
      show (if e = ⟨schildNode hI e.val hdem, hmem⟩ then eq
        else if dadjB hI root e ⟨schildNode hI e.val hdem, hmem⟩ then dr
          else po) = po
      rw [if_neg hne]; exact if_neg hd
  k_ex := fun k => k.elim

/-- THE ∀DR-PROPAGATION EXTRACTION: every satisfiable `DRFrag` concept has
    a VALID FINITE multi-tier certificate carrying it — the horizontal
    recursion with saturated labels, `ee_all` discharged by the `∀DR`
    reverse-firing, `e_ex` by coverage. -/
theorem extract_podr (C0 : Concept) (hfrag : DRFrag C0)
    (hsat : Satisfiable C0) :
    ∃ (β : Type) (T : MultiTier β Empty) (g : β),
      MultiTierOk T ∧ C0 ∈ T.tauE g := by
  obtain ⟨α, I, hI, x0, hdom0, hsat0⟩ := hsat
  let root : RNode I C0 :=
    { x := x0, s := [C0], hdom := hdom0
      hmty := fun F hF => by
        rw [List.mem_singleton.mp hF]
        exact mem_mty.mpr ⟨cl_self C0, hsat0⟩
      hcl := fun F hF => by
        rw [List.mem_singleton.mp hF]
        exact cl_self C0 }
  refine ⟨{m // m ∈ snodes hI root}, mtDR hI root,
    ⟨root, self_mem_snodes hI root⟩, mtDR_ok hI hfrag root, ?_⟩
  show C0 ∈ slabel root
  exact reqType_sub_slabel root C0
    (mem_reqType_of_mem (x := root.x) List.mem_cons_self)

/-- **∀DR-PROPAGATION SATISFIABILITY ⟺ A MULTI-TIER CERTIFICATE.**  Both
    directions kernel-checked: `←` the certified soundness pipeline
    (`multiTier_sound`), `→` the extraction (`extract_podr`).  This is the
    lift beyond `AllFree`: a fragment with genuine `∀`-firing (`∀DR`
    constraint propagation), certified via the saturated-label recursion
    and the tree-structural frame, no kernels.  Like the `AllFree` case
    this is a CERTIFICATE CHARACTERIZATION — `β` is quantified as an
    arbitrary `Type`; the finite-`β`/`K(C₀)` bound giving Decidability is
    the remaining step. -/
theorem satisfiable_iff_podr_cert (C0 : Concept) (hfrag : DRFrag C0) :
    Satisfiable C0 ↔
      ∃ (β : Type) (T : MultiTier β Empty) (g : β),
        MultiTierOk T ∧ C0 ∈ T.tauE g := by
  constructor
  · exact extract_podr C0 hfrag
  · rintro ⟨β, T, g, hok, hC0⟩
    exact multiTier_sound T hok (Sum.inl g) C0 hC0

end PODRAssembly

/-! ### The model-type-truncated-by-depth label (`mtk`, `ASSEMBLY_DESIGN.md §15`)

A cleaner route to the full horizontal fragment (nested `∀DR`, `∀PP`/
`∀PPI`, `∀EQ`/`∃EQ`, `∃PO`) — dissolving the `∀DR`-fixpoint of design (B)
and the `∃EQ`/`∀EQ` fold of (A) at once.  The label is the model type
TRUNCATED BY MODAL DEPTH: model-true formulas of depth `≤ k`.  The model
is already `∀`-closed (it satisfies every universal, both directions via
`conv`), and depth-truncation gives termination — so no syntactic
reverse-firing recursion is needed.  Valid only for a CERTIFICATE
CHARACTERIZATION (the extraction has the model in hand); the syntactic
`reqType` labels stay for the eventual decidability layer. -/

section MtkLabel

variable {C0 : Concept} {α : Type} {I : Interp α}

/-- The depth-`k` model type: model-true formulas of modal depth `≤ k`. -/
noncomputable def mtk (C0 : Concept) (I : Interp α) (x : α) (k : Nat) :
    List Concept :=
  (mty C0 I x).filter (fun F => decide (mdepth F ≤ k))

theorem mem_mtk {x : α} {k : Nat} {F : Concept} :
    F ∈ mtk C0 I x k ↔ F ∈ mty C0 I x ∧ mdepth F ≤ k := by
  constructor
  · intro h
    have h2 := List.mem_filter.mp h
    exact ⟨h2.1, of_decide_eq_true h2.2⟩
  · intro ⟨h1, h2⟩
    exact List.mem_filter.mpr ⟨h1, decide_eq_true h2⟩

theorem mtk_sub_cl {x : α} {k : Nat} : ∀ F ∈ mtk C0 I x k, F ∈ cl C0 :=
  fun _ hF => mty_sub _ (mem_mtk.mp hF).1

theorem mtk_clash {x : α} {k : Nat} {a : Nat}
    (h : Concept.atom a ∈ mtk C0 I x k) : Concept.natom a ∉ mtk C0 I x k :=
  fun h2 => mty_clash (mem_mtk.mp h).1 (mem_mtk.mp h2).1

theorem mtk_nobot {x : α} {k : Nat} : Concept.bot ∉ mtk C0 I x k :=
  fun h => mty_nobot (mem_mtk.mp h).1

theorem mtk_and {x : α} {k : Nat} {c d : Concept}
    (h : Concept.and c d ∈ mtk C0 I x k) :
    c ∈ mtk C0 I x k ∧ d ∈ mtk C0 I x k := by
  obtain ⟨hmty, hk⟩ := mem_mtk.mp h
  obtain ⟨hc, hd⟩ := mty_and hmty
  exact ⟨mem_mtk.mpr ⟨hc, Nat.le_trans (Nat.le_max_left _ _) hk⟩,
    mem_mtk.mpr ⟨hd, Nat.le_trans (Nat.le_max_right _ _) hk⟩⟩

theorem mtk_or {x : α} {k : Nat} {c d : Concept}
    (h : Concept.or c d ∈ mtk C0 I x k) :
    c ∈ mtk C0 I x k ∨ d ∈ mtk C0 I x k := by
  obtain ⟨hmty, hk⟩ := mem_mtk.mp h
  rcases mty_or hmty with hc | hd
  · exact Or.inl (mem_mtk.mpr ⟨hc, Nat.le_trans (Nat.le_max_left _ _) hk⟩)
  · exact Or.inr (mem_mtk.mpr ⟨hd, Nat.le_trans (Nat.le_max_right _ _) hk⟩)

/-- FORWARD `∀`-firing: a depth-`k` universal fires its argument into an
    `r`-neighbour's depth-`(k-1)` label (the model gives `c`, depth drops). -/
theorem mtk_all_fwd {x y : α} {k : Nat} {r : Atom} {c : Concept}
    (h : Concept.all r c ∈ mtk C0 I x k) (hy : I.dom y) (hr : I.rho x y = r) :
    c ∈ mtk C0 I y (k - 1) := by
  obtain ⟨hmty, hk⟩ := mem_mtk.mp h
  refine mem_mtk.mpr ⟨mty_all hmty hy hr, ?_⟩
  have : mdepth c + 1 ≤ k := hk
  omega

/-- REVERSE `∀DR`-firing (the crux, free from the model): a `∀DR` at a
    depth-`(k-1)` `DR`-child fires back into the parent's depth-`k` label
    — `conv DR = DR` makes the parent a `DR`-neighbour (`dr_reverse_sat`). -/
theorem mtk_all_dr_rev (hI : RCC5Interp I) {x y : α} {k : Nat} {c : Concept}
    (h : Concept.all dr c ∈ mtk C0 I y (k - 1)) (hx : I.dom x) (hy : I.dom y)
    (hr : I.rho x y = dr) : c ∈ mtk C0 I x k := by
  obtain ⟨hmty, hk⟩ := mem_mtk.mp h
  refine mem_mtk.mpr ⟨dr_reverse_sat hI hx hy hr hmty, ?_⟩
  have : mdepth c + 1 ≤ k - 1 := hk
  omega

/-- `∀EQ` reflexive fold: `∀EQ.c` at `x` gives `c` at `x` (`ρ x x = eq`). -/
theorem mtk_all_eq (hI : RCC5Interp I) {x : α} {k : Nat} {c : Concept}
    (h : Concept.all eq c ∈ mtk C0 I x k) (hx : I.dom x) : c ∈ mtk C0 I x k := by
  obtain ⟨hmty, hk⟩ := mem_mtk.mp h
  refine mem_mtk.mpr ⟨mty_all hmty hx (hI.refl_eq x hx), ?_⟩
  have : mdepth c + 1 ≤ k := hk
  omega

/-- `∃`-witnessing: a depth-`k` existential has a model witness carrying
    its argument at depth `k-1`. -/
theorem mtk_ex {x : α} {k : Nat} {r : Atom} {c : Concept}
    (h : Concept.ex r c ∈ mtk C0 I x k) :
    ∃ y, I.dom y ∧ I.rho x y = r ∧ c ∈ mtk C0 I y (k - 1) := by
  obtain ⟨hmty, hk⟩ := mem_mtk.mp h
  obtain ⟨y, hy, hr, hc⟩ := mty_ex hmty
  refine ⟨y, hy, hr, mem_mtk.mpr ⟨hc, ?_⟩⟩
  have : mdepth c + 1 ≤ k := hk
  omega

/-- `∃EQ` reflexive fold: `∃EQ.c` at `x` gives `c` at `x` (strong EQ:
    the `EQ`-witness IS `x`). -/
theorem mtk_ex_eq (hI : RCC5Interp I) {x : α} {k : Nat} {c : Concept}
    (h : Concept.ex eq c ∈ mtk C0 I x k) (hx : I.dom x) : c ∈ mtk C0 I x k := by
  obtain ⟨hmty, hk⟩ := mem_mtk.mp h
  obtain ⟨y, hy, hr, hc⟩ := mty_ex hmty
  have hxy : x = y := hI.eq_id x y hx hy hr
  rw [← hxy] at hc
  refine mem_mtk.mpr ⟨hc, ?_⟩
  have : mdepth c + 1 ≤ k := hk
  omega

end MtkLabel

/-! ### The depth-bounded coverage recursion (`mtkNodes`)

Parallels `rnodes`/`snodes`, but terminates on the budget `k` directly
(no `lmd`): each demand's witness lives at depth `k-1`, and any demand
forces `k ≥ 1`.  Its coverage theorem `mtkNodes_covers` discharges `e_ex`. -/

section MtkRecursion

variable {α : Type} {I : Interp α} {C0 : Concept}

/-- A reachable node: a model element with a depth budget.  `C0` is
    carried in the type so the (phantom) label parameter is inferable. -/
structure MTKNode (I : Interp α) (C0 : Concept) where
  x : α
  k : Nat
  hx : I.dom x

/-- The child covering a demand: its model witness, budget one less. -/
noncomputable def mtkWitness (n : MTKNode I C0) {r : Atom} {c : Concept}
    (hF : Concept.ex r c ∈ mtk C0 I n.x n.k) : MTKNode I C0 :=
  ⟨Classical.choose (mtk_ex hF), n.k - 1, (Classical.choose_spec (mtk_ex hF)).1⟩

theorem mtkWitness_rho (n : MTKNode I C0) {r : Atom} {c : Concept}
    (hF : Concept.ex r c ∈ mtk C0 I n.x n.k) :
    I.rho n.x (mtkWitness n hF).x = r :=
  (Classical.choose_spec (mtk_ex hF)).2.1

theorem mtkWitness_arg (n : MTKNode I C0) {r : Atom} {c : Concept}
    (hF : Concept.ex r c ∈ mtk C0 I n.x n.k) :
    c ∈ mtk C0 I (mtkWitness n hF).x (mtkWitness n hF).k :=
  (Classical.choose_spec (mtk_ex hF)).2.2

/-- Termination for `mtkNodes`: the child's budget is strictly smaller
    (a demand forces `n.k ≥ 1`). -/
theorem mtkWitness_k_lt (n : MTKNode I C0) {r : Atom} {c : Concept}
    (hF : Concept.ex r c ∈ mtk C0 I n.x n.k) : (mtkWitness n hF).k < n.k := by
  have hk : mdepth c + 1 ≤ n.k := (mem_mtk.mp hF).2
  show n.k - 1 < n.k
  omega

/-- The depth-bounded coverage node set. -/
noncomputable def mtkNodes (n : MTKNode I C0) : List (MTKNode I C0) :=
  n :: (mtk C0 I n.x n.k).attach.flatMap
    (fun p => match p with
      | ⟨.ex r c, hF⟩ => mtkNodes (mtkWitness n hF)
      | _ => [])
termination_by n.k
decreasing_by exact mtkWitness_k_lt n hF

theorem self_mem_mtkNodes (n : MTKNode I C0) : n ∈ mtkNodes n := by
  rw [mtkNodes]; exact List.mem_cons_self

theorem sub_mtkNodes_witness (n : MTKNode I C0) {r : Atom} {c : Concept}
    (hF : Concept.ex r c ∈ mtk C0 I n.x n.k) :
    ∀ m ∈ mtkNodes (mtkWitness n hF), m ∈ mtkNodes n := by
  intro m hm
  rw [mtkNodes]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
    ⟨⟨Concept.ex r c, hF⟩, List.mem_attach _ _, hm⟩)

theorem mtkWitness_mem (n : MTKNode I C0) {r : Atom} {c : Concept}
    (hF : Concept.ex r c ∈ mtk C0 I n.x n.k) :
    mtkWitness n hF ∈ mtkNodes n :=
  sub_mtkNodes_witness n hF _ (self_mem_mtkNodes _)

theorem mtkNodes_trans (n : MTKNode I C0) :
    ∀ m ∈ mtkNodes n, ∀ k ∈ mtkNodes m, k ∈ mtkNodes n := by
  induction n using mtkNodes.induct with
  | _ x ih =>
    intro m hm k hk
    rw [mtkNodes] at hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact hk
    · obtain ⟨⟨F, hF⟩, _, hmm⟩ := List.mem_flatMap.mp hm'
      cases F with
      | ex r c => exact sub_mtkNodes_witness x hF k (ih r c hF m hmm k hk)
      | top => exact absurd hmm List.not_mem_nil
      | bot => exact absurd hmm List.not_mem_nil
      | atom a => exact absurd hmm List.not_mem_nil
      | natom a => exact absurd hmm List.not_mem_nil
      | and a b => exact absurd hmm List.not_mem_nil
      | or a b => exact absurd hmm List.not_mem_nil
      | all r c => exact absurd hmm List.not_mem_nil

/-- COVERAGE: every demand at any reachable node is fulfilled by a
    reachable node (its model witness). -/
theorem mtkNodes_covers (root : MTKNode I C0) :
    ∀ m ∈ mtkNodes root, ∀ (r : Atom) (c : Concept),
      Concept.ex r c ∈ mtk C0 I m.x m.k →
      ∃ m' ∈ mtkNodes root,
        I.rho m.x m'.x = r ∧ c ∈ mtk C0 I m'.x m'.k := by
  intro m hm r c hF
  exact ⟨mtkWitness m hF,
    mtkNodes_trans root m hm _ (mtkWitness_mem m hF),
    mtkWitness_rho m hF, mtkWitness_arg m hF⟩

/-- **THE HORIZONTAL-ONLY COVERAGE NODE SET** (step 4): like `mtkNodes` but the
    recursion STOPS at `∃PP`/`∃PPI` demands — those attach a kernel (the tree
    frame has no `PP`/`PPI` edges), only `∃DR`/`∃PO`/`∃EQ` spawn horizontal
    children.  So `mtkNodesH` is the horizontal skeleton; the vertical demands
    are the kernel's job. -/
noncomputable def mtkNodesH (n : MTKNode I C0) : List (MTKNode I C0) :=
  n :: (mtk C0 I n.x n.k).attach.flatMap
    (fun p => match p with
      | ⟨.ex r c, hF⟩ =>
        if r = pp ∨ r = ppi then [] else mtkNodesH (mtkWitness n hF)
      | _ => [])
termination_by n.k
decreasing_by exact mtkWitness_k_lt n hF

theorem self_mem_mtkNodesH (n : MTKNode I C0) : n ∈ mtkNodesH n := by
  rw [mtkNodesH]; exact List.mem_cons_self

theorem sub_mtkNodesH_witness (n : MTKNode I C0) {r : Atom} {c : Concept}
    (hF : Concept.ex r c ∈ mtk C0 I n.x n.k) (hv : ¬ (r = pp ∨ r = ppi)) :
    ∀ m ∈ mtkNodesH (mtkWitness n hF), m ∈ mtkNodesH n := by
  intro m hm
  rw [mtkNodesH]
  refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr
    ⟨⟨Concept.ex r c, hF⟩, List.mem_attach _ _, ?_⟩)
  show m ∈ (if r = pp ∨ r = ppi then ([] : List (MTKNode I C0))
    else mtkNodesH (mtkWitness n hF))
  rw [if_neg hv]; exact hm

theorem mtkWitnessH_mem (n : MTKNode I C0) {r : Atom} {c : Concept}
    (hF : Concept.ex r c ∈ mtk C0 I n.x n.k) (hv : ¬ (r = pp ∨ r = ppi)) :
    mtkWitness n hF ∈ mtkNodesH n :=
  sub_mtkNodesH_witness n hF hv _ (self_mem_mtkNodesH _)

theorem mtkNodesH_trans (n : MTKNode I C0) :
    ∀ m ∈ mtkNodesH n, ∀ k ∈ mtkNodesH m, k ∈ mtkNodesH n := by
  induction n using mtkNodesH.induct with
  | _ x ih =>
    intro m hm k hk
    rw [mtkNodesH] at hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact hk
    · obtain ⟨⟨F, hF⟩, _, hmm⟩ := List.mem_flatMap.mp hm'
      cases F with
      | ex r c =>
        have hmm2 : m ∈ (if r = pp ∨ r = ppi then ([] : List (MTKNode I C0))
            else mtkNodesH (mtkWitness x hF)) := hmm
        by_cases hv : r = pp ∨ r = ppi
        · rw [if_pos hv] at hmm2; exact absurd hmm2 List.not_mem_nil
        · rw [if_neg hv] at hmm2
          exact sub_mtkNodesH_witness x hF hv k (ih r c hF m hmm2 k hk)
      | top => exact absurd hmm List.not_mem_nil
      | bot => exact absurd hmm List.not_mem_nil
      | atom a => exact absurd hmm List.not_mem_nil
      | natom a => exact absurd hmm List.not_mem_nil
      | and a b => exact absurd hmm List.not_mem_nil
      | or a b => exact absurd hmm List.not_mem_nil
      | all r c => exact absurd hmm List.not_mem_nil

/-- HORIZONTAL COVERAGE: every NON-vertical demand (`∃DR`/`∃PO`/`∃EQ`) at any
    reachable node is fulfilled by a reachable node. -/
theorem mtkNodesH_covers (root : MTKNode I C0) :
    ∀ m ∈ mtkNodesH root, ∀ (r : Atom) (c : Concept),
      Concept.ex r c ∈ mtk C0 I m.x m.k → ¬ (r = pp ∨ r = ppi) →
      ∃ m' ∈ mtkNodesH root,
        I.rho m.x m'.x = r ∧ c ∈ mtk C0 I m'.x m'.k := by
  intro m hm r c hF hv
  exact ⟨mtkWitness m hF,
    mtkNodesH_trans root m hm _ (mtkWitnessH_mem m hF hv),
    mtkWitness_rho m hF, mtkWitness_arg m hF⟩

/-- A computable size bound: `mtkBound C0 k = 1 + |cl C0|·(previous)`,
    i.e. `(|cl C0|+1)^k` unrolled — bounds `|mtkNodes n|` at budget `k`. -/
def mtkBound (C0 : Concept) : Nat → Nat
  | 0 => 1
  | k + 1 => 1 + (cl C0).length * mtkBound C0 k

/-- `sum (map g l) ≤ |l| · M` when every `g a ≤ M`. -/
theorem sum_map_le {A : Type} (l : List A) (g : A → Nat) (M : Nat)
    (h : ∀ a ∈ l, g a ≤ M) : (l.map g).sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 : g a ≤ M := h a (List.mem_cons_self ..)
    have h2 : (t.map g).sum ≤ t.length * M :=
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    calc g a + (t.map g).sum ≤ M + t.length * M := Nat.add_le_add h1 h2
      _ = (t.length + 1) * M := by rw [Nat.succ_mul, Nat.add_comm]

/-- **THE COVERAGE NODE SET IS SIZE-BOUNDED** by `mtkBound C0 n.k`
    (`K(C₀)` for the root, budget `= mdepth C0`).  Makes the `codes`
    enumeration finite. -/
theorem mtkNodes_length_le (n : MTKNode I C0) :
    (mtkNodes n).length ≤ mtkBound C0 n.k := by
  induction n using mtkNodes.induct with
  | _ x ih =>
    rw [mtkNodes, List.length_cons, List.length_flatMap]
    have hmtklen : (mtk C0 I x.x x.k).attach.length ≤ (cl C0).length := by
      rw [List.length_attach, mtk]
      exact Nat.le_trans (List.length_filter_le _ _) (List.length_filter_le _ _)
    by_cases hx0 : x.k = 0
    · refine Nat.le_trans (Nat.add_le_add_right (sum_map_le _ _ 0 ?_) 1) ?_
      · rintro ⟨F, hF⟩ _
        cases F with
        | ex r c => exact absurd (mem_mtk.mp hF).2 (by rw [hx0]; exact Nat.not_succ_le_zero _)
        | _ => exact Nat.le_refl 0
      · rw [Nat.mul_zero, Nat.zero_add, hx0]; exact Nat.le_refl 1
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hx0
      refine Nat.le_trans (Nat.add_le_add_right
        (Nat.le_trans (sum_map_le _ _ (mtkBound C0 m) ?_)
          (Nat.mul_le_mul_right _ hmtklen)) 1) ?_
      · rintro ⟨F, hF⟩ _
        cases F with
        | ex r c =>
          have hih := ih r c hF
          rwa [show (mtkWitness x hF).k = m from by
            show x.k - 1 = m; omega] at hih
        | _ => exact Nat.zero_le _
      · rw [hm]
        show (cl C0).length * mtkBound C0 m + 1 ≤ 1 + (cl C0).length * mtkBound C0 m
        omega

end MtkRecursion

/-! ### The horizontal ∀PO-free fragment (`ASSEMBLY_DESIGN.md §15`)

The full ∀PO-free fragment MINUS vertical existentials (`∃PP`/`∃PPI`),
certified both directions via the `mtk` label and the tree-structural
frame — nested `∀DR`, `∀PP`/`∀PPI` (vacuous), `∀EQ`/`∃EQ` (reflexive),
`∃PO`, `∃DR`.  Strictly generalises `AllFree` and `DRFrag`. -/

section HorizFragAssembly

variable {α : Type} {I : Interp α} {C0 : Concept}

/-- THE HORIZONTAL ∀PO-FREE FRAGMENT: every existential is `DR`/`PO`/`EQ`
    (no vertical `∃PP`/`∃PPI` — those need kernels), every universal is
    non-`PO` (∀PO-free).  NO guard-freeness — nested `∀DR` is handled by
    the model-closed `mtk` label. -/
structure HFrag (C0 : Concept) : Prop where
  hex : ∀ r c, Concept.ex r c ∈ cl C0 → r = dr ∨ r = po ∨ r = eq
  hall : ∀ r c, Concept.all r c ∈ cl C0 → r ≠ po

/-- Symmetric `DR`-adjacency of coverage nodes (via `mtkWitness`). -/
def sAdjK (n n' : MTKNode I C0) : Prop :=
  (∃ (c : Concept) (hF : Concept.ex dr c ∈ mtk C0 I n.x n.k),
    mtkWitness n hF = n') ∨
  (∃ (c : Concept) (hF : Concept.ex dr c ∈ mtk C0 I n'.x n'.k),
    mtkWitness n' hF = n)

theorem sAdjK_symm (n n' : MTKNode I C0) : sAdjK n n' ↔ sAdjK n' n :=
  ⟨Or.symm, Or.symm⟩

theorem mtkWitness_x_ne (hI : RCC5Interp I) (n : MTKNode I C0) {r : Atom}
    {c : Concept} (hF : Concept.ex r c ∈ mtk C0 I n.x n.k) (hrne : r ≠ eq) :
    n.x ≠ (mtkWitness n hF).x := by
  intro hx
  have hrho := mtkWitness_rho n hF
  rw [← hx, hI.refl_eq n.x n.hx] at hrho
  exact hrne hrho.symm

theorem sAdjK_rho_dr (hI : RCC5Interp I) {n n' : MTKNode I C0}
    (h : sAdjK n n') : I.rho n.x n'.x = dr := by
  rcases h with ⟨_, hF, hchild⟩ | ⟨_, hF, hchild⟩
  · have hrho := mtkWitness_rho n hF
    rw [hchild] at hrho; exact hrho
  · have hrho := mtkWitness_rho n' hF
    rw [hchild] at hrho
    have hc := hI.conv_ n'.x n.x n'.hx n.hx
    rw [hrho] at hc
    rw [hc]; decide

theorem po_not_sAdjK (hI : RCC5Interp I) {n n' : MTKNode I C0}
    (h : I.rho n.x n'.x = po) : ¬ sAdjK n n' := by
  intro hadj
  rw [sAdjK_rho_dr hI hadj] at h
  exact absurd h (by decide)

open Classical in
noncomputable def dadjBK (_hI : RCC5Interp I) (root : MTKNode I C0)
    (m m' : {n // n ∈ mtkNodes root}) : Bool :=
  decide (sAdjK m.val m'.val)

theorem dadjBK_symm (hI : RCC5Interp I) (root : MTKNode I C0)
    (m m' : {n // n ∈ mtkNodes root}) :
    dadjBK hI root m m' = dadjBK hI root m' m := by
  unfold dadjBK
  rw [propext (sAdjK_symm m.val m'.val)]

open Classical in
/-- THE HORIZONTAL-FRAGMENT CERTIFICATE: coverage nodes, tree-structural
    frame, depth-bounded model-type labels, no kernels. -/
noncomputable def mtHF (hI : RCC5Interp I) (root : MTKNode I C0) :
    MultiTier {n // n ∈ mtkNodes root} Empty where
  E m m' := if m = m' then eq else if dadjBK hI root m m' then dr else po
  K k _ := k.elim
  Q k _ := k.elim
  up k := k.elim
  tauE m := mtk C0 I m.val.x m.val.k
  p k := k.elim
  phase k _ := k.elim

theorem mtHF_frame (hI : RCC5Interp I) (root : MTKNode I C0) :
    Frame (qnet (mtHF hI root).E (mtHF hI root).K (mtHF hI root).Q) := by
  apply qnet_empty_frame
  refine frame_ext ?_ (symDrPo_frame (dadjBK hI root) (dadjBK_symm hI root))
  intro v w
  simp only [mtHF]
  by_cases h : v = w
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

open Classical in
/-- THE HORIZONTAL-FRAGMENT CERTIFICATE IS VALID.  `ee_all`: `EQ` diagonal
    reflexive (`mtk_all_eq`), `DR` via forward/reverse model firing
    (`mtk_all_fwd`/`mtk_all_dr_rev`), `PO` excluded (∀PO-free), `PP`/`PPI`
    never occur on the frame; `e_ex`: `DR`/`PO` children + `EQ` reflexive
    (same node); kernels vacuous. -/
theorem mtHF_ok (hI : RCC5Interp I) (hfrag : HFrag C0)
    (root : MTKNode I C0) : MultiTierOk (mtHF hI root) where
  hp := fun k => k.elim
  frame_q := mtHF_frame hI root
  e_clash := fun e _ h => mtk_clash h
  e_nobot := fun _ => mtk_nobot
  e_and := fun _ _ _ h => mtk_and h
  e_or := fun _ _ _ h => mtk_or h
  k_clash := fun k => k.elim
  k_nobot := fun k => k.elim
  k_and := fun k => k.elim
  k_or := fun k => k.elim
  ee_all := by
    intro e f r c hall hEf
    have hEf' : (if e = f then eq
        else if dadjBK hI root e f then dr else po) = r := hEf
    by_cases hef : e = f
    · subst hef
      rw [if_pos rfl] at hEf'
      subst hEf'
      exact mtk_all_eq hI hall e.val.hx
    · rw [if_neg hef] at hEf'
      by_cases hd : dadjBK hI root e f = true
      · -- `DR` edge
        have hrdr : dr = r := (if_pos hd).symm.trans hEf'
        subst hrdr
        have hall' : Concept.all dr c ∈ mtk C0 I e.val.x e.val.k := hall
        rcases of_decide_eq_true hd with ⟨_, hF, hchild⟩ | ⟨_, hF, hchild⟩
        · -- forward: `f.val = mtkWitness e.val hF`
          show c ∈ mtk C0 I f.val.x f.val.k
          rw [← hchild]
          exact mtk_all_fwd hall' (mtkWitness e.val hF).hx
            (mtkWitness_rho e.val hF)
        · -- reverse: `e.val = mtkWitness f.val hF`
          show c ∈ mtk C0 I f.val.x f.val.k
          rw [← hchild] at hall'
          exact mtk_all_dr_rev hI hall' f.val.hx (mtkWitness f.val hF).hx
            (mtkWitness_rho f.val hF)
      · -- `PO` edge: `∀PO`-free, vacuous
        have hrpo : po = r := (if_neg hd).symm.trans hEf'
        exact absurd hrpo.symm (hfrag.hall r c (mtk_sub_cl _ hall))
  ek_all := fun _ _ _ _ k => k.elim
  ke_all := fun k => k.elim
  kk_pp := fun k => k.elim
  kk_ppi := fun k => k.elim
  kk_eq := fun k => k.elim
  kq_all := fun k => k.elim
  e_ex := by
    intro e r c hdem
    rcases hfrag.hex r c (mtk_sub_cl _ hdem) with hr | hr | hr
    · -- `∃DR`: `DR`-adjacent child
      subst hr
      have hmem : mtkWitness e.val hdem ∈ mtkNodes root :=
        mtkNodes_trans root e.val e.property _ (mtkWitness_mem e.val hdem)
      have hne : e ≠ ⟨mtkWitness e.val hdem, hmem⟩ := fun heq =>
        mtkWitness_x_ne hI e.val hdem (by decide)
          (congrArg (fun t => t.val.x) heq)
      refine Or.inl ⟨⟨mtkWitness e.val hdem, hmem⟩, ?_,
        mtkWitness_arg e.val hdem⟩
      have hd : dadjBK hI root e ⟨mtkWitness e.val hdem, hmem⟩ = true := by
        show decide (sAdjK e.val (mtkWitness e.val hdem)) = true
        rw [decide_eq_true_eq]; exact Or.inl ⟨c, hdem, rfl⟩
      show (if e = ⟨mtkWitness e.val hdem, hmem⟩ then eq
        else if dadjBK hI root e ⟨mtkWitness e.val hdem, hmem⟩ then dr
          else po) = dr
      rw [if_neg hne]; exact if_pos hd
    · -- `∃PO`: `PO`-child (not `DR`-adjacent)
      subst hr
      have hmem : mtkWitness e.val hdem ∈ mtkNodes root :=
        mtkNodes_trans root e.val e.property _ (mtkWitness_mem e.val hdem)
      have hne : e ≠ ⟨mtkWitness e.val hdem, hmem⟩ := fun heq =>
        mtkWitness_x_ne hI e.val hdem (by decide)
          (congrArg (fun t => t.val.x) heq)
      refine Or.inl ⟨⟨mtkWitness e.val hdem, hmem⟩, ?_,
        mtkWitness_arg e.val hdem⟩
      have hd : ¬ dadjBK hI root e ⟨mtkWitness e.val hdem, hmem⟩ = true := by
        show ¬ decide (sAdjK e.val (mtkWitness e.val hdem)) = true
        rw [decide_eq_true_eq]
        exact po_not_sAdjK hI (mtkWitness_rho e.val hdem)
      show (if e = ⟨mtkWitness e.val hdem, hmem⟩ then eq
        else if dadjBK hI root e ⟨mtkWitness e.val hdem, hmem⟩ then dr
          else po) = po
      rw [if_neg hne]; exact if_neg hd
    · -- `∃EQ`: reflexive, the SAME node (`E e e = eq`)
      subst hr
      refine Or.inl ⟨e, ?_, mtk_ex_eq hI hdem e.val.hx⟩
      show (if e = e then eq
        else if dadjBK hI root e e then dr else po) = eq
      rw [if_pos rfl]
  k_ex := fun k => k.elim

open Classical in
/-- **`ee_all` for the `mtHF` skeleton, generalized to `POFree`** (step 4 — the
    reusable horizontal handling of the `mtk`-with-kernels extraction).  Same
    proof as `mtHF_ok`'s `ee_all` (`EQ` diagonal reflexive, `DR` forward/reverse
    firing, `PP`/`PPI` never on the tree-structural frame), but the `PO`-edge
    vacuity uses `pofree_cl_all` (no `∀PO` in the `POFree` closure) instead of
    `HFrag`.  This is exactly `mtkKernel_ok`'s `hee` hypothesis when the cert's
    externals are the `mtHF` nodes (`g = ·.val.x`, `bud = ·.val.k`,
    `dadj = dadjBK`). -/
theorem mtk_ee_all (hI : RCC5Interp I) {C0 : Concept} (hpofree : POFree C0)
    (root : MTKNode I C0) (e f : {n // n ∈ mtkNodesH root}) (r : Atom)
    (c : Concept) (hall : Concept.all r c ∈ mtk C0 I e.val.x e.val.k)
    (hEf : (if e = f then eq else if decide (sAdjK e.val f.val) then dr else po) = r) :
    c ∈ mtk C0 I f.val.x f.val.k := by
  by_cases hef : e = f
  · subst hef
    rw [if_pos rfl] at hEf
    subst hEf
    exact mtk_all_eq hI hall e.val.hx
  · rw [if_neg hef] at hEf
    by_cases hd : decide (sAdjK e.val f.val) = true
    · -- `DR` edge
      have hrdr : dr = r := (if_pos hd).symm.trans hEf
      subst hrdr
      have hall' : Concept.all dr c ∈ mtk C0 I e.val.x e.val.k := hall
      rcases of_decide_eq_true hd with ⟨_, hF, hchild⟩ | ⟨_, hF, hchild⟩
      · show c ∈ mtk C0 I f.val.x f.val.k
        rw [← hchild]
        exact mtk_all_fwd hall' (mtkWitness e.val hF).hx (mtkWitness_rho e.val hF)
      · show c ∈ mtk C0 I f.val.x f.val.k
        rw [← hchild] at hall'
        exact mtk_all_dr_rev hI hall' f.val.hx (mtkWitness f.val hF).hx
          (mtkWitness_rho f.val hF)
    · -- `PO` edge: `∀PO`-free, vacuous
      have hrpo : po = r := (if_neg hd).symm.trans hEf
      exact absurd hrpo.symm (pofree_cl_all C0 hpofree r c (mtk_sub_cl _ hall))

open Classical in
/-- **`e_ex` for the `mtk`-with-kernels cert** (step 4).  A node `e`'s demand
    `∃r.D` is routed: `∃DR`/`∃PO`/`∃EQ` to a horizontal child (the `mtHF`
    routing, now over `mtkNodesH`); `∃PP` — which the fragment restricts to the
    attaching node `v0`, with the tower carrying its argument (`hpp_v0`) — to
    the KERNEL (`conv(K v0) = PP`); `∃PPI` excluded (`hno_ppi`).  Discharges
    `mtkKernel_ok`'s `he_ex` hypothesis for the `mtHF`-node instantiation. -/
theorem mtk_e_ex (hI : RCC5Interp I) {C0 : Concept} (root : MTKNode I C0)
    (c : Nat → α) (p i : Nat) (v0 : {n // n ∈ mtkNodesH root})
    (hpp_v0 : ∀ (e : {n // n ∈ mtkNodesH root}) (D : Concept),
      Concept.ex pp D ∈ mtk C0 I e.val.x e.val.k →
      e = v0 ∧ ∃ a, a < p ∧ D ∈ mtk C0 I (c (i + a)) v0.val.k)
    (hno_ppi : ∀ (e : {n // n ∈ mtkNodesH root}) (D : Concept),
      Concept.ex ppi D ∈ mtk C0 I e.val.x e.val.k → False)
    (e : {n // n ∈ mtkNodesH root}) (r : Atom) (D : Concept)
    (hdem : Concept.ex r D ∈ mtk C0 I e.val.x e.val.k) :
    (∃ f : {n // n ∈ mtkNodesH root},
      (if e = f then eq else if decide (sAdjK e.val f.val) then dr else po) = r ∧
      D ∈ mtk C0 I f.val.x f.val.k) ∨
    (conv (if e = v0 then ppi else po) = r ∧
      ∃ a, a < p ∧ D ∈ mtk C0 I (c (i + a)) v0.val.k) := by
  by_cases heq : r = eq
  · subst heq
    refine Or.inl ⟨e, ?_, mtk_ex_eq hI hdem e.val.hx⟩
    show (if e = e then eq else if decide (sAdjK e.val e.val) then dr else po) = eq
    rw [if_pos rfl]
  by_cases hdr : r = dr
  · subst hdr
    have hmem : mtkWitness e.val hdem ∈ mtkNodesH root :=
      mtkNodesH_trans root e.val e.property _ (mtkWitnessH_mem e.val hdem (by decide))
    have hne : e ≠ ⟨mtkWitness e.val hdem, hmem⟩ := fun heq =>
      mtkWitness_x_ne hI e.val hdem (by decide) (congrArg (fun t => t.val.x) heq)
    refine Or.inl ⟨⟨mtkWitness e.val hdem, hmem⟩, ?_, mtkWitness_arg e.val hdem⟩
    have hd : decide (sAdjK e.val (mtkWitness e.val hdem)) = true := by
      rw [decide_eq_true_eq]; exact Or.inl ⟨D, hdem, rfl⟩
    show (if e = ⟨mtkWitness e.val hdem, hmem⟩ then eq
      else if decide (sAdjK e.val (mtkWitness e.val hdem)) then dr else po) = dr
    rw [if_neg hne]; exact if_pos hd
  by_cases hpo : r = po
  · subst hpo
    have hmem : mtkWitness e.val hdem ∈ mtkNodesH root :=
      mtkNodesH_trans root e.val e.property _ (mtkWitnessH_mem e.val hdem (by decide))
    have hne : e ≠ ⟨mtkWitness e.val hdem, hmem⟩ := fun heq =>
      mtkWitness_x_ne hI e.val hdem (by decide) (congrArg (fun t => t.val.x) heq)
    refine Or.inl ⟨⟨mtkWitness e.val hdem, hmem⟩, ?_, mtkWitness_arg e.val hdem⟩
    have hd : ¬ decide (sAdjK e.val (mtkWitness e.val hdem)) = true := by
      rw [decide_eq_true_eq]
      exact po_not_sAdjK hI (mtkWitness_rho e.val hdem)
    show (if e = ⟨mtkWitness e.val hdem, hmem⟩ then eq
      else if decide (sAdjK e.val (mtkWitness e.val hdem)) then dr else po) = po
    rw [if_neg hne]; exact if_neg hd
  by_cases hpp : r = pp
  · subst hpp
    obtain ⟨hev0, a, ha, hDa⟩ := hpp_v0 e D hdem
    refine Or.inr ⟨?_, a, ha, hDa⟩
    rw [hev0, if_pos rfl]; rfl
  · have hppi : r = ppi := by cases r <;> simp_all
    subst hppi
    exact (hno_ppi e D hdem).elim

open Classical in
/-- **`k_ex` for the `mtk`-with-kernels cert** (step 4).  A tower phase's demand
    routes `∃PP` up the tower (`cdir true = PP`), `∃EQ` reflexively, AND a
    phase's HORIZONTAL `∃PO.D` demand OUT to a non-root external `f` carrying
    `D` via the `PO` `K`-edge (`K k f = po` for `f ≠ v0`) — route 1 of the
    `k_ex` clause.  This is what removes the "clean phases" restriction:
    `∀PO`-freeness makes the `PO` `K`-edge sound (no `∀PO` obligation to
    violate), so a phase need NOT be horizontally trivial.  `hk_class` supplies,
    per phase demand, one of: `∃PO` served by an external / `∃PP` up the tower /
    `∃EQ`.  Discharges `mtkKernel_ok`'s `hk_ex`. -/
theorem mtk_k_ex (hI : RCC5Interp I) {C0 : Concept} (root : MTKNode I C0)
    (c : Nat → α) (p i : Nat) (v0 : {n // n ∈ mtkNodesH root})
    (hdom : ∀ n, I.dom (c n))
    (hk_class : ∀ a r D, Concept.ex r D ∈ mtk C0 I (c (i + a)) v0.val.k →
      (∃ f : {n // n ∈ mtkNodesH root}, f ≠ v0 ∧ r = po ∧
        D ∈ mtk C0 I f.val.x f.val.k) ∨
      (r = pp ∧ ∃ b, b < p ∧ D ∈ mtk C0 I (c (i + b)) v0.val.k) ∨ r = eq)
    (a : Nat) (r : Atom) (D : Concept)
    (hmem : Concept.ex r D ∈ mtk C0 I (c (i + a)) v0.val.k) :
    (∃ f : {n // n ∈ mtkNodesH root},
      (if f = v0 then ppi else po) = r ∧ D ∈ mtk C0 I f.val.x f.val.k) ∨
    (r = pp ∧ ∃ b, b < p ∧ D ∈ mtk C0 I (c (i + b)) v0.val.k) ∨
    (r = eq ∧ D ∈ mtk C0 I (c (i + a)) v0.val.k) := by
  rcases hk_class a r D hmem with ⟨f, hfv0, rfl, hDf⟩ | ⟨rfl, b, hb, hDb⟩ | rfl
  · exact Or.inl ⟨f, by rw [if_neg hfv0], hDf⟩
  · exact Or.inr (Or.inl ⟨rfl, b, hb, hDb⟩)
  · exact Or.inr (Or.inr ⟨rfl, mtk_ex_eq hI hmem (hdom (i + a))⟩)

/-- THE HORIZONTAL-FRAGMENT EXTRACTION: every satisfiable `HFrag` concept
    has a valid finite multi-tier certificate carrying it. -/
theorem extract_hfrag (C0 : Concept) (hfrag : HFrag C0)
    (hsat : Satisfiable C0) :
    ∃ (β : Type) (T : MultiTier β Empty) (g : β),
      MultiTierOk T ∧ C0 ∈ T.tauE g := by
  obtain ⟨α, I, hI, x0, hdom0, hsat0⟩ := hsat
  let root : MTKNode I C0 := ⟨x0, mdepth C0, hdom0⟩
  refine ⟨{n // n ∈ mtkNodes root}, mtHF hI root,
    ⟨root, self_mem_mtkNodes root⟩, mtHF_ok hI hfrag root, ?_⟩
  show C0 ∈ mtk C0 I x0 (mdepth C0)
  exact mem_mtk.mpr ⟨mem_mty.mpr ⟨cl_self C0, hsat0⟩, Nat.le_refl _⟩

/-! ### Round E3s (2026-07-31): FinMT-encoding the horizontal certificate

Toward `Decidable (Satisfiable C0)` (roadmap §22): encode the kernel-free
`mtHF` certificate as a first-order `FinMT` and transport its
`MultiTierOk` across the position↔node map, so the Boolean checker
`mtOkB` accepts it.  Externals = the DISTINCT nodes of `mtkNodes root`
indexed by list position; labels = `mtk`; relations = `eq/dr/po`; no
kernels. -/

section CDedup
open Classical

/-- Classical dedup — core lacks `List.dedup` for `DecidableEq` (only
    `eraseDups` for `BEq`, and `MTKNode` has no `BEq`).  Keeps the last
    occurrence of each element; the result is `Nodup` with the same
    membership. -/
noncomputable def cdedup {A : Type} : List A → List A
  | [] => []
  | a :: l => if a ∈ cdedup l then cdedup l else a :: cdedup l

theorem mem_cdedup {A : Type} (a : A) (l : List A) : a ∈ cdedup l ↔ a ∈ l := by
  induction l with
  | nil => exact Iff.rfl
  | cons b t ih =>
    show a ∈ (if b ∈ cdedup t then cdedup t else b :: cdedup t) ↔ a ∈ b :: t
    by_cases hb : b ∈ cdedup t
    · rw [if_pos hb, List.mem_cons, ih]
      constructor
      · exact fun h => Or.inr h
      · rintro (rfl | h)
        · exact ih.mp hb
        · exact h
    · rw [if_neg hb, List.mem_cons, List.mem_cons, ih]

theorem nodup_cdedup {A : Type} (l : List A) : (cdedup l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons b t ih =>
    show (if b ∈ cdedup t then cdedup t else b :: cdedup t).Nodup
    by_cases hb : b ∈ cdedup t
    · rw [if_pos hb]; exact ih
    · rw [if_neg hb]; exact List.nodup_cons.mpr ⟨hb, ih⟩

end CDedup

/-- In-range `getD` commutes with `map` (default-independent). -/
theorem getD_map_lt {A B : Type} (f : A → B) (l : List A) :
    ∀ (i : Nat) (d1 : B) (d2 : A), i < l.length →
    (l.map f).getD i d1 = f (l.getD i d2) := by
  induction l with
  | nil => intro i _ _ h; exact absurd h (Nat.not_lt_zero i)
  | cons a t ih =>
    intro i d1 d2 h
    match i with
    | 0 => rfl
    | j + 1 => exact ih j d1 d2 (Nat.lt_of_succ_lt_succ h)

open Classical in
/-- FinMT encoding of the horizontal (kernel-free) certificate.  Externals
    are the DISTINCT subtype elements `cdedup (mtkNodes root).attach`
    (indexed by list position — `Nodup`, so `eq` stays on the diagonal);
    labels `= mtk`, relations `= mtHF`'s `eq/dr/po` table. -/
noncomputable def encodeHF (hI : RCC5Interp I) (root : MTKNode I C0) : FinMT where
  tauE := (cdedup (mtkNodes root).attach).map (fun m => mtk C0 I m.val.x m.val.k)
  E := (cdedup (mtkNodes root).attach).map (fun m =>
        (cdedup (mtkNodes root).attach).map (fun m' =>
          if m = m' then eq else if dadjBK hI root m m' then dr else po))
  K := []
  Q := []
  up := []
  phases := []

/-- The distinct-external list. -/
noncomputable def hfExt (root : MTKNode I C0) : List {n // n ∈ mtkNodes root} :=
  cdedup (mtkNodes root).attach

/-- The default external (the root node itself). -/
noncomputable def hfRootN (root : MTKNode I C0) : {n // n ∈ mtkNodes root} :=
  ⟨root, self_mem_mtkNodes root⟩

/-- The external at position `i` (a subtype node). -/
noncomputable def hfNode (root : MTKNode I C0) (i : Nat) : {n // n ∈ mtkNodes root} :=
  (hfExt root).getD i (hfRootN root)

theorem encodeHF_nE (hI : RCC5Interp I) (root : MTKNode I C0) :
    (encodeHF hI root).nE = (hfExt root).length := by
  simp [FinMT.nE, encodeHF, hfExt, List.length_map]

theorem encodeHF_nK (hI : RCC5Interp I) (root : MTKNode I C0) :
    (encodeHF hI root).nK = 0 := rfl

/-- Data-preservation for labels: `decodeMT`'s external label at position
    `i` is `mtHF`'s label at node `hfNode i`. -/
theorem encodeHF_tE (hI : RCC5Interp I) (root : MTKNode I C0) (i : Nat)
    (h : i < (hfExt root).length) :
    (encodeHF hI root).tE i = (mtHF hI root).tauE (hfNode root i) := by
  show ((hfExt root).map (fun m => mtk C0 I m.val.x m.val.k)).getD i [] = _
  rw [getD_map_lt (fun m => mtk C0 I m.val.x m.val.k) _ i [] (hfRootN root) h]
  rfl

open Classical in
/-- Data-preservation for relations: `decodeMT`'s external table at `(i,j)`
    is `mtHF`'s relation between nodes `hfNode i`, `hfNode j`. -/
theorem encodeHF_Ea (hI : RCC5Interp I) (root : MTKNode I C0) (i j : Nat)
    (hi : i < (hfExt root).length) (hj : j < (hfExt root).length) :
    (encodeHF hI root).Ea i j = (mtHF hI root).E (hfNode root i) (hfNode root j) := by
  show (((hfExt root).map (fun m => (hfExt root).map (fun m' =>
      if m = m' then eq else if dadjBK hI root m m' then dr else po))).getD i []).getD j dr = _
  rw [getD_map_lt _ _ i [] (hfRootN root) hi,
    getD_map_lt _ _ j dr (hfRootN root) hj]
  rfl

/-- In-range, `hfNode` is `getElem`. -/
theorem hfNode_getElem (root : MTKNode I C0) (j : Nat)
    (hj : j < (hfExt root).length) : hfNode root j = (hfExt root)[j] := by
  show (hfExt root).getD j (hfRootN root) = (hfExt root)[j]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

/-- **THE HORIZONTAL CERTIFICATE'S FinMT ENCODING IS VALID.**  Transport
    `mtHF_ok` across the position↔node map: labels/relations agree
    (`encodeHF_tE`/`encodeHF_Ea`), the frame comes from `mtHF.E`'s
    (`symDrPo`) frame + `hfNode` injectivity (`Nodup`), and `e_ex` pulls
    each witness node back to its list index (surjectivity). -/
theorem encodeHF_mtOk (hI : RCC5Interp I) (hfrag : HFrag C0)
    (root : MTKNode I C0) : MultiTierOk (decodeMT (encodeHF hI root)) := by
  have hlen : (encodeHF hI root).nE = (hfExt root).length := encodeHF_nE hI root
  have hlt : ∀ e : Fin (encodeHF hI root).nE, e.val < (hfExt root).length :=
    fun e => hlen ▸ e.isLt
  have hDtau : ∀ e : Fin (encodeHF hI root).nE,
      (decodeMT (encodeHF hI root)).tauE e = (mtHF hI root).tauE (hfNode root e.val) :=
    fun e => encodeHF_tE hI root e.val (hlt e)
  have hDE : ∀ e f : Fin (encodeHF hI root).nE,
      (decodeMT (encodeHF hI root)).E e f
        = (mtHF hI root).E (hfNode root e.val) (hfNode root f.val) :=
    fun e f => encodeHF_Ea hI root e.val f.val (hlt e) (hlt f)
  have hME : Frame (mtHF hI root).E := by
    refine frame_ext ?_ (symDrPo_frame (dadjBK hI root) (dadjBK_symm hI root))
    intro v w
    simp only [mtHF]
    by_cases h : v = w
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  have hMok := mtHF_ok hI hfrag root
  have hDEframe : Frame (decodeMT (encodeHF hI root)).E :=
    { refl_eq := fun e => by rw [hDE e e]; exact hME.refl_eq _
      eq_id := fun e f h => by
        rw [hDE e f] at h
        exact Fin.ext ((List.getD_inj (hlt e) (hlt f) (nodup_cdedup _)).mp (hME.eq_id _ _ h))
      conv_ := fun e f => by rw [hDE f e, hDE e f]; exact hME.conv_ _ _
      comp_ := fun e f g => by rw [hDE e g, hDE e f, hDE f g]; exact hME.comp_ _ _ _ }
  refine
    { hp := fun k => k.elim0
      frame_q := qnet_empty_frame' _ _ _ (fun k => k.elim0) hDEframe
      e_clash := fun e a h => by rw [hDtau e] at h ⊢; exact hMok.e_clash _ a h
      e_nobot := fun e => by rw [hDtau e]; exact hMok.e_nobot _
      e_and := fun e c d h => by rw [hDtau e] at h ⊢; exact hMok.e_and _ c d h
      e_or := fun e c d h => by rw [hDtau e] at h ⊢; exact hMok.e_or _ c d h
      k_clash := fun k => k.elim0
      k_nobot := fun k => k.elim0
      k_and := fun k => k.elim0
      k_or := fun k => k.elim0
      ee_all := fun e f r c hall hEf => by
        rw [hDtau f]; rw [hDtau e] at hall; rw [hDE e f] at hEf
        exact hMok.ee_all _ _ r c hall hEf
      ek_all := fun e r c _ k => k.elim0
      ke_all := fun k => k.elim0
      kk_pp := fun k => k.elim0
      kk_ppi := fun k => k.elim0
      kk_eq := fun k => k.elim0
      kq_all := fun k => k.elim0
      e_ex := fun e r c hmem => by
        rw [hDtau e] at hmem
        rcases hMok.e_ex _ r c hmem with ⟨f', hEf', harg'⟩ | ⟨k, _⟩
        · have hf'mem : f' ∈ hfExt root :=
            (mem_cdedup f' ((mtkNodes root).attach)).mpr (List.mem_attach (mtkNodes root) f')
          obtain ⟨j, hj, hjf⟩ := List.getElem_of_mem hf'mem
          have hjnode : hfNode root j = f' := (hfNode_getElem root j hj).trans hjf
          have hjE : j < (encodeHF hI root).nE := hlen ▸ hj
          refine Or.inl ⟨⟨j, hjE⟩, ?_, ?_⟩
          · rw [hDE e ⟨j, hjE⟩]
            show (mtHF hI root).E (hfNode root e.val) (hfNode root j) = r
            rw [hjnode]; exact hEf'
          · rw [hDtau ⟨j, hjE⟩]
            show c ∈ (mtHF hI root).tauE (hfNode root j)
            rw [hjnode]; exact harg'
        · exact k.elim
      k_ex := fun k => k.elim0 }

/-- The encoded certificate is ACCEPTED at a BOUNDED root index (the
    root node's external position `< nE`). -/
theorem encodeHF_accepts (hI : RCC5Interp I) (hfrag : HFrag C0)
    (root : MTKNode I C0) (hC0 : C0 ∈ mtk C0 I root.x root.k) :
    ∃ rootIdx, rootIdx < (encodeHF hI root).nE ∧
      (encodeHF hI root).mtAcceptB rootIdx C0 = true := by
  have hok := encodeHF_mtOk hI hfrag root
  have hrootmem : hfRootN root ∈ hfExt root :=
    (mem_cdedup _ _).mpr (List.mem_attach _ _)
  obtain ⟨e0, he0, he0f⟩ := List.getElem_of_mem hrootmem
  have he0node : hfNode root e0 = hfRootN root := (hfNode_getElem root e0 he0).trans he0f
  have he0E : e0 < (encodeHF hI root).nE := (encodeHF_nE hI root) ▸ he0
  refine ⟨e0, he0E, ?_⟩
  rw [FinMT.mtAcceptB]
  refine andB_intro (mtOkB_complete _ hok) ?_
  rw [FinMT.rootB, if_pos he0E]
  apply decide_eq_true
  show C0 ∈ (encodeHF hI root).tE e0
  rw [encodeHF_tE hI root e0 he0, he0node]
  exact hC0

/-! ### Enumeration combinators (core lacks `List.pi`/`sublists`) -/

/-- All lists of length exactly `n` over `L`. -/
def allListsLen {A : Type} (L : List A) : Nat → List (List A)
  | 0 => [[]]
  | n + 1 => L.flatMap (fun a => (allListsLen L n).map (fun l => a :: l))

theorem mem_allListsLen {A : Type} (L : List A) (n : Nat) (l : List A) :
    l ∈ allListsLen L n ↔ l.length = n ∧ ∀ x ∈ l, x ∈ L := by
  induction n generalizing l with
  | zero =>
    constructor
    · intro h
      simp only [allListsLen, List.mem_singleton] at h
      subst h; exact ⟨rfl, fun x hx => absurd hx List.not_mem_nil⟩
    · rintro ⟨hlen, _⟩
      have hl : l = [] := List.length_eq_zero_iff.mp hlen
      subst hl; exact List.mem_singleton.mpr rfl
  | succ n ih =>
    constructor
    · intro h
      simp only [allListsLen, List.mem_flatMap, List.mem_map] at h
      obtain ⟨a, ha, l', hl', rfl⟩ := h
      obtain ⟨hlen, hmem⟩ := (ih l').mp hl'
      refine ⟨by rw [List.length_cons, hlen], fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ha
      · exact hmem x hx'
    · rintro ⟨hlen, hmem⟩
      cases l with
      | nil => simp at hlen
      | cons a l' =>
        simp only [allListsLen, List.mem_flatMap, List.mem_map]
        exact ⟨a, hmem a (List.mem_cons_self ..), l',
          (ih l').mpr ⟨by simpa using hlen, fun x hx => hmem x (List.mem_cons_of_mem a hx)⟩, rfl⟩

/-- All lists of length `≤ n` over `L`. -/
def allListsLe {A : Type} (L : List A) (n : Nat) : List (List A) :=
  (List.range (n + 1)).flatMap (allListsLen L)

theorem mem_allListsLe {A : Type} (L : List A) (n : Nat) (l : List A) :
    l ∈ allListsLe L n ↔ l.length ≤ n ∧ ∀ x ∈ l, x ∈ L := by
  simp only [allListsLe, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨m, hm, hl⟩
    obtain ⟨hlen, hmem⟩ := (mem_allListsLen L m l).mp hl
    exact ⟨by omega, hmem⟩
  · rintro ⟨hlen, hmem⟩
    exact ⟨l.length, by omega, (mem_allListsLen L l.length l).mpr ⟨rfl, hmem⟩⟩

/-- All five RCC5 atoms. -/
def allAtoms : List Atom := [Atom.eq, Atom.pp, Atom.ppi, Atom.po, Atom.dr]

theorem mem_allAtoms (a : Atom) : a ∈ allAtoms := by cases a <;> decide

open Classical in
theorem length_cdedup_le {A : Type} (l : List A) : (cdedup l).length ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a t ih =>
    show (if a ∈ cdedup t then cdedup t else a :: cdedup t).length ≤ (a :: t).length
    rw [List.length_cons]
    by_cases h : a ∈ cdedup t
    · rw [if_pos h]; exact Nat.le_trans ih (Nat.le_succ _)
    · rw [if_neg h, List.length_cons]; exact Nat.succ_le_succ ih

/-- The fixed, model-independent code enumeration for `C0`: all kernel-free
    `FinMT`s with labels drawn from `cl C0` (length `≤ |cl C0|`), `≤ K(C0)`
    externals, `eq/dr/po/…` tables, paired with a root index `≤ K(C0)`. -/
def codes (C0 : Concept) : List (FinMT × Nat) :=
  (allListsLe (allListsLe (cl C0) (cl C0).length) (mtkBound C0 (mdepth C0))).flatMap
    (fun tauE => (allListsLe (allListsLe allAtoms (mtkBound C0 (mdepth C0)))
        (mtkBound C0 (mdepth C0))).flatMap
      (fun E => (List.range (mtkBound C0 (mdepth C0) + 1)).map
        (fun rootIdx => (⟨tauE, E, [], [], [], []⟩, rootIdx))))

/-- The encoded certificate's code lies in the enumeration. -/
theorem encodeHF_mem_codes (hI : RCC5Interp I) (root : MTKNode I C0)
    (hrk : root.k = mdepth C0) (rootIdx : Nat)
    (hri : rootIdx < (encodeHF hI root).nE) :
    (encodeHF hI root, rootIdx) ∈ codes C0 := by
  have hExtLe : (hfExt root).length ≤ mtkBound C0 (mdepth C0) := by
    calc (hfExt root).length
        ≤ (mtkNodes root).attach.length := length_cdedup_le _
      _ = (mtkNodes root).length := List.length_attach
      _ ≤ mtkBound C0 root.k := mtkNodes_length_le root
      _ = mtkBound C0 (mdepth C0) := by rw [hrk]
  have htauElen : (encodeHF hI root).tauE.length = (hfExt root).length := by
    show ((hfExt root).map _).length = _; rw [List.length_map]
  have hElen : (encodeHF hI root).E.length = (hfExt root).length := by
    show ((hfExt root).map _).length = _; rw [List.length_map]
  refine List.mem_flatMap.mpr ⟨(encodeHF hI root).tauE, ?_,
    List.mem_flatMap.mpr ⟨(encodeHF hI root).E, ?_,
      List.mem_map.mpr ⟨rootIdx, List.mem_range.mpr (by
        have := (encodeHF_nE hI root) ▸ hri; omega), rfl⟩⟩⟩
  · -- tauE ∈ allListsLe labels B
    rw [mem_allListsLe]
    refine ⟨?_, fun lab hlab => ?_⟩
    · rw [htauElen]; exact hExtLe
    · rw [mem_allListsLe]
      obtain ⟨m, _, rfl⟩ := List.mem_map.mp (show lab ∈ (hfExt root).map _ from hlab)
      refine ⟨?_, fun y hy => mtk_sub_cl _ hy⟩
      rw [mtk, mty]
      exact Nat.le_trans (List.length_filter_le _ _) (List.length_filter_le _ _)
  · -- E ∈ allListsLe (allListsLe allAtoms B) B
    rw [mem_allListsLe]
    refine ⟨?_, fun row hrow => ?_⟩
    · rw [hElen]; exact hExtLe
    · rw [mem_allListsLe]
      obtain ⟨m, _, rfl⟩ := List.mem_map.mp (show row ∈ (hfExt root).map _ from hrow)
      refine ⟨?_, fun y _ => mem_allAtoms y⟩
      show ((hfExt root).map _).length ≤ _
      rw [List.length_map]; exact hExtLe

/-- COMPLETENESS of the enumeration: every satisfiable `HFrag` concept has
    an accepted code in the fixed list `codes C0`. -/
theorem hfrag_hcompl (C0 : Concept) (hfrag : HFrag C0) :
    Satisfiable C0 → ∃ p ∈ codes C0, (p.1).mtAcceptB p.2 C0 = true := by
  intro hsat
  obtain ⟨α, I, hI, x0, hdom0, hsat0⟩ := hsat
  have hC0 : C0 ∈ mtk C0 I (⟨x0, mdepth C0, hdom0⟩ : MTKNode I C0).x
      (⟨x0, mdepth C0, hdom0⟩ : MTKNode I C0).k :=
    mem_mtk.mpr ⟨mem_mty.mpr ⟨cl_self C0, hsat0⟩, Nat.le_refl _⟩
  obtain ⟨rootIdx, hri, hacc⟩ :=
    encodeHF_accepts hI hfrag ⟨x0, mdepth C0, hdom0⟩ hC0
  exact ⟨(encodeHF hI ⟨x0, mdepth C0, hdom0⟩, rootIdx),
    encodeHF_mem_codes hI ⟨x0, mdepth C0, hdom0⟩ rfl rootIdx hri, hacc⟩

/-- **THE HORIZONTAL ∀PO-FREE FRAGMENT IS DECIDABLE.**  The project's first
    kernel-checked `Decidable (Satisfiable C0)`: soundness from
    `mtAcceptB_sound`, completeness from `hfrag_hcompl` (encode the
    depth-truncated certificate, size-bounded by `K(C0)`, into the fixed
    enumeration `codes C0`). -/
def decidableSat_hfrag (C0 : Concept) (hfrag : HFrag C0) :
    Decidable (Satisfiable C0) :=
  decidableSat_of_codes C0 (codes C0) (hfrag_hcompl C0 hfrag)

/-- **HORIZONTAL ∀PO-FREE SATISFIABILITY ⟺ A MULTI-TIER CERTIFICATE.**
    Both directions kernel-checked.  This is the full ∀PO-free fragment
    MINUS vertical existentials `∃PP`/`∃PPI`: nested `∀DR`, `∀PP`/`∀PPI`,
    `∀EQ`/`∃EQ`, `∃PO`, `∃DR` — via the model-type-truncated-by-depth
    label, no fixpoint, no kernels.  Strictly generalises both
    `satisfiable_iff_allfree_cert` and `satisfiable_iff_podr_cert`.  Still
    a CERTIFICATE CHARACTERIZATION (`β` an arbitrary `Type`). -/
theorem satisfiable_iff_hfrag_cert (C0 : Concept) (hfrag : HFrag C0) :
    Satisfiable C0 ↔
      ∃ (β : Type) (T : MultiTier β Empty) (g : β),
        MultiTierOk T ∧ C0 ∈ T.tauE g := by
  constructor
  · exact extract_hfrag C0 hfrag
  · rintro ⟨β, T, g, hok, hC0⟩
    exact multiTier_sound T hok (Sum.inl g) C0 hC0

end HorizFragAssembly

/-! ### Round E3v (2026-08-02): the GENERAL FinMT encoder (for kernels)

Toward VERTICAL decidability (roadmap §24): a `MultiTier` over `Fin nE ×
Fin nK` (any finite index — the shape a reindexed kernel certificate
takes) encodes to a `FinMT` by direct table tabulation.  Cleaner than
`encodeHF`: the index types are preserved, so `e_ex`/`k_ex` witnesses
transfer with NO pullback. -/

section EncodeMT
variable {nE nK : Nat}

/-- Tabulate a `Fin`-indexed `MultiTier` into a first-order `FinMT`. -/
def encodeMT (T : MultiTier (Fin nE) (Fin nK)) : FinMT where
  tauE := (List.finRange nE).map T.tauE
  E := (List.finRange nE).map (fun e => (List.finRange nE).map (T.E e))
  K := (List.finRange nK).map (fun k => (List.finRange nE).map (T.K k))
  Q := (List.finRange nK).map (fun k => (List.finRange nK).map (T.Q k))
  up := (List.finRange nK).map T.up
  phases := (List.finRange nK).map (fun k => (List.range (T.p k)).map (T.phase k))

theorem finRange_getD_self {n : Nat} (e : Fin n) (d : Fin n) :
    (List.finRange n).getD e.val d = e := by
  have h1 : e.val < (List.finRange n).length := by rw [List.length_finRange]; exact e.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem_finRange,
    Option.getD_some]
  exact Fin.ext rfl

theorem range_getD_self {n : Nat} (a : Nat) (ha : a < n) (d : Nat) :
    (List.range n).getD a d = a := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [List.length_range]; exact ha),
    List.getElem_range, Option.getD_some]

theorem encodeMT_nE (T : MultiTier (Fin nE) (Fin nK)) : (encodeMT T).nE = nE := by
  show ((List.finRange nE).map _).length = nE; rw [List.length_map, List.length_finRange]

theorem encodeMT_nK (T : MultiTier (Fin nE) (Fin nK)) : (encodeMT T).nK = nK := by
  show ((List.finRange nK).map _).length = nK; rw [List.length_map, List.length_finRange]

theorem encodeMT_tE (T : MultiTier (Fin nE) (Fin nK)) (e : Fin nE) :
    (encodeMT T).tE e.val = T.tauE e := by
  show ((List.finRange nE).map T.tauE).getD e.val [] = T.tauE e
  rw [getD_map_lt T.tauE (List.finRange nE) e.val [] e
    (by rw [List.length_finRange]; exact e.isLt), finRange_getD_self]

theorem encodeMT_Ea (T : MultiTier (Fin nE) (Fin nK)) (e f : Fin nE) :
    (encodeMT T).Ea e.val f.val = T.E e f := by
  show (((List.finRange nE).map (fun e => (List.finRange nE).map (T.E e))).getD
    e.val []).getD f.val dr = T.E e f
  rw [getD_map_lt _ (List.finRange nE) e.val [] e
    (by rw [List.length_finRange]; exact e.isLt), finRange_getD_self,
    getD_map_lt (T.E e) (List.finRange nE) f.val dr f
    (by rw [List.length_finRange]; exact f.isLt), finRange_getD_self]

theorem encodeMT_Ka (T : MultiTier (Fin nE) (Fin nK)) (k : Fin nK) (e : Fin nE) :
    (encodeMT T).Ka k.val e.val = T.K k e := by
  show (((List.finRange nK).map (fun k => (List.finRange nE).map (T.K k))).getD
    k.val []).getD e.val dr = T.K k e
  rw [getD_map_lt _ (List.finRange nK) k.val [] k
    (by rw [List.length_finRange]; exact k.isLt), finRange_getD_self,
    getD_map_lt (T.K k) (List.finRange nE) e.val dr e
    (by rw [List.length_finRange]; exact e.isLt), finRange_getD_self]

theorem encodeMT_Qa (T : MultiTier (Fin nE) (Fin nK)) (k k' : Fin nK) :
    (encodeMT T).Qa k.val k'.val = T.Q k k' := by
  show (((List.finRange nK).map (fun k => (List.finRange nK).map (T.Q k))).getD
    k.val []).getD k'.val dr = T.Q k k'
  rw [getD_map_lt _ (List.finRange nK) k.val [] k
    (by rw [List.length_finRange]; exact k.isLt), finRange_getD_self,
    getD_map_lt (T.Q k) (List.finRange nK) k'.val dr k'
    (by rw [List.length_finRange]; exact k'.isLt), finRange_getD_self]

theorem encodeMT_upa (T : MultiTier (Fin nE) (Fin nK)) (k : Fin nK) :
    (encodeMT T).upa k.val = T.up k := by
  show ((List.finRange nK).map T.up).getD k.val true = T.up k
  rw [getD_map_lt T.up (List.finRange nK) k.val true k
    (by rw [List.length_finRange]; exact k.isLt), finRange_getD_self]

theorem encodeMT_pk (T : MultiTier (Fin nE) (Fin nK)) (k : Fin nK) :
    (encodeMT T).pk k.val = T.p k := by
  show (((List.finRange nK).map (fun k => (List.range (T.p k)).map (T.phase k))).getD
    k.val []).length = T.p k
  rw [getD_map_lt _ (List.finRange nK) k.val [] k
    (by rw [List.length_finRange]; exact k.isLt), finRange_getD_self,
    List.length_map, List.length_range]

theorem encodeMT_phase (T : MultiTier (Fin nE) (Fin nK)) (k : Fin nK) (a : Nat)
    (ha : a < T.p k) : (encodeMT T).phase k.val a = T.phase k a := by
  show (((List.finRange nK).map (fun k => (List.range (T.p k)).map (T.phase k))).getD
    k.val []).getD a [] = T.phase k a
  rw [getD_map_lt _ (List.finRange nK) k.val [] k
    (by rw [List.length_finRange]; exact k.isLt), finRange_getD_self,
    getD_map_lt (T.phase k) (List.range (T.p k)) a [] a
    (by rw [List.length_range]; exact ha), range_getD_self a ha]

end EncodeMT

/-- A `Frame` transports backward along an injective reindex `φ` (data
    matching pointwise: `N' x y = N (φ x) (φ y)`). -/
theorem frame_reindex {V V' : Type} (φ : V' → V)
    (hinj : ∀ x y, φ x = φ y → x = y)
    (N : V → V → Atom) (N' : V' → V' → Atom)
    (hNN : ∀ x y, N' x y = N (φ x) (φ y)) (h : Frame N) : Frame N' where
  refl_eq := fun x => by rw [hNN]; exact h.refl_eq (φ x)
  eq_id := fun x y hxy => by rw [hNN] at hxy; exact hinj x y (h.eq_id _ _ hxy)
  conv_ := fun x y => by rw [hNN, hNN]; exact h.conv_ (φ x) (φ y)
  comp_ := fun x y z => by rw [hNN, hNN, hNN]; exact h.comp_ (φ x) (φ y) (φ z)

/-- **THE GENERAL ENCODER IS VALID.**  A `Fin`-indexed valid certificate
    encodes to a `FinMT` the Boolean checker accepts.  Transports all 12
    `MultiTierOk` fields across the `Fin.cast` (index equality is a
    theorem, not defeq); `frame_q` via `frame_reindex`; `e_ex`/`k_ex`
    witnesses via the cast round-trips (no pullback — index types match). -/
theorem encodeMT_mtOk {nE nK : Nat} (T : MultiTier (Fin nE) (Fin nK))
    (hok : MultiTierOk T) : (encodeMT T).mtOkB = true := by
  apply mtOkB_complete
  have henE : (encodeMT T).nE = nE := encodeMT_nE T
  have henK : (encodeMT T).nK = nK := encodeMT_nK T
  have hDtau : ∀ e, (decodeMT (encodeMT T)).tauE e = T.tauE (Fin.cast henE e) :=
    fun e => encodeMT_tE T (Fin.cast henE e)
  have hDE : ∀ e f, (decodeMT (encodeMT T)).E e f
      = T.E (Fin.cast henE e) (Fin.cast henE f) :=
    fun e f => encodeMT_Ea T (Fin.cast henE e) (Fin.cast henE f)
  have hDK : ∀ k e, (decodeMT (encodeMT T)).K k e
      = T.K (Fin.cast henK k) (Fin.cast henE e) :=
    fun k e => encodeMT_Ka T (Fin.cast henK k) (Fin.cast henE e)
  have hDQ : ∀ k k', (decodeMT (encodeMT T)).Q k k'
      = T.Q (Fin.cast henK k) (Fin.cast henK k') :=
    fun k k' => encodeMT_Qa T (Fin.cast henK k) (Fin.cast henK k')
  have hDup : ∀ k, (decodeMT (encodeMT T)).up k = T.up (Fin.cast henK k) :=
    fun k => encodeMT_upa T (Fin.cast henK k)
  have hDp : ∀ k, (decodeMT (encodeMT T)).p k = T.p (Fin.cast henK k) :=
    fun k => encodeMT_pk T (Fin.cast henK k)
  have hDphase : ∀ k a, a < (decodeMT (encodeMT T)).p k →
      (decodeMT (encodeMT T)).phase k a = T.phase (Fin.cast henK k) a :=
    fun k a ha => encodeMT_phase T (Fin.cast henK k) a (hDp k ▸ ha)
  have hcE : ∀ f : Fin nE, (Fin.cast henE (Fin.cast henE.symm f) : Fin nE) = f :=
    fun f => Fin.ext rfl
  have hcK : ∀ k : Fin nK, (Fin.cast henK (Fin.cast henK.symm k) : Fin nK) = k :=
    fun k => Fin.ext rfl
  have hceinj : ∀ a b : Fin (encodeMT T).nE, Fin.cast henE a = Fin.cast henE b → a = b :=
    fun a b h => congrArg (Fin.cast henE.symm) h
  have hckinj : ∀ a b : Fin (encodeMT T).nK, Fin.cast henK a = Fin.cast henK b → a = b :=
    fun a b h => congrArg (Fin.cast henK.symm) h
  refine
    { hp := fun k => by rw [hDp k]; exact hok.hp _
      frame_q := ?_
      e_clash := fun e a h => by rw [hDtau e] at h ⊢; exact hok.e_clash _ a h
      e_nobot := fun e => by rw [hDtau e]; exact hok.e_nobot _
      e_and := fun e c d h => by rw [hDtau e] at h ⊢; exact hok.e_and _ c d h
      e_or := fun e c d h => by rw [hDtau e] at h ⊢; exact hok.e_or _ c d h
      k_clash := fun k a ha n h => by
        rw [hDphase k a ha] at h ⊢; exact hok.k_clash _ a (hDp k ▸ ha) n h
      k_nobot := fun k a ha => by
        rw [hDphase k a ha]; exact hok.k_nobot _ a (hDp k ▸ ha)
      k_and := fun k a ha c d h => by
        rw [hDphase k a ha] at h ⊢; exact hok.k_and _ a (hDp k ▸ ha) c d h
      k_or := fun k a ha c d h => by
        rw [hDphase k a ha] at h ⊢; exact hok.k_or _ a (hDp k ▸ ha) c d h
      ee_all := fun e f r c hall hEf => by
        rw [hDtau f]; rw [hDtau e] at hall; rw [hDE e f] at hEf
        exact hok.ee_all _ _ r c hall hEf
      ek_all := fun e r c hall k hK a ha => by
        rw [hDphase k a ha]; rw [hDtau e] at hall; rw [hDK k e] at hK
        exact hok.ek_all _ r c hall _ hK a (hDp k ▸ ha)
      ke_all := fun k a ha r c hall f hK => by
        rw [hDtau f]; rw [hDphase k a ha] at hall; rw [hDK k f] at hK
        exact hok.ke_all _ a (hDp k ▸ ha) r c hall _ hK
      kk_pp := fun k a ha c hall b hb => by
        rw [hDphase k b hb]; rw [hDphase k a ha] at hall
        exact hok.kk_pp _ a (hDp k ▸ ha) c hall b (hDp k ▸ hb)
      kk_ppi := fun k a ha c hall b hb => by
        rw [hDphase k b hb]; rw [hDphase k a ha] at hall
        exact hok.kk_ppi _ a (hDp k ▸ ha) c hall b (hDp k ▸ hb)
      kk_eq := fun k a ha c hall => by
        rw [hDphase k a ha] at hall ⊢; exact hok.kk_eq _ a (hDp k ▸ ha) c hall
      kq_all := fun k k' hkk a ha r c hall hQ b hb => by
        rw [hDphase k' b hb]; rw [hDphase k a ha] at hall; rw [hDQ k k'] at hQ
        exact hok.kq_all _ _ (fun h => hkk (hckinj k k' h))
          a (hDp k ▸ ha) r c hall hQ b (hDp k' ▸ hb)
      e_ex := ?_
      k_ex := ?_ }
  · refine frame_reindex (Sum.map (Fin.cast henE) (Fin.cast henK)) ?_
      (qnet T.E T.K T.Q) _ ?_ hok.frame_q
    · rintro (x | x) (y | y) h
      · exact congrArg Sum.inl (hceinj x y (by simpa [Sum.map] using h))
      · simp [Sum.map] at h
      · simp [Sum.map] at h
      · exact congrArg Sum.inr (hckinj x y (by simpa [Sum.map] using h))
    · rintro (e | k) (f | k')
      · exact hDE e f
      · show conv ((decodeMT (encodeMT T)).K k' e)
          = conv (T.K (Fin.cast henK k') (Fin.cast henE e))
        rw [hDK k' e]
      · exact hDK k f
      · show (if k = k' then eq else (decodeMT (encodeMT T)).Q k k')
          = (if Fin.cast henK k = Fin.cast henK k' then eq
             else T.Q (Fin.cast henK k) (Fin.cast henK k'))
        by_cases hkk : k = k'
        · rw [if_pos hkk, if_pos (by rw [hkk])]
        · rw [if_neg hkk, if_neg (fun h => hkk (hckinj k k' h)), hDQ k k']
  · intro e r c hmem
    rw [hDtau e] at hmem
    rcases hok.e_ex (Fin.cast henE e) r c hmem with ⟨f, hEf, harg⟩ | ⟨k, hK, a, ha, harg⟩
    · refine Or.inl ⟨Fin.cast henE.symm f, ?_, ?_⟩
      · rw [hDE e (Fin.cast henE.symm f), hcE f]; exact hEf
      · rw [hDtau (Fin.cast henE.symm f), hcE f]; exact harg
    · have ha' : a < (decodeMT (encodeMT T)).p (Fin.cast henK.symm k) := by
        rw [hDp, hcK k]; exact ha
      refine Or.inr ⟨Fin.cast henK.symm k, ?_, a, ha', ?_⟩
      · rw [hDK (Fin.cast henK.symm k) e, hcK k]; exact hK
      · rw [hDphase (Fin.cast henK.symm k) a ha', hcK k]; exact harg
  · intro k a ha r c hmem
    rw [hDphase k a ha] at hmem
    rcases hok.k_ex (Fin.cast henK k) a (hDp k ▸ ha) r c hmem with
      ⟨f, hK, harg⟩ | ⟨hr, b, hb, harg⟩ | ⟨hr, harg⟩ | ⟨k', hkk, hQ, b, hb, harg⟩
    · refine Or.inl ⟨Fin.cast henE.symm f, ?_, ?_⟩
      · rw [hDK k (Fin.cast henE.symm f), hcE f]; exact hK
      · rw [hDtau (Fin.cast henE.symm f), hcE f]; exact harg
    · have hb' : b < (decodeMT (encodeMT T)).p k := by rw [hDp k]; exact hb
      refine Or.inr (Or.inl ⟨?_, b, hb', ?_⟩)
      · rw [hDup k]; exact hr
      · rw [hDphase k b hb']; exact harg
    · exact Or.inr (Or.inr (Or.inl ⟨hr, by rw [hDphase k a ha]; exact harg⟩))
    · have hb' : b < (decodeMT (encodeMT T)).p (Fin.cast henK.symm k') := by
        rw [hDp, hcK k']; exact hb
      refine Or.inr (Or.inr (Or.inr ⟨Fin.cast henK.symm k',
        fun h => hkk (by rw [h]; exact hcK k'), ?_, b, hb', ?_⟩))
      · rw [hDQ k (Fin.cast henK.symm k'), hcK k']; exact hQ
      · rw [hDphase (Fin.cast henK.symm k') b hb', hcK k']; exact harg

/-- The encoded certificate is ACCEPTED at external index `e.val`
    (carrying `C0`). -/
theorem encodeMT_accepts {nE nK : Nat} (T : MultiTier (Fin nE) (Fin nK))
    (hok : MultiTierOk T) (C0 : Concept) (e : Fin nE) (hC0 : C0 ∈ T.tauE e) :
    (encodeMT T).mtAcceptB e.val C0 = true := by
  rw [FinMT.mtAcceptB]
  refine andB_intro (encodeMT_mtOk T hok) ?_
  rw [FinMT.rootB, if_pos (by rw [encodeMT_nE]; exact e.isLt)]
  apply decide_eq_true
  rw [encodeMT_tE T e]; exact hC0

/-! ### Reindexing a certificate onto new index types (e.g. `Unit → Fin 1`) -/

/-- Reindex a `MultiTier` along maps on the index types. -/
def reindexMT {β κ β' κ' : Type} (fβ : β' → β) (fκ : κ' → κ)
    (T : MultiTier β κ) : MultiTier β' κ' where
  E := fun e f => T.E (fβ e) (fβ f)
  K := fun k e => T.K (fκ k) (fβ e)
  Q := fun k k' => T.Q (fκ k) (fκ k')
  up := fun k => T.up (fκ k)
  tauE := fun e => T.tauE (fβ e)
  p := fun k => T.p (fκ k)
  phase := fun k a => T.phase (fκ k) a

/-- Reindexing along BIJECTIVE index maps preserves validity (injective for
    the frame, surjective for existential-witness pullback). -/
theorem reindexMT_ok {β κ β' κ' : Type} [DecidableEq κ] [DecidableEq κ']
    (fβ : β' → β) (fκ : κ' → κ) (T : MultiTier β κ) (hok : MultiTierOk T)
    (hβinj : ∀ e f, fβ e = fβ f → e = f) (hβsurj : ∀ b, ∃ e, fβ e = b)
    (hκinj : ∀ k k', fκ k = fκ k' → k = k') (hκsurj : ∀ k, ∃ k', fκ k' = k) :
    MultiTierOk (reindexMT fβ fκ T) := by
  refine
    { hp := fun k => hok.hp (fκ k)
      frame_q := frame_reindex (Sum.map fβ fκ) ?_ (qnet T.E T.K T.Q) _ ?_ hok.frame_q
      e_clash := fun e a h => hok.e_clash (fβ e) a h
      e_nobot := fun e => hok.e_nobot (fβ e)
      e_and := fun e c d h => hok.e_and (fβ e) c d h
      e_or := fun e c d h => hok.e_or (fβ e) c d h
      k_clash := fun k a ha n h => hok.k_clash (fκ k) a ha n h
      k_nobot := fun k a ha => hok.k_nobot (fκ k) a ha
      k_and := fun k a ha c d h => hok.k_and (fκ k) a ha c d h
      k_or := fun k a ha c d h => hok.k_or (fκ k) a ha c d h
      ee_all := fun e f r c hall hEf => hok.ee_all (fβ e) (fβ f) r c hall hEf
      ek_all := fun e r c hall k hK a ha => hok.ek_all (fβ e) r c hall (fκ k) hK a ha
      ke_all := fun k a ha r c hall f hK => hok.ke_all (fκ k) a ha r c hall (fβ f) hK
      kk_pp := fun k a ha c hall b hb => hok.kk_pp (fκ k) a ha c hall b hb
      kk_ppi := fun k a ha c hall b hb => hok.kk_ppi (fκ k) a ha c hall b hb
      kk_eq := fun k a ha c hall => hok.kk_eq (fκ k) a ha c hall
      kq_all := fun k k' hkk a ha r c hall hQ b hb =>
        hok.kq_all (fκ k) (fκ k') (fun h => hkk (hκinj k k' h)) a ha r c hall hQ b hb
      e_ex := ?_
      k_ex := ?_ }
  · rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (hβinj x y (by simpa [Sum.map] using h))
    · simp [Sum.map] at h
    · simp [Sum.map] at h
    · exact congrArg Sum.inr (hκinj x y (by simpa [Sum.map] using h))
  · rintro (e | k) (f | k')
    · rfl
    · rfl
    · rfl
    · show (if k = k' then eq else (reindexMT fβ fκ T).Q k k')
        = (if fκ k = fκ k' then eq else T.Q (fκ k) (fκ k'))
      by_cases hkk : k = k'
      · rw [if_pos hkk, if_pos (by rw [hkk])]
      · rw [if_neg hkk, if_neg (fun h => hkk (hκinj k k' h))]; rfl
  · intro e r c hmem
    rcases hok.e_ex (fβ e) r c hmem with ⟨f, hEf, harg⟩ | ⟨k, hK, a, ha, harg⟩
    · obtain ⟨f', rfl⟩ := hβsurj f; exact Or.inl ⟨f', hEf, harg⟩
    · obtain ⟨k', rfl⟩ := hκsurj k; exact Or.inr ⟨k', hK, a, ha, harg⟩
  · intro k a ha r c hmem
    rcases hok.k_ex (fκ k) a ha r c hmem with
      ⟨f, hK, harg⟩ | ⟨hr, b, hb, harg⟩ | ⟨hr, harg⟩ | ⟨k', hkk, hQ, b, hb, harg⟩
    · obtain ⟨f', rfl⟩ := hβsurj f; exact Or.inl ⟨f', hK, harg⟩
    · exact Or.inr (Or.inl ⟨hr, b, hb, harg⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hr, harg⟩))
    · obtain ⟨k'', rfl⟩ := hκsurj k'
      exact Or.inr (Or.inr (Or.inr ⟨k'', fun h => hkk (by rw [h]), hQ, b, hb, harg⟩))

/-- The `Fin 1`-reindexed encoding of a valid `(Unit, Unit)` certificate
    carrying `C0` is accepted (the `Fin 1 → Unit` maps are bijections since
    both are subsingletons). -/
theorem unitTower_accepted (T : MultiTier Unit Unit) (hok : MultiTierOk T)
    (C0 : Concept) (hC0 : C0 ∈ T.tauE ()) :
    (encodeMT (reindexMT (fun _ : Fin 1 => (() : Unit))
      (fun _ : Fin 1 => (() : Unit)) T)).mtAcceptB 0 C0 = true := by
  have hokR : MultiTierOk (reindexMT (fun _ : Fin 1 => (() : Unit))
      (fun _ : Fin 1 => (() : Unit)) T) :=
    reindexMT_ok _ _ T hok
      (fun e f _ => Subsingleton.elim e f)
      (fun _ => ⟨0, Subsingleton.elim _ _⟩)
      (fun k k' _ => Subsingleton.elim k k')
      (fun _ => ⟨0, Subsingleton.elim _ _⟩)
  exact encodeMT_accepts _ hokR C0 0 hC0

/-- The `Fin 1`-reindexed encoding of a valid `(Unit, Fin nK)` certificate
    (root + `N` kernels) carrying `C0` is accepted — the external map is a
    subsingleton bijection, the kernel map is the identity. -/
theorem multiTower_accepted {nK : Nat} (T : MultiTier Unit (Fin nK))
    (hok : MultiTierOk T) (C0 : Concept) (hC0 : C0 ∈ T.tauE ()) :
    (encodeMT (reindexMT (fun _ : Fin 1 => (() : Unit)) (id : Fin nK → Fin nK)
      T)).mtAcceptB 0 C0 = true := by
  have hokR : MultiTierOk (reindexMT (fun _ : Fin 1 => (() : Unit))
      (id : Fin nK → Fin nK) T) :=
    reindexMT_ok _ _ T hok
      (fun e f _ => Subsingleton.elim e f)
      (fun _ => ⟨0, Subsingleton.elim _ _⟩)
      (fun _ _ h => h)
      (fun k => ⟨k, rfl⟩)
  exact encodeMT_accepts _ hokR C0 0 hC0

/-- `1×1` atom tables (`nE = nK = 1`); the free `bool` column. -/
def atomTab1 : List (List (List Atom)) := allListsLe (allListsLe allAtoms 1) 1
def boolCol : List (List Bool) := allListsLe [true, false] 1

/-- The fixed, model-independent enumeration for the SINGLE-TOWER case:
    kernel-ful `FinMT`s (`nE ≤ 1`, `nK ≤ 1`) with labels/phase-types drawn
    from `cl C0`, `≤ B` phases per kernel, `1×1` atom tables, root index
    `0`.  Computable. -/
def codesV (C0 : Concept) : List (FinMT × Nat) :=
  let labels := allListsLe (cl C0) (cl C0).length
  let phaseCol := allListsLe (allListsLe labels labels.length) 1
  (allListsLe labels 1).flatMap fun tauE =>
    atomTab1.flatMap fun E =>
      atomTab1.flatMap fun K =>
        atomTab1.flatMap fun Q =>
          boolCol.flatMap fun up =>
            phaseCol.map fun phases => (⟨tauE, E, K, Q, up, phases⟩, 0)

/-- The `Fin 1`-encoded certificate's code lies in `codesV C0`, given its
    label + phase-types are drawn from `cl C0` and its period is `≤ B`. -/
theorem unitTower_mem_codesV (T : MultiTier Unit Unit) (C0 : Concept)
    (htauL : T.tauE () ∈ allListsLe (cl C0) (cl C0).length)
    (hphL : ∀ a, T.phase () a ∈ allListsLe (cl C0) (cl C0).length)
    (hpB : T.p () ≤ (allListsLe (cl C0) (cl C0).length).length) :
    (encodeMT (reindexMT (fun _ : Fin 1 => (() : Unit))
      (fun _ : Fin 1 => (() : Unit)) T), 0) ∈ codesV C0 := by
  have hmap1 : ∀ {A : Type} (g : Fin 1 → A) (univ : List A), g 0 ∈ univ →
      (List.finRange 1).map g ∈ allListsLe univ 1 := by
    intro A g univ hg
    rw [mem_allListsLe]
    refine ⟨Nat.le_of_eq (by rw [List.length_map, List.length_finRange]),
      fun x hx => ?_⟩
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    rw [Subsingleton.elim e 0]; exact hg
  have hbool : ∀ b : Bool, b ∈ [true, false] := by intro b; cases b <;> decide
  simp only [codesV, atomTab1, boolCol, List.mem_flatMap, List.mem_map]
  refine ⟨_, ?_, _, ?_, _, ?_, _, ?_, _, ?_, _, ?_, rfl⟩
  · exact hmap1 _ _ htauL
  · exact hmap1 _ _ (hmap1 _ _ (mem_allAtoms _))
  · exact hmap1 _ _ (hmap1 _ _ (mem_allAtoms _))
  · exact hmap1 _ _ (hmap1 _ _ (mem_allAtoms _))
  · exact hmap1 _ _ (hbool _)
  · refine hmap1 _ _ ?_
    rw [mem_allListsLe]
    refine ⟨by rw [List.length_map, List.length_range]; exact hpB, fun x hx => ?_⟩
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    exact hphL a

/-- WIDER-period enumeration: `codesV` with the phase-list length bound as
    a parameter `Pb` (the round-robin period is `≤ B·L > B`, so it needs
    `Pb = B·L`, not `codesV`'s single-demand `B`). -/
def codesVB (C0 : Concept) (Pb : Nat) : List (FinMT × Nat) :=
  let labels := allListsLe (cl C0) (cl C0).length
  let phaseCol := allListsLe (allListsLe labels Pb) 1
  (allListsLe labels 1).flatMap fun tauE =>
    atomTab1.flatMap fun E =>
      atomTab1.flatMap fun K =>
        atomTab1.flatMap fun Q =>
          boolCol.flatMap fun up =>
            phaseCol.map fun phases => (⟨tauE, E, K, Q, up, phases⟩, 0)

/-- Membership for the wider enumeration: period bound `p ≤ Pb`. -/
theorem unitTower_mem_codesVB (T : MultiTier Unit Unit) (C0 : Concept) (Pb : Nat)
    (htauL : T.tauE () ∈ allListsLe (cl C0) (cl C0).length)
    (hphL : ∀ a, T.phase () a ∈ allListsLe (cl C0) (cl C0).length)
    (hpB : T.p () ≤ Pb) :
    (encodeMT (reindexMT (fun _ : Fin 1 => (() : Unit))
      (fun _ : Fin 1 => (() : Unit)) T), 0) ∈ codesVB C0 Pb := by
  have hmap1 : ∀ {A : Type} (g : Fin 1 → A) (univ : List A), g 0 ∈ univ →
      (List.finRange 1).map g ∈ allListsLe univ 1 := by
    intro A g univ hg
    rw [mem_allListsLe]
    refine ⟨Nat.le_of_eq (by rw [List.length_map, List.length_finRange]),
      fun x hx => ?_⟩
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    rw [Subsingleton.elim e 0]; exact hg
  have hbool : ∀ b : Bool, b ∈ [true, false] := by intro b; cases b <;> decide
  simp only [codesVB, atomTab1, boolCol, List.mem_flatMap, List.mem_map]
  refine ⟨_, ?_, _, ?_, _, ?_, _, ?_, _, ?_, _, ?_, rfl⟩
  · exact hmap1 _ _ htauL
  · exact hmap1 _ _ (hmap1 _ _ (mem_allAtoms _))
  · exact hmap1 _ _ (hmap1 _ _ (mem_allAtoms _))
  · exact hmap1 _ _ (hmap1 _ _ (mem_allAtoms _))
  · exact hmap1 _ _ (hbool _)
  · refine hmap1 _ _ ?_
    rw [mem_allListsLe]
    refine ⟨by rw [List.length_map, List.length_range]; exact hpB, fun x hx => ?_⟩
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    exact hphL a

/-- The chain's model type recurs with a COMPUTABLY BOUNDED period `p ≤ B`
    (`B = |allListsLe (cl C0) |cl C0||`), past any `L` — the type sequence
    lives in `allListsLe (cl C0) |cl C0|`, so `segment_exists_bounded`
    applies. -/
theorem mty_segment_bounded {α : Type} {I : Interp α} (C0 : Concept)
    (c : Nat → α) (L : Nat) :
    ∃ i p, L ≤ i ∧ 0 < p ∧ p ≤ (allListsLe (cl C0) (cl C0).length).length ∧
      mty C0 I (c i) = mty C0 I (c (i + p)) := by
  have hmem : ∀ n, mty C0 I (c n) ∈ allListsLe (cl C0) (cl C0).length := by
    intro n
    rw [mem_allListsLe]
    exact ⟨by rw [mty]; exact List.length_filter_le _ _,
      fun x hx => by rw [mty] at hx; exact (List.mem_filter.mp hx).1⟩
  obtain ⟨i, j, hLi, hij, hjB, heq⟩ :=
    segment_exists_bounded (allListsLe (cl C0) (cl C0).length)
      (fun n => mty C0 I (c n)) hmem L
  exact ⟨i, j - i, hLi, by omega, by omega,
    by rw [show i + (j - i) = j from by omega]; exact heq⟩

/-- Consecutive `L` residues cover `[0, L)`: for any target `k < L` and any
    offset `c`, some `b < L` has `(c + b) % L = k`.  The arithmetic heart of
    round-robin coverage — every demand-arg is reached within one cycle. -/
theorem mod_shift_cover (c k L : Nat) (hL : 0 < L) (hk : k < L) :
    ∃ b, b < L ∧ (c + b) % L = k := by
  rcases Nat.lt_or_ge k (c % L) with h | h
  · refine ⟨k + L - c % L, by have := Nat.mod_lt c hL; omega, ?_⟩
    have hb : c + (k + L - c % L) = k + (c / L + 1) * L := by
      have hdm := Nat.div_add_mod' c L
      have hcm := Nat.mod_lt c hL
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [hb, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  · refine ⟨k - c % L, by omega, ?_⟩
    have hb : c + (k - c % L) = k + c / L * L := by
      have hdm := Nat.div_add_mod' c L; omega
    rw [hb, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]

/-- ROUND-ROBIN RECURRENCE: the type recurs along the round-robin chain
    with a period that is a MULTIPLE of `L = Ds.length` — got for free by
    pigeonholing only the sub-sequence at multiples of `L`, so the period
    `(b−a)·L` covers whole cycles.  Avoids a product pigeonhole. -/
theorem rr_segment {α : Type} {I : Interp α} (hI : RCC5Interp I) (C0 : Concept)
    (Ds : List Concept) (hL : 0 < Ds.length) (x0 : α)
    (h0 : persistAll I C0 Ds x0) :
    ∃ i p, 0 < i ∧ 0 < p ∧
      p ≤ (allListsLe (cl C0) (cl C0).length).length * Ds.length ∧
      Ds.length ∣ p ∧
      mty C0 I (rrPt hI C0 Ds hL x0 h0 i) =
      mty C0 I (rrPt hI C0 Ds hL x0 h0 (i + p)) := by
  have hmem : ∀ n, mty C0 I (rrPt hI C0 Ds hL x0 h0 (n * Ds.length)) ∈
      allListsLe (cl C0) (cl C0).length := by
    intro n
    rw [mem_allListsLe]
    exact ⟨by rw [mty]; exact List.length_filter_le _ _,
      fun x hx => by rw [mty] at hx; exact (List.mem_filter.mp hx).1⟩
  obtain ⟨a, b, hLa, hab, hjB, heq⟩ :=
    segment_exists_bounded (allListsLe (cl C0) (cl C0).length)
      (fun n => mty C0 I (rrPt hI C0 Ds hL x0 h0 (n * Ds.length))) hmem 1
  have harith : a * Ds.length + (b - a) * Ds.length = b * Ds.length := by
    rw [← Nat.add_mul, show a + (b - a) = b from by omega]
  refine ⟨a * Ds.length, (b - a) * Ds.length, Nat.mul_pos (by omega) hL,
    Nat.mul_pos (by omega) hL, Nat.mul_le_mul (by omega) (Nat.le_refl _),
    ⟨b - a, Nat.mul_comm (b - a) Ds.length⟩, ?_⟩
  rw [harith]
  exact heq

/-- ROUND-ROBIN COVERAGE: within a recurrent segment `[i, i+p)` whose
    period `p` is a multiple of `L`, EVERY demand-arg `Ds[k]` is carried at
    some phase `b < p`.  Combines `mod_shift_cover` (pick the phase whose
    served-demand index is `k`) with `rrPt_serves`. -/
theorem rr_covers {α : Type} {I : Interp α} (hI : RCC5Interp I) (C0 : Concept)
    (Ds : List Concept) (hL : 0 < Ds.length) (x0 : α)
    (h0 : persistAll I C0 Ds x0) (i p : Nat) (hi : 0 < i) (hp : 0 < p)
    (hdvd : Ds.length ∣ p) (k : Nat) (hk : k < Ds.length) :
    ∃ b, b < p ∧ Ds.get ⟨k, hk⟩ ∈ mty C0 I (rrPt hI C0 Ds hL x0 h0 (i + b)) := by
  obtain ⟨b, hbL, hbmod⟩ := mod_shift_cover (i - 1) k Ds.length hL hk
  refine ⟨b, by have := Nat.le_of_dvd hp hdvd; omega, ?_⟩
  have hs := rrPt_serves hI C0 Ds hL x0 h0 (i - 1 + b)
  rw [show i - 1 + b + 1 = i + b from by omega] at hs
  rw [show (⟨(i - 1 + b) % Ds.length, Nat.mod_lt _ hL⟩ : Fin Ds.length) = ⟨k, hk⟩
    from Fin.ext hbmod] at hs
  exact hs

/-- DESCENDING recurrence (mirror of `rr_segment`): period a multiple of
    `L`, `≤ B·L`.  Proof is direction-agnostic (pigeonhole on the
    sub-sequence at multiples of `L`). -/
theorem rr_segmentI {α : Type} {I : Interp α} (hI : RCC5Interp I) (C0 : Concept)
    (Ds : List Concept) (hL : 0 < Ds.length) (x0 : α)
    (h0 : persistAllI I C0 Ds x0) :
    ∃ i p, 0 < i ∧ 0 < p ∧
      p ≤ (allListsLe (cl C0) (cl C0).length).length * Ds.length ∧
      Ds.length ∣ p ∧
      mty C0 I (rrPtI hI C0 Ds hL x0 h0 i) =
      mty C0 I (rrPtI hI C0 Ds hL x0 h0 (i + p)) := by
  have hmem : ∀ n, mty C0 I (rrPtI hI C0 Ds hL x0 h0 (n * Ds.length)) ∈
      allListsLe (cl C0) (cl C0).length := by
    intro n
    rw [mem_allListsLe]
    exact ⟨by rw [mty]; exact List.length_filter_le _ _,
      fun x hx => by rw [mty] at hx; exact (List.mem_filter.mp hx).1⟩
  obtain ⟨a, b, hLa, hab, hjB, heq⟩ :=
    segment_exists_bounded (allListsLe (cl C0) (cl C0).length)
      (fun n => mty C0 I (rrPtI hI C0 Ds hL x0 h0 (n * Ds.length))) hmem 1
  have harith : a * Ds.length + (b - a) * Ds.length = b * Ds.length := by
    rw [← Nat.add_mul, show a + (b - a) = b from by omega]
  refine ⟨a * Ds.length, (b - a) * Ds.length, Nat.mul_pos (by omega) hL,
    Nat.mul_pos (by omega) hL, Nat.mul_le_mul (by omega) (Nat.le_refl _),
    ⟨b - a, Nat.mul_comm (b - a) Ds.length⟩, ?_⟩
  rw [harith]
  exact heq

/-- DESCENDING coverage (mirror of `rr_covers`): every demand-arg is
    carried at some phase in the recurrent period. -/
theorem rr_coversI {α : Type} {I : Interp α} (hI : RCC5Interp I) (C0 : Concept)
    (Ds : List Concept) (hL : 0 < Ds.length) (x0 : α)
    (h0 : persistAllI I C0 Ds x0) (i p : Nat) (hi : 0 < i) (hp : 0 < p)
    (hdvd : Ds.length ∣ p) (k : Nat) (hk : k < Ds.length) :
    ∃ b, b < p ∧ Ds.get ⟨k, hk⟩ ∈ mty C0 I (rrPtI hI C0 Ds hL x0 h0 (i + b)) := by
  obtain ⟨b, hbL, hbmod⟩ := mod_shift_cover (i - 1) k Ds.length hL hk
  refine ⟨b, by have := Nat.le_of_dvd hp hdvd; omega, ?_⟩
  have hs := rrPtI_serves hI C0 Ds hL x0 h0 (i - 1 + b)
  rw [show i - 1 + b + 1 = i + b from by omega] at hs
  rw [show (⟨(i - 1 + b) % Ds.length, Nat.mod_lt _ hL⟩ : Fin Ds.length) = ⟨k, hk⟩
    from Fin.ext hbmod] at hs
  exact hs

/-- Per-formula fragment check: existentials are `DR`/`PO`/`EQ`,
    universals are non-`PO`. -/
def hfragOk (F : Concept) : Bool :=
  match F with
  | .ex r _ => decide (r = dr ∨ r = po ∨ r = eq)
  | .all r _ => decide (r ≠ po)
  | _ => true

/-- DECIDABLE FRAGMENT MEMBERSHIP: `HFrag C₀` reduces to a Boolean check
    over the finite closure `cl C₀` — so membership is `by decide`. -/
def hfragB (C0 : Concept) : Bool := (cl C0).all hfragOk

theorem hfragB_iff (C0 : Concept) : hfragB C0 = true ↔ HFrag C0 := by
  rw [hfragB, List.all_eq_true]
  constructor
  · intro h
    refine ⟨fun r c hmem => ?_, fun r c hmem => ?_⟩
    · have hc := h (Concept.ex r c) hmem
      simpa only [hfragOk, decide_eq_true_eq] using hc
    · have hc := h (Concept.all r c) hmem
      simpa only [hfragOk, decide_eq_true_eq] using hc
  · intro ⟨hex, hall⟩ F hmem
    cases F with
    | ex r c => simpa only [hfragOk, decide_eq_true_eq] using hex r c hmem
    | all r c => simpa only [hfragOk, decide_eq_true_eq] using hall r c hmem
    | top => rfl
    | bot => rfl
    | atom a => rfl
    | natom a => rfl
    | and a b => rfl
    | or a b => rfl

/-! ### The ASCENDING-MIXED fragment `AscMix` (∀PO-free ∧ ∃PPI-free)

The first mixing milestone.  `AscMix C0` = `POFree C0` (∀PO-free) together with
∃PPI-freeness (no *descending* existential in the closure).  Existentials may be
`DR`/`PO`/`EQ`/`PP` — so this is a STRICT extension of `HFrag` (which forbids
`∃PP`).  The point of isolating it: with only ascending verticals, every kernel
is reached from the root along a path that takes a horizontal step (budget−1)
before each new kernel base, so the coverage recursion TERMINATES ON BUDGET
ALONE — no §21 finite-poset-of-kernels argument (that is only forced by
same-budget OPPOSITE-direction nesting, which ∃PPI-freeness rules out). -/

/-- Per-formula ascending-mixed check: existentials avoid `PPI` (descending);
    universals are non-`PO`. -/
def ascExOk (F : Concept) : Bool :=
  match F with
  | .ex ppi _ => false
  | .all r _ => decide (r ≠ po)
  | _ => true

/-- The ASCENDING-MIXED fragment: `∀PO`-free and `∃PPI`-free.  Carries `POFree`
    directly (so no cl→structural derivation is needed) plus ∃PPI-freeness. -/
structure AscMix (C0 : Concept) : Prop where
  pofree : POFree C0
  hnoppi : ∀ c, Concept.ex ppi c ∉ cl C0

/-- DECIDABLE membership: `AscMix C₀` is a Boolean check over `cl C₀`. -/
def ascMixB (C0 : Concept) : Bool := pofreeB C0 && (cl C0).all ascExOk

theorem ascMixB_iff (C0 : Concept) : ascMixB C0 = true ↔ AscMix C0 := by
  rw [ascMixB, Bool.and_eq_true, pofreeB_iff, List.all_eq_true]
  constructor
  · intro ⟨hpo, hall⟩
    refine ⟨hpo, fun c hmem => ?_⟩
    exact absurd (hall (Concept.ex ppi c) hmem) (by simp [ascExOk])
  · intro ⟨hpo, hnoppi⟩
    refine ⟨hpo, fun F hmem => ?_⟩
    cases F with
    | ex r c =>
      cases r with
      | ppi => exact absurd hmem (hnoppi c)
      | dr => rfl
      | po => rfl
      | eq => rfl
      | pp => rfl
    | all r c =>
      simpa only [ascExOk, decide_eq_true_eq] using pofree_cl_all C0 hpo r c hmem
    | top => rfl
    | bot => rfl
    | atom a => rfl
    | natom a => rfl
    | and a b => rfl
    | or a b => rfl

/-- Non-vacuity + strictness: `Casc = ∃PP.A₀` is in `AscMix` but NOT in `HFrag`
    (its `∃PP` is forbidden horizontally) — the fragment genuinely extends the
    horizontal one with ascending verticals. -/
def Casc : Concept := .ex pp (.atom 0)

theorem casc_ascmix : AscMix Casc := (ascMixB_iff Casc).mp (by decide)

theorem casc_not_hfrag : ¬ HFrag Casc :=
  fun h => absurd (h.hex pp (Concept.atom 0) (cl_self Casc)) (by decide)

/-! ### Non-vacuity: the horizontal fragment fires on a nested-`∀DR` concept

`Cwit = ∃DR.⊤ ⊓ ∀DR.(∀DR.A)` is EXCLUDED from `DRFrag` (its `∀DR` guards
a `∀DR`, so it is not DR-guard-free) but lies IN `HFrag`.  It is
satisfiable in a two-point all-`DR` model, so `satisfiable_iff_hfrag_cert`
produces a valid certificate — demonstrating the lift is non-vacuous and
strictly beyond the `∀DR`-propagation fragment. -/

namespace HFragWitness

/-- The two-point all-`DR` frame (`EQ` on the diagonal). -/
def Nwit : Bool → Bool → Atom := fun v w => if v = w then eq else dr

theorem Nwit_frame : Frame Nwit := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `A = atom 0`, true at the point `true`. -/
def valwit : Nat → Bool → Prop := fun a x => a = 0 ∧ x = true

def Iwit : Interp Bool := ⟨fun _ => True, Nwit, valwit⟩

theorem Iwit_rcc5 : RCC5Interp Iwit := frame_rcc5 Nwit Nwit_frame valwit

/-- `∃DR.⊤ ⊓ ∀DR.(∀DR.A)` — nested `∀DR`, excluded from `DRFrag`. -/
def Cwit : Concept :=
  .and (.ex dr .top) (.all dr (.all dr (.atom 0)))

theorem Cwit_sat : Satisfiable Cwit :=
  ⟨Bool, Iwit, Iwit_rcc5, true, trivial,
    ⟨⟨false, trivial, rfl, trivial⟩, by
      intro y _ hy
      cases y with
      | true => exact absurd hy (by decide)
      | false =>
        intro z _ hz
        cases z with
        | true => exact ⟨rfl, rfl⟩
        | false => exact absurd hz (by decide)⟩⟩

theorem Cwit_hfrag : HFrag Cwit := (hfragB_iff Cwit).mp (by decide)

/-- The `∀DR`-nested `Cwit` is NOT DR-guard-free, so `DRFrag Cwit` fails —
    `HFrag` strictly extends the `∀DR`-propagation fragment. -/
theorem Cwit_not_drfrag : ¬ DRFrag Cwit := fun h =>
  h.hgf (Concept.all dr (Concept.atom 0)) (by decide)

/-- THE HORIZONTAL FRAGMENT THEOREM FIRES on the nested-`∀DR` `Cwit`:
    a valid finite multi-tier certificate carrying it exists. -/
theorem Cwit_has_cert :
    ∃ (β : Type) (T : MultiTier β Empty) (g : β),
      MultiTierOk T ∧ Cwit ∈ T.tauE g :=
  (satisfiable_iff_hfrag_cert Cwit Cwit_hfrag).mp Cwit_sat

end HFragWitness

/-- **∀-FREE SATISFIABILITY ⟺ A MULTI-TIER CERTIFICATE.**  Both
    directions now kernel-checked: `←` is the certified soundness
    pipeline (`multiTier_sound`), `→` is the extraction
    (`extract_allfree`, the horizontal recursion with coverage).  So for
    the ∀-free fragment a concept is satisfiable IFF it admits a valid
    multi-tier certificate.  NB: this is a CERTIFICATE CHARACTERIZATION,
    not a certified finite-model property — the certificate is built
    from a finite node set (and with `κ = Empty` the unfolded model is
    in fact finite), but the theorem quantifies `β` as an ARBITRARY
    `Type` with no `Fintype`/cardinality claim.  Certifying finiteness
    (a `Fintype β` + `K(C₀)` bound) is the remaining step, and it is
    exactly what yields Decidability via `decidableSat_of_codes`. -/
theorem satisfiable_iff_allfree_cert (C0 : Concept) (haf : AllFree C0) :
    Satisfiable C0 ↔
      ∃ (β : Type) (T : MultiTier β Empty) (g : β),
        MultiTierOk T ∧ C0 ∈ T.tauE g := by
  constructor
  · exact extract_allfree C0 haf
  · rintro ⟨β, T, g, hok, hC0⟩
    exact multiTier_sound T hok (Sum.inl g) C0 hC0

/-! ## Round E3h (2026-07-24): the vertical kernel, β = Empty — certified

The persistent-vertical milestone of ASSEMBLY_DESIGN.md §§17–19: a single
ascending `PP`-kernel with NO externals is a full `MultiTierOk`.  The key
(correcting §18): the chain `persistPP_chain` builds CARRIES the `∃PP.G`
argument `G` at every rung (the discarded `_` in `persistPP_productive`),
so a chain-carried `∃PP.G` routes to `k_ex` disjunct 2 — the CHAIN, not
an external.  Given only `hG0 : G ∈ phase 0` and `hdemands` (every phase
existential is the chain demand `∃PP.G`, or an `∃EQ`), `vkernel` is
valid: `∀PP`-firing via `segment_kk_pp`, `∃EQ` in-phase via `seg_ex_eq`,
externals/pool vacuous.  The reusable kernel-certificate builder for the
externals-free case — the summit's mixing (multiple `∃PP` demands ⟹
externals ⟹ the `e_ex`/`hserve` recursion) remains open. -/

section VerticalKernel

variable {α : Type} {I : Interp α}

/-- The β = Empty, κ = Unit vertical kernel: one ascending `PP`-chain,
    phases = the segment's model types, kernel representative = `c i`. -/
noncomputable def vkernel (I : Interp α) (C0 : Concept) (c : Nat → α)
    (i p : Nat) : MultiTier Empty Unit where
  E := fun e f => I.rho e.elim f.elim
  K := fun _ f => I.rho (c i) f.elim
  Q := fun _ _ => I.rho (c i) (c i)
  up := fun _ => true
  tauE := fun e => e.elim
  p := fun _ => p
  phase := fun _ a => mty C0 I (c (i + a))

/-- THE VERTICAL KERNEL IS VALID: an ascending model chain with a
    type-recurrent segment, whose phase existentials are all the single
    chain demand `∃PP.G` (served by the chain) or `∃EQ` (served
    in-phase), yields a full `MultiTierOk` with NO externals — genuine
    `∀PP`-firing, cyclic phases, `∃PP` fulfilled by the chain itself. -/
theorem vkernel_ok (hI : RCC5Interp I) (C0 G : Concept) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n))
    (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    {i p : Nat} (hp : 0 < p)
    (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    (hG0 : G ∈ mty C0 I (c i))
    (hdemands : ∀ a r D, Concept.ex r D ∈ mty C0 I (c (i + a)) →
      (r = pp ∧ D = G) ∨ r = eq) :
    MultiTierOk (vkernel I C0 c i p) := by
  have hinj : ∀ v w : Empty ⊕ Unit,
      Sum.elim (fun e : Empty => e.elim) (fun _ : Unit => c i) v
        = Sum.elim (fun e : Empty => e.elim) (fun _ : Unit => c i) w → v = w := by
    rintro (e | ⟨⟩) (f | ⟨⟩) _
    · exact e.elim
    · exact e.elim
    · exact f.elim
    · rfl
  refine
    { hp := fun _ => hp
      frame_q := readoff_qnet_frame hI (fun e : Empty => e.elim)
        (fun _ : Unit => c i) (fun e => e.elim) (fun _ => hdom i) hinj
      e_clash := fun e => e.elim
      e_nobot := fun e => e.elim
      e_and := fun e => e.elim
      e_or := fun e => e.elim
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := fun e => e.elim
      ek_all := fun e => e.elim
      ke_all := fun _ _ _ _ _ _ f => f.elim
      kk_pp := fun _ _ ha E hE b hb =>
        segment_kk_pp hI hdom hstep hty ha hE b hb
      kk_ppi := fun _ _ ha E hE b hb =>
        segment_kk_ppi hI hdom hstep hty ha hE b hb
      kk_eq := fun _ _ _ E hE => seg_eq hI hdom hE
      kq_all := fun k k' hne => absurd rfl hne
      e_ex := fun e => e.elim
      k_ex := ?_ }
  intro _ a _ r D hmem
  rcases hdemands a r D hmem with ⟨rfl, rfl⟩ | rfl
  · exact Or.inr (Or.inl ⟨rfl, 0, hp, hG0⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, seg_ex_eq hI hdom hmem⟩))

/-- THE SELF-CARRYING VERTICAL KERNEL (linear-nested `∃PP`): if every
    phase's `∃PP.D` demand has its argument `D` carried by SOME phase of
    the chain (self-carrying), the kernel is valid — the chain serves
    EACH nested demand at the phase carrying its argument, `∃EQ`
    in-phase.  Generalises `vkernel_ok` (single fixed `G`) to a CASCADE
    of arguments (the "one chain = one kernel" case of cross-linked
    `∃PP`).  β = Empty, no `e_ex` recursion. -/
theorem vkernelG_ok (hI : RCC5Interp I) (C0 : Concept) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n))
    (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    {i p : Nat} (hp : 0 < p)
    (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    (hdemands : ∀ a r D, Concept.ex r D ∈ mty C0 I (c (i + a)) →
      (r = pp ∧ ∃ b, b < p ∧ D ∈ mty C0 I (c (i + b))) ∨ r = eq) :
    MultiTierOk (vkernel I C0 c i p) := by
  have hinj : ∀ v w : Empty ⊕ Unit,
      Sum.elim (fun e : Empty => e.elim) (fun _ : Unit => c i) v
        = Sum.elim (fun e : Empty => e.elim) (fun _ : Unit => c i) w → v = w := by
    rintro (e | ⟨⟩) (f | ⟨⟩) _
    · exact e.elim
    · exact e.elim
    · exact f.elim
    · rfl
  refine
    { hp := fun _ => hp
      frame_q := readoff_qnet_frame hI (fun e : Empty => e.elim)
        (fun _ : Unit => c i) (fun e => e.elim) (fun _ => hdom i) hinj
      e_clash := fun e => e.elim
      e_nobot := fun e => e.elim
      e_and := fun e => e.elim
      e_or := fun e => e.elim
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := fun e => e.elim
      ek_all := fun e => e.elim
      ke_all := fun _ _ _ _ _ _ f => f.elim
      kk_pp := fun _ _ ha E hE b hb =>
        segment_kk_pp hI hdom hstep hty ha hE b hb
      kk_ppi := fun _ _ ha E hE b hb =>
        segment_kk_ppi hI hdom hstep hty ha hE b hb
      kk_eq := fun _ _ _ E hE => seg_eq hI hdom hE
      kq_all := fun k k' hne => absurd rfl hne
      e_ex := fun e => e.elim
      k_ex := ?_ }
  intro _ a _ r D hmem
  rcases hdemands a r D hmem with ⟨rfl, b, hb, hDb⟩ | rfl
  · exact Or.inr (Or.inl ⟨rfl, b, hb, hDb⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, seg_ex_eq hI hdom hmem⟩))

/-! ### Round E3h′ (2026-07-24): the FIRST `e_ex` discharge — a root
external below the kernel

The vertical kernel with ONE external `x0` sitting BELOW the chain
(`x0 PP c i`, so `x0 PP c m` for the whole segment).  This is the first
`MultiTierOk` with a genuine external whose `e_ex` residual is
DISCHARGED — not vacuously (β ≠ Empty) — and it carries `C0` at that
external node (the model root, where `C0` actually holds).  The move:
`x0`'s own `∃PP.G` demand routes DOWN-UP into the kernel (`e_ex`
disjunct 2, `conv (K () x0) = pp` since `x0 PP c i`, `G ∈ phase 0`);
its `∃EQ` demands are self-served.  The external's `∀`-obligations fire
by `mty_all` through the constant `pp`-row `x0 → segment`.  This is the
first stone of the mixing: an external served by an existing kernel.
(The open summit is externals that need NEW kernels — the multi-cluster
recursion — where `x0`'s `∃PP` argument is off the one chain.) -/

/-- The vertical kernel with a single below-external `x0` (the root):
    `β = Unit`.  Every value read off the model. -/
noncomputable def vkernel1 (I : Interp α) (C0 : Concept) (c : Nat → α)
    (x0 : α) (i p : Nat) : MultiTier Unit Unit where
  E := fun _ _ => I.rho x0 x0
  K := fun _ _ => I.rho (c i) x0
  Q := fun _ _ => I.rho (c i) (c i)
  up := fun _ => true
  tauE := fun _ => mty C0 I x0
  p := fun _ => p
  phase := fun _ a => mty C0 I (c (i + a))

/-- THE ROOT-EXTERNAL KERNEL IS VALID: with `x0 PP` the whole segment
    (`hx0pp`) and `x0`'s existentials the single chain demand `∃PP.G` or
    `∃EQ` (`hx0dem`), the one-external kernel is a full `MultiTierOk` —
    `x0`'s `e_ex` discharged INTO the kernel, `∀`-firing via the
    constant `pp`-row. -/
theorem vkernel1_ok (hI : RCC5Interp I) (C0 G : Concept) (c : Nat → α)
    (x0 : α) (hx0dom : I.dom x0)
    (hdom : ∀ n, I.dom (c n))
    (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    {i p : Nat} (hp : 0 < p)
    (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    (hG0 : G ∈ mty C0 I (c i))
    (hx0pp : ∀ a, I.rho x0 (c (i + a)) = pp)
    (hdemands : ∀ a r D, Concept.ex r D ∈ mty C0 I (c (i + a)) →
      (r = pp ∧ D = G) ∨ r = eq)
    (hx0dem : ∀ r D, Concept.ex r D ∈ mty C0 I x0 →
      (r = pp ∧ D = G) ∨ r = eq) :
    MultiTierOk (vkernel1 I C0 c x0 i p) := by
  -- the kernel base sits ABOVE the root: `c i → x0 = PPI`
  have hKppi : I.rho (c i) x0 = ppi := by
    have h0 := hx0pp 0
    rw [Nat.add_zero] at h0
    rw [hI.conv_ x0 (c i) hx0dom (hdom i), h0]; rfl
  have hx0ne : x0 ≠ c i := by
    intro h
    have h0 := hx0pp 0
    rw [Nat.add_zero, h, hI.refl_eq (c i) (hdom i)] at h0
    exact absurd h0 (by decide)
  have hEK : ∀ a, I.rho (c (i + a)) x0 = ppi := by
    intro a
    rw [hI.conv_ x0 (c (i + a)) hx0dom (hdom (i + a)), hx0pp a]; rfl
  have hinj : ∀ v w : Unit ⊕ Unit,
      Sum.elim (fun _ : Unit => x0) (fun _ : Unit => c i) v
        = Sum.elim (fun _ : Unit => x0) (fun _ : Unit => c i) w → v = w := by
    rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) h
    · rfl
    · exact absurd h hx0ne
    · exact absurd h.symm hx0ne
    · rfl
  refine
    { hp := fun _ => hp
      frame_q := readoff_qnet_frame hI (fun _ : Unit => x0)
        (fun _ : Unit => c i) (fun _ => hx0dom) (fun _ => hdom i) hinj
      e_clash := fun _ _ h => mty_clash h
      e_nobot := fun _ => mty_nobot
      e_and := fun _ _ _ h => mty_and h
      e_or := fun _ _ _ h => mty_or h
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := fun _ _ _ _ hmem hEr => mty_all hmem hx0dom hEr
      ek_all := ?_
      ke_all := ?_
      kk_pp := fun _ _ ha E hE b hb =>
        segment_kk_pp hI hdom hstep hty ha hE b hb
      kk_ppi := fun _ _ ha E hE b hb =>
        segment_kk_ppi hI hdom hstep hty ha hE b hb
      kk_eq := fun _ _ _ E hE => seg_eq hI hdom hE
      kq_all := fun k k' hne => absurd rfl hne
      e_ex := ?_
      k_ex := ?_ }
  · -- ek_all: x0's `∀` fires into every phase through the constant `pp`-row
    intro _ r X hmem k hr a _
    have hrpp : r = pp := by
      rw [← hr]; show conv (I.rho (c i) x0) = pp; rw [hKppi]; rfl
    subst hrpp
    exact mty_all hmem (hdom (i + a)) (hx0pp a)
  · -- ke_all: a phase's `∀` fires at x0 through the `ppi`-row
    intro k a _ r X hmem f hr
    have hrppi : r = ppi := by rw [← hr]; exact hKppi
    subst hrppi
    exact mty_all hmem hx0dom (hEK a)
  · -- e_ex: x0's `∃PP.G` routes INTO the kernel; `∃EQ` self-serves
    intro _ r D hmem
    rcases hx0dem r D hmem with ⟨rfl, rfl⟩ | rfl
    · refine Or.inr ⟨(), ?_, 0, hp, hG0⟩
      show conv (I.rho (c i) x0) = pp; rw [hKppi]; rfl
    · refine Or.inl ⟨(), hI.refl_eq x0 hx0dom, ?_⟩
      obtain ⟨y, hy, hyr, hyD⟩ := mty_ex hmem
      rwa [hI.eq_id x0 y hx0dom hy hyr]
  · -- k_ex: as the externals-free kernel (chain / in-phase)
    intro _ a _ r D hmem
    rcases hdemands a r D hmem with ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, 0, hp, hG0⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, seg_ex_eq hI hdom hmem⟩))

/-- THE SELF-CARRYING KERNEL IS VALID: like `vkernel1_ok`, but each `∃PP.D`
    demand (of `x0` or of a phase) is served by WHATEVER phase `b` carries
    `D` (`hdemands`/`hx0dem` give `∃ b, D ∈ phase b`), not a single fixed
    `G`.  This is the summit's routing mechanism, proved here where the
    concept FORCES the co-carrying.  Everything but the two `∃`-routing
    disjuncts is verbatim `vkernel1_ok`. -/
theorem vkernel1G_ok (hI : RCC5Interp I) (C0 : Concept) (c : Nat → α)
    (x0 : α) (hx0dom : I.dom x0)
    (hdom : ∀ n, I.dom (c n))
    (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    {i p : Nat} (hp : 0 < p)
    (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    (hx0pp : ∀ a, I.rho x0 (c (i + a)) = pp)
    (hdemands : ∀ a r D, Concept.ex r D ∈ mty C0 I (c (i + a)) →
      (r = pp ∧ ∃ b, b < p ∧ D ∈ mty C0 I (c (i + b))) ∨ r = eq)
    (hx0dem : ∀ r D, Concept.ex r D ∈ mty C0 I x0 →
      (r = pp ∧ ∃ b, b < p ∧ D ∈ mty C0 I (c (i + b))) ∨ r = eq) :
    MultiTierOk (vkernel1 I C0 c x0 i p) := by
  have hKppi : I.rho (c i) x0 = ppi := by
    have h0 := hx0pp 0
    rw [Nat.add_zero] at h0
    rw [hI.conv_ x0 (c i) hx0dom (hdom i), h0]; rfl
  have hx0ne : x0 ≠ c i := by
    intro h
    have h0 := hx0pp 0
    rw [Nat.add_zero, h, hI.refl_eq (c i) (hdom i)] at h0
    exact absurd h0 (by decide)
  have hEK : ∀ a, I.rho (c (i + a)) x0 = ppi := by
    intro a
    rw [hI.conv_ x0 (c (i + a)) hx0dom (hdom (i + a)), hx0pp a]; rfl
  have hinj : ∀ v w : Unit ⊕ Unit,
      Sum.elim (fun _ : Unit => x0) (fun _ : Unit => c i) v
        = Sum.elim (fun _ : Unit => x0) (fun _ : Unit => c i) w → v = w := by
    rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) h
    · rfl
    · exact absurd h hx0ne
    · exact absurd h.symm hx0ne
    · rfl
  refine
    { hp := fun _ => hp
      frame_q := readoff_qnet_frame hI (fun _ : Unit => x0)
        (fun _ : Unit => c i) (fun _ => hx0dom) (fun _ => hdom i) hinj
      e_clash := fun _ _ h => mty_clash h
      e_nobot := fun _ => mty_nobot
      e_and := fun _ _ _ h => mty_and h
      e_or := fun _ _ _ h => mty_or h
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := fun _ _ _ _ hmem hEr => mty_all hmem hx0dom hEr
      ek_all := ?_
      ke_all := ?_
      kk_pp := fun _ _ ha E hE b hb =>
        segment_kk_pp hI hdom hstep hty ha hE b hb
      kk_ppi := fun _ _ ha E hE b hb =>
        segment_kk_ppi hI hdom hstep hty ha hE b hb
      kk_eq := fun _ _ _ E hE => seg_eq hI hdom hE
      kq_all := fun k k' hne => absurd rfl hne
      e_ex := ?_
      k_ex := ?_ }
  · intro _ r X hmem k hr a _
    have hrpp : r = pp := by
      rw [← hr]; show conv (I.rho (c i) x0) = pp; rw [hKppi]; rfl
    subst hrpp
    exact mty_all hmem (hdom (i + a)) (hx0pp a)
  · intro k a _ r X hmem f hr
    have hrppi : r = ppi := by rw [← hr]; exact hKppi
    subst hrppi
    exact mty_all hmem hx0dom (hEK a)
  · intro _ r D hmem
    rcases hx0dem r D hmem with ⟨rfl, b, hb, hDb⟩ | rfl
    · refine Or.inr ⟨(), ?_, b, hb, hDb⟩
      show conv (I.rho (c i) x0) = pp; rw [hKppi]; rfl
    · refine Or.inl ⟨(), hI.refl_eq x0 hx0dom, ?_⟩
      obtain ⟨y, hy, hyr, hyD⟩ := mty_ex hmem
      rwa [hI.eq_id x0 y hx0dom hy hyr]
  · intro _ a _ r D hmem
    rcases hdemands a r D hmem with ⟨rfl, b, hb, hDb⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, b, hb, hDb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, seg_ex_eq hI hdom hmem⟩))

/-- The DESCENDING one-external kernel (`up = false`): the root `x0` sits
    ABOVE the chain (`x0 ⊃ dᵢ`), so `K` reads `pp` and the chain serves
    `∃PPI` (`cdir false = ppi`).  Mirror of `vkernel1`. -/
noncomputable def vkernel1I (I : Interp α) (C0 : Concept) (d : Nat → α)
    (x0 : α) (i p : Nat) : MultiTier Unit Unit where
  E := fun _ _ => I.rho x0 x0
  K := fun _ _ => I.rho (d i) x0
  Q := fun _ _ => I.rho (d i) (d i)
  up := fun _ => false
  tauE := fun _ => mty C0 I x0
  p := fun _ => p
  phase := fun _ a => mty C0 I (d (i + a))

/-- THE DESCENDING SELF-CARRYING KERNEL IS VALID: mirror of `vkernel1G_ok`
    with `up := false`, the descending segment lemmas (`dsegment_kk_pp`/
    `dsegment_kk_ppi`), and the geometry flipped (`x0 ⊃ dᵢ`, `K = pp`,
    chain serves `∃PPI`). -/
theorem vkernel1GI_ok (hI : RCC5Interp I) (C0 : Concept) (d : Nat → α)
    (x0 : α) (hx0dom : I.dom x0)
    (hdom : ∀ n, I.dom (d n))
    (hstep : ∀ n, I.rho (d n) (d (n + 1)) = ppi)
    {i p : Nat} (hp : 0 < p)
    (hty : mty C0 I (d i) = mty C0 I (d (i + p)))
    (hx0ppi : ∀ a, I.rho x0 (d (i + a)) = ppi)
    (hdemands : ∀ a r D, Concept.ex r D ∈ mty C0 I (d (i + a)) →
      (r = ppi ∧ ∃ b, b < p ∧ D ∈ mty C0 I (d (i + b))) ∨ r = eq)
    (hx0dem : ∀ r D, Concept.ex r D ∈ mty C0 I x0 →
      (r = ppi ∧ ∃ b, b < p ∧ D ∈ mty C0 I (d (i + b))) ∨ r = eq) :
    MultiTierOk (vkernel1I I C0 d x0 i p) := by
  have hKpp : I.rho (d i) x0 = pp := by
    have h0 := hx0ppi 0
    rw [Nat.add_zero] at h0
    rw [hI.conv_ x0 (d i) hx0dom (hdom i), h0]; rfl
  have hx0ne : x0 ≠ d i := by
    intro h
    have h0 := hx0ppi 0
    rw [Nat.add_zero, h, hI.refl_eq (d i) (hdom i)] at h0
    exact absurd h0 (by decide)
  have hEK : ∀ a, I.rho (d (i + a)) x0 = pp := by
    intro a
    rw [hI.conv_ x0 (d (i + a)) hx0dom (hdom (i + a)), hx0ppi a]; rfl
  have hinj : ∀ v w : Unit ⊕ Unit,
      Sum.elim (fun _ : Unit => x0) (fun _ : Unit => d i) v
        = Sum.elim (fun _ : Unit => x0) (fun _ : Unit => d i) w → v = w := by
    rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) h
    · rfl
    · exact absurd h hx0ne
    · exact absurd h.symm hx0ne
    · rfl
  refine
    { hp := fun _ => hp
      frame_q := readoff_qnet_frame hI (fun _ : Unit => x0)
        (fun _ : Unit => d i) (fun _ => hx0dom) (fun _ => hdom i) hinj
      e_clash := fun _ _ h => mty_clash h
      e_nobot := fun _ => mty_nobot
      e_and := fun _ _ _ h => mty_and h
      e_or := fun _ _ _ h => mty_or h
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := fun _ _ _ _ hmem hEr => mty_all hmem hx0dom hEr
      ek_all := ?_
      ke_all := ?_
      kk_pp := fun _ _ ha E hE b hb =>
        dsegment_kk_pp hI hdom hstep hty ha hE b hb
      kk_ppi := fun _ _ ha E hE b hb =>
        dsegment_kk_ppi hI hdom hstep hty ha hE b hb
      kk_eq := fun _ a _ E hE =>
        mty_all hE (hdom (i + a)) (hI.refl_eq (d (i + a)) (hdom (i + a)))
      kq_all := fun k k' hne => absurd rfl hne
      e_ex := ?_
      k_ex := ?_ }
  · intro _ r X hmem k hr a _
    have hrppi : r = ppi := by
      rw [← hr]; show conv (I.rho (d i) x0) = ppi; rw [hKpp]; rfl
    subst hrppi
    exact mty_all hmem (hdom (i + a)) (hx0ppi a)
  · intro k a _ r X hmem f hr
    have hrpp : r = pp := by rw [← hr]; exact hKpp
    subst hrpp
    exact mty_all hmem hx0dom (hEK a)
  · intro _ r D hmem
    rcases hx0dem r D hmem with ⟨rfl, b, hb, hDb⟩ | rfl
    · refine Or.inr ⟨(), ?_, b, hb, hDb⟩
      show conv (I.rho (d i) x0) = ppi; rw [hKpp]; rfl
    · refine Or.inl ⟨(), hI.refl_eq x0 hx0dom, ?_⟩
      obtain ⟨y, hy, hyr, hyD⟩ := mty_ex hmem
      rwa [hI.eq_id x0 y hx0dom hy hyr]
  · intro _ a _ r D hmem
    rcases hdemands a r D hmem with ⟨rfl, b, hb, hDb⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, b, hb, hDb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, seg_ex_eq hI hdom hmem⟩))

/-! ### Round E3h″ (2026-07-24): the first MULTI-kernel certificate

`vkernel2`/`vkernel2_ok`: TWO ascending `PP`-kernels (`κ = Bool`,
`β = Empty`), each serving its own `∃PP` via its own chain.  The new
content over the single-kernel case is **`kq_all`** — a `∀`-obligation
in one kernel's phase fires along the cross-kernel `Q`-edge into the
OTHER kernel's phases — discharged by `mty_all` through the cross-row
constancy `hrectQ` (the rectangle condition, here supplied as a
hypothesis and, on the witness, trivial because the cross-value is a
constant `DR`).  This is the two-kernel FRAME (`readoff_qnet_frame` over
two bases) plus genuine cross-kernel universal propagation — the shape
`cbothMT` hand-built, now a GENERAL lemma from two model chains.  (Still
no cross-kernel `∃`: each kernel is `∃`-self-contained; a demand that
crosses to the other kernel — `k_ex` disjunct 4 — is the next step, and
the summit adds externals that spawn NEW kernels.) -/

/-- **`mtk` propagation AT THE SAME BUDGET**: a `∀r.cc` at budget `b` lands its
    argument `cc` at the SAME budget `b` in any `r`-neighbour — not `b-1`,
    because `cc` is one modal level shallower than `∀r.cc`, so it fits the full
    budget.  This is exactly what lets a kernel's `∀`-obligation cross to a
    same-budget node (the attaching node and the tower phases), which is the
    key to the `mtk`-truncated merge's `ek_all`/`ke_all`. -/
theorem all_into {C0 : Concept} {x y : α} {b : Nat} {r : Atom} {cc : Concept}
    (hmem : Concept.all r cc ∈ mtk C0 I x b) (hr : I.rho x y = r) (hy : I.dom y) :
    cc ∈ mtk C0 I y b := by
  obtain ⟨hmty, hb⟩ := mem_mtk.mp hmem
  refine mem_mtk.mpr ⟨mty_all hmty hy hr, ?_⟩
  have hlt : mdepth cc + 1 ≤ b := hb
  omega

open Classical in
/-- **THE PO-DEFAULT KERNEL'S `ek_all`** (the wp89 depth-seam fix, formalized).
    An external `e`'s `∀r.cc` fires into the kernel only through
    `conv(K e) = if e=v0 then pp else po`.  `PO` edges are VACUOUS (no `∀PO` in
    the `∀PO`-free closure); the one `PP` edge — from the attaching node `v0`,
    which sits BELOW the tower (`ρ(g v0, phase) = pp`) — lands `cc` at the
    phase's SAME budget via `all_into`.  So the phases stay `mtk`-truncated at
    `v0`'s budget with no over-truncation. -/
theorem podefault_ek {C0 : Concept} (hpofree : POFree C0) {β : Type}
    (g : β → α) (v0 : β) (bud : β → Nat)
    {phasept : α} (hpp : I.rho (g v0) phasept = pp) (hpdom : I.dom phasept)
    {e : β} {r : Atom} {cc : Concept}
    (hmem : Concept.all r cc ∈ mtk C0 I (g e) (bud e))
    (hconv : (if e = v0 then pp else po) = r) :
    cc ∈ mtk C0 I phasept (bud v0) := by
  by_cases he : e = v0
  · subst he; rw [if_pos rfl] at hconv; subst hconv
    exact all_into hmem hpp hpdom
  · rw [if_neg he] at hconv; subst hconv
    exact absurd (mem_mtk.mp hmem).1 (mty_no_all_po hpofree)

open Classical in
/-- **THE PO-DEFAULT KERNEL'S `ke_all`** (the wp89 depth-seam fix, formalized).
    A phase's `∀r.cc` fires at external `f` only through
    `K f = if f=v0 then ppi else po`.  `PO` edges VACUOUS (no `∀PO`); the one
    `PPI` edge — to `v0`, above which the phase sits (`ρ(phase, g v0) = ppi`) —
    lands `cc` at `v0`'s SAME budget via `all_into`.  With PO-default `K` the
    depth seam never bites: no forced far edge, so no deep universal reaches an
    under-budget external. -/
theorem podefault_ke {C0 : Concept} (hpofree : POFree C0) {β : Type}
    (g : β → α) (v0 : β) (bud : β → Nat) (hv0dom : I.dom (g v0))
    {x : α} (hppi : I.rho x (g v0) = ppi)
    {r : Atom} {cc : Concept} (hmem : Concept.all r cc ∈ mtk C0 I x (bud v0))
    {f : β} (hK : (if f = v0 then ppi else po) = r) :
    cc ∈ mtk C0 I (g f) (bud f) := by
  by_cases hf : f = v0
  · subst hf; rw [if_pos rfl] at hK; subst hK
    exact all_into hmem hppi hv0dom
  · rw [if_neg hf] at hK; subst hK
    exact absurd (mem_mtk.mp hmem).1 (mty_no_all_po hpofree)

open Classical in
/-- **THE PO-DEFAULT-WITH-DR-CHILDREN `ke_all`** (the forcing-completion wiring:
    the `ke_all` for the `po_dr_multi_kernel_frame` `K`-edge).  A phase's `∀r.cc`
    fires at external `f` through `K f = if f = v0 then ppi else if kdr f then dr
    else po`.  The `PPI` edge (attach) lands via `all_into` (phase above attach);
    the `DR` edge (a child) lands via `all_into` too — a `∀DR.cc` at the phase
    reaches the child `f`, which is a REAL `DR`-successor of the phase (`hdr`,
    the child `DR` to EVERY phase, matching budget); `PO` edges are vacuous
    (`∀PO`-free).  This is what serves phase-`∃DR`: the depth seam is avoided
    because the child budget need only satisfy `bud v0 ≤ bud f + 1` — a `∀DR.cc`
    at a phase of budget `bud v0` has `mdepth cc ≤ bud v0 - 1`, so it fits a child
    at budget `bud v0 - 1` (DECREASING — this is what lets a general DR-child
    recursion TERMINATE, not just the leaf-child witness where `bud f = bud v0`). -/
theorem podefault_ke_dr {C0 : Concept} (hpofree : POFree C0) {β : Type}
    (g : β → α) (hgdom : ∀ e, I.dom (g e)) (v0 : β) (kdr : β → Bool) (bud : β → Nat)
    (hv0dom : I.dom (g v0)) {x : α} (hppi : I.rho x (g v0) = ppi)
    (hdr : ∀ f, kdr f = true → I.rho x (g f) = dr ∧ bud v0 ≤ bud f + 1)
    {r : Atom} {cc : Concept} (hmem : Concept.all r cc ∈ mtk C0 I x (bud v0))
    {f : β} (hK : (if f = v0 then ppi else if kdr f then dr else po) = r) :
    cc ∈ mtk C0 I (g f) (bud f) := by
  by_cases hf : f = v0
  · subst hf; rw [if_pos rfl] at hK; subst hK
    exact all_into hmem hppi hv0dom
  · rw [if_neg hf] at hK
    by_cases hc : kdr f = true
    · rw [if_pos hc] at hK; subst hK
      obtain ⟨hdrf, hbudf⟩ := hdr f hc
      have h1 : cc ∈ mtk C0 I (g f) (bud v0) := all_into hmem hdrf (hgdom f)
      refine mem_mtk.mpr ⟨(mem_mtk.mp h1).1, ?_⟩
      have hmd : mdepth cc + 1 ≤ bud v0 := (mem_mtk.mp hmem).2
      omega
    · rw [if_neg hc] at hK; subst hK
      exact absurd (mem_mtk.mp hmem).1 (mty_no_all_po hpofree)

open Classical in
/-- **THE DR-CHILDREN `ek_all`** (the dual of `podefault_ke_dr`).  An external
    `e`'s `∀r.cc` fires into kernel `k`'s phases through `conv(K k e) = if e = v0
    then pp else if kdr e then dr else po`.  The `PP` edge (attach, `e = v0`)
    lands via `all_into` (attach below phase); the `DR` edge (a child external)
    lands via `all_into` too — a `∀DR.cc` at a child reaches the phase (a real
    `DR`-neighbour, `hdr`), budget `bud e ≤ bud v0 + 1` (the child may sit one
    budget BELOW — decreasing); `PO` vacuous.  Needed only if a DR-child external
    itself carries a `∀DR`. -/
theorem podefault_ek_dr {C0 : Concept} (hpofree : POFree C0) {β : Type}
    (g : β → α) (v0 : β) (kdr : β → Bool) (bud : β → Nat)
    {phasept : α} (hpp : I.rho (g v0) phasept = pp) (hpdom : I.dom phasept)
    (hdr : ∀ e, kdr e = true → I.rho (g e) phasept = dr ∧ bud e ≤ bud v0 + 1)
    {e : β} {r : Atom} {cc : Concept}
    (hmem : Concept.all r cc ∈ mtk C0 I (g e) (bud e))
    (hconv : (if e = v0 then pp else if kdr e then dr else po) = r) :
    cc ∈ mtk C0 I phasept (bud v0) := by
  by_cases he : e = v0
  · subst he; rw [if_pos rfl] at hconv; subst hconv
    exact all_into hmem hpp hpdom
  · rw [if_neg he] at hconv
    by_cases hc : kdr e = true
    · rw [if_pos hc] at hconv; subst hconv
      obtain ⟨hdre, hbude⟩ := hdr e hc
      have h1 : cc ∈ mtk C0 I phasept (bud e) := all_into hmem hdre hpdom
      refine mem_mtk.mpr ⟨(mem_mtk.mp h1).1, ?_⟩
      have hmd : mdepth cc + 1 ≤ bud e := (mem_mtk.mp hmem).2
      omega
    · rw [if_neg hc] at hconv; subst hconv
      exact absurd (mem_mtk.mp hmem).1 (mty_no_all_po hpofree)

/-- `kk_pp` on `mtk`-truncated phases: lift to `mty`, apply `segment_kk_pp`,
    restrict back (the argument fits the same budget, one level shallower). -/
theorem mtk_kk_pp (hI : RCC5Interp I) {C0 : Concept} (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    {i p : Nat} (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    {a : Nat} (ha : a < p) (bv : Nat) {cc : Concept}
    (hmem : Concept.all pp cc ∈ mtk C0 I (c (i + a)) bv)
    {b : Nat} (hb : b < p) : cc ∈ mtk C0 I (c (i + b)) bv := by
  obtain ⟨hmty, hbd⟩ := mem_mtk.mp hmem
  refine mem_mtk.mpr ⟨segment_kk_pp hI hdom hstep hty ha hmty b hb, ?_⟩
  have hlt : mdepth cc + 1 ≤ bv := hbd; omega

/-- `kk_ppi` on `mtk`-truncated phases (mirror of `mtk_kk_pp`). -/
theorem mtk_kk_ppi (hI : RCC5Interp I) {C0 : Concept} (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    {i p : Nat} (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    {a : Nat} (ha : a < p) (bv : Nat) {cc : Concept}
    (hmem : Concept.all ppi cc ∈ mtk C0 I (c (i + a)) bv)
    {b : Nat} (hb : b < p) : cc ∈ mtk C0 I (c (i + b)) bv := by
  obtain ⟨hmty, hbd⟩ := mem_mtk.mp hmem
  refine mem_mtk.mpr ⟨segment_kk_ppi hI hdom hstep hty ha hmty b hb, ?_⟩
  have hlt : mdepth cc + 1 ≤ bv := hbd; omega

open Classical in
/-- **THE PO-DEFAULT SINGLE-KERNEL CERTIFICATE** (`mtk`-truncated).  A `symDrPo`
    external skeleton (labels `mtk(g e)(bud e)`) plus one ascending kernel
    attached at `v0`: `K` is `PPI` to `v0`, `PO` elsewhere (the wp90 policy);
    phases `mtk`-truncated at `v0`'s budget. -/
noncomputable def mtkKernel (I : Interp α) (C0 : Concept) {β : Type}
    (g : β → α) (bud : β → Nat) (dadj : β → β → Bool) (v0 : β)
    (c : Nat → α) (i p : Nat) : MultiTier β Unit where
  E e f := if e = f then eq else if dadj e f then dr else po
  K _ e := if e = v0 then ppi else po
  Q _ _ := eq
  up _ := true
  tauE e := mtk C0 I (g e) (bud e)
  p _ := p
  phase _ a := mtk C0 I (c (i + a)) (bud v0)

open Classical in
/-- **THE PO-DEFAULT SINGLE-KERNEL MERGE IS VALID.**  Combines the certified
    pieces: `frame_q` = `po_default_asc_frame`; `ek_all`/`ke_all` = the wp89
    fix (`podefault_ek`/`podefault_ke`, the depth seam avoided by PO-default);
    `kk_*` = `mtk_kk_pp/ppi` + `all_into`; propositional clauses from `mtk`.
    The horizontal `ee_all` and the demand routing `e_ex`/`k_ex` are supplied
    as hypotheses (what the `mtk`-with-kernels node construction provides — the
    same `mtHF` external handling, now with an `∃PP` node routed to the
    kernel). -/
theorem mtkKernel_ok (hI : RCC5Interp I) {C0 : Concept} (hpofree : POFree C0)
    {β : Type} (g : β → α) (hgdom : ∀ e, I.dom (g e)) (bud : β → Nat)
    (dadj : β → β → Bool) (hsym : ∀ e f, dadj e f = dadj f e) (v0 : β)
    (c : Nat → α) (hdom : ∀ n, I.dom (c n))
    (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    (i p : Nat) (hp : 0 < p)
    (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    (hv0pp : ∀ a, I.rho (g v0) (c (i + a)) = pp)
    (hee : ∀ e f r cc, Concept.all r cc ∈ mtk C0 I (g e) (bud e) →
      (if e = f then eq else if dadj e f then dr else po) = r →
      cc ∈ mtk C0 I (g f) (bud f))
    (he_ex : ∀ e r D, Concept.ex r D ∈ mtk C0 I (g e) (bud e) →
      (∃ f, (if e = f then eq else if dadj e f then dr else po) = r ∧
        D ∈ mtk C0 I (g f) (bud f)) ∨
      (conv (if e = v0 then ppi else po) = r ∧
        ∃ a, a < p ∧ D ∈ mtk C0 I (c (i + a)) (bud v0)))
    (hk_ex : ∀ a r D, Concept.ex r D ∈ mtk C0 I (c (i + a)) (bud v0) →
      (∃ f, (if f = v0 then ppi else po) = r ∧ D ∈ mtk C0 I (g f) (bud f)) ∨
      (r = pp ∧ ∃ b, b < p ∧ D ∈ mtk C0 I (c (i + b)) (bud v0)) ∨
      (r = eq ∧ D ∈ mtk C0 I (c (i + a)) (bud v0))) :
    MultiTierOk (mtkKernel I C0 g bud dadj v0 c i p) := by
  have hv0dom : I.dom (g v0) := hgdom v0
  have hppi : ∀ a, I.rho (c (i + a)) (g v0) = ppi := fun a => by
    rw [hI.conv_ (g v0) (c (i + a)) hv0dom (hdom (i + a)), hv0pp a]; rfl
  have hKe : ∀ (k : Unit) (e : β),
      conv ((mtkKernel I C0 g bud dadj v0 c i p).K k e)
        = if e = v0 then pp else po := by
    intro _ e; show conv (if e = v0 then ppi else po) = if e = v0 then pp else po
    by_cases he : e = v0
    · rw [if_pos he, if_pos he]; rfl
    · rw [if_neg he, if_neg he]; rfl
  refine
    { hp := fun _ => hp
      frame_q := po_default_asc_frame dadj hsym v0
      e_clash := fun _ _ h => mtk_clash h
      e_nobot := fun _ => mtk_nobot
      e_and := fun _ _ _ h => mtk_and h
      e_or := fun _ _ _ h => mtk_or h
      k_clash := fun _ _ _ _ h => mtk_clash h
      k_nobot := fun _ _ _ => mtk_nobot
      k_and := fun _ _ _ _ _ h => mtk_and h
      k_or := fun _ _ _ _ _ h => mtk_or h
      ee_all := fun e f r cc hmem hE => hee e f r cc hmem hE
      ek_all := ?_
      ke_all := ?_
      kk_pp := fun _ a ha cc hmem b hb =>
        mtk_kk_pp hI c hdom hstep hty ha (bud v0) hmem hb
      kk_ppi := fun _ a ha cc hmem b hb =>
        mtk_kk_ppi hI c hdom hstep hty ha (bud v0) hmem hb
      kk_eq := fun _ a _ cc hmem =>
        all_into hmem (hI.refl_eq (c (i + a)) (hdom (i + a))) (hdom (i + a))
      kq_all := fun _ _ hne => absurd rfl hne
      e_ex := ?_
      k_ex := ?_ }
  · -- ek_all
    intro e r cc hmem k hr a _
    rw [hKe k e] at hr
    exact podefault_ek hpofree g v0 bud (hv0pp a) (hdom (i + a)) hmem hr
  · -- ke_all
    intro k a _ r cc hmem f hK
    exact podefault_ke hpofree g v0 bud hv0dom (hppi a) hmem hK
  · -- e_ex
    intro e r D hmem
    rcases he_ex e r D hmem with ⟨f, hf, hDf⟩ | ⟨hK, a, ha, hDa⟩
    · exact Or.inl ⟨f, hf, hDf⟩
    · exact Or.inr ⟨(), hK, a, ha, hDa⟩
  · -- k_ex
    intro k a _ r D hmem
    rcases hk_ex a r D hmem with ⟨f, hf, hDf⟩ | ⟨rfl, b, hb, hDb⟩ | ⟨rfl, hD⟩
    · exact Or.inl ⟨f, hf, hDf⟩
    · exact Or.inr (Or.inl ⟨rfl, b, hb, hDb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hD⟩))

/-- **`mtkKernel` is `∀PO`-obligation-free** — the GLUABILITY property.  Both
    `tauE` and `phase` are `mtk` labels (`⊆ mty`), which carry no `∀PO` for a
    `POFree` concept (`mty_no_all_po`, lifted through `mem_mtk`).  So a
    single-kernel `mtkKernel` certificate is `MTNoPo`, hence a valid amalgamand
    for `glueMTOk`: FAMILIES of towers glue all-cross-`PO` into one valid
    certificate.  This is the certificate-level patchwork closing the multi-tower
    general theorem — `∀PO`-freeness makes the cross-tower `PO` edges free. -/
theorem mtkKernel_nopo {C0 : Concept} (hpo : POFree C0) {β : Type}
    (g : β → α) (bud : β → Nat) (dadj : β → β → Bool) (v0 : β)
    (c : Nat → α) (i p : Nat) :
    MTNoPo (mtkKernel I C0 g bud dadj v0 c i p) where
  ext := fun _ _E h => mty_no_all_po hpo (mem_mtk.mp h).1
  ker := fun _ _ _ _E h => mty_no_all_po hpo (mem_mtk.mp h).1

open Classical in
/-- **THE MtkK MULTI-KERNEL CERTIFICATE** (`mtk`-truncated, PO-default).  The
    uniform-`β` multi-tower cert: a `symDrPo` external skeleton + `κ` ascending
    kernels, each `PPI` to its attach point `v0 k`, `PO` elsewhere; cross-kernel
    `Q` = `PO` (`qnet` diagonal `eq`).  Generalises `mtkKernel` (`κ = Unit`) —
    the whole point of the mtk multi-kernel route: with PO-default `Q` the
    kernels coexist in ONE certificate over a shared external skeleton (nested
    towers: a skeleton node's own `∃PP`-tower is another kernel), NOT via
    `glueMTOk` copies. -/
noncomputable def mtkKernels (I : Interp α) (C0 : Concept) {β κ : Type}
    (g : β → α) (bud : β → Nat) (dadj : β → β → Bool) (v0 : κ → β)
    (ck : κ → Nat → α) (ik pk : κ → Nat) : MultiTier β κ where
  E e f := if e = f then eq else if dadj e f then dr else po
  K k e := if e = v0 k then ppi else po
  Q _ _ := po
  up _ := true
  tauE e := mtk C0 I (g e) (bud e)
  p := pk
  phase k a := mtk C0 I (ck k (ik k + a)) (bud (v0 k))

open Classical in
/-- **THE MtkK MULTI-KERNEL MERGE IS VALID.**  Generalises `mtkKernel_ok` to
    `κ` kernels.  `frame_q` = `po_default_multi_frame`; `ek_all`/`ke_all` =
    `podefault_ek`/`podefault_ke` per kernel; `kk_pp`/`kk_ppi` = `mtk_kk_*` on
    each kernel's own chain; `kk_eq`/`all_into`; **`kq_all` VACUOUS** (cross-`Q`
    = `PO`, no `∀PO` in the `mtk` phases — the PO-default insight); `ee_all`,
    `e_ex`, `k_ex` supplied as hypotheses (what the multi-tower node
    construction provides).  `hk_ex` is the single-kernel shape per kernel —
    each phase demand serves via external (`∃PO`/`∃DR`/`∃EQ`) / up-tower
    (`∃PP`) / self (`∃EQ`); no cross-kernel `∃` needed. -/
theorem mtkKernels_ok (hI : RCC5Interp I) {C0 : Concept} (hpofree : POFree C0)
    {β κ : Type} (g : β → α) (hgdom : ∀ e, I.dom (g e)) (bud : β → Nat)
    (dadj : β → β → Bool) (hsym : ∀ e f, dadj e f = dadj f e) (v0 : κ → β)
    (ck : κ → Nat → α) (hdom : ∀ k n, I.dom (ck k n))
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = pp)
    (ik pk : κ → Nat) (hp : ∀ k, 0 < pk k)
    (hty : ∀ k, mty C0 I (ck k (ik k)) = mty C0 I (ck k (ik k + pk k)))
    (hv0pp : ∀ k a, I.rho (g (v0 k)) (ck k (ik k + a)) = pp)
    (hee : ∀ e f r cc, Concept.all r cc ∈ mtk C0 I (g e) (bud e) →
      (if e = f then eq else if dadj e f then dr else po) = r →
      cc ∈ mtk C0 I (g f) (bud f))
    (he_ex : ∀ e r D, Concept.ex r D ∈ mtk C0 I (g e) (bud e) →
      (∃ f, (if e = f then eq else if dadj e f then dr else po) = r ∧
        D ∈ mtk C0 I (g f) (bud f)) ∨
      (∃ k, conv (if e = v0 k then ppi else po) = r ∧
        ∃ a, a < pk k ∧ D ∈ mtk C0 I (ck k (ik k + a)) (bud (v0 k))))
    (hk_ex : ∀ k a r D, Concept.ex r D ∈ mtk C0 I (ck k (ik k + a)) (bud (v0 k)) →
      (∃ f, (if f = v0 k then ppi else po) = r ∧ D ∈ mtk C0 I (g f) (bud f)) ∨
      (r = pp ∧ ∃ b, b < pk k ∧ D ∈ mtk C0 I (ck k (ik k + b)) (bud (v0 k))) ∨
      (r = eq ∧ D ∈ mtk C0 I (ck k (ik k + a)) (bud (v0 k)))) :
    MultiTierOk (mtkKernels I C0 g bud dadj v0 ck ik pk) := by
  have hv0dom : ∀ k, I.dom (g (v0 k)) := fun k => hgdom (v0 k)
  have hppi : ∀ k a, I.rho (ck k (ik k + a)) (g (v0 k)) = ppi := fun k a => by
    rw [hI.conv_ (g (v0 k)) (ck k (ik k + a)) (hv0dom k) (hdom k (ik k + a)), hv0pp k a]; rfl
  have hKe : ∀ (k : κ) (e : β),
      conv ((mtkKernels I C0 g bud dadj v0 ck ik pk).K k e)
        = if e = v0 k then pp else po := by
    intro k e; show conv (if e = v0 k then ppi else po) = if e = v0 k then pp else po
    by_cases he : e = v0 k
    · rw [if_pos he, if_pos he]; rfl
    · rw [if_neg he, if_neg he]; rfl
  refine
    { hp := hp
      frame_q := po_default_multi_frame dadj hsym v0
      e_clash := fun _ _ h => mtk_clash h
      e_nobot := fun _ => mtk_nobot
      e_and := fun _ _ _ h => mtk_and h
      e_or := fun _ _ _ h => mtk_or h
      k_clash := fun _ _ _ _ h => mtk_clash h
      k_nobot := fun _ _ _ => mtk_nobot
      k_and := fun _ _ _ _ _ h => mtk_and h
      k_or := fun _ _ _ _ _ h => mtk_or h
      ee_all := fun e f r cc hmem hE => hee e f r cc hmem hE
      ek_all := ?_
      ke_all := ?_
      kk_pp := fun k a ha cc hmem b hb =>
        mtk_kk_pp hI (ck k) (hdom k) (hstep k) (hty k) ha (bud (v0 k)) hmem hb
      kk_ppi := fun k a ha cc hmem b hb =>
        mtk_kk_ppi hI (ck k) (hdom k) (hstep k) (hty k) ha (bud (v0 k)) hmem hb
      kk_eq := fun k a _ cc hmem =>
        all_into hmem (hI.refl_eq (ck k (ik k + a)) (hdom k (ik k + a))) (hdom k (ik k + a))
      kq_all := ?_
      e_ex := ?_
      k_ex := ?_ }
  · -- ek_all
    intro e r cc hmem k hr a _
    rw [hKe k e] at hr
    exact podefault_ek hpofree g (v0 k) bud (hv0pp k a) (hdom k (ik k + a)) hmem hr
  · -- ke_all
    intro k a _ r cc hmem f hK
    exact podefault_ke hpofree g (v0 k) bud (hv0dom k) (hppi k a) hmem hK
  · -- kq_all: VACUOUS — cross-Q = PO, no ∀PO in mtk phases
    intro k k' _ a _ r cc hmem hQ b _
    have hr : r = po := hQ.symm
    subst hr
    exact absurd (mem_mtk.mp hmem).1 (mty_no_all_po hpofree)
  · -- e_ex
    intro e r D hmem
    rcases he_ex e r D hmem with ⟨f, hf, hDf⟩ | ⟨k, hK, a, ha, hDa⟩
    · exact Or.inl ⟨f, hf, hDf⟩
    · exact Or.inr ⟨k, hK, a, ha, hDa⟩
  · -- k_ex
    intro k a _ r D hmem
    rcases hk_ex k a r D hmem with ⟨f, hf, hDf⟩ | ⟨rfl, b, hb, hDb⟩ | ⟨rfl, hD⟩
    · exact Or.inl ⟨f, hf, hDf⟩
    · exact Or.inr (Or.inl ⟨rfl, b, hb, hDb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hD⟩))

/-- **`mtkKernels` is `∀PO`-obligation-free** — gluability + `kq_all`-vacuity
    source for the multi-kernel cert (same `mkBlock_nopo` pattern). -/
theorem mtkKernels_nopo {C0 : Concept} (hpo : POFree C0) {β κ : Type}
    (g : β → α) (bud : β → Nat) (dadj : β → β → Bool) (v0 : κ → β)
    (ck : κ → Nat → α) (ik pk : κ → Nat) :
    MTNoPo (mtkKernels I C0 g bud dadj v0 ck ik pk) where
  ext := fun _ _E h => mty_no_all_po hpo (mem_mtk.mp h).1
  ker := fun _ _ _ _E h => mty_no_all_po hpo (mem_mtk.mp h).1

open Classical in
/-- **THE MtkK MULTI-KERNEL CERTIFICATE WITH DR-CHILDREN** — `mtkKernels` with
    forced `DR` `K`-edges (phase-`∃DR` service).  `K k e` = `PPI` to attach /
    `DR` to `k`'s children (`kdr k e`) / `PO` else. -/
noncomputable def mtkKernelsDR (I : Interp α) (C0 : Concept) {β κ : Type}
    (g : β → α) (bud : β → Nat) (dadj : β → β → Bool) (v0 : κ → β) (kdr : κ → β → Bool)
    (ck : κ → Nat → α) (ik pk : κ → Nat) : MultiTier β κ where
  E e f := if e = f then eq else if dadj e f then dr else po
  K k e := if e = v0 k then ppi else if kdr k e then dr else po
  Q _ _ := po
  up _ := true
  tauE e := mtk C0 I (g e) (bud e)
  p := pk
  phase k a := mtk C0 I (ck k (ik k + a)) (bud (v0 k))

open Classical in
/-- **THE DR-CHILDREN MULTI-KERNEL MERGE IS VALID** — the phase-`∃DR` wiring
    assembled.  `frame_q` = `po_dr_multi_kernel_frame` (forcing-completion frame);
    `ek_all`/`ke_all` = `podefault_ek_dr`/`podefault_ke_dr` (DR children served at
    the SAME budget, no depth seam); `kk_*`/`kq_all` as `mtkKernels_ok`.  `hcoh`
    (children `DR`-adjacent to attach) feeds the frame; `hdr` (children `DR` to
    EVERY phase, matching budget) feeds the `∀DR` propagation.  `hee`/`he_ex`/
    `hk_ex` carry the routing (now with `DR` `K`-edges: a phase's `∃DR.D` is
    served by a child via `k_ex` disjunct-1). -/
theorem mtkKernelsDR_ok (hI : RCC5Interp I) {C0 : Concept} (hpofree : POFree C0)
    {β κ : Type} (g : β → α) (hgdom : ∀ e, I.dom (g e)) (bud : β → Nat)
    (dadj : β → β → Bool) (hsym : ∀ e f, dadj e f = dadj f e) (v0 : κ → β)
    (kdr : κ → β → Bool) (hcoh : ∀ k e, kdr k e = true → dadj e (v0 k) = true)
    (ck : κ → Nat → α) (hdom : ∀ k n, I.dom (ck k n))
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = pp)
    (ik pk : κ → Nat) (hp : ∀ k, 0 < pk k)
    (hty : ∀ k, mty C0 I (ck k (ik k)) = mty C0 I (ck k (ik k + pk k)))
    (hv0pp : ∀ k a, I.rho (g (v0 k)) (ck k (ik k + a)) = pp)
    (hdr : ∀ k a e, kdr k e = true →
      I.rho (g e) (ck k (ik k + a)) = dr ∧
        bud (v0 k) ≤ bud e + 1 ∧ bud e ≤ bud (v0 k) + 1)
    (hee : ∀ e f r cc, Concept.all r cc ∈ mtk C0 I (g e) (bud e) →
      (if e = f then eq else if dadj e f then dr else po) = r →
      cc ∈ mtk C0 I (g f) (bud f))
    (he_ex : ∀ e r D, Concept.ex r D ∈ mtk C0 I (g e) (bud e) →
      (∃ f, (if e = f then eq else if dadj e f then dr else po) = r ∧
        D ∈ mtk C0 I (g f) (bud f)) ∨
      (∃ k, conv (if e = v0 k then ppi else if kdr k e then dr else po) = r ∧
        ∃ a, a < pk k ∧ D ∈ mtk C0 I (ck k (ik k + a)) (bud (v0 k))))
    (hk_ex : ∀ k a r D, Concept.ex r D ∈ mtk C0 I (ck k (ik k + a)) (bud (v0 k)) →
      (∃ f, (if f = v0 k then ppi else if kdr k f then dr else po) = r ∧
        D ∈ mtk C0 I (g f) (bud f)) ∨
      (r = pp ∧ ∃ b, b < pk k ∧ D ∈ mtk C0 I (ck k (ik k + b)) (bud (v0 k))) ∨
      (r = eq ∧ D ∈ mtk C0 I (ck k (ik k + a)) (bud (v0 k)))) :
    MultiTierOk (mtkKernelsDR I C0 g bud dadj v0 kdr ck ik pk) := by
  have hv0dom : ∀ k, I.dom (g (v0 k)) := fun k => hgdom (v0 k)
  have hppi : ∀ k a, I.rho (ck k (ik k + a)) (g (v0 k)) = ppi := fun k a => by
    rw [hI.conv_ (g (v0 k)) (ck k (ik k + a)) (hv0dom k) (hdom k (ik k + a)), hv0pp k a]; rfl
  have hKe : ∀ (k : κ) (e : β),
      conv ((mtkKernelsDR I C0 g bud dadj v0 kdr ck ik pk).K k e)
        = if e = v0 k then pp else if kdr k e then dr else po := by
    intro k e
    show conv (if e = v0 k then ppi else if kdr k e then dr else po)
      = if e = v0 k then pp else if kdr k e then dr else po
    by_cases he : e = v0 k
    · rw [if_pos he, if_pos he]; rfl
    · by_cases hc : kdr k e = true
      · rw [if_neg he, if_pos hc, if_neg he]; rfl
      · rw [if_neg he, if_neg hc, if_neg he]; rfl
  refine
    { hp := hp
      frame_q := po_dr_multi_kernel_frame dadj hsym v0 kdr hcoh
      e_clash := fun _ _ h => mtk_clash h
      e_nobot := fun _ => mtk_nobot
      e_and := fun _ _ _ h => mtk_and h
      e_or := fun _ _ _ h => mtk_or h
      k_clash := fun _ _ _ _ h => mtk_clash h
      k_nobot := fun _ _ _ => mtk_nobot
      k_and := fun _ _ _ _ _ h => mtk_and h
      k_or := fun _ _ _ _ _ h => mtk_or h
      ee_all := fun e f r cc hmem hE => hee e f r cc hmem hE
      ek_all := ?_
      ke_all := ?_
      kk_pp := fun k a ha cc hmem b hb =>
        mtk_kk_pp hI (ck k) (hdom k) (hstep k) (hty k) ha (bud (v0 k)) hmem hb
      kk_ppi := fun k a ha cc hmem b hb =>
        mtk_kk_ppi hI (ck k) (hdom k) (hstep k) (hty k) ha (bud (v0 k)) hmem hb
      kk_eq := fun k a _ cc hmem =>
        all_into hmem (hI.refl_eq (ck k (ik k + a)) (hdom k (ik k + a))) (hdom k (ik k + a))
      kq_all := ?_
      e_ex := ?_
      k_ex := ?_ }
  · -- ek_all
    intro e r cc hmem k hr a _
    rw [hKe k e] at hr
    exact podefault_ek_dr hpofree g (v0 k) (kdr k) bud (hv0pp k a) (hdom k (ik k + a))
      (fun e' he' => ⟨(hdr k a e' he').1, (hdr k a e' he').2.2⟩) hmem hr
  · -- ke_all
    intro k a _ r cc hmem f hK
    refine podefault_ke_dr hpofree g hgdom (v0 k) (kdr k) bud (hv0dom k) (hppi k a)
      (fun f' hf' => ⟨?_, (hdr k a f' hf').2.1⟩) hmem hK
    rw [hI.conv_ (g f') (ck k (ik k + a)) (hgdom f') (hdom k (ik k + a)), (hdr k a f' hf').1]; rfl
  · -- kq_all vacuous
    intro k k' _ a _ r cc hmem hQ b _
    have hr : r = po := hQ.symm; subst hr
    exact absurd (mem_mtk.mp hmem).1 (mty_no_all_po hpofree)
  · -- e_ex
    intro e r D hmem
    rcases he_ex e r D hmem with ⟨f, hf, hDf⟩ | ⟨k, hK, a, ha, hDa⟩
    · exact Or.inl ⟨f, hf, hDf⟩
    · exact Or.inr ⟨k, hK, a, ha, hDa⟩
  · -- k_ex
    intro k a _ r D hmem
    rcases hk_ex k a r D hmem with ⟨f, hf, hDf⟩ | ⟨rfl, b, hb, hDb⟩ | ⟨rfl, hD⟩
    · exact Or.inl ⟨f, hf, hDf⟩
    · exact Or.inr (Or.inl ⟨rfl, b, hb, hDb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hD⟩))

/-- **`mtkKernelsDR` is `∀PO`-obligation-free** — gluability of the DR-children
    cert (same `mkBlock_nopo` pattern: `tauE`/`phase` are `mtk` labels ⊆ `mty`,
    no `∀PO` for a `POFree` concept). -/
theorem mtkKernelsDR_nopo {C0 : Concept} (hpo : POFree C0) {β κ : Type}
    (g : β → α) (bud : β → Nat) (dadj : β → β → Bool) (v0 : κ → β) (kdr : κ → β → Bool)
    (ck : κ → Nat → α) (ik pk : κ → Nat) :
    MTNoPo (mtkKernelsDR I C0 g bud dadj v0 kdr ck ik pk) where
  ext := fun _ _E h => mty_no_all_po hpo (mem_mtk.mp h).1
  ker := fun _ _ _ _E h => mty_no_all_po hpo (mem_mtk.mp h).1

/-- `ite` does not depend on the `Decidable` instance (it is a `Subsingleton`) —
    the bridge between the `mtkNodesH`-subtype's `DecidableEq` (used by the
    routing lemmas) and the `Classical.propDecidable` the generic `mtkKernel`
    bakes in.  Core Lean has no `convert`, so this is proved by hand. -/
theorem ite_inst_irrel {γ : Type} {cc : Prop} (i1 i2 : Decidable cc) (a b : γ) :
    @ite γ cc i1 a b = @ite γ cc i2 a b := by
  cases i1 with
  | isTrue h1 => cases i2 with
    | isTrue _ => rfl
    | isFalse h2 => exact absurd h1 h2
  | isFalse h1 => cases i2 with
    | isTrue h2 => exact absurd h2 h1
    | isFalse _ => rfl

open Classical in
/-- **THE `mtk`-WITH-KERNELS CERTIFICATE IS VALID** (step 4 capstone,
    single-kernel).  The whole extraction assembled: `mtHF` horizontal skeleton
    (`mtkNodesH`) + one ascending kernel at the root, PO-default `K`,
    `mtk`-truncated labels — a valid `MultiTierOk`.  `mtkKernel_ok` fed the
    three routing lemmas (`mtk_ee_all`/`mtk_e_ex`/`mtk_k_ex`), the `Decidable`
    instance bridged by `ite_inst_irrel`.  The certificate SOUNDNESS is now
    complete; a full extraction theorem additionally needs the MODEL-side
    supply of `hpp_v0`/`hno_ppi`/`hk_class` (the demand structure of a
    single-self-carrying-tower `POFree` concept). -/
theorem extract_mtkKernel (hI : RCC5Interp I) {C0 : Concept} (hpofree : POFree C0)
    (root : MTKNode I C0) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    (i p : Nat) (hp : 0 < p)
    (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    (hv0pp : ∀ a, I.rho root.x (c (i + a)) = pp)
    (hpp_v0 : ∀ (e : {n // n ∈ mtkNodesH root}) (D : Concept),
      Concept.ex pp D ∈ mtk C0 I e.val.x e.val.k →
      e = ⟨root, self_mem_mtkNodesH root⟩ ∧
        ∃ a, a < p ∧ D ∈ mtk C0 I (c (i + a)) root.k)
    (hno_ppi : ∀ (e : {n // n ∈ mtkNodesH root}) (D : Concept),
      Concept.ex ppi D ∈ mtk C0 I e.val.x e.val.k → False)
    (hk_class : ∀ a r D, Concept.ex r D ∈ mtk C0 I (c (i + a)) root.k →
      (∃ f : {n // n ∈ mtkNodesH root}, f ≠ ⟨root, self_mem_mtkNodesH root⟩ ∧
        r = po ∧ D ∈ mtk C0 I f.val.x f.val.k) ∨
      (r = pp ∧ ∃ b, b < p ∧ D ∈ mtk C0 I (c (i + b)) root.k) ∨ r = eq) :
    MultiTierOk (mtkKernel I C0 (fun e : {n // n ∈ mtkNodesH root} => e.val.x)
      (fun e => e.val.k) (fun e f => decide (sAdjK e.val f.val))
      ⟨root, self_mem_mtkNodesH root⟩ c i p) := by
  refine mtkKernel_ok (β := {n // n ∈ mtkNodesH root}) hI hpofree (fun e => e.val.x) (fun e => e.val.hx)
    (fun e => e.val.k) (fun e f => decide (sAdjK e.val f.val))
    (fun e f => by rw [propext (sAdjK_symm e.val f.val)])
    ⟨root, self_mem_mtkNodesH root⟩ c hdom hstep i p hp hty hv0pp ?_ ?_ ?_
  · intro e f r cc hall hEf
    exact mtk_ee_all hI hpofree root e f r cc hall (Eq.trans (ite_inst_irrel _ _ _ _) hEf)
  · intro e r D hdem
    rcases mtk_e_ex hI root c p i ⟨root, self_mem_mtkNodesH root⟩ hpp_v0 hno_ppi
      e r D hdem with ⟨f, hEf, hDf⟩ | ⟨hK, a, ha, hDa⟩
    · exact Or.inl ⟨f, Eq.trans (ite_inst_irrel _ _ _ _) hEf, hDf⟩
    · exact Or.inr ⟨Eq.trans (congrArg conv (ite_inst_irrel _ _ _ _)) hK, a, ha, hDa⟩
  · intro a r D hmem
    rcases mtk_k_ex hI root c p i ⟨root, self_mem_mtkNodesH root⟩ hdom hk_class
      a r D hmem with ⟨f, hf, hDf⟩ | h
    · exact Or.inl ⟨f, Eq.trans (ite_inst_irrel _ _ _ _) hf, hDf⟩
    · exact Or.inr h

/-- **`hno_ppi` for free** — the SYNTACTIC third of the completeness inputs to
    `extract_mtkKernel`.  A concept with no `∃PPI` in its closure can never have
    a node demanding `∃PPI`: every `mtk` label sits inside `mty ⊆ cl C0`
    (`mem_mtk`, `mty_sub`).  Reusable for any `∃PPI`-free `C0` and any `root`. -/
theorem no_ppi_demand {C0 : Concept} (root : MTKNode I C0)
    (hcl : ∀ D, Concept.ex ppi D ∉ cl C0) :
    ∀ (e : {n // n ∈ mtkNodesH root}) (D : Concept),
      Concept.ex ppi D ∈ mtk C0 I e.val.x e.val.k → False :=
  fun _ D hdem => hcl D (mty_sub _ (mem_mtk.mp hdem).1)

/-- **`PP`-transitivity along a chain** — in any `PP`-ascending chain `c`, the
    base `c 0` sits `PP`-below every later point (`comp(PP,PP) = {PP}` forces the
    composite).  Gives `hv0pp` for a root placed at `c 0` over ANY model,
    generalising the concrete `chain_lt` the ℕ-chain witnesses used. -/
theorem pp_chain_below (hI : RCC5Interp I) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp) :
    ∀ m, I.rho (c 0) (c (m + 1)) = pp := by
  intro m
  induction m with
  | zero => exact hstep 0
  | succ m ih =>
    have hc := hI.comp_ (c 0) (c (m + 1)) (c (m + 1 + 1))
      (hdom 0) (hdom (m + 1)) (hdom (m + 1 + 1))
    rw [ih, hstep (m + 1), show comp pp pp = [pp] from rfl, List.mem_singleton] at hc
    exact hc

/-- **Auto-build the tower from the model** — a single persistent-`∃PP` point
    `x0` (`persistPP`) yields the whole ascending `PP`-tower via `buildChain` +
    `persistPP_productive`: `c 0 = x0`, every point is in-domain, adjacent points
    are `PP`, and persistence propagates (so `mty_segment_bounded` + `pp_chain_below`
    apply).  Discharges `extract_mtkKernel`'s `c`/`hdom`/`hstep` for ANY model
    from just the forced-tower witness. -/
theorem tower_from_persistPP (hI : RCC5Interp I) {C0 G : Concept} {x0 : α}
    (hpers : persistPP I C0 G x0) :
    ∃ c : Nat → α, c 0 = x0 ∧ (∀ n, I.dom (c n)) ∧
      (∀ n, I.rho (c n) (c (n + 1)) = pp) ∧ (∀ n, persistPP I C0 G (c n)) := by
  have hprod : ∀ x, persistPP I C0 G x →
      ∃ y, persistPP I C0 G y ∧ I.dom y ∧ I.rho x y = pp :=
    fun x hx => persistPP_productive hI x hx
  exact ⟨buildChain (persistPP I C0 G) hprod x0 hpers,
    buildChain_zero (persistPP I C0 G) hprod x0 hpers,
    buildChain_dom (persistPP I C0 G) hprod x0 hpers hpers.1,
    buildChain_step (persistPP I C0 G) hprod x0 hpers,
    buildChain_prop (persistPP I C0 G) hprod x0 hpers⟩

open Classical in
/-- **GENERAL EXTRACTION MODULO CLEANLINESS** — the completeness direction for
    the single-tower ∀PO-free fragment, with the open content isolated.  Given a
    `PP`-tower `c` in a model (root `c 0` carrying `C0`), the syntactic
    `∃PPI`-freeness of `C0`, and a recurrence `(i,p)`, this discharges ALL of
    `extract_mtkKernel`'s structural inputs — `hv0pp` (via `pp_chain_below`, root
    `PP`-below every phase), `hno_ppi` (via `no_ppi_demand`), the root, and the
    `multiTier_sound` read-off — leaving EXACTLY the two model-side CLEANLINESS
    obligations as hypotheses: `hpp_v0` (only the root carries `∃PP` among
    skeleton nodes) and `hk_class` (each phase demands only a served `∃PP` or
    `∃EQ`).  The witnesses `cvert_generic_satisfiable` (degenerate skeleton) and
    `cmerge_generic_satisfiable` (non-degenerate) discharge cleanliness
    concretely; the GENERAL discharge (a clean model always exists) is the
    remaining analytic content (W2′/F6 territory). -/
theorem extract_from_tower (hI : RCC5Interp I) {C0 : Concept} (hpofree : POFree C0)
    (c : Nat → α) (hdom : ∀ n, I.dom (c n))
    (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    (hC0 : C0 ∈ mty C0 I (c 0)) (hnoppi : ∀ D, Concept.ex ppi D ∉ cl C0)
    (i p : Nat) (hi : 0 < i) (hp : 0 < p)
    (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    (hpp_v0 : ∀ (e : {n // n ∈ mtkNodesH (⟨c 0, mdepth C0, hdom 0⟩ : MTKNode I C0)})
        (D : Concept),
      Concept.ex pp D ∈ mtk C0 I e.val.x e.val.k →
      e = ⟨⟨c 0, mdepth C0, hdom 0⟩, self_mem_mtkNodesH ⟨c 0, mdepth C0, hdom 0⟩⟩ ∧
        ∃ a, a < p ∧ D ∈ mtk C0 I (c (i + a)) (mdepth C0))
    (hk_class : ∀ a r D, Concept.ex r D ∈ mtk C0 I (c (i + a)) (mdepth C0) →
      (∃ f : {n // n ∈ mtkNodesH (⟨c 0, mdepth C0, hdom 0⟩ : MTKNode I C0)},
        f ≠ ⟨⟨c 0, mdepth C0, hdom 0⟩, self_mem_mtkNodesH ⟨c 0, mdepth C0, hdom 0⟩⟩ ∧
        r = po ∧ D ∈ mtk C0 I f.val.x f.val.k) ∨
      (r = pp ∧ ∃ b, b < p ∧ D ∈ mtk C0 I (c (i + b)) (mdepth C0)) ∨ r = eq) :
    Satisfiable C0 :=
  multiTier_sound _
    (extract_mtkKernel hI hpofree ⟨c 0, mdepth C0, hdom 0⟩ c hdom hstep i p hp hty
      (fun a => by
        have h := pp_chain_below hI c hdom hstep (i + a - 1)
        rwa [show i + a - 1 + 1 = i + a from by omega] at h)
      hpp_v0 (no_ppi_demand ⟨c 0, mdepth C0, hdom 0⟩ hnoppi) hk_class)
    (Sum.inl ⟨⟨c 0, mdepth C0, hdom 0⟩, self_mem_mtkNodesH ⟨c 0, mdepth C0, hdom 0⟩⟩)
    C0 (mem_mtk.mpr ⟨hC0, Nat.le_refl _⟩)

open Classical in
/-- **THE FLAT MULTI-TOWER EXTRACTION** — `cnest` generalised to ARBITRARY `κ`.
    `κ` ascending towers over one model, all bases mutually `PO` (the flat
    cross-`PO` skeleton, `dadj ≡ false`), each base `ck k 0` carrying `C0` and
    `PP`-below its own phase window (`ik k ≥ 1`).  The demand routing (base and
    phase): `∃PP` → own kernel, `∃PO` → another base, `∃EQ` → self; NO `∃DR`
    (no `DR` among flat bases) and NO `∃PPI` (excluded by the routing shape).
    Feeds `mtkKernels_ok`
    and reads off `Satisfiable C0`.  `cnest` is the `κ = Bool` instance; this is
    the general "N cross-`PO` towers" extraction. -/
theorem extract_flat_towers (hI : RCC5Interp I) {C0 : Concept} (hpofree : POFree C0)
    {κ : Type} (ck : κ → Nat → α) (hdom : ∀ k n, I.dom (ck k n))
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = pp)
    (ik pk : κ → Nat) (hik : ∀ k, 0 < ik k) (hp : ∀ k, 0 < pk k)
    (hty : ∀ k, mty C0 I (ck k (ik k)) = mty C0 I (ck k (ik k + pk k)))
    (hbase : ∀ e r D, Concept.ex r D ∈ mtk C0 I (ck e 0) (mdepth C0) →
      (r = pp ∧ D ∈ mtk C0 I (ck e (ik e)) (mdepth C0)) ∨
      (r = po ∧ ∃ f, f ≠ e ∧ D ∈ mtk C0 I (ck f 0) (mdepth C0)) ∨
      (r = eq ∧ D ∈ mtk C0 I (ck e 0) (mdepth C0)))
    (hphase : ∀ k a r D, Concept.ex r D ∈ mtk C0 I (ck k (ik k + a)) (mdepth C0) →
      (r = pp ∧ ∃ b, b < pk k ∧ D ∈ mtk C0 I (ck k (ik k + b)) (mdepth C0)) ∨
      (r = po ∧ ∃ f, f ≠ k ∧ D ∈ mtk C0 I (ck f 0) (mdepth C0)) ∨
      (r = eq ∧ D ∈ mtk C0 I (ck k (ik k + a)) (mdepth C0)))
    (kroot : κ) (hroot : C0 ∈ mty C0 I (ck kroot 0)) :
    Satisfiable C0 := by
  have hok := mtkKernels_ok hI hpofree (fun k => ck k 0) (fun k => hdom k 0)
    (fun _ => mdepth C0) (fun _ _ => false) (fun _ _ => rfl) (id) ck hdom hstep ik pk hp hty
    (by intro k a
        have h := pp_chain_below hI (ck k) (hdom k) (hstep k) (ik k + a - 1)
        rwa [show ik k + a - 1 + 1 = ik k + a from by have := hik k; omega] at h)
    (by intro e f r cc hmem hE
        by_cases hef : e = f
        · subst hef
          rw [if_pos rfl] at hE; subst hE
          exact all_into hmem (hI.refl_eq (ck e 0) (hdom e 0)) (hdom e 0)
        · rw [if_neg hef] at hE
          have hrpo : r = po := hE.symm
          subst hrpo
          exact absurd (mem_mtk.mp hmem).1 (mty_no_all_po hpofree))
    (by intro e r D hmem
        rcases hbase e r D hmem with ⟨rfl, hD⟩ | ⟨rfl, f, hfe, hDf⟩ | ⟨rfl, hD⟩
        · refine Or.inr ⟨e, ?_, 0, hp e, hD⟩
          split
          · rfl
          · exact absurd (rfl : e = id e) (by assumption)
        · refine Or.inl ⟨f, ?_, hDf⟩
          rw [if_neg (fun h => hfe h.symm)]; rfl
        · exact Or.inl ⟨e, by rw [if_pos rfl], hD⟩)
    (by intro k a r D hmem
        rcases hphase k a r D hmem with ⟨rfl, b, hb, hDb⟩ | ⟨rfl, f, hfk, hDf⟩ | ⟨rfl, hD⟩
        · exact Or.inr (Or.inl ⟨rfl, b, hb, hDb⟩)
        · refine Or.inl ⟨f, ?_, hDf⟩
          rw [if_neg (show f ≠ id k from hfk)]
        · exact Or.inr (Or.inr ⟨rfl, hD⟩))
  exact @multiTier_sound κ κ (fun a b => Classical.propDecidable (a = b)) _ hok
    (Sum.inl kroot) C0 (mem_mtk.mpr ⟨hroot, Nat.le_refl _⟩)

open Classical in
/-- **THE DR-SKELETON MULTI-TOWER EXTRACTION** — `extract_flat_towers` extended
    with a `DR`/`PO` skeleton AMONG the bases (item 1 of the nested summit).
    `dadj : κ → κ → Bool` a symmetric adjacency with the model correspondence
    `hdadj` (adjacent bases are `DR`); the frame is `po_default_multi_frame dadj`.
    Routing gains `∃DR` at bases (→ a `DR`-adjacent base); phases stay `∃DR`-clean
    (`K` has no `DR` edge — that is the deferred phase-spawning summit).
    `ek_all`/`ke_all` for `∀DR`/`∀PPI` at bases are handled INSIDE
    `mtkKernels_ok` (proven generically — no `DR`/`PPI` `K`/`conv K` edge, so
    they never fire to a kernel). Generalises `extract_flat_towers`
    (`dadj ≡ false`). -/
theorem extract_skel_towers (hI : RCC5Interp I) {C0 : Concept} (hpofree : POFree C0)
    {κ : Type} (ck : κ → Nat → α) (hdom : ∀ k n, I.dom (ck k n))
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = pp)
    (ik pk : κ → Nat) (hik : ∀ k, 0 < ik k) (hp : ∀ k, 0 < pk k)
    (hty : ∀ k, mty C0 I (ck k (ik k)) = mty C0 I (ck k (ik k + pk k)))
    (dadj : κ → κ → Bool) (hsym : ∀ e f, dadj e f = dadj f e)
    (hdadj : ∀ e f, dadj e f = true → I.rho (ck e 0) (ck f 0) = dr)
    (hbase : ∀ e r D, Concept.ex r D ∈ mtk C0 I (ck e 0) (mdepth C0) →
      (r = pp ∧ D ∈ mtk C0 I (ck e (ik e)) (mdepth C0)) ∨
      (r = dr ∧ ∃ f, e ≠ f ∧ dadj e f = true ∧ D ∈ mtk C0 I (ck f 0) (mdepth C0)) ∨
      (r = po ∧ ∃ f, e ≠ f ∧ dadj e f = false ∧ D ∈ mtk C0 I (ck f 0) (mdepth C0)) ∨
      (r = eq ∧ D ∈ mtk C0 I (ck e 0) (mdepth C0)))
    (hphase : ∀ k a r D, Concept.ex r D ∈ mtk C0 I (ck k (ik k + a)) (mdepth C0) →
      (r = pp ∧ ∃ b, b < pk k ∧ D ∈ mtk C0 I (ck k (ik k + b)) (mdepth C0)) ∨
      (r = po ∧ ∃ f, f ≠ k ∧ D ∈ mtk C0 I (ck f 0) (mdepth C0)) ∨
      (r = eq ∧ D ∈ mtk C0 I (ck k (ik k + a)) (mdepth C0)))
    (kroot : κ) (hroot : C0 ∈ mty C0 I (ck kroot 0)) :
    Satisfiable C0 := by
  have hok := mtkKernels_ok hI hpofree (fun k => ck k 0) (fun k => hdom k 0)
    (fun _ => mdepth C0) dadj hsym (id) ck hdom hstep ik pk hp hty
    (by intro k a
        have h := pp_chain_below hI (ck k) (hdom k) (hstep k) (ik k + a - 1)
        rwa [show ik k + a - 1 + 1 = ik k + a from by have := hik k; omega] at h)
    (by intro e f r cc hmem hE
        by_cases hef : e = f
        · subst hef
          rw [if_pos rfl] at hE; subst hE
          exact all_into hmem (hI.refl_eq (ck e 0) (hdom e 0)) (hdom e 0)
        · rw [if_neg hef] at hE
          by_cases hd : dadj e f = true
          · rw [if_pos hd] at hE; subst hE
            exact all_into hmem (hdadj e f hd) (hdom f 0)
          · rw [if_neg hd] at hE
            have hrpo : r = po := hE.symm
            subst hrpo
            exact absurd (mem_mtk.mp hmem).1 (mty_no_all_po hpofree))
    (by intro e r D hmem
        rcases hbase e r D hmem with ⟨rfl, hD⟩ | ⟨rfl, f, hef, hd, hDf⟩ |
          ⟨rfl, f, hef, hd, hDf⟩ | ⟨rfl, hD⟩
        · refine Or.inr ⟨e, ?_, 0, hp e, hD⟩
          split
          · rfl
          · exact absurd (rfl : e = id e) (by assumption)
        · refine Or.inl ⟨f, ?_, hDf⟩
          rw [if_neg hef, if_pos hd]
        · refine Or.inl ⟨f, ?_, hDf⟩
          rw [if_neg hef, if_neg (show dadj e f ≠ true from by simp [hd])]
        · exact Or.inl ⟨e, by rw [if_pos rfl], hD⟩)
    (by intro k a r D hmem
        rcases hphase k a r D hmem with ⟨rfl, b, hb, hDb⟩ | ⟨rfl, f, hfk, hDf⟩ | ⟨rfl, hD⟩
        · exact Or.inr (Or.inl ⟨rfl, b, hb, hDb⟩)
        · refine Or.inl ⟨f, ?_, hDf⟩
          rw [if_neg (show f ≠ id k from hfk)]
        · exact Or.inr (Or.inr ⟨rfl, hD⟩))
  exact @multiTier_sound κ κ (fun a b => Classical.propDecidable (a = b)) _ hok
    (Sum.inl kroot) C0 (mem_mtk.mpr ⟨hroot, Nat.le_refl _⟩)

open Classical in
/-- **THE PHASE-`∃DR` MULTI-KERNEL EXTRACTION ENGINE** — the reusable entry
    point for the DR-children route, parallel to `extract_skel_towers` but built
    on `mtkKernelsDR_ok` (which serves phase-`∃DR` via `DR`-children, not just
    base-`∃DR`).  β indexes ALL externals (bases `v0 k` AND their `DR`-children,
    selected by `kdr`); κ indexes the ascending kernels; `bud : β → Nat` is the
    per-node truncation budget, allowing a `DR`-child to sit at a budget STRICTLY
    below its phase (the budget-slack of `podefault_ke/ek_dr`, the termination
    measure of the general recursion).  Given the model correspondences + the
    routing hypotheses (`hee`/`he_ex`/`hk_ex`, in the frame's raw `if`-form) and
    a root external carrying `C0`, it discharges `Satisfiable C0`.  This packages
    the whole `mtkKernelsDR_ok → multiTier_sound` pipeline the `Cpdr` witness ran
    inline, so the eventual coverage construction only has to produce β/κ + the
    routing, not re-thread the certificate. -/
theorem extract_dr_children (hI : RCC5Interp I) {C0 : Concept}
    (hpofree : POFree C0) {β κ : Type} (g : β → α) (hgdom : ∀ e, I.dom (g e))
    (bud : β → Nat) (dadj : β → β → Bool) (hsym : ∀ e f, dadj e f = dadj f e)
    (v0 : κ → β) (kdr : κ → β → Bool)
    (hcoh : ∀ k e, kdr k e = true → dadj e (v0 k) = true)
    (ck : κ → Nat → α) (hdom : ∀ k n, I.dom (ck k n))
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = pp)
    (ik pk : κ → Nat) (hp : ∀ k, 0 < pk k)
    (hty : ∀ k, mty C0 I (ck k (ik k)) = mty C0 I (ck k (ik k + pk k)))
    (hv0pp : ∀ k a, I.rho (g (v0 k)) (ck k (ik k + a)) = pp)
    (hdr : ∀ k a e, kdr k e = true →
      I.rho (g e) (ck k (ik k + a)) = dr ∧
        bud (v0 k) ≤ bud e + 1 ∧ bud e ≤ bud (v0 k) + 1)
    (hee : ∀ e f r cc, Concept.all r cc ∈ mtk C0 I (g e) (bud e) →
      (if e = f then eq else if dadj e f then dr else po) = r →
      cc ∈ mtk C0 I (g f) (bud f))
    (he_ex : ∀ e r D, Concept.ex r D ∈ mtk C0 I (g e) (bud e) →
      (∃ f, (if e = f then eq else if dadj e f then dr else po) = r ∧
        D ∈ mtk C0 I (g f) (bud f)) ∨
      (∃ k, conv (if e = v0 k then ppi else if kdr k e then dr else po) = r ∧
        ∃ a, a < pk k ∧ D ∈ mtk C0 I (ck k (ik k + a)) (bud (v0 k))))
    (hk_ex : ∀ k a r D, Concept.ex r D ∈ mtk C0 I (ck k (ik k + a)) (bud (v0 k)) →
      (∃ f, (if f = v0 k then ppi else if kdr k f then dr else po) = r ∧
        D ∈ mtk C0 I (g f) (bud f)) ∨
      (r = pp ∧ ∃ b, b < pk k ∧ D ∈ mtk C0 I (ck k (ik k + b)) (bud (v0 k))) ∨
      (r = eq ∧ D ∈ mtk C0 I (ck k (ik k + a)) (bud (v0 k))))
    (root : β) (hroot : C0 ∈ mtk C0 I (g root) (bud root)) :
    Satisfiable C0 := by
  have hok := mtkKernelsDR_ok hI hpofree g hgdom bud dadj hsym v0 kdr hcoh ck hdom
    hstep ik pk hp hty hv0pp hdr hee he_ex hk_ex
  exact multiTier_sound _ hok (Sum.inl root) C0 hroot

/-- **KERNEL FROM A PERSISTENT `∃PP` NODE** (the AscMix coverage's vertical
    core, §31.3).  A `persistPP` node `x0` (carrying `∃PP.G` and its `∀PP` guard)
    yields the raw kernel data `extract_dr_children`/`mtkKernels_ok` consume: an
    ascending `PP`-chain `c` from `x0`, a period `(i, p)` with `mty`-coincidence
    (`mty_segment_bounded`), the demand `∃PP.G` carried at every chain point, and
    — for a period start `i ≥ 1` — the base-to-phase relation `x0 PP c(i+a)`
    (`pp_chain_below`).  Packages `persistPP_chain` + `mty_segment_bounded` +
    `pp_chain_below` into the exact shape the mixing assembly needs. -/
theorem ascKernel (hI : RCC5Interp I) {C0 G : Concept} (x0 : α)
    (h0 : persistPP I C0 G x0) (L : Nat) :
    ∃ (c : Nat → α) (i p : Nat),
      c 0 = x0 ∧ (∀ n, I.dom (c n)) ∧ (∀ n, I.rho (c n) (c (n + 1)) = pp) ∧
      L ≤ i ∧ 0 < p ∧ mty C0 I (c i) = mty C0 I (c (i + p)) ∧
      (∀ n, Concept.ex pp G ∈ mty C0 I (c n)) ∧
      (0 < i → ∀ a, I.rho x0 (c (i + a)) = pp) := by
  obtain ⟨c, hc0, hdom, hstep, hdem⟩ := persistPP_chain hI x0 h0
  obtain ⟨i, p, hLi, hp, _, hty⟩ := mty_segment_bounded C0 c L
  refine ⟨c, i, p, hc0, hdom, hstep, hLi, hp, hty, hdem, ?_⟩
  intro hi a
  rw [← hc0]
  rw [show i + a = (i + a - 1) + 1 from by omega]
  exact pp_chain_below hI c hdom hstep (i + a - 1)

/-- Descending analog of `pp_chain_below`: a `PPI`-chain's base is `PPI` to every
    later point (`comp(PPI,PPI) = {PPI}`). -/
theorem ppi_chain_below (hI : RCC5Interp I) (d : Nat → α)
    (hdom : ∀ n, I.dom (d n)) (hstep : ∀ n, I.rho (d n) (d (n + 1)) = ppi) :
    ∀ m, I.rho (d 0) (d (m + 1)) = ppi := by
  intro m
  induction m with
  | zero => exact hstep 0
  | succ m ih =>
    have hc := hI.comp_ (d 0) (d (m + 1)) (d (m + 1 + 1))
      (hdom 0) (hdom (m + 1)) (hdom (m + 1 + 1))
    rw [ih, hstep (m + 1), show comp ppi ppi = [ppi] from rfl, List.mem_singleton] at hc
    exact hc

/-- **DESCENDING KERNEL FROM A PERSISTENT `∃PPI` NODE** — the `dascKernel` mirror
    of `ascKernel`, for the eventual descending (`∃PPI`) arm of the full pofree
    assembly.  A `persistPPI` node `x0` yields the descending `PPI`-chain data
    (`persistPPI_chain` + `mty_segment_bounded` + `ppi_chain_below`). -/
theorem dascKernel (hI : RCC5Interp I) {C0 G : Concept} (x0 : α)
    (h0 : persistPPI I C0 G x0) (L : Nat) :
    ∃ (d : Nat → α) (i p : Nat),
      d 0 = x0 ∧ (∀ n, I.dom (d n)) ∧ (∀ n, I.rho (d n) (d (n + 1)) = ppi) ∧
      L ≤ i ∧ 0 < p ∧ mty C0 I (d i) = mty C0 I (d (i + p)) ∧
      (∀ n, Concept.ex ppi G ∈ mty C0 I (d n)) ∧
      (0 < i → ∀ a, I.rho x0 (d (i + a)) = ppi) := by
  obtain ⟨d, hd0, hdom, hstep, hdem⟩ := persistPPI_chain hI x0 h0
  obtain ⟨i, p, hLi, hp, _, hty⟩ := mty_segment_bounded C0 d L
  refine ⟨d, i, p, hd0, hdom, hstep, hLi, hp, hty, hdem, ?_⟩
  intro hi a
  rw [← hd0]
  rw [show i + a = (i + a - 1) + 1 from by omega]
  exact ppi_chain_below hI d hdom hstep (i + a - 1)

/-- **BUNDLED ascending-kernel data** — `ascKernel`'s output as a `Type`-level
    structure, so it can be DESTRUCTURED inside a (noncomputable) definition (the
    node-set construction needs the chain `c`/period `i,p` as data, not just an
    existential).  Every field is a projection of `ascKernel`'s conjunction. -/
structure AscKernelPack {α : Type} (I : Interp α) (C0 G : Concept) (x0 : α) (L : Nat) where
  c : Nat → α
  i : Nat
  p : Nat
  c0 : c 0 = x0
  dom : ∀ n, I.dom (c n)
  step : ∀ n, I.rho (c n) (c (n + 1)) = pp
  iLE : L ≤ i
  pPos : 0 < p
  period : mty C0 I (c i) = mty C0 I (c (i + p))
  dem : ∀ n, Concept.ex pp G ∈ mty C0 I (c n)
  base : 0 < i → ∀ a, I.rho x0 (c (i + a)) = pp

/-- Extract the bundled kernel data from a `persistPP` node — via
    `Nonempty` + `Classical.choice` (so the existential in `ascKernel` is
    eliminated into a `Type` result legitimately). -/
noncomputable def ascKernelPack (hI : RCC5Interp I) {C0 G : Concept} (x0 : α)
    (h0 : persistPP I C0 G x0) (L : Nat) : AscKernelPack I C0 G x0 L :=
  Classical.choice (by
    obtain ⟨c, i, p, hc0, hdom, hstep, hiLE, hpPos, hperiod, hdem, hbase⟩ :=
      ascKernel hI x0 h0 L
    exact ⟨⟨c, i, p, hc0, hdom, hstep, hiLE, hpPos, hperiod, hdem, hbase⟩⟩)

/-- **KERNEL WITH STABILIZED EXTERNALS** — `AscKernelPack` extended with the
    external-interface data `mixKernel_ok` needs as a SINGLE object.  On top of the
    ascending chain + period, it carries `stab`: every external `e ∈ exts` has a
    phase-INDEPENDENT relation to the chain from `c i` on (`ρ e (c(i+a)) = ρ e (c i)`
    — the external→chain orientation of `mixKernel_ok`'s `hstab`), plus `recur`, the
    cofinal recurrence of every phase type (for the round-robin serving of the
    kernel's own `∃PP`).  This is precisely what makes the "late picking" of the
    period `i` legitimate: past the finite stabilization horizon of `exts`, the
    externals see a constant kernel interface. -/
structure StabKernelPack {α : Type} (I : Interp α) (C0 G : Concept) (x0 : α)
    (exts : List α) (L : Nat) where
  c : Nat → α
  i : Nat
  p : Nat
  c0 : c 0 = x0
  dom : ∀ n, I.dom (c n)
  step : ∀ n, I.rho (c n) (c (n + 1)) = pp
  iLE : L ≤ i
  pPos : 0 < p
  period : mty C0 I (c i) = mty C0 I (c (i + p))
  dem : ∀ n, Concept.ex pp G ∈ mty C0 I (c n)
  stab : ∀ e ∈ exts, ∀ a, I.rho e (c (i + a)) = I.rho e (c i)
  recur : ∀ a, i ≤ a → ∀ N, ∃ m, N ≤ m ∧ mty C0 I (c m) = mty C0 I (c a)

/-- Extract the bundled kernel-with-externals data from a `persistPP` node and a
    finite external list — `persistPP_chain` for the chain, `segment_select` for
    the period + stabilized interface + recurrence (all at once).  The `stab`
    field converts `segment_select`'s chain→external rows into the external→chain
    orientation via `hI.conv_`. -/
noncomputable def stabKernelPack (hI : RCC5Interp I) {C0 G : Concept} (x0 : α)
    (h0 : persistPP I C0 G x0) (exts : List α) (hexts : ∀ e ∈ exts, I.dom e)
    (L : Nat) : StabKernelPack I C0 G x0 exts L :=
  Classical.choice (by
    obtain ⟨c, hc0, hdom, hstep, hdem⟩ := persistPP_chain hI x0 h0
    obtain ⟨i, p, hLi, hp, hty, hstabraw, hrecur⟩ :=
      segment_select hI hdom hstep C0 exts hexts L
    refine ⟨⟨c, i, p, hc0, hdom, hstep, hLi, hp, hty, hdem, ?_, hrecur⟩⟩
    intro e he a
    have h1 : I.rho e (c (i + a)) = conv (I.rho (c (i + a)) e) :=
      hI.conv_ (c (i + a)) e (hdom (i + a)) (hexts e he)
    have h2 : I.rho (c (i + a)) e = I.rho (c i) e := hstabraw e he (i + a) (by omega)
    have h3 : I.rho e (c i) = conv (I.rho (c i) e) :=
      hI.conv_ (c i) e (hdom i) (hexts e he)
    rw [h1, h2, ← h3])

/-- **DESCENDING KERNEL WITH STABILIZED EXTERNALS** — the `dascKernel` mirror of
    `StabKernelPack`, for a `persistPPI` node: a descending `PPI`-chain plus the
    stabilized external interface + recurrence.  Same `stab` orientation
    (external→chain) and same `recur`; `step` is `ppi`.  Together with
    `StabKernelPack` this supplies the per-kernel data `mixKernels_ok` needs for
    kernels of EITHER direction (`dir k`). -/
structure DStabKernelPack {α : Type} (I : Interp α) (C0 G : Concept) (x0 : α)
    (exts : List α) (L : Nat) where
  d : Nat → α
  i : Nat
  p : Nat
  d0 : d 0 = x0
  dom : ∀ n, I.dom (d n)
  step : ∀ n, I.rho (d n) (d (n + 1)) = ppi
  iLE : L ≤ i
  pPos : 0 < p
  period : mty C0 I (d i) = mty C0 I (d (i + p))
  dem : ∀ n, Concept.ex ppi G ∈ mty C0 I (d n)
  stab : ∀ e ∈ exts, ∀ a, I.rho e (d (i + a)) = I.rho e (d i)
  recur : ∀ a, i ≤ a → ∀ N, ∃ m, N ≤ m ∧ mty C0 I (d m) = mty C0 I (d a)

/-- Extract the descending bundled data from a `persistPPI` node + a finite
    external list — `persistPPI_chain` + `dsegment_select`, the exact mirror of
    `stabKernelPack`. -/
noncomputable def dStabKernelPack (hI : RCC5Interp I) {C0 G : Concept} (x0 : α)
    (h0 : persistPPI I C0 G x0) (exts : List α) (hexts : ∀ e ∈ exts, I.dom e)
    (L : Nat) : DStabKernelPack I C0 G x0 exts L :=
  Classical.choice (by
    obtain ⟨d, hd0, hdom, hstep, hdem⟩ := persistPPI_chain hI x0 h0
    obtain ⟨i, p, hLi, hp, hty, hstabraw, hrecur⟩ :=
      dsegment_select hI hdom hstep C0 exts hexts L
    refine ⟨⟨d, i, p, hd0, hdom, hstep, hLi, hp, hty, hdem, ?_, hrecur⟩⟩
    intro e he a
    have h1 : I.rho e (d (i + a)) = conv (I.rho (d (i + a)) e) :=
      hI.conv_ (d (i + a)) e (hdom (i + a)) (hexts e he)
    have h2 : I.rho (d (i + a)) e = I.rho (d i) e := hstabraw e he (i + a) (by omega)
    have h3 : I.rho e (d i) = conv (I.rho (d i) e) :=
      hI.conv_ (d i) e (hdom i) (hexts e he)
    rw [h1, h2, ← h3])

/-! ### Cross-kernel disjointness stabilization (toward `hrectQ`)

`mixKernels_ok`'s `hrectQ` needs the relation between two kernels' chains
constant across all phase-pairs.  The relation `ρ(c m)(d n)` decomposes into
three monotone indicators (disjoint / `c ⊆ d` / `d ⊆ c`); the DISJOINTNESS
indicator is the clean, pure-composition-table one: for two ascending
PP-towers, "overlap" (`≠ DR`) is closed to the NE (both towers only grow), so
disjointness is eventually constant on a NE-quadrant.  This is that brick. -/

/-- Along an ascending `PP`-chain, `c i PP c j` for `i < j`
    (`comp(PP,PP) = {PP}`). -/
theorem chain_pp_lt (hI : RCC5Interp I) (c : Nat → α) (hdom : ∀ n, I.dom (c n))
    (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp) :
    ∀ i j, i < j → I.rho (c i) (c j) = pp := by
  intro i j
  induction j with
  | zero => intro h; exact absurd h (Nat.not_lt_zero i)
  | succ j ih =>
    intro h
    rcases Nat.lt_or_ge i j with hlt | hge
    · have hc := hI.comp_ (c i) (c j) (c (j + 1)) (hdom i) (hdom j) (hdom (j + 1))
      rw [ih hlt, hstep j, show comp pp pp = [pp] from rfl, List.mem_singleton] at hc
      exact hc
    · have hij : i = j := Nat.le_antisymm (Nat.lt_succ_iff.mp h) hge
      subst hij; exact hstep i

/-- Overlap is preserved as the LEFT tower grows (`m ≤ m'`): if `c m` is not
    disjoint from `d n`, neither is the larger `c m'`.  Pure composition:
    `dr ∉ comp(PPI, X)` for every non-`DR` `X`. -/
theorem cross_overlap_mono_m (hI : RCC5Interp I) (c d : Nat → α)
    (hcdom : ∀ n, I.dom (c n)) (hddom : ∀ n, I.dom (d n))
    (hcstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    {m m' n : Nat} (hm : m ≤ m') (h : I.rho (c m) (d n) ≠ dr) :
    I.rho (c m') (d n) ≠ dr := by
  rcases Nat.lt_or_ge m m' with hlt | hge
  · have hppi : I.rho (c m') (c m) = ppi := by
      rw [hI.conv_ (c m) (c m') (hcdom m) (hcdom m'), chain_pp_lt hI c hcdom hcstep m m' hlt]
      rfl
    have hc := hI.comp_ (c m') (c m) (d n) (hcdom m') (hcdom m) (hddom n)
    rw [hppi] at hc
    intro hbad
    rw [hbad] at hc
    generalize hF : I.rho (c m) (d n) = F at hc h
    cases F <;> first | exact h rfl | exact absurd hc (by decide)
  · have hmm : m = m' := Nat.le_antisymm hm hge
    subst hmm; exact h

/-- Overlap is preserved as the RIGHT tower grows (`n ≤ n'`).  Pure
    composition: `dr ∉ comp(X, PP)` for every non-`DR` `X`. -/
theorem cross_overlap_mono_n (hI : RCC5Interp I) (c d : Nat → α)
    (hcdom : ∀ n, I.dom (c n)) (hddom : ∀ n, I.dom (d n))
    (hdstep : ∀ n, I.rho (d n) (d (n + 1)) = pp)
    {m n n' : Nat} (hn : n ≤ n') (h : I.rho (c m) (d n) ≠ dr) :
    I.rho (c m) (d n') ≠ dr := by
  rcases Nat.lt_or_ge n n' with hlt | hge
  · have hc := hI.comp_ (c m) (d n) (d n') (hcdom m) (hddom n) (hddom n')
    rw [chain_pp_lt hI d hddom hdstep n n' hlt] at hc
    intro hbad
    rw [hbad] at hc
    generalize hF : I.rho (c m) (d n) = F at hc h
    cases F <;> first | exact h rfl | exact absurd hc (by decide)
  · have hnn : n = n' := Nat.le_antisymm hn hge
    subst hnn; exact h

/-- Overlap between two ascending `PP`-towers is closed to the NE. -/
theorem cross_overlap_mono (hI : RCC5Interp I) (c d : Nat → α)
    (hcdom : ∀ n, I.dom (c n)) (hddom : ∀ n, I.dom (d n))
    (hcstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    (hdstep : ∀ n, I.rho (d n) (d (n + 1)) = pp)
    {m n m' n' : Nat} (hm : m ≤ m') (hn : n ≤ n') (h : I.rho (c m) (d n) ≠ dr) :
    I.rho (c m') (d n') ≠ dr :=
  cross_overlap_mono_n hI c d hcdom hddom hdstep hn
    (cross_overlap_mono_m hI c d hcdom hddom hcstep hm h)

/-- **DISJOINTNESS STABILIZES** — for two ascending kernels' chains, whether
    they are disjoint is eventually constant on a NE-quadrant.  The `DR`-indicator
    third of `mixKernels_ok`'s `hrectQ` (the `⊆`-indicators, needing the rank
    argument + marginal stabilization, are the remaining two thirds). -/
theorem cross_dr_stabilizes (hI : RCC5Interp I) (c d : Nat → α)
    (hcdom : ∀ n, I.dom (c n)) (hddom : ∀ n, I.dom (d n))
    (hcstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    (hdstep : ∀ n, I.rho (d n) (d (n + 1)) = pp) :
    ∃ N, ∀ m n, N ≤ m → N ≤ n →
      (I.rho (c m) (d n) = dr ↔ I.rho (c N) (d N) = dr) := by
  rcases Classical.em (∃ a b, I.rho (c a) (d b) ≠ dr) with ⟨a, b, hab⟩ | hnone
  · refine ⟨max a b, fun m n hm hn => ?_⟩
    have h1 : I.rho (c m) (d n) ≠ dr :=
      cross_overlap_mono hI c d hcdom hddom hcstep hdstep
        (Nat.le_trans (Nat.le_max_left a b) hm) (Nat.le_trans (Nat.le_max_right a b) hn) hab
    have h2 : I.rho (c (max a b)) (d (max a b)) ≠ dr :=
      cross_overlap_mono hI c d hcdom hddom hcstep hdstep
        (Nat.le_max_left a b) (Nat.le_max_right a b) hab
    exact ⟨fun hh => absurd hh h1, fun hh => absurd hh h2⟩
  · refine ⟨0, fun m n _ _ => ?_⟩
    have hmn : I.rho (c m) (d n) = dr := by
      rcases Classical.em (I.rho (c m) (d n) = dr) with hd | hnd
      · exact hd
      · exact absurd ⟨m, n, hnd⟩ hnone
    have h00 : I.rho (c 0) (d 0) = dr := by
      rcases Classical.em (I.rho (c 0) (d 0) = dr) with hd | hnd
      · exact hd
      · exact absurd ⟨0, 0, hnd⟩ hnone
    exact ⟨fun _ => h00, fun _ => hmn⟩

/-- **PO STABILIZES** — the incomparable-overlap third of `hrectQ` (§36).  If the
    two towers are INCOMPARABLE (each has a "private part": `c i0` is a subregion
    of NO `d j` — `ρ(c i0)(d j) ∉ {PP,EQ}` — and `d j0` a subregion of no `c i` —
    `ρ(c i)(d j0) ≠ PPI`) and OVERLAP (`ρ(c i0)(d j0) ≠ DR`), then `ρ(c i)(d j) =
    PO` for all `i ≥ i0, j ≥ j0` — a CONSTANT `PO` NE-quadrant.  Proved directly
    (no `eta` needed): the private-part conditions PROPAGATE up each tower
    (`c i0 ⊆ c i` and `comp(PP,PP)={PP}` / `eq_id` carry `⊄ d j` from `i0` to `i`;
    dually for `d`), and `≠DR` rides `cross_overlap_mono`; the four exclusions
    leave exactly `PO`.  This is the PO analogue of `cross_dr_stabilizes`. -/
theorem cross_po_stabilizes (hI : RCC5Interp I) (c d : Nat → α)
    (hcdom : ∀ n, I.dom (c n)) (hddom : ∀ n, I.dom (d n))
    (hcstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    (hdstep : ∀ n, I.rho (d n) (d (n + 1)) = pp)
    (i0 j0 : Nat)
    (hc : ∀ j, I.rho (c i0) (d j) ≠ pp ∧ I.rho (c i0) (d j) ≠ eq)
    (hd : ∀ i, I.rho (c i) (d j0) ≠ ppi)
    (ho : I.rho (c i0) (d j0) ≠ dr) :
    ∀ i j, i0 ≤ i → j0 ≤ j → I.rho (c i) (d j) = po := by
  intro i j hi hj
  have hndr : I.rho (c i) (d j) ≠ dr :=
    cross_overlap_mono hI c d hcdom hddom hcstep hdstep hi hj ho
  have hnpp : I.rho (c i) (d j) ≠ pp := by
    intro hpp
    rcases Nat.lt_or_ge i0 i with hlt | hge
    · have hci0i : I.rho (c i0) (c i) = pp := chain_pp_lt hI c hcdom hcstep i0 i hlt
      have hcomp := hI.comp_ (c i0) (c i) (d j) (hcdom i0) (hcdom i) (hddom j)
      rw [hci0i, hpp, show comp pp pp = [pp] from rfl, List.mem_singleton] at hcomp
      exact (hc j).1 hcomp
    · have hii : i0 = i := Nat.le_antisymm hi hge
      exact (hc j).1 (by rw [hii]; exact hpp)
  have hneq : I.rho (c i) (d j) ≠ eq := by
    intro heq
    rcases Nat.lt_or_ge i0 i with hlt | hge
    · have hij : c i = d j := hI.eq_id (c i) (d j) (hcdom i) (hddom j) heq
      have hci0i : I.rho (c i0) (c i) = pp := chain_pp_lt hI c hcdom hcstep i0 i hlt
      rw [hij] at hci0i
      exact (hc j).1 hci0i
    · have hii : i0 = i := Nat.le_antisymm hi hge
      exact (hc j).2 (by rw [hii]; exact heq)
  have hnppi : I.rho (c i) (d j) ≠ ppi := by
    intro hppi
    rcases Nat.lt_or_ge j0 j with hlt | hge
    · have hdj0j : I.rho (d j0) (d j) = pp := chain_pp_lt hI d hddom hdstep j0 j hlt
      have hdjj0 : I.rho (d j) (d j0) = ppi := by
        rw [hI.conv_ (d j0) (d j) (hddom j0) (hddom j), hdj0j]; rfl
      have hcomp := hI.comp_ (c i) (d j) (d j0) (hcdom i) (hddom j) (hddom j0)
      rw [hppi, hdjj0, show comp ppi ppi = [ppi] from rfl, List.mem_singleton] at hcomp
      exact hd i hcomp
    · have hjj : j0 = j := Nat.le_antisymm hj hge
      exact hd i (by rw [hjj]; exact hppi)
  cases hrel : I.rho (c i) (d j) with
  | eq => exact absurd hrel hneq
  | pp => exact absurd hrel hnpp
  | ppi => exact absurd hrel hnppi
  | po => rfl
  | dr => exact absurd hrel hndr

/-- The c-side private-part condition (`c i0 ⊄ any d j`) PROPAGATES UP the
    c-tower: if it holds at `i0` it holds at every `i ≥ i0` (a larger `c i` is
    even less a subregion of `d j`).  Same argument as `cross_po_stabilizes`'s
    `¬PP`/`¬EQ` steps, isolated for the classification's late-witness bump. -/
theorem cprivate_up (hI : RCC5Interp I) (c d : Nat → α)
    (hcdom : ∀ n, I.dom (c n)) (hddom : ∀ n, I.dom (d n))
    (hcstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    {i0 i : Nat} (hii : i0 ≤ i)
    (h : ∀ j, I.rho (c i0) (d j) ≠ pp ∧ I.rho (c i0) (d j) ≠ eq) :
    ∀ j, I.rho (c i) (d j) ≠ pp ∧ I.rho (c i) (d j) ≠ eq := by
  intro j
  refine ⟨fun hpp => ?_, fun heq => ?_⟩
  · rcases Nat.lt_or_ge i0 i with hlt | hge
    · have hci0i : I.rho (c i0) (c i) = pp := chain_pp_lt hI c hcdom hcstep i0 i hlt
      have hcomp := hI.comp_ (c i0) (c i) (d j) (hcdom i0) (hcdom i) (hddom j)
      rw [hci0i, hpp, show comp pp pp = [pp] from rfl, List.mem_singleton] at hcomp
      exact (h j).1 hcomp
    · exact (h j).1 (by rw [Nat.le_antisymm hii hge]; exact hpp)
  · rcases Nat.lt_or_ge i0 i with hlt | hge
    · have hij : c i = d j := hI.eq_id (c i) (d j) (hcdom i) (hddom j) heq
      have hci0i : I.rho (c i0) (c i) = pp := chain_pp_lt hI c hcdom hcstep i0 i hlt
      rw [hij] at hci0i
      exact (h j).1 hci0i
    · exact (h j).2 (by rw [Nat.le_antisymm hii hge]; exact heq)

/-- The d-side private-part condition (`d j0 ⊄ any c i`) propagates up the
    d-tower (mirror of `cprivate_up`). -/
theorem dprivate_up (hI : RCC5Interp I) (c d : Nat → α)
    (hcdom : ∀ n, I.dom (c n)) (hddom : ∀ n, I.dom (d n))
    (hdstep : ∀ n, I.rho (d n) (d (n + 1)) = pp)
    {j0 j : Nat} (hjj : j0 ≤ j)
    (h : ∀ i, I.rho (c i) (d j0) ≠ ppi) :
    ∀ i, I.rho (c i) (d j) ≠ ppi := by
  intro i hppi
  rcases Nat.lt_or_ge j0 j with hlt | hge
  · have hdj0j : I.rho (d j0) (d j) = pp := chain_pp_lt hI d hddom hdstep j0 j hlt
    have hdjj0 : I.rho (d j) (d j0) = ppi := by
      rw [hI.conv_ (d j0) (d j) (hddom j0) (hddom j), hdj0j]; rfl
    have hcomp := hI.comp_ (c i) (d j) (d j0) (hcdom i) (hddom j) (hddom j0)
    rw [hppi, hdjj0, show comp ppi ppi = [ppi] from rfl, List.mem_singleton] at hcomp
    exact h i hcomp
  · exact h i (by rw [Nat.le_antisymm hjj hge]; exact hppi)

/-- **THE CROSS-KERNEL CLASSIFICATION** (§36): for two ascending kernels'
    chains, EXACTLY one of three holds — either the cross-relation is eventually
    CONSTANT (some `v`, on a NE-quadrant — this is `hrectQ` for the pair, `v = PO`
    when incomparable+overlapping via `cross_po_stabilizes`, `v = DR` when
    disjoint), OR one tower EMBEDS in the other (`c i ⊆` some `d j` for every `i`,
    or dually) — the comparable/staircase case that must be MERGED via a shared
    round-robin kernel.  Pure `Classical.em` on the two private-part predicates
    and overlap; the constant-`PO` witness is bumped to a common level
    (`cprivate_up`/`dprivate_up`) so overlap is secured there. -/
theorem classify_cross (hI : RCC5Interp I) (c d : Nat → α)
    (hcdom : ∀ n, I.dom (c n)) (hddom : ∀ n, I.dom (d n))
    (hcstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    (hdstep : ∀ n, I.rho (d n) (d (n + 1)) = pp) :
    (∃ N v, ∀ i j, N ≤ i → N ≤ j → I.rho (c i) (d j) = v)
    ∨ (∀ i, ∃ j, I.rho (c i) (d j) = pp ∨ I.rho (c i) (d j) = eq)
    ∨ (∀ j, ∃ i, I.rho (c i) (d j) = ppi) := by
  rcases Classical.em (∃ i0, ∀ j, I.rho (c i0) (d j) ≠ pp ∧ I.rho (c i0) (d j) ≠ eq)
    with hP | hnP
  · rcases Classical.em (∃ j0, ∀ i, I.rho (c i) (d j0) ≠ ppi) with hQ | hnQ
    · rcases Classical.em (∃ i1 j1, I.rho (c i1) (d j1) ≠ dr) with hov | hnov
      · -- incomparable + overlapping ⟹ constant PO
        obtain ⟨i0, hi0⟩ := hP
        obtain ⟨j0, hj0⟩ := hQ
        obtain ⟨i1, j1, hov1⟩ := hov
        refine Or.inl ⟨max (max i0 i1) (max j0 j1), po, fun i j hi hj => ?_⟩
        have hI0c := cprivate_up hI c d hcdom hddom hcstep (Nat.le_max_left i0 i1) hi0
        have hJ0d := dprivate_up hI c d hcdom hddom hdstep (Nat.le_max_left j0 j1) hj0
        have hoIJ : I.rho (c (max i0 i1)) (d (max j0 j1)) ≠ dr :=
          cross_overlap_mono hI c d hcdom hddom hcstep hdstep
            (Nat.le_max_right i0 i1) (Nat.le_max_right j0 j1) hov1
        exact cross_po_stabilizes hI c d hcdom hddom hcstep hdstep
          (max i0 i1) (max j0 j1) hI0c hJ0d hoIJ i j
          (Nat.le_trans (Nat.le_max_left _ _) hi) (Nat.le_trans (Nat.le_max_right _ _) hj)
      · -- disjoint everywhere ⟹ constant DR
        refine Or.inl ⟨0, dr, fun i j _ _ => ?_⟩
        rcases Classical.em (I.rho (c i) (d j) = dr) with hd | hnd
        · exact hd
        · exact absurd ⟨i, j, hnd⟩ hnov
    · -- ¬Q: every d-level embeds in some c-level (merge d into c)
      refine Or.inr (Or.inr (fun j => ?_))
      rcases Classical.em (∃ i, I.rho (c i) (d j) = ppi) with h | h
      · exact h
      · exact absurd ⟨j, fun i hppi => h ⟨i, hppi⟩⟩ hnQ
  · -- ¬P: every c-level embeds in some d-level (merge c into d)
    refine Or.inr (Or.inl (fun i => ?_))
    rcases Classical.em (∃ j, I.rho (c i) (d j) = pp ∨ I.rho (c i) (d j) = eq) with h | h
    · exact h
    · exact absurd ⟨i, fun j => ⟨fun hpp => h ⟨j, Or.inl hpp⟩, fun heq => h ⟨j, Or.inr heq⟩⟩⟩ hnP

/-- **THE FAMILY `hrectQ` LIFT** — `mixKernels_ok`'s cross-kernel rectangle from
    the pairwise classification.  If every ordered pair `k ≠ k'` has a horizon
    `hN k k'` past which the cross-relation is CONSTANT (`classify_cross`
    disjunct 1, for pairwise-incomparable/disjoint kernels), and every base
    `ik k` is ≥ that horizon (chosen past the joint `max` over the finite `κ`),
    then `hrectQ` holds: both `ρ(ck k (ik k+a))(ck k'(ik k'+b))` and
    `ρ(ck k (ik k))(ck k'(ik k'))` sit in the constant region and collapse to the
    same value.  This is the exact `hrectQ` field `mixKernels_ok` consumes. -/
theorem family_hrectQ {κ : Type} (ck : κ → Nat → α) (ik : κ → Nat)
    (hN : κ → κ → Nat)
    (hconst : ∀ k k', k ≠ k' → ∀ i j, hN k k' ≤ i → hN k k' ≤ j →
      I.rho (ck k i) (ck k' j) = I.rho (ck k (hN k k')) (ck k' (hN k k')))
    (hbk : ∀ k k', k ≠ k' → hN k k' ≤ ik k)
    (hbk' : ∀ k k', k ≠ k' → hN k k' ≤ ik k') :
    ∀ k k', k ≠ k' → ∀ a b,
      I.rho (ck k (ik k + a)) (ck k' (ik k' + b))
        = I.rho (ck k (ik k)) (ck k' (ik k')) := by
  intro k k' hkk a b
  have hk := hbk k k' hkk
  have hk' := hbk' k k' hkk
  rw [hconst k k' hkk (ik k + a) (ik k' + b) (by omega) (by omega),
      hconst k k' hkk (ik k) (ik k') hk hk']

/-- A function on a finite `Fin n` domain is bounded — the base-choice step:
    it lets the extraction pick a single `B` above every per-pair horizon
    `hN k k'`, then set every base `ik k := B` to satisfy `family_hrectQ`'s
    `hbk`/`hbk'`. -/
theorem exists_bound : ∀ (n : Nat) (f : Fin n → Nat), ∃ B, ∀ k, f k ≤ B := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨0, fun k => k.elim0⟩
  | succ n ih =>
    intro f
    obtain ⟨B, hB⟩ := ih (fun i => f i.succ)
    refine ⟨max (f 0) B, fun k => ?_⟩
    refine Fin.cases ?_ ?_ k
    · exact Nat.le_max_left _ _
    · exact fun i => Nat.le_trans (hB i) (Nat.le_max_right _ _)

/-- A function on `Fin n × Fin n` is bounded — the JOINT horizon for
    `family_hrectQ` over a finite kernel family (`κ = Fin n`). -/
theorem exists_bound2 (n : Nat) (f : Fin n → Fin n → Nat) :
    ∃ B, ∀ k k', f k k' ≤ B := by
  obtain ⟨g, hgspec⟩ := Classical.axiomOfChoice (fun k => exists_bound n (f k))
  obtain ⟨B, hB⟩ := exists_bound n g
  exact ⟨B, fun k k' => Nat.le_trans (hgspec k k') (hB k)⟩

/-- **`hrectQ` IS DISCHARGEABLE FOR A FINITE KERNEL FAMILY** — the capstone of
    the `hrectQ` assembly.  For `κ = Fin n` kernels, given a per-pair horizon `hN`
    past which each cross-relation is constant (`classify_cross` disjunct 1),
    there EXIST bases `ik` (every one set to the joint bound `B = max hN`, via
    `exists_bound2`) for which `mixKernels_ok`'s `hrectQ` holds (via
    `family_hrectQ`).  So once the extraction supplies the per-pair constancy for
    pairwise-incomparable/disjoint kernels, `hrectQ` is free. -/
theorem family_hrectQ_bounded {n : Nat} (ck : Fin n → Nat → α) (hN : Fin n → Fin n → Nat)
    (hconst : ∀ k k', k ≠ k' → ∀ i j, hN k k' ≤ i → hN k k' ≤ j →
      I.rho (ck k i) (ck k' j) = I.rho (ck k (hN k k')) (ck k' (hN k k'))) :
    ∃ ik : Fin n → Nat, ∀ k k', k ≠ k' → ∀ a b,
      I.rho (ck k (ik k + a)) (ck k' (ik k' + b))
        = I.rho (ck k (ik k)) (ck k' (ik k')) := by
  obtain ⟨B, hB⟩ := exists_bound2 n hN
  exact ⟨fun _ => B, family_hrectQ ck (fun _ => B) hN hconst
    (fun k k' _ => hB k k') (fun k k' _ => hB k k')⟩

/-- **THE MERGE CORE** (§36): a persistent demand's `∀PP`-guard PROPAGATES UP.
    If `z` is `PP`-above a node `x` carrying `∀PP.(∃PP.D)`, then `z` carries BOTH
    `∃PP.D` (`mty_all`) and the guard itself (`sat_all_pp_up`).  Consequence: a
    node above TWO persistent roots is a `persistAll` node for BOTH demands, so
    round-robin (`rr_covers`) serves them from ONE tower.  This dispels the
    "poset-with-cycles" fear for the merge — comparable towers merge because the
    larger tower ABSORBS the smaller's demand. -/
theorem guard_propagates (hI : RCC5Interp I) {C0 D : Concept} {x z : α}
    (hx : I.dom x) (hz : I.dom z) (hxz : I.rho x z = pp)
    (hguard : Concept.all pp (Concept.ex pp D) ∈ mty C0 I x) :
    Concept.ex pp D ∈ mty C0 I z ∧ sat I z (Concept.all pp (Concept.ex pp D)) :=
  ⟨mty_all hguard hz hxz, sat_all_pp_up hI hx hz hxz (mem_mty.mp hguard).2⟩

/-- **THE MERGE** (§36): a comparability class collapses to ONE round-robin
    kernel.  If a node `z` is `PP`-above a guard-carrier for EVERY demand in `Ds`
    (each `D`'s persistent root sits `PP`-below `z`), then `z` is a `persistAll`
    node for the whole list `Ds` — so `rr_covers` serves all of `Ds` from `z`'s
    single tower by round-robin.  Comparable persistent towers thus MERGE into one
    kernel (the larger tower, whose sufficiently-high node absorbs every demand's
    guard), leaving distinct kernels pairwise incomparable/disjoint —
    `hrectQ`-ready via `classify_cross`/`family_hrectQ_bounded`.  So the merge is
    `guard_propagates` per demand, NOT a poset-with-cycles. -/
theorem merge_persistAll (hI : RCC5Interp I) {C0 : Concept} {Ds : List Concept}
    {z : α} (hz : I.dom z)
    (hguards : ∀ D ∈ Ds, ∃ x, I.dom x ∧ I.rho x z = pp ∧
      Concept.all pp (Concept.ex pp D) ∈ mty C0 I x) :
    persistAll I C0 Ds z := by
  refine ⟨hz, fun D hD => ?_⟩
  obtain ⟨x, hx, hxz, hgx⟩ := hguards D hD
  exact guard_propagates hI hx hz hxz hgx

/-- **THE PAIRWISE MERGE, CONSTRUCTED** — the common upper node exists.  From two
    persistent roots `xc` (demand `Dc`) and `d 0` (demand `Dd`, the base of `d`'s
    tower) and the embedding `xc PP d j0` (`classify_cross` disjunct 2), the node
    `z = d (j0+1)` is `PP`-above BOTH roots (`xc` via `comp(PP,PP)={PP}`, `d 0`
    via `chain_pp_lt`), so `merge_persistAll` makes it a `persistAll` node for
    `[Dc, Dd]`.  This discharges the merge's model-side existence for the pairwise
    case; `rr_covers` then serves both demands from `d`'s tower. -/
theorem merge_pair (hI : RCC5Interp I) {C0 Dc Dd : Concept} {xc : α}
    (hxc : persistPP I C0 Dc xc)
    (d : Nat → α) (hddom : ∀ n, I.dom (d n))
    (hdstep : ∀ n, I.rho (d n) (d (n + 1)) = pp)
    (hxd : Concept.all pp (Concept.ex pp Dd) ∈ mty C0 I (d 0))
    (j0 : Nat) (hemb : I.rho xc (d j0) = pp) :
    persistAll I C0 [Dc, Dd] (d (j0 + 1)) := by
  refine merge_persistAll hI (hddom (j0 + 1)) (fun D hD => ?_)
  rcases List.mem_cons.mp hD with rfl | hD
  · refine ⟨xc, hxc.1, ?_, hxc.2.2⟩
    have hc := hI.comp_ xc (d j0) (d (j0 + 1)) hxc.1 (hddom j0) (hddom (j0 + 1))
    rw [hemb, hdstep j0, show comp pp pp = [pp] from rfl, List.mem_singleton] at hc
    exact hc
  · rcases List.mem_cons.mp hD with rfl | hD
    · exact ⟨d 0, hddom 0, chain_pp_lt hI d hddom hdstep 0 (j0 + 1) (Nat.succ_pos j0), hxd⟩
    · nomatch hD

/-- Bridge `classify_cross`'s embedding output (`ρ x (d j) ∈ {PP,EQ}`) to
    `merge_pair`'s `PP` input: the `EQ` case means `x = d j` (strong-EQ), so
    `x PP d (j+1)`.  So `x` being a subregion of some `d`-node always yields a
    `d`-level STRICTLY above `x`. -/
theorem embed_to_pp (hI : RCC5Interp I) {d : Nat → α}
    (hddom : ∀ n, I.dom (d n)) (hdstep : ∀ n, I.rho (d n) (d (n + 1)) = pp)
    {x : α} (hx : I.dom x) {j0 : Nat}
    (hemb : I.rho x (d j0) = pp ∨ I.rho x (d j0) = eq) :
    ∃ j', I.rho x (d j') = pp := by
  rcases hemb with hpp | heq
  · exact ⟨j0, hpp⟩
  · refine ⟨j0 + 1, ?_⟩
    rw [hI.eq_id x (d j0) hx (hddom j0) heq]
    exact hdstep j0

/-- **EMBEDDING IS TRANSITIVE** (§37) — the key to the partition.  "Tower `c`
    embeds in tower `d`" (`∀ i, ∃ j, ρ(c i)(d j) ∈ {PP,EQ}`, `classify_cross`
    disjunct 2) is a TRANSITIVE preorder: `c ⊆ d ⊆ e ⟹ c ⊆ e`, because
    `comp({PP,EQ},{PP,EQ}) ⊆ {PP,EQ}`.  So although *comparability* (embeds either
    way) is NOT transitive, embedding IS — hence the persistent demands' towers
    form a finite preorder, whose MAXIMAL towers are a dominating antichain (each
    maximal tower serves every tower below it by guard absorption; distinct
    maximal towers are incomparable, so `hrectQ`-ready).  This is why the "merge"
    partition is well-defined. -/
theorem embed_trans (hI : RCC5Interp I) {c d e : Nat → α}
    (hcdom : ∀ n, I.dom (c n)) (hddom : ∀ n, I.dom (d n)) (hedom : ∀ n, I.dom (e n))
    (hcd : ∀ i, ∃ j, I.rho (c i) (d j) = pp ∨ I.rho (c i) (d j) = eq)
    (hde : ∀ j, ∃ k, I.rho (d j) (e k) = pp ∨ I.rho (d j) (e k) = eq) :
    ∀ i, ∃ k, I.rho (c i) (e k) = pp ∨ I.rho (c i) (e k) = eq := by
  intro i
  obtain ⟨j, hij⟩ := hcd i
  obtain ⟨k, hjk⟩ := hde j
  have hcomp := hI.comp_ (c i) (d j) (e k) (hcdom i) (hddom j) (hedom k)
  refine ⟨k, ?_⟩
  rcases hij with h1 | h1 <;> rcases hjk with h2 | h2 <;> rw [h1, h2] at hcomp <;>
    simp only [show comp pp pp = [pp] from rfl, show comp pp eq = [pp] from rfl,
      show comp eq pp = [pp] from rfl, show comp eq eq = [eq] from rfl,
      List.mem_singleton] at hcomp <;>
    (first | exact Or.inl hcomp | exact Or.inr hcomp)

/-! ### Maximal-element domination in a finite preorder (§37.1)

The one abstract order-theory fact the partition needs: in a finite preorder
every element is `≤` a maximal element.  Proved via strong induction on the
count `#{k : le a k}` (a maximal ⟹ done; else a strictly-greater `a'` drops the
count).  Core Lean has no `Finset.exists_maximal` and a preorder has no total
`max`, so the two `List.countP` steps (`countP_mono`, `countP_lt`) are proved
inline. -/

/-- `p a` holds and `a ∈ l` ⟹ `1 ≤ countP p l`. -/
theorem one_le_countP_of_mem {β : Type} (p : β → Bool) {a : β} {l : List β}
    (ha : a ∈ l) (hpa : p a = true) : 1 ≤ l.countP p := by
  induction l with
  | nil => nomatch ha
  | cons b rest ih =>
    rw [List.countP_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [if_pos hpa]; omega
    · have := ih ha; omega

/-- `countP` is monotone: `q ⟹ p` on `l` gives `countP q l ≤ countP p l`. -/
theorem countP_mono {β : Type} (p q : β → Bool) :
    ∀ (l : List β), (∀ x ∈ l, q x = true → p x = true) → l.countP q ≤ l.countP p := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a rest ih =>
    intro h
    rw [List.countP_cons, List.countP_cons]
    have hrest : rest.countP q ≤ rest.countP p :=
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have himpl : q a = true → p a = true := h a (List.mem_cons.mpr (Or.inl rfl))
    have ha : (if q a = true then 1 else 0) ≤ (if p a = true then 1 else 0) := by
      cases hq : q a <;> cases hp : p a <;> simp_all
    omega

/-- Strict version: `q ⟹ p` on `l`, and some `x ∈ l` has `p x` but not `q x`,
    gives `countP q l < countP p l`. -/
theorem countP_lt {β : Type} (p q : β → Bool) :
    ∀ (l : List β), (∀ x ∈ l, q x = true → p x = true) →
      (∃ x ∈ l, p x = true ∧ q x = false) → l.countP q < l.countP p := by
  intro l
  induction l with
  | nil => intro _ hex; obtain ⟨x, hx, _⟩ := hex; nomatch hx
  | cons a rest ih =>
    intro h hex
    rw [List.countP_cons, List.countP_cons]
    have hmono : rest.countP q ≤ rest.countP p :=
      countP_mono p q rest (fun x hx => h x (List.mem_cons_of_mem a hx))
    by_cases hcase : p a = true ∧ q a = false
    · obtain ⟨hpa, hqa⟩ := hcase
      rw [if_pos hpa, if_neg (by rw [hqa]; simp)]
      omega
    · have hexr : ∃ x ∈ rest, p x = true ∧ q x = false := by
        obtain ⟨x, hx, hpx, hqx⟩ := hex
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd ⟨hpx, hqx⟩ hcase
        · exact ⟨x, hx, hpx, hqx⟩
      have hlt : rest.countP q < rest.countP p :=
        ih (fun x hx => h x (List.mem_cons_of_mem a hx)) hexr
      have himpl : q a = true → p a = true := h a (List.mem_cons.mpr (Or.inl rfl))
      have ha : (if q a = true then 1 else 0) ≤ (if p a = true then 1 else 0) := by
        cases hq : q a <;> cases hp : p a <;> simp_all
      omega

/-- **MAXIMAL-ELEMENT DOMINATION** — in a finite preorder (`le` on `Fin n`,
    transitive + reflexive) every element is `≤` a maximal element `m`
    (`∀ k, le m k → le k m`).  This is the abstract fact the partition rests on:
    the demand-towers form a finite preorder (`embed_trans`), so `κ` = the
    maximal towers, and every demand embeds in one. -/
theorem maximal_dominated {n : Nat} (le : Fin n → Fin n → Prop) [DecidableRel le]
    (htrans : ∀ a b c, le a b → le b c → le a c) (hrefl : ∀ a, le a a) :
    ∀ a, ∃ m, le a m ∧ ∀ k, le m k → le k m := by
  have key : ∀ N (a : Fin n),
      (List.finRange n).countP (fun k => decide (le a k)) ≤ N →
      ∃ m, le a m ∧ ∀ k, le m k → le k m := by
    intro N
    induction N with
    | zero =>
      intro a hcnt
      have hpos : 1 ≤ (List.finRange n).countP (fun k => decide (le a k)) :=
        one_le_countP_of_mem _ (List.mem_finRange a) (by simp [hrefl a])
      omega
    | succ N ih =>
      intro a hcnt
      by_cases hmax : ∀ k, le a k → le k a
      · exact ⟨a, hrefl a, hmax⟩
      · have hne : ∃ a', le a a' ∧ ¬ le a' a := by
          rcases Classical.em (∃ a', le a a' ∧ ¬ le a' a) with h | h
          · exact h
          · exfalso; apply hmax; intro k hak
            rcases Classical.em (le k a) with hka | hka
            · exact hka
            · exact absurd ⟨k, hak, hka⟩ h
        obtain ⟨a', haa', hna'a⟩ := hne
        have hlt : (List.finRange n).countP (fun k => decide (le a' k)) <
            (List.finRange n).countP (fun k => decide (le a k)) := by
          apply countP_lt (fun k => decide (le a k)) (fun k => decide (le a' k))
          · intro x _ hx
            simp only [decide_eq_true_eq] at hx ⊢
            exact htrans a a' x haa' hx
          · exact ⟨a, List.mem_finRange a, by simp [hrefl a], by simp [hna'a]⟩
        obtain ⟨m, ha'm, hmax_m⟩ := ih a' (by omega)
        exact ⟨m, htrans a a' m haa' ha'm, hmax_m⟩
  intro a
  exact key _ a (Nat.le_refl _)

/-- **κ = THE MAXIMAL TOWERS** (§37) — `maximal_dominated` instantiated at the
    tower-embedding relation.  For a finite family of ascending towers
    `ck : Fin n → ℕ → α`, every tower `i` embeds in a MAXIMAL tower `j`
    (`∀ a, ∃ b, ρ(ck i a)(ck j b) ∈ {PP,EQ}`, and `j` is maximal: any tower `j`
    embeds in is `≈ j`).  Embedding is a preorder — reflexive by `refl_eq`,
    transitive by `embed_trans` — and `DecidableRel` classically; this is the
    direct application.  So `κ` = the maximal towers is a dominating antichain
    (up to mutual embedding), each serving every tower below it by guard
    absorption. -/
theorem exists_maximal_tower (hI : RCC5Interp I) {n : Nat} (ck : Fin n → Nat → α)
    (hdom : ∀ i m, I.dom (ck i m)) :
    ∀ i, ∃ j,
      (∀ a, ∃ b, I.rho (ck i a) (ck j b) = pp ∨ I.rho (ck i a) (ck j b) = eq) ∧
      (∀ k, (∀ a, ∃ b, I.rho (ck j a) (ck k b) = pp ∨ I.rho (ck j a) (ck k b) = eq) →
            (∀ a, ∃ b, I.rho (ck k a) (ck j b) = pp ∨ I.rho (ck k a) (ck j b) = eq)) := by
  let emb : Fin n → Fin n → Prop := fun i j =>
    ∀ a, ∃ b, I.rho (ck i a) (ck j b) = pp ∨ I.rho (ck i a) (ck j b) = eq
  haveI : DecidableRel emb := fun _ _ => Classical.propDecidable _
  have htrans : ∀ a b c, emb a b → emb b c → emb a c :=
    fun a b c hab hbc => embed_trans hI (hdom a) (hdom b) (hdom c) hab hbc
  have hrefl : ∀ a, emb a a :=
    fun a m => ⟨m, Or.inr (hI.refl_eq (ck a m) (hdom a m))⟩
  exact maximal_dominated emb htrans hrefl

/-- A function on a finite LIST is bounded (list analogue of `exists_bound`). -/
theorem list_bound {β : Type} (f : β → Nat) :
    ∀ (l : List β), ∃ B, ∀ x ∈ l, f x ≤ B := by
  intro l
  induction l with
  | nil => exact ⟨0, fun x hx => nomatch hx⟩
  | cons a rest ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨max (f a) B, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (hB x hx) (Nat.le_max_right _ _)

/-- **THE COMMON UPPER NODE ON A TOWER** (§37) — given a finite list of `roots`
    each `PP`-below tower `d` at level `lvl x` (`ρ x (d (lvl x)) = PP`), the single
    node `d (B+1)` with `B = max lvl` is `PP`-above ALL of them (`comp(PP,PP)={PP}`
    through `d (lvl x) PP d (B+1)`), and `B+1 > 0` so `d 0` is below it too.  This
    is the node `merge_persistAll` needs: one node above every root of the demands
    dominated by a maximal tower — hence a `persistAll` node for the whole
    comparability class. -/
theorem common_upper_on_tower (hI : RCC5Interp I) (d : Nat → α)
    (hddom : ∀ n, I.dom (d n)) (hdstep : ∀ n, I.rho (d n) (d (n + 1)) = pp)
    (roots : List α) (hrdom : ∀ x ∈ roots, I.dom x) (lvl : α → Nat)
    (hlvl : ∀ x ∈ roots, I.rho x (d (lvl x)) = pp) :
    ∃ N, 0 < N ∧ ∀ x ∈ roots, I.rho x (d N) = pp := by
  obtain ⟨B, hB⟩ := list_bound lvl roots
  refine ⟨B + 1, Nat.succ_pos B, fun x hx => ?_⟩
  have hll : I.rho (d (lvl x)) (d (B + 1)) = pp :=
    chain_pp_lt hI d hddom hdstep (lvl x) (B + 1) (by have := hB x hx; omega)
  have hc := hI.comp_ x (d (lvl x)) (d (B + 1)) (hrdom x hx) (hddom (lvl x)) (hddom (B + 1))
  rw [hlvl x hx, hll, show comp pp pp = [pp] from rfl, List.mem_singleton] at hc
  exact hc

/-- **THE CLASS `persistAll` NODE** (§38) — each maximal tower serves its whole
    comparability class.  Given ascending towers `ck` with per-root persistence
    guards, a maximal tower `j`, and the list `below` of demands whose roots embed
    into `j`'s tower, there is a node `ck j N` that is a `persistAll` node for ALL
    of `below`'s demand formulas.  Combines `embed_to_pp` (levels), the level
    function (`classical` `Classical.choose`), `common_upper_on_tower` (the common
    node), and `merge_persistAll` (guard absorption).  So `rr_covers` then serves
    the entire class from `ck j`'s single tower. -/
theorem class_persistAll (hI : RCC5Interp I) {C0 : Concept} {n : Nat}
    (ck : Fin n → Nat → α) (hdom : ∀ i m, I.dom (ck i m))
    (hstep : ∀ i m, I.rho (ck i m) (ck i (m + 1)) = pp)
    (D : Fin n → Concept)
    (hguard : ∀ i, Concept.all pp (Concept.ex pp (D i)) ∈ mty C0 I (ck i 0))
    (j : Fin n) (below : List (Fin n))
    (hbelow : ∀ i ∈ below, ∃ b,
      I.rho (ck i 0) (ck j b) = pp ∨ I.rho (ck i 0) (ck j b) = eq) :
    ∃ N, persistAll I C0 (below.map D) (ck j N) := by
  classical
  let lvl : α → Nat := fun x => if h : ∃ b, I.rho x (ck j b) = pp then Classical.choose h else 0
  have hrdom : ∀ x ∈ below.map (fun i => ck i 0), I.dom x := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hdom i 0
  have hlvl : ∀ x ∈ below.map (fun i => ck i 0), I.rho x (ck j (lvl x)) = pp := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hex : ∃ b, I.rho (ck i 0) (ck j b) = pp := by
      obtain ⟨b, hb⟩ := hbelow i hi
      exact embed_to_pp hI (hdom j) (hstep j) (hdom i 0) hb
    have hlvli : lvl (ck i 0) = Classical.choose hex := dif_pos hex
    rw [hlvli]
    exact Classical.choose_spec hex
  obtain ⟨N, _, hN⟩ := common_upper_on_tower hI (ck j) (hdom j) (hstep j)
    (below.map (fun i => ck i 0)) hrdom lvl hlvl
  refine ⟨N, merge_persistAll hI (hdom j N) (fun Dm hDm => ?_)⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hDm
  exact ⟨ck i 0, hdom i 0, hN (ck i 0) (List.mem_map.mpr ⟨i, hi, rfl⟩), hguard i⟩

/-- **TOWERS FROM PERSISTENT ROOTS** (§38, the input side) — a finite family of
    `persistPP` roots `xs : Fin n → α` (demand `D i`) yields the tower FUNCTION
    `ck : Fin n → ℕ → α` (each `ck i` the ascending `PP`-chain from `xs i`,
    `persistPP_chain` + `Classical.axiomOfChoice` to make it a function).  With
    `ck i 0 = xs i`, the per-root guards `hpersist i` are exactly
    `class_persistAll`/`exists_maximal_tower`'s inputs. -/
theorem towers_from_persistPP (hI : RCC5Interp I) {C0 : Concept} {n : Nat}
    (D : Fin n → Concept) (xs : Fin n → α)
    (hpersist : ∀ i, persistPP I C0 (D i) (xs i)) :
    ∃ ck : Fin n → Nat → α, (∀ i, ck i 0 = xs i) ∧ (∀ i m, I.dom (ck i m)) ∧
      (∀ i m, I.rho (ck i m) (ck i (m + 1)) = pp) := by
  have h : ∀ i, ∃ c : Nat → α, c 0 = xs i ∧ (∀ m, I.dom (c m)) ∧
      (∀ m, I.rho (c m) (c (m + 1)) = pp) := by
    intro i
    obtain ⟨c, hc0, hcdom, hcstep, _⟩ := persistPP_chain hI (xs i) (hpersist i)
    exact ⟨c, hc0, hcdom, hcstep⟩
  obtain ⟨ck, hck⟩ := Classical.axiomOfChoice h
  exact ⟨ck, fun i => (hck i).1, fun i m => (hck i).2.1 m, fun i m => (hck i).2.2 m⟩

/-- **THE CLASS KERNEL** (§38) — a `persistAll` node yields complete round-robin
    kernel data.  From `persistAll I C0 Ds x0`, the round-robin tower `rrPt` is an
    ascending `PP`-chain (`rrPt_dom`/`rrPt_step`) with a period `(i,p)`
    (`rr_segment`) at which every demand in `Ds` is carried at some phase in
    `[i, i+p)` (`rr_covers`).  This is exactly the ascending-kernel data
    `mixKernels_ok` consumes (`ck`, `ik`, `pk`, `hstep`, `hp`, `hty`) plus the
    per-demand serving that its `k_ex` routing needs — one kernel for a whole
    comparability class. -/
theorem class_kernel (hI : RCC5Interp I) {C0 : Concept} (Ds : List Concept)
    (hL : 0 < Ds.length) (x0 : α) (h0 : persistAll I C0 Ds x0) :
    ∃ (c : Nat → α) (i p : Nat),
      (∀ n, I.dom (c n)) ∧ (∀ n, I.rho (c n) (c (n + 1)) = pp) ∧
      0 < i ∧ 0 < p ∧ mty C0 I (c i) = mty C0 I (c (i + p)) ∧
      (∀ k (hk : k < Ds.length), ∃ b, b < p ∧ Ds.get ⟨k, hk⟩ ∈ mty C0 I (c (i + b))) := by
  obtain ⟨i, p, hi, hp, _, hdvd, hty⟩ := rr_segment hI C0 Ds hL x0 h0
  exact ⟨rrPt hI C0 Ds hL x0 h0, i, p, rrPt_dom hI C0 Ds hL x0 h0,
    rrPt_step hI C0 Ds hL x0 h0, hi, hp, hty,
    fun k hk => rr_covers hI C0 Ds hL x0 h0 i p hi hp hdvd k hk⟩

/-! ### §38.1 — the purely-vertical multi-tower certificate

The first `mixKernels_ok` INSTANTIATION: a finite family of persistent towers
(one per maximal tower, §37) with NO externals (`β = Empty`) is a full
`MultiTierOk`.  The one scheduling problem the assembly has to solve is that
`hty` (per-kernel type recurrence) and `hrectQ` (cross-kernel constancy) are
produced by *different* arguments at *different* bases: the pigeonhole picks a
recurrence base, `classify_cross` picks a constancy horizon.  The fix is
`rr_segment_from` — the recurrence base is available past ANY threshold — so
the chain is fixed first, the horizons are joined (`exists_bound2`), and only
then is each base chosen above the joint horizon.  Both obligations then hold at
the same bases.  `hinj` is FREE (`cross_const_ne_eq`), `hstab`/`he_ex` are
vacuous. -/

/-- `rr_segment` with a THRESHOLD: the round-robin recurrence base can be taken
    past any `L0` (the pigeonhole on the sub-sequence at multiples of `L` is
    started at `L0+1` instead of `1`).  This is what lets a single base carry the
    type recurrence AND sit above the cross-kernel constancy horizon. -/
theorem rr_segment_from (hI : RCC5Interp I) (C0 : Concept)
    (Ds : List Concept) (hL : 0 < Ds.length) (x0 : α)
    (h0 : persistAll I C0 Ds x0) (L0 : Nat) :
    ∃ i p, L0 ≤ i ∧ 0 < i ∧ 0 < p ∧ Ds.length ∣ p ∧
      p ≤ (allListsLe (cl C0) (cl C0).length).length * Ds.length ∧
      mty C0 I (rrPt hI C0 Ds hL x0 h0 i) =
      mty C0 I (rrPt hI C0 Ds hL x0 h0 (i + p)) := by
  have hmem : ∀ m, mty C0 I (rrPt hI C0 Ds hL x0 h0 (m * Ds.length)) ∈
      allListsLe (cl C0) (cl C0).length := by
    intro m
    rw [mem_allListsLe]
    exact ⟨by rw [mty]; exact List.length_filter_le _ _,
      fun x hx => by rw [mty] at hx; exact (List.mem_filter.mp hx).1⟩
  obtain ⟨a, b, hLa, hab, hjB, heq⟩ :=
    segment_exists_bounded (allListsLe (cl C0) (cl C0).length)
      (fun m => mty C0 I (rrPt hI C0 Ds hL x0 h0 (m * Ds.length))) hmem (L0 + 1)
  have harith : a * Ds.length + (b - a) * Ds.length = b * Ds.length := by
    rw [← Nat.add_mul, show a + (b - a) = b from by omega]
  have hL1 : 1 ≤ Ds.length := hL
  have hge : a ≤ a * Ds.length := by
    have h := Nat.mul_le_mul (Nat.le_refl a) hL1
    rwa [Nat.mul_one] at h
  refine ⟨a * Ds.length, (b - a) * Ds.length, by omega, Nat.mul_pos (by omega) hL,
    Nat.mul_pos (by omega) hL, ⟨b - a, Nat.mul_comm (b - a) Ds.length⟩, ?_, ?_⟩
  · exact Nat.mul_le_mul (by omega) (Nat.le_refl _)
  · rw [harith]; exact heq

/-- **THE CLASS TOWER** (§38) — `class_kernel` split at the seam the assembly
    needs: the CHAIN `c` is fixed once (it is what `classify_cross` classifies),
    while the base `i` and period `p` are available at ARBITRARILY LATE `L0`,
    with the full round-robin demand coverage stated by MEMBERSHIP (`D ∈ Ds`)
    rather than by index.  So a comparability class contributes one chain, and
    its base is chosen only after the cross-kernel horizons are known. -/
theorem class_tower (hI : RCC5Interp I) {C0 : Concept} (Ds : List Concept)
    (hL : 0 < Ds.length) (x0 : α) (h0 : persistAll I C0 Ds x0) :
    ∃ c : Nat → α, (∀ m, I.dom (c m)) ∧ (∀ m, I.rho (c m) (c (m + 1)) = pp) ∧
      ∀ L0, ∃ i p, L0 ≤ i ∧ 0 < p ∧
        mty C0 I (c i) = mty C0 I (c (i + p)) ∧
        ∀ D ∈ Ds, ∃ b, b < p ∧ D ∈ mty C0 I (c (i + b)) := by
  refine ⟨rrPt hI C0 Ds hL x0 h0, rrPt_dom hI C0 Ds hL x0 h0,
    rrPt_step hI C0 Ds hL x0 h0, fun L0 => ?_⟩
  obtain ⟨i, p, hL0, hi, hp, hdvd, _, hty⟩ := rr_segment_from hI C0 Ds hL x0 h0 L0
  refine ⟨i, p, hL0, hp, hty, fun D hD => ?_⟩
  obtain ⟨jj, hget⟩ := List.get_of_mem hD
  obtain ⟨b, hb, hDb⟩ := rr_covers hI C0 Ds hL x0 h0 i p hi hp hdvd jj.1 jj.2
  exact ⟨b, hb, hget ▸ hDb⟩

/-- A CONSTANT cross-relation between two towers is never `EQ`: strong-EQ
    identity would force `d N = d (N+1)` against the strict `PP` step.  So
    `mixKernels_ok`'s `hinj` (distinct bases) comes FREE for pairwise
    non-comparable kernels — no separate distinctness hypothesis is owed. -/
theorem cross_const_ne_eq (hI : RCC5Interp I) (c d : Nat → α)
    (hcdom : ∀ m, I.dom (c m)) (hddom : ∀ m, I.dom (d m))
    (hdstep : ∀ m, I.rho (d m) (d (m + 1)) = pp)
    (N : Nat) (v : Atom)
    (hconst : ∀ i j, N ≤ i → N ≤ j → I.rho (c i) (d j) = v) : v ≠ eq := by
  intro hv
  have h1 : I.rho (c N) (d N) = eq := by
    rw [hconst N N (Nat.le_refl N) (Nat.le_refl N), hv]
  have h2 : I.rho (c N) (d (N + 1)) = eq := by
    rw [hconst N (N + 1) (Nat.le_refl N) (Nat.le_succ N), hv]
  have e1 : c N = d N := hI.eq_id _ _ (hcdom N) (hddom N) h1
  have hstepeq : I.rho (d N) (d (N + 1)) = eq := by rw [← e1]; exact h2
  rw [hdstep N] at hstepeq
  exact absurd hstepeq (by decide)

/-- **THE KERNEL PHASE NODES** of a `persistPP` node `n` (demand `∃PP.G`): the
    `p` phase elements `c(i), …, c(i+p-1)` of its ascending kernel, as `MTKNode`s
    at `n`'s budget.  These are the κ-internal tower positions whose HORIZONTAL
    demands the coverage must serve as β-externals (their PP relations stay in the
    kernel clauses).  The base-`L` is `1`, so `0 < i` and `n.x PP` every phase. -/
noncomputable def ppPhaseNodes (hI : RCC5Interp I) {C0 G : Concept} (n : MTKNode I C0)
    (hpp : persistPP I C0 G n.x) : List (MTKNode I C0) :=
  let pk := ascKernelPack hI n.x hpp 1
  (List.range pk.p).map (fun a => ⟨pk.c (pk.i + a), n.k, pk.dom (pk.i + a)⟩)

/-- Each phase node's element is a genuine chain position `c(i+a)`, `a < p`. -/
theorem ppPhaseNodes_spec (hI : RCC5Interp I) {C0 G : Concept} (n : MTKNode I C0)
    (hpp : persistPP I C0 G n.x) :
    ∀ m ∈ ppPhaseNodes hI n hpp,
      ∃ a, a < (ascKernelPack hI n.x hpp 1).p ∧
        m.x = (ascKernelPack hI n.x hpp 1).c ((ascKernelPack hI n.x hpp 1).i + a) ∧
        m.k = n.k := by
  intro m hm
  simp only [ppPhaseNodes, List.mem_map, List.mem_range] at hm
  obtain ⟨a, ha, rfl⟩ := hm
  exact ⟨a, ha, rfl, rfl⟩

open Classical in
/-- **THE ASCENDING-MIXED COVERAGE NODE SET** (§31.4, non-nested case).  The
    β-externals reachable from `n`: `n` itself, the horizontal closures of its
    `∃DR`/`∃PO`/`∃EQ` witnesses, and — for a persistent `∃PP` site — the
    horizontal closures of its kernel PHASES' horizontal witnesses.  A phase's own
    `∃PP` (the up-tower demand) is served inside the kernel, so it is NOT recursed
    (that is the non-nested restriction; nested `∃PP.(∃PP.·)` = the
    (budget, demand-mdepth) lexicographic case, deferred).  Every recursive call
    is at budget `n.k − 1`, so termination is the single measure `n.k`. -/
noncomputable def ascNodes (hI : RCC5Interp I) (n : MTKNode I C0) : List (MTKNode I C0) :=
  n :: (mtk C0 I n.x n.k).attach.flatMap
    (fun p => match p with
      | ⟨.ex r c, hF⟩ =>
        if r = dr ∨ r = po ∨ r = eq then ascNodes hI (mtkWitness n hF)
        else if r = pp then
          if hpp : persistPP I C0 c n.x then
            (ppPhaseNodes hI n hpp).flatMap (fun q =>
              (mtk C0 I q.x q.k).attach.flatMap (fun p' => match p' with
                | ⟨.ex r' c', hF'⟩ =>
                  if r' = dr ∨ r' = po ∨ r' = eq then
                    ascNodes hI ⟨(mtkWitness q hF').x, n.k - 1, (mtkWitness q hF').hx⟩
                  else []
                | _ => []))
          else ascNodes hI (mtkWitness n hF)
        else []
      | _ => [])
termination_by n.k
decreasing_by
  · exact mtkWitness_k_lt n hF
  · show n.k - 1 < n.k
    have h1 : mdepth (Concept.ex pp c) ≤ n.k := (mem_mtk.mp hF).2
    have h2 : 1 ≤ mdepth (Concept.ex pp c) := Nat.succ_le_succ (Nat.zero_le _)
    omega
  · exact mtkWitness_k_lt n hF

/-- The root node is in its own ascending-coverage set. -/
theorem self_mem_ascNodes (hI : RCC5Interp I) (n : MTKNode I C0) :
    n ∈ ascNodes hI n := by
  rw [ascNodes]; exact List.mem_cons_self ..

/-- A horizontal (`∃DR`/`∃PO`/`∃EQ`) witness's whole coverage set is contained in
    the parent's — the horizontal-recursion inclusion (the analogue of
    `sub_mtkNodes_witness`, restricted to the non-`pp`/`ppi` branch). -/
theorem sub_ascNodes_hwitness (hI : RCC5Interp I) (n : MTKNode I C0) {r : Atom}
    {c : Concept} (hF : Concept.ex r c ∈ mtk C0 I n.x n.k)
    (hr : r = dr ∨ r = po ∨ r = eq) :
    ∀ m ∈ ascNodes hI (mtkWitness n hF), m ∈ ascNodes hI n := by
  intro m hm
  rw [ascNodes]
  refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨⟨Concept.ex r c, hF⟩,
    List.mem_attach _ _, ?_⟩)
  simp only [if_pos hr]
  exact hm

/-- A phase-witness's whole coverage set is contained in the parent's — the
    VERTICAL-branch inclusion (for a persistent `∃PP` site's kernel phase's
    horizontal witness). -/
theorem sub_ascNodes_phasewitness (hI : RCC5Interp I) (n : MTKNode I C0) {c : Concept}
    (hF : Concept.ex pp c ∈ mtk C0 I n.x n.k) (hpp : persistPP I C0 c n.x)
    {q : MTKNode I C0} (hq : q ∈ ppPhaseNodes hI n hpp)
    {r' : Atom} {c' : Concept} (hF' : Concept.ex r' c' ∈ mtk C0 I q.x q.k)
    (hr' : r' = dr ∨ r' = po ∨ r' = eq) :
    ∀ m ∈ ascNodes hI ⟨(mtkWitness q hF').x, n.k - 1, (mtkWitness q hF').hx⟩,
      m ∈ ascNodes hI n := by
  intro m hm
  rw [ascNodes]
  refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨⟨Concept.ex pp c, hF⟩,
    List.mem_attach _ _, ?_⟩)
  simp only [if_neg (show ¬ (pp = dr ∨ pp = po ∨ pp = eq) by decide), dif_pos hpp]
  exact List.mem_flatMap.mpr ⟨q, hq, List.mem_flatMap.mpr ⟨⟨Concept.ex r' c', hF'⟩,
    List.mem_attach _ _, by simp only [if_pos hr']; exact hm⟩⟩

/-- A ONE-SHOT `∃PP` witness's coverage set is contained in the parent's (the
    `r = pp`, non-`persistPP` branch — the finite-tower witness). -/
theorem sub_ascNodes_oneshot (hI : RCC5Interp I) (x : MTKNode I C0) {c : Concept}
    (hF : Concept.ex pp c ∈ mtk C0 I x.x x.k) (hnp : ¬ persistPP I C0 c x.x) :
    ∀ m ∈ ascNodes hI (mtkWitness x hF), m ∈ ascNodes hI x := by
  intro m hm
  rw [ascNodes]
  refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨⟨Concept.ex pp c, hF⟩,
    List.mem_attach _ _, ?_⟩)
  simp only [if_neg (show ¬ (pp = dr ∨ pp = po ∨ pp = eq) by decide), dif_neg hnp]
  exact hm

/-- **TRANSITIVITY of the ascending-coverage set**: the coverage set of any
    reachable node is contained in the root's.  Case-splits the three recursion
    branches (horizontal / one-shot `∃PP` / persistent-`∃PP` phase) and applies
    the matching inclusion lemma + IH (`ih2` = the `mtkWitness` recursion,
    `ih1` = the phase-witness recursion, from `ascNodes.induct`). -/
theorem ascNodes_trans (hI : RCC5Interp I) (n : MTKNode I C0) :
    ∀ m ∈ ascNodes hI n, ∀ k ∈ ascNodes hI m, k ∈ ascNodes hI n := by
  induction n using ascNodes.induct with
  | case1 x ih2 ih1 =>
    intro m hm k hk
    rw [ascNodes] at hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact hk
    · obtain ⟨⟨F, hF⟩, _, hmm⟩ := List.mem_flatMap.mp hm'
      cases F with
      | ex r c =>
        simp only at hmm
        by_cases hr : r = dr ∨ r = po ∨ r = eq
        · rw [if_pos hr] at hmm
          exact sub_ascNodes_hwitness hI x hF hr k (ih2 r c hF m hmm k hk)
        · rw [if_neg hr] at hmm
          by_cases hrpp : r = pp
          · rw [if_pos hrpp] at hmm
            subst hrpp
            by_cases hpp : persistPP I C0 c x.x
            · rw [dif_pos hpp] at hmm
              obtain ⟨q, hq, hmq⟩ := List.mem_flatMap.mp hmm
              obtain ⟨⟨F', hF'⟩, _, hmm'⟩ := List.mem_flatMap.mp hmq
              cases F' with
              | ex r' c' =>
                simp only at hmm'
                by_cases hr' : r' = dr ∨ r' = po ∨ r' = eq
                · rw [if_pos hr'] at hmm'
                  exact sub_ascNodes_phasewitness hI x hF hpp hq hF' hr' k
                    (ih1 pp c hF q r' c' hF' m hmm' k hk)
                · rw [if_neg hr'] at hmm'; simp at hmm'
              | top => simp at hmm'
              | bot => simp at hmm'
              | atom a => simp at hmm'
              | natom a => simp at hmm'
              | and a b => simp at hmm'
              | or a b => simp at hmm'
              | all r'' c'' => simp at hmm'
            · rw [dif_neg hpp] at hmm
              exact sub_ascNodes_oneshot hI x hF hpp k (ih2 pp c hF m hmm k hk)
          · rw [if_neg hrpp] at hmm; simp at hmm
      | top => simp at hmm
      | bot => simp at hmm
      | atom a => simp at hmm
      | natom a => simp at hmm
      | and a b => simp at hmm
      | or a b => simp at hmm
      | all r c => simp at hmm

/-- **HORIZONTAL COVERAGE of the ascending-coverage set**: every `∃DR`/`∃PO`/`∃EQ`
    demand at a reachable node is fulfilled by a node in the SAME set (its model
    witness) — the `he_ex` horizontal disjunct (analogue of `mtkNodesH_covers`).
    The witness `mtkWitness m hF` lies in `ascNodes m` (self-membership through the
    horizontal branch) and hence in `ascNodes root` by transitivity.  (The
    VERTICAL `∃PP` demands are served by the kernels, not by β-externals.) -/
theorem ascNodes_covers (hI : RCC5Interp I) (root : MTKNode I C0) :
    ∀ m ∈ ascNodes hI root, ∀ (r : Atom) (c : Concept),
      Concept.ex r c ∈ mtk C0 I m.x m.k → (r = dr ∨ r = po ∨ r = eq) →
      ∃ m' ∈ ascNodes hI root,
        I.rho m.x m'.x = r ∧ c ∈ mtk C0 I m'.x m'.k := by
  intro m hm r c hF hr
  refine ⟨mtkWitness m hF, ?_, mtkWitness_rho m hF, mtkWitness_arg m hF⟩
  exact ascNodes_trans hI root m hm _
    (sub_ascNodes_hwitness hI m hF hr _ (self_mem_ascNodes hI (mtkWitness m hF)))

/-- **PHASE-HORIZONTAL COVERAGE**: a kernel PHASE's `∃DR`/`∃PO`/`∃EQ` demand is
    fulfilled by a node in `ascNodes root` (its model witness) — the `hk_ex`
    horizontal disjunct.  The phase-witness lies in `ascNodes m` (via
    `sub_ascNodes_phasewitness` + self-membership) and hence in `ascNodes root` by
    transitivity; `ppPhaseNodes_spec` bridges `q.k = m.k` for the argument. -/
theorem ascNodes_covers_phase (hI : RCC5Interp I) (root : MTKNode I C0)
    {m : MTKNode I C0} (hm : m ∈ ascNodes hI root) {c : Concept}
    (hF : Concept.ex pp c ∈ mtk C0 I m.x m.k) (hpp : persistPP I C0 c m.x)
    {q : MTKNode I C0} (hq : q ∈ ppPhaseNodes hI m hpp)
    {r' : Atom} {c' : Concept} (hF' : Concept.ex r' c' ∈ mtk C0 I q.x q.k)
    (hr' : r' = dr ∨ r' = po ∨ r' = eq) :
    ∃ w ∈ ascNodes hI root, I.rho q.x w.x = r' ∧ c' ∈ mtk C0 I w.x w.k := by
  obtain ⟨_, _, _, hqk⟩ := ppPhaseNodes_spec hI m hpp q hq
  refine ⟨⟨(mtkWitness q hF').x, m.k - 1, (mtkWitness q hF').hx⟩, ?_,
    mtkWitness_rho q hF', ?_⟩
  · exact ascNodes_trans hI root m hm _
      (sub_ascNodes_phasewitness hI m hF hpp hq hF' hr' _
        (self_mem_ascNodes hI ⟨(mtkWitness q hF').x, m.k - 1, (mtkWitness q hF').hx⟩))
  · show c' ∈ mtk C0 I (mtkWitness q hF').x (m.k - 1)
    rw [← hqk]; exact mtkWitness_arg q hF'

open Classical in
/-- **`hee` for the AscMix node set** — the β-β `∀`-propagation over the
    `sAdjK` (DR/PO) skeleton on `{n // n ∈ ascNodes root}`.  Same proof as
    `mtk_ee_all` (node-set-agnostic: `∀EQ` reflexive, `∀DR` fwd/rev via
    `mtk_all_fwd`/`mtk_all_dr_rev`, `∀PO` vacuous by `∀PO`-freeness) — the
    `hee` hypothesis for the AscMix `extract_dr_children` assembly. -/
theorem ascNodes_ee_all (hI : RCC5Interp I) {C0 : Concept} (hpofree : POFree C0)
    (root : MTKNode I C0) (e f : {n // n ∈ ascNodes hI root}) (r : Atom)
    (c : Concept) (hall : Concept.all r c ∈ mtk C0 I e.val.x e.val.k)
    (hEf : (if e = f then eq else if decide (sAdjK e.val f.val) then dr else po) = r) :
    c ∈ mtk C0 I f.val.x f.val.k := by
  by_cases hef : e = f
  · subst hef
    rw [if_pos rfl] at hEf
    subst hEf
    exact mtk_all_eq hI hall e.val.hx
  · rw [if_neg hef] at hEf
    by_cases hd : decide (sAdjK e.val f.val) = true
    · have hrdr : dr = r := (if_pos hd).symm.trans hEf
      subst hrdr
      have hall' : Concept.all dr c ∈ mtk C0 I e.val.x e.val.k := hall
      rcases of_decide_eq_true hd with ⟨_, hF, hchild⟩ | ⟨_, hF, hchild⟩
      · show c ∈ mtk C0 I f.val.x f.val.k
        rw [← hchild]
        exact mtk_all_fwd hall' (mtkWitness e.val hF).hx (mtkWitness_rho e.val hF)
      · show c ∈ mtk C0 I f.val.x f.val.k
        rw [← hchild] at hall'
        exact mtk_all_dr_rev hI hall' f.val.hx (mtkWitness f.val hF).hx
          (mtkWitness_rho f.val hF)
    · have hrpo : po = r := (if_neg hd).symm.trans hEf
      exact absurd hrpo.symm (pofree_cl_all C0 hpofree r c (mtk_sub_cl _ hall))

/-- **THE MIXED DR/PO SKELETON** for the AscMix assembly: `DR` between two nodes
    that are `DR`-related in the model AND at CONSECUTIVE budgets (`k ± 1`).  This
    captures BOTH the horizontal `DR`-children AND the phase-`∃DR` witnesses (all
    at `base.k − 1`, `DR` to the base by `comp(PP,DR)={DR}`), while a deeper
    `DR`-relative gets a composition-consistent `PO`-default edge.  Symmetric by
    construction (`DR` is self-converse, the budget guard is symmetric). -/
def ascDadj (hI : RCC5Interp I) {C0 : Concept} {root : MTKNode I C0}
    (e f : {n // n ∈ ascNodes hI root}) : Bool :=
  (decide (I.rho e.val.x f.val.x = dr) || decide (I.rho f.val.x e.val.x = dr)) &&
    (decide (f.val.k + 1 = e.val.k) || decide (e.val.k + 1 = f.val.k))

theorem ascDadj_symm (hI : RCC5Interp I) {C0 : Concept} {root : MTKNode I C0}
    (e f : {n // n ∈ ascNodes hI root}) : ascDadj hI e f = ascDadj hI f e := by
  unfold ascDadj; ac_rfl

open Classical in
/-- **`hee` for the AscMix assembly** over the `ascDadj` skeleton: the β-β
    `∀`-propagation.  `∀EQ` reflexive; `∀DR` via `mty_all` + the UNIFORM budget
    bound `mdepth c ≤ e.k − 1 ≤ f.k` (holds for BOTH consecutive-budget
    directions); `∀PO` vacuous by `∀PO`-freeness.  The consecutive-budget guard is
    exactly what makes the `mty_all` route sound (deeper `DR`-relatives are
    `PO`-default, not fired on). -/
theorem ascNodes_ee_all2 (hI : RCC5Interp I) {C0 : Concept} (hpofree : POFree C0)
    (root : MTKNode I C0) (e f : {n // n ∈ ascNodes hI root}) (r : Atom)
    (c : Concept) (hall : Concept.all r c ∈ mtk C0 I e.val.x e.val.k)
    (hEf : (if e = f then eq else if ascDadj hI e f then dr else po) = r) :
    c ∈ mtk C0 I f.val.x f.val.k := by
  by_cases hef : e = f
  · subst hef; rw [if_pos rfl] at hEf; subst hEf; exact mtk_all_eq hI hall e.val.hx
  · rw [if_neg hef] at hEf
    by_cases hd : ascDadj hI e f = true
    · rw [if_pos hd] at hEf
      subst hEf
      simp only [ascDadj, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hd
      obtain ⟨hrho, hbud⟩ := hd
      have hrhoef : I.rho e.val.x f.val.x = dr := by
        rcases hrho with h | h
        · exact h
        · rw [hI.conv_ f.val.x e.val.x f.val.hx e.val.hx, h]; rfl
      have hcmty : c ∈ mty C0 I f.val.x :=
        mty_all (mem_mtk.mp hall).1 f.val.hx hrhoef
      have hmd2 : mdepth c + 1 ≤ e.val.k := (mem_mtk.mp hall).2
      refine mem_mtk.mpr ⟨hcmty, ?_⟩
      rcases hbud with h | h <;> omega
    · rw [if_neg hd] at hEf
      exact absurd hEf.symm (pofree_cl_all C0 hpofree r c (mtk_sub_cl _ hall))

/-- **THE GENERIC MERGED KERNEL** (§25.4 step 2 — `mixCert_ok` generalized off
    `Imix`/`Cmix`): a `MultiTier` with an ARBITRARY external family `g : β → α`
    (full `mty` labels) PLUS a SINGLE ascending kernel (the tower `c`).  Every
    edge value is read off the model — `E` among externals, `K` external↔base,
    `Q` the (diagonal) base.  This is the externals-with-kernel shape that
    complements `vkernel2`'s kernels-only shape. -/
noncomputable def mixKernel (I : Interp α) (C0 : Concept) {β : Type}
    (g : β → α) (c : Nat → α) (i p : Nat) : MultiTier β Unit where
  E := fun e f => I.rho (g e) (g f)
  K := fun _ e => I.rho (c i) (g e)
  Q := fun _ _ => I.rho (c i) (c i)
  up := fun _ => true
  tauE := fun e => mty C0 I (g e)
  p := fun _ => p
  phase := fun _ a => mty C0 I (c (i + a))

/-- **THE MERGED CERTIFICATE IS VALID** — the crux merge of `mtHF_ok`'s
    external handling and `vkernel1G_ok`'s kernel handling.  `ee_all` is pure
    `mty_all` (universal closure of `mty`, so C0-general — no `POFree` needed
    here; ∀PO-freeness is what makes the demand hypotheses SATISFIABLE in the
    extraction, not what the soundness needs).  The cross-fields
    `ek_all`/`ke_all` ride the external↔chain STABILIZATION `hstab` (each
    external's relation to the chain is phase-independent — the "all-phase"
    condition the extraction guarantees by late picking); `kq_all` is vacuous
    (single kernel).  Demands are routed in the `e_ex`/`k_ex` disjunction
    shape via the hypotheses `he_ex`/`hk_ex`. -/
theorem mixKernel_ok (hI : RCC5Interp I) (C0 : Concept)
    {β : Type} (g : β → α) (hgdom : ∀ e, I.dom (g e))
    (c : Nat → α) (hdom : ∀ n, I.dom (c n))
    (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    (i p : Nat) (hp : 0 < p)
    (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    (hstab : ∀ e a, I.rho (g e) (c (i + a)) = I.rho (g e) (c i))
    (hinj : ∀ v w : β ⊕ Unit,
      Sum.elim g (fun _ : Unit => c i) v
        = Sum.elim g (fun _ : Unit => c i) w → v = w)
    (he_ex : ∀ e r D, Concept.ex r D ∈ mty C0 I (g e) →
      (∃ f, I.rho (g e) (g f) = r ∧ D ∈ mty C0 I (g f)) ∨
      (conv (I.rho (c i) (g e)) = r ∧ ∃ b, b < p ∧ D ∈ mty C0 I (c (i + b))))
    (hk_ex : ∀ a r D, Concept.ex r D ∈ mty C0 I (c (i + a)) →
      (∃ f, I.rho (c i) (g f) = r ∧ D ∈ mty C0 I (g f)) ∨
      (r = pp ∧ ∃ b, b < p ∧ D ∈ mty C0 I (c (i + b))) ∨
      (r = eq ∧ D ∈ mty C0 I (c (i + a)))) :
    MultiTierOk (mixKernel I C0 g c i p) := by
  refine
    { hp := fun _ => hp
      frame_q := readoff_qnet_frame hI g (fun _ : Unit => c i)
        hgdom (fun _ => hdom i) hinj
      e_clash := fun _ _ h => mty_clash h
      e_nobot := fun _ => mty_nobot
      e_and := fun _ _ _ h => mty_and h
      e_or := fun _ _ _ h => mty_or h
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := fun _ f _ _ hmem hEr => mty_all hmem (hgdom f) hEr
      ek_all := ?_
      ke_all := ?_
      kk_pp := fun _ a ha E hE b hb => segment_kk_pp hI hdom hstep hty ha hE b hb
      kk_ppi := fun _ a ha E hE b hb => segment_kk_ppi hI hdom hstep hty ha hE b hb
      kk_eq := fun _ a _ E hE =>
        mty_all hE (hdom (i + a)) (hI.refl_eq (c (i + a)) (hdom (i + a)))
      kq_all := fun _ _ hne => absurd rfl hne
      e_ex := ?_
      k_ex := ?_ }
  · -- ek_all: external `∀r.X`, `conv(K k e) = r` ⟹ every phase, via `hstab`
    intro e r X hmem k hr a _
    apply mty_all hmem (hdom (i + a))
    rw [hstab e a, hI.conv_ (c i) (g e) (hdom i) (hgdom e)]
    exact hr
  · -- ke_all: phase `∀r.X`, `K k f = r` ⟹ external `f`, via `hstab`
    intro k a _ r X hmem f hr
    apply mty_all hmem (hgdom f)
    rw [hI.conv_ (g f) (c (i + a)) (hgdom f) (hdom (i + a)), hstab f a,
      ← hI.conv_ (g f) (c i) (hgdom f) (hdom i)]
    exact hr
  · -- e_ex: horizontal child (external) or into the kernel
    intro e r X hmem
    rcases he_ex e r X hmem with ⟨f, hEf, hXf⟩ | ⟨hK, b, hb, hXb⟩
    · exact Or.inl ⟨f, hEf, hXf⟩
    · exact Or.inr ⟨(), hK, b, hb, hXb⟩
  · -- k_ex: external child, up the chain (`cdir true = pp`), or reflexive `eq`
    intro k a _ r X hmem
    rcases hk_ex a r X hmem with ⟨f, hKf, hXf⟩ | ⟨rfl, b, hb, hXb⟩ | ⟨rfl, hX⟩
    · exact Or.inl ⟨f, hKf, hXf⟩
    · exact Or.inr (Or.inl ⟨rfl, b, hb, hXb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hX⟩))

/-- **THE GENERIC MERGED KERNEL, DESCENDING** (`mixKernel` mirror, `up = false`):
    arbitrary externals `g : β → α` plus a SINGLE descending kernel (`c` a
    `PPI`-chain, `cdir false = ppi`).  Same read-off shape as `mixKernel`. -/
noncomputable def mixKernelI (I : Interp α) (C0 : Concept) {β : Type}
    (g : β → α) (c : Nat → α) (i p : Nat) : MultiTier β Unit where
  E := fun e f => I.rho (g e) (g f)
  K := fun _ e => I.rho (c i) (g e)
  Q := fun _ _ => I.rho (c i) (c i)
  up := fun _ => false
  tauE := fun e => mty C0 I (g e)
  p := fun _ => p
  phase := fun _ a => mty C0 I (c (i + a))

/-- **THE DESCENDING MERGED CERTIFICATE IS VALID** — mirror of `mixKernel_ok`
    with `up = false`, the descending segment lemmas (`dsegment_kk_pp/ppi`), and
    the chain serving `∃PPI` (`cdir false = ppi`).  The cross-fields
    `ek_all`/`ke_all` are IDENTICAL to the ascending case: they ride only
    `hstab` and `hI.conv_`, never mentioning the chain direction. -/
theorem mixKernelI_ok (hI : RCC5Interp I) (C0 : Concept)
    {β : Type} (g : β → α) (hgdom : ∀ e, I.dom (g e))
    (c : Nat → α) (hdom : ∀ n, I.dom (c n))
    (hstep : ∀ n, I.rho (c n) (c (n + 1)) = ppi)
    (i p : Nat) (hp : 0 < p)
    (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    (hstab : ∀ e a, I.rho (g e) (c (i + a)) = I.rho (g e) (c i))
    (hinj : ∀ v w : β ⊕ Unit,
      Sum.elim g (fun _ : Unit => c i) v
        = Sum.elim g (fun _ : Unit => c i) w → v = w)
    (he_ex : ∀ e r D, Concept.ex r D ∈ mty C0 I (g e) →
      (∃ f, I.rho (g e) (g f) = r ∧ D ∈ mty C0 I (g f)) ∨
      (conv (I.rho (c i) (g e)) = r ∧ ∃ b, b < p ∧ D ∈ mty C0 I (c (i + b))))
    (hk_ex : ∀ a r D, Concept.ex r D ∈ mty C0 I (c (i + a)) →
      (∃ f, I.rho (c i) (g f) = r ∧ D ∈ mty C0 I (g f)) ∨
      (r = ppi ∧ ∃ b, b < p ∧ D ∈ mty C0 I (c (i + b))) ∨
      (r = eq ∧ D ∈ mty C0 I (c (i + a)))) :
    MultiTierOk (mixKernelI I C0 g c i p) := by
  refine
    { hp := fun _ => hp
      frame_q := readoff_qnet_frame hI g (fun _ : Unit => c i)
        hgdom (fun _ => hdom i) hinj
      e_clash := fun _ _ h => mty_clash h
      e_nobot := fun _ => mty_nobot
      e_and := fun _ _ _ h => mty_and h
      e_or := fun _ _ _ h => mty_or h
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := fun _ f _ _ hmem hEr => mty_all hmem (hgdom f) hEr
      ek_all := ?_
      ke_all := ?_
      kk_pp := fun _ a ha E hE b hb => dsegment_kk_pp hI hdom hstep hty ha hE b hb
      kk_ppi := fun _ a ha E hE b hb => dsegment_kk_ppi hI hdom hstep hty ha hE b hb
      kk_eq := fun _ a _ E hE =>
        mty_all hE (hdom (i + a)) (hI.refl_eq (c (i + a)) (hdom (i + a)))
      kq_all := fun _ _ hne => absurd rfl hne
      e_ex := ?_
      k_ex := ?_ }
  · intro e r X hmem k hr a _
    apply mty_all hmem (hdom (i + a))
    rw [hstab e a, hI.conv_ (c i) (g e) (hdom i) (hgdom e)]
    exact hr
  · intro k a _ r X hmem f hr
    apply mty_all hmem (hgdom f)
    rw [hI.conv_ (g f) (c (i + a)) (hgdom f) (hdom (i + a)), hstab f a,
      ← hI.conv_ (g f) (c i) (hgdom f) (hdom i)]
    exact hr
  · intro e r X hmem
    rcases he_ex e r X hmem with ⟨f, hEf, hXf⟩ | ⟨hK, b, hb, hXb⟩
    · exact Or.inl ⟨f, hEf, hXf⟩
    · exact Or.inr ⟨(), hK, b, hb, hXb⟩
  · intro k a _ r X hmem
    rcases hk_ex a r X hmem with ⟨f, hKf, hXf⟩ | ⟨rfl, b, hb, hXb⟩ | ⟨rfl, hX⟩
    · exact Or.inl ⟨f, hKf, hXf⟩
    · exact Or.inr (Or.inl ⟨rfl, b, hb, hXb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hX⟩))

/-- **THE FULL MULTI-KERNEL MERGE** (§25.4 step 2, general form): arbitrary
    externals `g : β → α` (full `mty` labels) PLUS a family of kernels
    `ck : κ → ℕ → α`, each with its own base `ik k`, period `pk k`, and
    DIRECTION `dir k` (ascending `PP` / descending `PPI`).  Every edge read off
    the model — `E` among externals, `K` each base↔external, `Q` between the
    bases.  Generalizes both `mixKernel` (κ = Unit) and `vkernel2` (β = Empty),
    with the cross-kernel field `kq_all` NON-vacuous. -/
noncomputable def mixKernels (I : Interp α) (C0 : Concept) {β κ : Type}
    (g : β → α) (ck : κ → Nat → α) (ik pk : κ → Nat) (dir : κ → Bool) :
    MultiTier β κ where
  E := fun e f => I.rho (g e) (g f)
  K := fun k e => I.rho (ck k (ik k)) (g e)
  Q := fun k k' => I.rho (ck k (ik k)) (ck k' (ik k'))
  up := dir
  tauE := fun e => mty C0 I (g e)
  p := pk
  phase := fun k a => mty C0 I (ck k (ik k + a))

/-- **THE FULL MULTI-KERNEL MERGE IS VALID.**  Combines `mixKernel_ok`'s
    external↔kernel handling (`ek_all`/`ke_all` via the per-kernel
    stabilization `hstab`) with `vkernel2_ok`'s cross-kernel handling
    (`kq_all` via the rectangle condition `hrectQ` — the cross-kernel relation
    is constant across all phase-pairs).  `kk_pp`/`kk_ppi` branch on the
    kernel's `dir` (ascending `segment_*` / descending `dsegment_*`).  Demands
    are routed in the FULL `e_ex`/`k_ex` disjunction shape — `k_ex` now
    including the cross-kernel disjunct (a phase demand served by ANOTHER
    kernel).  Still C0-general (no `POFree` needed for soundness).

    **`hstab` is on the PHASE WINDOW** (`a < pk k`), not on the whole chain
    (§39.4).  The unrestricted form was strictly too strong to be discharged by
    the extraction's own machinery: `kernel_site` produces phase-witnesses with
    the constant row `∀ b ≤ p, ρ (c (i+b)) w = r` — a WINDOW fact, since such a
    witness is picked above the segment and the chain may later swallow it. The
    field is used only at `a < pk k` in `ek_all`/`ke_all`, so the window form
    costs nothing and admits those witnesses.  Pre-known externals still supply
    the stronger unrestricted form via `StabKernelPack.stab`. -/
theorem mixKernels_ok [DecidableEq κ] (hI : RCC5Interp I) (C0 : Concept)
    {β : Type} (g : β → α) (hgdom : ∀ e, I.dom (g e))
    (ck : κ → Nat → α) (hdom : ∀ k n, I.dom (ck k n))
    (ik pk : κ → Nat) (dir : κ → Bool)
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = cdir (dir k))
    (hp : ∀ k, 0 < pk k)
    (hty : ∀ k, mty C0 I (ck k (ik k)) = mty C0 I (ck k (ik k + pk k)))
    (hstab : ∀ k e a, a < pk k →
      I.rho (g e) (ck k (ik k + a)) = I.rho (g e) (ck k (ik k)))
    (hrectQ : ∀ k k', k ≠ k' → ∀ a b,
      I.rho (ck k (ik k + a)) (ck k' (ik k' + b))
        = I.rho (ck k (ik k)) (ck k' (ik k')))
    (hinj : ∀ v w : β ⊕ κ,
      Sum.elim g (fun k => ck k (ik k)) v
        = Sum.elim g (fun k => ck k (ik k)) w → v = w)
    (he_ex : ∀ e r D, Concept.ex r D ∈ mty C0 I (g e) →
      (∃ f, I.rho (g e) (g f) = r ∧ D ∈ mty C0 I (g f)) ∨
      (∃ k, conv (I.rho (ck k (ik k)) (g e)) = r ∧
        ∃ b, b < pk k ∧ D ∈ mty C0 I (ck k (ik k + b))))
    (hk_ex : ∀ k a r D, Concept.ex r D ∈ mty C0 I (ck k (ik k + a)) →
      (∃ f, I.rho (ck k (ik k)) (g f) = r ∧ D ∈ mty C0 I (g f)) ∨
      (r = cdir (dir k) ∧ ∃ b, b < pk k ∧ D ∈ mty C0 I (ck k (ik k + b))) ∨
      (r = eq ∧ D ∈ mty C0 I (ck k (ik k + a))) ∨
      (∃ k', k ≠ k' ∧ I.rho (ck k (ik k)) (ck k' (ik k')) = r ∧
        ∃ b, b < pk k' ∧ D ∈ mty C0 I (ck k' (ik k' + b)))) :
    MultiTierOk (mixKernels I C0 g ck ik pk dir) := by
  refine
    { hp := hp
      frame_q := readoff_qnet_frame hI g (fun k => ck k (ik k))
        hgdom (fun k => hdom k (ik k)) hinj
      e_clash := fun _ _ h => mty_clash h
      e_nobot := fun _ => mty_nobot
      e_and := fun _ _ _ h => mty_and h
      e_or := fun _ _ _ h => mty_or h
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := fun _ f _ _ hmem hEr => mty_all hmem (hgdom f) hEr
      ek_all := ?_
      ke_all := ?_
      kk_pp := ?_
      kk_ppi := ?_
      kk_eq := fun k a _ E hE =>
        mty_all hE (hdom k (ik k + a)) (hI.refl_eq (ck k (ik k + a)) (hdom k (ik k + a)))
      kq_all := ?_
      e_ex := ?_
      k_ex := ?_ }
  · -- ek_all
    intro e r X hmem k hr a ha
    apply mty_all hmem (hdom k (ik k + a))
    rw [hstab k e a ha, hI.conv_ (ck k (ik k)) (g e) (hdom k (ik k)) (hgdom e)]
    exact hr
  · -- ke_all
    intro k a ha r X hmem f hr
    apply mty_all hmem (hgdom f)
    rw [hI.conv_ (g f) (ck k (ik k + a)) (hgdom f) (hdom k (ik k + a)), hstab k f a ha,
      ← hI.conv_ (g f) (ck k (ik k)) (hgdom f) (hdom k (ik k))]
    exact hr
  · -- kk_pp: `all pp` propagates in both directions (segment / dsegment)
    intro k a ha E hE b hb
    by_cases hd : dir k = true
    · have hs : ∀ n, I.rho (ck k n) (ck k (n + 1)) = pp := by
        intro n; have h := hstep k n; rw [hd] at h; exact h
      exact segment_kk_pp hI (fun n => hdom k n) hs (hty k) ha hE b hb
    · have hd' : dir k = false := by
        cases hh : dir k with
        | false => rfl
        | true => exact absurd hh hd
      have hs : ∀ n, I.rho (ck k n) (ck k (n + 1)) = ppi := by
        intro n; have h := hstep k n; rw [hd'] at h; exact h
      exact dsegment_kk_pp hI (fun n => hdom k n) hs (hty k) ha hE b hb
  · -- kk_ppi: `all ppi` propagates in both directions
    intro k a ha E hE b hb
    by_cases hd : dir k = true
    · have hs : ∀ n, I.rho (ck k n) (ck k (n + 1)) = pp := by
        intro n; have h := hstep k n; rw [hd] at h; exact h
      exact segment_kk_ppi hI (fun n => hdom k n) hs (hty k) ha hE b hb
    · have hd' : dir k = false := by
        cases hh : dir k with
        | false => rfl
        | true => exact absurd hh hd
      have hs : ∀ n, I.rho (ck k n) (ck k (n + 1)) = ppi := by
        intro n; have h := hstep k n; rw [hd'] at h; exact h
      exact dsegment_kk_ppi hI (fun n => hdom k n) hs (hty k) ha hE b hb
  · -- kq_all: cross-kernel `∀` fires through the constant cross-row `hrectQ`
    intro k k' hkk a _ r c hmem hr b _
    apply mty_all hmem (hdom k' (ik k' + b))
    rw [hrectQ k k' hkk a b]
    exact hr
  · -- e_ex: horizontal child or into some kernel
    intro e r X hmem
    rcases he_ex e r X hmem with ⟨f, hEf, hXf⟩ | ⟨k, hK, b, hb, hXb⟩
    · exact Or.inl ⟨f, hEf, hXf⟩
    · exact Or.inr ⟨k, hK, b, hb, hXb⟩
  · -- k_ex: external child / up own chain / reflexive / cross-kernel
    intro k a _ r X hmem
    rcases hk_ex k a r X hmem with ⟨f, hKf, hXf⟩ | ⟨hcd, b, hb, hXb⟩ |
      ⟨rfl, hX⟩ | ⟨k', hne, hQ, b, hb, hXb⟩
    · exact Or.inl ⟨f, hKf, hXf⟩
    · exact Or.inr (Or.inl ⟨hcd, b, hb, hXb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hX⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨k', hne, hQ, b, hb, hXb⟩))

/-- **THE PURELY-VERTICAL MULTI-KERNEL CERTIFICATE** (§38) — `mixKernels_ok` at
    `β = Empty`, every kernel ASCENDING.  Every external obligation (`hstab`,
    `he_ex`, and the external half of `hinj`) is vacuous, leaving exactly the
    vertical interface: per-kernel recurrence `hty`, cross-kernel constancy
    `hrectQ`, distinct bases `hbase`, and the phase-demand routing `hk_ex`
    (own chain / reflexive `∃EQ` / another kernel). -/
theorem mixKernelsV_ok {κ : Type} [DecidableEq κ] (hI : RCC5Interp I) (C0 : Concept)
    (ck : κ → Nat → α) (hdom : ∀ k m, I.dom (ck k m))
    (ik pk : κ → Nat)
    (hstep : ∀ k m, I.rho (ck k m) (ck k (m + 1)) = pp)
    (hp : ∀ k, 0 < pk k)
    (hty : ∀ k, mty C0 I (ck k (ik k)) = mty C0 I (ck k (ik k + pk k)))
    (hrectQ : ∀ k k', k ≠ k' → ∀ a b,
      I.rho (ck k (ik k + a)) (ck k' (ik k' + b))
        = I.rho (ck k (ik k)) (ck k' (ik k')))
    (hbase : ∀ k k', ck k (ik k) = ck k' (ik k') → k = k')
    (hk_ex : ∀ k a r D, Concept.ex r D ∈ mty C0 I (ck k (ik k + a)) →
      (r = pp ∧ ∃ b, b < pk k ∧ D ∈ mty C0 I (ck k (ik k + b))) ∨
      (r = eq ∧ D ∈ mty C0 I (ck k (ik k + a))) ∨
      (∃ k', k ≠ k' ∧ I.rho (ck k (ik k)) (ck k' (ik k')) = r ∧
        ∃ b, b < pk k' ∧ D ∈ mty C0 I (ck k' (ik k' + b)))) :
    MultiTierOk (mixKernels I C0 (fun e : Empty => e.elim) ck ik pk (fun _ => true)) := by
  refine mixKernels_ok hI C0 (fun e : Empty => e.elim) (fun e => e.elim) ck hdom
    ik pk (fun _ => true) hstep hp hty (fun _ e => e.elim) hrectQ ?_
    (fun e => e.elim) ?_
  · rintro (e | k) (f | k') h
    · exact e.elim
    · exact e.elim
    · exact f.elim
    · simp only [Sum.elim_inr] at h
      rw [hbase k k' h]
  · intro k a r D hmem
    rcases hk_ex k a r D hmem with ⟨rfl, hb⟩ | ⟨rfl, hD⟩ | hcross
    · exact Or.inr (Or.inl ⟨rfl, hb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, hD⟩))
    · exact Or.inr (Or.inr (Or.inr hcross))

/-- **THE VERTICAL MULTI-TOWER CERTIFICATE, ASSEMBLED** (§38) — the first
    `mixKernels_ok` instantiation from model-side data.  Inputs: `n` ascending
    towers `ck` (each a class's `class_tower` chain), each with recurrence +
    round-robin coverage of its demand list `Ds k` past any threshold (`hrec`),
    pairwise cross-constancy horizons `hN` (`classify_cross` disjunct 1, i.e.
    the towers are pairwise non-comparable — comparable ones having been merged
    by §37's maximal-tower domination), and the purely-vertical phase condition
    `hdem` (every phase `∃`-demand is `∃PP` with argument in the tower's own
    round-robin list, or `∃EQ`).  Output: bases `ik` and periods `pk` at which
    the whole family is a valid `MultiTier` certificate.

    The base choice is the content: `exists_bound2` joins the per-pair horizons
    to a single `B`, and `hrec k B` supplies a recurrence base ABOVE `B` for
    every kernel — so `hty` and `hrectQ` (via `family_hrectQ`) hold at the same
    bases, and `hinj` follows from `cross_const_ne_eq`. -/
theorem vtowers_ok (hI : RCC5Interp I) (C0 : Concept) {n : Nat}
    (Ds : Fin n → List Concept) (ck : Fin n → Nat → α)
    (hdom : ∀ k m, I.dom (ck k m))
    (hstep : ∀ k m, I.rho (ck k m) (ck k (m + 1)) = pp)
    (hrec : ∀ k L0, ∃ i p, L0 ≤ i ∧ 0 < p ∧
      mty C0 I (ck k i) = mty C0 I (ck k (i + p)) ∧
      ∀ D ∈ Ds k, ∃ b, b < p ∧ D ∈ mty C0 I (ck k (i + b)))
    (hN : Fin n → Fin n → Nat)
    (hconst : ∀ k k', k ≠ k' → ∀ i j, hN k k' ≤ i → hN k k' ≤ j →
      I.rho (ck k i) (ck k' j) = I.rho (ck k (hN k k')) (ck k' (hN k k')))
    (hdem : ∀ k m r D, Concept.ex r D ∈ mty C0 I (ck k m) →
      (r = pp ∧ D ∈ Ds k) ∨ r = eq) :
    ∃ ik pk : Fin n → Nat,
      MultiTierOk (mixKernels I C0 (fun e : Empty => e.elim) ck ik pk (fun _ => true)) ∧
      ∀ k, ∀ D ∈ Ds k, ∃ b, b < pk k ∧ D ∈ mty C0 I (ck k (ik k + b)) := by
  classical
  obtain ⟨B, hB⟩ := exists_bound2 n hN
  have hpair : ∀ k : Fin n, ∃ ip : Nat × Nat, B ≤ ip.1 ∧ 0 < ip.2 ∧
      mty C0 I (ck k ip.1) = mty C0 I (ck k (ip.1 + ip.2)) ∧
      ∀ D ∈ Ds k, ∃ b, b < ip.2 ∧ D ∈ mty C0 I (ck k (ip.1 + b)) := by
    intro k
    obtain ⟨i, p, h1, h2, h3, h4⟩ := hrec k B
    exact ⟨(i, p), h1, h2, h3, h4⟩
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice hpair
  refine ⟨fun k => (f k).1, fun k => (f k).2, ?_, fun k => (hf k).2.2.2⟩
  have hbk : ∀ k k' : Fin n, k ≠ k' → hN k k' ≤ (f k).1 :=
    fun k k' _ => Nat.le_trans (hB k k') (hf k).1
  have hbk' : ∀ k k' : Fin n, k ≠ k' → hN k k' ≤ (f k').1 :=
    fun k k' _ => Nat.le_trans (hB k k') (hf k').1
  refine mixKernelsV_ok hI C0 ck hdom (fun k => (f k).1) (fun k => (f k).2)
    hstep (fun k => (hf k).2.1) (fun k => (hf k).2.2.1)
    (family_hrectQ ck (fun k => (f k).1) hN hconst hbk hbk') ?_ ?_
  · -- distinct bases: a constant cross-relation is never `EQ`
    intro k k' heq
    rcases Classical.em (k = k') with hkk | hne
    · exact hkk
    exfalso
    have hcv : I.rho (ck k (f k).1) (ck k' (f k').1)
        = I.rho (ck k (hN k k')) (ck k' (hN k k')) :=
      hconst k k' hne _ _ (hbk k k' hne) (hbk' k k' hne)
    refine cross_const_ne_eq hI (ck k) (ck k') (hdom k) (hdom k') (hstep k')
      (hN k k') _ (fun i j hi hj => hconst k k' hne i j hi hj) ?_
    rw [← hcv, heq]
    exact hI.refl_eq _ (hdom k' (f k').1)
  · -- phase-demand routing: own chain (round-robin) or reflexive `∃EQ`
    intro k a r D hmem
    rcases hdem k ((f k).1 + a) r D hmem with ⟨rfl, hD⟩ | rfl
    · exact Or.inl ⟨rfl, (hf k).2.2.2 D hD⟩
    · exact Or.inr (Or.inl ⟨rfl, seg_ex_eq hI (hdom k) hmem⟩)

/-! ### §38.2 — the model-side connection: `persistAll` nodes ⟹ the certificate

`vtowers_ok` consumes CHAINS, but the extraction starts from `persistAll` NODES,
and the classification (non-comparability) is a statement ABOUT the chains — so
the chains cannot stay existential.  `classChain` NAMES them (the round-robin
tower of each class), which lets hypothesis and conclusion both quote the same
object, and reduces the vertical extraction to the honest DICHOTOMY
`vtowers_or_comparable`: either the family is pairwise non-comparable and the
certificate exists, or two towers are comparable — the case §37 removes by
merging them under their dominating maximal tower. -/

/-- The named round-robin tower of a class (the chain `class_tower` produces). -/
noncomputable def classChain (hI : RCC5Interp I) (C0 : Concept) {n : Nat}
    (Ds : Fin n → List Concept) (hL : ∀ k, 0 < (Ds k).length)
    (x0 : Fin n → α) (h0 : ∀ k, persistAll I C0 (Ds k) (x0 k)) (k : Fin n) : Nat → α :=
  rrPt hI C0 (Ds k) (hL k) (x0 k) (h0 k)

theorem classChain_dom (hI : RCC5Interp I) (C0 : Concept) {n : Nat}
    (Ds : Fin n → List Concept) (hL : ∀ k, 0 < (Ds k).length)
    (x0 : Fin n → α) (h0 : ∀ k, persistAll I C0 (Ds k) (x0 k)) (k : Fin n) (m : Nat) :
    I.dom (classChain hI C0 Ds hL x0 h0 k m) :=
  rrPt_dom hI C0 (Ds k) (hL k) (x0 k) (h0 k) m

theorem classChain_step (hI : RCC5Interp I) (C0 : Concept) {n : Nat}
    (Ds : Fin n → List Concept) (hL : ∀ k, 0 < (Ds k).length)
    (x0 : Fin n → α) (h0 : ∀ k, persistAll I C0 (Ds k) (x0 k)) (k : Fin n) (m : Nat) :
    I.rho (classChain hI C0 Ds hL x0 h0 k m)
      (classChain hI C0 Ds hL x0 h0 k (m + 1)) = pp :=
  rrPt_step hI C0 (Ds k) (hL k) (x0 k) (h0 k) m

/-- Every rung of a class tower is the root or `PP`-above it — so a model-side
    condition imposed on the `PP`-cone of the root reaches the whole tower. -/
theorem classChain_above (hI : RCC5Interp I) (C0 : Concept) {n : Nat}
    (Ds : Fin n → List Concept) (hL : ∀ k, 0 < (Ds k).length)
    (x0 : Fin n → α) (h0 : ∀ k, persistAll I C0 (Ds k) (x0 k)) (k : Fin n) (m : Nat) :
    classChain hI C0 Ds hL x0 h0 k m = x0 k ∨
      I.rho (x0 k) (classChain hI C0 Ds hL x0 h0 k m) = pp := by
  cases m with
  | zero => exact Or.inl rfl
  | succ m =>
    refine Or.inr ?_
    have h := chain_pp_lt hI (classChain hI C0 Ds hL x0 h0 k)
      (classChain_dom hI C0 Ds hL x0 h0 k) (classChain_step hI C0 Ds hL x0 h0 k)
      0 (m + 1) (Nat.succ_pos m)
    exact h

/-- Each class tower has its recurrence + full round-robin demand coverage
    available past ANY threshold — `class_tower`'s content, on the named chain. -/
theorem classChain_rec (hI : RCC5Interp I) (C0 : Concept) {n : Nat}
    (Ds : Fin n → List Concept) (hL : ∀ k, 0 < (Ds k).length)
    (x0 : Fin n → α) (h0 : ∀ k, persistAll I C0 (Ds k) (x0 k)) (k : Fin n) (L0 : Nat) :
    ∃ i p, L0 ≤ i ∧ 0 < p ∧
      mty C0 I (classChain hI C0 Ds hL x0 h0 k i)
        = mty C0 I (classChain hI C0 Ds hL x0 h0 k (i + p)) ∧
      ∀ D ∈ Ds k, ∃ b, b < p ∧ D ∈ mty C0 I (classChain hI C0 Ds hL x0 h0 k (i + b)) := by
  obtain ⟨i, p, hL0, hi, hp, hdvd, _, hty⟩ :=
    rr_segment_from hI C0 (Ds k) (hL k) (x0 k) (h0 k) L0
  refine ⟨i, p, hL0, hp, hty, fun D hD => ?_⟩
  obtain ⟨jj, hget⟩ := List.get_of_mem hD
  obtain ⟨b, hb, hDb⟩ :=
    rr_covers hI C0 (Ds k) (hL k) (x0 k) (h0 k) i p hi hp hdvd jj.1 jj.2
  exact ⟨b, hb, hget ▸ hDb⟩

/-- **THE VERTICAL EXTRACTION DICHOTOMY** (§38.2), chain-generic form.  For any
    finite family of ascending towers with per-tower recurrence + round-robin
    coverage (`hrec`) and purely vertical phase demands (`hdem`), EITHER the
    family assembles into a full `MultiTierOk` certificate (`vtowers_ok`), OR two
    of the towers are COMPARABLE — the case §37 removes by merging them under
    their dominating maximal tower.  The split is `classify_cross`: its
    disjunct 1 (eventual constancy) is precisely what `vtowers_ok` needs, and
    its disjuncts 2/3 are precisely the merge trigger.  So no third case can
    arise, and nothing beyond the merge is owed on the vertical side. -/
theorem vtowers_or_comparable_gen (hI : RCC5Interp I) (C0 : Concept) {n : Nat}
    (Ds : Fin n → List Concept) (C : Fin n → Nat → α)
    (hdom : ∀ k m, I.dom (C k m))
    (hstep : ∀ k m, I.rho (C k m) (C k (m + 1)) = pp)
    (hrec : ∀ k L0, ∃ i p, L0 ≤ i ∧ 0 < p ∧
      mty C0 I (C k i) = mty C0 I (C k (i + p)) ∧
      ∀ D ∈ Ds k, ∃ b, b < p ∧ D ∈ mty C0 I (C k (i + b)))
    (hdem : ∀ k m r D, Concept.ex r D ∈ mty C0 I (C k m) →
      (r = pp ∧ D ∈ Ds k) ∨ r = eq) :
    (∃ ik pk : Fin n → Nat,
        MultiTierOk (mixKernels I C0 (fun e : Empty => e.elim) C ik pk (fun _ => true)) ∧
        ∀ k, ∀ D ∈ Ds k, ∃ b, b < pk k ∧ D ∈ mty C0 I (C k (ik k + b)))
    ∨ (∃ k k' : Fin n, k ≠ k' ∧
        ((∀ i, ∃ j, I.rho (C k i) (C k' j) = pp ∨ I.rho (C k i) (C k' j) = eq) ∨
         (∀ j, ∃ i, I.rho (C k i) (C k' j) = ppi))) := by
  classical
  rcases Classical.em (∀ k k' : Fin n, k ≠ k' →
      ∃ N v, ∀ i j, N ≤ i → N ≤ j → I.rho (C k i) (C k' j) = v) with hall | hsome
  · -- every cross-pair is eventually constant: build the certificate
    refine Or.inl ?_
    have hex : ∀ q : Fin n × Fin n, ∃ N : Nat, q.1 ≠ q.2 →
        ∀ i j, N ≤ i → N ≤ j → I.rho (C q.1 i) (C q.2 j) = I.rho (C q.1 N) (C q.2 N) := by
      intro q
      rcases Classical.em (q.1 ≠ q.2) with hne | hnn
      · obtain ⟨N, v, hv⟩ := hall q.1 q.2 hne
        exact ⟨N, fun _ i j hi hj => by
          rw [hv i j hi hj, hv N N (Nat.le_refl N) (Nat.le_refl N)]⟩
      · exact ⟨0, fun h => absurd h hnn⟩
    obtain ⟨hNf, hNspec⟩ := Classical.axiomOfChoice hex
    exact vtowers_ok hI C0 Ds C hdom hstep hrec
      (fun k k' => hNf (k, k')) (fun k k' hne => hNspec (k, k') hne) hdem
  · -- some cross-pair is NOT eventually constant: `classify_cross` ⟹ comparable
    refine Or.inr ?_
    rcases Classical.em (∃ k k' : Fin n, k ≠ k' ∧
        ¬ ∃ N v, ∀ i j, N ≤ i → N ≤ j → I.rho (C k i) (C k' j) = v)
      with ⟨k, k', hne, hnc⟩ | hno
    · refine ⟨k, k', hne, ?_⟩
      rcases classify_cross hI (C k) (C k') (hdom k) (hdom k') (hstep k) (hstep k')
        with hconst | hemb | hemb'
      · exact absurd hconst hnc
      · exact Or.inl hemb
      · exact Or.inr hemb'
    · exact absurd (fun k k' hne => Classical.byContradiction
        (fun hnc => hno ⟨k, k', hne, hnc⟩)) hsome

/-- **THE VERTICAL EXTRACTION DICHOTOMY, FROM `persistAll` NODES** (§38.2) — the
    model-side entry point.  Given `n` persistent roots `x0 k` with demand lists
    `Ds k`, and the purely vertical model-side condition `hdem` (in the `PP`-cone
    of each root, every `∃`-demand is `∃PP` with argument in that root's OWN
    list, or `∃EQ`), the class towers either assemble into a full `MultiTierOk`
    certificate or contain a comparable pair.  This is `vtowers_or_comparable_gen`
    at the named `classChain`, with `hrec` supplied by `classChain_rec` and the
    phase condition pulled back along `classChain_above`. -/
theorem vtowers_or_comparable (hI : RCC5Interp I) (C0 : Concept) {n : Nat}
    (Ds : Fin n → List Concept) (hL : ∀ k, 0 < (Ds k).length)
    (x0 : Fin n → α) (h0 : ∀ k, persistAll I C0 (Ds k) (x0 k))
    (hdem : ∀ k z, I.dom z → (z = x0 k ∨ I.rho (x0 k) z = pp) →
      ∀ r D, Concept.ex r D ∈ mty C0 I z → (r = pp ∧ D ∈ Ds k) ∨ r = eq) :
    (∃ ik pk : Fin n → Nat,
        MultiTierOk (mixKernels I C0 (fun e : Empty => e.elim)
          (classChain hI C0 Ds hL x0 h0) ik pk (fun _ => true)) ∧
        ∀ k, ∀ D ∈ Ds k, ∃ b, b < pk k ∧
          D ∈ mty C0 I (classChain hI C0 Ds hL x0 h0 k (ik k + b)))
    ∨ (∃ k k' : Fin n, k ≠ k' ∧
        ((∀ i, ∃ j, I.rho (classChain hI C0 Ds hL x0 h0 k i)
                      (classChain hI C0 Ds hL x0 h0 k' j) = pp ∨
                    I.rho (classChain hI C0 Ds hL x0 h0 k i)
                      (classChain hI C0 Ds hL x0 h0 k' j) = eq) ∨
         (∀ j, ∃ i, I.rho (classChain hI C0 Ds hL x0 h0 k i)
                      (classChain hI C0 Ds hL x0 h0 k' j) = ppi))) :=
  vtowers_or_comparable_gen hI C0 Ds (classChain hI C0 Ds hL x0 h0)
    (classChain_dom hI C0 Ds hL x0 h0) (classChain_step hI C0 Ds hL x0 h0)
    (classChain_rec hI C0 Ds hL x0 h0)
    (fun k m r D hmem => hdem k _ (classChain_dom hI C0 Ds hL x0 h0 k m)
      (classChain_above hI C0 Ds hL x0 h0 k m) r D hmem)

/-! ### §38.3 — the MERGE: closing the comparable branch

`vtowers_or_comparable`'s escape branch is closed by MERGING the comparable
pair.  §37's maximal-tower domination does NOT close it: that is a statement
about the *demand* towers, whereas the kernels are the ROUND-ROBIN re-towers
built above each class node, and incomparability does NOT transfer between the
two layers — `rrPt` ascends through chosen witnesses and can leave the demand
tower entirely, so two incomparable demand towers sitting inside a common region
can have mutually embedding round-robin towers.  The merge therefore has to run
on the KERNELS, as a recursion: a comparable pair becomes ONE merged
`persistAll` site carrying both demand lists, the site count strictly drops, and
the family is re-entered.  It terminates because the count decreases.

Corroboration that a single round never sufficed: `merge_persistAll` wants the
guard as `∀PP.(∃PP.D) ∈ mty C0 I x`, which `persistPP` ROOTS supply but
`persistAll` SITES do not (they carry it as `sat`).  `merge_persistAll_sat` is
the missing bridge, and it is exactly what a SECOND merge round needs. -/

/-- The per-site purely-vertical condition, carried through the merge: in the
    `PP`-cone of the site's node, every `∃`-demand is `∃PP` with argument in the
    site's OWN list, or `∃EQ`.  Preserved by merging because the merged node's
    cone is contained in each parent's (`comp(PP,PP) = {PP}`). -/
abbrev SiteDem (I : Interp α) (C0 : Concept) (s : α × List Concept) : Prop :=
  ∀ z, I.dom z → (z = s.1 ∨ I.rho s.1 z = pp) →
    ∀ r D, Concept.ex r D ∈ mty C0 I z → (r = pp ∧ D ∈ s.2) ∨ r = eq

/-- `merge_persistAll` with the guard in `sat` form — which is what a
    `persistAll` SITE actually carries.  The `mty` form only covers merges of
    `persistPP` roots, so this is the bridge the second merge round needs. -/
theorem merge_persistAll_sat (hI : RCC5Interp I) {C0 : Concept} {Ds : List Concept}
    {z : α} (hz : I.dom z)
    (hguards : ∀ D ∈ Ds, ∃ x, I.dom x ∧ I.rho x z = pp ∧
      Concept.ex pp D ∈ mty C0 I x ∧ sat I x (Concept.all pp (Concept.ex pp D))) :
    persistAll I C0 Ds z := by
  refine ⟨hz, fun D hD => ?_⟩
  obtain ⟨x, hx, hxz, hex, hall⟩ := hguards D hD
  exact ⟨mem_mty.mpr ⟨mty_sub _ hex, hall z hz hxz⟩, sat_all_pp_up hI hx hz hxz hall⟩

/-- **THE PAIRWISE SITE MERGE** — two `persistAll` sites with a common `PP`-upper
    node collapse to ONE site carrying both demand lists. -/
theorem persistAll_merge2 (hI : RCC5Interp I) {C0 : Concept} {Ds Ds' : List Concept}
    {x x' z : α} (h : persistAll I C0 Ds x) (h' : persistAll I C0 Ds' x')
    (hz : I.dom z) (hxz : I.rho x z = pp) (hxz' : I.rho x' z = pp) :
    persistAll I C0 (Ds ++ Ds') z := by
  refine merge_persistAll_sat hI hz (fun D hD => ?_)
  rcases List.mem_append.mp hD with hD | hD
  · exact ⟨x, h.1, hxz, (h.2 D hD).1, (h.2 D hD).2⟩
  · exact ⟨x', h'.1, hxz', (h'.2 D hD).1, (h'.2 D hD).2⟩

/-- **A COMPARABLE PAIR HAS A COMMON UPPER NODE.**  Either disjunct of the
    comparability output yields one node `PP`-above BOTH chain roots: from
    `c 0 ⊆ d j` take `d (j+1)`; from `d 0 ⊆ c i` take `c (i+1)`.  This is the
    input `persistAll_merge2` consumes. -/
theorem comparable_common_upper (hI : RCC5Interp I) (c d : Nat → α)
    (hcdom : ∀ m, I.dom (c m)) (hddom : ∀ m, I.dom (d m))
    (hcstep : ∀ m, I.rho (c m) (c (m + 1)) = pp)
    (hdstep : ∀ m, I.rho (d m) (d (m + 1)) = pp)
    (h : (∀ i, ∃ j, I.rho (c i) (d j) = pp ∨ I.rho (c i) (d j) = eq) ∨
         (∀ j, ∃ i, I.rho (c i) (d j) = ppi)) :
    ∃ w, I.dom w ∧ I.rho (c 0) w = pp ∧ I.rho (d 0) w = pp := by
  rcases h with hemb | hemb'
  · obtain ⟨j, hj⟩ := hemb 0
    obtain ⟨j', hj'⟩ := embed_to_pp hI hddom hdstep (hcdom 0) hj
    refine ⟨d (j' + 1), hddom _, ?_,
      chain_pp_lt hI d hddom hdstep 0 (j' + 1) (Nat.succ_pos j')⟩
    have hc := hI.comp_ (c 0) (d j') (d (j' + 1)) (hcdom 0) (hddom j') (hddom (j' + 1))
    rw [hj', hdstep j', show comp pp pp = [pp] from rfl, List.mem_singleton] at hc
    exact hc
  · obtain ⟨i, hi⟩ := hemb' 0
    have hdc : I.rho (d 0) (c i) = pp := by
      rw [hI.conv_ (c i) (d 0) (hcdom i) (hddom 0), hi]; rfl
    refine ⟨c (i + 1), hcdom _,
      chain_pp_lt hI c hcdom hcstep 0 (i + 1) (Nat.succ_pos i), ?_⟩
    have hc := hI.comp_ (d 0) (c i) (c (i + 1)) (hddom 0) (hcdom i) (hcdom (i + 1))
    rw [hdc, hcstep i, show comp pp pp = [pp] from rfl, List.mem_singleton] at hc
    exact hc

/-- A `filter` that drops at least one element of the list is strictly shorter
    (the measure step of the merge recursion). -/
theorem filter_length_lt {β : Type} (p : β → Bool) :
    ∀ (l : List β) (a : β), a ∈ l → p a = false → (l.filter p).length < l.length := by
  intro l
  induction l with
  | nil => intro a ha _; nomatch ha
  | cons b rest ih =>
    intro a ha hpa
    rw [List.filter_cons]
    have hle := List.length_filter_le p rest
    by_cases hb : p b = true
    · have hane : a ≠ b := by intro h; subst h; simp [hb] at hpa
      have harest : a ∈ rest := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h hane
        · exact h
      have hlt := ih a harest hpa
      rw [if_pos hb]
      simp only [List.length_cons]
      omega
    · rw [if_neg hb]
      simp only [List.length_cons]
      omega

/-- The dichotomy with BOTH branches' chains abstracted — the shape the merge
    recursion consumes (the `classChain` terms are long, and the recursion only
    needs the chain's root/dom/step). -/
theorem vtowers_or_comparable_ex (hI : RCC5Interp I) (C0 : Concept) {n : Nat}
    (Ds : Fin n → List Concept) (hL : ∀ k, 0 < (Ds k).length)
    (x0 : Fin n → α) (h0 : ∀ k, persistAll I C0 (Ds k) (x0 k))
    (hdem : ∀ k z, I.dom z → (z = x0 k ∨ I.rho (x0 k) z = pp) →
      ∀ r D, Concept.ex r D ∈ mty C0 I z → (r = pp ∧ D ∈ Ds k) ∨ r = eq) :
    (∃ (ck : Fin n → Nat → α) (ik pk : Fin n → Nat),
        MultiTierOk (mixKernels I C0 (fun e : Empty => e.elim) ck ik pk (fun _ => true)) ∧
        ∀ k, ∀ D ∈ Ds k, ∃ b, b < pk k ∧ D ∈ mty C0 I (ck k (ik k + b)))
    ∨ (∃ C : Fin n → Nat → α, (∀ k, C k 0 = x0 k) ∧ (∀ k m, I.dom (C k m)) ∧
        (∀ k m, I.rho (C k m) (C k (m + 1)) = pp) ∧
        ∃ k k', k ≠ k' ∧
          ((∀ i, ∃ j, I.rho (C k i) (C k' j) = pp ∨ I.rho (C k i) (C k' j) = eq) ∨
           (∀ j, ∃ i, I.rho (C k i) (C k' j) = ppi))) := by
  rcases vtowers_or_comparable hI C0 Ds hL x0 h0 hdem with
    ⟨ik, pk, hok, hserve⟩ | ⟨k, k', hne, hcomp⟩
  · exact Or.inl ⟨classChain hI C0 Ds hL x0 h0, ik, pk, hok, hserve⟩
  · exact Or.inr ⟨classChain hI C0 Ds hL x0 h0, fun _ => rfl,
      classChain_dom hI C0 Ds hL x0 h0, classChain_step hI C0 Ds hL x0 h0,
      k, k', hne, hcomp⟩

/-- **ONE MERGE STEP** — replacing a comparable pair of sites by their merge
    yields a STRICTLY SHORTER site list with every invariant preserved and every
    old demand list contained in a new one.  The new list is built by mapping the
    index range with `k` filtered out and `k'` overwritten by the merged site, so
    no double-erasure index arithmetic is needed. -/
theorem merge_step (hI : RCC5Interp I) (C0 : Concept) (L : List (α × List Concept))
    (hpa : ∀ s ∈ L, persistAll I C0 s.2 s.1)
    (hpos : ∀ s ∈ L, 0 < s.2.length)
    (hdemL : ∀ s ∈ L, SiteDem I C0 s)
    (k k' : Fin L.length) (hne : k ≠ k')
    (w : α) (hwdom : I.dom w)
    (hwk : I.rho (L.get k).1 w = pp) (hwk' : I.rho (L.get k').1 w = pp) :
    ∃ L' : List (α × List Concept), L'.length < L.length ∧
      (∀ s ∈ L', persistAll I C0 s.2 s.1) ∧
      (∀ s ∈ L', 0 < s.2.length) ∧
      (∀ s ∈ L', SiteDem I C0 s) ∧
      (∀ s ∈ L, ∃ t ∈ L', ∀ D ∈ s.2, D ∈ t.2) := by
  classical
  have hgk : L.get k ∈ L := List.get_mem L k
  have hgk' : L.get k' ∈ L := List.get_mem L k'
  have hmergeP : persistAll I C0 ((L.get k).2 ++ (L.get k').2) w :=
    persistAll_merge2 hI (hpa _ hgk) (hpa _ hgk') hwdom hwk hwk'
  obtain ⟨L', hL'def⟩ : ∃ L' : List (α × List Concept),
      L' = ((List.finRange L.length).filter (fun i => decide (i ≠ k))).map
        (fun i => if i = k' then (w, (L.get k).2 ++ (L.get k').2) else L.get i) := ⟨_, rfl⟩
  have hmemchar : ∀ s ∈ L', s = (w, (L.get k).2 ++ (L.get k').2) ∨ s ∈ L := by
    intro s hs
    rw [hL'def] at hs
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
    by_cases hik : i = k'
    · exact Or.inl (by rw [if_pos hik])
    · exact Or.inr (by rw [if_neg hik]; exact List.get_mem L i)
  have hmerged : (w, (L.get k).2 ++ (L.get k').2) ∈ L' := by
    rw [hL'def]
    exact List.mem_map.mpr ⟨k', List.mem_filter.mpr ⟨List.mem_finRange k',
      by simp only [decide_eq_true_eq]; exact fun h => hne h.symm⟩, by rw [if_pos rfl]⟩
  refine ⟨L', ?_, ?_, ?_, ?_, ?_⟩
  · -- strictly shorter
    rw [hL'def, List.length_map]
    have h := filter_length_lt (fun i : Fin L.length => decide (i ≠ k))
      (List.finRange L.length) k (List.mem_finRange k) (by simp)
    rwa [List.length_finRange] at h
  · -- persistAll
    intro s hs
    rcases hmemchar s hs with rfl | hsL
    · exact hmergeP
    · exact hpa s hsL
  · -- demand lists nonempty
    intro s hs
    rcases hmemchar s hs with rfl | hsL
    · have hk0 := hpos _ hgk
      show 0 < ((L.get k).2 ++ (L.get k').2).length
      simp only [List.length_append]; omega
    · exact hpos s hsL
  · -- SiteDem
    intro s hs
    rcases hmemchar s hs with rfl | hsL
    · intro z hz hcone r D hmemD
      have hcone' : z = (L.get k).1 ∨ I.rho (L.get k).1 z = pp := by
        rcases hcone with rfl | hwz
        · exact Or.inr hwk
        · refine Or.inr ?_
          have hc := hI.comp_ (L.get k).1 w z (hpa _ hgk).1 hwdom hz
          rw [hwk, hwz, show comp pp pp = [pp] from rfl, List.mem_singleton] at hc
          exact hc
      rcases hdemL _ hgk z hz hcone' r D hmemD with ⟨hr, hD⟩ | hr
      · exact Or.inl ⟨hr, List.mem_append.mpr (Or.inl hD)⟩
      · exact Or.inr hr
    · exact hdemL s hsL
  · -- every old list lands in a new one
    intro s hs
    obtain ⟨i, hi⟩ := List.get_of_mem hs
    by_cases hik : i = k
    · refine ⟨_, hmerged, fun D hD => List.mem_append.mpr (Or.inl ?_)⟩
      rw [← hi, hik] at hD; exact hD
    · by_cases hik' : i = k'
      · refine ⟨_, hmerged, fun D hD => List.mem_append.mpr (Or.inr ?_)⟩
        rw [← hi, hik'] at hD; exact hD
      · refine ⟨s, ?_, fun D hD => hD⟩
        rw [hL'def]
        exact List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨List.mem_finRange i,
          by simp only [decide_eq_true_eq]; exact hik⟩, by rw [if_neg hik']; exact hi⟩

/-- **THE MERGE RECURSION** (§38.3) — the site count is the measure.  Given a
    finite family of purely-vertical `persistAll` sites, either the class towers
    are pairwise non-comparable and `vtowers_ok` assembles the certificate, or a
    comparable pair merges (`comparable_common_upper` + `persistAll_merge2` +
    `merge_step`) and the strictly shorter family is re-entered.  The output
    certificate SERVES every demand in `Dall`. -/
theorem merge_sites (hI : RCC5Interp I) (C0 : Concept) (Dall : List Concept) :
    ∀ (N : Nat) (L : List (α × List Concept)), L.length ≤ N →
      (∀ s ∈ L, persistAll I C0 s.2 s.1) →
      (∀ s ∈ L, 0 < s.2.length) →
      (∀ s ∈ L, SiteDem I C0 s) →
      (∀ D ∈ Dall, ∃ s ∈ L, D ∈ s.2) →
      ∃ (m : Nat) (ck : Fin m → Nat → α) (ik pk : Fin m → Nat),
        MultiTierOk (mixKernels I C0 (fun e : Empty => e.elim) ck ik pk (fun _ => true)) ∧
        ∀ D ∈ Dall, ∃ k b, b < pk k ∧ D ∈ mty C0 I (ck k (ik k + b)) := by
  intro N
  induction N with
  | zero =>
    intro L hlen _ _ _ hcov
    have hnil : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    obtain ⟨ik, pk, hok, _⟩ := vtowers_ok hI C0 (fun k : Fin 0 => k.elim0)
      (fun k : Fin 0 => k.elim0) (fun k => k.elim0) (fun k => k.elim0)
      (fun k => k.elim0) (fun k => k.elim0) (fun k => k.elim0) (fun k => k.elim0)
    exact ⟨0, fun k => k.elim0, ik, pk, hok, fun D hD => by
      obtain ⟨s, hs, _⟩ := hcov D hD; nomatch hs⟩
  | succ N ih =>
    intro L hlen hpa hpos hdemL hcov
    have hget : ∀ k : Fin L.length, L.get k ∈ L := fun k => List.get_mem L k
    rcases vtowers_or_comparable_ex hI C0 (fun k : Fin L.length => (L.get k).2)
        (fun k => hpos _ (hget k)) (fun k : Fin L.length => (L.get k).1)
        (fun k => hpa _ (hget k)) (fun k => hdemL _ (hget k))
      with ⟨ck, ik, pk, hok, hserve⟩ | ⟨C, hC0, hCdom, hCstep, k, k', hne, hcomp⟩
    · -- pairwise non-comparable: the family IS the certificate
      refine ⟨L.length, ck, ik, pk, hok, fun D hD => ?_⟩
      obtain ⟨s, hs, hDs⟩ := hcov D hD
      obtain ⟨i, hi⟩ := List.get_of_mem hs
      obtain ⟨b, hb, hDb⟩ := hserve i D (by rw [hi]; exact hDs)
      exact ⟨i, b, hb, hDb⟩
    · -- a comparable pair: merge and re-enter with one site fewer
      obtain ⟨w, hwdom, hwk, hwk'⟩ := comparable_common_upper hI (C k) (C k')
        (hCdom k) (hCdom k') (hCstep k) (hCstep k') hcomp
      rw [hC0 k] at hwk
      rw [hC0 k'] at hwk'
      obtain ⟨L', hlt, hpa', hpos', hdem', hsub⟩ :=
        merge_step hI C0 L hpa hpos hdemL k k' hne w hwdom hwk hwk'
      refine ih L' (by omega) hpa' hpos' hdem' (fun D hD => ?_)
      obtain ⟨s, hs, hDs⟩ := hcov D hD
      obtain ⟨t, ht, hst⟩ := hsub s hs
      exact ⟨t, ht, hst D hDs⟩

/-- **THE VERTICAL MULTI-TOWER CERTIFICATE, UNCONDITIONAL** (§38.3) — the merge
    closes the dichotomy.  EVERY finite family of purely-vertical `persistAll`
    sites yields a `MultiTierOk` certificate serving every demand of every site;
    no comparability hypothesis is owed.  Comparable kernels are merged (the
    site count drops), non-comparable ones assemble by `vtowers_ok`. -/
theorem vtowers_merged (hI : RCC5Interp I) (C0 : Concept)
    (L : List (α × List Concept))
    (hpa : ∀ s ∈ L, persistAll I C0 s.2 s.1)
    (hpos : ∀ s ∈ L, 0 < s.2.length)
    (hdemL : ∀ s ∈ L, SiteDem I C0 s) :
    ∃ (m : Nat) (ck : Fin m → Nat → α) (ik pk : Fin m → Nat),
      MultiTierOk (mixKernels I C0 (fun e : Empty => e.elim) ck ik pk (fun _ => true)) ∧
      ∀ s ∈ L, ∀ D ∈ s.2, ∃ k b, b < pk k ∧ D ∈ mty C0 I (ck k (ik k + b)) := by
  obtain ⟨m, ck, ik, pk, hok, hserve⟩ :=
    merge_sites hI C0 (L.flatMap (fun s => s.2)) L.length L (Nat.le_refl _)
      hpa hpos hdemL (fun D hD => List.mem_flatMap.mp hD)
  exact ⟨m, ck, ik, pk, hok, fun s hs D hD =>
    hserve D (List.mem_flatMap.mpr ⟨s, hs, hD⟩)⟩

/-! ### §39 — the stabilization/serving tension (mixing probe)

Two facts about `mixKernels_ok`'s `hstab` that together pin why the MIXED
assembly has an ordering problem the vertical one does not.  `hstab` demands
that every β-external's row to every kernel be CONSTANT across phases.  The
lemmas below show what a constant row costs: once an external has been SWALLOWED
by an ascending chain at any point at or above the base, constancy forces its row
to be `PPI` at every phase — so it can serve `∃PPI` demands and nothing else.
A `∃DR`/`∃PP` phase-witness therefore has to be un-swallowed, i.e. picked ABOVE
the segment (which is exactly what `kernel_site` does, via
`dr_witness_all_below`/`pp_witness_all_below` at the bound `i + p`).

That is harmless for a kernel's OWN chain — `kernel_site` hands back the
constant row `∀ b ≤ p, ρ (c (i+b)) w = r` for free.  It is the CROSS-kernel
direction that has no such gift: such a `w` is a β-external for every OTHER
kernel too, and `externals_stabilize` only produces a horizon for a list of
externals given IN ADVANCE.  See ASSEMBLY_DESIGN §39 for the resulting cycle. -/

/-- **A STABILIZED, SWALLOWED EXTERNAL IS `PPI` AT EVERY PHASE.**  If `w`'s row to
    the chain is constant from the base `i` on (`mixKernels_ok`'s `hstab`) and the
    chain has swallowed `w` at some `j ≥ i` (`ρ (c j) w = ppi`), then
    `ρ (c (i+a)) w = ppi` for every phase. -/
theorem stab_swallowed_ppi (hI : RCC5Interp I) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) {w : α} (hw : I.dom w) (i : Nat)
    (hstab : ∀ a, I.rho w (c (i + a)) = I.rho w (c i))
    {j : Nat} (hj : i ≤ j) (hsw : I.rho (c j) w = ppi) :
    ∀ a, I.rho (c (i + a)) w = ppi := by
  have hwj : I.rho w (c j) = pp := by
    rw [hI.conv_ (c j) w (hdom j) hw, hsw]; rfl
  have hwi : I.rho w (c i) = pp := by
    have h := hstab (j - i)
    rw [show i + (j - i) = j from by omega] at h
    rw [← h, hwj]
  intro a
  rw [hI.conv_ w (c (i + a)) hw (hdom (i + a)), hstab a, hwi]
  rfl

/-- Consequently such an external serves NO `∃DR` and NO `∃PP` demand of any
    phase: the certificate's declared `K`-row for it is `PPI`.  This is why the
    DR/PP phase-witnesses of `kernel_site` must be picked ABOVE the segment, and
    hence AFTER the base — the ordering constraint §39 turns on. -/
theorem stab_swallowed_no_dr_pp (hI : RCC5Interp I) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) {w : α} (hw : I.dom w) (i : Nat)
    (hstab : ∀ a, I.rho w (c (i + a)) = I.rho w (c i))
    {j : Nat} (hj : i ≤ j) (hsw : I.rho (c j) w = ppi) :
    ∀ a r, (r = dr ∨ r = pp) → I.rho (c (i + a)) w ≠ r := by
  intro a r hr
  rw [stab_swallowed_ppi hI c hdom hw i hstab hj hsw a]
  rcases hr with rfl | rfl <;> exact by decide

/-- **THE `hstab` WINDOW DICHOTOMY** (§39.3/§39.3) — the two certified branches
    land in the SAME conclusion.  A window `[i, i+p)` is stable for an external
    `w` either because the row is still in its INITIAL rank-0 block at the top of
    the window ("stay low" — no horizon consulted at all) or because the row has
    already stabilized from `i` on ("push past" — `external_stabilizes` /
    `stab_window_family`).  Probe `wp91` part I measured BOTH as necessary (345
    of 2,552 solved configurations used one branch for one kernel and the other
    branch for the other), so neither disjunct may be dropped. -/
theorem window_stab_dichotomy (hI : RCC5Interp I) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    {w : α} (hw : I.dom w) (i p : Nat)
    (h : (I.rho (c (i + p)) w = dr ∨ I.rho (c (i + p)) w = pp) ∨
         (∀ m n, i ≤ m → i ≤ n → I.rho (c m) w = I.rho (c n) w)) :
    ∀ b, b < p → I.rho w (c (i + b)) = I.rho w (c i) := by
  intro b hb
  rcases h with hlow | hhigh
  · exact stab_window_of_rank0 hI hdom hstep hw hlow i b (by omega)
  · rw [hI.conv_ (c (i + b)) w (hdom (i + b)) hw,
      hhigh (i + b) i (by omega) (Nat.le_refl i),
      ← hI.conv_ (c i) w (hdom i) hw]

/-- **STABILITY OVER THE WHOLE KERNEL FAMILY** (§39.2) — `stab_window_family` lifted
    from one chain to the finite family: for a FIXED finite witness list and a
    window-length bound `p`, there is a SINGLE horizon `H` past which every
    witness's row is constant on every kernel's window.  `Fin m` finiteness via
    `exists_bound`; per-chain horizons via `stab_window_family`. -/
theorem stab_window_family_multi (hI : RCC5Interp I) {m : Nat} (ck : Fin m → Nat → α)
    (hdom : ∀ k n, I.dom (ck k n))
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = pp)
    (ws : List α) (hws : ∀ w ∈ ws, I.dom w) (p : Nat) :
    ∃ H, ∀ ik : Fin m → Nat, (∀ k, H ≤ ik k) →
      ∀ w ∈ ws, ∀ k b, b < p →
        I.rho w (ck k (ik k + b)) = I.rho w (ck k (ik k)) := by
  have h : ∀ k : Fin m, ∃ N, ∀ w ∈ ws, ∀ i, N ≤ i → ∀ a, a < p →
      I.rho w (ck k (i + a)) = I.rho w (ck k i) :=
    fun k => stab_window_family hI (hdom k) (hstep k) ws hws p
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice h
  obtain ⟨B, hB⟩ := exists_bound m f
  exact ⟨B, fun ik hik w hw k b hb =>
    hf k w hw (ik k) (Nat.le_trans (hB k) (hik k)) b hb⟩

/-! ### §39.3 — the per-kernel pigeonhole

With `three_spaced_not_all_bad` bounding each witness's damage at 2 spaced
candidates, choosing a base is a one-dimensional pigeonhole: a `p`-spaced
candidate list longer than twice the witness count contains a base good for ALL
of them.  No product counting over `Fin m → Fin R` (which core Lean would make
expensive) is needed — that is the payoff of the high-bank decoupling. -/

/-- Splitting a list by a Boolean predicate preserves total length. -/
theorem filter_length_split {A : Type} (q : A → Bool) :
    ∀ l : List A, (l.filter q).length + (l.filter (fun x => !q x)).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons a rest ih =>
    cases hq : q a <;> simp [hq] <;> omega

/-- **AT MOST TWO SPACED CANDIDATES ARE SPOILED** by one witness — the list form
    of `three_spaced_not_all_bad`.  A `p`-spaced list all of whose entries have a
    non-constant window has length ≤ 2, since its first three entries would
    contradict the rank ceiling. -/
theorem spoiled_length_le_two (hI : RCC5Interp I) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    {w : α} (hw : I.dom w) (p : Nat) (hp : 0 < p)
    (l : List Nat) (hsp : l.Pairwise (fun a b => a + p ≤ b))
    (hall : ∀ x ∈ l, I.rho (c x) w ≠ I.rho (c (x + p - 1)) w) :
    l.length ≤ 2 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
  · exact Nat.zero_le _
  · exact Nat.le_of_lt (by simp)
  · exact Nat.le_of_eq (by simp)
  · exfalso
    obtain ⟨hA, hsp1⟩ := List.pairwise_cons.mp hsp
    obtain ⟨hB, _⟩ := List.pairwise_cons.mp hsp1
    exact three_spaced_not_all_bad hI hdom hstep hw p hp a b d
      (hA b (List.mem_cons.mpr (Or.inl rfl)))
      (hB d (List.mem_cons.mpr (Or.inl rfl)))
      (hall a (List.mem_cons.mpr (Or.inl rfl)))
      (hall b (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
      (hall d (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

/-- **THE PIGEONHOLE** (§39.3) — abstract, so it applies to the whole witness
    bank at once.  If every witness spoils at most 2 entries of any `p`-spaced
    list, then a `p`-spaced candidate list longer than `2·|ws|` contains an entry
    good for EVERY witness.  Induction on the witness list, the surviving
    candidates shrinking by at most 2 each step. -/
theorem exists_good_candidate {A : Type} (p : Nat) (bad : A → Nat → Bool) :
    ∀ (ws : List A) (l : List Nat),
      (∀ w ∈ ws, ∀ l' : List Nat, l'.Pairwise (fun a b => a + p ≤ b) →
        (∀ x ∈ l', bad w x = true) → l'.length ≤ 2) →
      l.Pairwise (fun a b => a + p ≤ b) →
      2 * ws.length < l.length → ∃ i ∈ l, ∀ w ∈ ws, bad w i = false := by
  intro ws
  induction ws with
  | nil =>
    intro l _ _ hlen
    rcases l with _ | ⟨a, rest⟩
    · simp at hlen
    · exact ⟨a, List.mem_cons.mpr (Or.inl rfl), fun w hw => nomatch hw⟩
  | cons w rest ih =>
    intro l hbad2 hsp hlen
    have hkeep : (l.filter (fun x => !bad w x)).Pairwise (fun a b => a + p ≤ b) :=
      hsp.sublist List.filter_sublist
    have hdrop : (l.filter (fun x => bad w x)).length ≤ 2 :=
      hbad2 w (List.mem_cons.mpr (Or.inl rfl)) _ (hsp.sublist List.filter_sublist)
        (fun x hx => (List.mem_filter.mp hx).2)
    have hsplit := filter_length_split (fun x => bad w x) l
    have hlen' : 2 * rest.length < (l.filter (fun x => !bad w x)).length := by
      simp only [List.length_cons] at hlen; omega
    obtain ⟨i, hi, hgood⟩ := ih _
      (fun v hv => hbad2 v (List.mem_cons.mpr (Or.inr hv))) hkeep hlen'
    obtain ⟨hil, hiw⟩ := List.mem_filter.mp hi
    refine ⟨i, hil, fun v hv => ?_⟩
    rcases List.mem_cons.mp hv with rfl | hv
    · simpa using hiw
    · exact hgood v hv

/-- **A BOUNDED PARAMETER RECURS COFINALLY** (§39.5) — the link that lets the
    window length be FIXED.  `rr_segment_from` supplies a recurrence base past any
    threshold, but its period varies with the base; the stability argument needs
    ONE period.  Since the periods are bounded (`rr_segment`'s `p ≤ |types|·|Ds|`),
    some single value must serve cofinally many bases: otherwise each `q ≤ Pmax`
    would have a last base, and the max of those finitely many bounds would be
    exceeded by the next base. -/
theorem cofinal_fixed_param (Pmax : Nat) (Q : Nat → Nat → Prop)
    (h : ∀ L, ∃ i q, L ≤ i ∧ q ≤ Pmax ∧ Q i q) :
    ∃ q, q ≤ Pmax ∧ ∀ L, ∃ i, L ≤ i ∧ Q i q := by
  classical
  rcases Classical.em (∃ q, q ≤ Pmax ∧ ∀ L, ∃ i, L ≤ i ∧ Q i q) with hyes | hno
  · exact hyes
  · exfalso
    have hbound : ∀ q : Fin (Pmax + 1), ∃ L, ∀ i, L ≤ i → ¬ Q i q.val := by
      intro q
      rcases Classical.em (∃ L, ∀ i, L ≤ i → ¬ Q i q.val) with hh | hh
      · exact hh
      · exfalso
        refine hno ⟨q.val, by omega, fun L => ?_⟩
        rcases Classical.em (∃ i, L ≤ i ∧ Q i q.val) with h2 | h2
        · exact h2
        · exact absurd ⟨L, fun i hi hQ => h2 ⟨i, hi, hQ⟩⟩ hh
    obtain ⟨f, hf⟩ := Classical.axiomOfChoice hbound
    obtain ⟨B, hB⟩ := exists_bound (Pmax + 1) f
    obtain ⟨i, q, hLi, hq, hQ⟩ := h B
    exact hf ⟨q, by omega⟩ i (Nat.le_trans (hB ⟨q, by omega⟩) hLi) hQ

/-- **A SPACED LIST FROM A COFINAL PREDICATE** (§39.5) — the candidate list the
    base choice consumes.  If `P` holds cofinally (which is exactly what
    `rr_segment_from` gives for "is a type-recurrence base"), then for any length
    `n` and any threshold `L` there is a list of `n` positions, all satisfying `P`,
    all `≥ L`, pairwise spaced at least `p` apart.  Built by recursion: take the
    next `P`-position above the running threshold, then recurse above it `+ p`. -/
theorem exists_spaced_list (P : Nat → Prop) (hcof : ∀ L, ∃ i, L ≤ i ∧ P i) (p : Nat) :
    ∀ n L, ∃ l : List Nat, l.length = n ∧ (∀ x ∈ l, P x) ∧ (∀ x ∈ l, L ≤ x) ∧
      l.Pairwise (fun a b => a + p ≤ b) := by
  intro n
  induction n with
  | zero =>
    intro L
    refine ⟨[], rfl, ?_, ?_, List.Pairwise.nil⟩
    · intro x hx; nomatch hx
    · intro x hx; nomatch hx
  | succ n ih =>
    intro L
    obtain ⟨i, hLi, hPi⟩ := hcof L
    obtain ⟨l, hlen, hP, hge, hsp⟩ := ih (i + p)
    refine ⟨i :: l, by simp [hlen], ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hPi
      · exact hP x hx
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hLi
      · exact Nat.le_trans hLi (Nat.le_trans (Nat.le_add_right i p) (hge x hx))
    · exact List.pairwise_cons.mpr ⟨fun b hb => hge b hb, hsp⟩

open Classical in
/-- **THE BASE CHOICE, CERTIFIED** (§39.3) — the capstone of the selection.  Given
    a finite witness bank and a `p`-spaced candidate list longer than twice the
    bank, there is a base in the list whose whole window `[i, i+p)` is CONSTANT
    for EVERY witness — i.e. `mixKernels_ok`'s `hstab` holds at that base for the
    entire bank.  Combines `spoiled_length_le_two` (each witness spoils ≤2 spaced
    candidates, via the rank ceiling) with the pigeonhole `exists_good_candidate`,
    then converts "endpoints agree" to full window constancy by
    `window_const_iff_ends`.

    With `mixSelect_of_highBank` supplying the SERVING side (the bank picked above
    the range serves every window by backward forcing), this is the whole of
    `MixSelect` for a single chain — and since the high bank makes the kernels
    independent, it applies to each kernel separately. -/
theorem exists_stable_base (hI : RCC5Interp I) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    (ws : List α) (hws : ∀ w ∈ ws, I.dom w) (p : Nat) (hp : 0 < p)
    (l : List Nat) (hsp : l.Pairwise (fun a b => a + p ≤ b))
    (hlen : 2 * ws.length < l.length) :
    ∃ i ∈ l, ∀ w ∈ ws, ∀ b, b < p → I.rho w (c (i + b)) = I.rho w (c i) := by
  obtain ⟨i, hi, hgood⟩ :=
    exists_good_candidate p
      (fun w x => decide (I.rho (c x) w ≠ I.rho (c (x + p - 1)) w)) ws l
      (fun w hw l' hsp' hall =>
        spoiled_length_le_two hI c hdom hstep (hws w hw) p hp l' hsp'
          (fun x hx => of_decide_eq_true (hall x hx)))
      hsp hlen
  refine ⟨i, hi, fun w hw b hb => ?_⟩
  have hends : I.rho (c i) w = I.rho (c (i + p - 1)) w := by
    have := hgood w hw
    simp only [decide_eq_false_iff_not, Decidable.not_not] at this
    exact this
  exact window_const_iff_ends hI hdom hstep (hws w hw) i p hp hends b hb

/-- **THE STABILITY HALF, AT REAL EXTRACTION DATA** (§39.5) — `exists_stable_base`
    fed by `exists_spaced_list`.  For a finite witness bank and ANY cofinal
    supply of candidate positions (`P` = "is a type-recurrence base", cofinal by
    `rr_segment_from`), there is a position satisfying `P` whose whole window is
    constant for EVERY witness.  This is `mixKernels_ok`'s `hstab` for one kernel,
    with no hypothesis left except the cofinality the extraction already has.
    Because the high bank (`mixSelect_of_highBank`) makes the kernels
    independent, applying this per kernel discharges `hstab` for the family. -/
theorem exists_stable_recurrence (hI : RCC5Interp I) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    (ws : List α) (hws : ∀ w ∈ ws, I.dom w) (p : Nat) (hp : 0 < p)
    (P : Nat → Prop) (hcof : ∀ L, ∃ i, L ≤ i ∧ P i) (L : Nat) :
    ∃ i, L ≤ i ∧ P i ∧
      ∀ w ∈ ws, ∀ b, b < p → I.rho w (c (i + b)) = I.rho w (c i) := by
  obtain ⟨l, hlen, hP, hge, hsp⟩ :=
    exists_spaced_list P hcof p (2 * ws.length + 1) L
  obtain ⟨i, hi, hgood⟩ :=
    exists_stable_base hI c hdom hstep ws hws p hp l hsp (by omega)
  exact ⟨i, hge i hi, hP i hi, hgood⟩

/-- **THE CANDIDATE RANGE, EXPOSED BEFORE THE BANK** (§39.5) — the lemma that
    makes the high-bank construction formally coherent.

    The subtlety: `exists_stable_base` needs a candidate list longer than
    `2·|ws|`, but the high bank must be picked ABOVE the candidate range — so if
    the list length were driven by `|ws|` the two would be circular.  It is not,
    because the bank size is bounded A PRIORI (kernels × phase types × demands,
    all bounded by `C₀`).  Taking a size bound `S` as input, the list is built
    FIRST, its top `M` is exposed, and only THEN is `ws` quantified:

    `∃ M, ∀ ws, |ws| ≤ S → ∃ i, …, i + p ≤ M ∧ (stability for all of ws)`

    That quantifier order — `M` before `ws` — is the whole content.  The caller
    picks the bank at or above `M`, `mixSelect_of_highBank` then makes it serve
    every window (all of which end at or below `M`), and stability is already
    guaranteed here. -/
theorem stable_base_range (hI : RCC5Interp I) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    (p : Nat) (hp : 0 < p) (S : Nat)
    (P : Nat → Prop) (hcof : ∀ L, ∃ i, L ≤ i ∧ P i) (L : Nat) :
    ∃ M, ∀ ws : List α, (∀ w ∈ ws, I.dom w) → ws.length ≤ S →
      ∃ i, L ≤ i ∧ i + p ≤ M ∧ P i ∧
        ∀ w ∈ ws, ∀ b, b < p → I.rho w (c (i + b)) = I.rho w (c i) := by
  obtain ⟨l, hlen, hP, hge, hsp⟩ := exists_spaced_list P hcof p (2 * S + 1) L
  obtain ⟨Bmax, hBmax⟩ := list_bound (fun x => x) l
  refine ⟨Bmax + p, fun ws hws hS => ?_⟩
  obtain ⟨i, hi, hgood⟩ :=
    exists_stable_base hI c hdom hstep ws hws p hp l hsp (by omega)
  exact ⟨i, hge i hi, by have := hBmax i hi; omega, hP i hi, hgood⟩

/-- **THE KERNEL INTERFACE, FROM MODEL-SIDE DATA** (§39.5) — `hty` and `hstab`
    together, for one round-robin kernel and a given finite witness bank.

    Chain of reasoning: `rr_segment_from` gives a recurrence base past ANY
    threshold, but with a base-dependent period; its periods are bounded, so
    `cofinal_fixed_param` extracts ONE period `q` that still recurs cofinally;
    `exists_stable_recurrence` then picks, among those cofinally many `q`-bases,
    one whose whole window is constant for the entire bank.

    The output is exactly what `mixKernels_ok` consumes per kernel: a base `i`
    and period `q` with `mty (c i) = mty (c (i+q))` (its `hty`) and constant
    external rows across the window (its `hstab`).  With
    `mixSelect_of_highBank` supplying the serving side and the high bank making
    the kernels independent, this is the per-kernel interface complete. -/
theorem kernel_interface_of_persistAll (hI : RCC5Interp I) (C0 : Concept)
    (Ds : List Concept) (hL : 0 < Ds.length) (x0 : α)
    (h0 : persistAll I C0 Ds x0)
    (ws : List α) (hws : ∀ w ∈ ws, I.dom w) (L : Nat) :
    ∃ i q, L ≤ i ∧ 0 < q ∧
      mty C0 I (rrPt hI C0 Ds hL x0 h0 i)
        = mty C0 I (rrPt hI C0 Ds hL x0 h0 (i + q)) ∧
      (∀ w ∈ ws, ∀ b, b < q →
        I.rho w (rrPt hI C0 Ds hL x0 h0 (i + b))
          = I.rho w (rrPt hI C0 Ds hL x0 h0 i)) := by
  classical
  -- one period that still recurs cofinally
  obtain ⟨q, _, hq⟩ :=
    cofinal_fixed_param ((allListsLe (cl C0) (cl C0).length).length * Ds.length)
      (fun i q => 0 < q ∧ mty C0 I (rrPt hI C0 Ds hL x0 h0 i)
        = mty C0 I (rrPt hI C0 Ds hL x0 h0 (i + q)))
      (by
        intro L
        obtain ⟨i, pp', hL0, _, hp, _, hbnd, hty⟩ :=
          rr_segment_from hI C0 Ds hL x0 h0 L
        exact ⟨i, pp', hL0, hbnd, hp, hty⟩)
  -- positivity of that period, from any one of its cofinally many witnesses
  obtain ⟨i0, _, hq0, _⟩ := hq 0
  -- a base among them whose window is stable for the whole bank
  obtain ⟨i, hLi, hPi, hstab⟩ :=
    exists_stable_recurrence hI (rrPt hI C0 Ds hL x0 h0)
      (rrPt_dom hI C0 Ds hL x0 h0) (rrPt_step hI C0 Ds hL x0 h0) ws hws q hq0
      (fun i => 0 < q ∧ mty C0 I (rrPt hI C0 Ds hL x0 h0 i)
        = mty C0 I (rrPt hI C0 Ds hL x0 h0 (i + q))) hq L
  exact ⟨i, q, hLi, hq0, hPi.2, hstab⟩

/-- **THE KERNEL RANGE** (§39.5) — `kernel_interface_of_persistAll` with the
    candidate range EXPOSED, so the bank can be picked above it.  The period `q`
    is extracted first (by `cofinal_fixed_param`, independent of any bank), then
    `stable_base_range` fixes the top `M`; only afterwards is the bank `ws`
    quantified.  Output: for every bank of size `≤ S`, a base `i ≥ L` whose whole
    window ends at or below `M`, is a `q`-recurrence, and is stable for the bank. -/
theorem kernel_range_of_persistAll (hI : RCC5Interp I) (C0 : Concept)
    (Ds : List Concept) (hL : 0 < Ds.length) (x0 : α)
    (h0 : persistAll I C0 Ds x0) (S : Nat) (L : Nat) :
    ∃ q M, 0 < q ∧
      ∀ ws : List α, (∀ w ∈ ws, I.dom w) → ws.length ≤ S →
        ∃ i, L ≤ i ∧ i + q ≤ M ∧
          mty C0 I (rrPt hI C0 Ds hL x0 h0 i)
            = mty C0 I (rrPt hI C0 Ds hL x0 h0 (i + q)) ∧
          (∀ w ∈ ws, ∀ b, b < q →
            I.rho w (rrPt hI C0 Ds hL x0 h0 (i + b))
              = I.rho w (rrPt hI C0 Ds hL x0 h0 i)) := by
  classical
  obtain ⟨q, _, hq⟩ :=
    cofinal_fixed_param ((allListsLe (cl C0) (cl C0).length).length * Ds.length)
      (fun i q => 0 < q ∧ mty C0 I (rrPt hI C0 Ds hL x0 h0 i)
        = mty C0 I (rrPt hI C0 Ds hL x0 h0 (i + q)))
      (by
        intro L'
        obtain ⟨i, pp', hL0, _, hp, _, hbnd, hty⟩ :=
          rr_segment_from hI C0 Ds hL x0 h0 L'
        exact ⟨i, pp', hL0, hbnd, hp, hty⟩)
  obtain ⟨i0, _, hq0, _⟩ := hq 0
  obtain ⟨M, hM⟩ :=
    stable_base_range hI (rrPt hI C0 Ds hL x0 h0)
      (rrPt_dom hI C0 Ds hL x0 h0) (rrPt_step hI C0 Ds hL x0 h0) q hq0 S
      (fun i => 0 < q ∧ mty C0 I (rrPt hI C0 Ds hL x0 h0 i)
        = mty C0 I (rrPt hI C0 Ds hL x0 h0 (i + q))) hq L
  refine ⟨q, M, hq0, fun ws hws hS => ?_⟩
  obtain ⟨i, hLi, hiM, hPi, hstab⟩ := hM ws hws hS
  exact ⟨i, hLi, hiM, hPi.2, hstab⟩

open Classical in
/-- **THE WITNESS BANK** (§39.5) — the serving side, supplied at the range top.

    For a chain whose types recur cofinally past `T`, and any level `M`, there is
    a witness list `ws` of size at most `2·|cl C0|` such that EVERY `DR`/`PP`
    demand occurring at any phase past `T` is served by a member that is
    `r`-related to the chain at every level up to `M` — in particular AT `M`,
    which is what `mixSelect_of_highBank` consumes, and at every lower level, so
    it serves any window ending at or below `M`.

    Construction: one slot per `(D, r)` with `D ∈ cl C0` and `r ∈ {DR, PP}`,
    filled by `dr_witness_all_below` / `pp_witness_all_below` at bound `M` when
    such a witness exists and by the harmless default `c 0` otherwise — so the
    size bound is structural (`flatMap` of two-element lists), independent of the
    model.  Covering uses `cl_ex`: a demand's argument is itself in the closure,
    so it really does have a slot. -/
theorem exists_bank (hI : RCC5Interp I) (C0 : Concept) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    (T M : Nat)
    (hrecall : ∀ a, T ≤ a → ∀ N, ∃ m, N ≤ m ∧ mty C0 I (c m) = mty C0 I (c a)) :
    ∃ ws : List α, (∀ w ∈ ws, I.dom w) ∧ ws.length ≤ 2 * (cl C0).length ∧
      ∀ a, T ≤ a → ∀ r D, (r = dr ∨ r = pp) →
        Concept.ex r D ∈ mty C0 I (c a) →
        ∃ w ∈ ws, D ∈ mty C0 I w ∧ ∀ b, b ≤ M → I.rho (c b) w = r := by
  classical
  -- one slot per (argument, relation); `c 0` is the harmless filler
  let good : Atom → Concept → α → Prop :=
    fun r D w => I.dom w ∧ D ∈ mty C0 I w ∧ ∀ b, b ≤ M → I.rho (c b) w = r
  let pick : Atom → Concept → α :=
    fun r D => if h : ∃ w, good r D w then Classical.choose h else c 0
  have hpick_dom : ∀ r D, I.dom (pick r D) := by
    intro r D
    show I.dom (if h : ∃ w, good r D w then Classical.choose h else c 0)
    split
    · next h => exact (Classical.choose_spec h).1
    · exact hdom 0
  refine ⟨(cl C0).flatMap (fun D => [pick dr D, pick pp D]), ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨D, _, hmem⟩ := List.mem_flatMap.mp hw
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hpick_dom dr D
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hpick_dom pp D
      · nomatch hmem
  · -- the size bound is structural
    have : ((cl C0).flatMap (fun D => [pick dr D, pick pp D])).length
        = 2 * (cl C0).length := by
      induction (cl C0) with
      | nil => rfl
      | cons a rest ih => simp [List.flatMap_cons] at ih ⊢; omega
    omega
  · -- covering
    intro a hTa r D hr hmem
    have hDcl : D ∈ cl C0 := cl_ex (mty_sub _ hmem)
    have hex : ∃ w, good r D w := by
      have hrecT : ∀ N, ∃ m, N ≤ m ∧ mty C0 I (c m) = mty C0 I (c a) := hrecall a hTa
      rcases hr with rfl | rfl
      · obtain ⟨w, hw, hDw, hall⟩ :=
          dr_witness_all_below hI hdom hstep hrecT hmem M
        exact ⟨w, hw, hDw, hall⟩
      · obtain ⟨w, hw, hDw, hall⟩ :=
          pp_witness_all_below hI hdom hstep hrecT hmem M
        exact ⟨w, hw, hDw, hall⟩
    have hspec : good r D (pick r D) := by
      show good r D (if h : ∃ w, good r D w then Classical.choose h else c 0)
      rw [dif_pos hex]
      exact Classical.choose_spec hex
    refine ⟨pick r D, ?_, hspec.2.1, hspec.2.2⟩
    refine List.mem_flatMap.mpr ⟨D, hDcl, ?_⟩
    rcases hr with rfl | rfl
    · exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

/-- **THE FAMILY RANGE** (§39.5) — the whole per-kernel interface of
    `mixKernels_ok` with the candidate ranges exposed BEFORE the bank, which is
    what `mixSelect_of_highBank` needs in order to be applicable.  Periods `pk`
    and range tops `M` are fixed first; then for ANY bank of size `≤ S` there are
    bases giving `hty`, `hstab`, `hrectQ`, and every window ending at or below its
    kernel's `M` — so a bank picked at those `M`s serves every window. -/
theorem family_range (hI : RCC5Interp I) (C0 : Concept) {n : Nat}
    (Ds : Fin n → List Concept) (hL : ∀ k, 0 < (Ds k).length)
    (x0 : Fin n → α) (h0 : ∀ k, persistAll I C0 (Ds k) (x0 k)) (S : Nat) (L : Nat)
    (hN : Fin n → Fin n → Nat)
    (hconst : ∀ k k', k ≠ k' → ∀ i j, hN k k' ≤ i → hN k k' ≤ j →
      I.rho (classChain hI C0 Ds hL x0 h0 k i)
            (classChain hI C0 Ds hL x0 h0 k' j)
        = I.rho (classChain hI C0 Ds hL x0 h0 k (hN k k'))
                (classChain hI C0 Ds hL x0 h0 k' (hN k k'))) :
    ∃ pk M : Fin n → Nat, (∀ k, 0 < pk k) ∧
      ∀ ws : List α, (∀ w ∈ ws, I.dom w) → ws.length ≤ S →
        ∃ ik : Fin n → Nat,
          (∀ k, L ≤ ik k) ∧
          (∀ k, ik k + pk k ≤ M k) ∧
          (∀ k, mty C0 I (classChain hI C0 Ds hL x0 h0 k (ik k))
                = mty C0 I (classChain hI C0 Ds hL x0 h0 k (ik k + pk k))) ∧
          (∀ w ∈ ws, ∀ k b, b < pk k →
            I.rho w (classChain hI C0 Ds hL x0 h0 k (ik k + b))
              = I.rho w (classChain hI C0 Ds hL x0 h0 k (ik k))) ∧
          (∀ k k', k ≠ k' → ∀ a b,
            I.rho (classChain hI C0 Ds hL x0 h0 k (ik k + a))
                  (classChain hI C0 Ds hL x0 h0 k' (ik k' + b))
              = I.rho (classChain hI C0 Ds hL x0 h0 k (ik k))
                      (classChain hI C0 Ds hL x0 h0 k' (ik k'))) := by
  classical
  obtain ⟨B, hB⟩ := exists_bound2 n hN
  have hk : ∀ k : Fin n, ∃ qM : Nat × Nat, 0 < qM.1 ∧
      ∀ ws : List α, (∀ w ∈ ws, I.dom w) → ws.length ≤ S →
        ∃ i, max B L ≤ i ∧ i + qM.1 ≤ qM.2 ∧
          mty C0 I (classChain hI C0 Ds hL x0 h0 k i)
            = mty C0 I (classChain hI C0 Ds hL x0 h0 k (i + qM.1)) ∧
          (∀ w ∈ ws, ∀ b, b < qM.1 →
            I.rho w (classChain hI C0 Ds hL x0 h0 k (i + b))
              = I.rho w (classChain hI C0 Ds hL x0 h0 k i)) := by
    intro k
    obtain ⟨q, M, hq, hspec⟩ :=
      kernel_range_of_persistAll hI C0 (Ds k) (hL k) (x0 k) (h0 k) S (max B L)
    exact ⟨(q, M), hq, hspec⟩
  obtain ⟨g, hg⟩ := Classical.axiomOfChoice hk
  refine ⟨fun k => (g k).1, fun k => (g k).2, fun k => (hg k).1, fun ws hws hS => ?_⟩
  have hpick : ∀ k : Fin n, ∃ i, max B L ≤ i ∧ i + (g k).1 ≤ (g k).2 ∧
      mty C0 I (classChain hI C0 Ds hL x0 h0 k i)
        = mty C0 I (classChain hI C0 Ds hL x0 h0 k (i + (g k).1)) ∧
      (∀ w ∈ ws, ∀ b, b < (g k).1 →
        I.rho w (classChain hI C0 Ds hL x0 h0 k (i + b))
          = I.rho w (classChain hI C0 Ds hL x0 h0 k i)) :=
    fun k => (hg k).2 ws hws hS
  obtain ⟨ik, hik⟩ := Classical.axiomOfChoice hpick
  refine ⟨ik, fun k => Nat.le_trans (Nat.le_max_right B L) (hik k).1,
    fun k => (hik k).2.1, fun k => (hik k).2.2.1, ?_, ?_⟩
  · exact fun w hw k b hb => (hik k).2.2.2 w hw b hb
  · exact family_hrectQ (classChain hI C0 Ds hL x0 h0) ik hN hconst
      (fun k k' _ => Nat.le_trans (hB k k') (Nat.le_trans (Nat.le_max_left B L) (hik k).1))
      (fun k k' _ => Nat.le_trans (hB k k') (Nat.le_trans (Nat.le_max_left B L) (hik k').1))

/-- **THE FAMILY INTERFACE** (§39.5) — every per-kernel obligation of
    `mixKernels_ok` except the demand routing, discharged together from model-side
    data.  Given `n` `persistAll` sites whose class towers are pairwise
    NON-COMPARABLE (`hconst`, i.e. `classify_cross` disjunct 1 — comparable ones
    having been merged away by §38), and a global witness bank `ws`, there are
    bases `ik` and periods `pk` with:

    * `hp`     — every period positive;
    * `hty`    — per-kernel type recurrence at `(ik k, pk k)`;
    * `hstab`  — every bank witness's row constant across every kernel's window;
    * `hrectQ` — the cross-kernel rectangle.

    The scheduling that made §39 look circular is handled by the THRESHOLD: the
    joint cross-constancy horizon `B` is computed FIRST (`exists_bound2` over the
    finitely many pairs), and each kernel's base is then chosen above `B` —
    possible because `kernel_interface_of_persistAll` delivers its base past any
    threshold.  So `hrectQ` and `hty`/`hstab` are satisfied at the SAME bases. -/
theorem family_interface (hI : RCC5Interp I) (C0 : Concept) {n : Nat}
    (Ds : Fin n → List Concept) (hL : ∀ k, 0 < (Ds k).length)
    (x0 : Fin n → α) (h0 : ∀ k, persistAll I C0 (Ds k) (x0 k))
    (ws : List α) (hws : ∀ w ∈ ws, I.dom w)
    (hN : Fin n → Fin n → Nat)
    (hconst : ∀ k k', k ≠ k' → ∀ i j, hN k k' ≤ i → hN k k' ≤ j →
      I.rho (classChain hI C0 Ds hL x0 h0 k i)
            (classChain hI C0 Ds hL x0 h0 k' j)
        = I.rho (classChain hI C0 Ds hL x0 h0 k (hN k k'))
                (classChain hI C0 Ds hL x0 h0 k' (hN k k'))) :
    ∃ ik pk : Fin n → Nat,
      (∀ k, 0 < pk k) ∧
      (∀ k, mty C0 I (classChain hI C0 Ds hL x0 h0 k (ik k))
            = mty C0 I (classChain hI C0 Ds hL x0 h0 k (ik k + pk k))) ∧
      (∀ w ∈ ws, ∀ k b, b < pk k →
        I.rho w (classChain hI C0 Ds hL x0 h0 k (ik k + b))
          = I.rho w (classChain hI C0 Ds hL x0 h0 k (ik k))) ∧
      (∀ k k', k ≠ k' → ∀ a b,
        I.rho (classChain hI C0 Ds hL x0 h0 k (ik k + a))
              (classChain hI C0 Ds hL x0 h0 k' (ik k' + b))
          = I.rho (classChain hI C0 Ds hL x0 h0 k (ik k))
                  (classChain hI C0 Ds hL x0 h0 k' (ik k'))) := by
  classical
  -- the joint cross-constancy horizon, computed BEFORE any base is chosen
  obtain ⟨B, hB⟩ := exists_bound2 n hN
  have hper : ∀ k : Fin n, ∃ ip : Nat × Nat, B ≤ ip.1 ∧ 0 < ip.2 ∧
      mty C0 I (classChain hI C0 Ds hL x0 h0 k ip.1)
        = mty C0 I (classChain hI C0 Ds hL x0 h0 k (ip.1 + ip.2)) ∧
      (∀ w ∈ ws, ∀ b, b < ip.2 →
        I.rho w (classChain hI C0 Ds hL x0 h0 k (ip.1 + b))
          = I.rho w (classChain hI C0 Ds hL x0 h0 k ip.1)) := by
    intro k
    obtain ⟨i, q, hBi, hq, hty, hstab⟩ :=
      kernel_interface_of_persistAll hI C0 (Ds k) (hL k) (x0 k) (h0 k) ws hws B
    exact ⟨(i, q), hBi, hq, hty, hstab⟩
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice hper
  refine ⟨fun k => (f k).1, fun k => (f k).2, fun k => (hf k).2.1,
    fun k => (hf k).2.2.1, ?_, ?_⟩
  · exact fun w hw k b hb => (hf k).2.2.2 w hw b hb
  · exact family_hrectQ (classChain hI C0 Ds hL x0 h0) (fun k => (f k).1) hN hconst
      (fun k k' _ => Nat.le_trans (hB k k') (hf k).1)
      (fun k k' _ => Nat.le_trans (hB k k') (hf k').1)

/-- **THE COFINAL-WITNESS QUESTION** (§39.2) — what the whole mixed selection now
    rests on, stated on a SINGLE chain.  Every horizontal demand occurring
    anywhere on the chain is served by a witness bearing that relation to the
    ENTIRE chain.  Equivalently: the decreasing family
    `W_n = {w : ρ (c n) w = r ∧ D ∈ mty w}` (decreasing by backward forcing) has
    nonempty intersection.  Each `W_n` is nonempty exactly when the demand is
    live at level `n`. -/
def CofinalWitness (I : Interp α) (C0 : Concept) (c : Nat → α) : Prop :=
  ∀ (n : Nat) (r : Atom) (D : Concept), (r = dr ∨ r = pp) →
    Concept.ex r D ∈ mty C0 I (c n) →
    ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧ ∀ j, I.rho (c j) w = r

/-- The family `W_n` really is DECREASING — backward forcing, so the cofinal
    question is exactly "a decreasing family of nonempty sets has a common
    element", not an arbitrary intersection. -/
theorem witness_sets_decreasing (hI : RCC5Interp I) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    {w : α} (hw : I.dom w) {r : Atom} (hr : r = dr ∨ r = pp) {n : Nat}
    (h : I.rho (c n) w = r) : ∀ j, j ≤ n → I.rho (c j) w = r := by
  rcases hr with rfl | rfl
  · exact backward_forcing_dr hI hdom hstep hw h
  · exact backward_forcing_pp hI hdom hstep hw h

/-- **THE R6 SELECTION OBLIGATION** (§39.3) — the one thing the MIXED assembly
    still owes, stated rather than assumed (the project's `CompletenessObligation`
    pattern).  For every kernel `k` and every horizontal (`DR`/`PP`) demand of one
    of its phases, there is a witness that (i) serves that demand across `k`'s
    WHOLE window (what `kernel_site` gives by backward forcing) and (ii) has a
    CONSTANT row on EVERY kernel's window — which is exactly
    `mixKernels_ok`'s `hstab` for the witness once it joins `β`.

    Both ways of discharging (ii) are certified (`window_stab_dichotomy`); what
    is NOT proved is that a single witness can meet (i) and (ii) SIMULTANEOUSLY
    for all kernels at once — the joint selection.  Probe `wp91` parts G/H/K found
    no counterexample (0 failures in ~10,700 configurations, 2 and 3 kernels,
    periods ≥ 2, and with bases forced late once the prefix is long enough that
    truncation is excluded), so this is well-supported but UNPROVED. -/
def MixSelect (I : Interp α) (C0 : Concept) {m : Nat}
    (ck : Fin m → Nat → α) (ik pk : Fin m → Nat) : Prop :=
  ∀ (k : Fin m) (a : Nat) (r : Atom) (D : Concept), a < pk k →
    (r = dr ∨ r = pp) → Concept.ex r D ∈ mty C0 I (ck k (ik k + a)) →
    ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
      (∀ b, b < pk k → I.rho (ck k (ik k + b)) w = r) ∧
      (∀ k' b, b < pk k' → I.rho w (ck k' (ik k' + b)) = I.rho w (ck k' (ik k')))

/-- `MixSelect`'s cross-condition is DISCHARGEABLE FROM EITHER BRANCH — the
    dichotomy in the obligation's own shape.  So the obligation is not asking for
    new relational mathematics; it asks only that ONE witness can be chosen
    meeting the branches for all kernels at once. -/
theorem mixSelect_cross_of_dichotomy (hI : RCC5Interp I) {m : Nat}
    (ck : Fin m → Nat → α) (hdom : ∀ k n, I.dom (ck k n))
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = pp)
    (ik pk : Fin m → Nat) {w : α} (hw : I.dom w)
    (h : ∀ k', (I.rho (ck k' (ik k' + pk k')) w = dr ∨
                I.rho (ck k' (ik k' + pk k')) w = pp) ∨
               (∀ x y, ik k' ≤ x → ik k' ≤ y →
                 I.rho (ck k' x) w = I.rho (ck k' y) w)) :
    ∀ k' b, b < pk k' → I.rho w (ck k' (ik k' + b)) = I.rho w (ck k' (ik k')) :=
  fun k' b hb =>
    window_stab_dichotomy hI (ck k') (hdom k') (hstep k') hw (ik k') (pk k') (h k') b hb

/-- **THE COLLAPSE** (§39.2) — the multi-kernel JOINT selection reduces to a
    SINGLE-CHAIN question.  Suppose every horizontal (`DR`/`PP`) phase demand is
    served by a witness from a FIXED finite bank whose relation to its OWN chain
    is that value at EVERY level (`∀ j, ρ (ck k j) w = r` — "cofinal serving").
    Then there is a horizon `H` such that EVERY base vector above `H` satisfies
    `MixSelect`.

    Why this dissolves the §39 cycle: serving no longer depends on where the
    window sits (it holds at *all* levels, so no witness must be picked above the
    window), and the bank is fixed in advance, so `stab_window_family_multi`
    gives one horizon for all of it. The circular dependency — witness above
    base, base above witness's horizon — never forms. Note also that the
    §39.3 dichotomy is not even needed here: pure "push past" suffices.

    So the whole remaining question is the hypothesis `hcover`: does every
    persistent `∃DR`/`∃PP` demand admit a witness related to the whole chain?
    That is ONE chain and ONE demand — no kernels, no bases, no windows. -/
theorem mixSelect_of_cofinal_bank (hI : RCC5Interp I) (C0 : Concept) {m : Nat}
    (ck : Fin m → Nat → α) (hdom : ∀ k n, I.dom (ck k n))
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = pp)
    (p : Nat) (ws : List α) (hws : ∀ w ∈ ws, I.dom w)
    (hcover : ∀ (k : Fin m) (n : Nat) (r : Atom) (D : Concept),
      (r = dr ∨ r = pp) → Concept.ex r D ∈ mty C0 I (ck k n) →
      ∃ w ∈ ws, D ∈ mty C0 I w ∧ ∀ j, I.rho (ck k j) w = r) :
    ∃ H, ∀ ik pk : Fin m → Nat, (∀ k, H ≤ ik k) → (∀ k, pk k ≤ p) →
      MixSelect I C0 ck ik pk := by
  obtain ⟨H, hH⟩ := stab_window_family_multi hI ck hdom hstep ws hws p
  refine ⟨H, fun ik pk hik hpk => ?_⟩
  intro k a r D ha hr hmem
  obtain ⟨w, hwmem, hD, hall⟩ := hcover k (ik k + a) r D hr hmem
  exact ⟨w, hws w hwmem, hD, fun b _ => hall (ik k + b),
    fun k' b hb => hH ik hik w hwmem k' b (Nat.lt_of_lt_of_le hb (hpk k'))⟩

/-- **THE HIGH-BANK CONSTRUCTION** (§39.2) — the serving side of `MixSelect` comes
    FREE once the witnesses are picked ABOVE the whole candidate range.

    `witness_sets_decreasing` says `W_n` shrinks as `n` grows, so a witness chosen
    at a level `M k` at or above the top of kernel `k`'s window serves EVERY
    position of that window by backward forcing.  Consequently the bank does NOT
    depend on where the bases end up: fix the range, pick the bank above it, and
    the base choices DECOUPLE — each base need only dodge the finitely many
    values spoiled by the OTHER kernels' (already fixed) witnesses.

    This is precisely the step part O's greedy got wrong: it picked each witness
    just above its own base, so later witnesses kept invalidating earlier
    windows.  Picking the whole bank above the range removes the dependency
    instead of scheduling around it, and no product counting is needed.
    Probe `wp91` part U: serving held in 400/400 systems, the spoil-count bound
    `2(p-1)` held in 400/400 (worst exactly 2 and 4 at `p` = 2,3), and the
    decoupled base vector was found in 400/400. -/
theorem mixSelect_of_highBank (hI : RCC5Interp I) (C0 : Concept) {m : Nat}
    (ck : Fin m → Nat → α) (hdom : ∀ k n, I.dom (ck k n))
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = pp)
    (ik pk : Fin m → Nat) (M : Fin m → Nat)
    (hbelow : ∀ k, ik k + pk k ≤ M k)
    (hbank : ∀ k a r D, a < pk k → (r = dr ∨ r = pp) →
      Concept.ex r D ∈ mty C0 I (ck k (ik k + a)) →
      ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧
        I.rho (ck k (M k)) w = r ∧
        (∀ k' b, b < pk k' →
          I.rho w (ck k' (ik k' + b)) = I.rho w (ck k' (ik k')))) :
    MixSelect I C0 ck ik pk := by
  intro k a r D ha hr hmem
  obtain ⟨w, hw, hD, hMw, hstabw⟩ := hbank k a r D ha hr hmem
  refine ⟨w, hw, hD, fun b hb => ?_, hstabw⟩
  exact witness_sets_decreasing hI (ck k) (hdom k) (hstep k) hw hr hMw
    (ik k + b) (by have := hbelow k; omega)

/-- Two ascending `PP`-kernels indexed by `Bool`; every value read off
    the model, the cross-value `Q` from the two bases. -/
noncomputable def vkernel2 (I : Interp α) (C0 : Concept) (ck : Bool → Nat → α)
    (ik pk : Bool → Nat) : MultiTier Empty Bool where
  E := fun e f => I.rho e.elim f.elim
  K := fun k f => I.rho (ck k (ik k)) f.elim
  Q := fun k k' => I.rho (ck k (ik k)) (ck k' (ik k'))
  up := fun _ => true
  tauE := fun e => e.elim
  p := pk
  phase := fun k a => mty C0 I (ck k (ik k + a))

/-- THE TWO-KERNEL BLOCK IS VALID: two ascending chains with distinct
    bases (`hbase`), each type-recurrent (`hty`) and serving the single
    chain demand `∃PP.G`/`∃EQ` (`hdemands`), with constant cross-rows
    (`hrectQ`), give a full `MultiTierOk` — `kq_all` cross-kernel
    `∀`-firing via `mty_all`+`hrectQ`. -/
theorem vkernel2_ok (hI : RCC5Interp I) (C0 G : Concept) (ck : Bool → Nat → α)
    (hdom : ∀ k n, I.dom (ck k n))
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = pp)
    {ik pk : Bool → Nat} (hp : ∀ k, 0 < pk k)
    (hty : ∀ k, mty C0 I (ck k (ik k)) = mty C0 I (ck k (ik k + pk k)))
    (hG0 : ∀ k, G ∈ mty C0 I (ck k (ik k)))
    (hbase : ck true (ik true) ≠ ck false (ik false))
    (hrectQ : ∀ k k', k ≠ k' → ∀ a b,
      I.rho (ck k (ik k + a)) (ck k' (ik k' + b))
        = I.rho (ck k (ik k)) (ck k' (ik k')))
    (hdemands : ∀ k a r D, Concept.ex r D ∈ mty C0 I (ck k (ik k + a)) →
      (r = pp ∧ D = G) ∨ r = eq) :
    MultiTierOk (vkernel2 I C0 ck ik pk) := by
  have hinj : ∀ v w : Empty ⊕ Bool,
      Sum.elim (fun e : Empty => e.elim) (fun k : Bool => ck k (ik k)) v
        = Sum.elim (fun e : Empty => e.elim) (fun k : Bool => ck k (ik k)) w → v = w := by
    rintro (e | k) (f | k') h
    · exact e.elim
    · exact e.elim
    · exact f.elim
    · simp only [Sum.elim_inr] at h
      by_cases hk : k = k'
      · rw [hk]
      · exfalso
        cases k <;> cases k'
        · exact hk rfl
        · exact hbase h.symm
        · exact hbase h
        · exact hk rfl
  refine
    { hp := hp
      frame_q := readoff_qnet_frame hI (fun e : Empty => e.elim)
        (fun k : Bool => ck k (ik k)) (fun e => e.elim) (fun k => hdom k (ik k)) hinj
      e_clash := fun e => e.elim
      e_nobot := fun e => e.elim
      e_and := fun e => e.elim
      e_or := fun e => e.elim
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := fun e => e.elim
      ek_all := fun e => e.elim
      ke_all := fun _ _ _ _ _ _ f => f.elim
      kk_pp := fun k _ ha E hE b hb =>
        segment_kk_pp hI (fun n => hdom k n) (fun n => hstep k n) (hty k) ha hE b hb
      kk_ppi := fun k _ ha E hE b hb =>
        segment_kk_ppi hI (fun n => hdom k n) (fun n => hstep k n) (hty k) ha hE b hb
      kk_eq := fun k _ _ E hE => seg_eq hI (fun n => hdom k n) hE
      kq_all := ?_
      e_ex := fun e => e.elim
      k_ex := ?_ }
  · -- kq_all: cross-kernel `∀` fires through the constant cross-row
    intro k k' hkk a _ r c hmem hr b _
    apply mty_all hmem (hdom k' (ik k' + b))
    rw [hrectQ k k' hkk a b]
    exact hr
  · -- k_ex: each kernel serves its own `∃PP` via its chain
    intro k a _ r D hmem
    rcases hdemands k a r D hmem with ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, 0, hp k, hG0 k⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, seg_ex_eq hI (fun n => hdom k n) hmem⟩))

/-! ### Round E3h‴ (2026-07-24): cross-kernel `∃` — the last routing primitive

`vkernel2x_ok` extends `vkernel2_ok` with the ONE routing not yet in the
`vkernel` family: a kernel's `∃DR.Gx` demand served by the OTHER kernel
(`k_ex` disjunct 4), via the cross-`DR` value `Q k (!k)` (`hQdr`) and the
argument living in the other kernel's phase (`hGx`).  This is the shape
`cbothMT` hand-built (`∃DR.Dinf` served across), now GENERAL.  With it,
EVERY `k_ex`/`e_ex` disjunct has a certified general lemma — chain
(`vkernel_ok`), in-phase `∃EQ` (`seg_ex_eq`), down-into-kernel external
(`vkernel1_ok`), cross-kernel `∀` (`vkernel2_ok`), and now cross-kernel
`∃` — so the coverage recursion is pure assembly of certified routings. -/

/-- Two ascending kernels where each also serves an `∃DR.Gx` demand by
    the OTHER kernel (`k_ex` disjunct 4).  A genuine two-cluster
    certificate (the `∃DR` forces a second cluster). -/
theorem vkernel2x_ok (hI : RCC5Interp I) (C0 G Gx : Concept) (ck : Bool → Nat → α)
    (hdom : ∀ k n, I.dom (ck k n))
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = pp)
    {ik pk : Bool → Nat} (hp : ∀ k, 0 < pk k)
    (hty : ∀ k, mty C0 I (ck k (ik k)) = mty C0 I (ck k (ik k + pk k)))
    (hG0 : ∀ k, G ∈ mty C0 I (ck k (ik k)))
    (hbase : ck true (ik true) ≠ ck false (ik false))
    (hrectQ : ∀ k k', k ≠ k' → ∀ a b,
      I.rho (ck k (ik k + a)) (ck k' (ik k' + b))
        = I.rho (ck k (ik k)) (ck k' (ik k')))
    (hGx : ∀ k, Gx ∈ mty C0 I (ck (! k) (ik (! k))))
    (hQdr : ∀ k, I.rho (ck k (ik k)) (ck (! k) (ik (! k))) = dr)
    (hdemands : ∀ k a r D, Concept.ex r D ∈ mty C0 I (ck k (ik k + a)) →
      (r = pp ∧ D = G) ∨ (r = dr ∧ D = Gx) ∨ r = eq) :
    MultiTierOk (vkernel2 I C0 ck ik pk) := by
  have hinj : ∀ v w : Empty ⊕ Bool,
      Sum.elim (fun e : Empty => e.elim) (fun k : Bool => ck k (ik k)) v
        = Sum.elim (fun e : Empty => e.elim) (fun k : Bool => ck k (ik k)) w → v = w := by
    rintro (e | k) (f | k') h
    · exact e.elim
    · exact e.elim
    · exact f.elim
    · simp only [Sum.elim_inr] at h
      by_cases hk : k = k'
      · rw [hk]
      · exfalso
        cases k <;> cases k'
        · exact hk rfl
        · exact hbase h.symm
        · exact hbase h
        · exact hk rfl
  refine
    { hp := hp
      frame_q := readoff_qnet_frame hI (fun e : Empty => e.elim)
        (fun k : Bool => ck k (ik k)) (fun e => e.elim) (fun k => hdom k (ik k)) hinj
      e_clash := fun e => e.elim
      e_nobot := fun e => e.elim
      e_and := fun e => e.elim
      e_or := fun e => e.elim
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := fun e => e.elim
      ek_all := fun e => e.elim
      ke_all := fun _ _ _ _ _ _ f => f.elim
      kk_pp := fun k _ ha E hE b hb =>
        segment_kk_pp hI (fun n => hdom k n) (fun n => hstep k n) (hty k) ha hE b hb
      kk_ppi := fun k _ ha E hE b hb =>
        segment_kk_ppi hI (fun n => hdom k n) (fun n => hstep k n) (hty k) ha hE b hb
      kk_eq := fun k _ _ E hE => seg_eq hI (fun n => hdom k n) hE
      kq_all := ?_
      e_ex := fun e => e.elim
      k_ex := ?_ }
  · -- kq_all: unchanged from `vkernel2_ok`
    intro k k' hkk a _ r c hmem hr b _
    apply mty_all hmem (hdom k' (ik k' + b))
    rw [hrectQ k k' hkk a b]
    exact hr
  · -- k_ex: `∃PP`→chain, `∃DR.Gx`→the OTHER kernel, `∃EQ`→in-phase
    intro k a _ r D hmem
    rcases hdemands k a r D hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, 0, hp k, hG0 k⟩)
    · exact Or.inr (Or.inr (Or.inr
        ⟨! k, (by cases k <;> decide), hQdr k, 0, hp (! k), hGx k⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, seg_ex_eq hI (fun n => hdom k n) hmem⟩))

/-! ### Round E3h⁗ (2026-07-24): the DESCENDING vertical kernel

The mirror of `vkernel_ok` for `∃PPI` — a single DESCENDING kernel
(`up = false`, `PPI`-chain).  Same structure; `∃PPI` served by the chain
(`k_ex` disjunct 2, `cdir false = ppi`), `∀PP`/`∀PPI` via the descending
segment coherence `dsegment_kk_pp`/`dsegment_kk_ppi`, `∃EQ`/`∀EQ`
direction-agnostic (`seg_ex_eq`/`seg_eq`).  Completes the vertical
routing toolkit in BOTH directions (ascending `∃PP` + descending
`∃PPI`), as the fragment's kernels require. -/

/-- The β = Empty, κ = Unit DESCENDING kernel (`up = false`). -/
noncomputable def dvkernel (I : Interp α) (C0 : Concept) (c : Nat → α)
    (i p : Nat) : MultiTier Empty Unit where
  E := fun e f => I.rho e.elim f.elim
  K := fun _ f => I.rho (c i) f.elim
  Q := fun _ _ => I.rho (c i) (c i)
  up := fun _ => false
  tauE := fun e => e.elim
  p := fun _ => p
  phase := fun _ a => mty C0 I (c (i + a))

/-- THE DESCENDING VERTICAL KERNEL IS VALID (mirror of `vkernel_ok`): a
    descending `PPI`-chain, type-recurrent segment, `∃PPI.G`/`∃EQ`
    demands, gives a full `MultiTierOk`. -/
theorem dvkernel_ok (hI : RCC5Interp I) (C0 G : Concept) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n))
    (hstep : ∀ n, I.rho (c n) (c (n + 1)) = ppi)
    {i p : Nat} (hp : 0 < p)
    (hty : mty C0 I (c i) = mty C0 I (c (i + p)))
    (hG0 : G ∈ mty C0 I (c i))
    (hdemands : ∀ a r D, Concept.ex r D ∈ mty C0 I (c (i + a)) →
      (r = ppi ∧ D = G) ∨ r = eq) :
    MultiTierOk (dvkernel I C0 c i p) := by
  have hinj : ∀ v w : Empty ⊕ Unit,
      Sum.elim (fun e : Empty => e.elim) (fun _ : Unit => c i) v
        = Sum.elim (fun e : Empty => e.elim) (fun _ : Unit => c i) w → v = w := by
    rintro (e | ⟨⟩) (f | ⟨⟩) _
    · exact e.elim
    · exact e.elim
    · exact f.elim
    · rfl
  refine
    { hp := fun _ => hp
      frame_q := readoff_qnet_frame hI (fun e : Empty => e.elim)
        (fun _ : Unit => c i) (fun e => e.elim) (fun _ => hdom i) hinj
      e_clash := fun e => e.elim
      e_nobot := fun e => e.elim
      e_and := fun e => e.elim
      e_or := fun e => e.elim
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := fun e => e.elim
      ek_all := fun e => e.elim
      ke_all := fun _ _ _ _ _ _ f => f.elim
      kk_pp := fun _ _ ha E hE b hb =>
        dsegment_kk_pp hI hdom hstep hty ha hE b hb
      kk_ppi := fun _ _ ha E hE b hb =>
        dsegment_kk_ppi hI hdom hstep hty ha hE b hb
      kk_eq := fun _ _ _ E hE => seg_eq hI hdom hE
      kq_all := fun k k' hne => absurd rfl hne
      e_ex := fun e => e.elim
      k_ex := ?_ }
  intro _ a _ r D hmem
  rcases hdemands a r D hmem with ⟨rfl, rfl⟩ | rfl
  · exact Or.inr (Or.inl ⟨rfl, 0, hp, hG0⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, seg_ex_eq hI hdom hmem⟩))

/-! ### Round E3i (2026-07-24): the cluster-glue operation

`glueMTOk` combines a FINITE FAMILY of independent (cross-`PO`)
`MultiTierOk` clusters into ONE `MultiTierOk`, on the certified
`glueFam_ok` (all-cross-`PO`, empty pool).  This is the assembly's
"combine independent clusters" step: each cluster keeps its own
routings, cross-cluster edges are loose `PO` (inert on the ∀PO-free
fragment).  The cross-`∃`-LINKED case (a demand crossing clusters) uses
`vkernel2x_ok`'s routing instead; this handles the disjoint case that
the recursion produces when clusters share no demand. -/

/-- Weakening: a plain `MultiTierOk` block is `MTOkPool` against the
    EMPTY pool (the pool disjuncts of `e_ex`/`k_ex` simply go unused). -/
theorem mtOkPool_nil_of_mtOk {β κ : Type} [DecidableEq κ] {T : MultiTier β κ}
    (tag : Nat) (h : MultiTierOk T) : MTOkPool T tag [] where
  hp := h.hp
  frame_q := h.frame_q
  e_clash := h.e_clash
  e_nobot := h.e_nobot
  e_and := h.e_and
  e_or := h.e_or
  k_clash := h.k_clash
  k_nobot := h.k_nobot
  k_and := h.k_and
  k_or := h.k_or
  ee_all := h.ee_all
  ek_all := h.ek_all
  ke_all := h.ke_all
  kk_pp := h.kk_pp
  kk_ppi := h.kk_ppi
  kk_eq := h.kk_eq
  kq_all := h.kq_all
  e_ex := by
    intro e r c hmem
    rcases h.e_ex e r c hmem with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  k_ex := by
    intro k a ha r c hmem
    rcases h.k_ex k a ha r c hmem with h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))

/-- THE CLUSTER-GLUE: a finite family of independent `MultiTierOk`
    no-`∀PO` clusters glues (all-cross-`PO`) to a single `MultiTierOk`.
    Built directly on `glueFam_ok` with the empty pool. -/
theorem glueMTOk {β κ : Type} [DecidableEq κ] {B : Nat}
    {F : Fin B → MultiTier β κ}
    (hoks : ∀ b, MultiTierOk (F b)) (hnopo : ∀ b, MTNoPo (F b)) :
    MultiTierOk (glueFam F) :=
  glueFam_ok (P := []) (fun b => mtOkPool_nil_of_mtOk b.val (hoks b)) hnopo
    (fun _ hq => absurd hq List.not_mem_nil)

/-- The fragment's `∀PO`-vacuity for a `vkernel` (β = Empty externals
    vacuous; phases are model types with no `∀PO` by `mty_no_all_po`). -/
theorem vkernel_nopo {C0 : Concept} (hpo : POFree C0) (c : Nat → α) (i p : Nat) :
    MTNoPo (vkernel I C0 c i p) where
  ext := fun e => e.elim
  ker := fun _ _ _ _ => mty_no_all_po hpo

/-! ### Round E3j (2026-07-29): the single-`∃PP` GENERATOR

The first extraction on the vertical side: from a model element carrying
a persistent `∃PP.G` demand, BUILD a finite certificate carrying `C₀`.
This is `satisfiable_of_persistPP` — the vertical analogue of
`extract_hfrag`, for the fragment whose only existentials are ONE
persistent `∃PP.G` (plus `∃EQ`).  It threads: `persistPP_productive'`
(the demand's witness carries `G`) → `persistPP_chain'` (a chain carrying
`G` at EVERY rung — the correction of §18 made into a lemma) → a
type-recurrent segment → the root as a below-external whose `∃PP.G`
routes into the kernel (`vkernel1_ok`), with `chain_model_pp` placing the
root below the whole segment.  No `e_ex` recursion: the SINGLE demand is
chain-served, the root is the only external.  The MULTI-demand case (many
`∃PP.Gₖ`, each a kernel) is the next piece — this de-risks the extraction
skeleton on the one-kernel case. -/

/-- `persistPP_productive` strengthened: the chosen `PP`-successor also
    CARRIES the argument `G` (the fact `persistPP_productive` discarded). -/
theorem persistPP_productive' (hI : RCC5Interp I) {C0 G : Concept}
    (x : α) (hx : persistPP I C0 G x) :
    ∃ y, persistPP I C0 G y ∧ I.dom y ∧ I.rho x y = pp ∧ G ∈ mty C0 I y := by
  obtain ⟨hdx, hex, hall⟩ := hx
  obtain ⟨y, hdy, hr, hGy⟩ := mty_ex hex
  refine ⟨y, ⟨hdy, mty_all hall hdy hr, ?_⟩, hdy, hr, hGy⟩
  obtain ⟨hcl, hsat⟩ := mem_mty.mp hall
  exact mem_mty.mpr ⟨hcl, sat_all_pp_up hI hdx hdy hr hsat⟩

/-- A persistent-`∃PP` chain that CARRIES `G` at every rung (invariant
    `persistPP ∧ G ∈ mty`), started from a `G`-carrying persistent
    element. -/
theorem persistPP_chain' (hI : RCC5Interp I) {C0 G : Concept} (x1 : α)
    (hS1 : persistPP I C0 G x1 ∧ G ∈ mty C0 I x1) :
    ∃ d : Nat → α, d 0 = x1 ∧ (∀ n, I.dom (d n)) ∧
      (∀ n, I.rho (d n) (d (n + 1)) = pp) ∧ (∀ n, G ∈ mty C0 I (d n)) := by
  have hprod : ∀ x, (persistPP I C0 G x ∧ G ∈ mty C0 I x) →
      ∃ y, (persistPP I C0 G y ∧ G ∈ mty C0 I y) ∧ I.dom y ∧ I.rho x y = pp := by
    intro x hx
    obtain ⟨y, hpy, hdy, hry, hGy⟩ := persistPP_productive' hI x hx.1
    exact ⟨y, ⟨hpy, hGy⟩, hdy, hry⟩
  refine ⟨buildChain _ hprod x1 hS1, buildChain_zero _ hprod x1 hS1, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨⟨hdn, _, _⟩, _⟩ := buildChain_prop _ hprod x1 hS1 n
    exact hdn
  · exact fun n => buildChain_step _ hprod x1 hS1 n
  · intro n
    obtain ⟨_, hGn⟩ := buildChain_prop _ hprod x1 hS1 n
    exact hGn

/-- **G-CARRYING KERNEL for the vertical routing** — from a `persistPP G e` node,
    the ascending kernel whose phases carry `G` ITSELF (not just `∃PP.G`) and to
    which `e` is `PP`-below.  The base is `e`'s G-carrying `PP`-witness `y`
    (`persistPP_productive'`); `persistPP_chain'` carries `G` at every point,
    `mty_segment_bounded` gives the period, and `e PP c(i+a)` follows from
    `e PP y PP c(i+a)` via `comp(PP,PP)={PP}`.  This is exactly the data
    `extract_dr_children`'s he_ex vertical disjunct + `hv0pp` consume: `v0 = e`,
    `ck = c`, `phase 0 ∋ G`, `rho e (c(i+a)) = pp`. -/
theorem ascKernelG (hI : RCC5Interp I) {C0 G : Concept} (e : α)
    (h : persistPP I C0 G e) (L : Nat) :
    ∃ (c : Nat → α) (i p : Nat),
      (∀ n, I.dom (c n)) ∧ (∀ n, I.rho (c n) (c (n + 1)) = pp) ∧
      L ≤ i ∧ 0 < p ∧ mty C0 I (c i) = mty C0 I (c (i + p)) ∧
      (∀ n, G ∈ mty C0 I (c n)) ∧
      (0 < i → ∀ a, I.rho e (c (i + a)) = pp) := by
  obtain ⟨y, hpy, hdy, hey, hGy⟩ := persistPP_productive' hI e h
  obtain ⟨c, hc0, hdom, hstep, hG⟩ := persistPP_chain' hI y ⟨hpy, hGy⟩
  obtain ⟨i, p, hLi, hp, _, hty⟩ := mty_segment_bounded C0 c L
  refine ⟨c, i, p, hdom, hstep, hLi, hp, hty, hG, ?_⟩
  intro hi a
  have hyc : I.rho y (c (i + a)) = pp := by
    rw [← hc0, show i + a = (i + a - 1) + 1 from by omega]
    exact pp_chain_below hI c hdom hstep (i + a - 1)
  have hcomp := hI.comp_ e y (c (i + a)) h.1 hdy (hdom (i + a))
  rw [hey, hyc, show comp pp pp = [pp] from rfl, List.mem_singleton] at hcomp
  exact hcomp

/-- **BUNDLED G-carrying kernel data** — `ascKernelG`'s output as a `Type`-level
    structure, so the κ-construction can read the chain/period as DATA per site.
    Mirrors `AscKernelPack` but on `ascKernelG` (phases carry `G`; `base` is the
    `e PP` phase fact). -/
structure AscKernelPackG {α : Type} (I : Interp α) (C0 G : Concept) (e : α) (L : Nat) where
  c : Nat → α
  i : Nat
  p : Nat
  dom : ∀ n, I.dom (c n)
  step : ∀ n, I.rho (c n) (c (n + 1)) = pp
  iLE : L ≤ i
  pPos : 0 < p
  period : mty C0 I (c i) = mty C0 I (c (i + p))
  dem : ∀ n, G ∈ mty C0 I (c n)
  base : 0 < i → ∀ a, I.rho e (c (i + a)) = pp

/-- Extract the bundled G-carrying kernel data from a `persistPP` node. -/
noncomputable def ascKernelPackG (hI : RCC5Interp I) {C0 G : Concept} (e : α)
    (h : persistPP I C0 G e) (L : Nat) : AscKernelPackG I C0 G e L :=
  Classical.choice (by
    obtain ⟨c, i, p, hdom, hstep, hiLE, hpPos, hperiod, hdem, hbase⟩ := ascKernelG hI e h L
    exact ⟨⟨c, i, p, hdom, hstep, hiLE, hpPos, hperiod, hdem, hbase⟩⟩)

/-! ### The SAME-BUDGET PP-chain propagation (§34 building block 1 core)

The finite-PP-tower certificate (§33/§34) must keep all chain nodes at the SAME
budget `b` — a decreasing-budget tower re-hits the `∀PP`-across-transitive-edges
budget failure that forced kernels. At a fixed budget the `∀`-propagation along
the chain order is clean: `∀PP.E` climbs (`comp(PP,PP)={PP}`), `∀PPI.E` descends,
both via `mty_all` + the fixed-budget bound `mdepth E ≤ b−1 ≤ b`. These are the
`ee_all` core of the poset/chain `MultiTierOk`; `posetNet_frame` gives the frame. -/

/-- `∀PP.E` at a lower chain node propagates to every HIGHER one (same budget). -/
theorem chain_ee_up {C0 : Concept} (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) (b : Nat)
    (hpp : ∀ i j, i < j → I.rho (c i) (c j) = pp)
    {i j : Nat} (hij : i < j) {E : Concept}
    (hall : Concept.all pp E ∈ mtk C0 I (c i) b) :
    E ∈ mtk C0 I (c j) b := by
  have hE : E ∈ mty C0 I (c j) := mty_all (mem_mtk.mp hall).1 (hdom j) (hpp i j hij)
  refine mem_mtk.mpr ⟨hE, ?_⟩
  have hmd : mdepth E + 1 ≤ b := (mem_mtk.mp hall).2
  omega

/-- `∀PPI.E` at a higher chain node propagates to every LOWER one (same budget). -/
theorem chain_ee_down (hI : RCC5Interp I) {C0 : Concept} (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) (b : Nat)
    (hpp : ∀ i j, i < j → I.rho (c i) (c j) = pp)
    {i j : Nat} (hij : j < i) {E : Concept}
    (hall : Concept.all ppi E ∈ mtk C0 I (c i) b) :
    E ∈ mtk C0 I (c j) b := by
  have hrho : I.rho (c i) (c j) = ppi := by
    rw [hI.conv_ (c j) (c i) (hdom j) (hdom i), hpp j i hij]; rfl
  have hE : E ∈ mty C0 I (c j) := mty_all (mem_mtk.mp hall).1 (hdom j) hrho
  refine mem_mtk.mpr ⟨hE, ?_⟩
  have hmd : mdepth E + 1 ≤ b := (mem_mtk.mp hall).2
  omega

/-- **FIXED-BUDGET `∀`-PROPAGATION** (§34 block 1, the poset core): `∀r.E` at `x`
    propagates to any `r`-neighbour `y` at the SAME budget — `mty_all` + the bound
    `mdepth E ≤ b−1 ≤ b`.  General over the relation `r`; subsumes
    `chain_ee_up`/`chain_ee_down` (the `PP`/`PPI` chain cases) and is the `ee_all`
    core of a general POSET-of-nodes certificate. -/
theorem mtk_all_same {C0 : Concept} {x y : α} {r : Atom} {E : Concept} {b : Nat}
    (hall : Concept.all r E ∈ mtk C0 I x b) (hy : I.dom y) (hr : I.rho x y = r) :
    E ∈ mtk C0 I y b := by
  refine mem_mtk.mpr ⟨mty_all (mem_mtk.mp hall).1 hy hr, ?_⟩
  have hmd : mdepth E + 1 ≤ b := (mem_mtk.mp hall).2
  omega

/-- THE SINGLE-`∃PP` GENERATOR: a persistent `∃PP.G` element whose model
    types carry only the demands `∃PP.G`/`∃EQ` yields a finite
    certificate carrying `C₀` — extraction for the one-kernel vertical
    fragment. -/
theorem satisfiable_of_persistPP (hI : RCC5Interp I) (C0 G : Concept)
    (hdem : ∀ r D, Concept.ex r D ∈ cl C0 → (r = pp ∧ D = G) ∨ r = eq)
    {x0 : α} (hx0 : persistPP I C0 G x0) (hC0 : C0 ∈ mty C0 I x0) :
    Satisfiable C0 := by
  obtain ⟨x1, hp1, _, hr01, hG1⟩ := persistPP_productive' hI x0 hx0
  obtain ⟨d, hd0, hdom_d, hstep_d, hG_d⟩ := persistPP_chain' hI x1 ⟨hp1, hG1⟩
  obtain ⟨i, p, _, hp, hty, _, _⟩ := segment_select hI hdom_d hstep_d C0 [x0]
    (by intro e he; rw [List.mem_singleton.mp he]; exact hx0.1) 0
  have hx0d0 : I.rho x0 (d 0) = pp := by rw [hd0]; exact hr01
  have hx0pp : ∀ a, I.rho x0 (d (i + a)) = pp := by
    intro a
    rcases Nat.eq_zero_or_pos (i + a) with h0 | h0
    · rw [h0]; exact hx0d0
    · have hcomp := hI.comp_ x0 (d 0) (d (i + a)) hx0.1 (hdom_d 0) (hdom_d (i + a))
      rw [hx0d0, chain_model_pp hI hdom_d hstep_d 0 (i + a) h0,
        show comp pp pp = [pp] from rfl] at hcomp
      exact List.mem_singleton.mp hcomp
  have hok : MultiTierOk (vkernel1 I C0 d x0 i p) :=
    vkernel1_ok hI C0 G d x0 hx0.1 hdom_d hstep_d hp hty (hG_d i) hx0pp
      (fun a r D hmem => hdem r D (mty_sub _ hmem))
      (fun r D hmem => hdem r D (mty_sub _ hmem))
  exact multiTier_sound (vkernel1 I C0 d x0 i p) hok (Sum.inl ()) C0 hC0

/-- From a persistent `∃PP` demand, a BOUNDED-period single-tower
    certificate: `mty_segment_bounded` supplies `(i, p)` with `p ≤ B`, and
    `vkernel1_ok` needs only that recurrence.  Returns the chain + valid
    kernel carrying `C0` at its external. -/
theorem vkernel1_bounded_ok (hI : RCC5Interp I) (C0 G : Concept)
    (hdem : ∀ r D, Concept.ex r D ∈ cl C0 → (r = pp ∧ D = G) ∨ r = eq)
    {x0 : α} (hx0 : persistPP I C0 G x0) (hC0 : C0 ∈ mty C0 I x0) :
    ∃ (c : Nat → α) (i p : Nat),
      p ≤ (allListsLe (cl C0) (cl C0).length).length ∧ 0 < p ∧
      MultiTierOk (vkernel1 I C0 c x0 i p) ∧
      C0 ∈ (vkernel1 I C0 c x0 i p).tauE () := by
  obtain ⟨x1, hp1, _, hr01, hG1⟩ := persistPP_productive' hI x0 hx0
  obtain ⟨d, hd0, hdom_d, hstep_d, hG_d⟩ := persistPP_chain' hI x1 ⟨hp1, hG1⟩
  obtain ⟨i, p, _, hp, hpB, hty⟩ := mty_segment_bounded (I := I) C0 d 0
  have hx0d0 : I.rho x0 (d 0) = pp := by rw [hd0]; exact hr01
  have hx0pp : ∀ a, I.rho x0 (d (i + a)) = pp := by
    intro a
    rcases Nat.eq_zero_or_pos (i + a) with h0 | h0
    · rw [h0]; exact hx0d0
    · have hcomp := hI.comp_ x0 (d 0) (d (i + a)) hx0.1 (hdom_d 0) (hdom_d (i + a))
      rw [hx0d0, chain_model_pp hI hdom_d hstep_d 0 (i + a) h0,
        show comp pp pp = [pp] from rfl] at hcomp
      exact List.mem_singleton.mp hcomp
  have hok := vkernel1_ok hI C0 G d x0 hx0.1 hdom_d hstep_d hp hty (hG_d i) hx0pp
    (fun a r D hmem => hdem r D (mty_sub _ hmem))
    (fun r D hmem => hdem r D (mty_sub _ hmem))
  exact ⟨d, i, p, hpB, hp, hok, hC0⟩

/-- SELF-CARRYING bounded extraction: a persistent `∃PP.G0` chain generator
    `hx0` PLUS co-carrying `hcarry` (every `∃PP`-demand-arg `D` satisfies
    `∀PP.D` at `x0`, so every chain point carries it) yields a
    bounded-period `vkernel1` valid by `vkernel1G_ok`.  `hdem` only needs
    every existential to be `∃PP`/`∃EQ` (the pure-vertical fragment) — the
    single fixed `G` of `vkernel1_bounded_ok` is gone. -/
theorem vkernel1G_bounded_ok (hI : RCC5Interp I) (C0 G0 : Concept)
    {x0 : α}
    (hdem : ∀ r D, Concept.ex r D ∈ cl C0 → r = pp ∨ r = eq)
    (hcarry : ∀ D, Concept.ex pp D ∈ cl C0 → sat I x0 (Concept.all pp D))
    (hx0 : persistPP I C0 G0 x0) (hC0 : C0 ∈ mty C0 I x0) :
    ∃ (c : Nat → α) (i p : Nat),
      p ≤ (allListsLe (cl C0) (cl C0).length).length ∧ 0 < p ∧
      MultiTierOk (vkernel1 I C0 c x0 i p) ∧
      C0 ∈ (vkernel1 I C0 c x0 i p).tauE () := by
  obtain ⟨x1, hp1, _, hr01, hG1⟩ := persistPP_productive' hI x0 hx0
  obtain ⟨d, hd0, hdom_d, hstep_d, hG_d⟩ := persistPP_chain' hI x1 ⟨hp1, hG1⟩
  obtain ⟨i, p, _, hp, hpB, hty⟩ := mty_segment_bounded (I := I) C0 d 0
  have hx0d0 : I.rho x0 (d 0) = pp := by rw [hd0]; exact hr01
  have hx0pp : ∀ a, I.rho x0 (d (i + a)) = pp := by
    intro a
    rcases Nat.eq_zero_or_pos (i + a) with h0 | h0
    · rw [h0]; exact hx0d0
    · have hcomp := hI.comp_ x0 (d 0) (d (i + a)) hx0.1 (hdom_d 0) (hdom_d (i + a))
      rw [hx0d0, chain_model_pp hI hdom_d hstep_d 0 (i + a) h0,
        show comp pp pp = [pp] from rfl] at hcomp
      exact List.mem_singleton.mp hcomp
  -- co-carrying: every PP-demand-arg is carried at chain base `d i`
  have hcarry_d : ∀ D, Concept.ex pp D ∈ cl C0 → D ∈ mty C0 I (d (i + 0)) := by
    intro D hD
    exact mem_mty.mpr ⟨cl_ex hD, hcarry D hD (d (i + 0)) (hdom_d (i + 0)) (hx0pp 0)⟩
  have hdemands : ∀ a r D, Concept.ex r D ∈ mty C0 I (d (i + a)) →
      (r = pp ∧ ∃ b, b < p ∧ D ∈ mty C0 I (d (i + b))) ∨ r = eq := by
    intro a r D hmem
    have hcl : Concept.ex r D ∈ cl C0 := mty_sub _ hmem
    rcases hdem r D hcl with rfl | rfl
    · exact Or.inl ⟨rfl, 0, hp, hcarry_d D hcl⟩
    · exact Or.inr rfl
  have hx0dem : ∀ r D, Concept.ex r D ∈ mty C0 I x0 →
      (r = pp ∧ ∃ b, b < p ∧ D ∈ mty C0 I (d (i + b))) ∨ r = eq := by
    intro r D hmem
    have hcl : Concept.ex r D ∈ cl C0 := mty_sub _ hmem
    rcases hdem r D hcl with rfl | rfl
    · exact Or.inl ⟨rfl, 0, hp, hcarry_d D hcl⟩
    · exact Or.inr rfl
  have hok := vkernel1G_ok hI C0 d x0 hx0.1 hdom_d hstep_d hp hty hx0pp
    hdemands hx0dem
  exact ⟨d, i, p, hpB, hp, hok, hC0⟩

/-! ### Round E3k (2026-07-30): the STAR frame — root below many kernels

The multi-demand geometry: the witnesses of distinct `∃PP.Gₖ` demands at
one root are pairwise `PO`/`PP`/`PPI`/`EQ` (composition forbids `DR`
there), so the natural multi-kernel certificate is a STAR — the root
`PPI`-below every kernel base (so `x₀ PP` every tower), kernels cross-`PO`
(loose, `∀PO`-free ⟹ `kq_all` vacuous).  `starNet` declares exactly this
(`= qnet (fun _ _ => eq) (fun _ _ => ppi) (fun _ _ => po)`); its RCC5
validity is the keystone the multi-demand construction rests on. -/

/-- The star network on `Unit ⊕ N`: the `Unit` root is `PPI`-below every
    kernel point (`ppi` from point to root, `pp` from root to point);
    distinct kernel points are cross-`PO`. -/
def starNet {N : Type} [DecidableEq N] : (Unit ⊕ N) → (Unit ⊕ N) → Atom
  | .inl _, .inl _ => eq
  | .inl _, .inr _ => pp
  | .inr _, .inl _ => ppi
  | .inr k, .inr k' => if k = k' then eq else po

variable {N : Type} [DecidableEq N]

theorem starNet_ll : starNet (Sum.inl () : Unit ⊕ N) (Sum.inl ()) = eq := rfl
theorem starNet_lr (k : N) : starNet (Sum.inl ()) (Sum.inr k) = pp := rfl
theorem starNet_rl (k : N) : starNet (Sum.inr k) (Sum.inl ()) = ppi := rfl
theorem starNet_diag (k : N) : starNet (Sum.inr k) (Sum.inr k) = eq := if_pos rfl
theorem starNet_off {k k' : N} (h : k ≠ k') :
    starNet (Sum.inr k) (Sum.inr k') = po := if_neg h

/-- THE STAR FRAME: `starNet` is a genuine RCC5 frame.  The keystone of
    the multi-demand certificate.  Every case reduces each `starNet`
    entry (via the `rfl`-helpers, resolving the kernel-diagonal `if`) to
    a concrete atom, then `decide`s the composition membership. -/
theorem starNet_frame : Frame (@starNet N _) where
  refl_eq := by
    rintro (⟨⟩ | k)
    · rfl
    · exact starNet_diag k
  eq_id := by
    rintro (⟨⟩ | k) (⟨⟩ | k') h
    · rfl
    · rw [starNet_lr] at h; exact absurd h (by decide)
    · rw [starNet_rl] at h; exact absurd h (by decide)
    · by_cases hk : k = k'
      · rw [hk]
      · rw [starNet_off hk] at h; exact absurd h (by decide)
  conv_ := by
    rintro (⟨⟩ | k) (⟨⟩ | k')
    · rfl
    · rw [starNet_rl, starNet_lr]; rfl
    · rw [starNet_lr, starNet_rl]; rfl
    · by_cases hk : k = k'
      · subst hk; rw [starNet_diag]; rfl
      · rw [starNet_off hk, starNet_off (fun h => hk h.symm)]; rfl
  comp_ := by
    rintro (⟨⟩ | k) (⟨⟩ | k') (⟨⟩ | k'')
    · rw [starNet_ll]; decide
    · rw [starNet_ll, starNet_lr]; decide
    · rw [starNet_lr, starNet_rl, starNet_ll]; decide
    · rw [starNet_lr, starNet_lr]
      by_cases hk : k' = k''
      · subst hk; rw [starNet_diag]; decide
      · rw [starNet_off hk]; decide
    · rw [starNet_rl, starNet_ll]; decide
    · rw [starNet_rl, starNet_lr]
      by_cases hk : k = k''
      · subst hk; rw [starNet_diag]; decide
      · rw [starNet_off hk]; decide
    · rw [starNet_rl, starNet_rl]
      by_cases hk : k = k'
      · subst hk; rw [starNet_diag]; decide
      · rw [starNet_off hk]; decide
    · by_cases hkk' : k = k' <;> by_cases hk'k'' : k' = k''
      · subst hkk'; subst hk'k''; rw [starNet_diag]; decide
      · subst hkk'; rw [starNet_diag, starNet_off hk'k'']; decide
      · subst hk'k''; rw [starNet_diag, starNet_off hkk']; decide
      · by_cases hkk'' : k = k''
        · subst hkk''; rw [starNet_diag, starNet_off hkk', starNet_off hk'k'']; decide
        · rw [starNet_off hkk'', starNet_off hkk', starNet_off hk'k'']; decide

/-! ### Round E3o (2026-07-31): the POSET frame — the general vertical frame

Research finding (ASSEMBLY_DESIGN §21): the vertical structure of a
∀PO-free concept is a FINITE POSET of kernels (one per recurrent type),
root below all, `PP` up the nesting order, `PO` for incomparable types,
NO `DR`.  `posetNet` declares exactly this for any strict partial order
`lt` on the kernel index; `posetNet_frame` proves it a genuine RCC5 frame
via the CERTIFIED `ordered_disjoint_frame` (whose `DR`-downward-closure
hypothesis is vacuous here — the frame has no `DR`).  `starNet` is the
special case `lt = ∅` (all `PO`); this is the general keystone. -/

/-- The poset frame on `Unit ⊕ N`: root `PP`-below every kernel; kernels
    ordered by `lt` (`PP`/`PPI`), incomparable kernels cross-`PO`. -/
def posetNet {N : Type} [DecidableEq N] (lt : N → N → Prop) [DecidableRel lt] :
    (Unit ⊕ N) → (Unit ⊕ N) → Atom
  | .inl _, .inl _ => eq
  | .inl _, .inr _ => pp
  | .inr _, .inl _ => ppi
  | .inr k, .inr k' =>
      if k = k' then eq else if lt k k' then pp else if lt k' k then ppi else po

section PosetFrame
variable {N : Type} [DecidableEq N] (lt : N → N → Prop) [DecidableRel lt]

theorem posetNet_ll : posetNet lt (Sum.inl ()) (Sum.inl ()) = eq := rfl
theorem posetNet_lr (k : N) : posetNet lt (Sum.inl ()) (Sum.inr k) = pp := rfl
theorem posetNet_rl (k : N) : posetNet lt (Sum.inr k) (Sum.inl ()) = ppi := rfl
theorem posetNet_rr (k k' : N) :
    posetNet lt (Sum.inr k) (Sum.inr k')
      = if k = k' then eq else if lt k k' then pp else if lt k' k then ppi else po :=
  rfl

/-- The kernel–kernel value is one of `eq/pp/ppi/po`: extract which. -/
theorem posetNet_rr_cases (k k' : N) :
    posetNet lt (Sum.inr k) (Sum.inr k') = eq ∧ k = k'
    ∨ posetNet lt (Sum.inr k) (Sum.inr k') = pp ∧ lt k k'
    ∨ posetNet lt (Sum.inr k) (Sum.inr k') = ppi ∧ lt k' k
    ∨ posetNet lt (Sum.inr k) (Sum.inr k') = po := by
  rw [posetNet_rr]
  by_cases hk : k = k'
  · rw [if_pos hk]; exact Or.inl ⟨rfl, hk⟩
  · rw [if_neg hk]
    by_cases h1 : lt k k'
    · rw [if_pos h1]; exact Or.inr (Or.inl ⟨rfl, h1⟩)
    · rw [if_neg h1]
      by_cases h2 : lt k' k
      · rw [if_pos h2]; exact Or.inr (Or.inr (Or.inl ⟨rfl, h2⟩))
      · rw [if_neg h2]; exact Or.inr (Or.inr (Or.inr rfl))

theorem posetNet_ne_dr (x y : Unit ⊕ N) : posetNet lt x y ≠ dr := by
  rcases x with ⟨⟩ | k <;> rcases y with ⟨⟩ | k'
  · rw [posetNet_ll]; decide
  · rw [posetNet_lr]; decide
  · rw [posetNet_rl]; decide
  · rcases posetNet_rr_cases lt k k' with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | h <;>
      rw [h] <;> decide

/-- THE POSET FRAME: for any strict partial order `lt`, `posetNet lt` is
    an RCC5 frame.  Generalises `starNet_frame` (`lt = ∅`). -/
theorem posetNet_frame (hirr : ∀ k, ¬ lt k k)
    (htr : ∀ a b c, lt a b → lt b c → lt a c) : Frame (posetNet lt) := by
  have hasym : ∀ a b, lt a b → ¬ lt b a := fun a b hab hba => hirr a (htr a b a hab hba)
  -- kernel–kernel value lemmas (robust against `if`-ordering)
  have hppv : ∀ k k', lt k k' → posetNet lt (Sum.inr k) (Sum.inr k') = pp := by
    intro k k' h
    have hne : k ≠ k' := by rintro rfl; exact hirr k h
    rw [posetNet_rr, if_neg hne, if_pos h]
  have hppiv : ∀ k k', lt k' k → posetNet lt (Sum.inr k) (Sum.inr k') = ppi := by
    intro k k' h
    have hne : k ≠ k' := by rintro rfl; exact hirr k h
    rw [posetNet_rr, if_neg hne, if_neg (hasym k' k h), if_pos h]
  have hpov : ∀ k k', k ≠ k' → ¬ lt k k' → ¬ lt k' k →
      posetNet lt (Sum.inr k) (Sum.inr k') = po := by
    intro k k' hne h1 h2; rw [posetNet_rr, if_neg hne, if_neg h1, if_neg h2]
  have hkpp : ∀ k k', posetNet lt (Sum.inr k) (Sum.inr k') = pp → lt k k' := by
    intro k k' h
    rcases posetNet_rr_cases lt k k' with ⟨h', _⟩ | ⟨_, h1⟩ | ⟨h', _⟩ | h' <;>
      first | exact h1 | (rw [h'] at h; exact absurd h (by decide))
  -- strengthened case split (`po` carries the `¬lt` facts)
  have hval : ∀ k k',
      posetNet lt (Sum.inr k) (Sum.inr k') = eq ∧ k = k'
      ∨ posetNet lt (Sum.inr k) (Sum.inr k') = pp ∧ lt k k'
      ∨ posetNet lt (Sum.inr k) (Sum.inr k') = ppi ∧ lt k' k
      ∨ posetNet lt (Sum.inr k) (Sum.inr k') = po ∧ k ≠ k' ∧ ¬ lt k k' ∧ ¬ lt k' k := by
    intro k k'
    by_cases hk : k = k'
    · exact Or.inl ⟨by rw [posetNet_rr, if_pos hk], hk⟩
    · by_cases h1 : lt k k'
      · exact Or.inr (Or.inl ⟨hppv k k' h1, h1⟩)
      · by_cases h2 : lt k' k
        · exact Or.inr (Or.inr (Or.inl ⟨hppiv k k' h2, h2⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hpov k k' hk h1 h2, hk, h1, h2⟩))
  refine ordered_disjoint_frame _ ?_ ?_ ?_ ?_ ?_
  · rintro (⟨⟩ | k)
    · rfl
    · rw [posetNet_rr, if_pos rfl]
  · rintro (⟨⟩ | k) (⟨⟩ | k') h
    · rfl
    · rw [posetNet_lr] at h; exact absurd h (by decide)
    · rw [posetNet_rl] at h; exact absurd h (by decide)
    · rcases hval k k' with ⟨_, hkk⟩ | ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ <;>
        first
          | exact congrArg Sum.inr hkk
          | (rw [h'] at h; exact absurd h (by decide))
  · rintro (⟨⟩ | k) (⟨⟩ | k')
    · rfl
    · rw [posetNet_rl, posetNet_lr]; rfl
    · rw [posetNet_lr, posetNet_rl]; rfl
    · rcases hval k k' with ⟨h, hkk⟩ | ⟨h, h1⟩ | ⟨h, h1⟩ | ⟨h, hne, hn1, hn2⟩
      · subst hkk; rw [h]; rfl
      · rw [h, hppiv k' k h1]; rfl
      · rw [h, hppv k' k h1]; rfl
      · rw [h, hpov k' k (fun e => hne e.symm) hn2 hn1]; rfl
  · rintro (⟨⟩ | kx) (⟨⟩ | ky) (⟨⟩ | kz) hxy hyz
    · rw [posetNet_ll] at hxy; exact absurd hxy (by decide)
    · rw [posetNet_ll] at hxy; exact absurd hxy (by decide)
    · rw [posetNet_rl] at hyz; exact absurd hyz (by decide)
    · rfl
    · rw [posetNet_rl] at hxy; exact absurd hxy (by decide)
    · rw [posetNet_rl] at hxy; exact absurd hxy (by decide)
    · rw [posetNet_rl] at hyz; exact absurd hyz (by decide)
    · exact hppv kx kz (htr kx ky kz (hkpp kx ky hxy) (hkpp ky kz hyz))
  · intro x y z _ h2
    exact absurd h2 (posetNet_ne_dr lt y z)

end PosetFrame

/-- **THE FINITE-CHAIN FRAME** (§34 block 1): the ordered-disjoint read-off of the
    strict LINEAR order `<` on `Fin L` is an RCC5 Frame — a `base (Unit)` `PP`-below
    a linear chain of `L` nodes.  Just `posetNet_frame` at the total order `<`
    (`Nat.lt_irrefl` + `Nat.lt_trans`); no bespoke composition proof.  This is the
    frame the same-budget finite-PP-tower `MultiTierOk` uses (with `chain_ee_up`/
    `chain_ee_down` for `ee_all`). -/
theorem linChain_frame (L : Nat) :
    Frame (posetNet (fun i j : Fin L => i.val < j.val)) :=
  posetNet_frame _ (fun k => Nat.lt_irrefl k.val)
    (fun _ _ _ hab hbc => Nat.lt_trans hab hbc)

/-- **THE GENERAL FINITE-POSET-OF-NODES MultiTier** (§34 block 1, general): a base
    `PP`-below a finite POSET of same-budget nodes (`E = posetNet lt`, comparable
    ⟹ `PP`/`PPI`, incomparable ⟹ `PO`), `κ` empty.  Generalises `chainMT` (linear
    order) to a BRANCHING vertical structure — the actual shape of the vertical
    skeleton in the ordered-disjoint certificate. -/
noncomputable def posetMT (I : Interp α) (C0 : Concept) {N : Type} [DecidableEq N]
    (lt : N → N → Prop) [DecidableRel lt] (x0 : α) (g : N → α) (b : Nat) :
    MultiTier (Unit ⊕ N) Empty where
  E := posetNet lt
  K := fun e => e.elim
  Q := fun e => e.elim
  up := fun e => e.elim
  tauE := fun e => mtk C0 I (Sum.elim (fun _ => x0) g e) b
  p := fun e => e.elim
  phase := fun e => e.elim

/-- **THE GENERAL POSET CERTIFICATE IS VALID.**  `ee_all` = the fixed-budget
    order-propagation (`mtk_all_same` on `posetNet`'s value lemmas: base↔node via
    `hbelow`, node↔node via `hpp` + converse; the incomparable `PO` case
    discharged by `∀PO`-freeness); `e_ex` = the supplied `hdem`; `κ`-clauses
    vacuous.  Subsumes `chainMT_ok`; handles branching (`∃PP` to incomparable
    superparts). -/
theorem posetMT_ok (hI : RCC5Interp I) {C0 : Concept} (hpofree : POFree C0)
    {N : Type} [DecidableEq N] (lt : N → N → Prop) [DecidableRel lt]
    (hirr : ∀ k, ¬ lt k k) (htr : ∀ a b c, lt a b → lt b c → lt a c)
    (x0 : α) (hx0dom : I.dom x0) (g : N → α) (hgdom : ∀ k, I.dom (g k)) (b : Nat)
    (hbelow : ∀ k, I.rho x0 (g k) = pp)
    (hpp : ∀ k k', lt k k' → I.rho (g k) (g k') = pp)
    (hdem : ∀ e r D, Concept.ex r D ∈ (posetMT I C0 lt x0 g b).tauE e →
      ∃ f, posetNet lt e f = r ∧ D ∈ (posetMT I C0 lt x0 g b).tauE f) :
    MultiTierOk (posetMT I C0 lt x0 g b) := by
  refine
    { hp := fun e => e.elim
      frame_q := qnet_empty_frame' _ _ _ (fun e => e.elim) (posetNet_frame lt hirr htr)
      e_clash := fun _ a h => mtk_clash h
      e_nobot := fun _ => mtk_nobot
      e_and := fun _ x y h => mtk_and h
      e_or := fun _ x y h => mtk_or h
      k_clash := fun k => k.elim
      k_nobot := fun k => k.elim
      k_and := fun k => k.elim
      k_or := fun k => k.elim
      ee_all := ?_
      ek_all := fun _ _ _ _ k => k.elim
      ke_all := fun k => k.elim
      kk_pp := fun k => k.elim
      kk_ppi := fun k => k.elim
      kk_eq := fun k => k.elim
      kq_all := fun k => k.elim
      e_ex := fun e r D hmem => Or.inl (hdem e r D hmem)
      k_ex := fun k => k.elim }
  intro e f r c' hmem hEf
  rcases e with ⟨⟩ | k <;> rcases f with ⟨⟩ | k' <;>
    simp only [posetMT, Sum.elim_inl, Sum.elim_inr] at hmem hEf ⊢
  · rw [posetNet_ll] at hEf; subst hEf
    exact mtk_all_same hmem hx0dom (hI.refl_eq x0 hx0dom)
  · rw [posetNet_lr] at hEf; subst hEf
    exact mtk_all_same hmem (hgdom k') (hbelow k')
  · rw [posetNet_rl] at hEf; subst hEf
    exact mtk_all_same hmem hx0dom
      (by rw [hI.conv_ x0 (g k) hx0dom (hgdom k), hbelow k]; rfl)
  · rcases posetNet_rr_cases lt k k' with ⟨hv, hkk⟩ | ⟨hv, hkk⟩ | ⟨hv, hkk⟩ | hv
    · rw [hv] at hEf; subst hEf; subst hkk
      exact mtk_all_same hmem (hgdom k) (hI.refl_eq (g k) (hgdom k))
    · rw [hv] at hEf; subst hEf
      exact mtk_all_same hmem (hgdom k') (hpp k k' hkk)
    · rw [hv] at hEf; subst hEf
      exact mtk_all_same hmem (hgdom k')
        (by rw [hI.conv_ (g k') (g k) (hgdom k') (hgdom k), hpp k' k hkk]; rfl)
    · rw [hv] at hEf; subst hEf
      exact absurd rfl (pofree_cl_all C0 hpofree po c' (mtk_sub_cl _ hmem))

/-- The chain position of a node: base `= 0`, poset node `i = i+1`. -/
def cidx (L : Nat) : Unit ⊕ Fin L → Nat := Sum.elim (fun _ => 0) (fun i => i.val + 1)

/-- **THE FINITE-CHAIN MultiTier** (§34 block 1): the base `PP`-below a linear
    chain of `L` same-budget nodes; `κ` empty (no cycles — this is the ONE-SHOT
    tower). `E = posetNet (<)`, `tauE` = each node's `mtk`-label at the FIXED
    budget `b`. -/
noncomputable def chainMT (I : Interp α) (C0 : Concept) (c : Nat → α) (L b : Nat) :
    MultiTier (Unit ⊕ Fin L) Empty where
  E := posetNet (fun i j : Fin L => i.val < j.val)
  K := fun e => e.elim
  Q := fun e => e.elim
  up := fun e => e.elim
  tauE := fun e => mtk C0 I (c (cidx L e)) b
  p := fun e => e.elim
  phase := fun e => e.elim

/-- **THE FINITE-CHAIN CERTIFICATE IS VALID.**  `ee_all` = the same-budget PP-order
    propagation (`chain_ee_up`/`chain_ee_down` + `mtk_all_eq`, via `posetNet`'s
    value lemmas; the `po` case is impossible on a linear order); `e_ex` is the
    supplied demand routing (`hdem`); all `κ`-clauses vacuous (`Empty`).  This is
    the finite-PP-tower certificate the one-shot `∃PP` class needs. -/
theorem chainMT_ok (hI : RCC5Interp I) {C0 : Concept} (hpofree : POFree C0)
    (c : Nat → α) (hdom : ∀ n, I.dom (c n)) (L b : Nat)
    (hpp : ∀ i j, i < j → I.rho (c i) (c j) = pp)
    (hdem : ∀ e r D, Concept.ex r D ∈ mtk C0 I (c (cidx L e)) b →
      ∃ f, posetNet (fun i j : Fin L => i.val < j.val) e f = r ∧
        D ∈ mtk C0 I (c (cidx L f)) b) :
    MultiTierOk (chainMT I C0 c L b) := by
  refine
    { hp := fun e => e.elim
      frame_q := qnet_empty_frame' _ _ _ (fun e => e.elim) (linChain_frame L)
      e_clash := fun _ a h => mtk_clash h
      e_nobot := fun _ => mtk_nobot
      e_and := fun _ x y h => mtk_and h
      e_or := fun _ x y h => mtk_or h
      k_clash := fun k => k.elim
      k_nobot := fun k => k.elim
      k_and := fun k => k.elim
      k_or := fun k => k.elim
      ee_all := ?_
      ek_all := fun _ _ _ _ k => k.elim
      ke_all := fun k => k.elim
      kk_pp := fun k => k.elim
      kk_ppi := fun k => k.elim
      kk_eq := fun k => k.elim
      kq_all := fun k => k.elim
      e_ex := fun e r D hmem => Or.inl (hdem e r D hmem)
      k_ex := fun k => k.elim }
  intro e f r c' hmem hEf
  simp only [chainMT] at hmem hEf ⊢
  rcases e with ⟨⟩ | i <;> rcases f with ⟨⟩ | j
  · -- inl, inl: eq, self
    rw [posetNet_ll] at hEf; subst hEf; exact mtk_all_eq hI hmem (hdom _)
  · -- inl (0), inr j (j+1): pp, up
    rw [posetNet_lr] at hEf; subst hEf
    exact chain_ee_up c hdom b hpp (Nat.succ_pos j.val) hmem
  · -- inr i (i+1), inl (0): ppi, down
    rw [posetNet_rl] at hEf; subst hEf
    exact chain_ee_down hI c hdom b hpp (Nat.succ_pos i.val) hmem
  · -- inr i, inr j
    rcases posetNet_rr_cases (fun i j : Fin L => i.val < j.val) i j with
      ⟨hv, hij⟩ | ⟨hv, hij⟩ | ⟨hv, hij⟩ | hv
    · rw [hv] at hEf; subst hEf; subst hij; exact mtk_all_eq hI hmem (hdom _)
    · rw [hv] at hEf; subst hEf
      have hij2 : i.val < j.val := hij
      exact chain_ee_up c hdom b hpp (by simp only [cidx, Sum.elim_inr]; omega) hmem
    · rw [hv] at hEf; subst hEf
      have hij2 : j.val < i.val := hij
      exact chain_ee_down hI c hdom b hpp (by simp only [cidx, Sum.elim_inr]; omega) hmem
    · rw [hv] at hEf; subst hEf
      exact absurd rfl (pofree_cl_all C0 hpofree po c' (mtk_sub_cl _ hmem))

/-! ### Round E3l (2026-07-30): the multi-demand star certificate

`starKernel` is the `MultiTier` over the star frame: one root external
(carrying `C₀`) `PPI`-below `N` ascending kernels, cross-`PO`.
`starKernel_ok` proves validity: the root routes each `∃PP.(Gₖ k)` into
kernel `k` (`e_ex` disjunct 2), each kernel serves its own `∃PP.(Gₖ k)`
via its chain (`k_ex` disjunct 2), `∃EQ` self/in-phase, `kq_all` vacuous
(cross-`PO`, `∀PO`-free), the root↔kernel `∀`-obligations firing by
`mty_all` through the model's `x₀ PP`-chain rows.  This is the
multi-demand validity — the coverage CLOSES because each kernel's phases
carry only that kernel's demand (`hphase_dem`). -/

/-- The star `MultiTier`: root `Unit` (label `mty x₀`), `N` ascending
    kernels, frame `= starNet`. -/
noncomputable def starKernel (I : Interp α) (C0 : Concept) (x0 : α)
    (ck : N → Nat → α) (ik pk : N → Nat) : MultiTier Unit N where
  E := fun _ _ => eq
  K := fun _ _ => ppi
  Q := fun _ _ => po
  up := fun _ => true
  tauE := fun _ => mty C0 I x0
  p := pk
  phase := fun k a => mty C0 I (ck k (ik k + a))

/-- THE MULTI-DEMAND STAR CERTIFICATE IS VALID: a root `x₀` `PP`-below
    `N` ascending chains (`hbelow`), each type-recurrent (`hty`) and
    serving its own demand `∃PP.(Gₖ k)` (`hphase_dem`, `hchainG`), with
    the root's demands each some `Gₖ k` (`hroot_dem`), gives a full
    `MultiTierOk`. -/
theorem starKernel_ok (hI : RCC5Interp I) (C0 : Concept) (hpo : POFree C0)
    (x0 : α) (hx0dom : I.dom x0) (ck : N → Nat → α) {ik pk : N → Nat}
    (hdomc : ∀ k n, I.dom (ck k n))
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = pp)
    (hp : ∀ k, 0 < pk k)
    (hty : ∀ k, mty C0 I (ck k (ik k)) = mty C0 I (ck k (ik k + pk k)))
    (hbelow : ∀ k a, I.rho x0 (ck k (ik k + a)) = pp)
    (Gk : N → Concept)
    (hchainG : ∀ k, Gk k ∈ mty C0 I (ck k (ik k)))
    (hphase_dem : ∀ k a r D, Concept.ex r D ∈ mty C0 I (ck k (ik k + a)) →
      (r = pp ∧ D = Gk k) ∨ r = eq)
    (hroot_dem : ∀ r D, Concept.ex r D ∈ mty C0 I x0 →
      (r = pp ∧ ∃ k, D = Gk k) ∨ r = eq) :
    MultiTierOk (starKernel I C0 x0 ck ik pk) := by
  have hbc : ∀ k a, I.rho (ck k (ik k + a)) x0 = ppi := by
    intro k a
    rw [hI.conv_ x0 (ck k (ik k + a)) hx0dom (hdomc k _), hbelow k a]; rfl
  refine
    { hp := hp
      frame_q := frame_ext (fun x y => by
        rcases x with ⟨⟩ | k <;> rcases y with ⟨⟩ | k' <;> rfl) starNet_frame
      e_clash := fun _ a h => mty_clash h
      e_nobot := fun _ => mty_nobot
      e_and := fun _ x y h => mty_and h
      e_or := fun _ x y h => mty_or h
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := fun _ _ r c hmem hr =>
        mty_all hmem hx0dom ((hI.refl_eq x0 hx0dom).trans hr)
      ek_all := fun _ r c hmem k hr a _ =>
        mty_all hmem (hdomc k _) ((hbelow k a).trans hr)
      ke_all := fun k a _ r c hmem _ hr =>
        mty_all hmem hx0dom ((hbc k a).trans hr)
      kk_pp := fun k _ ha E hE b hb =>
        segment_kk_pp hI (fun n => hdomc k n) (fun n => hstep k n) (hty k) ha hE b hb
      kk_ppi := fun k _ ha E hE b hb =>
        segment_kk_ppi hI (fun n => hdomc k n) (fun n => hstep k n) (hty k) ha hE b hb
      kk_eq := fun k _ _ E hE => seg_eq hI (fun n => hdomc k n) hE
      kq_all := ?_
      e_ex := ?_
      k_ex := ?_ }
  · -- kq_all: cross-`PO` fires only `∀PO`, vacuous on the fragment
    intro k k' _ a _ r c hmem hr _ _
    have hrpo : r = po := hr.symm
    subst hrpo
    exact absurd hmem (mty_no_all_po hpo)
  · -- e_ex: root routes each `∃PP.(Gₖ k)` into kernel k; `∃EQ` self
    intro _ r c hmem
    rcases hroot_dem r c hmem with ⟨rfl, k, rfl⟩ | rfl
    · exact Or.inr ⟨k, rfl, 0, hp k, hchainG k⟩
    · refine Or.inl ⟨(), rfl, ?_⟩
      obtain ⟨y, hy, hyr, hyc⟩ := mty_ex hmem
      rwa [hI.eq_id x0 y hx0dom hy hyr]
  · -- k_ex: each kernel serves its own `∃PP.(Gₖ k)` via its chain
    intro k a _ r c hmem
    rcases hphase_dem k a r c hmem with ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, 0, hp k, hchainG k⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, seg_ex_eq hI (fun n => hdomc k n) hmem⟩))

/-! ### Round E3p (2026-07-31): the POSET multi-kernel — cross-`PP` fires

`posetKernel` generalises `starKernel` off the discrete (all-`PO`) star to
an ARBITRARY constant-cross poset of kernels: the kernel–kernel value `Q`
is read off the model, and the rectangle-constancy `hrectQ` makes
`kq_all` FIRE across comparable (`PP`/`PPI`) kernels — exactly
`vkernel2`'s mechanism, now with a root and any index `N`.  The root
machinery (`e_ex` routing, `k_ex` serving, `ee`/`ek`/`ke_all`) is
`starKernel`'s; only `kq_all` (now `hrectQ`, not vacuous-`PO`) and the
frame (`readoff` + `frame_ext`, not `starNet`) change.  This is §21.4's
general assembly lemma: no `POFree` needed, the rectangle transports
every cross-`∀` uniformly. -/

/-- The poset `MultiTier`: root `Unit` (label `mty x₀`), `N` kernels with
    cross-values read off the model. -/
noncomputable def posetKernel (I : Interp α) (C0 : Concept) (x0 : α)
    (ck : N → Nat → α) (ik pk : N → Nat) : MultiTier Unit N where
  E := fun _ _ => eq
  K := fun _ _ => ppi
  Q := fun k k' => I.rho (ck k (ik k)) (ck k' (ik k'))
  up := fun _ => true
  tauE := fun _ => mty C0 I x0
  p := pk
  phase := fun k a => mty C0 I (ck k (ik k + a))

/-- THE POSET MULTI-KERNEL IS VALID: a root `x₀` `PP`-below `N` kernels
    (`hbelow`), distinct (`hdist`/`hkinj`), each type-recurrent (`hty`)
    serving its own demand `∃PP.(Gₖ k)` (`hphase_dem`), with all
    cross-rectangles constant (`hrectQ`) so `kq_all` fires across
    comparable kernels.  Generalises `starKernel_ok`. -/
theorem posetKernel_ok (hI : RCC5Interp I) (C0 : Concept)
    (x0 : α) (hx0dom : I.dom x0) (ck : N → Nat → α) {ik pk : N → Nat}
    (hdomc : ∀ k n, I.dom (ck k n))
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = pp)
    (hp : ∀ k, 0 < pk k)
    (hty : ∀ k, mty C0 I (ck k (ik k)) = mty C0 I (ck k (ik k + pk k)))
    (hbelow : ∀ k a, I.rho x0 (ck k (ik k + a)) = pp)
    (hdist : ∀ k, x0 ≠ ck k (ik k))
    (hkinj : ∀ k k', ck k (ik k) = ck k' (ik k') → k = k')
    (hrectQ : ∀ k k', k ≠ k' → ∀ a b,
      I.rho (ck k (ik k + a)) (ck k' (ik k' + b))
        = I.rho (ck k (ik k)) (ck k' (ik k')))
    (Gk : N → Concept)
    (hchainG : ∀ k, Gk k ∈ mty C0 I (ck k (ik k)))
    (hphase_dem : ∀ k a r D, Concept.ex r D ∈ mty C0 I (ck k (ik k + a)) →
      (r = pp ∧ D = Gk k) ∨ r = eq)
    (hroot_dem : ∀ r D, Concept.ex r D ∈ mty C0 I x0 →
      (r = pp ∧ ∃ k, D = Gk k) ∨ r = eq) :
    MultiTierOk (posetKernel I C0 x0 ck ik pk) := by
  have hbc : ∀ k a, I.rho (ck k (ik k + a)) x0 = ppi := by
    intro k a
    rw [hI.conv_ x0 (ck k (ik k + a)) hx0dom (hdomc k _), hbelow k a]; rfl
  have hbc0 : ∀ k, I.rho (ck k (ik k)) x0 = ppi := fun k => hbc k 0
  have hinj : ∀ v w : Unit ⊕ N,
      Sum.elim (fun _ : Unit => x0) (fun k => ck k (ik k)) v
        = Sum.elim (fun _ : Unit => x0) (fun k => ck k (ik k)) w → v = w := by
    rintro (⟨⟩ | k) (⟨⟩ | k') h
    · rfl
    · exact absurd h (hdist k')
    · exact absurd h.symm (hdist k)
    · exact congrArg Sum.inr (hkinj k k' h)
  refine
    { hp := hp
      frame_q := frame_ext (by
        rintro (⟨⟩ | k) (⟨⟩ | k')
        · exact hI.refl_eq x0 hx0dom
        · show conv (I.rho (ck k' (ik k')) x0) = conv ppi; rw [hbc0 k']
        · exact hbc0 k
        · rfl) (readoff_qnet_frame hI (fun _ : Unit => x0) (fun k => ck k (ik k))
          (fun _ => hx0dom) (fun k => hdomc k (ik k)) hinj)
      e_clash := fun _ a h => mty_clash h
      e_nobot := fun _ => mty_nobot
      e_and := fun _ x y h => mty_and h
      e_or := fun _ x y h => mty_or h
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := fun _ _ r c hmem hr =>
        mty_all hmem hx0dom ((hI.refl_eq x0 hx0dom).trans hr)
      ek_all := fun _ r c hmem k hr a _ =>
        mty_all hmem (hdomc k _) ((hbelow k a).trans hr)
      ke_all := fun k a _ r c hmem _ hr =>
        mty_all hmem hx0dom ((hbc k a).trans hr)
      kk_pp := fun k _ ha E hE b hb =>
        segment_kk_pp hI (fun n => hdomc k n) (fun n => hstep k n) (hty k) ha hE b hb
      kk_ppi := fun k _ ha E hE b hb =>
        segment_kk_ppi hI (fun n => hdomc k n) (fun n => hstep k n) (hty k) ha hE b hb
      kk_eq := fun k _ _ E hE => seg_eq hI (fun n => hdomc k n) hE
      kq_all := ?_
      e_ex := ?_
      k_ex := ?_ }
  · -- kq_all: cross-value read off the model; `hrectQ` transports the `∀`
    intro k k' hkk a _ r c hmem hr b _
    apply mty_all hmem (hdomc k' _)
    rw [hrectQ k k' hkk a b]; exact hr
  · -- e_ex: root routes each `∃PP.(Gₖ k)` into kernel k; `∃EQ` self
    intro _ r c hmem
    rcases hroot_dem r c hmem with ⟨rfl, k, rfl⟩ | rfl
    · exact Or.inr ⟨k, rfl, 0, hp k, hchainG k⟩
    · refine Or.inl ⟨(), rfl, ?_⟩
      obtain ⟨y, hy, hyr, hyc⟩ := mty_ex hmem
      rwa [hI.eq_id x0 y hx0dom hy hyr]
  · -- k_ex: each kernel serves its own `∃PP.(Gₖ k)` via its chain
    intro k a _ r c hmem
    rcases hphase_dem k a r c hmem with ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, 0, hp k, hchainG k⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, seg_ex_eq hI (fun n => hdomc k n) hmem⟩))

/-- THE SELF-CARRYING POSET MULTI-KERNEL: as `posetKernel_ok` but each
    kernel's phase demands are served BY ITS OWN CHAIN at some phase
    (`hphase_dem` weakened to `∃ b, D ∈ phase b`, `vkernelG`-style), so a
    single kernel can serve SEVERAL `∃PP` demands.  Removes the
    single-demand-per-kernel limit; the root still routes to primary
    demands `Gₖ`. -/
theorem posetKernelG_ok (hI : RCC5Interp I) (C0 : Concept)
    (x0 : α) (hx0dom : I.dom x0) (ck : N → Nat → α) {ik pk : N → Nat}
    (hdomc : ∀ k n, I.dom (ck k n))
    (hstep : ∀ k n, I.rho (ck k n) (ck k (n + 1)) = pp)
    (hp : ∀ k, 0 < pk k)
    (hty : ∀ k, mty C0 I (ck k (ik k)) = mty C0 I (ck k (ik k + pk k)))
    (hbelow : ∀ k a, I.rho x0 (ck k (ik k + a)) = pp)
    (hdist : ∀ k, x0 ≠ ck k (ik k))
    (hkinj : ∀ k k', ck k (ik k) = ck k' (ik k') → k = k')
    (hrectQ : ∀ k k', k ≠ k' → ∀ a b,
      I.rho (ck k (ik k + a)) (ck k' (ik k' + b))
        = I.rho (ck k (ik k)) (ck k' (ik k')))
    (Gk : N → Concept)
    (hchainG : ∀ k, Gk k ∈ mty C0 I (ck k (ik k)))
    (hphase_dem : ∀ k a r D, Concept.ex r D ∈ mty C0 I (ck k (ik k + a)) →
      (r = pp ∧ ∃ b, b < pk k ∧ D ∈ mty C0 I (ck k (ik k + b))) ∨ r = eq)
    (hroot_dem : ∀ r D, Concept.ex r D ∈ mty C0 I x0 →
      (r = pp ∧ ∃ k, D = Gk k) ∨ r = eq) :
    MultiTierOk (posetKernel I C0 x0 ck ik pk) := by
  have hbc : ∀ k a, I.rho (ck k (ik k + a)) x0 = ppi := by
    intro k a
    rw [hI.conv_ x0 (ck k (ik k + a)) hx0dom (hdomc k _), hbelow k a]; rfl
  have hbc0 : ∀ k, I.rho (ck k (ik k)) x0 = ppi := fun k => hbc k 0
  have hinj : ∀ v w : Unit ⊕ N,
      Sum.elim (fun _ : Unit => x0) (fun k => ck k (ik k)) v
        = Sum.elim (fun _ : Unit => x0) (fun k => ck k (ik k)) w → v = w := by
    rintro (⟨⟩ | k) (⟨⟩ | k') h
    · rfl
    · exact absurd h (hdist k')
    · exact absurd h.symm (hdist k)
    · exact congrArg Sum.inr (hkinj k k' h)
  refine
    { hp := hp
      frame_q := frame_ext (by
        rintro (⟨⟩ | k) (⟨⟩ | k')
        · exact hI.refl_eq x0 hx0dom
        · show conv (I.rho (ck k' (ik k')) x0) = conv ppi; rw [hbc0 k']
        · exact hbc0 k
        · rfl) (readoff_qnet_frame hI (fun _ : Unit => x0) (fun k => ck k (ik k))
          (fun _ => hx0dom) (fun k => hdomc k (ik k)) hinj)
      e_clash := fun _ a h => mty_clash h
      e_nobot := fun _ => mty_nobot
      e_and := fun _ x y h => mty_and h
      e_or := fun _ x y h => mty_or h
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := fun _ _ r c hmem hr =>
        mty_all hmem hx0dom ((hI.refl_eq x0 hx0dom).trans hr)
      ek_all := fun _ r c hmem k hr a _ =>
        mty_all hmem (hdomc k _) ((hbelow k a).trans hr)
      ke_all := fun k a _ r c hmem _ hr =>
        mty_all hmem hx0dom ((hbc k a).trans hr)
      kk_pp := fun k _ ha E hE b hb =>
        segment_kk_pp hI (fun n => hdomc k n) (fun n => hstep k n) (hty k) ha hE b hb
      kk_ppi := fun k _ ha E hE b hb =>
        segment_kk_ppi hI (fun n => hdomc k n) (fun n => hstep k n) (hty k) ha hE b hb
      kk_eq := fun k _ _ E hE => seg_eq hI (fun n => hdomc k n) hE
      kq_all := ?_
      e_ex := ?_
      k_ex := ?_ }
  · intro k k' hkk a _ r c hmem hr b _
    apply mty_all hmem (hdomc k' _)
    rw [hrectQ k k' hkk a b]; exact hr
  · intro _ r c hmem
    rcases hroot_dem r c hmem with ⟨rfl, k, rfl⟩ | rfl
    · exact Or.inr ⟨k, rfl, 0, hp k, hchainG k⟩
    · refine Or.inl ⟨(), rfl, ?_⟩
      obtain ⟨y, hy, hyr, hyc⟩ := mty_ex hmem
      rwa [hI.eq_id x0 y hx0dom hy hyr]
  · -- k_ex: SELF-CARRYING — the demand is served by this chain at phase b
    intro k a _ r c hmem
    rcases hphase_dem k a r c hmem with ⟨rfl, b, hb, hDb⟩ | rfl
    · exact Or.inr (Or.inl ⟨rfl, b, hb, hDb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, seg_ex_eq hI (fun n => hdomc k n) hmem⟩))

end VerticalKernel

/-- COMPLETENESS for the single-tower case: given the demand condition
    `hdem` and that `C0` forces `persistPP` (`hforce`), every satisfiable
    such `C0` has an accepted code in `codesV C0`. -/
theorem vtower_hcompl (C0 G : Concept)
    (hdem : ∀ r D, Concept.ex r D ∈ cl C0 → (r = pp ∧ D = G) ∨ r = eq)
    (hforce : ∀ {α : Type} (I : Interp α) (x : α), RCC5Interp I → I.dom x →
      sat I x C0 → persistPP I C0 G x) :
    Satisfiable C0 → ∃ p ∈ codesV C0, (p.1).mtAcceptB p.2 C0 = true := by
  intro hsat
  obtain ⟨α, I, hI, x0, hdom0, hsat0⟩ := hsat
  have hC0 : C0 ∈ mty C0 I x0 := mem_mty.mpr ⟨cl_self C0, hsat0⟩
  have hpp : persistPP I C0 G x0 := hforce I x0 hI hdom0 hsat0
  obtain ⟨c, i, p, hpB, hp, hok, hCtau⟩ := vkernel1_bounded_ok hI C0 G hdem hpp hC0
  have hmtylbl : ∀ (x : α), mty C0 I x ∈ allListsLe (cl C0) (cl C0).length := by
    intro x
    rw [mem_allListsLe]
    exact ⟨by rw [mty]; exact List.length_filter_le _ _,
      fun y hy => by rw [mty] at hy; exact (List.mem_filter.mp hy).1⟩
  refine ⟨(encodeMT (reindexMT (fun _ : Fin 1 => (() : Unit))
    (fun _ : Fin 1 => (() : Unit)) (vkernel1 I C0 c x0 i p)), 0), ?_, ?_⟩
  · exact unitTower_mem_codesV (vkernel1 I C0 c x0 i p) C0
      (hmtylbl x0) (fun a => hmtylbl (c (i + a))) hpB
  · exact unitTower_accepted (vkernel1 I C0 c x0 i p) hok C0 hCtau

/-- **THE SINGLE-TOWER VERTICAL FRAGMENT IS DECIDABLE.**  A concept whose
    only existentials are `∃PP.G`/`∃EQ` (`hdem`) and which forces the
    persistent `∃PP.G` tower (`hforce`) has decidable satisfiability — the
    FIRST kernel-checked VERTICAL decidability, built on the general
    encoder + the bounded pigeonhole (period `≤ K(C0)`). -/
def decidableSat_vtower (C0 G : Concept)
    (hdem : ∀ r D, Concept.ex r D ∈ cl C0 → (r = pp ∧ D = G) ∨ r = eq)
    (hforce : ∀ {α : Type} (I : Interp α) (x : α), RCC5Interp I → I.dom x →
      sat I x C0 → persistPP I C0 G x) :
    Decidable (Satisfiable C0) :=
  decidableSat_of_codes C0 (codesV C0) (vtower_hcompl C0 G hdem hforce)

/-- COMPLETENESS for the SELF-CARRYING case: `hdem` only needs every
    existential `∃PP`/`∃EQ`; `hforce` gives a persistent `∃PP.G0` chain
    generator AND co-carrying (every `∃PP`-demand-arg's `∀PP` holds at the
    root).  Every satisfiable such `C0` has an accepted code in `codesV`. -/
theorem vtower_hcomplG (C0 G0 : Concept)
    (hdem : ∀ r D, Concept.ex r D ∈ cl C0 → r = pp ∨ r = eq)
    (hforce : ∀ {α : Type} (I : Interp α) (x : α), RCC5Interp I → I.dom x →
      sat I x C0 → persistPP I C0 G0 x ∧
        (∀ D, Concept.ex pp D ∈ cl C0 → sat I x (Concept.all pp D))) :
    Satisfiable C0 → ∃ p ∈ codesV C0, (p.1).mtAcceptB p.2 C0 = true := by
  intro hsat
  obtain ⟨α, I, hI, x0, hdom0, hsat0⟩ := hsat
  have hC0 : C0 ∈ mty C0 I x0 := mem_mty.mpr ⟨cl_self C0, hsat0⟩
  obtain ⟨hpp, hcarry⟩ := hforce I x0 hI hdom0 hsat0
  obtain ⟨c, i, p, hpB, hp, hok, hCtau⟩ :=
    vkernel1G_bounded_ok hI C0 G0 hdem hcarry hpp hC0
  have hmtylbl : ∀ (x : α), mty C0 I x ∈ allListsLe (cl C0) (cl C0).length := by
    intro x
    rw [mem_allListsLe]
    exact ⟨by rw [mty]; exact List.length_filter_le _ _,
      fun y hy => by rw [mty] at hy; exact (List.mem_filter.mp hy).1⟩
  refine ⟨(encodeMT (reindexMT (fun _ : Fin 1 => (() : Unit))
    (fun _ : Fin 1 => (() : Unit)) (vkernel1 I C0 c x0 i p)), 0), ?_, ?_⟩
  · exact unitTower_mem_codesV (vkernel1 I C0 c x0 i p) C0
      (hmtylbl x0) (fun a => hmtylbl (c (i + a))) hpB
  · exact unitTower_accepted (vkernel1 I C0 c x0 i p) hok C0 hCtau

/-- **THE SELF-CARRYING VERTICAL FRAGMENT IS DECIDABLE.**  A concept whose
    existentials are all `∃PP`/`∃EQ` (`hdem`, no single fixed `G`) and
    which forces a persistent chain + co-carrying (`hforce`) has decidable
    satisfiability.  Strictly generalises `decidableSat_vtower` (multi
    `∃PP`-demand, served by one self-carrying chain) — and its `k_ex`
    routing (`vkernel1G_ok`) is the mechanism the multi-tower summit
    reuses. -/
def decidableSat_vtowerG (C0 G0 : Concept)
    (hdem : ∀ r D, Concept.ex r D ∈ cl C0 → r = pp ∨ r = eq)
    (hforce : ∀ {α : Type} (I : Interp α) (x : α), RCC5Interp I → I.dom x →
      sat I x C0 → persistPP I C0 G0 x ∧
        (∀ D, Concept.ex pp D ∈ cl C0 → sat I x (Concept.all pp D))) :
    Decidable (Satisfiable C0) :=
  decidableSat_of_codes C0 (codesV C0) (vtower_hcomplG C0 G0 hdem hforce)

/-- COMPLETENESS for the ROUND-ROBIN (general non-co-carrying) case: a
    demand list `Ds` covering every `∃PP`-arg (`hDscov`), all `∃PP`/`∃EQ`
    (`hdem`), forced multi-persistent at the root (`hforce`).  Every
    satisfiable such `C0` has an accepted code in the wider `codesVB` —
    the round-robin chain's period covers all demands (`rr_covers`), so the
    self-carrying `vkernel1G_ok` fires WITHOUT co-carrying. -/
theorem vtower_rr_hcompl (C0 : Concept) (Ds : List Concept) (hLpos : 0 < Ds.length)
    (hdem : ∀ r D, Concept.ex r D ∈ cl C0 → r = pp ∨ r = eq)
    (hDscov : ∀ D, Concept.ex pp D ∈ cl C0 → D ∈ Ds)
    (hforce : ∀ {α : Type} (I : Interp α) (x : α), RCC5Interp I → I.dom x →
      sat I x C0 → persistAll I C0 Ds x) :
    Satisfiable C0 → ∃ q ∈ codesVB C0
      ((allListsLe (cl C0) (cl C0).length).length * Ds.length),
      (q.1).mtAcceptB q.2 C0 = true := by
  intro hsat
  obtain ⟨α, I, hI, x0, hdom0, hsat0⟩ := hsat
  have hC0 : C0 ∈ mty C0 I x0 := mem_mty.mpr ⟨cl_self C0, hsat0⟩
  have hpa : persistAll I C0 Ds x0 := hforce I x0 hI hdom0 hsat0
  obtain ⟨i, p, hi, hp, hpbd, hdvd, hty⟩ := rr_segment hI C0 Ds hLpos x0 hpa
  have hdom_d : ∀ n, I.dom (rrPt hI C0 Ds hLpos x0 hpa n) :=
    fun n => rrPt_dom hI C0 Ds hLpos x0 hpa n
  have hstep_d : ∀ n, I.rho (rrPt hI C0 Ds hLpos x0 hpa n)
      (rrPt hI C0 Ds hLpos x0 hpa (n + 1)) = pp :=
    fun n => rrPt_step hI C0 Ds hLpos x0 hpa n
  have hd0 : rrPt hI C0 Ds hLpos x0 hpa 0 = x0 := rfl
  have hx0pp : ∀ a, I.rho x0 (rrPt hI C0 Ds hLpos x0 hpa (i + a)) = pp := by
    intro a
    have h := chain_model_pp hI hdom_d hstep_d 0 (i + a) (by omega)
    rwa [hd0] at h
  have hmtylbl : ∀ (x : α), mty C0 I x ∈ allListsLe (cl C0) (cl C0).length := by
    intro x
    rw [mem_allListsLe]
    exact ⟨by rw [mty]; exact List.length_filter_le _ _,
      fun y hy => by rw [mty] at hy; exact (List.mem_filter.mp hy).1⟩
  have hcov : ∀ r D, Concept.ex r D ∈ cl C0 →
      (r = pp ∧ ∃ b, b < p ∧ D ∈ mty C0 I (rrPt hI C0 Ds hLpos x0 hpa (i + b))) ∨
        r = eq := by
    intro r D hcl
    rcases hdem r D hcl with rfl | rfl
    · have hDDs : D ∈ Ds := hDscov D hcl
      obtain ⟨⟨k, hk⟩, hget⟩ := List.get_of_mem hDDs
      obtain ⟨b, hbp, hb⟩ := rr_covers hI C0 Ds hLpos x0 hpa i p hi hp hdvd k hk
      exact Or.inl ⟨rfl, b, hbp, hget ▸ hb⟩
    · exact Or.inr rfl
  have hok := vkernel1G_ok hI C0 (rrPt hI C0 Ds hLpos x0 hpa) x0 hdom0 hdom_d
    hstep_d hp hty hx0pp
    (fun a r D hmem => hcov r D (mty_sub _ hmem))
    (fun r D hmem => hcov r D (mty_sub _ hmem))
  refine ⟨(encodeMT (reindexMT (fun _ : Fin 1 => (() : Unit))
    (fun _ : Fin 1 => (() : Unit))
    (vkernel1 I C0 (rrPt hI C0 Ds hLpos x0 hpa) x0 i p)), 0), ?_, ?_⟩
  · exact unitTower_mem_codesVB
      (vkernel1 I C0 (rrPt hI C0 Ds hLpos x0 hpa) x0 i p) C0 _
      (hmtylbl x0) (fun a => hmtylbl (rrPt hI C0 Ds hLpos x0 hpa (i + a))) hpbd
  · exact unitTower_accepted
      (vkernel1 I C0 (rrPt hI C0 Ds hLpos x0 hpa) x0 i p) hok C0 hC0

/-- **THE ROUND-ROBIN VERTICAL FRAGMENT IS DECIDABLE.**  Concepts whose
    existentials are all `∃PP`/`∃EQ`, whose `∃PP`-args are covered by a
    demand list `Ds` that is forced multi-persistent at the root — decided
    via the round-robin chain + the wider `codesVB`.  Handles NON-co-carrying
    concepts (distinct demands served round-robin), strictly beyond
    `decidableSat_vtowerG`; `∀PPI`-free. -/
def decidableSat_vtowerRR (C0 : Concept) (Ds : List Concept) (hLpos : 0 < Ds.length)
    (hdem : ∀ r D, Concept.ex r D ∈ cl C0 → r = pp ∨ r = eq)
    (hDscov : ∀ D, Concept.ex pp D ∈ cl C0 → D ∈ Ds)
    (hforce : ∀ {α : Type} (I : Interp α) (x : α), RCC5Interp I → I.dom x →
      sat I x C0 → persistAll I C0 Ds x) :
    Decidable (Satisfiable C0) :=
  decidableSat_of_codes C0
    (codesVB C0 ((allListsLe (cl C0) (cl C0).length).length * Ds.length))
    (vtower_rr_hcompl C0 Ds hLpos hdem hDscov hforce)

/-- COMPLETENESS for the DESCENDING round-robin (mirror of
    `vtower_rr_hcompl`): `∃PPI`/`∃EQ` demands (`hdem`), covered by `Ds`
    (`hDscov`), forced multi-persistent-down at the root (`hforce`).
    Uses the descending chain + `vkernel1GI_ok`. -/
theorem vtower_rrI_hcompl (C0 : Concept) (Ds : List Concept) (hLpos : 0 < Ds.length)
    (hdem : ∀ r D, Concept.ex r D ∈ cl C0 → r = ppi ∨ r = eq)
    (hDscov : ∀ D, Concept.ex ppi D ∈ cl C0 → D ∈ Ds)
    (hforce : ∀ {α : Type} (I : Interp α) (x : α), RCC5Interp I → I.dom x →
      sat I x C0 → persistAllI I C0 Ds x) :
    Satisfiable C0 → ∃ q ∈ codesVB C0
      ((allListsLe (cl C0) (cl C0).length).length * Ds.length),
      (q.1).mtAcceptB q.2 C0 = true := by
  intro hsat
  obtain ⟨α, I, hI, x0, hdom0, hsat0⟩ := hsat
  have hC0 : C0 ∈ mty C0 I x0 := mem_mty.mpr ⟨cl_self C0, hsat0⟩
  have hpa : persistAllI I C0 Ds x0 := hforce I x0 hI hdom0 hsat0
  obtain ⟨i, p, hi, hp, hpbd, hdvd, hty⟩ := rr_segmentI hI C0 Ds hLpos x0 hpa
  have hdom_d : ∀ n, I.dom (rrPtI hI C0 Ds hLpos x0 hpa n) :=
    fun n => rrPtI_dom hI C0 Ds hLpos x0 hpa n
  have hstep_d : ∀ n, I.rho (rrPtI hI C0 Ds hLpos x0 hpa n)
      (rrPtI hI C0 Ds hLpos x0 hpa (n + 1)) = ppi :=
    fun n => rrPtI_step hI C0 Ds hLpos x0 hpa n
  have hd0 : rrPtI hI C0 Ds hLpos x0 hpa 0 = x0 := rfl
  have hx0ppi : ∀ a, I.rho x0 (rrPtI hI C0 Ds hLpos x0 hpa (i + a)) = ppi := by
    intro a
    have h := dchain_model_ppi hI hdom_d hstep_d 0 (i + a) (by omega)
    rwa [hd0] at h
  have hmtylbl : ∀ (x : α), mty C0 I x ∈ allListsLe (cl C0) (cl C0).length := by
    intro x
    rw [mem_allListsLe]
    exact ⟨by rw [mty]; exact List.length_filter_le _ _,
      fun y hy => by rw [mty] at hy; exact (List.mem_filter.mp hy).1⟩
  have hcov : ∀ r D, Concept.ex r D ∈ cl C0 →
      (r = ppi ∧ ∃ b, b < p ∧ D ∈ mty C0 I (rrPtI hI C0 Ds hLpos x0 hpa (i + b))) ∨
        r = eq := by
    intro r D hcl
    rcases hdem r D hcl with rfl | rfl
    · have hDDs : D ∈ Ds := hDscov D hcl
      obtain ⟨⟨k, hk⟩, hget⟩ := List.get_of_mem hDDs
      obtain ⟨b, hbp, hb⟩ := rr_coversI hI C0 Ds hLpos x0 hpa i p hi hp hdvd k hk
      exact Or.inl ⟨rfl, b, hbp, hget ▸ hb⟩
    · exact Or.inr rfl
  have hok := vkernel1GI_ok hI C0 (rrPtI hI C0 Ds hLpos x0 hpa) x0 hdom0 hdom_d
    hstep_d hp hty hx0ppi
    (fun a r D hmem => hcov r D (mty_sub _ hmem))
    (fun r D hmem => hcov r D (mty_sub _ hmem))
  refine ⟨(encodeMT (reindexMT (fun _ : Fin 1 => (() : Unit))
    (fun _ : Fin 1 => (() : Unit))
    (vkernel1I I C0 (rrPtI hI C0 Ds hLpos x0 hpa) x0 i p)), 0), ?_, ?_⟩
  · exact unitTower_mem_codesVB
      (vkernel1I I C0 (rrPtI hI C0 Ds hLpos x0 hpa) x0 i p) C0 _
      (hmtylbl x0) (fun a => hmtylbl (rrPtI hI C0 Ds hLpos x0 hpa (i + a))) hpbd
  · exact unitTower_accepted
      (vkernel1I I C0 (rrPtI hI C0 Ds hLpos x0 hpa) x0 i p) hok C0 hC0

/-- **THE DESCENDING ROUND-ROBIN VERTICAL FRAGMENT IS DECIDABLE.**  The
    `∃PPI` dual of `decidableSat_vtowerRR` — distinct/incompatible `∃PPI`
    demands served round-robin down a descending tower.  `∀PP`-free. -/
def decidableSat_vtowerRRI (C0 : Concept) (Ds : List Concept) (hLpos : 0 < Ds.length)
    (hdem : ∀ r D, Concept.ex r D ∈ cl C0 → r = ppi ∨ r = eq)
    (hDscov : ∀ D, Concept.ex ppi D ∈ cl C0 → D ∈ Ds)
    (hforce : ∀ {α : Type} (I : Interp α) (x : α), RCC5Interp I → I.dom x →
      sat I x C0 → persistAllI I C0 Ds x) :
    Decidable (Satisfiable C0) :=
  decidableSat_of_codes C0
    (codesVB C0 ((allListsLe (cl C0) (cl C0).length).length * Ds.length))
    (vtower_rrI_hcompl C0 Ds hLpos hdem hDscov hforce)

/-! ### Non-vacuity: `Cvert`, a persistent-vertical concept beyond `Cinf`

`Cvert = A ⊓ ∃PP.A ⊓ ∀PP.(∃PP.A)` (`A = atom 0`) forces an infinite
ascending `PP`-tower (no finite model) and carries a real atom.  Its
ℕ-order model feeds `vkernel_ok`, so `Satisfiable Cvert` is produced
THROUGH the kernel machinery — the hypotheses are jointly satisfiable. -/

namespace VerticalWitness

/-- The ℕ-order chain is a frame. -/
theorem chainFrame : Frame chain :=
  ⟨chain_self, fun _ _ h => chain_eq_imp h, chain_conv, chain_cc⟩

/-- `A = atom 0`, true at every point; the domain is all of `ℕ`. -/
def Ivert : Interp Nat := ⟨fun _ => True, chain, fun a _ => a = 0⟩

theorem Ivert_rcc5 : RCC5Interp Ivert := frame_rcc5 chain chainFrame _

/-- `Cvert = (A ⊓ ∃PP.A) ⊓ ∀PP.(∃PP.A)`. -/
def Cvert : Concept :=
  .and (.and (.atom 0) (.ex pp (.atom 0))) (.all pp (.ex pp (.atom 0)))

/-- Every concept in `cl Cvert` is satisfied at every point (`A` holds
    everywhere and the `PP`-order is unbounded above). -/
theorem vsat_all (n : Nat) : ∀ D ∈ cl Cvert, sat Ivert n D := by
  have ha : ∀ m, sat Ivert m (Concept.atom 0) := fun _ => rfl
  have he : ∀ m, sat Ivert m (Concept.ex pp (Concept.atom 0)) :=
    fun m => ⟨m + 1, trivial, chain_lt (Nat.lt_succ_self m), ha (m + 1)⟩
  have hal : ∀ m, sat Ivert m (Concept.all pp (Concept.ex pp (Concept.atom 0))) :=
    fun _ y _ _ => he y
  intro D hD
  simp only [Cvert, cl, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false, or_assoc] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨ha n, he n⟩, hal n⟩
  · exact ⟨ha n, he n⟩
  · exact ha n
  · exact he n
  · exact ha n
  · exact hal n
  · exact he n
  · exact ha n

open Classical in
/-- Consequently every model type along the chain is the full closure. -/
theorem vfull (n : Nat) : mty Cvert Ivert n = cl Cvert := by
  unfold mty
  apply List.filter_eq_self.mpr
  intro D hD
  exact decide_eq_true (vsat_all n D hD)

/-- The only existential in the closure is `∃PP.A`. -/
def okDemand (E : Concept) : Bool :=
  match E with
  | Concept.ex r D => decide (r = pp ∧ D = Concept.atom 0)
  | _ => true

theorem cvert_demands_b : (cl Cvert).all okDemand = true := by decide

theorem cvert_demands : ∀ r D, Concept.ex r D ∈ cl Cvert →
    r = pp ∧ D = Concept.atom 0 := by
  intro r D h
  have hb := List.all_eq_true.mp cvert_demands_b (Concept.ex r D) h
  simpa only [okDemand, decide_eq_true_eq] using hb

/-- `Cvert` forces the persistent `∃PP.A` tower in EVERY model: its
    `∃PP.A` and `∀PP.(∃PP.A)` conjuncts hold, and both are in `cl Cvert`. -/
theorem cvert_force {α : Type} (I : Interp α) (x : α) (_hI : RCC5Interp I)
    (hdom : I.dom x) (hsat : sat I x Cvert) :
    persistPP I Cvert (Concept.atom 0) x := by
  obtain ⟨⟨_, hex⟩, hall⟩ := hsat
  exact ⟨hdom, mem_mty.mpr ⟨by decide, hex⟩, mem_mty.mpr ⟨by decide, hall⟩⟩

/-- **`Cvert`'s satisfiability is DECIDABLE via the vertical procedure** —
    the non-vacuity witness for `decidableSat_vtower`: `Cvert`'s demands
    are `∃PP.A` (`cvert_demands`) and it forces the tower (`cvert_force`). -/
def decidableSat_Cvert : Decidable (Satisfiable Cvert) :=
  decidableSat_vtower Cvert (Concept.atom 0)
    (fun r D h => Or.inl (cvert_demands r D h))
    (fun I x hI hdom hsat => cvert_force I x hI hdom hsat)

/-- `Cvert` is satisfiable — produced THROUGH `vkernel_ok` (a genuine
    kernel certificate), not by exhibiting the ℕ-model directly. -/
theorem cvert_satisfiable : Satisfiable Cvert := by
  have hok : MultiTierOk (vkernel Ivert Cvert (fun n => n) 0 1) :=
    vkernel_ok Ivert_rcc5 Cvert (Concept.atom 0) (fun n => n)
      (fun _ => trivial)
      (fun n => chain_lt (Nat.lt_succ_self n))
      Nat.one_pos
      ((vfull 0).trans (vfull (0 + 1)).symm)
      (by rw [vfull 0]; decide)
      (fun a r D h => Or.inl (cvert_demands r D (by rw [vfull (0 + a)] at h; exact h)))
  refine multiTier_sound (vkernel Ivert Cvert (fun n => n) 0 1) hok
    (Sum.inr ((), 0)) Cvert ?_
  have h1 : Cvert ∈ mty Cvert Ivert (0 + (0 % 1)) := by
    rw [vfull (0 + (0 % 1))]; exact cl_self Cvert
  exact h1

/-- `Cvert` is satisfiable via `vkernel1_ok` — the kernel PLUS the root
    external `0` (below the chain), which carries `Cvert` and whose
    `∃PP.A` demand is discharged INTO the kernel.  The first `e_ex`
    discharge with a genuine external. -/
theorem cvert_satisfiable_ext : Satisfiable Cvert := by
  have hok : MultiTierOk (vkernel1 Ivert Cvert (fun n => n) 0 1 1) :=
    vkernel1_ok Ivert_rcc5 Cvert (Concept.atom 0) (fun n => n) 0 trivial
      (fun _ => trivial)
      (fun n => chain_lt (Nat.lt_succ_self n))
      Nat.one_pos
      ((vfull 1).trans (vfull (1 + 1)).symm)
      (by rw [vfull 1]; decide)
      (fun a => chain_lt (by omega))
      (fun a r D h => Or.inl (cvert_demands r D (by rw [vfull (1 + a)] at h; exact h)))
      (fun r D h => Or.inl (cvert_demands r D (by rw [vfull 0] at h; exact h)))
  refine multiTier_sound (vkernel1 Ivert Cvert (fun n => n) 0 1 1) hok
    (Sum.inl ()) Cvert ?_
  show Cvert ∈ mty Cvert Ivert 0
  rw [vfull 0]; exact cl_self Cvert

/-! #### The two-tower model, for the first MULTI-kernel certificate

`chain2` = two disjoint `ℕ`-order towers (`Bool × ℕ`), cross-tower = `DR`
(disjoint), same-tower = the `chain` order.  It is a genuine RCC5 frame
(the cross cases rest on `comp(·,DR) ∋ DR` and `comp(DR,DR) ⊇ {PP,EQ,PPI}`).
`A = atom 0` holds everywhere, so `Cvert` holds at every point of both
towers — the two-ascending-kernel witness. -/

/-- Two disjoint `ℕ`-order towers; cross-tower is `DR`. -/
def chain2 : (Bool × Nat) → (Bool × Nat) → Atom :=
  fun p q => if p.1 = q.1 then chain p.2 q.2 else dr

theorem chain2_same (b : Bool) (n m : Nat) : chain2 (b, n) (b, m) = chain n m := by
  show (if b = b then chain n m else dr) = chain n m
  rw [if_pos rfl]

theorem chain2_diff {b b' : Bool} (n m : Nat) (h : b ≠ b') :
    chain2 (b, n) (b', m) = dr := by
  show (if b = b' then chain n m else dr) = dr
  rw [if_neg h]

theorem chain2_frame : Frame chain2 where
  refl_eq := fun ⟨b, n⟩ => by rw [chain2_same]; exact chain_self n
  eq_id := by
    rintro ⟨b, n⟩ ⟨b', m⟩ h
    by_cases hb : b = b'
    · subst hb; rw [chain2_same] at h
      have hnm := chain_eq_imp h; subst hnm; rfl
    · rw [chain2_diff n m hb] at h; exact absurd h (by decide)
  conv_ := by
    rintro ⟨b, n⟩ ⟨b', m⟩
    by_cases hb : b = b'
    · subst hb; rw [chain2_same, chain2_same]; exact chain_conv n m
    · rw [chain2_diff m n (fun h => hb h.symm), chain2_diff n m hb]; rfl
  comp_ := by
    rintro ⟨b, n⟩ ⟨b', m⟩ ⟨b'', k⟩
    by_cases h1 : b = b' <;> by_cases h2 : b' = b''
    · subst h1; subst h2
      rw [chain2_same, chain2_same, chain2_same]; exact chain_cc n m k
    · subst h1
      rw [chain2_same, chain2_diff n k h2, chain2_diff m k h2]
      rcases chain_vals n m with hc | hc | hc <;> rw [hc] <;> decide
    · subst h2
      rw [chain2_same, chain2_diff n m h1, chain2_diff n k h1]
      rcases chain_vals m k with hc | hc | hc <;> rw [hc] <;> decide
    · have hbb : b = b'' := by cases b <;> cases b' <;> cases b'' <;> simp_all
      subst hbb
      rw [chain2_same, chain2_diff n m h1, chain2_diff m k h2]
      rcases chain_vals n k with hc | hc | hc <;> rw [hc] <;> decide

/-- The two-tower interpretation (`A` true everywhere). -/
def Ivert2 : Interp (Bool × Nat) := ⟨fun _ => True, chain2, fun a _ => a = 0⟩

theorem Ivert2_rcc5 : RCC5Interp Ivert2 := frame_rcc5 chain2 chain2_frame _

/-- `Cvert` holds at every point of both towers. -/
theorem vsat_all2 (p : Bool × Nat) : ∀ D ∈ cl Cvert, sat Ivert2 p D := by
  have ha : ∀ q : Bool × Nat, sat Ivert2 q (Concept.atom 0) := fun _ => rfl
  have he : ∀ q : Bool × Nat, sat Ivert2 q (Concept.ex pp (Concept.atom 0)) := by
    rintro ⟨b, n⟩
    exact ⟨(b, n + 1), trivial,
      (chain2_same b n (n + 1)).trans (chain_lt (Nat.lt_succ_self n)), ha _⟩
  have hal : ∀ q : Bool × Nat,
      sat Ivert2 q (Concept.all pp (Concept.ex pp (Concept.atom 0))) :=
    fun _ y _ _ => he y
  intro D hD
  simp only [Cvert, cl, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false, or_assoc] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨ha p, he p⟩, hal p⟩
  · exact ⟨ha p, he p⟩
  · exact ha p
  · exact he p
  · exact ha p
  · exact hal p
  · exact he p
  · exact ha p

open Classical in
theorem vfull2 (p : Bool × Nat) : mty Cvert Ivert2 p = cl Cvert := by
  unfold mty
  apply List.filter_eq_self.mpr
  intro D hD
  exact decide_eq_true (vsat_all2 p D hD)

/-- `Cvert` via TWO ascending kernels — one per tower of the two-tower
    model, cross-`DR`.  The first multi-kernel certificate (`kq_all`
    non-trivially wired, though vacuous here as `Cvert` has no `∀DR`). -/
theorem cvert2_satisfiable : Satisfiable Cvert := by
  have hok : MultiTierOk
      (vkernel2 Ivert2 Cvert (fun b n => (b, n)) (fun _ => 0) (fun _ => 1)) :=
    vkernel2_ok Ivert2_rcc5 Cvert (Concept.atom 0) (fun b n => (b, n))
      (fun _ _ => trivial)
      (fun b n => (chain2_same b n (n + 1)).trans (chain_lt (Nat.lt_succ_self n)))
      (fun _ => Nat.one_pos)
      (fun k => (vfull2 (k, 0)).trans (vfull2 (k, 0 + 1)).symm)
      (fun k => by show Concept.atom 0 ∈ mty Cvert Ivert2 (k, 0);
                   rw [vfull2 (k, 0)]; decide)
      (by decide)
      (fun k k' hkk a b =>
        (chain2_diff (0 + a) (0 + b) hkk).trans (chain2_diff 0 0 hkk).symm)
      (fun k a r D h =>
        Or.inl (cvert_demands r D (by rw [vfull2 (k, 0 + a)] at h; exact h)))
  refine multiTier_sound
    (vkernel2 Ivert2 Cvert (fun b n => (b, n)) (fun _ => 0) (fun _ => 1)) hok
    (Sum.inr (true, 0)) Cvert ?_
  have h1 : Cvert ∈ mty Cvert Ivert2 (true, 0 + (0 % 1)) := by
    rw [vfull2 (true, 0 + (0 % 1))]; exact cl_self Cvert
  exact h1

/-! #### A GENUINE two-cluster concept, via `vkernel2x_ok`

`Cvert2x = Cvert ⊓ ∃DR.A` genuinely needs two clusters (the `∃DR` forces
a DR-neighbour, impossible inside one PP-tower).  In the two-tower model
each tower's `∃DR.A` is served by the OTHER tower — cross-kernel `∃`. -/

/-- `Cvert2x = Cvert ⊓ ∃DR.A` — a concept with no finite model that
    genuinely needs two DR-linked clusters. -/
def Cvert2x : Concept := .and Cvert (.ex dr (.atom 0))

theorem vsat_all2x (p : Bool × Nat) : ∀ D ∈ cl Cvert2x, sat Ivert2 p D := by
  have ha : ∀ q : Bool × Nat, sat Ivert2 q (Concept.atom 0) := fun _ => rfl
  have he : ∀ q : Bool × Nat, sat Ivert2 q (Concept.ex pp (Concept.atom 0)) := by
    rintro ⟨b, n⟩
    exact ⟨(b, n + 1), trivial,
      (chain2_same b n (n + 1)).trans (chain_lt (Nat.lt_succ_self n)), ha _⟩
  have hal : ∀ q : Bool × Nat,
      sat Ivert2 q (Concept.all pp (Concept.ex pp (Concept.atom 0))) :=
    fun _ y _ _ => he y
  have hdr : ∀ q : Bool × Nat, sat Ivert2 q (Concept.ex dr (Concept.atom 0)) := by
    rintro ⟨b, n⟩
    exact ⟨(! b, 0), trivial, chain2_diff n 0 (by cases b <;> decide), ha _⟩
  intro D hD
  simp only [Cvert2x, Cvert, cl, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false, or_assoc] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨⟨ha p, he p⟩, hal p⟩, hdr p⟩
  · exact ⟨⟨ha p, he p⟩, hal p⟩
  · exact ⟨ha p, he p⟩
  · exact ha p
  · exact he p
  · exact ha p
  · exact hal p
  · exact he p
  · exact ha p
  · exact hdr p
  · exact ha p

open Classical in
theorem vfull2x (p : Bool × Nat) : mty Cvert2x Ivert2 p = cl Cvert2x := by
  unfold mty
  apply List.filter_eq_self.mpr
  intro D hD
  exact decide_eq_true (vsat_all2x p D hD)

/-- Existentials of `cl Cvert2x`: `∃PP.A` and `∃DR.A` (arg always `A`). -/
def okDemand2x (E : Concept) : Bool :=
  match E with
  | Concept.ex r D => decide ((r = pp ∨ r = dr) ∧ D = Concept.atom 0)
  | _ => true

theorem cvert2x_demands_b : (cl Cvert2x).all okDemand2x = true := by decide

theorem cvert2x_demands : ∀ r D, Concept.ex r D ∈ cl Cvert2x →
    (r = pp ∨ r = dr) ∧ D = Concept.atom 0 := by
  intro r D h
  have hb := List.all_eq_true.mp cvert2x_demands_b (Concept.ex r D) h
  simpa only [okDemand2x, decide_eq_true_eq] using hb

/-- `Cvert2x` is satisfiable via `vkernel2x_ok` — TWO towers, each
    serving the other's `∃DR.A` (cross-kernel `∃`).  The first GENUINE
    (non-artificial) multi-kernel certificate. -/
theorem cvert2x_satisfiable : Satisfiable Cvert2x := by
  have hok : MultiTierOk
      (vkernel2 Ivert2 Cvert2x (fun b n => (b, n)) (fun _ => 0) (fun _ => 1)) :=
    vkernel2x_ok Ivert2_rcc5 Cvert2x (Concept.atom 0) (Concept.atom 0)
      (fun b n => (b, n))
      (fun _ _ => trivial)
      (fun b n => (chain2_same b n (n + 1)).trans (chain_lt (Nat.lt_succ_self n)))
      (fun _ => Nat.one_pos)
      (fun k => (vfull2x (k, 0)).trans (vfull2x (k, 0 + 1)).symm)
      (fun k => by show Concept.atom 0 ∈ mty Cvert2x Ivert2 (k, 0);
                   rw [vfull2x (k, 0)]; decide)
      (by decide)
      (fun k k' hkk a b =>
        (chain2_diff (0 + a) (0 + b) hkk).trans (chain2_diff 0 0 hkk).symm)
      (fun k => by show Concept.atom 0 ∈ mty Cvert2x Ivert2 (! k, 0);
                   rw [vfull2x (! k, 0)]; decide)
      (fun k => chain2_diff 0 0 (by cases k <;> decide))
      (fun k a r D h => by
        have hrd := cvert2x_demands r D (by rw [vfull2x (k, 0 + a)] at h; exact h)
        rcases hrd.1 with rfl | rfl
        · exact Or.inl ⟨rfl, hrd.2⟩
        · exact Or.inr (Or.inl ⟨rfl, hrd.2⟩))
  refine multiTier_sound
    (vkernel2 Ivert2 Cvert2x (fun b n => (b, n)) (fun _ => 0) (fun _ => 1)) hok
    (Sum.inr (true, 0)) Cvert2x ?_
  have h1 : Cvert2x ∈ mty Cvert2x Ivert2 (true, 0 + (0 % 1)) := by
    rw [vfull2x (true, 0 + (0 % 1))]; exact cl_self Cvert2x
  exact h1

/-! #### The DESCENDING witness (reversed `ℕ`-order, no `ℤ` needed)

`dchainN i j := chain j i` is the `ℕ`-order READ BACKWARDS — a genuine
RCC5 frame whose step `dchainN n (n+1) = chain (n+1) n = PPI` is
descending.  `Dvert = A ⊓ ∃PPI.A ⊓ ∀PPI.(∃PPI.A)` (no finite model)
feeds `dvkernel_ok`. -/

/-- The `ℕ`-order reversed: an infinite DESCENDING `PPI`-chain. -/
def dchainN (i j : Nat) : Atom := chain j i

theorem dchainN_frame : Frame dchainN where
  refl_eq := fun i => chain_self i
  eq_id := fun i j h => (chain_eq_imp h).symm
  conv_ := fun i j => chain_conv j i
  comp_ := by
    intro i j k
    show chain k i ∈ comp (chain j i) (chain k j)
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
      · simp only [chain_gt hij, chain_gt hjk, chain_gt (Nat.lt_trans hij hjk)]; decide
      · subst hjk; simp only [chain_gt hij, chain_self]; decide
      · simp only [chain_gt hij, chain_lt hjk]
        rcases chain_vals k i with h | h | h <;> simp only [h] <;> decide
    · subst hij
      simp only [chain_self]
      rcases chain_vals k i with h | h | h <;> simp only [h] <;> decide
    · rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
      · simp only [chain_lt hij, chain_gt hjk]
        rcases chain_vals k i with h | h | h <;> simp only [h] <;> decide
      · subst hjk; simp only [chain_lt hij, chain_self]; decide
      · simp only [chain_lt hij, chain_lt hjk, chain_lt (Nat.lt_trans hjk hij)]; decide

/-- The descending interpretation (`A` true everywhere). -/
def Idvert : Interp Nat := ⟨fun _ => True, dchainN, fun a _ => a = 0⟩

theorem Idvert_rcc5 : RCC5Interp Idvert := frame_rcc5 dchainN dchainN_frame _

/-- `Dvert = (A ⊓ ∃PPI.A) ⊓ ∀PPI.(∃PPI.A)`. -/
def Dvert : Concept :=
  .and (.and (.atom 0) (.ex ppi (.atom 0))) (.all ppi (.ex ppi (.atom 0)))

theorem dvsat_all (n : Nat) : ∀ D ∈ cl Dvert, sat Idvert n D := by
  have ha : ∀ m, sat Idvert m (Concept.atom 0) := fun _ => rfl
  have he : ∀ m, sat Idvert m (Concept.ex ppi (Concept.atom 0)) :=
    fun m => ⟨m + 1, trivial, chain_gt (Nat.lt_succ_self m), ha (m + 1)⟩
  have hal : ∀ m, sat Idvert m (Concept.all ppi (Concept.ex ppi (Concept.atom 0))) :=
    fun _ y _ _ => he y
  intro D hD
  simp only [Dvert, cl, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false, or_assoc] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨ha n, he n⟩, hal n⟩
  · exact ⟨ha n, he n⟩
  · exact ha n
  · exact he n
  · exact ha n
  · exact hal n
  · exact he n
  · exact ha n

open Classical in
theorem dvfull (n : Nat) : mty Dvert Idvert n = cl Dvert := by
  unfold mty
  apply List.filter_eq_self.mpr
  intro D hD
  exact decide_eq_true (dvsat_all n D hD)

def okDemandD (E : Concept) : Bool :=
  match E with
  | Concept.ex r D => decide (r = ppi ∧ D = Concept.atom 0)
  | _ => true

theorem dvert_demands_b : (cl Dvert).all okDemandD = true := by decide

theorem dvert_demands : ∀ r D, Concept.ex r D ∈ cl Dvert →
    r = ppi ∧ D = Concept.atom 0 := by
  intro r D h
  have hb := List.all_eq_true.mp dvert_demands_b (Concept.ex r D) h
  simpa only [okDemandD, decide_eq_true_eq] using hb

/-- `Dvert` is satisfiable via the DESCENDING kernel `dvkernel_ok`. -/
theorem dvert_satisfiable : Satisfiable Dvert := by
  have hok : MultiTierOk (dvkernel Idvert Dvert (fun n => n) 0 1) :=
    dvkernel_ok Idvert_rcc5 Dvert (Concept.atom 0) (fun n => n)
      (fun _ => trivial)
      (fun n => chain_gt (Nat.lt_succ_self n))
      Nat.one_pos
      ((dvfull 0).trans (dvfull (0 + 1)).symm)
      (by rw [dvfull 0]; decide)
      (fun a r D h => Or.inl (dvert_demands r D (by rw [dvfull (0 + a)] at h; exact h)))
  refine multiTier_sound (dvkernel Idvert Dvert (fun n => n) 0 1) hok
    (Sum.inr ((), 0)) Dvert ?_
  have h1 : Dvert ∈ mty Dvert Idvert (0 + (0 % 1)) := by
    rw [dvfull (0 + (0 % 1))]; exact cl_self Dvert
  exact h1

/-! ### `Cdesc`: the DESCENDING non-co-carrying witness (`Calt` dual)

`Cdesc = ∃PPI.A₀ ⊓ ∃PPI.¬A₀ ⊓ ∀PPI.(∃PPI.A₀) ⊓ ∀PPI.(∃PPI.¬A₀)` — two
INCOMPATIBLE `∃PPI` demands served round-robin down a descending tower;
the non-vacuity witness for `decidableSat_vtowerRRI`. -/

def Cdesc : Concept :=
  .and (.and (.and (.ex ppi (.atom 0)) (.ex ppi (.natom 0)))
    (.all ppi (.ex ppi (.atom 0)))) (.all ppi (.ex ppi (.natom 0)))

def cdescDem (E : Concept) : Bool :=
  match E with
  | Concept.ex r _ => decide (r = ppi ∨ r = eq)
  | _ => true

theorem cdesc_dem_b : (cl Cdesc).all cdescDem = true := by decide

theorem cdesc_dem : ∀ r D, Concept.ex r D ∈ cl Cdesc → r = ppi ∨ r = eq := by
  intro r D h
  have hb := List.all_eq_true.mp cdesc_dem_b (Concept.ex r D) h
  simpa only [cdescDem, decide_eq_true_eq] using hb

def cdescArg (E : Concept) : Bool :=
  match E with
  | Concept.ex _ D => decide (D = Concept.atom 0 ∨ D = Concept.natom 0)
  | _ => true

theorem cdesc_arg_b : (cl Cdesc).all cdescArg = true := by decide

theorem cdesc_dscov : ∀ D, Concept.ex ppi D ∈ cl Cdesc →
    D ∈ [Concept.atom 0, Concept.natom 0] := by
  intro D h
  have hb := List.all_eq_true.mp cdesc_arg_b (Concept.ex ppi D) h
  simp only [cdescArg, decide_eq_true_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact hb

/-- `Cdesc` forces both `∃PPI` demands multi-persistent-down at every point. -/
theorem cdesc_force {α : Type} (I : Interp α) (x : α) (_hI : RCC5Interp I)
    (hdom : I.dom x) (hsat : sat I x Cdesc) :
    persistAllI I Cdesc [Concept.atom 0, Concept.natom 0] x := by
  obtain ⟨⟨⟨he0, he1⟩, hae0⟩, hae1⟩ := hsat
  refine ⟨hdom, ?_⟩
  intro D hD
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl
  · exact ⟨mem_mty.mpr ⟨by decide, he0⟩, hae0⟩
  · exact ⟨mem_mty.mpr ⟨by decide, he1⟩, hae1⟩

/-- **`Cdesc`'s satisfiability is DECIDABLE via the descending round-robin
    procedure** — the non-vacuity witness for `decidableSat_vtowerRRI`. -/
def decidableSat_Cdesc : Decidable (Satisfiable Cdesc) :=
  decidableSat_vtowerRRI Cdesc [Concept.atom 0, Concept.natom 0] (by decide)
    cdesc_dem cdesc_dscov
    (fun I x hI hdom hsat => cdesc_force I x hI hdom hsat)

/-- The reversed-`ℕ` model with `A₀` at EVEN indices only. -/
def Idalt : Interp Nat := ⟨fun _ => True, dchainN, fun a n => a = 0 ∧ n % 2 = 0⟩

theorem Idalt_rcc5 : RCC5Interp Idalt := frame_rcc5 dchainN dchainN_frame _

/-- `Cdesc` IS satisfiable: down the descending tower, each point has both
    an even (`A₀`) and an odd (`¬A₀`) proper part below, but none both. -/
theorem cdesc_satisfiable : Satisfiable Cdesc := by
  have he0 : ∀ n, sat Idalt n (Concept.ex ppi (Concept.atom 0)) :=
    fun n => ⟨2 * n + 2, trivial, chain_gt (by omega), ⟨rfl, by omega⟩⟩
  have he1 : ∀ n, sat Idalt n (Concept.ex ppi (Concept.natom 0)) :=
    fun n => ⟨2 * n + 1, trivial, chain_gt (by omega),
      fun h => by obtain ⟨_, h2⟩ := h; omega⟩
  exact ⟨Nat, Idalt, Idalt_rcc5, 0, trivial,
    ⟨⟨⟨he0 0, he1 0⟩, fun y _ _ => he0 y⟩, fun y _ _ => he1 y⟩⟩

theorem Cvert_pofree : POFree Cvert := ⟨⟨trivial, trivial⟩, by decide, trivial⟩

/-- **The `Cvert` coverage skeleton is the SINGLETON `{n}`.**  `Cvert`'s only
    demand is the vertical `∃PP.A₀` (`cvert_demands`), which stops the
    `mtkNodesH` recursion — so there are no horizontal witnesses and every node
    in `mtkNodesH n` is `n` itself.  This discharges `hpp_v0` in the degenerate
    (trivial-skeleton) merge: the sole node is the root. -/
theorem cvert_nodes_singleton :
    ∀ (n : MTKNode Ivert Cvert), ∀ m ∈ mtkNodesH n, m = n := by
  intro n
  induction n using mtkNodesH.induct with
  | _ x _ih =>
    intro m hm
    rw [mtkNodesH] at hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · rfl
    · obtain ⟨⟨F, hF⟩, _, hmm⟩ := List.mem_flatMap.mp hm'
      cases F with
      | ex r c =>
        have hmm2 : m ∈ (if r = pp ∨ r = ppi then ([] : List (MTKNode Ivert Cvert))
            else mtkNodesH (mtkWitness x hF)) := hmm
        have hr : r = pp := (cvert_demands r c (mty_sub _ (mem_mtk.mp hF).1)).1
        rw [if_pos (Or.inl hr)] at hmm2
        exact absurd hmm2 List.not_mem_nil
      | top => exact absurd hmm List.not_mem_nil
      | bot => exact absurd hmm List.not_mem_nil
      | atom a => exact absurd hmm List.not_mem_nil
      | natom a => exact absurd hmm List.not_mem_nil
      | and a b => exact absurd hmm List.not_mem_nil
      | or a b => exact absurd hmm List.not_mem_nil
      | all r c => exact absurd hmm List.not_mem_nil

/-- The root node of the `Cvert` extraction: point `0`, budget `mdepth Cvert`
    (so `Cvert` itself sits in its own `mtk` label). -/
def cvertRoot : MTKNode Ivert Cvert := ⟨0, mdepth Cvert, trivial⟩

/-- `A₀` sits in every chain point's `mtk` label at the root budget. -/
theorem cvert_atom0_mtk (n : Nat) :
    Concept.atom 0 ∈ mtk Cvert Ivert n cvertRoot.k :=
  mem_mtk.mpr ⟨(vfull n).symm ▸ (by decide : Concept.atom 0 ∈ cl Cvert),
    Nat.zero_le _⟩

open Classical in
/-- **`Cvert` extracts through the GENERIC merged engine** — the completeness
    (extraction) direction fired end-to-end.  All three model-side inputs to
    `extract_mtkKernel` are discharged on `Ivert`: `hno_ppi` from
    `no_ppi_demand` (no `∃PPI` in `cl Cvert`), `hpp_v0` from
    `cvert_nodes_singleton` (the skeleton is `{root}`, so only the root carries
    `∃PP`, served by the tower), `hk_class` from `cvert_demands` (each phase's
    only demand is the self-carrying `∃PP.A₀`).  So the generic `mtkKernel`
    certificate is valid and `multiTier_sound` reads off a model — the same
    `Satisfiable Cvert` as `cvert_satisfiable`, now through the UNIFORM
    skeleton+kernel engine rather than the bespoke `vkernel`. -/
theorem cvert_generic_satisfiable : Satisfiable Cvert := by
  have hnoppi : ∀ D, Concept.ex ppi D ∉ cl Cvert := fun D h =>
    absurd (cvert_demands ppi D h).1 (by decide)
  have hok : MultiTierOk (mtkKernel Ivert Cvert
      (fun e : {n // n ∈ mtkNodesH cvertRoot} => e.val.x) (fun e => e.val.k)
      (fun e f => decide (sAdjK e.val f.val))
      ⟨cvertRoot, self_mem_mtkNodesH cvertRoot⟩ (fun n => n) 1 1) := by
    refine extract_mtkKernel Ivert_rcc5 Cvert_pofree cvertRoot (fun n => n)
      (fun _ => trivial) (fun n => chain_lt (Nat.lt_succ_self n)) 1 1 (by decide)
      ((vfull 1).trans (vfull (1 + 1)).symm) ?_ ?_ ?_ ?_
    · intro a; show chain 0 (1 + a) = pp; exact chain_lt (by omega)
    · intro e D hdem
      have he : e.val = cvertRoot := cvert_nodes_singleton cvertRoot e.val e.property
      have hmty : Concept.ex pp D ∈ mty Cvert Ivert e.val.x := (mem_mtk.mp hdem).1
      have hD : D = Concept.atom 0 := (cvert_demands pp D (mty_sub _ hmty)).2
      subst hD
      exact ⟨Subtype.ext he, 0, by decide, cvert_atom0_mtk (1 + 0)⟩
    · exact no_ppi_demand cvertRoot hnoppi
    · intro a r D hmem
      have hmty : Concept.ex r D ∈ mty Cvert Ivert (1 + a) := (mem_mtk.mp hmem).1
      obtain ⟨hr, hD⟩ := cvert_demands r D (mty_sub _ hmty)
      subst hr; subst hD
      exact Or.inr (Or.inl ⟨rfl, 0, by decide, cvert_atom0_mtk (1 + 0)⟩)
  exact multiTier_sound _ hok (Sum.inl ⟨cvertRoot, self_mem_mtkNodesH cvertRoot⟩)
    Cvert (mem_mtk.mpr ⟨(vfull 0).symm ▸ cl_self Cvert, Nat.le_refl _⟩)

/-- **Non-vacuity of `extract_from_tower`** — `Cvert` fires through the GENERAL
    theorem (degenerate skeleton), kernel-checking that the isolated cleanliness
    premise is inhabitable and the wrapper's `hv0pp`/root/`hno_ppi` plumbing all
    fire (`hv0pp` now comes from `pp_chain_below`, not the ad-hoc `chain_lt`). -/
theorem cvert_via_tower : Satisfiable Cvert := by
  refine extract_from_tower Ivert_rcc5 Cvert_pofree (fun n => n) (fun _ => trivial)
    (fun n => chain_lt (Nat.lt_succ_self n))
    (mem_mty.mpr ⟨cl_self Cvert, vsat_all 0 Cvert (cl_self Cvert)⟩)
    (fun D h => absurd (cvert_demands ppi D h).1 (by decide))
    1 1 Nat.one_pos Nat.one_pos ((vfull 1).trans (vfull (1 + 1)).symm) ?_ ?_
  · intro e D hdem
    have he := cvert_nodes_singleton _ e.val e.property
    have hmty : Concept.ex pp D ∈ mty Cvert Ivert e.val.x := (mem_mtk.mp hdem).1
    have hD : D = Concept.atom 0 := (cvert_demands pp D (mty_sub _ hmty)).2
    subst hD
    exact ⟨Subtype.ext he, 0, Nat.one_pos, cvert_atom0_mtk (1 + 0)⟩
  · intro a r D hmem
    have hmty : Concept.ex r D ∈ mty Cvert Ivert (1 + a) := (mem_mtk.mp hmem).1
    obtain ⟨hr, hD⟩ := cvert_demands r D (mty_sub _ hmty)
    subst hr; subst hD
    exact Or.inr (Or.inl ⟨rfl, 0, Nat.one_pos, cvert_atom0_mtk (1 + 0)⟩)

/-! ### The MIXING carrier: an ascending tower + one `PO`-node

`mixRho` on `ℕ ⊕ Unit`: the `ℕ`-tower (ascending `PP`) plus a single node
`nb = inr ()` that is `PO` to every tower point.  The minimal
horizontal+vertical frame — `∃PO` served by `nb`, `∃PP` up the tower —
and (since `∀PO`-free) `nb`'s universal propagation is vacuous. -/

/-- Tower `PP` on `ℕ`, `PO` between the tower and the extra node `nb`. -/
def mixRho : (Nat ⊕ Unit) → (Nat ⊕ Unit) → Atom
  | .inl i, .inl j => chain i j
  | .inl _, .inr _ => po
  | .inr _, .inl _ => po
  | .inr _, .inr _ => eq

theorem mixRho_frame : Frame mixRho where
  refl_eq := by
    rintro (i | ⟨⟩)
    · exact chain_self i
    · rfl
  eq_id := by
    rintro (a | ⟨⟩) (b | ⟨⟩) h
    · exact congrArg Sum.inl (chain_eq_imp h)
    · change po = eq at h; exact absurd h (by decide)
    · change po = eq at h; exact absurd h (by decide)
    · rfl
  conv_ := by
    rintro (a | ⟨⟩) (b | ⟨⟩)
    · exact chain_conv a b
    · rfl
    · rfl
    · rfl
  comp_ := by
    rintro (i | ⟨⟩) (j | ⟨⟩) (k | ⟨⟩)
    · exact chainFrame.comp_ i j k
    · show po ∈ comp (chain i j) po
      rcases chain_vals i j with h | h | h <;> rw [h] <;> decide
    · show chain i k ∈ comp po po
      rcases chain_vals i k with h | h | h <;> rw [h] <;> decide
    · show po ∈ comp po eq
      decide
    · show po ∈ comp po (chain j k)
      rcases chain_vals j k with h | h | h <;> rw [h] <;> decide
    · show eq ∈ comp po po
      decide
    · show po ∈ comp eq po
      decide
    · show eq ∈ comp eq eq
      decide

/-- The mixing model: `A₀` at every tower point, `A₁` at the node `nb`. -/
def Imix : Interp (Nat ⊕ Unit) :=
  ⟨fun _ => True, mixRho, fun a x => match x with | .inl _ => a = 0 | .inr _ => a = 1⟩

theorem Imix_rcc5 : RCC5Interp Imix := frame_rcc5 mixRho mixRho_frame _

/-- A genuinely MIXED concept: a horizontal `∃PO.A₁` demand AND a vertical
    `∃PP.A₀` tower, both at the root. -/
def Cmix : Concept :=
  .and (.and (.and (.atom 0) (.ex po (.atom 1))) (.ex pp (.atom 0)))
    (.all pp (.ex pp (.atom 0)))

/-- `Cmix` IS satisfiable: at the tower root `inl 0`, the `PO`-node `nb`
    serves `∃PO.A₁` while the tower above serves `∃PP.A₀` — horizontal and
    vertical demands coexisting in one model. -/
theorem cmix_satisfiable : Satisfiable Cmix := by
  have hA : ∀ i, sat Imix (Sum.inl i) (Concept.atom 0) := fun _ => rfl
  have hB : sat Imix (Sum.inr ()) (Concept.atom 1) := rfl
  have hePP : ∀ i, sat Imix (Sum.inl i) (Concept.ex pp (Concept.atom 0)) :=
    fun i => ⟨Sum.inl (i + 1), trivial, chain_lt (Nat.lt_succ_self i), hA (i + 1)⟩
  refine ⟨Nat ⊕ Unit, Imix, Imix_rcc5, Sum.inl 0, trivial,
    ⟨⟨⟨hA 0, ⟨Sum.inr (), trivial, rfl, hB⟩⟩, hePP 0⟩, ?_⟩⟩
  rintro (j | ⟨⟩) _ hr
  · exact hePP j
  · change po = pp at hr; exact absurd hr (by decide)

theorem Cmix_pofree : POFree Cmix := ⟨⟨⟨trivial, trivial⟩, trivial⟩, by decide, trivial⟩

/-- `Cmix`'s existentials are exactly `∃PO.A₁` (horizontal) and `∃PP.A₀`
    (vertical). -/
theorem cmix_demands : ∀ r D, Concept.ex r D ∈ cl Cmix →
    (r = po ∧ D = Concept.atom 1) ∨ (r = pp ∧ D = Concept.atom 0) := by
  intro r D h
  have hb := List.all_eq_true.mp
    (show (cl Cmix).all (fun E => match E with
      | Concept.ex r D => decide ((r = po ∧ D = Concept.atom 1) ∨
          (r = pp ∧ D = Concept.atom 0))
      | _ => true) = true from by decide) (Concept.ex r D) h
  simpa only [decide_eq_true_eq] using hb

/-- The MIXED certificate reading off `Imix`: TWO externals — the root
    `inl 0` (`false`) and the `PO`-node `nb = inr ()` (`true`) — and ONE
    kernel (the `A₀`-tower `inl 1, inl 2, …`).  `∃PO.A₁` is served by the
    direct external `nb`; `∃PP.A₀` by the kernel.  The first certificate
    with BOTH non-trivial externals AND a kernel. -/
noncomputable def mixEltE : Bool → (Nat ⊕ Unit) :=
  fun b => if b then Sum.inr () else Sum.inl 0

noncomputable def mixCert (i p : Nat) : MultiTier Bool Unit where
  E := fun e f => Imix.rho (mixEltE e) (mixEltE f)
  K := fun _ e => Imix.rho (Sum.inl i) (mixEltE e)
  Q := fun _ _ => Imix.rho (Sum.inl i) (Sum.inl i)
  up := fun _ => true
  tauE := fun e => mty Cmix Imix (mixEltE e)
  p := fun _ => p
  phase := fun _ a => mty Cmix Imix (Sum.inl (i + a))

/-- `nb` (the `PO`-node) satisfies NO existential of `Cmix` — it has no
    `PP`-successor and no `PO`-successor carrying `A₁`. -/
theorem nb_no_ex : ∀ r D, Concept.ex r D ∉ mty Cmix Imix (Sum.inr ()) := by
  intro r D hmem
  rcases cmix_demands r D (mty_sub _ hmem) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨y, _, hr, hy⟩ := mty_ex hmem
    rcases y with j | ⟨⟩
    · have h2 := (mem_mty.mp hy).2; change (1 : Nat) = 0 at h2
      exact absurd h2 (by decide)
    · change eq = po at hr; exact absurd hr (by decide)
  · obtain ⟨y, _, hr, _⟩ := mty_ex hmem
    rcases y with j | ⟨⟩
    · change po = pp at hr; exact absurd hr (by decide)
    · change eq = pp at hr; exact absurd hr (by decide)

/-- `cl Cmix` has no `∀PPI` (its only `∀` is `∀PP.(∃PP.A₀)`) — so the
    kernel's `ke_all` at the `PPI`-edge to the root is vacuous. -/
theorem cmix_no_allppi : ∀ c, Concept.all ppi c ∉ cl Cmix := by
  intro c hmem
  have hb := List.all_eq_true.mp
    (show (cl Cmix).all (fun F => match F with
      | Concept.all ppi _ => false | _ => true) = true from by decide)
    (Concept.all ppi c) hmem
  simp at hb

/-- In `Imix`, a `PO` edge always has an endpoint at the `PO`-node `nb = inr ()`
    (chain edges are never `PO`). -/
theorem mixRho_po_lemma : ∀ (a b : Nat ⊕ Unit), Imix.rho a b = po →
    b = Sum.inr () ∨ a = Sum.inr () := by
  rintro (i | ⟨⟩) (j | ⟨⟩) h
  · exfalso
    rcases chain_vals i j with h' | h' | h' <;>
      · rw [show Imix.rho (Sum.inl i) (Sum.inl j) = chain i j from rfl, h'] at h
        exact absurd h (by decide)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **The `Cmix` coverage skeleton is `{n} ∪ {nb}`.**  Every node in
    `mtkNodesH n` is either `n` itself or the `PO`-node `inr ()`: a chain node's
    only non-vertical demand is `∃PO.A₁` (served by `nb`), and `nb` has no demand
    at all (`nb_no_ex`).  This is the characterization that discharges `hpp_v0`
    (only the root can carry `∃PP` among skeleton nodes) for the generic
    extraction of `Cmix` through `extract_mtkKernel`. -/
theorem cmix_nodes_root :
    ∀ (n : MTKNode Imix Cmix), ∀ m ∈ mtkNodesH n, m = n ∨ m.x = Sum.inr () := by
  intro n
  induction n using mtkNodesH.induct with
  | _ x ih =>
    intro m hm
    rw [mtkNodesH] at hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact Or.inl rfl
    · obtain ⟨⟨F, hF⟩, _, hmm⟩ := List.mem_flatMap.mp hm'
      cases F with
      | ex r c =>
        have hmm2 : m ∈ (if r = pp ∨ r = ppi then ([] : List (MTKNode Imix Cmix))
            else mtkNodesH (mtkWitness x hF)) := hmm
        by_cases hv : r = pp ∨ r = ppi
        · rw [if_pos hv] at hmm2; exact absurd hmm2 List.not_mem_nil
        · rw [if_neg hv] at hmm2
          have hwit : (mtkWitness x hF).x = Sum.inr () := by
            have hrho : Imix.rho x.x (mtkWitness x hF).x = r := mtkWitness_rho x hF
            have hmty : Concept.ex r c ∈ mty Cmix Imix x.x := (mem_mtk.mp hF).1
            have hr_po : r = po := by
              rcases cmix_demands r c (mty_sub _ hmty) with ⟨rfl, _⟩ | ⟨rfl, _⟩
              · rfl
              · exact absurd (Or.inl rfl) hv
            rcases mixRho_po_lemma x.x (mtkWitness x hF).x (hrho.trans hr_po) with hb | ha
            · exact hb
            · exact absurd (ha ▸ hmty) (nb_no_ex r c)
          rcases ih r c hF m hmm2 with hmw | hmr
          · rw [hmw]; exact Or.inr hwit
          · exact Or.inr hmr
      | top => exact absurd hmm List.not_mem_nil
      | bot => exact absurd hmm List.not_mem_nil
      | atom a => exact absurd hmm List.not_mem_nil
      | natom a => exact absurd hmm List.not_mem_nil
      | and a b => exact absurd hmm List.not_mem_nil
      | or a b => exact absurd hmm List.not_mem_nil
      | all r c => exact absurd hmm List.not_mem_nil

/-- **THE MIXED CERTIFICATE IS VALID.**  The first `MultiTierOk` with BOTH
    non-trivial externals (root `inl 0` + `PO`-node `nb`) AND a kernel (the
    `A₀`-tower).  `∃PO.A₁` served by `nb` (direct external, `E`/`K`), `∃PP.A₀`
    by the kernel.  All `PO`-edges vacuous (`mty_no_all_po`); the recurrence
    `hty` comes from `mty_segment_bounded`, so NO homogeneity bisimulation. -/
theorem mixCert_ok (i p : Nat) (hi : 0 < i) (hp : 0 < p)
    (hty : mty Cmix Imix (Sum.inl i) = mty Cmix Imix (Sum.inl (i + p))) :
    MultiTierOk (mixCert i p) := by
  have hI : RCC5Interp Imix := Imix_rcc5
  have hdomI : ∀ n : Nat, Imix.dom (Sum.inl n) := fun _ => trivial
  have hstepI : ∀ n : Nat, Imix.rho (Sum.inl n) (Sum.inl (n + 1)) = pp :=
    fun n => chain_lt (Nat.lt_succ_self n)
  have hKppi : Imix.rho (Sum.inl i) (Sum.inl 0) = ppi := chain_gt hi
  have hx0pp : ∀ a, Imix.rho (Sum.inl 0) (Sum.inl (i + a)) = pp :=
    fun a => chain_lt (by omega)
  have hA0 : ∀ j, Concept.atom 0 ∈ mty Cmix Imix (Sum.inl j) :=
    fun j => mem_mty.mpr ⟨by decide, rfl⟩
  have hA1 : Concept.atom 1 ∈ mty Cmix Imix (Sum.inr ()) :=
    mem_mty.mpr ⟨by decide, rfl⟩
  have hinj : ∀ v w : Bool ⊕ Unit,
      Sum.elim mixEltE (fun _ : Unit => Sum.inl i) v
        = Sum.elim mixEltE (fun _ : Unit => Sum.inl i) w → v = w := by
    rintro (b | ⟨⟩) (b' | ⟨⟩) h <;>
      simp only [Sum.elim_inl, Sum.elim_inr, mixEltE] at h ⊢
    · cases b <;> cases b' <;> simp_all
    · cases b <;> simp_all <;> omega
    · cases b' <;> simp_all <;> omega
  refine
    { hp := fun _ => hp
      frame_q := readoff_qnet_frame hI mixEltE (fun _ : Unit => Sum.inl i)
        (fun _ => trivial) (fun _ => trivial) hinj
      e_clash := fun _ _ h => mty_clash h
      e_nobot := fun _ => mty_nobot
      e_and := fun _ _ _ h => mty_and h
      e_or := fun _ _ _ h => mty_or h
      k_clash := fun _ _ _ n h => mty_clash h
      k_nobot := fun _ _ _ => mty_nobot
      k_and := fun _ _ _ x y h => mty_and h
      k_or := fun _ _ _ x y h => mty_or h
      ee_all := ?_
      ek_all := ?_
      ke_all := ?_
      kk_pp := fun _ a ha E hE b hb =>
        segment_kk_pp hI hdomI hstepI hty ha hE b hb
      kk_ppi := fun _ a ha E hE b hb =>
        segment_kk_ppi hI hdomI hstepI hty ha hE b hb
      kk_eq := fun _ a _ E hE =>
        mty_all hE trivial (hI.refl_eq (Sum.inl (i + a)) trivial)
      kq_all := fun k k' hne => absurd rfl hne
      e_ex := ?_
      k_ex := ?_ }
  · intro e f r c hmem hEr
    cases e <;> cases f
    · subst hEr; exact mty_all hmem trivial (hI.refl_eq _ trivial)
    · subst hEr; exact absurd hmem (mty_no_all_po Cmix_pofree)
    · subst hEr; exact absurd hmem (mty_no_all_po Cmix_pofree)
    · subst hEr; exact mty_all hmem trivial (hI.refl_eq _ trivial)
  · intro e r c hmem k hK a _
    cases e
    · rw [show (mixCert i p).K k false = ppi from hKppi,
        show conv ppi = pp from rfl] at hK
      subst hK; exact mty_all hmem trivial (hx0pp a)
    · subst hK; exact absurd hmem (mty_no_all_po Cmix_pofree)
  · intro k a _ r c hmem f hK
    cases f
    · rw [show (mixCert i p).K k false = ppi from hKppi] at hK
      subst hK; exact absurd (mty_sub _ hmem) (cmix_no_allppi c)
    · subst hK; exact absurd hmem (mty_no_all_po Cmix_pofree)
  · intro e r c hmem
    cases e
    · rcases cmix_demands r c (mty_sub _ hmem) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨true, rfl, hA1⟩
      · refine Or.inr ⟨(), ?_, 0, hp, hA0 i⟩
        rw [show (mixCert i p).K () false = ppi from hKppi, show conv ppi = pp from rfl]
    · exact absurd hmem (nb_no_ex r c)
  · intro k a _ r c hmem
    rcases cmix_demands r c (mty_sub _ hmem) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨true, rfl, hA1⟩
    · exact Or.inr (Or.inl ⟨rfl, 0, hp, hA0 i⟩)

/-- **`Cmix` is satisfiable THROUGH the mixed certificate** — the first
    end-to-end mixing result: `mty_segment_bounded` supplies the tower
    recurrence `hty`, `mixCert_ok` validates the merged (externals+kernel)
    certificate, and `multiTier_sound` reads off a model with `Cmix` at the
    root.  The `∀PO`-free mixing quadrant's certificate machinery, closed. -/
theorem mix_cert_satisfiable : Satisfiable Cmix := by
  obtain ⟨i, p, hLi, hp, _, hty⟩ :=
    mty_segment_bounded (I := Imix) Cmix (fun n => Sum.inl n) 1
  have hok := mixCert_ok i p (by omega) hp hty
  refine multiTier_sound (mixCert i p) hok (Sum.inl false) Cmix ?_
  show Cmix ∈ mty Cmix Imix (Sum.inl 0)
  have hA : ∀ j, sat Imix (Sum.inl j) (Concept.atom 0) := fun _ => rfl
  have hB : sat Imix (Sum.inr ()) (Concept.atom 1) := rfl
  have hePP : ∀ j, sat Imix (Sum.inl j) (Concept.ex pp (Concept.atom 0)) :=
    fun j => ⟨Sum.inl (j + 1), trivial, chain_lt (Nat.lt_succ_self j), hA (j + 1)⟩
  refine mem_mty.mpr ⟨cl_self Cmix,
    ⟨⟨⟨hA 0, ⟨Sum.inr (), trivial, rfl, hB⟩⟩, hePP 0⟩, ?_⟩⟩
  rintro (j | ⟨⟩) _ hr
  · exact hePP j
  · change po = pp at hr; exact absurd hr (by decide)

/-- `Cmix` holds at the tower root `inl 0` (the merged certificate's root
    external). -/
theorem cmix_at_root : Cmix ∈ mty Cmix Imix (Sum.inl 0) := by
  have hA : ∀ j, sat Imix (Sum.inl j) (Concept.atom 0) := fun _ => rfl
  have hB : sat Imix (Sum.inr ()) (Concept.atom 1) := rfl
  have hePP : ∀ j, sat Imix (Sum.inl j) (Concept.ex pp (Concept.atom 0)) :=
    fun j => ⟨Sum.inl (j + 1), trivial, chain_lt (Nat.lt_succ_self j), hA (j + 1)⟩
  refine mem_mty.mpr ⟨cl_self Cmix,
    ⟨⟨⟨hA 0, ⟨Sum.inr (), trivial, rfl, hB⟩⟩, hePP 0⟩, ?_⟩⟩
  rintro (j | ⟨⟩) _ hr
  · exact hePP j
  · change po = pp at hr; exact absurd hr (by decide)

/-- The root node for the generic `Cmix` extraction. -/
def cmixRoot : MTKNode Imix Cmix := ⟨Sum.inl 0, mdepth Cmix, trivial⟩

/-- `A₀` sits in every tower point's `mtk` label at the root budget. -/
theorem cmix_atom0_mtk (n : Nat) :
    Concept.atom 0 ∈ mtk Cmix Imix (Sum.inl n) cmixRoot.k :=
  mem_mtk.mpr ⟨mem_mty.mpr ⟨by decide, rfl⟩, Nat.zero_le _⟩

/-- The root's `∃PO.A₁` demand, as an `mtk` membership — drives the `nb`
    external witness that serves the phases' horizontal demand. -/
theorem cmix_root_po_demand :
    Concept.ex po (Concept.atom 1) ∈ mtk Cmix Imix cmixRoot.x cmixRoot.k :=
  mem_mtk.mpr ⟨mem_mty.mpr ⟨by decide, ⟨Sum.inr (), trivial, rfl, rfl⟩⟩, by decide⟩

open Classical in
/-- **`Cmix` extracts through the GENERIC engine** — the first FULLY MIXED
    concept certified through `extract_mtkKernel` (NOT the bespoke `mixCert`):
    every tower phase demands a HORIZONTAL `∃PO.A₁`, served OUT to the external
    `nb` via the `PO` `K`-edge (`mtk_k_ex`'s new route-1), while `∃PP.A₀` goes up
    the tower.  So the general mixed extraction handles the very concept
    `mixCert` needed a hand-built certificate for — the clean-phase restriction
    is gone, exactly because `∀PO`-freeness makes the `PO` `K`-edge sound. -/
theorem cmix_generic_satisfiable : Satisfiable Cmix := by
  have hnoppi : ∀ D, Concept.ex ppi D ∉ cl Cmix := fun D h => by
    rcases cmix_demands ppi D h with ⟨h', _⟩ | ⟨h', _⟩ <;> exact absurd h' (by decide)
  obtain ⟨i, p, hLi, hp, _, hty⟩ :=
    mty_segment_bounded (I := Imix) Cmix (fun n => Sum.inl n) 1
  have hok : MultiTierOk (mtkKernel Imix Cmix
      (fun e : {n // n ∈ mtkNodesH cmixRoot} => e.val.x) (fun e => e.val.k)
      (fun e f => decide (sAdjK e.val f.val))
      ⟨cmixRoot, self_mem_mtkNodesH cmixRoot⟩ (fun n => Sum.inl n) i p) := by
    refine extract_mtkKernel Imix_rcc5 Cmix_pofree cmixRoot (fun n => Sum.inl n)
      (fun _ => trivial) (fun n => chain_lt (Nat.lt_succ_self n)) i p hp hty ?_ ?_ ?_ ?_
    · intro a; show chain 0 (i + a) = pp; exact chain_lt (by omega)
    · intro e D hdem
      rcases cmix_nodes_root cmixRoot e.val e.property with he | hinr
      · have hmty : Concept.ex pp D ∈ mty Cmix Imix e.val.x := (mem_mtk.mp hdem).1
        have hD : D = Concept.atom 0 := by
          rcases cmix_demands pp D (mty_sub _ hmty) with ⟨h', _⟩ | ⟨_, h'⟩
          · exact absurd h' (by decide)
          · exact h'
        subst hD
        exact ⟨Subtype.ext he, 0, hp, cmix_atom0_mtk (i + 0)⟩
      · exact absurd ((mem_mtk.mp hdem).1) (hinr ▸ nb_no_ex pp D)
    · exact no_ppi_demand cmixRoot hnoppi
    · intro a r D hmem
      have hmty : Concept.ex r D ∈ mty Cmix Imix (Sum.inl (i + a)) := (mem_mtk.mp hmem).1
      rcases cmix_demands r D (mty_sub _ hmty) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine Or.inl ⟨⟨mtkWitness cmixRoot cmix_root_po_demand,
          mtkWitnessH_mem cmixRoot cmix_root_po_demand (by decide)⟩, ?_, rfl,
          mtkWitness_arg cmixRoot cmix_root_po_demand⟩
        intro h
        have hx : (mtkWitness cmixRoot cmix_root_po_demand).x = Sum.inr () := by
          rcases mixRho_po_lemma cmixRoot.x _
            (mtkWitness_rho cmixRoot cmix_root_po_demand) with hb | ha
          · exact hb
          · exact absurd ha (by rw [show cmixRoot.x = Sum.inl 0 from rfl]; decide)
        have h2 : (mtkWitness cmixRoot cmix_root_po_demand).x = cmixRoot.x :=
          congrArg (fun z => (z : MTKNode Imix Cmix).x) (Subtype.ext_iff.mp h)
        rw [hx, show cmixRoot.x = Sum.inl 0 from rfl] at h2
        exact absurd h2 (by decide)
      · exact Or.inr (Or.inl ⟨rfl, 0, hp, cmix_atom0_mtk (i + 0)⟩)
  exact multiTier_sound _ hok (Sum.inl ⟨cmixRoot, self_mem_mtkNodesH cmixRoot⟩)
    Cmix (mem_mtk.mpr ⟨cmix_at_root, Nat.le_refl _⟩)

open Classical in
/-- **`Cmix` through the GENERAL `extract_from_tower`** — the general mixed
    extraction fires on the HORIZONTAL-phase class (route-1).  Together with
    `cvert_via_tower` (degenerate) and `cmerge_via_tower` (non-degenerate, clean
    phases) this witnesses that the ONE general theorem spans all three current
    mixing patterns; only cleanliness (a clean model exists) is the isolated
    remaining obligation. -/
theorem cmix_via_tower : Satisfiable Cmix := by
  obtain ⟨i, p, hLi, hp, _, hty⟩ :=
    mty_segment_bounded (I := Imix) Cmix (fun n => Sum.inl n) 1
  refine extract_from_tower Imix_rcc5 Cmix_pofree (fun n => Sum.inl n)
    (fun _ => trivial) (fun n => chain_lt (Nat.lt_succ_self n)) cmix_at_root
    (fun D h => by
      rcases cmix_demands ppi D h with ⟨h', _⟩ | ⟨h', _⟩ <;> exact absurd h' (by decide))
    i p (by omega) hp hty ?_ ?_
  · intro e D hdem
    rcases cmix_nodes_root _ e.val e.property with he | hinr
    · have hmty : Concept.ex pp D ∈ mty Cmix Imix e.val.x := (mem_mtk.mp hdem).1
      have hD : D = Concept.atom 0 := by
        rcases cmix_demands pp D (mty_sub _ hmty) with ⟨h', _⟩ | ⟨_, h'⟩
        · exact absurd h' (by decide)
        · exact h'
      subst hD
      exact ⟨Subtype.ext he, 0, hp, cmix_atom0_mtk (i + 0)⟩
    · exact absurd ((mem_mtk.mp hdem).1) (hinr ▸ nb_no_ex pp D)
  · intro a r D hmem
    have hmty : Concept.ex r D ∈ mty Cmix Imix (Sum.inl (i + a)) := (mem_mtk.mp hmem).1
    rcases cmix_demands r D (mty_sub _ hmty) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine Or.inl ⟨⟨mtkWitness cmixRoot cmix_root_po_demand,
        mtkWitnessH_mem cmixRoot cmix_root_po_demand (by decide)⟩, ?_, rfl,
        mtkWitness_arg cmixRoot cmix_root_po_demand⟩
      intro h
      have hx : (mtkWitness cmixRoot cmix_root_po_demand).x = Sum.inr () := by
        rcases mixRho_po_lemma cmixRoot.x _
          (mtkWitness_rho cmixRoot cmix_root_po_demand) with hb | ha
        · exact hb
        · exact absurd ha (by rw [show cmixRoot.x = Sum.inl 0 from rfl]; decide)
      have h2 : (mtkWitness cmixRoot cmix_root_po_demand).x = cmixRoot.x :=
        congrArg (fun z => (z : MTKNode Imix Cmix).x) (Subtype.ext_iff.mp h)
      rw [hx, show cmixRoot.x = Sum.inl 0 from rfl] at h2
      exact absurd h2 (by decide)
    · exact Or.inr (Or.inl ⟨rfl, 0, hp, cmix_atom0_mtk (i + 0)⟩)

/-- The merged certificate, encoded as a `FinMT` (`nE = 2`, `nK = 1`) and
    ACCEPTED at the root — the encoding side of the mixed decision
    procedure.  `Bool ↔ Fin 2` / `Unit ↔ Fin 1` bijections are `by decide`. -/
theorem mixTower_accepted (i p : Nat) (hi : 0 < i) (hp : 0 < p)
    (hty : mty Cmix Imix (Sum.inl i) = mty Cmix Imix (Sum.inl (i + p))) :
    (encodeMT (reindexMT (fun j : Fin 2 => decide (j = 1))
      (fun _ : Fin 1 => (() : Unit)) (mixCert i p))).mtAcceptB 0 Cmix = true := by
  have hok := mixCert_ok i p hi hp hty
  have hokR := reindexMT_ok (fun j : Fin 2 => decide (j = 1))
    (fun _ : Fin 1 => (() : Unit)) (mixCert i p) hok
    (by decide) (by decide)
    (fun k k' _ => Subsingleton.elim k k')
    (fun _ => ⟨0, Subsingleton.elim _ _⟩)
  exact encodeMT_accepts _ hokR Cmix 0 cmix_at_root

/-- The fixed mixed enumeration for `Cmix` (`nE = 2`, `nK = 1`): finitely
    many candidate `FinMT` codes.  Contains the merged certificate's code. -/
def codesMCmix : List (FinMT × Nat) :=
  let labels := allListsLe (cl Cmix) (cl Cmix).length
  let phaseCol := allListsLe (allListsLe labels labels.length) 1
  (allListsLe labels 2).flatMap fun tauE =>
    (allListsLe (allListsLe allAtoms 2) 2).flatMap fun E =>
      (allListsLe (allListsLe allAtoms 2) 1).flatMap fun K =>
        (allListsLe (allListsLe allAtoms 1) 1).flatMap fun Q =>
          (allListsLe [true, false] 1).flatMap fun up =>
            phaseCol.map fun phases => (⟨tauE, E, K, Q, up, phases⟩, 0)

/-- The encoded merged certificate lies in `codesMCmix`. -/
theorem mixCode_mem (i p : Nat)
    (hpB : p ≤ (allListsLe (cl Cmix) (cl Cmix).length).length) :
    (encodeMT (reindexMT (fun j : Fin 2 => decide (j = 1))
      (fun _ : Fin 1 => (() : Unit)) (mixCert i p)), 0) ∈ codesMCmix := by
  have hmap1 : ∀ {A : Type} (g : Fin 1 → A) (u : List A), g 0 ∈ u →
      (List.finRange 1).map g ∈ allListsLe u 1 := by
    intro A g u hg; rw [mem_allListsLe]
    refine ⟨Nat.le_of_eq (by rw [List.length_map, List.length_finRange]), fun x hx => ?_⟩
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx; rw [Subsingleton.elim e 0]; exact hg
  have hmap2 : ∀ {A : Type} (g : Fin 2 → A) (u : List A), g 0 ∈ u → g 1 ∈ u →
      (List.finRange 2).map g ∈ allListsLe u 2 := by
    intro A g u h0 h1; rw [mem_allListsLe]
    refine ⟨Nat.le_of_eq (by rw [List.length_map, List.length_finRange]), fun x hx => ?_⟩
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · exact h0
    · exact h1
  have hlbl : ∀ x, mty Cmix Imix x ∈ allListsLe (cl Cmix) (cl Cmix).length := by
    intro x; rw [mem_allListsLe]
    exact ⟨by rw [mty]; exact List.length_filter_le _ _,
      fun y hy => by rw [mty] at hy; exact (List.mem_filter.mp hy).1⟩
  have hbool : ∀ b : Bool, b ∈ [true, false] := by intro b; cases b <;> decide
  simp only [codesMCmix, List.mem_flatMap, List.mem_map]
  refine ⟨_, ?_, _, ?_, _, ?_, _, ?_, _, ?_, _, ?_, rfl⟩
  · exact hmap2 _ _ (hlbl _) (hlbl _)
  · exact hmap2 _ _ (hmap2 _ _ (mem_allAtoms _) (mem_allAtoms _))
      (hmap2 _ _ (mem_allAtoms _) (mem_allAtoms _))
  · exact hmap1 _ _ (hmap2 _ _ (mem_allAtoms _) (mem_allAtoms _))
  · exact hmap1 _ _ (hmap1 _ _ (mem_allAtoms _))
  · exact hmap1 _ _ (hbool _)
  · refine hmap1 _ _ ?_
    rw [mem_allListsLe]
    refine ⟨by rw [List.length_map, List.length_range]; exact hpB, fun x hx => ?_⟩
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx; exact hlbl _

/-- **`Cmix`'s satisfiability is DECIDABLE** — the FIRST mixing decidability:
    the merged certificate's code, in the fixed `codesMCmix` enumeration and
    accepted, drives `decidableSat_of_codes`.  A concept with BOTH a
    horizontal `∃PO` and a vertical `∃PP` demand, decided. -/
def decidableSat_Cmix : Decidable (Satisfiable Cmix) :=
  decidableSat_of_codes Cmix codesMCmix (by
    intro _
    obtain ⟨i, p, hLi, hp, hpB, hty⟩ :=
      mty_segment_bounded (I := Imix) Cmix (fun n => Sum.inl n) 1
    exact ⟨_, mixCode_mem i p hpB, mixTower_accepted i p (by omega) hp hty⟩)

/-- `Cvert` via the CLUSTER-GLUE `glueMTOk` of two independent vkernels
    (cross-`PO`) — demonstrating the assembly's combine-clusters step. -/
theorem cvert_glue2 : Satisfiable Cvert := by
  have hoks : ∀ _ : Fin 2, MultiTierOk (vkernel Ivert Cvert (fun n => n) 0 1) :=
    fun _ => vkernel_ok Ivert_rcc5 Cvert (Concept.atom 0) (fun n => n)
      (fun _ => trivial) (fun n => chain_lt (Nat.lt_succ_self n)) Nat.one_pos
      ((vfull 0).trans (vfull (0 + 1)).symm) (by rw [vfull 0]; decide)
      (fun a r D h => Or.inl (cvert_demands r D (by rw [vfull (0 + a)] at h; exact h)))
  have hnopo : ∀ _ : Fin 2, MTNoPo (vkernel Ivert Cvert (fun n => n) 0 1) :=
    fun _ => vkernel_nopo Cvert_pofree _ 0 1
  have hok := glueMTOk (F := fun _ : Fin 2 => vkernel Ivert Cvert (fun n => n) 0 1)
    hoks hnopo
  refine multiTier_sound _ hok (Sum.inr ((⟨0, by decide⟩, ()), 0)) Cvert ?_
  have h1 : Cvert ∈ mty Cvert Ivert (0 + (0 % 1)) := by
    rw [vfull (0 + (0 % 1))]; exact cl_self Cvert
  exact h1

/-- `Cvert` recovered THROUGH the generator `satisfiable_of_persistPP`
    (not the hand-built kernel) — the generator fires on a real concept. -/
theorem cvert_via_generator : Satisfiable Cvert :=
  satisfiable_of_persistPP Ivert_rcc5 Cvert (Concept.atom 0)
    (fun r D h => Or.inl (cvert_demands r D h))
    ⟨trivial, by rw [vfull 0]; decide, by rw [vfull 0]; decide⟩
    (by rw [vfull 0]; exact cl_self Cvert)

/-! #### `vkernelG` fires: a chain carrying TWO `∃PP` arguments

`Clin = ∃PP.A₀ ⊓ ∃PP.A₁ ⊓ ∀PP.(∃PP.A₀ ⊓ ∃PP.A₁)` has two distinct
`∃PP` demands; a single self-carrying chain (both `A₀`, `A₁` on it)
serves both via `vkernelG_ok` — impossible for `vkernel_ok` (single
`G`).  Model: `A₀`, `A₁` both true everywhere on the ℕ-order. -/

def Ilin : Interp Nat := ⟨fun _ => True, chain, fun a _ => a = 0 ∨ a = 1⟩

theorem Ilin_rcc5 : RCC5Interp Ilin := frame_rcc5 chain chainFrame _

def Clin : Concept :=
  .and (.and (.ex pp (.atom 0)) (.ex pp (.atom 1)))
    (.all pp (.and (.ex pp (.atom 0)) (.ex pp (.atom 1))))

theorem lsat_all (n : Nat) : ∀ D ∈ cl Clin, sat Ilin n D := by
  have ha0 : ∀ m, sat Ilin m (Concept.atom 0) := fun _ => Or.inl rfl
  have ha1 : ∀ m, sat Ilin m (Concept.atom 1) := fun _ => Or.inr rfl
  have he0 : ∀ m, sat Ilin m (Concept.ex pp (Concept.atom 0)) :=
    fun m => ⟨m + 1, trivial, chain_lt (Nat.lt_succ_self m), ha0 _⟩
  have he1 : ∀ m, sat Ilin m (Concept.ex pp (Concept.atom 1)) :=
    fun m => ⟨m + 1, trivial, chain_lt (Nat.lt_succ_self m), ha1 _⟩
  have hal : ∀ m, sat Ilin m
      (Concept.all pp (Concept.and (Concept.ex pp (Concept.atom 0))
        (Concept.ex pp (Concept.atom 1)))) :=
    fun _ y _ _ => ⟨he0 y, he1 y⟩
  intro D hD
  simp only [Clin, cl, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false, or_assoc] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨he0 n, he1 n⟩, hal n⟩
  · exact ⟨he0 n, he1 n⟩
  · exact he0 n
  · exact ha0 n
  · exact he1 n
  · exact ha1 n
  · exact hal n
  · exact ⟨he0 n, he1 n⟩
  · exact he0 n
  · exact ha0 n
  · exact he1 n
  · exact ha1 n

open Classical in
theorem lfull (n : Nat) : mty Clin Ilin n = cl Clin := by
  unfold mty
  apply List.filter_eq_self.mpr
  intro D hD
  exact decide_eq_true (lsat_all n D hD)

/-- The self-carrying demand check: every `∃` in `cl Clin` is `∃PP.A₀`
    or `∃PP.A₁`. -/
def okDemandL (E : Concept) : Bool :=
  match E with
  | Concept.ex r D => decide (r = pp ∧ (D = Concept.atom 0 ∨ D = Concept.atom 1))
  | _ => true

theorem clin_demands_b : (cl Clin).all okDemandL = true := by decide

/-- `Clin` is satisfiable via `vkernelG_ok` — one chain, TWO arguments. -/
theorem clin_satisfiable : Satisfiable Clin := by
  have hok : MultiTierOk (vkernel Ilin Clin (fun n => n) 0 1) :=
    vkernelG_ok Ilin_rcc5 Clin (fun n => n) (fun _ => trivial)
      (fun n => chain_lt (Nat.lt_succ_self n)) Nat.one_pos
      ((lfull 0).trans (lfull (0 + 1)).symm)
      (fun a r D h => by
        have hb := List.all_eq_true.mp clin_demands_b (Concept.ex r D)
          (by rw [lfull (0 + a)] at h; exact h)
        simp only [okDemandL, decide_eq_true_eq] at hb
        exact Or.inl ⟨hb.1, 0, Nat.one_pos, by
          rw [lfull (0 + 0)]; rcases hb.2 with rfl | rfl <;> decide⟩)
  refine multiTier_sound (vkernel Ilin Clin (fun n => n) 0 1) hok
    (Sum.inr ((), 0)) Clin ?_
  have h1 : Clin ∈ mty Clin Ilin (0 + (0 % 1)) := by
    rw [lfull (0 + (0 % 1))]; exact cl_self Clin
  exact h1

/-- `Clin`'s existentials are all `∃PP` (hence `∃PP`/`∃EQ`). -/
theorem clin_dem : ∀ r D, Concept.ex r D ∈ cl Clin → r = pp ∨ r = eq := by
  intro r D h
  have hb := List.all_eq_true.mp clin_demands_b (Concept.ex r D) h
  simp only [okDemandL, decide_eq_true_eq] at hb
  exact Or.inl hb.1

/-- `Clin`'s `∃PP`-args are `A₀`/`A₁`. -/
theorem clin_dscov : ∀ D, Concept.ex pp D ∈ cl Clin →
    D ∈ [Concept.atom 0, Concept.atom 1] := by
  intro D h
  have hb := List.all_eq_true.mp clin_demands_b (Concept.ex pp D) h
  simp only [okDemandL, decide_eq_true_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact hb.2

/-- `Clin` forces both demands multi-persistent — its COMBINED guard
    `∀PP.(∃PP.A₀ ⊓ ∃PP.A₁)` yields each `sat x (∀PP.(∃PP.Aᵢ))` (the
    sat-based `persistAll` guard makes this fit; the mty-based one did
    not, since `∀PP.(∃PP.A₀) ∉ cl Clin`). -/
theorem clin_force {α : Type} (I : Interp α) (x : α) (_hI : RCC5Interp I)
    (hdom : I.dom x) (hsat : sat I x Clin) :
    persistAll I Clin [Concept.atom 0, Concept.atom 1] x := by
  obtain ⟨⟨he0, he1⟩, hcomb⟩ := hsat
  refine ⟨hdom, ?_⟩
  intro D hD
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl
  · exact ⟨mem_mty.mpr ⟨by decide, he0⟩, fun y hy hr => (hcomb y hy hr).1⟩
  · exact ⟨mem_mty.mpr ⟨by decide, he1⟩, fun y hy hr => (hcomb y hy hr).2⟩

/-- **`Clin`'s satisfiability is DECIDABLE via the round-robin procedure**
    — a COMBINED-guard concept, now fitting `decidableSat_vtowerRR` thanks
    to the sat-based `persistAll`. -/
def decidableSat_Clin_rr : Decidable (Satisfiable Clin) :=
  decidableSat_vtowerRR Clin [Concept.atom 0, Concept.atom 1] (by decide)
    clin_dem clin_dscov
    (fun I x hI hdom hsat => clin_force I x hI hdom hsat)

/-! #### The NESTING model: `kq_all` fires at a cross-`PP` edge

`nestNet` = two `ℕ`-order towers with the `false`-tower entirely
`PP`-BELOW the `true`-tower (cross `false→true = pp`, `true→false = ppi`).
Feeding it to `vkernel2_ok` (which reads the cross value off the model,
here `pp`, and fires `kq_all` via `hrectQ`) demonstrates the cross-`PP`
`kq_all` FIRING — the `∀pp`-across-the-nest propagation that the
`DR`-cross `cvert2` witness left vacuous.  Grounds §20.4: cross-`PP`
kernels are sound and covered by `vkernel2_ok`. -/

/-- `false`-tower `PP`-below `true`-tower; same-tower is the `chain`. -/
def nestNet : (Bool × Nat) → (Bool × Nat) → Atom :=
  fun p q => if p.1 = q.1 then chain p.2 q.2 else if p.1 = true then ppi else pp

theorem nestNet_same (b : Bool) (n m : Nat) : nestNet (b, n) (b, m) = chain n m := by
  show (if b = b then chain n m else _) = chain n m
  rw [if_pos rfl]

theorem nestNet_ft (n m : Nat) : nestNet (false, n) (true, m) = pp := rfl
theorem nestNet_tf (n m : Nat) : nestNet (true, n) (false, m) = ppi := rfl

theorem nestNet_frame : Frame nestNet where
  refl_eq := fun ⟨b, n⟩ => by rw [nestNet_same]; exact chain_self n
  eq_id := by
    rintro ⟨b, n⟩ ⟨b', m⟩ h
    cases b <;> cases b'
    · rw [nestNet_same] at h; have := chain_eq_imp h; subst this; rfl
    · rw [nestNet_ft] at h; exact absurd h (by decide)
    · rw [nestNet_tf] at h; exact absurd h (by decide)
    · rw [nestNet_same] at h; have := chain_eq_imp h; subst this; rfl
  conv_ := by
    rintro ⟨b, n⟩ ⟨b', m⟩
    cases b <;> cases b'
    · rw [nestNet_same, nestNet_same]; exact chain_conv n m
    · rw [nestNet_tf, nestNet_ft]; rfl
    · rw [nestNet_ft, nestNet_tf]; rfl
    · rw [nestNet_same, nestNet_same]; exact chain_conv n m
  comp_ := by
    rintro ⟨bx, nx⟩ ⟨by_, ny⟩ ⟨bz, nz⟩
    cases bx <;> cases by_ <;> cases bz
    · exact chain_cc nx ny nz
    · rw [nestNet_ft, nestNet_same, nestNet_ft]
      rcases chain_vals nx ny with h | h | h <;> rw [h] <;> decide
    · rw [nestNet_same, nestNet_ft, nestNet_tf]
      rcases chain_vals nx nz with h | h | h <;> rw [h] <;> decide
    · rw [nestNet_ft, nestNet_ft, nestNet_same]
      rcases chain_vals ny nz with h | h | h <;> rw [h] <;> decide
    · rw [nestNet_tf, nestNet_tf, nestNet_same]
      rcases chain_vals ny nz with h | h | h <;> rw [h] <;> decide
    · rw [nestNet_same, nestNet_tf, nestNet_ft]
      rcases chain_vals nx nz with h | h | h <;> rw [h] <;> decide
    · rw [nestNet_tf, nestNet_same, nestNet_tf]
      rcases chain_vals nx ny with h | h | h <;> rw [h] <;> decide
    · exact chain_cc nx ny nz

def Inest : Interp (Bool × Nat) := ⟨fun _ => True, nestNet, fun a _ => a = 0⟩

theorem Inest_rcc5 : RCC5Interp Inest := frame_rcc5 nestNet nestNet_frame _

theorem nsat_all (p : Bool × Nat) : ∀ D ∈ cl Cvert, sat Inest p D := by
  have ha : ∀ q : Bool × Nat, sat Inest q (Concept.atom 0) := fun _ => rfl
  have he : ∀ q : Bool × Nat, sat Inest q (Concept.ex pp (Concept.atom 0)) := by
    rintro ⟨b, n⟩
    exact ⟨(b, n + 1), trivial,
      (nestNet_same b n (n + 1)).trans (chain_lt (Nat.lt_succ_self n)), ha _⟩
  have hal : ∀ q : Bool × Nat,
      sat Inest q (Concept.all pp (Concept.ex pp (Concept.atom 0))) :=
    fun _ y _ _ => he y
  intro D hD
  simp only [Cvert, cl, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false, or_assoc] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨ha p, he p⟩, hal p⟩
  · exact ⟨ha p, he p⟩
  · exact ha p
  · exact he p
  · exact ha p
  · exact hal p
  · exact he p
  · exact ha p

open Classical in
theorem nfull (p : Bool × Nat) : mty Cvert Inest p = cl Cvert := by
  unfold mty
  apply List.filter_eq_self.mpr
  intro D hD
  exact decide_eq_true (nsat_all p D hD)

/-- `Cvert` via TWO kernels in the NESTING model — `vkernel2_ok` fires
    `kq_all` at the cross-`PP` edge (`∀pp.(∃pp.A)` propagates from the
    lower tower into the upper), NON-vacuous unlike the `DR`-cross
    `cvert2`.  Grounds §20: cross-`PP` kernels are sound + covered. -/
theorem cnest_satisfiable : Satisfiable Cvert := by
  have hok : MultiTierOk
      (vkernel2 Inest Cvert (fun b n => (b, n)) (fun _ => 0) (fun _ => 1)) :=
    vkernel2_ok Inest_rcc5 Cvert (Concept.atom 0) (fun b n => (b, n))
      (fun _ _ => trivial)
      (fun b n => (nestNet_same b n (n + 1)).trans (chain_lt (Nat.lt_succ_self n)))
      (fun _ => Nat.one_pos)
      (fun k => (nfull (k, 0)).trans (nfull (k, 0 + 1)).symm)
      (fun k => by show Concept.atom 0 ∈ mty Cvert Inest (k, 0);
                   rw [nfull (k, 0)]; decide)
      (by decide)
      (fun k k' hkk _ _ => by
        cases k <;> cases k'
        · exact absurd rfl hkk
        · rfl
        · rfl
        · exact absurd rfl hkk)
      (fun k a r D h =>
        Or.inl (cvert_demands r D (by rw [nfull (k, 0 + a)] at h; exact h)))
  refine multiTier_sound
    (vkernel2 Inest Cvert (fun b n => (b, n)) (fun _ => 0) (fun _ => 1)) hok
    (Sum.inr (true, 0)) Cvert ?_
  have h1 : Cvert ∈ mty Cvert Inest (true, 0 + (0 % 1)) := by
    rw [nfull (true, 0 + (0 % 1))]; exact cl_self Cvert
  exact h1

/-! ### The strong `posetKernel` witness: cross-`PP` FIRES WITH A ROOT

`rootNest` adds a root below the two nesting towers (`Unit ⊕ Bool × Nat`,
root `PP` below all, towers `= nestNet`).  Feeding it to `posetKernel_ok`
(`x₀ = root`, kernels `= the two towers`, cross `= PP`) proves that
lemma's hypotheses are jointly satisfiable AND exercises the new
capability: `kq_all` firing across the cross-`PP` kernel link over a root
— the full §21 shape (root + finite poset of kernels) at `N = 2`. -/

/-- Which side of the nesting a `nestNet` value lands on: never `dr`. -/
theorem nestNet_vals (p q : Bool × Nat) :
    nestNet p q = pp ∨ nestNet p q = ppi ∨ nestNet p q = eq := by
  unfold nestNet
  by_cases h : p.1 = q.1
  · rw [if_pos h]
    rcases chain_vals p.2 q.2 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)
    · exact Or.inr (Or.inl h1)
  · rw [if_neg h]
    by_cases h2 : p.1 = true
    · rw [if_pos h2]; exact Or.inr (Or.inl rfl)
    · rw [if_neg h2]; exact Or.inl rfl

/-- Root `PP`-below the two nesting towers. -/
def rootNest : (Unit ⊕ Bool × Nat) → (Unit ⊕ Bool × Nat) → Atom
  | .inl _, .inl _ => eq
  | .inl _, .inr _ => pp
  | .inr _, .inl _ => ppi
  | .inr p, .inr q => nestNet p q

theorem rootNest_frame : Frame rootNest := by
  have hn := nestNet_frame
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (⟨⟩ | p)
    · rfl
    · exact hn.refl_eq p
  · rintro (⟨⟩ | p) (⟨⟩ | q) h
    · rfl
    · exact absurd h (show pp ≠ eq by decide)
    · exact absurd h (show ppi ≠ eq by decide)
    · exact congrArg Sum.inr (hn.eq_id p q h)
  · rintro (⟨⟩ | p) (⟨⟩ | q)
    · rfl
    · rfl
    · rfl
    · exact hn.conv_ p q
  · rintro (⟨⟩ | px) (⟨⟩ | py) (⟨⟩ | pz)
    · show eq ∈ comp eq eq; decide
    · show pp ∈ comp eq pp; decide
    · show eq ∈ comp pp ppi; decide
    · show pp ∈ comp pp (nestNet py pz)
      rcases nestNet_vals py pz with h | h | h <;> rw [h] <;> decide
    · show ppi ∈ comp ppi eq; decide
    · show nestNet px pz ∈ comp ppi pp
      rcases nestNet_vals px pz with h | h | h <;> rw [h] <;> decide
    · show ppi ∈ comp (nestNet px py) ppi
      rcases nestNet_vals px py with h | h | h <;> rw [h] <;> decide
    · exact hn.comp_ px py pz

/-- The rooted-nesting model: `A = atom 0` everywhere, domain all. -/
def Irnest : Interp (Unit ⊕ Bool × Nat) := ⟨fun _ => True, rootNest, fun a _ => a = 0⟩

theorem Irnest_rcc5 : RCC5Interp Irnest := frame_rcc5 rootNest rootNest_frame _

theorem rnsat_all (x : Unit ⊕ Bool × Nat) : ∀ D ∈ cl Cvert, sat Irnest x D := by
  have ha : ∀ y, sat Irnest y (Concept.atom 0) := fun _ => rfl
  have he : ∀ y, sat Irnest y (Concept.ex pp (Concept.atom 0)) := by
    rintro (⟨⟩ | ⟨b, n⟩)
    · exact ⟨Sum.inr (false, 0), trivial, rfl, rfl⟩
    · exact ⟨Sum.inr (b, n + 1), trivial,
        (nestNet_same b n (n + 1)).trans (chain_lt (Nat.lt_succ_self n)), rfl⟩
  have hal : ∀ y, sat Irnest y (Concept.all pp (Concept.ex pp (Concept.atom 0))) :=
    fun _ z _ _ => he z
  intro D hD
  simp only [Cvert, cl, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false, or_assoc] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨ha x, he x⟩, hal x⟩
  · exact ⟨ha x, he x⟩
  · exact ha x
  · exact he x
  · exact ha x
  · exact hal x
  · exact he x
  · exact ha x

open Classical in
theorem rnfull (x : Unit ⊕ Bool × Nat) : mty Cvert Irnest x = cl Cvert := by
  unfold mty
  apply List.filter_eq_self.mpr
  intro D hD
  exact decide_eq_true (rnsat_all x D hD)

/-- `Cvert` via the POSET multi-kernel — root `PP`-below two cross-`PP`
    kernels, `kq_all` firing over the root.  Non-vacuity for
    `posetKernel_ok` at `N = 2`. -/
theorem crnest_satisfiable : Satisfiable Cvert := by
  have hok : MultiTierOk (posetKernel Irnest Cvert (Sum.inl ())
      (fun b n => Sum.inr (b, n)) (fun _ => 0) (fun _ => 1)) :=
    posetKernel_ok Irnest_rcc5 Cvert (Sum.inl ()) trivial
      (fun b n => Sum.inr (b, n))
      (fun _ _ => trivial)
      (fun b n => (nestNet_same b n (n + 1)).trans (chain_lt (Nat.lt_succ_self n)))
      (fun _ => Nat.one_pos)
      (fun b => (rnfull (Sum.inr (b, 0))).trans (rnfull (Sum.inr (b, 0 + 1))).symm)
      (fun _ _ => rfl)
      (fun _ => by simp)
      (fun b b' h => by simp only [Sum.inr.injEq, Prod.mk.injEq] at h; exact h.1)
      (fun b b' hbb a c => by
        show nestNet (b, 0 + a) (b', 0 + c) = nestNet (b, 0) (b', 0)
        cases b <;> cases b' <;> first | exact absurd rfl hbb | rfl)
      (fun _ => Concept.atom 0)
      (fun b => by rw [rnfull (Sum.inr (b, 0))]; decide)
      (fun b a r D h =>
        Or.inl (cvert_demands r D (by rw [rnfull (Sum.inr (b, 0 + a))] at h; exact h)))
      (fun r D h => by
        have hd := cvert_demands r D (by rw [rnfull (Sum.inl ())] at h; exact h)
        exact Or.inl ⟨hd.1, false, hd.2⟩)
  refine multiTier_sound (posetKernel Irnest Cvert (Sum.inl ())
    (fun b n => Sum.inr (b, n)) (fun _ => 0) (fun _ => 1)) hok
    (Sum.inl ()) Cvert ?_
  show Cvert ∈ mty Cvert Irnest (Sum.inl ())
  rw [rnfull (Sum.inl ())]; exact cl_self Cvert

/-! ### `Ccar`: a genuinely MULTI-`∃PP`-demand CO-CARRYING concept

`Ccar = ∃PP.A₀ ⊓ ∃PP.A₁ ⊓ ∀PP.A₀ ⊓ ∀PP.A₁ ⊓ ∀PP.(∃PP.A₀) ⊓ ∀PP.(∃PP.A₁)`
has TWO distinct `∃PP` demands (`A₀ = atom 0`, `A₁ = atom 1`) whose ATOMS
are force-carried (`∀PP.A₀`/`∀PP.A₁`), so ONE self-carrying chain serves
both.  Distinct from the pre-existing `Clin` (which forces only the
demands' recurrence, not the atoms).  Beyond `decidableSat_vtower` (single
fixed `G`); the non-vacuity witness for `decidableSat_vtowerG`. -/

/-- `Ccar` — two distinct persistent `∃PP` demands + their co-carrying
    atom-universals. -/
def Ccar : Concept :=
  .and (.and (.and (.and (.and
    (.ex pp (.atom 0)) (.ex pp (.atom 1)))
    (.all pp (.atom 0))) (.all pp (.atom 1)))
    (.all pp (.ex pp (.atom 0)))) (.all pp (.ex pp (.atom 1)))

/-- Every existential in `cl Ccar` is `∃PP`/`∃EQ` (in fact all `∃PP`). -/
def ccarDem (E : Concept) : Bool :=
  match E with
  | Concept.ex r _ => decide (r = pp ∨ r = eq)
  | _ => true

theorem ccar_dem_b : (cl Ccar).all ccarDem = true := by decide

theorem ccar_dem : ∀ r D, Concept.ex r D ∈ cl Ccar → r = pp ∨ r = eq := by
  intro r D h
  have hb := List.all_eq_true.mp ccar_dem_b (Concept.ex r D) h
  simpa only [ccarDem, decide_eq_true_eq] using hb

/-- Every `∃`-argument in `cl Ccar` is `A₀` or `A₁`. -/
def ccarArg (E : Concept) : Bool :=
  match E with
  | Concept.ex _ D => decide (D = Concept.atom 0 ∨ D = Concept.atom 1)
  | _ => true

theorem ccar_arg_b : (cl Ccar).all ccarArg = true := by decide

theorem ccar_arg : ∀ D, Concept.ex pp D ∈ cl Ccar →
    D = Concept.atom 0 ∨ D = Concept.atom 1 := by
  intro D h
  have hb := List.all_eq_true.mp ccar_arg_b (Concept.ex pp D) h
  simpa only [ccarArg, decide_eq_true_eq] using hb

/-- `Ccar` forces a persistent `∃PP.A₀` chain AND co-carrying (every
    `∃PP`-arg's `∀PP` holds) in every model — from its six conjuncts. -/
theorem ccar_force {α : Type} (I : Interp α) (x : α) (_hI : RCC5Interp I)
    (hdom : I.dom x) (hsat : sat I x Ccar) :
    persistPP I Ccar (Concept.atom 0) x ∧
      (∀ D, Concept.ex pp D ∈ cl Ccar → sat I x (Concept.all pp D)) := by
  obtain ⟨⟨⟨⟨⟨he0, _he1⟩, ha0u⟩, ha1u⟩, hae0⟩, _hae1⟩ := hsat
  refine ⟨⟨hdom, mem_mty.mpr ⟨by decide, he0⟩, mem_mty.mpr ⟨by decide, hae0⟩⟩, ?_⟩
  intro D hD
  rcases ccar_arg D hD with rfl | rfl
  · exact ha0u
  · exact ha1u

/-- **`Ccar`'s satisfiability is DECIDABLE via the self-carrying procedure**
    — the non-vacuity witness for `decidableSat_vtowerG`, a concept with
    TWO distinct `∃PP` demands that `decidableSat_vtower` cannot express. -/
def decidableSat_Ccar : Decidable (Satisfiable Ccar) :=
  decidableSat_vtowerG Ccar (Concept.atom 0) ccar_dem
    (fun I x hI hdom hsat => ccar_force I x hI hdom hsat)

/-- `Ccar` IS satisfiable: the ℕ-chain `Ilin` with both `A₀` and `A₁` true
    everywhere — every rung carries both demand-args, unbounded above. -/
theorem ccar_satisfiable : Satisfiable Ccar := by
  have ha0 : ∀ n, sat Ilin n (Concept.atom 0) := fun _ => Or.inl rfl
  have ha1 : ∀ n, sat Ilin n (Concept.atom 1) := fun _ => Or.inr rfl
  have he0 : ∀ n, sat Ilin n (Concept.ex pp (Concept.atom 0)) :=
    fun n => ⟨n + 1, trivial, chain_lt (Nat.lt_succ_self n), ha0 (n + 1)⟩
  have he1 : ∀ n, sat Ilin n (Concept.ex pp (Concept.atom 1)) :=
    fun n => ⟨n + 1, trivial, chain_lt (Nat.lt_succ_self n), ha1 (n + 1)⟩
  exact ⟨Nat, Ilin, Ilin_rcc5, 0, trivial,
    ⟨⟨⟨⟨⟨he0 0, he1 0⟩, fun y _ _ => ha0 y⟩, fun y _ _ => ha1 y⟩,
      fun y _ _ => he0 y⟩, fun y _ _ => he1 y⟩⟩

/-! ### `Calt`: a genuinely NON-CO-CARRYING round-robin witness

`Calt = ∃PP.A₀ ⊓ ∃PP.¬A₀ ⊓ ∀PP.(∃PP.A₀) ⊓ ∀PP.(∃PP.¬A₀)` demands both an
`A₀`-witness and a `¬A₀`-witness above every point — NO single point can
carry both, so it is beyond `decidableSat_vtowerG` (co-carrying); it is
decided by `decidableSat_vtowerRR` (round-robin: `A₀`, `¬A₀` served on
alternating rungs). -/

/-- `Calt` — two INCOMPATIBLE persistent `∃PP` demands (`A₀`, `¬A₀`). -/
def Calt : Concept :=
  .and (.and (.and (.ex pp (.atom 0)) (.ex pp (.natom 0)))
    (.all pp (.ex pp (.atom 0)))) (.all pp (.ex pp (.natom 0)))

def caltDem (E : Concept) : Bool :=
  match E with
  | Concept.ex r _ => decide (r = pp ∨ r = eq)
  | _ => true

theorem calt_dem_b : (cl Calt).all caltDem = true := by decide

theorem calt_dem : ∀ r D, Concept.ex r D ∈ cl Calt → r = pp ∨ r = eq := by
  intro r D h
  have hb := List.all_eq_true.mp calt_dem_b (Concept.ex r D) h
  simpa only [caltDem, decide_eq_true_eq] using hb

def caltArg (E : Concept) : Bool :=
  match E with
  | Concept.ex _ D => decide (D = Concept.atom 0 ∨ D = Concept.natom 0)
  | _ => true

theorem calt_arg_b : (cl Calt).all caltArg = true := by decide

theorem calt_dscov : ∀ D, Concept.ex pp D ∈ cl Calt →
    D ∈ [Concept.atom 0, Concept.natom 0] := by
  intro D h
  have hb := List.all_eq_true.mp calt_arg_b (Concept.ex pp D) h
  simp only [caltArg, decide_eq_true_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact hb

/-- `Calt` forces both demands multi-persistent at every model point. -/
theorem calt_force {α : Type} (I : Interp α) (x : α) (_hI : RCC5Interp I)
    (hdom : I.dom x) (hsat : sat I x Calt) :
    persistAll I Calt [Concept.atom 0, Concept.natom 0] x := by
  obtain ⟨⟨⟨he0, he1⟩, hae0⟩, hae1⟩ := hsat
  refine ⟨hdom, ?_⟩
  intro D hD
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl
  · exact ⟨mem_mty.mpr ⟨by decide, he0⟩, hae0⟩
  · exact ⟨mem_mty.mpr ⟨by decide, he1⟩, hae1⟩

/-- **`Calt`'s satisfiability is DECIDABLE via the round-robin procedure**
    — the non-vacuity witness for `decidableSat_vtowerRR`: two INCOMPATIBLE
    `∃PP` demands, impossible to co-carry, served on alternating rungs. -/
def decidableSat_Calt : Decidable (Satisfiable Calt) :=
  decidableSat_vtowerRR Calt [Concept.atom 0, Concept.natom 0] (by decide)
    calt_dem calt_dscov
    (fun I x hI hdom hsat => calt_force I x hI hdom hsat)

/-- `Calt` IS satisfiable: the ℕ-chain `Ialt` with `A₀` at EVEN points
    only — every point has both an even (`A₀`) and an odd (`¬A₀`) witness
    above, but NO point carries both. -/
def Ialt : Interp Nat := ⟨fun _ => True, chain, fun a n => a = 0 ∧ n % 2 = 0⟩

theorem Ialt_rcc5 : RCC5Interp Ialt := frame_rcc5 chain chainFrame _

theorem calt_satisfiable : Satisfiable Calt := by
  have he0 : ∀ n, sat Ialt n (Concept.ex pp (Concept.atom 0)) :=
    fun n => ⟨2 * n + 2, trivial, chain_lt (by omega), ⟨rfl, by omega⟩⟩
  have he1 : ∀ n, sat Ialt n (Concept.ex pp (Concept.natom 0)) :=
    fun n => ⟨2 * n + 1, trivial, chain_lt (by omega),
      fun h => by obtain ⟨_, h2⟩ := h; omega⟩
  exact ⟨Nat, Ialt, Ialt_rcc5, 0, trivial,
    ⟨⟨⟨he0 0, he1 0⟩, fun y _ _ => he0 y⟩, fun y _ _ => he1 y⟩⟩

/-! ### A NON-TRIVIAL-skeleton merge witness: `Cmerge`

The clean-tower carrier `cleanRho` on `ℕ ⊕ Unit`: the ascending `PP`-tower
(`inl`) plus a leaf `nb = inr ()` that is `DR` to the ROOT `inl 0` but `PO` to
every tower phase `inl (j+1)`.  So the root has a genuine horizontal `∃DR.B`
demand (served by `nb`, a second skeleton node), while the tower stays
horizontally CLEAN: a phase's only neighbour off the chain is `nb` at `PO`, and
`∃PO.B ∉ cl Cmerge`, so phases demand only the self-carrying `∃PP.A`.  `nb`
itself has no `PP`-neighbour (so it never inherits `∃PP`) and its sole
`DR`-neighbour is the root (carrying `A`, not `B`), so it has no `cl Cmerge`
demand at all.  This is the first extraction through `extract_mtkKernel` with a
NON-DEGENERATE horizontal skeleton `{root, nb}`. -/

/-- The clean-tower relation: chain on the tower; `DR` root↔leaf, `PO`
    phase↔leaf. -/
def cleanRho : (Nat ⊕ Unit) → (Nat ⊕ Unit) → Atom
  | .inl i, .inl j => chain i j
  | .inl 0, .inr _ => dr
  | .inl (_ + 1), .inr _ => po
  | .inr _, .inl 0 => dr
  | .inr _, .inl (_ + 1) => po
  | .inr _, .inr _ => eq

theorem cleanRho_frame : Frame cleanRho where
  refl_eq := by
    rintro (i | ⟨⟩)
    · exact chain_self i
    · rfl
  eq_id := by
    rintro (a | ⟨⟩) (b | ⟨⟩) h
    · exact congrArg Sum.inl (chain_eq_imp h)
    · cases a <;> simp only [cleanRho] at h <;> exact absurd h (by decide)
    · cases b <;> simp only [cleanRho] at h <;> exact absurd h (by decide)
    · rfl
  conv_ := by
    rintro (a | ⟨⟩) (b | ⟨⟩)
    · exact chain_conv a b
    · cases a <;> rfl
    · cases b <;> rfl
    · rfl
  comp_ := by
    rintro (i | ⟨⟩) (j | ⟨⟩) (k | ⟨⟩)
    · exact chainFrame.comp_ i j k
    · cases i with
      | zero => cases j with
        | zero => simp only [cleanRho]; decide
        | succ j' => simp only [cleanRho]; rw [chain_lt (Nat.succ_pos j')]; decide
      | succ i' => cases j with
        | zero => simp only [cleanRho]; rw [chain_gt (Nat.succ_pos i')]; decide
        | succ j' => simp only [cleanRho]
                     rcases chain_vals (i' + 1) (j' + 1) with h | h | h <;> rw [h] <;> decide
    · cases i with
      | zero => cases k with
        | zero => simp only [cleanRho]; decide
        | succ k' => simp only [cleanRho]; rw [chain_lt (Nat.succ_pos k')]; decide
      | succ i' => cases k with
        | zero => simp only [cleanRho]; rw [chain_gt (Nat.succ_pos i')]; decide
        | succ k' => simp only [cleanRho]
                     rcases chain_vals (i' + 1) (k' + 1) with h | h | h <;> rw [h] <;> decide
    · cases i <;> simp only [cleanRho] <;> decide
    · cases j with
      | zero => cases k with
        | zero => simp only [cleanRho]; decide
        | succ k' => simp only [cleanRho]; rw [chain_lt (Nat.succ_pos k')]; decide
      | succ j' => cases k with
        | zero => simp only [cleanRho]; rw [chain_gt (Nat.succ_pos j')]; decide
        | succ k' => simp only [cleanRho]
                     rcases chain_vals (j' + 1) (k' + 1) with h | h | h <;> rw [h] <;> decide
    · cases j <;> simp only [cleanRho] <;> decide
    · cases k <;> simp only [cleanRho] <;> decide
    · simp only [cleanRho]; decide

/-- The clean-tower model: `A₀` at every tower point, `B = A₁` at the leaf. -/
def Imerge : Interp (Nat ⊕ Unit) :=
  ⟨fun _ => True, cleanRho, fun a x => match x with | .inl _ => a = 0 | .inr _ => a = 1⟩

theorem Imerge_rcc5 : RCC5Interp Imerge := frame_rcc5 cleanRho cleanRho_frame _

/-- The non-trivial-skeleton merge concept: a horizontal `∃DR.B` demand AND a
    vertical `∃PP.A` tower, both at the root. -/
def Cmerge : Concept :=
  .and (.and (.and (.atom 0) (.ex dr (.atom 1))) (.ex pp (.atom 0)))
    (.all pp (.ex pp (.atom 0)))

theorem Cmerge_pofree : POFree Cmerge :=
  ⟨⟨⟨trivial, trivial⟩, trivial⟩, by decide, trivial⟩

/-- `Cmerge`'s existentials are exactly `∃DR.A₁` (horizontal) and `∃PP.A₀`
    (vertical). -/
theorem cmerge_demands : ∀ r D, Concept.ex r D ∈ cl Cmerge →
    (r = dr ∧ D = Concept.atom 1) ∨ (r = pp ∧ D = Concept.atom 0) := by
  intro r D h
  have hb := List.all_eq_true.mp
    (show (cl Cmerge).all (fun E => match E with
      | Concept.ex r D => decide ((r = dr ∧ D = Concept.atom 1) ∨
          (r = pp ∧ D = Concept.atom 0))
      | _ => true) = true from by decide) (Concept.ex r D) h
  simpa only [decide_eq_true_eq] using hb

/-- In `Imerge` a `DR` edge always has an endpoint at the leaf `nb = inr ()`
    (chain edges are never `DR`; the leaf is `PO`, not `DR`, to every phase). -/
theorem cleanRho_dr_lemma : ∀ (a b : Nat ⊕ Unit), Imerge.rho a b = dr →
    b = Sum.inr () ∨ a = Sum.inr () := by
  rintro (i | ⟨⟩) (j | ⟨⟩) h
  · exfalso
    rw [show Imerge.rho (Sum.inl i) (Sum.inl j) = chain i j from rfl] at h
    rcases chain_vals i j with h' | h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The leaf `nb` satisfies NO existential of `Cmerge`: its only `DR`-neighbour
    is the root (carrying `A₀`, not `A₁`), and it has no `PP`-neighbour. -/
theorem nb_merge_no_ex : ∀ r D, Concept.ex r D ∉ mty Cmerge Imerge (Sum.inr ()) := by
  intro r D hmem
  obtain ⟨y, _, hr, hy⟩ := mty_ex hmem
  rcases cmerge_demands r D (mty_sub _ hmem) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases y with j | ⟨⟩
    · cases j with
      | zero =>
        have h2 := (mem_mty.mp hy).2; change (1 : Nat) = 0 at h2
        exact absurd h2 (by decide)
      | succ j' => change po = dr at hr; exact absurd hr (by decide)
    · change eq = dr at hr; exact absurd hr (by decide)
  · rcases y with j | ⟨⟩
    · cases j with
      | zero => change dr = pp at hr; exact absurd hr (by decide)
      | succ j' => change po = pp at hr; exact absurd hr (by decide)
    · change eq = pp at hr; exact absurd hr (by decide)

/-- A tower phase `inl (n+1)` has NO `DR`-successor (its off-chain neighbour is
    the leaf, at `PO`). -/
theorem cmerge_pos_dr_none : ∀ (n : Nat), 0 < n → ∀ (y : Nat ⊕ Unit),
    Imerge.rho (Sum.inl n) y ≠ dr := by
  intro n hn y hr
  cases n with
  | zero => omega
  | succ n' =>
    rcases y with j | ⟨⟩
    · rw [show Imerge.rho (Sum.inl (n' + 1)) (Sum.inl j) = chain (n' + 1) j from rfl] at hr
      rcases chain_vals (n' + 1) j with h | h | h <;> rw [h] at hr <;> exact absurd hr (by decide)
    · rw [show Imerge.rho (Sum.inl (n' + 1)) (Sum.inr ()) = po from rfl] at hr
      exact absurd hr (by decide)

/-- **The `Cmerge` coverage skeleton is `{n} ∪ {nb}`.**  Every node in
    `mtkNodesH n` is either `n` or the leaf `inr ()`: a chain node's only
    non-vertical demand is `∃DR.A₁` (served by `nb`, `cleanRho_dr_lemma`), and
    `nb` has no demand (`nb_merge_no_ex`).  The NON-DEGENERATE analogue of
    `cvert_nodes_singleton`. -/
theorem cmerge_nodes :
    ∀ (n : MTKNode Imerge Cmerge), ∀ m ∈ mtkNodesH n, m = n ∨ m.x = Sum.inr () := by
  intro n
  induction n using mtkNodesH.induct with
  | _ x ih =>
    intro m hm
    rw [mtkNodesH] at hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact Or.inl rfl
    · obtain ⟨⟨F, hF⟩, _, hmm⟩ := List.mem_flatMap.mp hm'
      cases F with
      | ex r c =>
        have hmm2 : m ∈ (if r = pp ∨ r = ppi then ([] : List (MTKNode Imerge Cmerge))
            else mtkNodesH (mtkWitness x hF)) := hmm
        by_cases hv : r = pp ∨ r = ppi
        · rw [if_pos hv] at hmm2; exact absurd hmm2 List.not_mem_nil
        · rw [if_neg hv] at hmm2
          have hwit : (mtkWitness x hF).x = Sum.inr () := by
            have hrho : Imerge.rho x.x (mtkWitness x hF).x = r := mtkWitness_rho x hF
            have hmty : Concept.ex r c ∈ mty Cmerge Imerge x.x := (mem_mtk.mp hF).1
            have hr_dr : r = dr := by
              rcases cmerge_demands r c (mty_sub _ hmty) with ⟨rfl, _⟩ | ⟨rfl, _⟩
              · rfl
              · exact absurd (Or.inl rfl) hv
            rcases cleanRho_dr_lemma x.x (mtkWitness x hF).x (hrho.trans hr_dr) with hb | ha
            · exact hb
            · exact absurd (ha ▸ hmty) (nb_merge_no_ex r c)
          rcases ih r c hF m hmm2 with hmw | hmr
          · rw [hmw]; exact Or.inr hwit
          · exact Or.inr hmr
      | top => exact absurd hmm List.not_mem_nil
      | bot => exact absurd hmm List.not_mem_nil
      | atom a => exact absurd hmm List.not_mem_nil
      | natom a => exact absurd hmm List.not_mem_nil
      | and a b => exact absurd hmm List.not_mem_nil
      | or a b => exact absurd hmm List.not_mem_nil
      | all r c => exact absurd hmm List.not_mem_nil

/-- The root node: point `inl 0`, budget `mdepth Cmerge`. -/
def cmergeRoot : MTKNode Imerge Cmerge := ⟨Sum.inl 0, mdepth Cmerge, trivial⟩

/-- `A₀` sits in every tower point's `mtk` label at the root budget. -/
theorem cmerge_atom0_mtk (n : Nat) :
    Concept.atom 0 ∈ mtk Cmerge Imerge (Sum.inl n) cmergeRoot.k :=
  mem_mtk.mpr ⟨mem_mty.mpr ⟨by decide, rfl⟩, Nat.zero_le _⟩

/-- The root `inl 0` satisfies `Cmerge`. -/
theorem cmerge_sat_root : sat Imerge (Sum.inl 0) Cmerge := by
  refine ⟨⟨⟨rfl, ⟨Sum.inr (), trivial, rfl, rfl⟩⟩,
    ⟨Sum.inl 1, trivial, ?_, rfl⟩⟩, ?_⟩
  · show chain 0 1 = pp; exact chain_lt (by omega)
  · rintro (j | ⟨⟩) _ hr
    · refine ⟨Sum.inl (j + 1), trivial, ?_, rfl⟩
      show chain j (j + 1) = pp; exact chain_lt (Nat.lt_succ_self j)
    · change dr = pp at hr; exact absurd hr (by decide)

open Classical in
/-- **`Cmerge` extracts through the GENERIC merged engine with a NON-DEGENERATE
    skeleton** — the completeness (extraction) direction on a concept whose
    horizontal skeleton `{root, nb}` genuinely fires (root's `∃DR.A₁` served by
    the second skeleton node), merged with the self-carrying `∃PP.A₀` tower.
    `hpp_v0` = `cmerge_nodes` + `nb_merge_no_ex` (only the root carries `∃PP`);
    `hk_class` = `cmerge_demands` + `cmerge_pos_dr_none` (a phase's `∃DR.A₁` is
    unsatisfiable — no `DR`-successor — so phases demand only `∃PP.A₀`);
    `hno_ppi` = `no_ppi_demand`.  Unlike `Cvert` (singleton skeleton) this
    exercises the horizontal routing merged with the kernel. -/
theorem cmerge_generic_satisfiable : Satisfiable Cmerge := by
  have hnoppi : ∀ D, Concept.ex ppi D ∉ cl Cmerge := fun D h => by
    rcases cmerge_demands ppi D h with ⟨h', _⟩ | ⟨h', _⟩ <;> exact absurd h' (by decide)
  obtain ⟨i, p, hLi, hp, _, hty⟩ :=
    mty_segment_bounded (I := Imerge) Cmerge (fun n => Sum.inl n) 1
  have hok : MultiTierOk (mtkKernel Imerge Cmerge
      (fun e : {n // n ∈ mtkNodesH cmergeRoot} => e.val.x) (fun e => e.val.k)
      (fun e f => decide (sAdjK e.val f.val))
      ⟨cmergeRoot, self_mem_mtkNodesH cmergeRoot⟩ (fun n => Sum.inl n) i p) := by
    refine extract_mtkKernel Imerge_rcc5 Cmerge_pofree cmergeRoot (fun n => Sum.inl n)
      (fun _ => trivial) (fun n => chain_lt (Nat.lt_succ_self n)) i p hp hty ?_ ?_ ?_ ?_
    · intro a; show chain 0 (i + a) = pp; exact chain_lt (by omega)
    · intro e D hdem
      rcases cmerge_nodes cmergeRoot e.val e.property with he | hinr
      · have hmty : Concept.ex pp D ∈ mty Cmerge Imerge e.val.x := (mem_mtk.mp hdem).1
        have hD : D = Concept.atom 0 := by
          rcases cmerge_demands pp D (mty_sub _ hmty) with ⟨h', _⟩ | ⟨_, h'⟩
          · exact absurd h' (by decide)
          · exact h'
        subst hD
        exact ⟨Subtype.ext he, 0, hp, cmerge_atom0_mtk (i + 0)⟩
      · exact absurd ((mem_mtk.mp hdem).1) (hinr ▸ nb_merge_no_ex pp D)
    · exact no_ppi_demand cmergeRoot hnoppi
    · intro a r D hmem
      have hmty : Concept.ex r D ∈ mty Cmerge Imerge (Sum.inl (i + a)) := (mem_mtk.mp hmem).1
      rcases cmerge_demands r D (mty_sub _ hmty) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨y, _, hr, _⟩ := mty_ex hmty
        exact absurd hr (cmerge_pos_dr_none (i + a) (by omega) y)
      · exact Or.inr (Or.inl ⟨rfl, 0, hp, cmerge_atom0_mtk (i + 0)⟩)
  exact multiTier_sound _ hok (Sum.inl ⟨cmergeRoot, self_mem_mtkNodesH cmergeRoot⟩)
    Cmerge (mem_mtk.mpr ⟨mem_mty.mpr ⟨cl_self Cmerge, cmerge_sat_root⟩, Nat.le_refl _⟩)

open Classical in
/-- **`Cmerge` through the GENERAL `extract_from_tower`** — the general mixed
    extraction fires on the NON-DEGENERATE clean-phase class (root `∃DR.A₁`
    served by the skeleton node `nb`; phases demand only the tower `∃PP.A₀`).
    The middle of the three witness classes spanned by the one general theorem. -/
theorem cmerge_via_tower : Satisfiable Cmerge := by
  obtain ⟨i, p, hLi, hp, _, hty⟩ :=
    mty_segment_bounded (I := Imerge) Cmerge (fun n => Sum.inl n) 1
  refine extract_from_tower Imerge_rcc5 Cmerge_pofree (fun n => Sum.inl n)
    (fun _ => trivial) (fun n => chain_lt (Nat.lt_succ_self n))
    (mem_mty.mpr ⟨cl_self Cmerge, cmerge_sat_root⟩)
    (fun D h => by
      rcases cmerge_demands ppi D h with ⟨h', _⟩ | ⟨h', _⟩ <;> exact absurd h' (by decide))
    i p (by omega) hp hty ?_ ?_
  · intro e D hdem
    rcases cmerge_nodes _ e.val e.property with he | hinr
    · have hmty : Concept.ex pp D ∈ mty Cmerge Imerge e.val.x := (mem_mtk.mp hdem).1
      have hD : D = Concept.atom 0 := by
        rcases cmerge_demands pp D (mty_sub _ hmty) with ⟨h', _⟩ | ⟨_, h'⟩
        · exact absurd h' (by decide)
        · exact h'
      subst hD
      exact ⟨Subtype.ext he, 0, hp, cmerge_atom0_mtk (i + 0)⟩
    · exact absurd ((mem_mtk.mp hdem).1) (hinr ▸ nb_merge_no_ex pp D)
  · intro a r D hmem
    have hmty : Concept.ex r D ∈ mty Cmerge Imerge (Sum.inl (i + a)) := (mem_mtk.mp hmem).1
    rcases cmerge_demands r D (mty_sub _ hmty) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨y, _, hr, _⟩ := mty_ex hmty
      exact absurd hr (cmerge_pos_dr_none (i + a) (by omega) y)
    · exact Or.inr (Or.inl ⟨rfl, 0, hp, cmerge_atom0_mtk (i + 0)⟩)

/-! ### A NESTED TWO-TOWER witness `Cnest`, through the MULTI-kernel engine

`Cnest = Cvert ⊓ ∃PO.Cvert` on the all-cross-`PO` two-region carrier
`Bool × ℕ`: within a region the ascending `PP`-chain, across regions `PO`.
Each region's base carries its OWN `∃PP.A` tower — so `Cnest` needs TWO
kernels (`κ = Bool`), the first genuinely multi-kernel extraction.  The
cross-tower `∃PO.Cvert` demand routes to the OTHER region's base via the `PO`
`K`-edge (`mtk_k_ex` route-1) — no `∃DR` summit.  Validates `mtkKernels_ok`
end-to-end, as `cmix` did for the single kernel. -/

/-- All-cross-`PO` two-region relation: within a region the chain, across `PO`. -/
def nestRho : (Bool × Nat) → (Bool × Nat) → Atom
  | (b, i), (b', j) => if b = b' then chain i j else po

theorem nestRho_frame : Frame nestRho where
  refl_eq := by rintro ⟨b, i⟩; show (if b = b then chain i i else po) = eq
                rw [if_pos rfl]; exact chain_self i
  eq_id := by
    rintro ⟨b, i⟩ ⟨b', j⟩ h
    show (⟨b, i⟩ : Bool × Nat) = ⟨b', j⟩
    by_cases hb : b = b'
    · have h' : chain i j = eq := by
        have : (if b = b' then chain i j else po) = eq := h
        rwa [if_pos hb] at this
      subst hb; rw [chain_eq_imp h']
    · have : (if b = b' then chain i j else po) = eq := h
      rw [if_neg hb] at this; exact absurd this (by decide)
  conv_ := by
    rintro ⟨b, i⟩ ⟨b', j⟩
    show (if b' = b then chain j i else po) = conv (if b = b' then chain i j else po)
    by_cases hb : b = b'
    · rw [if_pos hb, if_pos hb.symm]; exact chain_conv i j
    · rw [if_neg hb, if_neg (fun h => hb h.symm)]; rfl
  comp_ := by
    rintro ⟨b, i⟩ ⟨b', j⟩ ⟨b'', k⟩
    show (if b = b'' then chain i k else po)
      ∈ comp (if b = b' then chain i j else po) (if b' = b'' then chain j k else po)
    by_cases hbb' : b = b' <;> by_cases hb'b'' : b' = b''
    · subst hbb'; subst hb'b''; rw [if_pos rfl, if_pos rfl, if_pos rfl]
      exact chainFrame.comp_ i j k
    · rw [if_pos hbb', if_neg hb'b'', if_neg (hbb' ▸ hb'b'')]
      exact po_mem_comp_right _
    · rw [if_neg hbb', if_pos hb'b'', if_neg (fun h => hbb' (h.trans hb'b''.symm))]
      exact po_mem_comp_left _
    · by_cases hbb'' : b = b''
      · rw [if_pos hbb'', if_neg hbb', if_neg hb'b'']; exact mem_comp_po_po _
      · rw [if_neg hbb'', if_neg hbb', if_neg hb'b'']; exact mem_comp_po_po _

/-- The all-cross-`PO` model: `A₀` at every point. -/
def Ipo : Interp (Bool × Nat) := ⟨fun _ => True, nestRho, fun a _ => a = 0⟩

theorem Ipo_rcc5 : RCC5Interp Ipo := frame_rcc5 nestRho nestRho_frame _

/-- `Cnest = Cvert ⊓ ∃PO.Cvert`. -/
def Cnest : Concept := .and Cvert (.ex po Cvert)

theorem Cnest_pofree : POFree Cnest := ⟨Cvert_pofree, Cvert_pofree⟩

/-- `A₀` at every `Ipo` point. -/
theorem po_ha : ∀ q : Bool × Nat, sat Ipo q (Concept.atom 0) := fun _ => rfl

/-- `∃PP.A₀` at every point (same-region successor). -/
theorem po_he : ∀ q : Bool × Nat, sat Ipo q (Concept.ex pp (Concept.atom 0)) := by
  rintro ⟨b, n⟩
  refine ⟨(b, n + 1), trivial, ?_, rfl⟩
  show (if b = b then chain n (n + 1) else po) = pp
  rw [if_pos rfl]; exact chain_lt (Nat.lt_succ_self n)

/-- `∀PP.(∃PP.A₀)` at every point. -/
theorem po_hal : ∀ q : Bool × Nat,
    sat Ipo q (Concept.all pp (Concept.ex pp (Concept.atom 0))) :=
  fun _ y _ _ => po_he y

/-- `Cvert` at every `Ipo` point. -/
theorem po_hcv : ∀ q : Bool × Nat, sat Ipo q Cvert :=
  fun q => ⟨⟨po_ha q, po_he q⟩, po_hal q⟩

/-- `∃PO.Cvert` at every point (the OTHER region's base). -/
theorem po_hpo : ∀ q : Bool × Nat, sat Ipo q (Concept.ex po Cvert) := by
  rintro ⟨b, n⟩
  refine ⟨(!b, 0), trivial, ?_, po_hcv (!b, 0)⟩
  show (if b = !b then chain n 0 else po) = po
  rw [if_neg (by cases b <;> decide)]

/-- `Cnest` at every point. -/
theorem po_hcn : ∀ q : Bool × Nat, sat Ipo q Cnest :=
  fun q => ⟨po_hcv q, po_hpo q⟩

/-- Everything in `cl Cvert` is satisfied at every `Ipo` point (mirror of the
    `nestNet` `nsat_all`, now for the all-cross-`PO` model). -/
theorem pcv_all (p : Bool × Nat) : ∀ D ∈ cl Cvert, sat Ipo p D := by
  intro D hD
  simp only [Cvert, cl, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false, or_assoc] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨po_ha p, po_he p⟩, po_hal p⟩
  · exact ⟨po_ha p, po_he p⟩
  · exact po_ha p
  · exact po_he p
  · exact po_ha p
  · exact po_hal p
  · exact po_he p
  · exact po_ha p

open Classical in
/-- `mty Cvert Ipo` is CONSTANT `= cl Cvert` on the two-region model. -/
theorem pcvfull (p : Bool × Nat) : mty Cvert Ipo p = cl Cvert := by
  unfold mty
  apply List.filter_eq_self.mpr
  intro D hD
  exact decide_eq_true (pcv_all p D hD)

/-- The region selector of the two-tower witness. -/
def reg2 (k : Fin 2) : Bool := k.val == 1

theorem reg2_ne : ∀ k k' : Fin 2, k ≠ k' → reg2 k ≠ reg2 k' := by decide

/-- The `Fin 2`-indexed family of ascending towers of the all-cross-`PO` model:
    tower `k` is region `reg2 k`'s `PP`-chain. -/
def twoTowers (k : Fin 2) (m : Nat) : Bool × Nat := (reg2 k, m)

/-- **NON-VACUITY OF `vtowers_ok` — A GENUINE TWO-KERNEL PURELY-VERTICAL
    CERTIFICATE** (§38.1).  In the two-region all-cross-`PO` model `Ipo`, the two
    regions' ascending `PP`-chains are pairwise NON-comparable with constant
    cross-value `PO` (the `cross_po_stabilizes` third of the §36 trichotomy),
    each serves the single demand `A₀` of `Cvert`, and no phase carries a
    horizontal demand (`cvert_demands`) — so `vtowers_ok`'s hypotheses are
    jointly satisfiable at `n = 2` and the assembled certificate exists.  This
    rules out the degenerate readings the review ledger keeps finding: `κ` has
    TWO elements (not a disguised single kernel), and the cross-kernel rectangle
    `hrectQ` is exercised at a REAL non-`EQ` value, so `hinj` is discharged by
    `cross_const_ne_eq` rather than holding trivially. -/
theorem vtowers_two_nonvacuous :
    ∃ ik pk : Fin 2 → Nat,
      MultiTierOk (mixKernels Ipo Cvert (fun e : Empty => e.elim)
        twoTowers ik pk (fun _ => true)) ∧
      ∀ k, ∀ D ∈ [Concept.atom 0], ∃ b, b < pk k ∧
        D ∈ mty Cvert Ipo (twoTowers k (ik k + b)) := by
  refine vtowers_ok Ipo_rcc5 Cvert (fun _ => [Concept.atom 0]) twoTowers
    (fun _ _ => trivial) ?_ ?_ (fun _ _ => 0) ?_ ?_
  · -- each tower ascends by `PP` inside its own region
    intro k m
    show (if reg2 k = reg2 k then chain m (m + 1) else po) = pp
    rw [if_pos rfl]; exact chain_lt (Nat.lt_succ_self m)
  · -- recurrence + round-robin coverage past ANY threshold
    intro k L0
    refine ⟨L0, 1, Nat.le_refl _, Nat.one_pos, by rw [pcvfull, pcvfull], ?_⟩
    intro D hD
    rcases List.mem_singleton.mp hD with rfl
    exact ⟨0, Nat.one_pos, by rw [pcvfull]; decide⟩
  · -- the cross-kernel relation is CONSTANT `PO` (never `EQ`)
    intro k k' hne i j _ _
    have hb : reg2 k ≠ reg2 k' := reg2_ne k k' hne
    show (if reg2 k = reg2 k' then chain i j else po)
      = (if reg2 k = reg2 k' then chain 0 0 else po)
    rw [if_neg hb, if_neg hb]
  · -- every phase demand is `∃PP.A₀` — purely vertical
    intro k m r D hmem
    obtain ⟨rfl, rfl⟩ := cvert_demands r D (mty_sub _ hmem)
    exact Or.inl ⟨rfl, List.mem_singleton.mpr rfl⟩

/-- `nestRho` in projection form (so it applies to non-literal pairs). -/
theorem nestRho_eq (p q : Bool × Nat) :
    nestRho p q = if p.1 = q.1 then chain p.2 q.2 else po := by
  cases p; cases q; rfl

/-- A `PP`-step of `Ipo` never leaves its region (across regions the value is
    `PO`).  So an ascending tower of `Ipo` stays inside the region of its root. -/
theorem po_pp_same_region {p q : Bool × Nat} (h : Ipo.rho p q = pp) : p.1 = q.1 := by
  rcases Classical.em (p.1 = q.1) with hb | hb
  · exact hb
  · exfalso
    have h' : nestRho p q = pp := h
    rw [nestRho_eq, if_neg hb] at h'
    exact absurd h' (by decide)

/-- Consequently the class tower of a root stays in the root's region. -/
theorem classChain_region {n : Nat} (Ds : Fin n → List Concept)
    (hL : ∀ k, 0 < (Ds k).length) (x0 : Fin n → Bool × Nat)
    (h0 : ∀ k, persistAll Ipo Cvert (Ds k) (x0 k)) (k : Fin n) :
    ∀ m, (classChain Ipo_rcc5 Cvert Ds hL x0 h0 k m).1 = (x0 k).1 := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← ih]
    exact (po_pp_same_region (classChain_step Ipo_rcc5 Cvert Ds hL x0 h0 k m)).symm

/-- Each region base is a `persistAll` node for `Cvert`'s single demand `A₀`. -/
theorem po_persistAllAt (q : Bool × Nat) : persistAll Ipo Cvert [Concept.atom 0] q :=
  ⟨trivial, fun D hD => by
    rcases List.mem_singleton.mp hD with rfl
    exact ⟨mem_mty.mpr ⟨by decide, po_he q⟩, po_hal q⟩⟩

theorem po_persistAll (b : Bool) : persistAll Ipo Cvert [Concept.atom 0] (b, 0) :=
  po_persistAllAt (b, 0)

/-- Every `Ipo` site with `Cvert`'s single demand satisfies the purely-vertical
    site condition: `cl Cvert`'s only existential is `∃PP.A₀` (`cvert_demands`),
    so no cone reasoning is needed. -/
theorem po_siteDem (q : Bool × Nat) : SiteDem Ipo Cvert (q, [Concept.atom 0]) := by
  intro z _ _ r D hmem
  obtain ⟨rfl, rfl⟩ := cvert_demands r D (mty_sub _ hmem)
  exact Or.inl ⟨rfl, List.mem_singleton.mpr rfl⟩

/-- **NON-VACUITY OF THE MODEL-SIDE ENTRY POINT `vtowers_or_comparable`** — the
    CERTIFICATE branch actually fires.  Starting from two `persistAll` NODES (the
    two region bases of `Ipo`), the dichotomy's escape branch is REFUTED: each
    class tower stays in its root's region (`classChain_region`), so every
    cross-value is `PO`, and neither comparability disjunct can hold.  Hence the
    model-side entry point delivers a genuine two-kernel `MultiTierOk` and is not
    a disguised "always comparable" statement. -/
theorem vtowers_from_nodes_nonvacuous :
    ∃ ik pk : Fin 2 → Nat,
      MultiTierOk (mixKernels Ipo Cvert (fun e : Empty => e.elim)
        (classChain Ipo_rcc5 Cvert (fun _ => [Concept.atom 0]) (fun _ => Nat.one_pos)
          (fun k => (reg2 k, 0)) (fun k => po_persistAll (reg2 k)))
        ik pk (fun _ => true)) ∧
      ∀ k, ∀ D ∈ [Concept.atom 0], ∃ b, b < pk k ∧
        D ∈ mty Cvert Ipo (classChain Ipo_rcc5 Cvert (fun _ => [Concept.atom 0])
          (fun _ => Nat.one_pos) (fun k => (reg2 k, 0))
          (fun k => po_persistAll (reg2 k)) k (ik k + b)) := by
  have hdem : ∀ (k : Fin 2) (z : Bool × Nat), Ipo.dom z →
      (z = (reg2 k, 0) ∨ Ipo.rho (reg2 k, 0) z = pp) →
      ∀ r D, Concept.ex r D ∈ mty Cvert Ipo z →
        (r = pp ∧ D ∈ [Concept.atom 0]) ∨ r = eq := by
    intro _ _ _ _ r D hmem
    obtain ⟨rfl, rfl⟩ := cvert_demands r D (mty_sub _ hmem)
    exact Or.inl ⟨rfl, List.mem_singleton.mpr rfl⟩
  rcases vtowers_or_comparable Ipo_rcc5 Cvert (fun _ => [Concept.atom 0])
      (fun _ => Nat.one_pos) (fun k => (reg2 k, 0))
      (fun k => po_persistAll (reg2 k)) hdem with hcert | ⟨k, k', hne, hcomp⟩
  · exact hcert
  · exfalso
    have key : ∀ p q : Bool × Nat, p.1 ≠ q.1 → Ipo.rho p q = po := by
      intro p q h
      show nestRho p q = po
      rw [nestRho_eq, if_neg h]
    have hr := classChain_region (fun _ => [Concept.atom 0]) (fun _ => Nat.one_pos)
      (fun k : Fin 2 => (reg2 k, 0)) (fun k => po_persistAll (reg2 k))
    have hpo : ∀ i j,
        Ipo.rho (classChain Ipo_rcc5 Cvert (fun _ => [Concept.atom 0])
                  (fun _ => Nat.one_pos) (fun k => (reg2 k, 0))
                  (fun k => po_persistAll (reg2 k)) k i)
                (classChain Ipo_rcc5 Cvert (fun _ => [Concept.atom 0])
                  (fun _ => Nat.one_pos) (fun k => (reg2 k, 0))
                  (fun k => po_persistAll (reg2 k)) k' j) = po :=
      fun i j => key _ _ (by rw [hr k i, hr k' j]; exact reg2_ne k k' hne)
    rcases hcomp with hemb | hemb'
    · obtain ⟨j, hj⟩ := hemb 0
      rcases hj with h | h <;> rw [hpo 0 j] at h <;> exact absurd h (by decide)
    · obtain ⟨i, hi⟩ := hemb' 0
      rw [hpo i 0] at hi
      exact absurd hi (by decide)

/-- **THE MERGE PRIMITIVE FIRES** — two `persistAll` sites at different heights
    of the SAME `Ipo` region (`(false,0)` and `(false,7)`: the nested geometry
    the merge exists for) collapse into ONE site at `(false,8)` carrying both
    demand lists.  `persistAll_merge2` is therefore not vacuous, and in
    particular its `sat`-form guard bridge `merge_persistAll_sat` is exercised on
    genuine `persistAll` sites — the case `merge_persistAll`'s `mty`-form guard
    could not reach. -/
theorem persistAll_merge2_nonvacuous :
    persistAll Ipo Cvert ([Concept.atom 0] ++ [Concept.atom 0]) (false, 8) :=
  persistAll_merge2 Ipo_rcc5 (po_persistAllAt (false, 0)) (po_persistAllAt (false, 7))
    trivial
    (by show (if false = false then chain 0 8 else po) = pp
        rw [if_pos rfl]; exact chain_lt (by omega))
    (by show (if false = false then chain 7 8 else po) = pp
        rw [if_pos rfl]; exact chain_lt (by omega))

/-- **NON-VACUITY OF `vtowers_merged`** — the unconditional certificate is
    delivered on a two-site family sitting at different heights of ONE `Ipo`
    region, the nested geometry the merge exists for.  Honest scope: this
    witnesses that the hypotheses are satisfiable and the serving conclusion is
    reached; it does NOT claim which branch the recursion took (that would need
    the staircase argument of §36.1).  The merge primitive itself is witnessed
    firing by `persistAll_merge2_nonvacuous`. -/
theorem vtowers_merged_nonvacuous :
    ∃ (m : Nat) (ck : Fin m → Nat → (Bool × Nat)) (ik pk : Fin m → Nat),
      MultiTierOk (mixKernels Ipo Cvert (fun e : Empty => e.elim) ck ik pk (fun _ => true)) ∧
      ∃ k b, b < pk k ∧ Concept.atom 0 ∈ mty Cvert Ipo (ck k (ik k + b)) := by
  have hpa : ∀ s ∈ ([(((false, 0) : Bool × Nat), [Concept.atom 0]),
      (((false, 7) : Bool × Nat), [Concept.atom 0])] : List ((Bool × Nat) × List Concept)),
      persistAll Ipo Cvert s.2 s.1 := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact po_persistAllAt (false, 0)
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact po_persistAllAt (false, 7)
      · nomatch hs
  have hpos : ∀ s ∈ ([(((false, 0) : Bool × Nat), [Concept.atom 0]),
      (((false, 7) : Bool × Nat), [Concept.atom 0])] : List ((Bool × Nat) × List Concept)),
      0 < s.2.length := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact Nat.one_pos
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact Nat.one_pos
      · nomatch hs
  have hdem : ∀ s ∈ ([(((false, 0) : Bool × Nat), [Concept.atom 0]),
      (((false, 7) : Bool × Nat), [Concept.atom 0])] : List ((Bool × Nat) × List Concept)),
      SiteDem Ipo Cvert s := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact po_siteDem (false, 0)
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact po_siteDem (false, 7)
      · nomatch hs
  obtain ⟨m, ck, ik, pk, hok, hserve⟩ := vtowers_merged Ipo_rcc5 Cvert _ hpa hpos hdem
  exact ⟨m, ck, ik, pk, hok,
    hserve _ (List.mem_cons.mpr (Or.inl rfl)) _ (List.mem_singleton.mpr rfl)⟩

/-- **NON-VACUITY OF `family_interface`** — with a NONEMPTY bank, so the base
    choice is genuinely exercised.  The bank witness `(false,5)` sits ON one of
    the two region chains, so its row to that chain is NOT constant globally
    (`chain 0 5 = PP` but `chain 6 5 = PPI`) — the theorem has to place that
    kernel's window past the transition.  Cross-pairs are constant `PO`
    (`classChain_region`), so the non-comparability hypothesis holds with the
    zero horizon. -/
theorem family_interface_nonvacuous :
    ∃ ik pk : Fin 2 → Nat, (∀ k, 0 < pk k) ∧
      ∀ w ∈ [((false, 5) : Bool × Nat)], ∀ (k : Fin 2) (b : Nat), b < pk k →
        Ipo.rho w (classChain Ipo_rcc5 Cvert (fun _ => [Concept.atom 0])
                    (fun _ => Nat.one_pos) (fun k => (reg2 k, 0))
                    (fun k => po_persistAll (reg2 k)) k (ik k + b))
          = Ipo.rho w (classChain Ipo_rcc5 Cvert (fun _ => [Concept.atom 0])
                    (fun _ => Nat.one_pos) (fun k => (reg2 k, 0))
                    (fun k => po_persistAll (reg2 k)) k (ik k)) := by
  have hr := classChain_region (fun _ => [Concept.atom 0]) (fun _ => Nat.one_pos)
    (fun k : Fin 2 => (reg2 k, 0)) (fun k => po_persistAll (reg2 k))
  have hconst : ∀ k k' : Fin 2, k ≠ k' → ∀ i j, (0 : Nat) ≤ i → (0 : Nat) ≤ j →
      Ipo.rho (classChain Ipo_rcc5 Cvert (fun _ => [Concept.atom 0])
                 (fun _ => Nat.one_pos) (fun k => (reg2 k, 0))
                 (fun k => po_persistAll (reg2 k)) k i)
              (classChain Ipo_rcc5 Cvert (fun _ => [Concept.atom 0])
                 (fun _ => Nat.one_pos) (fun k => (reg2 k, 0))
                 (fun k => po_persistAll (reg2 k)) k' j)
        = Ipo.rho (classChain Ipo_rcc5 Cvert (fun _ => [Concept.atom 0])
                 (fun _ => Nat.one_pos) (fun k => (reg2 k, 0))
                 (fun k => po_persistAll (reg2 k)) k 0)
                (classChain Ipo_rcc5 Cvert (fun _ => [Concept.atom 0])
                 (fun _ => Nat.one_pos) (fun k => (reg2 k, 0))
                 (fun k => po_persistAll (reg2 k)) k' 0) := by
    intro k k' hne i j _ _
    have key : ∀ q q' : Bool × Nat, q.1 ≠ q'.1 → Ipo.rho q q' = po := by
      intro q q' h
      show nestRho q q' = po
      rw [nestRho_eq, if_neg h]
    rw [key _ _ (by rw [hr k i, hr k' j]; exact reg2_ne k k' hne),
      key _ _ (by rw [hr k 0, hr k' 0]; exact reg2_ne k k' hne)]
  obtain ⟨ik, pk, hp, _, hstab, _⟩ := family_interface Ipo_rcc5 Cvert
    (fun _ => [Concept.atom 0]) (fun _ => Nat.one_pos) (fun k => (reg2 k, 0))
    (fun k => po_persistAll (reg2 k)) [((false, 5) : Bool × Nat)]
    (fun _ _ => trivial) (fun _ _ => 0) hconst
  exact ⟨ik, pk, hp, hstab⟩

/-- Everything in `cl Cnest` is satisfied at every `Ipo` point. -/
theorem psat_all (p : Bool × Nat) : ∀ D ∈ cl Cnest, sat Ipo p D := by
  intro D hD
  rcases List.mem_cons.mp hD with rfl | hD2
  · exact po_hcn p
  rcases List.mem_append.mp hD2 with hD3 | hD4
  · exact pcv_all p D hD3
  · rcases List.mem_cons.mp hD4 with rfl | hD5
    · exact po_hpo p
    · exact pcv_all p D hD5

open Classical in
/-- `mty Cnest Ipo` is CONSTANT `= cl Cnest` (everything sat everywhere). -/
theorem pfull (p : Bool × Nat) : mty Cnest Ipo p = cl Cnest := by
  unfold mty
  apply List.filter_eq_self.mpr
  intro D hD
  exact decide_eq_true (psat_all p D hD)

/-- `Cnest`'s existentials are exactly `∃PP.A₀` and `∃PO.Cvert`. -/
theorem cnest_demands : ∀ r D, Concept.ex r D ∈ cl Cnest →
    (r = pp ∧ D = Concept.atom 0) ∨ (r = po ∧ D = Cvert) := by
  intro r D h
  have hb := List.all_eq_true.mp
    (show (cl Cnest).all (fun E => match E with
      | Concept.ex r D => decide ((r = pp ∧ D = Concept.atom 0) ∨
          (r = po ∧ D = Cvert))
      | _ => true) = true from by decide) (Concept.ex r D) h
  simpa only [decide_eq_true_eq] using hb

/-- The only universal in `cl Cnest` is `∀PP.(∃PP.A₀)`. -/
theorem cnest_all_pp : ∀ r cc, Concept.all r cc ∈ cl Cnest → r = pp := by
  intro r cc h
  have hb := List.all_eq_true.mp
    (show (cl Cnest).all (fun E => match E with
      | Concept.all r _ => decide (r = pp)
      | _ => true) = true from by decide) (Concept.all r cc) h
  simpa only [decide_eq_true_eq] using hb

/-- `A₀` in every point's `mtk` label at the `Cnest` root budget. -/
theorem po_atom0_mtk (b : Bool) (n : Nat) :
    Concept.atom 0 ∈ mtk Cnest Ipo (b, n) (mdepth Cnest) :=
  mem_mtk.mpr ⟨mem_mty.mpr ⟨by decide, rfl⟩, by decide⟩

/-- `Cvert` in a base's `mtk` label. -/
theorem po_cvert_mtk (b : Bool) :
    Cvert ∈ mtk Cnest Ipo (b, 0) (mdepth Cnest) :=
  mem_mtk.mpr ⟨mem_mty.mpr ⟨by decide, po_hcv (b, 0)⟩, by decide⟩

open Classical in
/-- **`Cnest` extracts through the MULTI-kernel engine `mtkKernels_ok`** — the
    FIRST genuine two-kernel extraction.  Two ascending towers (`κ = Bool`),
    each region's base carrying its own `∃PP.A₀`; the cross-tower `∃PO.Cvert`
    routes to the OTHER base via the `PO` `K`-edge (route-1).  Validates the
    multi-kernel certificate `mtkKernels_ok` end-to-end, as `cmix` did for the
    single kernel. -/
theorem cnest_generic_satisfiable : Satisfiable Cnest := by
  have hok := mtkKernels_ok Ipo_rcc5 Cnest_pofree (fun b : Bool => (b, 0))
    (fun _ => trivial) (fun _ => mdepth Cnest) (fun _ _ => false) (fun _ _ => rfl)
    (id) (fun b n => (b, n)) (fun _ _ => trivial)
    (by intro k n; show (if k = k then chain n (n + 1) else po) = pp
        rw [if_pos rfl]; exact chain_lt (Nat.lt_succ_self n))
    (fun _ => 1) (fun _ => 1) (fun _ => Nat.one_pos)
    (by intro k; exact (pfull (k, 1)).trans (pfull (k, 1 + 1)).symm)
    (by intro k a; show (if k = k then chain 0 (1 + a) else po) = pp
        rw [if_pos rfl]; exact chain_lt (by omega))
    (by intro e f r cc hmem hE
        have hr : r = pp := cnest_all_pp r cc (mty_sub _ (mem_mtk.mp hmem).1)
        subst hr
        by_cases hef : e = f
        · rw [if_pos hef] at hE; exact absurd hE (by decide)
        · rw [if_neg hef] at hE; exact absurd hE (by cases e <;> cases f <;> decide))
    (by intro e r D hmem
        rcases cnest_demands r D (mty_sub _ (mem_mtk.mp hmem).1) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine Or.inr ⟨e, ?_, 0, Nat.one_pos, po_atom0_mtk e 1⟩
          split
          · rfl
          · exact absurd (rfl : e = id e) (by assumption)
        · refine Or.inl ⟨!e, ?_, po_cvert_mtk !e⟩
          rw [if_neg (show e ≠ !e from by cases e <;> decide)]
          cases e <;> rfl)
    (by intro k a r D hmem
        rcases cnest_demands r D (mty_sub _ (mem_mtk.mp hmem).1) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, 0, Nat.one_pos, po_atom0_mtk k 1⟩)
        · refine Or.inl ⟨!k, ?_, po_cvert_mtk !k⟩
          rw [if_neg (show (!k) ≠ id k from by cases k <;> decide)])
  exact @multiTier_sound Bool Bool (fun a b => Classical.propDecidable (a = b)) _ hok
    (Sum.inl false) Cnest
    (by show Cnest ∈ mtk Cnest Ipo (false, 0) (mdepth Cnest)
        exact mem_mtk.mpr ⟨mem_mty.mpr ⟨cl_self Cnest, po_hcn (false, 0)⟩, Nat.le_refl _⟩)

/-- **`Cnest` is an instance of `extract_flat_towers`** — the general
    arbitrary-`κ` flat multi-tower extraction fires on `Cnest` (`κ = Bool`),
    confirming the general lemma is correctly general and non-vacuous.  The
    routing: `∃PP.A₀` → own kernel, `∃PO.Cvert` → the other base. -/
theorem cnest_via_flat : Satisfiable Cnest := by
  refine extract_flat_towers Ipo_rcc5 Cnest_pofree (fun b n => (b, n))
    (fun _ _ => trivial)
    (by intro k n; show (if k = k then chain n (n + 1) else po) = pp
        rw [if_pos rfl]; exact chain_lt (Nat.lt_succ_self n))
    (fun _ => 1) (fun _ => 1) (fun _ => Nat.one_pos) (fun _ => Nat.one_pos)
    (fun k => (pfull (k, 1)).trans (pfull (k, 1 + 1)).symm)
    ?_ ?_ false (mem_mty.mpr ⟨cl_self Cnest, po_hcn (false, 0)⟩)
  · intro e r D hmem
    rcases cnest_demands r D (mty_sub _ (mem_mtk.mp hmem).1) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, po_atom0_mtk e 1⟩
    · exact Or.inr (Or.inl ⟨rfl, !e, by cases e <;> decide, po_cvert_mtk !e⟩)
  · intro k a r D hmem
    rcases cnest_demands r D (mty_sub _ (mem_mtk.mp hmem).1) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, 0, Nat.one_pos, po_atom0_mtk k 1⟩
    · exact Or.inr (Or.inl ⟨rfl, !k, by cases k <;> decide, po_cvert_mtk !k⟩)

/-! ### A PHASE-∃DR witness `Cpdr`, through the DR-children cert `mtkKernelsDR_ok`

`Cpdr = Cvert ⊓ ∃DR.A₁ ⊓ ∀PP.(∃DR.A₁)` on the cross-`DR` carrier `Bool × ℕ`:
within a region the ascending `PP`-tower, ACROSS regions `DR`.  Because
`comp(PP,DR) = {DR}`, `DR` propagates DOWN the tower — the whole tower region is
`DR` to the other region.  So every tower PHASE (via `∀PP`) demands `∃DR.A₁`,
served by the OTHER region's `DR`-child through the forced `DR` `K`-edge.  This
fires `mtkKernelsDR_ok` — the first phase-`∃DR` extraction. -/

/-- Cross-`DR` two-region relation: within a region the chain, across `DR`. -/
def drRho : (Bool × Nat) → (Bool × Nat) → Atom
  | (b, i), (b', j) => if b = b' then chain i j else dr

theorem drRho_frame : Frame drRho where
  refl_eq := by
    rintro ⟨b, i⟩
    show (if b = b then chain i i else dr) = eq
    rw [if_pos rfl]; exact chain_self i
  eq_id := by
    rintro ⟨b, i⟩ ⟨b', j⟩ h
    show (⟨b, i⟩ : Bool × Nat) = ⟨b', j⟩
    by_cases hb : b = b'
    · have h' : chain i j = eq := by
        have hh : (if b = b' then chain i j else dr) = eq := h
        rwa [if_pos hb] at hh
      subst hb; rw [chain_eq_imp h']
    · have hh : (if b = b' then chain i j else dr) = eq := h
      rw [if_neg hb] at hh; exact absurd hh (by decide)
  conv_ := by
    rintro ⟨b, i⟩ ⟨b', j⟩
    show (if b' = b then chain j i else dr) = conv (if b = b' then chain i j else dr)
    by_cases hb : b = b'
    · rw [if_pos hb, if_pos hb.symm]; exact chain_conv i j
    · rw [if_neg hb, if_neg (fun h => hb h.symm)]; rfl
  comp_ := by
    rintro ⟨b, i⟩ ⟨b', j⟩ ⟨b'', k⟩
    show (if b = b'' then chain i k else dr)
      ∈ comp (if b = b' then chain i j else dr) (if b' = b'' then chain j k else dr)
    by_cases hbb' : b = b'
    · by_cases hb'b'' : b' = b''
      · subst hbb'; subst hb'b''; rw [if_pos rfl, if_pos rfl, if_pos rfl]
        exact chainFrame.comp_ i j k
      · rw [if_pos hbb', if_neg hb'b'', if_neg (fun h => hb'b'' (hbb'.symm.trans h))]
        rcases chain_vals i j with h | h | h <;> rw [h] <;> decide
    · by_cases hb'b'' : b' = b''
      · rw [if_neg hbb', if_pos hb'b'', if_neg (fun h => hbb' (h.trans hb'b''.symm))]
        rcases chain_vals j k with h | h | h <;> rw [h] <;> decide
      · by_cases hbb'' : b = b''
        · rw [if_pos hbb'', if_neg hbb', if_neg hb'b'']
          rcases chain_vals i k with h | h | h <;> rw [h] <;> decide
        · rw [if_neg hbb'', if_neg hbb', if_neg hb'b'']; decide

/-- The phase-`∃DR` model: `A₀` on region `false` (the tower), `A₁` on region
    `true` (the `DR`-child). -/
def Idr : Interp (Bool × Nat) :=
  ⟨fun _ => True, drRho, fun a p => match p with | (false, _) => a = 0 | (true, _) => a = 1⟩

theorem Idr_rcc5 : RCC5Interp Idr := frame_rcc5 drRho drRho_frame _

/-- `Cpdr = Cvert ⊓ ∃DR.A₁ ⊓ ∀PP.(∃DR.A₁)` — a PHASE-`∃DR` concept. -/
def Cpdr : Concept :=
  .and (.and Cvert (.ex dr (.atom 1))) (.all pp (.ex dr (.atom 1)))

theorem Cpdr_pofree : POFree Cpdr := ⟨⟨Cvert_pofree, trivial⟩, by decide, trivial⟩

theorem dr_ha : ∀ n, sat Idr (false, n) (Concept.atom 0) := fun _ => rfl
theorem dr_ha1 : sat Idr (true, 0) (Concept.atom 1) := rfl

theorem dr_hpp : ∀ n, sat Idr (false, n) (Concept.ex pp (Concept.atom 0)) := by
  intro n
  refine ⟨(false, n + 1), trivial, ?_, rfl⟩
  show (if false = false then chain n (n + 1) else dr) = pp
  rw [if_pos rfl]; exact chain_lt (Nat.lt_succ_self n)

theorem dr_hdr : ∀ n, sat Idr (false, n) (Concept.ex dr (Concept.atom 1)) := by
  intro n
  exact ⟨(true, 0), trivial, rfl, rfl⟩

theorem dr_hall_pp : ∀ n, sat Idr (false, n)
    (Concept.all pp (Concept.ex pp (Concept.atom 0))) := by
  rintro n ⟨b, m⟩ _ hr
  cases b with
  | false => exact dr_hpp m
  | true => exact absurd (show (dr : Atom) = pp from hr) (by decide)

theorem dr_hall_dr : ∀ n, sat Idr (false, n)
    (Concept.all pp (Concept.ex dr (Concept.atom 1))) := by
  rintro n ⟨b, m⟩ _ hr
  cases b with
  | false => exact dr_hdr m
  | true => exact absurd (show (dr : Atom) = pp from hr) (by decide)

theorem dr_hcv : ∀ n, sat Idr (false, n) Cvert :=
  fun n => ⟨⟨dr_ha n, dr_hpp n⟩, dr_hall_pp n⟩

theorem dr_hcpdr : ∀ n, sat Idr (false, n) Cpdr :=
  fun n => ⟨⟨dr_hcv n, dr_hdr n⟩, dr_hall_dr n⟩

/-- `Cpdr`'s existentials are exactly `∃PP.A₀` and `∃DR.A₁`. -/
theorem cpdr_demands : ∀ r D, Concept.ex r D ∈ cl Cpdr →
    (r = pp ∧ D = Concept.atom 0) ∨ (r = dr ∧ D = Concept.atom 1) := by
  intro r D h
  have hb := List.all_eq_true.mp
    (show (cl Cpdr).all (fun E => match E with
      | Concept.ex r D => decide ((r = pp ∧ D = Concept.atom 0) ∨
          (r = dr ∧ D = Concept.atom 1))
      | _ => true) = true from by decide) (Concept.ex r D) h
  simpa only [decide_eq_true_eq] using hb

/-- The only universals in `cl Cpdr` are `∀PP`. -/
theorem cpdr_all_pp : ∀ r cc, Concept.all r cc ∈ cl Cpdr → r = pp := by
  intro r cc h
  have hb := List.all_eq_true.mp
    (show (cl Cpdr).all (fun E => match E with
      | Concept.all r _ => decide (r = pp) | _ => true) = true from by decide)
    (Concept.all r cc) h
  simpa only [decide_eq_true_eq] using hb

theorem dr_a0_mtk (n : Nat) :
    Concept.atom 0 ∈ mtk Cpdr Idr (false, n) (mdepth Cpdr) :=
  mem_mtk.mpr ⟨mem_mty.mpr ⟨by decide, rfl⟩, by decide⟩

theorem dr_a1_mtk :
    Concept.atom 1 ∈ mtk Cpdr Idr (true, 0) (mdepth Cpdr) :=
  mem_mtk.mpr ⟨mem_mty.mpr ⟨by decide, rfl⟩, by decide⟩

theorem cpdr_at_root : Cpdr ∈ mty Cpdr Idr (false, 0) :=
  mem_mty.mpr ⟨cl_self Cpdr, dr_hcpdr 0⟩

/-- The child `(true,0)` has NO existential of `cl Cpdr`: it carries `A₁` but its
    `PP`/`DR`-successors never carry the demanded atom (its `DR`-neighbours are
    the tower region, which carries `A₀`, not `A₁`). -/
theorem dchild_no_ex : ∀ r D, Concept.ex r D ∉ mty Cpdr Idr (true, 0) := by
  intro r D hmem
  obtain ⟨y, _, hr, hy⟩ := mty_ex hmem
  rcases cpdr_demands r D (mty_sub _ hmem) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases y with ⟨b, m⟩
    cases b with
    | true =>
      have h2 : (0 : Nat) = 1 := (mem_mty.mp hy).2
      exact absurd h2 (by decide)
    | false => exact absurd (show (dr : Atom) = pp from hr) (by decide)
  · rcases y with ⟨b, m⟩
    cases b with
    | true => exact absurd (show chain 0 m = dr from hr)
                (by rcases chain_vals 0 m with h | h | h <;> rw [h] <;> decide)
    | false =>
      have h2 : (1 : Nat) = 0 := (mem_mty.mp hy).2
      exact absurd h2 (by decide)

open Classical in
/-- **`Cpdr` extracts through `mtkKernelsDR_ok` — the FIRST phase-`∃DR`
    extraction.**  Every tower phase demands `∃DR.A₁` (via `∀PP`), served by the
    child `(true,0)` through the forced `DR` `K`-edge (`kdr () true`); `∃PP.A₀`
    goes up the tower.  So the forcing-completion frame + DR-children cert serve
    a genuine phase-level `∃DR` — the item-2 mechanism, end-to-end. -/
theorem cpdr_generic_satisfiable : Satisfiable Cpdr := by
  obtain ⟨i, p, hLi, hp, _, hty⟩ :=
    mty_segment_bounded (I := Idr) Cpdr (fun n => (false, n)) 1
  refine extract_dr_children Idr_rcc5 Cpdr_pofree (fun e : Bool => (e, 0))
      (fun _ => trivial) (fun _ => mdepth Cpdr) (fun e f => decide (e ≠ f))
      (by intro e f; cases e <;> cases f <;> rfl) (fun _ : Unit => false)
      (fun _ e => e)
      (fun _ e he => by cases e with | false => exact absurd he (by decide) | true => decide)
      (fun _ n => (false, n)) (fun _ _ => trivial)
      (by intro _ n; show (if false = false then chain n (n + 1) else dr) = pp
          rw [if_pos rfl]; exact chain_lt (Nat.lt_succ_self n))
      (fun _ => i) (fun _ => p) (fun _ => hp) (fun _ => hty)
      (by intro _ a; show (if false = false then chain 0 (i + a) else dr) = pp
          rw [if_pos rfl]; exact chain_lt (by omega))
      (by intro _ a e he
          cases e with
          | false => exact absurd he (by decide)
          | true =>
            refine ⟨?_, by omega, by omega⟩
            show (if true = false then chain (i + a) 0 else dr) = dr
            rw [if_neg (by decide)])
      ?_ ?_ ?_ false (mem_mtk.mpr ⟨cpdr_at_root, Nat.le_refl _⟩)
  · -- hee: only ∀ is ∀PP; E ∈ {eq, dr}, never pp
    intro e f r cc hmem hE
    have hr : r = pp := cpdr_all_pp r cc (mty_sub _ (mem_mtk.mp hmem).1)
    subst hr
    by_cases hef : e = f
    · rw [if_pos hef] at hE; exact absurd hE (by decide)
    · rw [if_neg hef] at hE
      cases e <;> cases f <;> simp_all <;> exact absurd hE (by decide)
  · -- he_ex
    intro e r D hmem
    cases e with
    | false =>
      rcases cpdr_demands r D (mty_sub _ (mem_mtk.mp hmem).1) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine Or.inr ⟨(), ?_, 0, hp, dr_a0_mtk (i + 0)⟩
        split
        · rfl
        · rename_i h; exact absurd rfl h
      · refine Or.inl ⟨true, ?_, dr_a1_mtk⟩
        split
        · rename_i h; exact absurd h (by decide)
        · rfl
    | true => exact absurd (mem_mtk.mp hmem).1 (dchild_no_ex r D)
  · -- hk_ex
    intro _ a r D hmem
    rcases cpdr_demands r D (mty_sub _ (mem_mtk.mp hmem).1) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, 0, hp, dr_a0_mtk (i + 0)⟩)
    · refine Or.inl ⟨true, ?_, dr_a1_mtk⟩
      split
      · rename_i h; exact absurd h (by decide)
      · rfl

end VerticalWitness

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
#print axioms glueFam_ok
#print axioms mty_mem_sublists
#print axioms readoff_qnet_frame
#print axioms buildChain_step
#print axioms externals_stabilize
#print axioms segment_select
#print axioms segment_kk_pp
#print axioms segment_kk_ppi
#print axioms dexternal_stabilizes
#print axioms dforward_forcing_dr
#print axioms dbackward_absorption_ppi
#print axioms dseg_ppi
#print axioms dseg_pp
#print axioms dppi_witness_all_below
#print axioms ddr_witness_all_above
#print axioms dbuildChain_step
#print axioms dsegment_select
#print axioms dsegment_kk_ppi
#print axioms anchored_all
#print axioms ppi_witness_bank
#print axioms kernel_site
#print axioms ddrpp_witness_bank
#print axioms dkernel_site
#print axioms mtOkPool_of_block
#print axioms one_kernel_block
#print axioms kernel_block_of_chain
#print axioms done_kernel_block
#print axioms dkernel_block_of_chain
#print axioms ordered_disjoint_frame
#print axioms twoSorted_frame
#print axioms multi_kernel_block
#print axioms mkBlock_nopo
#print axioms tightNePo_symm
#print axioms tightNePo_htpp
#print axioms tightNePo_htdr
#print axioms twoSorted_eq_readoff
#print axioms multiBlock_of_site
#print axioms multiBlock_of_chain
#print axioms dmultiBlock_of_site
#print axioms dmultiBlock_of_chain
#print axioms persistPP_productive
#print axioms persistPP_chain
#print axioms block_of_persistent
#print axioms ascKernel
#print axioms ascKernelG
#print axioms chain_ee_up
#print axioms chain_ee_down
#print axioms mtk_all_same
#print axioms linChain_frame
#print axioms chainMT_ok
#print axioms posetMT_ok
#print axioms dascKernel
#print axioms ascKernelPack
#print axioms stabKernelPack
#print axioms dStabKernelPack
#print axioms chain_pp_lt
#print axioms cross_dr_stabilizes
#print axioms cross_po_stabilizes
#print axioms classify_cross
#print axioms family_hrectQ
#print axioms exists_bound2
#print axioms family_hrectQ_bounded
#print axioms guard_propagates
#print axioms merge_persistAll
#print axioms merge_pair
#print axioms embed_to_pp
#print axioms embed_trans
#print axioms maximal_dominated
#print axioms exists_maximal_tower
#print axioms common_upper_on_tower
#print axioms class_persistAll
#print axioms towers_from_persistPP
#print axioms class_kernel
#print axioms rr_segment_from
#print axioms class_tower
#print axioms cross_const_ne_eq
#print axioms mixKernelsV_ok
#print axioms vtowers_ok
#print axioms classChain_above
#print axioms classChain_rec
#print axioms vtowers_or_comparable_gen
#print axioms vtowers_or_comparable
#print axioms merge_persistAll_sat
#print axioms persistAll_merge2
#print axioms comparable_common_upper
#print axioms filter_length_lt
#print axioms merge_step
#print axioms merge_sites
#print axioms vtowers_merged
#print axioms stab_swallowed_ppi
#print axioms stab_swallowed_no_dr_pp
#print axioms stab_window_family
#print axioms stab_window_family_multi
#print axioms mixSelect_of_cofinal_bank
#print axioms witness_sets_decreasing
#print axioms mixSelect_of_highBank
#print axioms filter_length_split
#print axioms spoiled_length_le_two
#print axioms exists_good_candidate
#print axioms cofinal_fixed_param
#print axioms exists_spaced_list
#print axioms exists_stable_base
#print axioms exists_stable_recurrence
#print axioms stable_base_range
#print axioms kernel_interface_of_persistAll
#print axioms kernel_range_of_persistAll
#print axioms exists_bank
#print axioms family_range
#print axioms family_interface
#print axioms window_stab_dichotomy
#print axioms mixSelect_cross_of_dichotomy
#print axioms rank_eq_imp_value_eq
#print axioms row_no_return
#print axioms ends_differ_rank_lt
#print axioms three_spaced_not_all_bad
#print axioms window_const_iff_ends
#print axioms stab_window_of_dr
#print axioms stab_window_of_pp
#print axioms stab_window_of_rank0
#print axioms cofinal_dr_all
#print axioms cofinal_dr_stab
#print axioms VerticalWitness.persistAll_merge2_nonvacuous
#print axioms VerticalWitness.vtowers_merged_nonvacuous
#print axioms VerticalWitness.vtowers_two_nonvacuous
#print axioms VerticalWitness.classChain_region
#print axioms VerticalWitness.vtowers_from_nodes_nonvacuous
#print axioms VerticalWitness.family_interface_nonvacuous
#print axioms ppPhaseNodes
#print axioms ppPhaseNodes_spec
#print axioms ascNodes
#print axioms self_mem_ascNodes
#print axioms sub_ascNodes_hwitness
#print axioms sub_ascNodes_phasewitness
#print axioms sub_ascNodes_oneshot
#print axioms ascNodes_trans
#print axioms ascNodes_covers
#print axioms ascNodes_covers_phase
#print axioms ascNodes_ee_all
#print axioms ascDadj_symm
#print axioms ascNodes_ee_all2
#print axioms persistPPI_productive
#print axioms persistPPI_chain
#print axioms block_of_persistent_desc
#print axioms cl_mdepth_le
#print axioms cl_ex_mdepth_lt
#print axioms cl_all_mdepth_lt
#print axioms ext_pp_asc_const
#print axioms ext_dr_desc_const
#print axioms mem_expand_self
#print axioms expand_sub_cl
#print axioms expand_sub_mty
#print axioms expand_and
#print axioms expand_or
#print axioms reqType_sub_mty
#print axioms reqType_and
#print axioms reqType_or
#print axioms mem_fire
#print axioms fire_sat
#print axioms fire_sub_cl
#print axioms reqType_sub_cl
#print axioms reqType_ex_witness
#print axioms reqType_ex_mdepth
#print axioms mem_mdepth_le_lmd
#print axioms lmd_lt
#print axioms childSeed_sub_mty
#print axioms childSeed_sub_cl
#print axioms child_lmd_lt
#print axioms self_mem_rnodes
#print axioms sub_rnodes_childNode
#print axioms childNode_mem
#print axioms rnodes_trans
#print axioms rnodes_covers
#print axioms slabel
#print axioms slabel_sub_mty
#print axioms slabel_sub_cl
#print axioms slabel_reverse
#print axioms slabel_forward_reqType
#print axioms slabel_lmd_le
#print axioms snodes
#print axioms snodes_covers
#print axioms schild_lmd_lt
#print axioms slabel_alldr_reqType
#print axioms slabel_exdr_reqType
#print axioms schildNode_eq_childNode
#print axioms slabel_dr_forward
#print axioms slabel_dr_reverse
#print axioms noDR_cl
#print axioms revfire_lmd_lt
#print axioms dr_reverse_sat
#print axioms allfree_cl_no_all
#print axioms allfree_reqType_no_all
#print axioms mtVF_frame
#print axioms mtVF_ok
#print axioms extract_allfree
#print axioms satisfiable_iff_allfree_cert
#print axioms allfree_imp_pofree
#print axioms symDrPo_frame
#print axioms qnet_empty_frame
#print axioms mtDR_frame
#print axioms mtDR_ok
#print axioms extract_podr
#print axioms satisfiable_iff_podr_cert
#print axioms mtkNodes_covers
#print axioms mtHF_ok
#print axioms extract_hfrag
#print axioms satisfiable_iff_hfrag_cert
#print axioms ascMixB_iff
#print axioms casc_ascmix
#print axioms casc_not_hfrag
#print axioms HFragWitness.Cwit_sat
#print axioms HFragWitness.Cwit_has_cert
#print axioms HFragWitness.Cwit_not_drfrag
#print axioms multiTierOk_of_pool_nil
#print axioms vkernel_ok
#print axioms VerticalWitness.cvert_satisfiable
#print axioms vkernel1_ok
#print axioms VerticalWitness.cvert_satisfiable_ext
#print axioms vkernel2_ok
#print axioms mixKernel_ok
#print axioms mixKernelI_ok
#print axioms mixKernels_ok
#print axioms po_default_asc_frame
#print axioms pp_twin_frame
#print axioms po_default_desc_frame
#print axioms all_into
#print axioms podefault_ek
#print axioms podefault_ke
#print axioms mtk_kk_pp
#print axioms mtkKernel_ok
#print axioms mtk_ee_all
#print axioms mtkNodesH_covers
#print axioms mtk_e_ex
#print axioms mtk_k_ex
#print axioms extract_mtkKernel
#print axioms pp_chain_below
#print axioms tower_from_persistPP
#print axioms extract_from_tower
#print axioms mtkKernel_nopo
#print axioms po_default_multi_frame
#print axioms po_dr_asc_frame
#print axioms po_dr_multi_child_frame
#print axioms po_dr_multi_kernel_frame
#print axioms podefault_ke_dr
#print axioms podefault_ek_dr
#print axioms mtkKernelsDR_ok
#print axioms mtkKernelsDR_nopo
#print axioms extract_dr_children
#print axioms VerticalWitness.drRho_frame
#print axioms VerticalWitness.Idr_rcc5
#print axioms VerticalWitness.dchild_no_ex
#print axioms VerticalWitness.cpdr_generic_satisfiable
#print axioms VerticalWitness.dr_hcpdr
#print axioms mtkKernels_ok
#print axioms mtkKernels_nopo
#print axioms extract_flat_towers
#print axioms extract_skel_towers
#print axioms no_ppi_demand
#print axioms VerticalWitness.cvert2_satisfiable
#print axioms vkernel2x_ok
#print axioms VerticalWitness.cvert2x_satisfiable
#print axioms dvkernel_ok
#print axioms VerticalWitness.dvert_satisfiable
#print axioms glueMTOk
#print axioms VerticalWitness.cvert_glue2
#print axioms satisfiable_of_persistPP
#print axioms VerticalWitness.cvert_via_generator
#print axioms starNet_frame
#print axioms posetNet_frame
#print axioms starKernel_ok
#print axioms posetKernel_ok
#print axioms posetKernelG_ok
#print axioms vkernelG_ok
#print axioms VerticalWitness.clin_satisfiable
#print axioms VerticalWitness.nestNet_frame
#print axioms VerticalWitness.cnest_satisfiable
#print axioms VerticalWitness.rootNest_frame
#print axioms VerticalWitness.crnest_satisfiable
#print axioms encodeHF_mtOk
#print axioms mtkNodes_length_le
#print axioms decidableSat_hfrag
#print axioms hfrag_hcompl
#print axioms encodeMT_mtOk
#print axioms decidableSat_vtower
#print axioms decidableSat_vtowerG
#print axioms decidableSat_vtowerRR
#print axioms decidableSat_vtowerRRI
#print axioms VerticalWitness.decidableSat_Ccar
#print axioms VerticalWitness.ccar_satisfiable
#print axioms VerticalWitness.decidableSat_Calt
#print axioms VerticalWitness.calt_satisfiable
#print axioms VerticalWitness.decidableSat_Cdesc
#print axioms VerticalWitness.cdesc_satisfiable
#print axioms VerticalWitness.cmix_satisfiable
#print axioms VerticalWitness.mixRho_frame
#print axioms VerticalWitness.mixCert_ok
#print axioms VerticalWitness.mix_cert_satisfiable
#print axioms VerticalWitness.decidableSat_Cmix
#print axioms VerticalWitness.cmix_nodes_root
#print axioms VerticalWitness.mixRho_po_lemma
#print axioms VerticalWitness.cvert_nodes_singleton
#print axioms VerticalWitness.cvert_generic_satisfiable
#print axioms VerticalWitness.cvert_via_tower
#print axioms VerticalWitness.cleanRho_frame
#print axioms VerticalWitness.Imerge_rcc5
#print axioms VerticalWitness.cmerge_nodes
#print axioms VerticalWitness.cmerge_generic_satisfiable
#print axioms VerticalWitness.cmix_generic_satisfiable
#print axioms VerticalWitness.cmix_via_tower
#print axioms VerticalWitness.nestRho_frame
#print axioms VerticalWitness.Ipo_rcc5
#print axioms VerticalWitness.cnest_generic_satisfiable
#print axioms VerticalWitness.cnest_via_flat
#print axioms VerticalWitness.cmerge_via_tower

end POFreeLift
