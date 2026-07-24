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
      | ⟨.ex dr d, hF⟩ => fire (slabel (childNode node hF)) dr
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
          exact fire_dr_reverse hI node.hdom (childNode node hG).hdom
            (childNode_rho node hG) (ih d hG) F hFm
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
        | dr => exact fire_sub_cl (ih d hG) F hFm
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
    ⟨⟨Concept.ex dr d, hF⟩, List.mem_attach _ _, mem_fire.mpr h⟩)

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
          have hall : Concept.all dr F ∈ slabel (childNode node hG) :=
            mem_fire.mp hFm
          exact Nat.le_of_lt (Nat.lt_of_lt_of_le (mdepth_all_lt dr F)
            (Nat.le_trans (ih d hG _ hall)
              (Nat.le_of_lt (child_lmd_lt hG))))
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
    s := c :: fire (slabel node) r
    hdom := hw.1
    hmty := by
      intro F hFm
      rcases List.mem_cons.mp hFm with rfl | h
      · exact hw.2.2
      · exact fire_sat (slabel_sub_mty hI node) hw.1 hw.2.1 F h
    hcl := by
      intro F hFm
      rcases List.mem_cons.mp hFm with rfl | h
      · exact cl_ex (slabel_sub_cl node _ hF)
      · exact fire_sub_cl (slabel_sub_cl node) F h }

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

/-- Termination for `snodes`: the saturated-label child is strictly
    shallower — its argument and forward-fired formulas are below the
    node's `lmd` (`slabel_lmd_le`). -/
theorem schild_lmd_lt (node : RNode I C0) {w : α} {r : Atom} {c : Concept}
    (hdem : Concept.ex r c ∈ slabel node) :
    lmd (reqType I w (c :: fire (slabel node) r)) <
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
    · have hall : Concept.all r F ∈ slabel node := mem_fire.mp hFfire
      exact Nat.lt_of_lt_of_le (mdepth_all_lt r F)
        (Nat.le_trans (mem_mdepth_le_lmd _ _ hall) (slabel_lmd_le node))
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

end POFreeLift
