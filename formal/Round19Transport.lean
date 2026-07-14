/-
Round-19: the source-oriented transport layer for ALCI_RCC5 cluster
quasimodels, authored in Lean 4 (core only, no mathlib).

This file is the NORMATIVE artifact of round 19.  The prose companion
(papers/fable5_round19/) is commentary on it.  Rationale: defects #10,
#11-adjacent and #12 of the review series were all divergences between
prose renditions of total recursive definitions and their intended
(executable) semantics.  In this medium the definition IS the artifact:
`uSource` below is total by construction (the compiler checks case
exhaustiveness), and the thirteenth review's witnesses are theorems
checked by the kernel.

Content:
  1. RCC5 atoms, converse, composition table; the finite facts used by
     rounds 13-18 (horizontal absorption, vertical transitivity,
     DR-column absorption, EQ-never-forced, converse closure,
     one-orientation triangle equivalence) -- all `by decide`.
  2. Certificates: core network, templates (inherited slots / core /
     fresh ports, total pattern nets), attachment steps in CANONICAL
     ORDER (a list -- canonical-order determinism is definitional, per
     the thirteenth review's cure for the false order-invariance
     lemma), injective slot maps as a wellformedness predicate (17.4).
  3. The operational unfolding `unfoldAll`: a fold over the step list,
     assigning pattern values and steering values; steering rows are
     recorded (the `frows` ledger).
  4. The SOURCE-ORIENTED update `uSource` (the thirteenth review's
     U1-U5): every pair value looked up where it was RECORDED --
     core row / birth pattern of the younger-or-equal side (covering
     the co-birth case, defect #12's first witness) / steering recorded
     at the younger's birth, with the flip on orientation.  Total by
     construction.
  5. The U-characterization theorem `uSource_eq_frame`, PROVED in
     round 20 (2026-07-13): on wellformed certificates, `uSource`
     agrees with the operational frame.  This is the exact statement
     that prose failed to render correctly in rounds 17 and 18; in
     round 19 it was the stated `sorry`; it is now a kernel-checked
     theorem (`frame_char`, induction on the canonical step list),
     together with the fuel-adequacy obligation
     (`uSourceFuel_irrel`, threshold `fuelNeed`).  The proof FORCED
     four additional `Wellformed` clauses (`targets_exist`,
     `targets_length`, `net_conv`, `f_reads_rows`) -- each intended
     all along and honored by the WP34 generator, none previously
     stated; see the `Wellformed` docstring.
  6. The thirteenth review's witnesses A/B/D as kernel-checked
     examples: the co-birth value is reachable by uSource (A'), the
     mis-source distinction (B'), and the S4-critical pin (D').
  7. Non-vacuity: `certC_wellformed` exhibits a certificate with an
     inherited slot satisfying the full `Wellformed`, and an `example`
     applies `uSource_eq_frame` to it end to end.
  8. Round-21 (2026-07-13): the S-layer soundness kernel.  `SCond`
     (the manuscripts' S4, stated on certificate-computable values via
     `pairVal`) implies the unfolded frame is composition-closed
     (`frame_closed`), converse-coherent (`frame_conv`) and EQ-free
     (`frame_proper`); `uSource_conv` is R2 for the update, and the
     closure proof is a max-birth rotation argument over the
     kernel-checked triangle-rotation facts (`comp_rot1`/`comp_rot2`).
     This is the statement WP30 Part C and WP32 Part C checked
     empirically.  Kernel-checked both ways: `certC_scond` + a closed
     end-to-end example, and `certD` (adversarial steering, the WP32
     Part-C control as a theorem) whose S-condition provably fails at
     the comp(DR,PO)-pinned triangle and whose frame provably breaks
     closure exactly there.
  9. Round-22 (2026-07-13): the catalogue level.  `SCat` states the
     S-condition on `(coreNet, templates, f)` ALONE — abstract
     enumerated rows replace occurrences, so the check is independent
     of the step count — and `scat_scond` proves that `SCat` plus
     pattern faithfulness (`Faithful`, the thirteenth review's
     parent-pattern agreement as a per-certificate condition) yield
     the full `SCond` for EVERY faithful unfolding: one finite check
     certifies unboundedly many step lists.  The steered-steered case
     is the manuscripts' joint steering (round-16 Q4′) made exact: the
     old pair's value enters constrained through every separator
     member by closure below the step (`fresh_tri` + the
     `closedBelow_all` induction).  Witnesses: `certC_scat` +
     `certC_faithful` reproduce `SCond certC` through the catalogue
     route; `certD_scat_violated` pins the catalogue check's failure
     to exactly the reachable row `DR` against `comp(PPI,PO)`.
 10. Round-23 (2026-07-13): the catalogue GENERATOR.  A `Catalog`
     carries templates, N2 attachment rules (child slots map to
     parent member ports, never core), and template-indexed steering;
     `buildCert` turns a plan (rule/parent choices) into a
     certificate.  `build_wellformed` and `build_faithful` prove every
     planned certificate is `Wellformed` and `Faithful` BY
     CONSTRUCTION (faithfulness by a parent-chain induction using each
     rule's port-agreement condition — the thirteenth review's
     parent-pattern lemma discharged structurally), so
     `catalogue_soundness` yields the full `SCond` for EVERY valid
     plan from `CatOk` + `PlanOk` + the catalogue check `SCat`.
     "Every unfolding of the catalogue" is now a theorem about a
     syntactic object.  Witness: `certK` (a root + one inherited-slot
     rule) drives the whole round-19..23 pipeline to `certK_scond`
     plus a closed frame, with no per-certificate proof.
 11. Round-24 (2026-07-13): the LOGIC LAYER.  `Concept` (ALCI_RCC5 in
     NNF), `sat` (semantics over an atomic frame), `Hintikka` (locally
     coherent type labellings with one-step ∃-fulfilment), and the
     `truth_lemma` (every concept in an occurrence's type is satisfied
     there).  `RCC5Interp` states the frame conditions R1/R2/R3;
     `certInterp_rcc5` proves the pipeline frame is a legitimate RCC5
     interpretation frame (from `pairVal_conv`/`pairVal_closed`/
     `pairVal_proper`).  Capstone `sat_from_hintikka`: a wellformed,
     S-conditioned certificate carrying a root-anchored Hintikka
     labelling yields an RCC5 MODEL of the target concept.
     `sample_satisfiable` is a concrete non-vacuity witness.
 12. Round-25 (2026-07-13): completeness of the Hintikka abstraction.
     `HintikkaP` (predicate labellings) + `truth_lemmaP`;
     `model_hintikkaP` (every interpretation's own satisfaction
     relation is a Hintikka labelling — the clauses ARE `sat`'s
     recursion); hence `satisfiable_iff_hintikkaP` — satisfiability and
     Hintikka-realizability COINCIDE (both directions), so the
     type-system certificate loses nothing.  `hintikka_listP` feeds
     round-24's List labellings in; `generated_satisfiable` is the
     completeness INTERFACE (a generated catalogue + a Hintikka
     labelling ⟹ a model).  `sample_satisfiable_ex` (A₀ ⊓ ∃DR.A₁ in a
     two-point DR model) exercises a REAL fulfilled existential —
     one-step, the crux the no-automata thread never discharged.
     `CompletenessObligation` STATES (not proves, not axiomatizes) the
     one remaining target: every satisfiable concept admits a FINITE
     catalogue+plan+labelling — gated by the open items F6 (width) and
     W2′ (uniformization).

  Round-20 provenance note: `doStep` was refactored (let-extraction
  into `memberPortsList`/`patternVals`/`steeringVals`, propositional
  pattern guard) -- extensionally the same fold round 19 shipped, as
  the unchanged kernel-checked witness theorems and WP34 Part B
  re-verify.
-/

namespace Round19

/-! ## 1. Atoms and the composition table -/

inductive Atom | eq | pp | ppi | po | dr
deriving DecidableEq, Repr

open Atom

def conv : Atom → Atom
  | eq => eq | pp => ppi | ppi => pp | po => po | dr => dr

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

def atoms : List Atom := [eq, pp, ppi, po, dr]
def horizontal (a : Atom) : Bool := a == dr || a == po

/-- Converse is an involution. -/
theorem conv_involution : ∀ a, conv (conv a) = a := by
  intro a; cases a <;> decide

/-- Converse closure of the table (13th review App-check, S1-style). -/
theorem comp_conv_closure :
    ∀ a b c, (c ∈ comp a b) ↔ (conv c ∈ comp (conv b) (conv a)) := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

/-- One-orientation triangle equivalence (11th/13th review checks). -/
theorem triangle_orientations :
    ∀ a b c, (c ∈ comp a b) ↔ (a ∈ comp c (conv b)) := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide

/-- Horizontal absorption (round-13 Fact 2.1 / round-15 toolkit). -/
theorem horizontal_absorption :
    ∀ a b, horizontal a → horizontal b →
      dr ∈ comp a b ∧ po ∈ comp a b := by
  intro a b; cases a <;> cases b <;> decide

/-- Vertical transitivity (round-13 Fact 2.2). -/
theorem vertical_transitivity :
    comp pp pp = [pp] ∧ comp ppi ppi = [ppi] := by decide

/-- DR-column absorption (round-15 toolkit). -/
theorem dr_column_absorption : ∀ w, dr ∈ comp w dr := by
  intro w; cases w <;> decide

/-- EQ never forced (round-13 Fact 2.4 / App-G support). -/
theorem eq_never_forced :
    ∀ a b, ¬(a = eq ∧ b = eq) → eq ∈ comp a b →
      pp ∈ comp a b ∧ ppi ∈ comp a b ∧ po ∈ comp a b := by
  intro a b; cases a <;> cases b <;> decide

/-- The S4-critical pin of defects #10/#12: composing PP with DR
    leaves exactly DR -- the fact every escaped-triangle witness used. -/
theorem s4_pin : comp pp dr = [dr] := by decide

end Round19

namespace Round19
open Atom

/-! ## 2. Certificates: occurrences, templates, canonical step lists -/

/-- An occurrence: a core index, or the j-th fresh port of the copy
    attached at step i (0-based).  Canonical order is definitional. -/
inductive Occ
  | core (i : Nat)
  | born (step : Nat) (j : Nat)
deriving DecidableEq, Repr

/-- Birth step; core occurrences are born at the base. -/
def Occ.birth : Occ → Option Nat
  | .core _ => none
  | .born s _ => some s

/-- Template ports: inherited slot k / core i / fresh j. -/
abbrev TPort := Sum Nat (Sum Nat Nat)

structure Template where
  nSlots : Nat
  nFresh : Nat
  net : TPort → TPort → Atom

/-- An attachment step in the CANONICAL list. -/
structure Step where
  tmpl : Nat
  slotTargets : List Occ

structure Cert where
  nCore : Nat
  coreNet : Nat → Nat → Atom
  templates : List Template
  steps : List Step
  /-- steering: step index, steered occurrence's core row and slot row,
      fresh port index ↦ value.  Total by type. -/
  f : Nat → (Nat → Atom) → (Nat → Atom) → Nat → Atom

def Cert.template (C : Cert) (i : Nat) : Template :=
  (C.templates.getD i ⟨0, 0, fun _ _ => Atom.dr⟩)

def Cert.step (C : Cert) (i : Nat) : Step :=
  (C.steps.getD i ⟨0, []⟩)

/-- The port of `x` inside the copy attached at step `i`, if any. -/
def memberPort (C : Cert) (i : Nat) (x : Occ) : Option TPort :=
  match x with
  | .core c => some (.inr (.inl c))
  | .born s j =>
    if s = i then some (.inr (.inr j))
    else match (C.step i).slotTargets.findIdx? (· = .born s j) with
         | some k => some (.inl k)
         | none => none

/-! ## 3. The operational unfolding (the fold) -/

abbrev Frame := List ((Occ × Occ) × Atom)

def Frame.get? (F : Frame) (x y : Occ) : Option Atom :=
  (F.find? (fun e => e.1.1 == x && e.1.2 == y)).map (·.2)

/-- All occurrences existing strictly before step i. -/
def existingBefore (C : Cert) (i : Nat) : List Occ :=
  (List.range C.nCore).map .core ++
  (List.range i).flatMap (fun s =>
    (List.range (C.template (C.step s).tmpl).nFresh).map (.born s))

def coreRowOf (C : Cert) (F : Frame) (x : Occ) : Nat → Atom :=
  fun c => match x with
    | .core c' => C.coreNet c' c
    | _ => (Frame.get? F x (.core c)).getD Atom.dr

def slotRowOf (C : Cert) (F : Frame) (i : Nat) (x : Occ) : Nat → Atom :=
  fun k => match (C.step i).slotTargets[k]? with
    | some t => (Frame.get? F x t).getD Atom.dr
    | none => Atom.dr

def portOcc (C : Cert) (i : Nat) : TPort → Occ
  | .inl k => ((C.step i).slotTargets.getD k (.core 0))
  | .inr (.inl c) => .core c
  | .inr (.inr j) => .born i j

/-- The member ports of the copy attached at step `i`: inherited slots,
    core ports, fresh ports.  (Named top-level in round-20 -- extracted
    from `doStep`'s `let`-block for proof modularity; `doStep` below is
    definitionally the same fold round-19 shipped, as the kernel-checked
    witness theorems re-verify.) -/
def memberPortsList (C : Cert) (i : Nat) : List TPort :=
  (List.range (C.template (C.step i).tmpl).nSlots).map .inl ++
  (List.range C.nCore).map (fun c => .inr (.inl c)) ++
  (List.range (C.template (C.step i).tmpl).nFresh).map (fun j => .inr (.inr j))

/-- Pattern values of step `i`: for every ordered pair of member ports
    with distinct occurrences whose pair is not already bound, the
    template's net value. -/
def patternVals (C : Cert) (F : Frame) (i : Nat) : Frame :=
  (memberPortsList C i).flatMap (fun p =>
    (memberPortsList C i).filterMap (fun q =>
      if portOcc C i p ≠ portOcc C i q ∧
         Frame.get? F (portOcc C i p) (portOcc C i q) = none
      then some ((portOcc C i p, portOcc C i q),
                 (C.template (C.step i).tmpl).net p q) else none))

/-- Steering values of step `i`: every existing non-member is steered to
    every fresh port, both orientations recorded. -/
def steeringVals (C : Cert) (F : Frame) (i : Nat) : Frame :=
  ((existingBefore C i).filter (fun x => (memberPort C i x).isNone)).flatMap
    (fun x =>
      (List.range (C.template (C.step i).tmpl).nFresh).flatMap (fun j =>
        [((x, .born i j), C.f i (coreRowOf C F x) (slotRowOf C F i x) j),
         ((.born i j, x),
          conv (C.f i (coreRowOf C F x) (slotRowOf C F i x) j))]))

/-- One attachment step: pattern values between the copy's members
    (only for pairs not already bound -- no overwrite structurally),
    then steering values from every pre-existing non-member to every
    fresh port.  The frame itself is the steering ledger. -/
def doStep (C : Cert) (F : Frame) (i : Nat) : Frame :=
  F ++ patternVals C F i ++ steeringVals C F i

/-- The operational frame: a plain left fold over the canonical step
    list.  Canonical-order determinism is definitional -- the
    thirteenth review's cure for the false order-invariance lemma. -/
def unfoldAll (C : Cert) : Frame :=
  (List.range C.steps.length).foldl (doStep C) []

end Round19

namespace Round19
open Atom

/-! ## 4. Round-18's WRITTEN update, and the source-oriented repair -/

/-- Round-18's Definition U as WRITTEN (the four-case split rejected by
    the thirteenth review), Option-valued: `none` = no clause fires.
    `parentStep` is the attachment step of the current parent copy k;
    `inParent x` decides x ∈ V_k. -/
def writtenU18 (_C : Cert) (_parentStep : Nat) (inParent : Occ → Bool)
    (x s : Occ) : Option String :=
  match s with
  | .core _ => some "U-core"
  | .born bs _ =>
    if inParent x then some "U-res"
    else match x with
      | .core _ => some "U-core-row"
      | .born bx _ =>
        if bx < bs then some "U-down@parent"   -- reads f at parentStep (!)
        else if bx > bs then some "U-flip"
        else none                               -- co-birth: NO CLAUSE

/-- The SOURCE-ORIENTED update (thirteenth review U1-U5): every value
    looked up where it was RECORDED.  Fuel-based recursion makes it
    total by construction; fuel adequacy on wellformed certificates is
    one of the stated obligations below.  Rows fed to the steering
    function are themselves source-oriented recursive calls -- the
    definition never consults the operational frame. -/
def uSourceFuel (C : Cert) : Nat → Occ → Occ → Atom
  | 0, _, _ => Atom.dr        -- fuel exhaustion (never hit when adequate)
  | _fuel+1, .core c, .core c' => C.coreNet c c'
  | _fuel+1, .core c, .born s j =>
      -- core is a member of every copy: birth-pattern value (U1/U2)
      conv ((C.template (C.step s).tmpl).net (.inr (.inr j)) (.inr (.inl c)))
  | _fuel+1, .born s j, .core c =>
      (C.template (C.step s).tmpl).net (.inr (.inr j)) (.inr (.inl c))
  | fuel+1, .born sx jx, .born ss js =>
      if sx = ss then
        -- co-birth: birth-pattern value (U2, covering defect #12's gap)
        (C.template (C.step sx).tmpl).net (.inr (.inr jx)) (.inr (.inr js))
      else if sx < ss then
        -- x older: value recorded at s's BIRTH step (U3)
        match memberPort C ss (.born sx jx) with
        | some p => (C.template (C.step ss).tmpl).net p (.inr (.inr js))
        | none =>
          C.f ss (fun c => uSourceFuel C fuel (.born sx jx) (.core c))
                 (fun k => match (C.step ss).slotTargets[k]? with
                   | some t => uSourceFuel C fuel (.born sx jx) t
                   | none => Atom.dr)   -- pad EXACTLY like slotRowOf
                 js
      else
        -- x younger: the birth flip (U4)
        conv (uSourceFuel C fuel (.born ss js) (.born sx jx))

/-- Default fuel.  Each recursion strictly decreases the lexicographic
    measure (max birth step, flip-flag): a flip preserves the max birth
    and clears the flag; a steered-row call strictly decreases the max
    birth.  Hence depth ≤ 2·steps + 2; we take a safe margin.  ROUND-20:
    fuel adequacy is now PROVED -- `uSourceFuel_irrel` shows the value
    is constant in the fuel above the explicit threshold `fuelNeed x y
    = 2·maxBirth + 1 (+1 flipped)`, which the default fuel dominates
    for all existing occurrences.  (WP34's development had caught an
    insufficient `steps + 1` bound empirically.) -/
def uSource (C : Cert) (x y : Occ) : Atom :=
  uSourceFuel C (2 * C.steps.length + 4) x y

/-! ## 5. Wellformedness and the characterization obligation -/

/-- Certificate wellformedness (17.4 port discipline + the N1/N2/N3
    normal-form skeleton).  ROUND-20 NOTE: the clauses `targets_exist`,
    `targets_length`, `net_conv` and `f_reads_rows` were FORCED by the
    characterization proof `uSource_eq_frame` below -- each was
    semantically intended all along (and honored by the WP34
    generator), but round-19's "minimal" predicate left them unstated:
    without `targets_exist`, ghost occurrences (out-of-range fresh
    indices) enter patterns; without `targets_length`, out-of-range
    slot ports alias core 0 under `portOcc`'s default; without
    `net_conv` (patterns are converse-coherent -- the R2 half of being
    a closed atomic network), the two orientations of one pattern pair
    can disagree and the birth flip is unsound; without `f_reads_rows`
    (steering reads only the actual interface rows), the steering
    function could distinguish the frame's DR-padding from template
    junk outside the interface. -/
structure Wellformed (C : Cert) : Prop where
  /-- Slot targets are BORN occurrences that pre-exist their step.
      Core occurrences are never slot targets: the core is already a
      member of every copy through its dedicated core ports (N3), and a
      core-targeting slot would give one occurrence two ports in one
      pattern, whose net columns could disagree -- a duplication defect
      the WP34 mirror harness surfaced during development. -/
  targets_preexist :
    ∀ i, i < C.steps.length →
      ∀ t ∈ (C.step i).slotTargets,
        match t with
        | .core _ => False
        | .born s _ => s < i
  /-- Slot targets are real occurrences (in-range fresh indices). -/
  targets_exist :
    ∀ i, i < C.steps.length →
      ∀ t ∈ (C.step i).slotTargets, t ∈ existingBefore C i
  /-- Exactly one target per template slot. -/
  targets_length :
    ∀ i, i < C.steps.length →
      (C.step i).slotTargets.length = (C.template (C.step i).tmpl).nSlots
  targets_injective :
    ∀ i, i < C.steps.length → (C.step i).slotTargets.Nodup
  tmpl_valid :
    ∀ i, i < C.steps.length → (C.step i).tmpl < C.templates.length
  /-- Pattern nets are converse-coherent (R2 for patterns). -/
  net_conv :
    ∀ i, i < C.steps.length → ∀ p q,
      (C.template (C.step i).tmpl).net q p
        = conv ((C.template (C.step i).tmpl).net p q)
  /-- The steering function is a function OF THE ROWS: it reads only
      in-range core columns and in-range slot columns. -/
  f_reads_rows :
    ∀ i, i < C.steps.length → ∀ r1 r1' r2 r2' j,
      (∀ c, c < C.nCore → r1 c = r1' c) →
      (∀ k, k < (C.template (C.step i).tmpl).nSlots → r2 k = r2' k) →
      C.f i r1 r2 j = C.f i r1' r2' j

/-! ### 5b. Round-20: the characterization proof

The round-19 `sorry` is discharged below.  Architecture: a plain
induction on the canonical step list (`frame_char`), resting on
  (i)   a first-match calculus for `Frame.get?` over appends,
  (ii)  the domain invariant (frame keys mention only existing
        occurrences),
  (iii) injectivity of `portOcc` on member ports (17.4 made usable),
  (iv)  fuel irrelevance for `uSourceFuel` above the explicit
        threshold `fuelNeed` -- which IS round-19's stated
        fuel-adequacy obligation, and
  (v)   the four `Wellformed` clauses the proof itself forced.
-/

theorem Frame.get?_nil (x y : Occ) : Frame.get? ([] : Frame) x y = none := rfl

theorem Frame.get?_cons (e : (Occ × Occ) × Atom) (F : Frame) (x y : Occ) :
    Frame.get? (e :: F) x y =
      if e.1.1 = x ∧ e.1.2 = y then some e.2 else Frame.get? F x y := by
  by_cases h : e.1.1 = x ∧ e.1.2 = y
  · rw [if_pos h]
    unfold Frame.get?
    rw [List.find?_cons_of_pos (by simp [h.1, h.2])]
    rfl
  · rw [if_neg h]
    unfold Frame.get?
    have hb : ¬((e.1.1 == x && e.1.2 == y) = true) := by
      intro hb
      exact h (by simpa [Bool.and_eq_true, beq_iff_eq] using hb)
    exact congrArg (Option.map fun r : (Occ × Occ) × Atom => r.2)
      (List.find?_cons_of_neg hb)

theorem get?_append_some {F G : Frame} {x y : Occ} {v : Atom}
    (h : Frame.get? F x y = some v) :
    Frame.get? (F ++ G) x y = some v := by
  induction F with
  | nil => rw [Frame.get?_nil] at h; cases h
  | cons e F ih =>
    rw [Frame.get?_cons] at h
    rw [List.cons_append, Frame.get?_cons]
    by_cases hk : e.1.1 = x ∧ e.1.2 = y
    · rwa [if_pos hk] at h ⊢
    · rw [if_neg hk] at h ⊢; exact ih h

theorem get?_append_none {F G : Frame} {x y : Occ}
    (h : Frame.get? F x y = none) :
    Frame.get? (F ++ G) x y = Frame.get? G x y := by
  induction F with
  | nil => rfl
  | cons e F ih =>
    rw [Frame.get?_cons] at h
    rw [List.cons_append, Frame.get?_cons]
    by_cases hk : e.1.1 = x ∧ e.1.2 = y
    · rw [if_pos hk] at h; cases h
    · rw [if_neg hk] at h ⊢; exact ih h

theorem get?_eq_none_of_forall {F : Frame} {x y : Occ}
    (h : ∀ e ∈ F, ¬(e.1.1 = x ∧ e.1.2 = y)) :
    Frame.get? F x y = none := by
  induction F with
  | nil => rfl
  | cons e F ih =>
    rw [Frame.get?_cons, if_neg (h e (List.mem_cons_self ..))]
    exact ih fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- First-match lookup from membership plus value-uniqueness: no
    ordering reasoning needed anywhere downstream. -/
theorem get?_of_mem_of_unique {F : Frame} {x y : Occ} {v : Atom}
    (hmem : ((x, y), v) ∈ F)
    (huniq : ∀ w, ((x, y), w) ∈ F → w = v) :
    Frame.get? F x y = some v := by
  induction F with
  | nil => cases hmem
  | cons e F ih =>
    rw [Frame.get?_cons]
    by_cases hk : e.1.1 = x ∧ e.1.2 = y
    · rw [if_pos hk]
      have he : e = ((x, y), e.2) := by
        obtain ⟨h1, h2⟩ := hk
        obtain ⟨⟨a, b⟩, w⟩ := e
        simp at h1 h2
        rw [h1, h2]
      rw [huniq e.2 (by rw [← he]; exact List.mem_cons_self ..)]
    · rw [if_neg hk]
      have hmem' : ((x, y), v) ∈ F := by
        cases List.mem_cons.mp hmem with
        | inl h => exact absurd ⟨by rw [← h], by rw [← h]⟩ hk
        | inr h => exact h
      exact ih hmem' fun w hw => huniq w (List.mem_cons_of_mem _ hw)

/-- The frame after the first `n` canonical steps. -/
def unfoldPrefix (C : Cert) (n : Nat) : Frame :=
  (List.range n).foldl (doStep C) []

theorem unfoldPrefix_succ (C : Cert) (n : Nat) :
    unfoldPrefix C (n+1) = doStep C (unfoldPrefix C n) n := by
  unfold unfoldPrefix
  rw [List.range_succ, List.foldl_append]
  rfl

theorem existingBefore_succ (C : Cert) (n : Nat) :
    existingBefore C (n+1) = existingBefore C n ++
      (List.range (C.template (C.step n).tmpl).nFresh).map (.born n) := by
  unfold existingBefore
  rw [List.range_succ, List.flatMap_append, ← List.append_assoc]
  simp

theorem mem_existingBefore_core {C : Cert} {n c : Nat} :
    Occ.core c ∈ existingBefore C n ↔ c < C.nCore := by
  simp [existingBefore]

theorem mem_existingBefore_born {C : Cert} {n s j : Nat} :
    Occ.born s j ∈ existingBefore C n ↔
      s < n ∧ j < (C.template (C.step s).tmpl).nFresh := by
  simp [existingBefore]

theorem mem_existingBefore_mono {C : Cert} {n : Nat} {x : Occ}
    (h : x ∈ existingBefore C n) : x ∈ existingBefore C (n+1) := by
  rw [existingBefore_succ]
  exact List.mem_append.mpr (Or.inl h)

/-- Fresh occurrences of step `n` do not exist before step `n`. -/
theorem fresh_not_existing {C : Cert} {n j : Nat} :
    Occ.born n j ∉ existingBefore C n := by
  intro h
  exact absurd (mem_existingBefore_born.mp h).1 (Nat.lt_irrefl n)

theorem slotPort_mem_memberPortsList {C : Cert} {i k : Nat}
    (hk : k < (C.template (C.step i).tmpl).nSlots) :
    (.inl k : TPort) ∈ memberPortsList C i := by
  unfold memberPortsList
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
    (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))))

theorem corePort_mem_memberPortsList {C : Cert} {i c : Nat}
    (hc : c < C.nCore) :
    (.inr (.inl c) : TPort) ∈ memberPortsList C i := by
  unfold memberPortsList
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
    (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩))))

theorem freshPort_mem_memberPortsList {C : Cert} {i j : Nat}
    (hj : j < (C.template (C.step i).tmpl).nFresh) :
    (.inr (.inr j) : TPort) ∈ memberPortsList C i := by
  unfold memberPortsList
  exact List.mem_append.mpr (Or.inr
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))

theorem mem_memberPortsList_elim {C : Cert} {i : Nat} {p : TPort}
    (h : p ∈ memberPortsList C i) :
    (∃ k, k < (C.template (C.step i).tmpl).nSlots ∧ p = .inl k) ∨
    (∃ c, c < C.nCore ∧ p = .inr (.inl c)) ∨
    (∃ j, j < (C.template (C.step i).tmpl).nFresh ∧ p = .inr (.inr j)) := by
  unfold memberPortsList at h
  cases List.mem_append.mp h with
  | inl h1 =>
    cases List.mem_append.mp h1 with
    | inl hs =>
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hs
      exact Or.inl ⟨k, List.mem_range.mp hk, rfl⟩
    | inr hc =>
      obtain ⟨c, hcr, rfl⟩ := List.mem_map.mp hc
      exact Or.inr (Or.inl ⟨c, List.mem_range.mp hcr, rfl⟩)
  | inr hf =>
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
    exact Or.inr (Or.inr ⟨j, List.mem_range.mp hj, rfl⟩)

/-- `findIdx?` returns an index whose element satisfies the predicate. -/
theorem findIdx?_spec {α : Type} (p : α → Bool) :
    ∀ (l : List α) (k : Nat), l.findIdx? p = some k →
      ∃ a, l[k]? = some a ∧ p a = true := by
  intro l
  induction l with
  | nil =>
    intro k h
    rw [show List.findIdx? p ([] : List α) = none from rfl] at h
    simp at h
  | cons a l ih =>
    intro k h
    rw [List.findIdx?_cons] at h
    by_cases hp : p a = true
    · rw [if_pos hp] at h
      cases h
      exact ⟨a, rfl, hp⟩
    · rw [if_neg hp] at h
      cases hfi : l.findIdx? p with
      | none => rw [hfi] at h; simp at h
      | some k' =>
        rw [hfi] at h
        simp at h
        obtain ⟨a', ha', hpa'⟩ := ih k' hfi
        subst h
        exact ⟨a', by simpa using ha', hpa'⟩

theorem findIdx?_ne_none_of_mem {α : Type} [DecidableEq α]
    {l : List α} {t : α} (h : t ∈ l) :
    l.findIdx? (· = t) ≠ none := by
  intro hn
  have := List.findIdx?_eq_none_iff.mp hn t h
  simp at this

theorem memberPort_core (C : Cert) (i c : Nat) :
    memberPort C i (.core c) = some (.inr (.inl c)) := rfl

theorem memberPort_born (C : Cert) (i s j : Nat) :
    memberPort C i (.born s j) =
      if s = i then some (.inr (.inr j))
      else match (C.step i).slotTargets.findIdx? (· = Occ.born s j) with
           | some k => some (.inl k)
           | none => none := rfl

theorem memberPort_fresh (C : Cert) (i j : Nat) :
    memberPort C i (.born i j) = some (.inr (.inr j)) := by
  rw [memberPort_born, if_pos rfl]

theorem portOcc_slot_eq {C : Cert} {i k : Nat}
    (hk : k < (C.step i).slotTargets.length) :
    portOcc C i (.inl k) = (C.step i).slotTargets[k] := by
  show (C.step i).slotTargets.getD k (.core 0) = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

/-- The target of a slot, decomposed once: born, pre-step, existing. -/
theorem target_shape {C : Cert} (hwf : Wellformed C) {i : Nat}
    (hi : i < C.steps.length) {t : Occ}
    (ht : t ∈ (C.step i).slotTargets) :
    ∃ s j, t = .born s j ∧ s < i := by
  have hb := hwf.targets_preexist i hi t ht
  cases t with
  | core c => exact hb.elim
  | born s j => exact ⟨s, j, rfl, hb⟩

theorem memberPort_isSome_of_target {C : Cert} (hwf : Wellformed C)
    {i : Nat} (hi : i < C.steps.length) {t : Occ}
    (ht : t ∈ (C.step i).slotTargets) : (memberPort C i t).isSome := by
  obtain ⟨s, j, rfl, hs⟩ := target_shape hwf hi ht
  rw [memberPort_born, if_neg (by omega : ¬s = i)]
  cases hfi : (C.step i).slotTargets.findIdx? (· = Occ.born s j) with
  | none => exact absurd hfi (findIdx?_ne_none_of_mem ht)
  | some k => rfl

/-- What a member port certifies: list membership and `portOcc`
    inversion. -/
theorem memberPort_spec {C : Cert} (hwf : Wellformed C) {i : Nat}
    (hi : i < C.steps.length) {x : Occ} {p : TPort}
    (hx : x ∈ existingBefore C i) (h : memberPort C i x = some p) :
    p ∈ memberPortsList C i ∧ portOcc C i p = x := by
  cases x with
  | core c =>
    rw [memberPort_core] at h
    cases h
    exact ⟨corePort_mem_memberPortsList (mem_existingBefore_core.mp hx), rfl⟩
  | born s j =>
    have hs : s < i := (mem_existingBefore_born.mp hx).1
    rw [memberPort_born, if_neg (by omega : ¬s = i)] at h
    cases hfi : (C.step i).slotTargets.findIdx? (· = Occ.born s j) with
    | none => rw [hfi] at h; simp at h
    | some k =>
      rw [hfi] at h
      injection h with h
      subst h
      obtain ⟨a, hak, hpa⟩ := findIdx?_spec _ _ _ hfi
      have hae : a = Occ.born s j := by simpa using hpa
      subst hae
      obtain ⟨hklen, hgk⟩ := List.getElem?_eq_some_iff.mp hak
      constructor
      · apply slotPort_mem_memberPortsList
        rw [← hwf.targets_length i hi]
        exact hklen
      · rw [portOcc_slot_eq hklen, hgk]

/-- `portOcc` of a member port is an existing occurrence (of the next
    stage). -/
theorem portOcc_mem_existing {C : Cert} (hwf : Wellformed C) {i : Nat}
    (hi : i < C.steps.length) {p : TPort} (hp : p ∈ memberPortsList C i) :
    portOcc C i p ∈ existingBefore C (i+1) := by
  cases mem_memberPortsList_elim hp with
  | inl h =>
    obtain ⟨k, hk, rfl⟩ := h
    have hklen : k < (C.step i).slotTargets.length := by
      rw [hwf.targets_length i hi]; exact hk
    rw [portOcc_slot_eq hklen]
    exact mem_existingBefore_mono
      (hwf.targets_exist i hi _ (List.getElem_mem hklen))
  | inr h =>
    cases h with
    | inl hc =>
      obtain ⟨c, hc, rfl⟩ := hc
      exact mem_existingBefore_core.mpr hc
    | inr hf =>
      obtain ⟨j, hj, rfl⟩ := hf
      exact mem_existingBefore_born.mpr ⟨Nat.lt_succ_self i, hj⟩

/-- Injectivity of `portOcc` on member ports (the usable form of the
    17.4 discipline). -/
theorem portOcc_inj {C : Cert} (hwf : Wellformed C) {i : Nat}
    (hi : i < C.steps.length) {p q : TPort}
    (hp : p ∈ memberPortsList C i) (hq : q ∈ memberPortsList C i)
    (heq : portOcc C i p = portOcc C i q) : p = q := by
  have hlen := hwf.targets_length i hi
  cases mem_memberPortsList_elim hp with
  | inl hks =>
    obtain ⟨k, hk, rfl⟩ := hks
    have hk' : k < (C.step i).slotTargets.length := by rw [hlen]; exact hk
    rw [portOcc_slot_eq hk'] at heq
    obtain ⟨s, j, htk, hsi⟩ :=
      target_shape hwf hi (List.getElem_mem hk')
    cases mem_memberPortsList_elim hq with
    | inl hks2 =>
      obtain ⟨k2, hk2, rfl⟩ := hks2
      have hk2' : k2 < (C.step i).slotTargets.length := by
        rw [hlen]; exact hk2
      rw [portOcc_slot_eq hk2'] at heq
      by_cases hkk : k = k2
      · rw [hkk]
      · exfalso
        have hnd := hwf.targets_injective i hi
        cases Nat.lt_or_ge k k2 with
        | inl hlt =>
          exact (List.pairwise_iff_getElem.mp hnd k k2 hk' hk2' hlt) heq
        | inr hge =>
          have hlt : k2 < k := Nat.lt_of_le_of_ne hge fun h => hkk h.symm
          exact (List.pairwise_iff_getElem.mp hnd k2 k hk2' hk' hlt) heq.symm
    | inr h2 =>
      cases h2 with
      | inl hc =>
        obtain ⟨c, _, rfl⟩ := hc
        rw [htk] at heq
        exact Occ.noConfusion heq
      | inr hf =>
        obtain ⟨j2, _, rfl⟩ := hf
        rw [htk] at heq
        injection heq with h1 _
        omega
  | inr h1 =>
    cases h1 with
    | inl hc =>
      obtain ⟨c, _, rfl⟩ := hc
      cases mem_memberPortsList_elim hq with
      | inl hks2 =>
        obtain ⟨k2, hk2, rfl⟩ := hks2
        have hk2' : k2 < (C.step i).slotTargets.length := by
          rw [hlen]; exact hk2
        rw [portOcc_slot_eq hk2'] at heq
        obtain ⟨s, j, htk, _⟩ :=
          target_shape hwf hi (List.getElem_mem hk2')
        rw [htk] at heq
        exact Occ.noConfusion heq
      | inr h2 =>
        cases h2 with
        | inl hc2 =>
          obtain ⟨c2, _, rfl⟩ := hc2
          have : c = c2 := by
            have h3 : Occ.core c = Occ.core c2 := heq
            injection h3
          rw [this]
        | inr hf2 =>
          obtain ⟨j2, _, rfl⟩ := hf2
          exact Occ.noConfusion heq
    | inr hf =>
      obtain ⟨j, _, rfl⟩ := hf
      cases mem_memberPortsList_elim hq with
      | inl hks2 =>
        obtain ⟨k2, hk2, rfl⟩ := hks2
        have hk2' : k2 < (C.step i).slotTargets.length := by
          rw [hlen]; exact hk2
        rw [portOcc_slot_eq hk2'] at heq
        obtain ⟨s, j2, htk, hsi⟩ :=
          target_shape hwf hi (List.getElem_mem hk2')
        rw [htk] at heq
        injection heq with h1 _
        omega
      | inr h2 =>
        cases h2 with
        | inl hc2 =>
          obtain ⟨c2, _, rfl⟩ := hc2
          exact Occ.noConfusion heq
        | inr hf2 =>
          obtain ⟨j2, _, rfl⟩ := hf2
          have : j = j2 := by
            have h3 : Occ.born i j = Occ.born i j2 := heq
            injection h3 with _ h4
          rw [this]

/-- Every member port's occurrence is a member (`memberPort` finds a
    port for it). -/
theorem memberPort_portOcc_isSome {C : Cert} (hwf : Wellformed C)
    {i : Nat} (hi : i < C.steps.length) {p : TPort}
    (hp : p ∈ memberPortsList C i) :
    (memberPort C i (portOcc C i p)).isSome := by
  cases mem_memberPortsList_elim hp with
  | inl h =>
    obtain ⟨k, hk, rfl⟩ := h
    have hk' : k < (C.step i).slotTargets.length := by
      rw [hwf.targets_length i hi]; exact hk
    rw [portOcc_slot_eq hk']
    exact memberPort_isSome_of_target hwf hi (List.getElem_mem hk')
  | inr h =>
    cases h with
    | inl hc =>
      obtain ⟨c, _, rfl⟩ := hc
      rw [show portOcc C i (.inr (.inl c)) = Occ.core c from rfl,
          memberPort_core]
      rfl
    | inr hf =>
      obtain ⟨j, _, rfl⟩ := hf
      rw [show portOcc C i (.inr (.inr j)) = Occ.born i j from rfl,
          memberPort_fresh]
      rfl

theorem mem_patternVals {C : Cert} {F : Frame} {i : Nat}
    {e : (Occ × Occ) × Atom} :
    e ∈ patternVals C F i ↔
      ∃ p, p ∈ memberPortsList C i ∧ ∃ q, q ∈ memberPortsList C i ∧
        portOcc C i p ≠ portOcc C i q ∧
        Frame.get? F (portOcc C i p) (portOcc C i q) = none ∧
        e = ((portOcc C i p, portOcc C i q),
             (C.template (C.step i).tmpl).net p q) := by
  unfold patternVals
  rw [List.mem_flatMap]
  constructor
  · intro h
    obtain ⟨p, hp, he⟩ := h
    rw [List.mem_filterMap] at he
    obtain ⟨q, hq, hfq⟩ := he
    by_cases hc : portOcc C i p ≠ portOcc C i q ∧
        Frame.get? F (portOcc C i p) (portOcc C i q) = none
    · rw [if_pos hc] at hfq
      injection hfq with hfq
      exact ⟨p, hp, q, hq, hc.1, hc.2, hfq.symm⟩
    · rw [if_neg hc] at hfq
      cases hfq
  · intro h
    obtain ⟨p, hp, q, hq, hne, hnone, he⟩ := h
    exact ⟨p, hp, List.mem_filterMap.mpr
      ⟨q, hq, by rw [if_pos ⟨hne, hnone⟩, he]⟩⟩

theorem mem_steeringVals {C : Cert} {F : Frame} {i : Nat}
    {e : (Occ × Occ) × Atom} :
    e ∈ steeringVals C F i ↔
      ∃ x, x ∈ existingBefore C i ∧ memberPort C i x = none ∧
        ∃ j, j < (C.template (C.step i).tmpl).nFresh ∧
          (e = ((x, .born i j),
                C.f i (coreRowOf C F x) (slotRowOf C F i x) j) ∨
           e = ((.born i j, x),
                conv (C.f i (coreRowOf C F x) (slotRowOf C F i x) j))) := by
  unfold steeringVals
  rw [List.mem_flatMap]
  constructor
  · intro h
    obtain ⟨x, hx, he⟩ := h
    rw [List.mem_filter] at hx
    rw [List.mem_flatMap] at he
    obtain ⟨j, hj, he2⟩ := he
    refine ⟨x, hx.1, Option.isNone_iff_eq_none.mp hx.2, j,
            List.mem_range.mp hj, ?_⟩
    cases List.mem_cons.mp he2 with
    | inl h1 => exact Or.inl h1
    | inr h1 =>
      cases List.mem_cons.mp h1 with
      | inl h2 => exact Or.inr h2
      | inr h2 => cases h2
  · intro h
    obtain ⟨x, hx, hmp, j, hj, hor⟩ := h
    refine ⟨x, List.mem_filter.mpr
      ⟨hx, Option.isNone_iff_eq_none.mpr hmp⟩, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨j, List.mem_range.mpr hj, ?_⟩
    cases hor with
    | inl h1 => rw [h1]; exact List.mem_cons_self ..
    | inr h1 => rw [h1]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

/-- Domain invariant: frame keys mention only existing occurrences. -/
theorem unfoldPrefix_keys {C : Cert} (hwf : Wellformed C) :
    ∀ n, n ≤ C.steps.length →
      ∀ e ∈ unfoldPrefix C n,
        e.1.1 ∈ existingBefore C n ∧ e.1.2 ∈ existingBefore C n := by
  intro n
  induction n with
  | zero => intro _ e he; cases he
  | succ n ih =>
    intro hn e he
    have hn' : n < C.steps.length := Nat.lt_of_succ_le hn
    rw [unfoldPrefix_succ] at he
    unfold doStep at he
    cases List.mem_append.mp he with
    | inl hFP =>
      cases List.mem_append.mp hFP with
      | inl hF =>
        have h2 := ih (Nat.le_of_lt hn') e hF
        exact ⟨mem_existingBefore_mono h2.1, mem_existingBefore_mono h2.2⟩
      | inr hP =>
        obtain ⟨p, hp, q, hq, _, _, rfl⟩ := mem_patternVals.mp hP
        exact ⟨portOcc_mem_existing hwf hn' hp,
               portOcc_mem_existing hwf hn' hq⟩
    | inr hS =>
      obtain ⟨x, hx, _, j, hj, hor⟩ := mem_steeringVals.mp hS
      cases hor with
      | inl h1 =>
        rw [h1]
        exact ⟨mem_existingBefore_mono hx,
               mem_existingBefore_born.mpr ⟨Nat.lt_succ_self n, hj⟩⟩
      | inr h1 =>
        rw [h1]
        exact ⟨mem_existingBefore_born.mpr ⟨Nat.lt_succ_self n, hj⟩,
               mem_existingBefore_mono hx⟩

theorem get?_prefix_none_left {C : Cert} (hwf : Wellformed C) {n : Nat}
    (hn : n ≤ C.steps.length) {x y : Occ}
    (hx : x ∉ existingBefore C n) :
    Frame.get? (unfoldPrefix C n) x y = none :=
  get?_eq_none_of_forall fun e he hxy =>
    hx (hxy.1 ▸ (unfoldPrefix_keys hwf n hn e he).1)

theorem get?_prefix_none_right {C : Cert} (hwf : Wellformed C) {n : Nat}
    (hn : n ≤ C.steps.length) {x y : Occ}
    (hy : y ∉ existingBefore C n) :
    Frame.get? (unfoldPrefix C n) x y = none :=
  get?_eq_none_of_forall fun e he hxy =>
    hy (hxy.2 ▸ (unfoldPrefix_keys hwf n hn e he).2)

/-! #### Fuel irrelevance (round-19's fuel-adequacy obligation) -/

/-- The exact fuel threshold: `2·maxBirth + 1`, plus one on the flipped
    (younger-first) born-born orientation. -/
def fuelNeed : Occ → Occ → Nat
  | .core _, .core _ => 1
  | .core _, .born s _ => 2 * s + 1
  | .born s _, .core _ => 2 * s + 1
  | .born sx _, .born ss _ => 2 * max sx ss + 1 + (if ss < sx then 1 else 0)

theorem fuelNeed_pos (x y : Occ) : 1 ≤ fuelNeed x y := by
  cases x <;> cases y <;> simp [fuelNeed] <;> omega

/-- The born-born unfolding of `uSourceFuel`, one layer. -/
theorem uSourceFuel_born_born (C : Cert) (fuel sx jx ss js : Nat) :
    uSourceFuel C (fuel+1) (.born sx jx) (.born ss js) =
      if sx = ss then
        (C.template (C.step sx).tmpl).net (.inr (.inr jx)) (.inr (.inr js))
      else if sx < ss then
        match memberPort C ss (.born sx jx) with
        | some p => (C.template (C.step ss).tmpl).net p (.inr (.inr js))
        | none =>
          C.f ss (fun c => uSourceFuel C fuel (.born sx jx) (.core c))
                 (fun k => match (C.step ss).slotTargets[k]? with
                   | some t => uSourceFuel C fuel (.born sx jx) t
                   | none => Atom.dr)
                 js
      else conv (uSourceFuel C fuel (.born ss js) (.born sx jx)) := rfl

/-- Fuel irrelevance above the threshold: `uSourceFuel` is constant in
    the fuel once it exceeds `fuelNeed`.  This is the round-19
    fuel-adequacy obligation, discharged.  (Wellformedness is needed:
    the recursion descends through slot targets, whose births are
    bounded by `targets_preexist`.) -/
theorem uSourceFuel_irrel (C : Cert) (hwf : Wellformed C) :
    ∀ m x y, fuelNeed x y ≤ m →
      (∀ s j, x = .born s j → s < C.steps.length) →
      (∀ s j, y = .born s j → s < C.steps.length) →
      ∀ f₁ f₂, fuelNeed x y ≤ f₁ → fuelNeed x y ≤ f₂ →
        uSourceFuel C f₁ x y = uSourceFuel C f₂ x y := by
  intro m
  induction m with
  | zero =>
    intro x y hm _ _
    have := fuelNeed_pos x y
    omega
  | succ m ih =>
    intro x y hm hxs hys f₁ f₂ h1 h2
    have hpos := fuelNeed_pos x y
    cases f₁ with
    | zero => omega
    | succ g₁ =>
      cases f₂ with
      | zero => omega
      | succ g₂ =>
        cases x with
        | core c =>
          cases y with
          | core c' => rfl
          | born s j => rfl
        | born sx jx =>
          cases y with
          | core c => rfl
          | born ss js =>
            rw [uSourceFuel_born_born, uSourceFuel_born_born]
            by_cases hss : sx = ss
            · rw [if_pos hss, if_pos hss]
            · rw [if_neg hss, if_neg hss]
              by_cases hlt : sx < ss
              · rw [if_pos hlt, if_pos hlt]
                cases hmp : memberPort C ss (.born sx jx) with
                | some p => rfl
                | none =>
                  have hss_len : ss < C.steps.length := hys ss js rfl
                  have hm' : 2 * ss + 1 ≤ m + 1 := by
                    simp only [fuelNeed] at hm
                    rw [Nat.max_eq_right (Nat.le_of_lt hlt),
                        if_neg (by omega : ¬ss < sx)] at hm
                    omega
                  have hg₁ : 2 * ss + 1 ≤ g₁ + 1 := by
                    simp only [fuelNeed] at h1
                    rw [Nat.max_eq_right (Nat.le_of_lt hlt),
                        if_neg (by omega : ¬ss < sx)] at h1
                    omega
                  have hg₂ : 2 * ss + 1 ≤ g₂ + 1 := by
                    simp only [fuelNeed] at h2
                    rw [Nat.max_eq_right (Nat.le_of_lt hlt),
                        if_neg (by omega : ¬ss < sx)] at h2
                    omega
                  have hcrow :
                      (fun c => uSourceFuel C g₁ (.born sx jx) (.core c))
                        = fun c => uSourceFuel C g₂ (.born sx jx) (.core c) := by
                    funext c
                    exact ih (.born sx jx) (.core c)
                      (by simp only [fuelNeed]; omega)
                      hxs (fun s j h => Occ.noConfusion h)
                      g₁ g₂
                      (by simp only [fuelNeed]; omega)
                      (by simp only [fuelNeed]; omega)
                  have hsrow :
                      (fun k : Nat => match (C.step ss).slotTargets[k]? with
                        | some t => uSourceFuel C g₁ (.born sx jx) t
                        | none => Atom.dr)
                        = fun k : Nat => match (C.step ss).slotTargets[k]? with
                        | some t => uSourceFuel C g₂ (.born sx jx) t
                        | none => Atom.dr := by
                    funext k
                    cases htk : (C.step ss).slotTargets[k]? with
                    | none => rfl
                    | some t =>
                      obtain ⟨hklen, hgk⟩ := List.getElem?_eq_some_iff.mp htk
                      obtain ⟨st, jt, hteq, hst⟩ :=
                        target_shape hwf hss_len (hgk ▸ List.getElem_mem hklen)
                      subst hteq
                      have hb : fuelNeed (.born sx jx) (.born st jt)
                          ≤ 2 * ss := by
                        simp only [fuelNeed]
                        have hmx : max sx st ≤ ss - 1 :=
                          Nat.max_le.mpr ⟨by omega, by omega⟩
                        split <;> omega
                      exact ih (.born sx jx) (.born st jt)
                        (by omega) hxs
                        (fun s j h => by
                          injection h with hh1 _
                          omega)
                        g₁ g₂ (by omega) (by omega)
                  rw [hcrow, hsrow]
              · have hgt : ss < sx := by omega
                rw [if_neg hlt, if_neg hlt]
                have hm' : 2 * sx + 2 ≤ m + 1 := by
                  simp only [fuelNeed] at hm
                  rw [Nat.max_eq_left (Nat.le_of_lt hgt), if_pos hgt] at hm
                  omega
                have hg₁ : 2 * sx + 2 ≤ g₁ + 1 := by
                  simp only [fuelNeed] at h1
                  rw [Nat.max_eq_left (Nat.le_of_lt hgt), if_pos hgt] at h1
                  omega
                have hg₂ : 2 * sx + 2 ≤ g₂ + 1 := by
                  simp only [fuelNeed] at h2
                  rw [Nat.max_eq_left (Nat.le_of_lt hgt), if_pos hgt] at h2
                  omega
                have hflip : fuelNeed (.born ss js) (.born sx jx)
                    = 2 * sx + 1 := by
                  simp only [fuelNeed]
                  rw [Nat.max_eq_right (Nat.le_of_lt hgt),
                      if_neg (by omega : ¬sx < ss)]
                rw [ih (.born ss js) (.born sx jx)
                  (by omega) hys hxs g₁ g₂ (by omega) (by omega)]

/-! #### The master induction -/

/-- Round-20 master theorem: after `n` canonical steps the operational
    frame agrees with the source-oriented update on every distinct
    existing non-core-core pair. -/
theorem frame_char (C : Cert) (hwf : Wellformed C) :
    ∀ n, n ≤ C.steps.length → ∀ x y : Occ, x ≠ y →
      (∀ c c', ¬(x = .core c ∧ y = .core c')) →
      x ∈ existingBefore C n → y ∈ existingBefore C n →
      Frame.get? (unfoldPrefix C n) x y = some (uSource C x y) := by
  intro n
  induction n with
  | zero =>
    intro _ x y _ hcc hx hy
    exfalso
    cases x with
    | born s j =>
      exact absurd (mem_existingBefore_born.mp hx).1 (Nat.not_lt_zero s)
    | core c =>
      cases y with
      | born s j =>
        exact absurd (mem_existingBefore_born.mp hy).1 (Nat.not_lt_zero s)
      | core c' => exact hcc c c' ⟨rfl, rfl⟩
  | succ n ih =>
    intro hlen x y hxy hcc hx hy
    have hn : n < C.steps.length := Nat.lt_of_succ_le hlen
    have hnle : n ≤ C.steps.length := Nat.le_of_lt hn
    rw [unfoldPrefix_succ]
    unfold doStep
    rw [existingBefore_succ] at hx hy
    cases List.mem_append.mp hx with
    | inl hxo =>
      cases List.mem_append.mp hy with
      | inl hyo =>
        -- CASE A: both old.  IH plus first-match monotonicity.
        exact get?_append_some (get?_append_some
          (ih hnle x y hxy hcc hxo hyo))
      | inr hyf =>
        -- CASE B: x old, y fresh at step n.
        obtain ⟨jy, hjyr, heq⟩ := List.mem_map.mp hyf
        have hjy : jy < (C.template (C.step n).tmpl).nFresh :=
          List.mem_range.mp hjyr
        subst heq
        have hFnone : Frame.get? (unfoldPrefix C n) x (.born n jy) = none :=
          get?_prefix_none_right hwf hnle fresh_not_existing
        cases hmp : memberPort C n x with
        | some p =>
          -- B1: x is a member; the pair receives the pattern value.
          obtain ⟨hpmem, hpocc⟩ := memberPort_spec hwf hn hxo hmp
          have hqmem : (.inr (.inr jy) : TPort) ∈ memberPortsList C n :=
            freshPort_mem_memberPortsList hjy
          have hmemP : ((x, Occ.born n jy),
              (C.template (C.step n).tmpl).net p (.inr (.inr jy)))
              ∈ patternVals C (unfoldPrefix C n) n := by
            rw [mem_patternVals]
            refine ⟨p, hpmem, .inr (.inr jy), hqmem, ?_, ?_, ?_⟩
            · rw [hpocc]; exact hxy
            · rw [hpocc]; exact hFnone
            · rw [hpocc]; rfl
          have huniqP : ∀ w, ((x, Occ.born n jy), w)
              ∈ patternVals C (unfoldPrefix C n) n →
              w = (C.template (C.step n).tmpl).net p (.inr (.inr jy)) := by
            intro w hw
            rw [mem_patternVals] at hw
            obtain ⟨p', hp', q', hq', _, _, heq'⟩ := hw
            simp only [Prod.mk.injEq] at heq'
            obtain ⟨⟨hxp, hyq⟩, hw'⟩ := heq'
            have hp'eq : p' = p :=
              portOcc_inj hwf hn hp' hpmem (hxp.symm.trans hpocc.symm)
            have hq'eq : q' = (.inr (.inr jy) : TPort) :=
              portOcc_inj hwf hn hq' hqmem hyq.symm
            rw [hw', hp'eq, hq'eq]
          have hVal : Frame.get?
              (unfoldPrefix C n ++ patternVals C (unfoldPrefix C n) n
                ++ steeringVals C (unfoldPrefix C n) n) x (.born n jy)
              = some ((C.template (C.step n).tmpl).net p (.inr (.inr jy))) :=
            get?_append_some (by
              rw [get?_append_none hFnone]
              exact get?_of_mem_of_unique hmemP huniqP)
          rw [hVal]
          congr 1
          cases x with
          | core c =>
            have hp_eq : p = .inr (.inl c) := by
              have h2 := (memberPort_core C n c).symm.trans hmp
              injection h2 with h3
              exact h3.symm
            subst hp_eq
            rw [show uSource C (.core c) (.born n jy)
                = conv ((C.template (C.step n).tmpl).net
                    (.inr (.inr jy)) (.inr (.inl c))) from rfl]
            exact hwf.net_conv n hn _ _
          | born sx jx =>
            have hsx : sx < n := (mem_existingBefore_born.mp hxo).1
            rw [show uSource C (.born sx jx) (.born n jy)
                = uSourceFuel C ((2*C.steps.length+3)+1)
                    (.born sx jx) (.born n jy) from rfl,
              uSourceFuel_born_born, if_neg (by omega : ¬sx = n),
              if_pos hsx, hmp]
        | none =>
          -- B2: x is steered; the pair receives the steering value.
          cases x with
          | core c => rw [memberPort_core] at hmp; simp at hmp
          | born sx jx =>
            have hsx : sx < n := (mem_existingBefore_born.mp hxo).1
            have hPnone : Frame.get? (patternVals C (unfoldPrefix C n) n)
                (.born sx jx) (.born n jy) = none := by
              apply get?_eq_none_of_forall
              intro e he hkey
              rw [mem_patternVals] at he
              obtain ⟨p', hp', q', hq', _, _, rfl⟩ := he
              have hsome := memberPort_portOcc_isSome hwf hn hp'
              have h1 : portOcc C n p' = Occ.born sx jx := hkey.1
              rw [h1, hmp] at hsome
              simp at hsome
            have hmemS : ((Occ.born sx jx, Occ.born n jy),
                C.f n (coreRowOf C (unfoldPrefix C n) (.born sx jx))
                      (slotRowOf C (unfoldPrefix C n) n (.born sx jx)) jy)
                ∈ steeringVals C (unfoldPrefix C n) n := by
              rw [mem_steeringVals]
              exact ⟨.born sx jx, hxo, hmp, jy, hjy, Or.inl rfl⟩
            have huniqS : ∀ w, ((Occ.born sx jx, Occ.born n jy), w)
                ∈ steeringVals C (unfoldPrefix C n) n →
                w = C.f n (coreRowOf C (unfoldPrefix C n) (.born sx jx))
                      (slotRowOf C (unfoldPrefix C n) n (.born sx jx)) jy := by
              intro w hw
              rw [mem_steeringVals] at hw
              obtain ⟨x', hx', _, j', _, hor⟩ := hw
              cases hor with
              | inl h1 =>
                simp only [Prod.mk.injEq] at h1
                obtain ⟨⟨hxx, hjj⟩, hww⟩ := h1
                injection hjj with _ hj2
                rw [hww, ← hxx, ← hj2]
              | inr h1 =>
                exfalso
                simp only [Prod.mk.injEq] at h1
                injection h1.1.1 with h4 _
                omega
            have hFPn : Frame.get?
                (unfoldPrefix C n ++ patternVals C (unfoldPrefix C n) n)
                (.born sx jx) (.born n jy) = none := by
              rw [get?_append_none hFnone]
              exact hPnone
            have hVal : Frame.get?
                (unfoldPrefix C n ++ patternVals C (unfoldPrefix C n) n
                  ++ steeringVals C (unfoldPrefix C n) n)
                (.born sx jx) (.born n jy)
                = some (C.f n (coreRowOf C (unfoldPrefix C n) (.born sx jx))
                    (slotRowOf C (unfoldPrefix C n) n (.born sx jx)) jy) := by
              rw [get?_append_none hFPn]
              exact get?_of_mem_of_unique hmemS huniqS
            rw [hVal]
            congr 1
            -- uSource unfolds to the U3 steering clause:
            rw [show uSource C (.born sx jx) (.born n jy)
                = uSourceFuel C ((2*C.steps.length+3)+1)
                    (.born sx jx) (.born n jy) from rfl,
              uSourceFuel_born_born, if_neg (by omega : ¬sx = n),
              if_pos hsx, hmp]
            -- rows agree in range; f reads only rows:
            apply hwf.f_reads_rows n hn
            · intro c hc
              have hcm : Occ.core c ∈ existingBefore C n :=
                mem_existingBefore_core.mpr hc
              have hne : (Occ.born sx jx) ≠ Occ.core c :=
                fun h => Occ.noConfusion h
              have hP := ih hnle (.born sx jx) (.core c) hne
                (fun c1 c2 h => Occ.noConfusion h.1) hxo hcm
              show (Frame.get? (unfoldPrefix C n)
                  (.born sx jx) (.core c)).getD Atom.dr = _
              rw [hP]
              rfl
            · intro k _
              show (match (C.step n).slotTargets[k]? with
                    | some t => (Frame.get? (unfoldPrefix C n)
                        (.born sx jx) t).getD Atom.dr
                    | none => Atom.dr) = _
              cases htk : (C.step n).slotTargets[k]? with
              | none => rfl
              | some t =>
                obtain ⟨hklen, hgk⟩ := List.getElem?_eq_some_iff.mp htk
                have htmem : t ∈ (C.step n).slotTargets :=
                  hgk ▸ List.getElem_mem hklen
                obtain ⟨st, jt, hteq, hst⟩ := target_shape hwf hn htmem
                subst hteq
                have htex := hwf.targets_exist n hn _ htmem
                have hne2 : (Occ.born sx jx) ≠ (Occ.born st jt) := by
                  intro h
                  have hs2 := memberPort_isSome_of_target hwf hn htmem
                  rw [← h, hmp] at hs2
                  simp at hs2
                have hP := ih hnle (.born sx jx) (.born st jt) hne2
                  (fun c1 c2 h => Occ.noConfusion h.1) hxo htex
                show ((unfoldPrefix C n).get? (Occ.born sx jx)
                    (Occ.born st jt)).getD Atom.dr
                  = uSourceFuel C (2*C.steps.length+3) (Occ.born sx jx)
                      (Occ.born st jt)
                rw [hP]
                show uSource C (.born sx jx) (.born st jt) = _
                have hfn : fuelNeed (.born sx jx) (.born st jt)
                    ≤ 2 * C.steps.length + 3 := by
                  simp only [fuelNeed]
                  have hmx : max sx st ≤ C.steps.length :=
                    Nat.max_le.mpr ⟨by omega, by omega⟩
                  split <;> omega
                exact uSourceFuel_irrel C hwf (2*C.steps.length+4)
                  (.born sx jx) (.born st jt) (by omega)
                  (fun s j h => by injection h with hh _; omega)
                  (fun s j h => by injection h with hh _; omega)
                  _ _ (by omega) (by omega)
    | inr hxf =>
      -- x fresh at step n.
      obtain ⟨jx, hjxr, heqx⟩ := List.mem_map.mp hxf
      have hjx : jx < (C.template (C.step n).tmpl).nFresh :=
        List.mem_range.mp hjxr
      subst heqx
      have hFnone : Frame.get? (unfoldPrefix C n) (.born n jx) y = none :=
        get?_prefix_none_left hwf hnle fresh_not_existing
      cases List.mem_append.mp hy with
      | inl hyo =>
        -- CASE C: x fresh, y old.
        cases hmp : memberPort C n y with
        | some q =>
          -- C1: y is a member; pattern value, flipped by net_conv.
          obtain ⟨hqmem, hqocc⟩ := memberPort_spec hwf hn hyo hmp
          have hpmem : (.inr (.inr jx) : TPort) ∈ memberPortsList C n :=
            freshPort_mem_memberPortsList hjx
          have hmemP : ((Occ.born n jx, y),
              (C.template (C.step n).tmpl).net (.inr (.inr jx)) q)
              ∈ patternVals C (unfoldPrefix C n) n := by
            rw [mem_patternVals]
            refine ⟨.inr (.inr jx), hpmem, q, hqmem, ?_, ?_, ?_⟩
            · rw [hqocc]; exact hxy
            · rw [hqocc]; exact hFnone
            · rw [hqocc]; rfl
          have huniqP : ∀ w, ((Occ.born n jx, y), w)
              ∈ patternVals C (unfoldPrefix C n) n →
              w = (C.template (C.step n).tmpl).net (.inr (.inr jx)) q := by
            intro w hw
            rw [mem_patternVals] at hw
            obtain ⟨p', hp', q', hq', _, _, heq'⟩ := hw
            simp only [Prod.mk.injEq] at heq'
            obtain ⟨⟨hxp, hyq⟩, hw'⟩ := heq'
            have hp'eq : p' = (.inr (.inr jx) : TPort) :=
              portOcc_inj hwf hn hp' hpmem hxp.symm
            have hq'eq : q' = q :=
              portOcc_inj hwf hn hq' hqmem (hyq.symm.trans hqocc.symm)
            rw [hw', hp'eq, hq'eq]
          have hVal : Frame.get?
              (unfoldPrefix C n ++ patternVals C (unfoldPrefix C n) n
                ++ steeringVals C (unfoldPrefix C n) n) (.born n jx) y
              = some ((C.template (C.step n).tmpl).net (.inr (.inr jx)) q) :=
            get?_append_some (by
              rw [get?_append_none hFnone]
              exact get?_of_mem_of_unique hmemP huniqP)
          rw [hVal]
          congr 1
          cases y with
          | core c =>
            have hq_eq : q = .inr (.inl c) := by
              have h2 := (memberPort_core C n c).symm.trans hmp
              injection h2 with h3
              exact h3.symm
            subst hq_eq
            rfl
          | born sy jy =>
            have hsy : sy < n := (mem_existingBefore_born.mp hyo).1
            rw [show uSource C (.born n jx) (.born sy jy)
                = uSourceFuel C ((2*C.steps.length+3)+1)
                    (.born n jx) (.born sy jy) from rfl,
              uSourceFuel_born_born, if_neg (by omega : ¬n = sy),
              if_neg (by omega : ¬n < sy),
              show (2*C.steps.length+3 : Nat) = (2*C.steps.length+2)+1
                from rfl,
              uSourceFuel_born_born, if_neg (by omega : ¬sy = n),
              if_pos hsy, hmp]
            exact hwf.net_conv n hn _ _
        | none =>
          -- C2: y is steered; the reverse orientation carries conv.
          cases y with
          | core c => rw [memberPort_core] at hmp; simp at hmp
          | born sy jy =>
            have hsy : sy < n := (mem_existingBefore_born.mp hyo).1
            have hPnone : Frame.get? (patternVals C (unfoldPrefix C n) n)
                (.born n jx) (.born sy jy) = none := by
              apply get?_eq_none_of_forall
              intro e he hkey
              rw [mem_patternVals] at he
              obtain ⟨p', hp', q', hq', _, _, rfl⟩ := he
              have hsome := memberPort_portOcc_isSome hwf hn hq'
              have h1 : portOcc C n q' = Occ.born sy jy := hkey.2
              rw [h1, hmp] at hsome
              simp at hsome
            have hmemS : ((Occ.born n jx, Occ.born sy jy),
                conv (C.f n (coreRowOf C (unfoldPrefix C n) (.born sy jy))
                      (slotRowOf C (unfoldPrefix C n) n (.born sy jy)) jx))
                ∈ steeringVals C (unfoldPrefix C n) n := by
              rw [mem_steeringVals]
              exact ⟨.born sy jy, hyo, hmp, jx, hjx, Or.inr rfl⟩
            have huniqS : ∀ w, ((Occ.born n jx, Occ.born sy jy), w)
                ∈ steeringVals C (unfoldPrefix C n) n →
                w = conv (C.f n
                      (coreRowOf C (unfoldPrefix C n) (.born sy jy))
                      (slotRowOf C (unfoldPrefix C n) n (.born sy jy)) jx) := by
              intro w hw
              rw [mem_steeringVals] at hw
              obtain ⟨x', hx', _, j', _, hor⟩ := hw
              cases hor with
              | inl h1 =>
                exfalso
                simp only [Prod.mk.injEq] at h1
                injection h1.1.2 with h4 _
                omega
              | inr h1 =>
                simp only [Prod.mk.injEq] at h1
                obtain ⟨⟨hbb, hxx⟩, hww⟩ := h1
                injection hbb with _ hj2
                rw [hww, ← hxx, ← hj2]
            have hFPn : Frame.get?
                (unfoldPrefix C n ++ patternVals C (unfoldPrefix C n) n)
                (.born n jx) (.born sy jy) = none := by
              rw [get?_append_none hFnone]
              exact hPnone
            have hVal : Frame.get?
                (unfoldPrefix C n ++ patternVals C (unfoldPrefix C n) n
                  ++ steeringVals C (unfoldPrefix C n) n)
                (.born n jx) (.born sy jy)
                = some (conv (C.f n
                    (coreRowOf C (unfoldPrefix C n) (.born sy jy))
                    (slotRowOf C (unfoldPrefix C n) n (.born sy jy)) jx)) := by
              rw [get?_append_none hFPn]
              exact get?_of_mem_of_unique hmemS huniqS
            rw [hVal]
            congr 1
            rw [show uSource C (.born n jx) (.born sy jy)
                = uSourceFuel C ((2*C.steps.length+3)+1)
                    (.born n jx) (.born sy jy) from rfl,
              uSourceFuel_born_born, if_neg (by omega : ¬n = sy),
              if_neg (by omega : ¬n < sy)]
            congr 1
            rw [show (2*C.steps.length+3 : Nat) = (2*C.steps.length+2)+1
                from rfl,
              uSourceFuel_born_born, if_neg (by omega : ¬sy = n),
              if_pos hsy, hmp]
            apply hwf.f_reads_rows n hn
            · intro c hc
              have hcm : Occ.core c ∈ existingBefore C n :=
                mem_existingBefore_core.mpr hc
              have hne : (Occ.born sy jy) ≠ Occ.core c :=
                fun h => Occ.noConfusion h
              have hP := ih hnle (.born sy jy) (.core c) hne
                (fun c1 c2 h => Occ.noConfusion h.1) hyo hcm
              show (Frame.get? (unfoldPrefix C n)
                  (.born sy jy) (.core c)).getD Atom.dr = _
              rw [hP]
              rfl
            · intro k _
              show (match (C.step n).slotTargets[k]? with
                    | some t => (Frame.get? (unfoldPrefix C n)
                        (.born sy jy) t).getD Atom.dr
                    | none => Atom.dr) = _
              cases htk : (C.step n).slotTargets[k]? with
              | none => rfl
              | some t =>
                obtain ⟨hklen, hgk⟩ := List.getElem?_eq_some_iff.mp htk
                have htmem : t ∈ (C.step n).slotTargets :=
                  hgk ▸ List.getElem_mem hklen
                obtain ⟨st, jt, hteq, hst⟩ := target_shape hwf hn htmem
                subst hteq
                have htex := hwf.targets_exist n hn _ htmem
                have hne2 : (Occ.born sy jy) ≠ (Occ.born st jt) := by
                  intro h
                  have hs2 := memberPort_isSome_of_target hwf hn htmem
                  rw [← h, hmp] at hs2
                  simp at hs2
                have hP := ih hnle (.born sy jy) (.born st jt) hne2
                  (fun c1 c2 h => Occ.noConfusion h.1) hyo htex
                show ((unfoldPrefix C n).get? (Occ.born sy jy)
                    (Occ.born st jt)).getD Atom.dr
                  = uSourceFuel C (2*C.steps.length+2) (Occ.born sy jy)
                      (Occ.born st jt)
                rw [hP]
                show uSource C (.born sy jy) (.born st jt) = _
                have hfn : fuelNeed (.born sy jy) (.born st jt)
                    ≤ 2 * C.steps.length + 2 := by
                  simp only [fuelNeed]
                  have hmx : max sy st ≤ C.steps.length :=
                    Nat.max_le.mpr ⟨by omega, by omega⟩
                  split <;> omega
                exact uSourceFuel_irrel C hwf (2*C.steps.length+4)
                  (.born sy jy) (.born st jt) (by omega)
                  (fun s j h => by injection h with hh _; omega)
                  (fun s j h => by injection h with hh _; omega)
                  _ _ (by omega) (by omega)
      | inr hyf =>
        -- CASE D: both fresh at step n (co-birth).
        obtain ⟨jy, hjyr, heqy⟩ := List.mem_map.mp hyf
        have hjy : jy < (C.template (C.step n).tmpl).nFresh :=
          List.mem_range.mp hjyr
        subst heqy
        have hpmem : (.inr (.inr jx) : TPort) ∈ memberPortsList C n :=
          freshPort_mem_memberPortsList hjx
        have hqmem : (.inr (.inr jy) : TPort) ∈ memberPortsList C n :=
          freshPort_mem_memberPortsList hjy
        have hmemP : ((Occ.born n jx, Occ.born n jy),
            (C.template (C.step n).tmpl).net (.inr (.inr jx)) (.inr (.inr jy)))
            ∈ patternVals C (unfoldPrefix C n) n := by
          rw [mem_patternVals]
          exact ⟨.inr (.inr jx), hpmem, .inr (.inr jy), hqmem,
                 hxy, hFnone, rfl⟩
        have huniqP : ∀ w, ((Occ.born n jx, Occ.born n jy), w)
            ∈ patternVals C (unfoldPrefix C n) n →
            w = (C.template (C.step n).tmpl).net
                  (.inr (.inr jx)) (.inr (.inr jy)) := by
          intro w hw
          rw [mem_patternVals] at hw
          obtain ⟨p', hp', q', hq', _, _, heq'⟩ := hw
          simp only [Prod.mk.injEq] at heq'
          obtain ⟨⟨hxp, hyq⟩, hw'⟩ := heq'
          have hp'eq : p' = (.inr (.inr jx) : TPort) :=
            portOcc_inj hwf hn hp' hpmem hxp.symm
          have hq'eq : q' = (.inr (.inr jy) : TPort) :=
            portOcc_inj hwf hn hq' hqmem hyq.symm
          rw [hw', hp'eq, hq'eq]
        have hVal : Frame.get?
            (unfoldPrefix C n ++ patternVals C (unfoldPrefix C n) n
              ++ steeringVals C (unfoldPrefix C n) n)
            (.born n jx) (.born n jy)
            = some ((C.template (C.step n).tmpl).net
                (.inr (.inr jx)) (.inr (.inr jy))) :=
          get?_append_some (by
            rw [get?_append_none hFnone]
            exact get?_of_mem_of_unique hmemP huniqP)
        rw [hVal]
        congr 1
        rw [show uSource C (.born n jx) (.born n jy)
            = uSourceFuel C ((2*C.steps.length+3)+1)
                (.born n jx) (.born n jy) from rfl,
          uSourceFuel_born_born, if_pos rfl]

/-- THE former mechanization frontier, now a theorem (round-20): on
    wellformed certificates the source-oriented update agrees with the
    operational frame on all distinct existing occurrences.  This is
    the exact statement rounds 17 and 18 failed to render in prose --
    here it is proved by `frame_char`'s induction on the canonical
    step list, with fuel adequacy discharged by `uSourceFuel_irrel`. -/
theorem uSource_eq_frame (C : Cert) (hwf : Wellformed C) :
    ∀ x y, x ≠ y →
      x ∈ existingBefore C C.steps.length →
      y ∈ existingBefore C C.steps.length →
      (∀ c c', ¬(x = .core c ∧ y = .core c')) →   -- core-core lives in coreNet
      Frame.get? (unfoldAll C) x y = some (uSource C x y) := by
  intro x y hxy hx hy hcc
  exact frame_char C hwf C.steps.length (Nat.le_refl _) x y hxy hcc hx hy

/-! ## 6. The thirteenth review's witnesses, kernel-checked -/

/-- Witness A geometry: step 0 births x = born 0 0 and a = born 0 1
    with pattern value x PP a; step 1 inherits ONLY a (slot 0) and
    births b = born 1 0. -/
def certA : Cert where
  nCore := 0
  coreNet := fun _ _ => Atom.dr
  templates :=
    [ ⟨0, 2, fun p q =>
        match p, q with
        | .inr (.inr 0), .inr (.inr 1) => Atom.pp
        | .inr (.inr 1), .inr (.inr 0) => Atom.ppi
        | _, _ => Atom.eq⟩,
      ⟨1, 1, fun p q =>
        match p, q with
        | .inl 0, .inr (.inr 0) => Atom.ppi   -- a PPI b (b PP a)
        | .inr (.inr 0), .inl 0 => Atom.pp
        | _, _ => Atom.eq⟩ ]
  steps := [⟨0, []⟩, ⟨1, [.born 0 1]⟩]
  f := fun _ _ _ _ => Atom.dr   -- steering: DR everywhere (legal here)

/-- Defect #12, kernel-checked: at a child of the copy that inherited
    `a`, round-18's WRITTEN case split fires NO clause for the co-birth
    pair (x, a) -- x is not a member of that copy, and b(x) = b(a). -/
theorem defect12_written_gap :
    writtenU18 certA 1 (fun x => (memberPort certA 1 x).isSome)
      (.born 0 0) (.born 0 1) = none := by native_decide

/-- The repair covers it: the source-oriented update returns the
    birth-pattern value ... -/
theorem repair_covers_cobirth :
    uSource certA (.born 0 0) (.born 0 1) = Atom.pp := by native_decide

/-- ... and it agrees with the operational frame on this pair. -/
theorem repair_matches_frame_on_witnessA :
    Frame.get? (unfoldAll certA) (.born 0 0) (.born 0 1)
      = some (uSource certA (.born 0 0) (.born 0 1)) := by native_decide

/-- Witness-B skeleton: `a` (born at step 1) is NOT fresh at step 2 --
    it enters through a slot -- so a "current-parent steering row"
    lookup for it is vacuous; the correct source is its birth step.
    Here: the source-oriented value for an older x equals the recorded
    steering value at a's birth (f ≡ DR in certB). -/
def certB : Cert where
  nCore := 0
  coreNet := fun _ _ => Atom.dr
  templates :=
    [ ⟨0, 1, fun _ _ => Atom.eq⟩,
      ⟨0, 1, fun _ _ => Atom.eq⟩,
      ⟨1, 1, fun p q =>
        match p, q with
        | .inl 0, .inr (.inr 0) => Atom.ppi
        | .inr (.inr 0), .inl 0 => Atom.pp
        | _, _ => Atom.eq⟩ ]
  steps := [⟨0, []⟩, ⟨1, []⟩, ⟨2, [.born 1 0]⟩]
  f := fun _ _ _ _ => Atom.dr

theorem witnessB_source_is_birth_step :
    uSource certB (.born 0 0) (.born 1 0) = Atom.dr ∧
    Frame.get? (unfoldAll certB) (.born 0 0) (.born 1 0)
      = some Atom.dr ∧
    (memberPort certB 2 (.born 1 0) = some (.inl 0)) := by native_decide

end Round19

namespace Round19
open Atom

/-! ## 7. Non-vacuity of `Wellformed` (round-20)

`certC` satisfies every `Wellformed` clause -- including the four
round-20 additions -- and exercises the inherited-slot path (its step-1
copy inherits `born 0 0`).  Constant-`DR` pattern nets make `net_conv`
definitional (`conv dr = dr`), and a constant steering function makes
`f_reads_rows` definitional. -/

def certC : Cert where
  nCore := 0
  coreNet := fun _ _ => Atom.dr
  templates :=
    [ ⟨0, 2, fun _ _ => Atom.dr⟩,
      ⟨1, 1, fun _ _ => Atom.dr⟩ ]
  steps := [⟨0, []⟩, ⟨1, [.born 0 0]⟩]
  f := fun _ _ _ _ => Atom.dr

theorem certC_wellformed : Wellformed certC := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- targets_preexist
    intro i hi t ht
    match i with
    | 0 => cases ht
    | 1 =>
      cases ht with
      | head => exact Nat.zero_lt_one
      | tail _ h => cases h
    | n+2 =>
      have h2 : certC.steps.length = 2 := rfl
      omega
  · -- targets_exist
    intro i hi t ht
    match i with
    | 0 => cases ht
    | 1 =>
      cases ht with
      | head => decide
      | tail _ h => cases h
    | n+2 =>
      have h2 : certC.steps.length = 2 := rfl
      omega
  · -- targets_length
    intro i hi
    match i with
    | 0 => rfl
    | 1 => rfl
    | n+2 =>
      have h2 : certC.steps.length = 2 := rfl
      omega
  · -- targets_injective
    intro i hi
    match i with
    | 0 => exact List.Pairwise.nil
    | 1 => decide
    | n+2 =>
      have h2 : certC.steps.length = 2 := rfl
      omega
  · -- tmpl_valid
    intro i hi
    match i with
    | 0 => decide
    | 1 => decide
    | n+2 =>
      have h2 : certC.steps.length = 2 := rfl
      omega
  · -- net_conv: all nets are constant DR and conv dr = dr
    intro i hi p q
    match i with
    | 0 => rfl
    | 1 => rfl
    | n+2 =>
      have h2 : certC.steps.length = 2 := rfl
      omega
  · -- f_reads_rows: f is constant
    intro i hi r1 r1' r2 r2' j h1 h2
    rfl

/-- The characterization theorem fires end to end on a concrete
    wellformed certificate with an inherited slot. -/
example : Frame.get? (unfoldAll certC) (.born 0 1) (.born 1 0)
    = some (uSource certC (.born 0 1) (.born 1 0)) :=
  uSource_eq_frame certC certC_wellformed _ _
    (by decide) (by decide) (by decide)
    (fun c c' h => Occ.noConfusion h.1)

end Round19

namespace Round19
open Atom

/-! ## 8. Round-21: the S-layer — converse coherence, S-conditions,
    and the closure theorem

The soundness kernel of rounds 15-18, in the kernel: a certificate
whose steering satisfies the S-condition (`SCond`, the manuscripts'
S4 on certificate-computable values) unfolds to a composition-closed,
converse-coherent, EQ-free frame.  WP30 Part C and WP32 Part C checked
this empirically (S4-valid steering ⟹ closed unfoldings, 100/100 and
150/150); here it is a theorem.  The negative direction is also
kernel-checked: `certD` below violates the S-condition and its frame
provably breaks closure — WP32's adversarial control as a theorem. -/

/-- Rotation of closed triangles, first form: if `u` labels `x→y`,
    `v` labels `x→z`, `w` labels `z→y` consistently, the same three
    points witness `v ∈ comp u (conv w)`. -/
theorem comp_rot1 : ∀ u v w : Atom, u ∈ comp v w → v ∈ comp u (conv w) := by
  intro u v w
  cases u <;> cases v <;> cases w <;> decide

/-- Rotation of closed triangles, second form. -/
theorem comp_rot2 : ∀ u v w : Atom, u ∈ comp v w → w ∈ comp (conv v) u := by
  intro u v w
  cases u <;> cases v <;> cases w <;> decide

/-- Converse coherence of the source-oriented update (R2 for
    `uSource`): definitional in every clause except the two that cross
    a fuel boundary, which `uSourceFuel_irrel` bridges. -/
theorem uSource_conv (C : Cert) (hwf : Wellformed C) :
    ∀ x y : Occ, x ≠ y →
      (∀ s j, x = .born s j → s < C.steps.length) →
      (∀ s j, y = .born s j → s < C.steps.length) →
      (∀ c c', ¬(x = .core c ∧ y = .core c')) →
      uSource C y x = conv (uSource C x y) := by
  intro x y hxy hxs hys hcc
  cases x with
  | core c =>
    cases y with
    | core c' => exact absurd ⟨rfl, rfl⟩ (hcc c c')
    | born s j =>
      show (C.template (C.step s).tmpl).net (.inr (.inr j)) (.inr (.inl c))
        = conv (conv ((C.template (C.step s).tmpl).net
            (.inr (.inr j)) (.inr (.inl c))))
      exact (conv_involution _).symm
  | born sx jx =>
    cases y with
    | core c => rfl
    | born ss js =>
      obtain hlt | heq | hgt := Nat.lt_trichotomy sx ss
      · -- x older: (y,x) is the flip of (x,y)
        have hsl : ss < C.steps.length := hys ss js rfl
        have hb : fuelNeed (.born sx jx) (.born ss js)
            ≤ 2 * C.steps.length + 3 := by
          simp only [fuelNeed]
          rw [Nat.max_eq_right (Nat.le_of_lt hlt),
              if_neg (by omega : ¬ss < sx)]
          omega
        rw [show uSource C (.born ss js) (.born sx jx)
            = uSourceFuel C ((2*C.steps.length+3)+1)
                (.born ss js) (.born sx jx) from rfl,
          uSourceFuel_born_born, if_neg (by omega : ¬ss = sx),
          if_neg (by omega : ¬ss < sx)]
        show conv (uSourceFuel C (2*C.steps.length+3)
            (.born sx jx) (.born ss js)) = _
        congr 1
        exact uSourceFuel_irrel C hwf (2*C.steps.length+4)
          (.born sx jx) (.born ss js) (by omega) hxs hys
          _ _ (by omega) (by omega)
      · -- co-birth: both directions are pattern values; net_conv
        subst heq
        have hsl : sx < C.steps.length := hxs sx jx rfl
        rw [show uSource C (.born sx js) (.born sx jx)
            = uSourceFuel C ((2*C.steps.length+3)+1)
                (.born sx js) (.born sx jx) from rfl,
          uSourceFuel_born_born, if_pos rfl,
          show uSource C (.born sx jx) (.born sx js)
            = uSourceFuel C ((2*C.steps.length+3)+1)
                (.born sx jx) (.born sx js) from rfl,
          uSourceFuel_born_born, if_pos rfl]
        exact hwf.net_conv sx hsl _ _
      · -- y older: (x,y) is the flip of (y,x)
        have hsl : sx < C.steps.length := hxs sx jx rfl
        have hb : fuelNeed (.born ss js) (.born sx jx)
            ≤ 2 * C.steps.length + 3 := by
          simp only [fuelNeed]
          rw [Nat.max_eq_right (Nat.le_of_lt hgt),
              if_neg (by omega : ¬sx < ss)]
          omega
        rw [show uSource C (.born sx jx) (.born ss js)
            = uSourceFuel C ((2*C.steps.length+3)+1)
                (.born sx jx) (.born ss js) from rfl,
          uSourceFuel_born_born, if_neg (by omega : ¬sx = ss),
          if_neg (by omega : ¬sx < ss), conv_involution]
        exact uSourceFuel_irrel C hwf (2*C.steps.length+4)
          (.born ss js) (.born sx jx) (by omega) hys hxs
          _ _ (by omega) (by omega)

/-- The realized pair value of a certificate: core-core pairs read the
    core net, all others the source-oriented update.  This is the
    total network the S-condition constrains. -/
def pairVal (C : Cert) : Occ → Occ → Atom
  | .core c, .core c' => C.coreNet c c'
  | .core c, .born s j => uSource C (.core c) (.born s j)
  | .born s j, y => uSource C (.born s j) y

/-- The S-condition (the manuscripts' S4, on certificate-computable
    values): the core net is converse-coherent, proper and closed;
    template core rows agree with it (N3); and at every step, every
    triangle through a fresh occurrence is composition-closed and
    every fresh pair is EQ-free.  All fields are finitely checkable on
    a concrete certificate (the two unbounded core fields become
    range-bounded or vacuous once `nCore` is fixed). -/
structure SCond (C : Cert) : Prop where
  core_conv : ∀ c c', C.coreNet c' c = conv (C.coreNet c c')
  core_proper : ∀ c c', c < C.nCore → c' < C.nCore → c ≠ c' →
    C.coreNet c c' ≠ Atom.eq
  core_closed : ∀ c1 c2 c3, c1 < C.nCore → c2 < C.nCore → c3 < C.nCore →
    c1 ≠ c2 → c1 ≠ c3 → c3 ≠ c2 →
    C.coreNet c1 c2 ∈ comp (C.coreNet c1 c3) (C.coreNet c3 c2)
  core_rows : ∀ i, i < C.steps.length → ∀ c c', c < C.nCore → c' < C.nCore →
    c ≠ c' →
    (C.template (C.step i).tmpl).net (.inr (.inl c)) (.inr (.inl c'))
      = C.coreNet c c'
  tri : ∀ i, i < C.steps.length →
    ∀ x ∈ existingBefore C (i+1), ∀ y ∈ existingBefore C (i+1),
    ∀ jz, jz < (C.template (C.step i).tmpl).nFresh →
    x ≠ y → x ≠ .born i jz → y ≠ .born i jz →
    pairVal C x y ∈ comp (pairVal C x (.born i jz))
                         (pairVal C (.born i jz) y)
  pair_proper : ∀ i, i < C.steps.length →
    ∀ x ∈ existingBefore C (i+1),
    ∀ jz, jz < (C.template (C.step i).tmpl).nFresh →
    x ≠ .born i jz → pairVal C x (.born i jz) ≠ Atom.eq

/-- Birth bounds from membership in the full unfolding. -/
theorem birthBound {C : Cert} {x : Occ}
    (hx : x ∈ existingBefore C C.steps.length) :
    ∀ s j, x = .born s j → s < C.steps.length := by
  intro s j h
  subst h
  exact (mem_existingBefore_born.mp hx).1

/-- Membership transfers down to any stage past the birth. -/
theorem mem_downgrade {C : Cert} {x : Occ}
    (hx : x ∈ existingBefore C C.steps.length) (i : Nat)
    (hb : ∀ s j, x = .born s j → s ≤ i) :
    x ∈ existingBefore C (i+1) := by
  cases x with
  | core c => exact mem_existingBefore_core.mpr (mem_existingBefore_core.mp hx)
  | born s j =>
    have h2 := mem_existingBefore_born.mp hx
    exact mem_existingBefore_born.mpr ⟨Nat.lt_succ_of_le (hb s j rfl), h2.2⟩

/-- Converse coherence of the realized network. -/
theorem pairVal_conv (C : Cert) (hwf : Wellformed C)
    (hcc : ∀ c c', C.coreNet c' c = conv (C.coreNet c c'))
    {x y : Occ} (hxy : x ≠ y)
    (hxs : ∀ s j, x = .born s j → s < C.steps.length)
    (hys : ∀ s j, y = .born s j → s < C.steps.length) :
    pairVal C y x = conv (pairVal C x y) := by
  cases x with
  | core c =>
    cases y with
    | core c' => exact hcc c c'
    | born s j =>
      show uSource C (.born s j) (.core c)
        = conv (uSource C (.core c) (.born s j))
      exact uSource_conv C hwf _ _ hxy hxs hys
        (fun c1 c2 h => Occ.noConfusion h.2)
  | born s j =>
    cases y with
    | core c =>
      show uSource C (.core c) (.born s j)
        = conv (uSource C (.born s j) (.core c))
      exact uSource_conv C hwf _ _ hxy hxs hys
        (fun c1 c2 h => Occ.noConfusion h.1)
    | born s' j' =>
      show uSource C (.born s' j') (.born s j)
        = conv (uSource C (.born s j) (.born s' j'))
      exact uSource_conv C hwf _ _ hxy hxs hys
        (fun c1 c2 h => Occ.noConfusion h.1)

end Round19

namespace Round19
open Atom

/-! ### The closure theorem on the realized network -/

/-- The per-step triangle condition (the body of `SCond.tri` at one
    step); round-22 derives it from the catalogue-level check. -/
def TriAt (C : Cert) (i : Nat) : Prop :=
  ∀ x ∈ existingBefore C (i+1), ∀ y ∈ existingBefore C (i+1),
  ∀ jz, jz < (C.template (C.step i).tmpl).nFresh →
  x ≠ y → x ≠ .born i jz → y ≠ .born i jz →
  pairVal C x y ∈ comp (pairVal C x (.born i jz))
                       (pairVal C (.born i jz) y)

/-- Route 1: the fresh occurrence is the middle element. -/
theorem route_direct {C : Cert} {i jc : Nat} (htri : TriAt C i)
    (hjc : jc < (C.template (C.step i).tmpl).nFresh)
    {a b : Occ} (ha : a ∈ existingBefore C (i+1))
    (hb : b ∈ existingBefore C (i+1))
    (hab : a ≠ b) (hac : a ≠ .born i jc) (hbc : b ≠ .born i jc) :
    pairVal C a b ∈ comp (pairVal C a (.born i jc))
                         (pairVal C (.born i jc) b) :=
  htri a ha b hb jc hjc hab hac hbc

/-- Route 2: the fresh occurrence sits in the third position; rotate
    with `comp_rot1` and converse coherence. -/
theorem route_rotb {C : Cert} (hwf : Wellformed C)
    (hcc : ∀ c c', C.coreNet c' c = conv (C.coreNet c c'))
    {i jb : Nat} (hi : i < C.steps.length) (htri : TriAt C i)
    (hjb : jb < (C.template (C.step i).tmpl).nFresh)
    {a c : Occ} (ha : a ∈ existingBefore C (i+1))
    (hc : c ∈ existingBefore C (i+1))
    (hac : a ≠ c) (hab : a ≠ .born i jb) (hcb : c ≠ .born i jb)
    (hcs : ∀ s j, c = .born s j → s < C.steps.length) :
    pairVal C a (.born i jb) ∈ comp (pairVal C a c)
                                    (pairVal C c (.born i jb)) := by
  have h := htri a ha c hc jb hjb hac hab hcb
  have h2 := comp_rot1 _ _ _ h
  rwa [show conv (pairVal C (.born i jb) c) = pairVal C c (.born i jb) from
    (pairVal_conv C hwf hcc (fun h3 => hcb h3.symm)
      (fun s j h3 => by injection h3 with h4 _; omega) hcs).symm] at h2

/-- Route 3: the fresh occurrence sits in the first position; rotate
    with `comp_rot2` and converse coherence. -/
theorem route_rota {C : Cert} (hwf : Wellformed C)
    (hcc : ∀ c c', C.coreNet c' c = conv (C.coreNet c c'))
    {i ja : Nat} (hi : i < C.steps.length) (htri : TriAt C i)
    (hja : ja < (C.template (C.step i).tmpl).nFresh)
    {b c : Occ} (hb : b ∈ existingBefore C (i+1))
    (hc : c ∈ existingBefore C (i+1))
    (hcb : c ≠ b) (hca : c ≠ .born i ja) (hba : b ≠ .born i ja)
    (hcs : ∀ s j, c = .born s j → s < C.steps.length) :
    pairVal C (.born i ja) b ∈ comp (pairVal C (.born i ja) c)
                                    (pairVal C c b) := by
  have h := htri c hc b hb ja hja hcb hca hba
  have h2 := comp_rot2 _ _ _ h
  rwa [show conv (pairVal C c (.born i ja)) = pairVal C (.born i ja) c from
    (pairVal_conv C hwf hcc hca hcs
      (fun s j h3 => by injection h3 with h4 _; omega)).symm] at h2

/-- The realized network of an S-conditioned certificate is
    composition-closed on all distinct existing triples. -/
theorem pairVal_closed (C : Cert) (hwf : Wellformed C) (hs : SCond C) :
    ∀ a b c : Occ,
      a ∈ existingBefore C C.steps.length →
      b ∈ existingBefore C C.steps.length →
      c ∈ existingBefore C C.steps.length →
      a ≠ b → a ≠ c → c ≠ b →
      pairVal C a b ∈ comp (pairVal C a c) (pairVal C c b) := by
  intro a b c ha hb hc hab hac hcb
  cases c with
  | born sc jc =>
    have hcd := mem_existingBefore_born.mp hc
    cases a with
    | core ca =>
      cases b with
      | core cb =>
        exact route_direct (hs.tri sc hcd.1) hcd.2
          (mem_existingBefore_core.mpr (mem_existingBefore_core.mp ha))
          (mem_existingBefore_core.mpr (mem_existingBefore_core.mp hb))
          hab hac hcb.symm
      | born sb jb =>
        have hbd := mem_existingBefore_born.mp hb
        by_cases hbs : sb ≤ sc
        · exact route_direct (hs.tri sc hcd.1) hcd.2
            (mem_existingBefore_core.mpr (mem_existingBefore_core.mp ha))
            (mem_downgrade hb sc (fun s j h => by injection h with h1 _; omega))
            hab hac hcb.symm
        · exact route_rotb hwf hs.core_conv hbd.1 (hs.tri sb hbd.1) hbd.2
            (mem_existingBefore_core.mpr (mem_existingBefore_core.mp ha))
            (mem_downgrade hc sb (fun s j h => by injection h with h1 _; omega))
            hac hab hcb (birthBound hc)
    | born sa ja =>
      have had := mem_existingBefore_born.mp ha
      cases b with
      | core cb =>
        by_cases has : sa ≤ sc
        · exact route_direct (hs.tri sc hcd.1) hcd.2
            (mem_downgrade ha sc (fun s j h => by injection h with h1 _; omega))
            (mem_existingBefore_core.mpr (mem_existingBefore_core.mp hb))
            hab hac hcb.symm
        · exact route_rota hwf hs.core_conv had.1 (hs.tri sa had.1) had.2
            (mem_existingBefore_core.mpr (mem_existingBefore_core.mp hb))
            (mem_downgrade hc sa (fun s j h => by injection h with h1 _; omega))
            hcb (fun h => hac h.symm) (fun h => hab h.symm) (birthBound hc)
      | born sb jb =>
        have hbd := mem_existingBefore_born.mp hb
        by_cases hasc : sa ≤ sc
        · by_cases hbsc : sb ≤ sc
          · exact route_direct (hs.tri sc hcd.1) hcd.2
              (mem_downgrade ha sc (fun s j h => by injection h with h1 _; omega))
              (mem_downgrade hb sc (fun s j h => by injection h with h1 _; omega))
              hab hac hcb.symm
          · exact route_rotb hwf hs.core_conv hbd.1 (hs.tri sb hbd.1) hbd.2
              (mem_downgrade ha sb (fun s j h => by injection h with h1 _; omega))
              (mem_downgrade hc sb (fun s j h => by injection h with h1 _; omega))
              hac hab hcb (birthBound hc)
        · by_cases habs : sa ≤ sb
          · exact route_rotb hwf hs.core_conv hbd.1 (hs.tri sb hbd.1) hbd.2
              (mem_downgrade ha sb (fun s j h => by injection h with h1 _; omega))
              (mem_downgrade hc sb (fun s j h => by injection h with h1 _; omega))
              hac hab hcb (birthBound hc)
          · exact route_rota hwf hs.core_conv had.1 (hs.tri sa had.1) had.2
              (mem_downgrade hb sa (fun s j h => by injection h with h1 _; omega))
              (mem_downgrade hc sa (fun s j h => by injection h with h1 _; omega))
              hcb (fun h => hac h.symm) (fun h => hab h.symm) (birthBound hc)
  | core cc =>
    cases a with
    | core ca =>
      cases b with
      | core cb =>
        have h1 := mem_existingBefore_core.mp ha
        have h2 := mem_existingBefore_core.mp hb
        have h3 := mem_existingBefore_core.mp hc
        exact hs.core_closed ca cb cc h1 h2 h3
          (fun h => hab (congrArg Occ.core h))
          (fun h => hac (congrArg Occ.core h))
          (fun h => hcb (congrArg Occ.core h))
      | born sb jb =>
        have hbd := mem_existingBefore_born.mp hb
        exact route_rotb hwf hs.core_conv hbd.1 (hs.tri sb hbd.1) hbd.2
          (mem_existingBefore_core.mpr (mem_existingBefore_core.mp ha))
          (mem_existingBefore_core.mpr (mem_existingBefore_core.mp hc))
          hac hab hcb (birthBound hc)
    | born sa ja =>
      have had := mem_existingBefore_born.mp ha
      cases b with
      | core cb =>
        exact route_rota hwf hs.core_conv had.1 (hs.tri sa had.1) had.2
          (mem_existingBefore_core.mpr (mem_existingBefore_core.mp hb))
          (mem_existingBefore_core.mpr (mem_existingBefore_core.mp hc))
          hcb (fun h => hac h.symm) (fun h => hab h.symm) (birthBound hc)
      | born sb jb =>
        have hbd := mem_existingBefore_born.mp hb
        by_cases habs : sa ≤ sb
        · exact route_rotb hwf hs.core_conv hbd.1 (hs.tri sb hbd.1) hbd.2
            (mem_downgrade ha sb (fun s j h => by injection h with h1 _; omega))
            (mem_existingBefore_core.mpr (mem_existingBefore_core.mp hc))
            hac hab hcb (birthBound hc)
        · exact route_rota hwf hs.core_conv had.1 (hs.tri sa had.1) had.2
            (mem_downgrade hb sa (fun s j h => by injection h with h1 _; omega))
            (mem_existingBefore_core.mpr (mem_existingBefore_core.mp hc))
            hcb (fun h => hac h.symm) (fun h => hab h.symm) (birthBound hc)

/-- The realized network is EQ-free on distinct pairs (strong-EQ
    discipline: EQ is identity, so distinct occurrences never carry
    it). -/
theorem pairVal_proper (C : Cert) (hwf : Wellformed C) (hs : SCond C) :
    ∀ x y : Occ,
      x ∈ existingBefore C C.steps.length →
      y ∈ existingBefore C C.steps.length →
      x ≠ y → pairVal C x y ≠ Atom.eq := by
  intro x y hx hy hxy
  have hconvroute :
      ∀ {a b : Occ}, a ∈ existingBefore C C.steps.length →
        b ∈ existingBefore C C.steps.length → a ≠ b →
        pairVal C b a ≠ Atom.eq → pairVal C a b ≠ Atom.eq := by
    intro a b ha hb hab hba h
    apply hba
    rw [pairVal_conv C hwf hs.core_conv hab (birthBound ha)
          (birthBound hb), h]
    rfl
  cases x with
  | core cx =>
    cases y with
    | core cy =>
      exact hs.core_proper cx cy (mem_existingBefore_core.mp hx)
        (mem_existingBefore_core.mp hy)
        (fun h => hxy (congrArg Occ.core h))
    | born sy jy =>
      have hyd := mem_existingBefore_born.mp hy
      exact hs.pair_proper sy hyd.1 (.core cx)
        (mem_existingBefore_core.mpr (mem_existingBefore_core.mp hx))
        jy hyd.2 hxy
  | born sx jx =>
    have hxd := mem_existingBefore_born.mp hx
    cases y with
    | core cy =>
      exact hconvroute hx hy hxy
        (hs.pair_proper sx hxd.1 (.core cy)
          (mem_existingBefore_core.mpr (mem_existingBefore_core.mp hy))
          jx hxd.2 (fun h => hxy h.symm))
    | born sy jy =>
      have hyd := mem_existingBefore_born.mp hy
      by_cases hxs : sx ≤ sy
      · exact hs.pair_proper sy hyd.1 (.born sx jx)
          (mem_downgrade hx sy (fun s j h => by injection h with h1 _; omega))
          jy hyd.2 hxy
      · exact hconvroute hx hy hxy
          (hs.pair_proper sx hxd.1 (.born sy jy)
            (mem_downgrade hy sx (fun s j h => by injection h with h1 _; omega))
            jx hxd.2 (fun h => hxy h.symm))

end Round19

namespace Round19
open Atom

/-! ### Transport to the operational frame -/

theorem get?_some_mem {F : Frame} {x y : Occ} {v : Atom}
    (h : Frame.get? F x y = some v) : ((x, y), v) ∈ F := by
  unfold Frame.get? at h
  cases hf : F.find? (fun e => e.1.1 == x && e.1.2 == y) with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    have hmem := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    injection h with h
    obtain ⟨⟨a, b⟩, w⟩ := e
    simp only at hp h
    rw [← hp.1, ← hp.2, ← h]
    exact hmem

theorem get?_append_cases {F G : Frame} {x y : Occ} {v : Atom}
    (h : Frame.get? (F ++ G) x y = some v) :
    Frame.get? F x y = some v ∨
      (Frame.get? F x y = none ∧ Frame.get? G x y = some v) := by
  cases hF : Frame.get? F x y with
  | none =>
    right
    exact ⟨rfl, by rwa [get?_append_none hF] at h⟩
  | some w =>
    left
    rw [get?_append_some hF] at h
    injection h with h
    subst h
    rfl

/-- Core-core frame entries carry the core net (under `core_rows`):
    the first write is a pattern write with core ports, whose value
    the N3 condition pins to `coreNet`; steering never touches
    core-core pairs. -/
theorem get?_corecore {C : Cert} (hwf : Wellformed C) (hs : SCond C) :
    ∀ n, n ≤ C.steps.length → ∀ c c', c ≠ c' → ∀ v,
      Frame.get? (unfoldPrefix C n) (.core c) (.core c') = some v →
      v = C.coreNet c c' := by
  intro n
  induction n with
  | zero =>
    intro _ c c' _ v h
    cases h
  | succ n ih =>
    intro hn c c' hne v h
    have hn' : n < C.steps.length := Nat.lt_of_succ_le hn
    rw [unfoldPrefix_succ] at h
    unfold doStep at h
    cases get?_append_cases h with
    | inl hFP =>
      cases get?_append_cases hFP with
      | inl hF => exact ih (Nat.le_of_lt hn') c c' hne v hF
      | inr hP =>
        have hmem := get?_some_mem hP.2
        rw [mem_patternVals] at hmem
        obtain ⟨p', hp', q', hq', _, _, heq⟩ := hmem
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨h1, h2⟩, h3⟩ := heq
        -- ports mapping to cores are core ports with in-range indices
        have hpcore : p' = (.inr (.inl c) : TPort) ∧ c < C.nCore := by
          cases mem_memberPortsList_elim hp' with
          | inl hk =>
            obtain ⟨k, hk, rfl⟩ := hk
            have hk' : k < (C.step n).slotTargets.length := by
              rw [hwf.targets_length n hn']; exact hk
            obtain ⟨s, j, htk, _⟩ :=
              target_shape hwf hn' (List.getElem_mem hk')
            rw [portOcc_slot_eq hk', htk] at h1
            exact absurd h1 (fun h4 => Occ.noConfusion h4)
          | inr hcf =>
            cases hcf with
            | inl hcp =>
              obtain ⟨c1, hc1, rfl⟩ := hcp
              have h1' : Occ.core c = Occ.core c1 := h1
              injection h1' with h1'
              subst h1'
              exact ⟨rfl, hc1⟩
            | inr hfp =>
              obtain ⟨j, _, rfl⟩ := hfp
              exact absurd (h1 : Occ.core c = Occ.born n j)
                (fun h4 => Occ.noConfusion h4)
        have hqcore : q' = (.inr (.inl c') : TPort) ∧ c' < C.nCore := by
          cases mem_memberPortsList_elim hq' with
          | inl hk =>
            obtain ⟨k, hk, rfl⟩ := hk
            have hk' : k < (C.step n).slotTargets.length := by
              rw [hwf.targets_length n hn']; exact hk
            obtain ⟨s, j, htk, _⟩ :=
              target_shape hwf hn' (List.getElem_mem hk')
            rw [portOcc_slot_eq hk', htk] at h2
            exact absurd h2 (fun h4 => Occ.noConfusion h4)
          | inr hcf =>
            cases hcf with
            | inl hcp =>
              obtain ⟨c1, hc1, rfl⟩ := hcp
              have h2' : Occ.core c' = Occ.core c1 := h2
              injection h2' with h2'
              subst h2'
              exact ⟨rfl, hc1⟩
            | inr hfp =>
              obtain ⟨j, _, rfl⟩ := hfp
              exact absurd (h2 : Occ.core c' = Occ.born n j)
                (fun h4 => Occ.noConfusion h4)
        rw [h3, hpcore.1, hqcore.1]
        exact hs.core_rows n hn' c c' hpcore.2 hqcore.2 hne
    | inr hS =>
      have hmem := get?_some_mem hS.2
      rw [mem_steeringVals] at hmem
      obtain ⟨x', _, _, j', _, hor⟩ := hmem
      cases hor with
      | inl h1 =>
        simp only [Prod.mk.injEq] at h1
        exact absurd h1.1.2 (fun h => Occ.noConfusion h)
      | inr h1 =>
        simp only [Prod.mk.injEq] at h1
        exact absurd h1.1.1 (fun h => Occ.noConfusion h)

/-- Every frame entry between distinct existing occurrences carries
    the realized `pairVal` (round-20's theorem for non-core-core
    pairs; the core-row lemma for core-core pairs). -/
theorem get?_eq_pairVal (C : Cert) (hwf : Wellformed C) (hs : SCond C)
    {x y : Occ} {v : Atom}
    (hx : x ∈ existingBefore C C.steps.length)
    (hy : y ∈ existingBefore C C.steps.length)
    (hxy : x ≠ y)
    (h : Frame.get? (unfoldAll C) x y = some v) :
    v = pairVal C x y := by
  cases x with
  | core c =>
    cases y with
    | core c' =>
      exact get?_corecore hwf hs C.steps.length (Nat.le_refl _) c c'
        (fun h2 => hxy (congrArg Occ.core h2)) v h
    | born s j =>
      have h2 := uSource_eq_frame C hwf _ _ hxy hx hy
        (fun c1 c2 h3 => Occ.noConfusion h3.2)
      rw [h] at h2
      injection h2 with h2
  | born s j =>
    have h2 := uSource_eq_frame C hwf _ _ hxy hx hy
      (fun c1 c2 h3 => Occ.noConfusion h3.1)
    rw [h] at h2
    injection h2 with h2

/-- ROUND-21 MAIN THEOREM (the S4 soundness kernel, operational form):
    the unfolded frame of a wellformed, S-conditioned certificate is
    composition-closed on every distinct existing triangle.  This is
    the statement WP30 Part C and WP32 Part C checked empirically. -/
theorem frame_closed (C : Cert) (hwf : Wellformed C) (hs : SCond C)
    {x y z : Occ} {v1 v2 v3 : Atom}
    (hx : x ∈ existingBefore C C.steps.length)
    (hy : y ∈ existingBefore C C.steps.length)
    (hz : z ∈ existingBefore C C.steps.length)
    (hxy : x ≠ y) (hxz : x ≠ z) (hzy : z ≠ y)
    (h1 : Frame.get? (unfoldAll C) x y = some v1)
    (h2 : Frame.get? (unfoldAll C) x z = some v2)
    (h3 : Frame.get? (unfoldAll C) z y = some v3) :
    v1 ∈ comp v2 v3 := by
  rw [get?_eq_pairVal C hwf hs hx hy hxy h1,
      get?_eq_pairVal C hwf hs hx hz hxz h2,
      get?_eq_pairVal C hwf hs hz hy hzy h3]
  exact pairVal_closed C hwf hs x y z hx hy hz hxy hxz hzy

/-- The unfolded frame is converse-coherent (R2). -/
theorem frame_conv (C : Cert) (hwf : Wellformed C) (hs : SCond C)
    {x y : Occ} {v1 v2 : Atom}
    (hx : x ∈ existingBefore C C.steps.length)
    (hy : y ∈ existingBefore C C.steps.length)
    (hxy : x ≠ y)
    (h1 : Frame.get? (unfoldAll C) x y = some v1)
    (h2 : Frame.get? (unfoldAll C) y x = some v2) :
    v2 = conv v1 := by
  rw [get?_eq_pairVal C hwf hs hx hy hxy h1,
      get?_eq_pairVal C hwf hs hy hx (fun h => hxy h.symm) h2]
  exact pairVal_conv C hwf hs.core_conv hxy (birthBound hx) (birthBound hy)

/-- The unfolded frame is EQ-free on distinct pairs (strong EQ). -/
theorem frame_proper (C : Cert) (hwf : Wellformed C) (hs : SCond C)
    {x y : Occ} {v : Atom}
    (hx : x ∈ existingBefore C C.steps.length)
    (hy : y ∈ existingBefore C C.steps.length)
    (hxy : x ≠ y)
    (h : Frame.get? (unfoldAll C) x y = some v) :
    v ≠ Atom.eq := by
  rw [get?_eq_pairVal C hwf hs hx hy hxy h]
  exact pairVal_proper C hwf hs x y hx hy hxy

end Round19

namespace Round19
open Atom

/-! ### Kernel-checked witnesses for the S-layer -/

/-- Core Lean has no general `Decidable (p → q)` instance; the bounded
    S-condition quantifiers need one to be `decide`-checkable on
    concrete certificates. -/
instance decImp {p q : Prop} [dp : Decidable p] [dq : Decidable q] :
    Decidable (p → q) :=
  match dp with
  | isTrue hp =>
    match dq with
    | isTrue hq => isTrue fun _ => hq
    | isFalse hq => isFalse fun h => hq (h hp)
  | isFalse hp => isTrue fun h => absurd h hp

/-- `certC` satisfies the S-condition: all pattern, core and steering
    values are `DR`, and `comp dr dr` is the full atom set. -/
theorem certC_scond : SCond certC := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro c c' hc hc' hne
    have h0 : certC.nCore = 0 := rfl
    omega
  · intro c1 c2 c3 h1 h2 h3 h4 h5 h6
    have h0 : certC.nCore = 0 := rfl
    omega
  · intro i hi c c' hc hc' hne
    have h0 : certC.nCore = 0 := rfl
    omega
  · native_decide
  · native_decide

/-- End to end: the operational frame of the S-conditioned `certC` is
    closed on its inherited-slot triangle -- the round-21 theorem
    applied to a concrete certificate. -/
example {v1 v2 v3 : Atom}
    (h1 : Frame.get? (unfoldAll certC) (.born 0 0) (.born 0 1) = some v1)
    (h2 : Frame.get? (unfoldAll certC) (.born 0 0) (.born 1 0) = some v2)
    (h3 : Frame.get? (unfoldAll certC) (.born 1 0) (.born 0 1) = some v3) :
    v1 ∈ comp v2 v3 :=
  frame_closed certC certC_wellformed certC_scond
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h1 h2 h3

/-- The adversarial control (WP32 Part C in the kernel): pattern
    geometry `x DR z` (step 0), `z PO b` (step 1, `z` inherited), but
    the steering function insists on `PPI` for the steered `x` toward
    the fresh `b` -- against `comp DR PO = {PP, PO, DR}`. -/
def certD : Cert where
  nCore := 0
  coreNet := fun _ _ => Atom.dr
  templates :=
    [ ⟨0, 2, fun _ _ => Atom.dr⟩,
      ⟨1, 1, fun _ _ => Atom.po⟩ ]
  steps := [⟨0, []⟩, ⟨1, [.born 0 1]⟩]
  f := fun _ _ _ _ => Atom.ppi

theorem certD_wellformed : Wellformed certD := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi t ht
    match i with
    | 0 => cases ht
    | 1 =>
      cases ht with
      | head => exact Nat.zero_lt_one
      | tail _ h => cases h
    | n+2 =>
      have h2 : certD.steps.length = 2 := rfl
      omega
  · intro i hi t ht
    match i with
    | 0 => cases ht
    | 1 =>
      cases ht with
      | head => decide
      | tail _ h => cases h
    | n+2 =>
      have h2 : certD.steps.length = 2 := rfl
      omega
  · intro i hi
    match i with
    | 0 => rfl
    | 1 => rfl
    | n+2 =>
      have h2 : certD.steps.length = 2 := rfl
      omega
  · intro i hi
    match i with
    | 0 => exact List.Pairwise.nil
    | 1 => decide
    | n+2 =>
      have h2 : certD.steps.length = 2 := rfl
      omega
  · intro i hi
    match i with
    | 0 => decide
    | 1 => decide
    | n+2 =>
      have h2 : certD.steps.length = 2 := rfl
      omega
  · intro i hi p q
    match i with
    | 0 => rfl
    | 1 => rfl
    | n+2 =>
      have h2 : certD.steps.length = 2 := rfl
      omega
  · intro i hi r1 r1' r2 r2' j h1 h2
    rfl

/-- The S-condition fails on `certD` at the predicted triangle: the
    old pair is pinned to `comp PPI PO = {PPI, PO}`, but the recorded
    value is `DR`.  (This is the instance of `SCond.tri` at step 1,
    `x = born 0 0`, `y = born 0 1`, `jz = 0`.) -/
theorem certD_scond_violated :
    pairVal certD (.born 0 0) (.born 0 1) ∉
      comp (pairVal certD (.born 0 0) (.born 1 0))
           (pairVal certD (.born 1 0) (.born 0 1)) := by native_decide

/-- ... and the operational frame indeed breaks closure exactly
    there -- `certD` is wellformed, so by `frame_closed`
    (contrapositive) no `SCond` can exist for it. -/
theorem certD_frame_not_closed :
    Frame.get? (unfoldAll certD) (.born 0 0) (.born 0 1) = some Atom.dr ∧
    Frame.get? (unfoldAll certD) (.born 0 0) (.born 1 0) = some Atom.ppi ∧
    Frame.get? (unfoldAll certD) (.born 1 0) (.born 0 1) = some Atom.po ∧
    Atom.dr ∉ comp Atom.ppi Atom.po := by native_decide

end Round19

namespace Round19
open Atom

/-! ## 9. Round-22: the catalogue level — interface-state S-conditions

`SCond` (round-21) quantifies over the occurrences of one unfolding.
This section lifts the check to the CATALOGUE: `SCat` below is a
condition on `(coreNet, templates, f)` only — it never mentions the
step list — so one finite check covers every certificate sharing that
data.  Together with per-certificate pattern faithfulness (a
structural condition the round-23 generator will guarantee by
construction), `SCat` implies `SCond`, hence closed frames, for every
unfolding.  The steered-steered case is the manuscripts' joint
steering (round-16 Q4′): the old pair's value is constrained through
every separator member by closure below the current step — a
strengthened induction, not a per-triple check. -/

/-- All atom lists of a given length (the abstract-row enumeration). -/
def atomLists : Nat → List (List Atom)
  | 0 => [[]]
  | n+1 => (atomLists n).flatMap (fun l => atoms.map (fun a => a :: l))

theorem mem_atomLists : ∀ l : List Atom, l ∈ atomLists l.length := by
  intro l
  induction l with
  | nil => exact List.mem_cons_self ..
  | cons a l ih =>
    show a :: l ∈ (atomLists l.length).flatMap
      (fun l' => atoms.map (fun x => x :: l'))
    exact List.mem_flatMap.mpr
      ⟨l, ih, List.mem_map.mpr ⟨a, by cases a <;> decide, rfl⟩⟩

/-- The old-member addresses of a template: inherited slots and core
    ports (fresh ports are never "old"). -/
def oldPorts (T : Template) (nCore : Nat) : List TPort :=
  (List.range T.nSlots).map .inl ++
  (List.range nCore).map (fun c => .inr (.inl c))

/-- Reading an abstract row pair at an old address (padding `DR`,
    matching `coreRowOf`/`slotRowOf`). -/
def rowval (r1 r2 : List Atom) : TPort → Atom
  | .inl k => r2.getD k Atom.dr
  | .inr (.inl c) => r1.getD c Atom.dr
  | .inr (.inr _) => Atom.dr

/-- A member's value toward a fresh port is the current template's
    net entry at its port (uSource's member clause, with `net_conv`
    absorbing the core orientation). -/
theorem member_val {C : Cert} (hwf : Wellformed C) {i : Nat}
    (hi : i < C.steps.length) {x : Occ} {p : TPort}
    (hx : x ∈ existingBefore C (i+1)) (hmp : memberPort C i x = some p)
    (jz : Nat) :
    pairVal C x (.born i jz)
      = (C.template (C.step i).tmpl).net p (.inr (.inr jz)) := by
  cases x with
  | core c =>
    have hp : p = (.inr (.inl c) : TPort) := by
      have h2 := (memberPort_core C i c).symm.trans hmp
      injection h2 with h2
      exact h2.symm
    subst hp
    show conv ((C.template (C.step i).tmpl).net
        (.inr (.inr jz)) (.inr (.inl c))) = _
    exact (hwf.net_conv i hi _ _).symm
  | born sx jx =>
    have hsx : sx < i + 1 := (mem_existingBefore_born.mp hx).1
    by_cases hei : sx = i
    · subst hei
      have hp : p = (.inr (.inr jx) : TPort) := by
        have h2 := (memberPort_fresh C sx jx).symm.trans hmp
        injection h2 with h2
        exact h2.symm
      subst hp
      show uSourceFuel C ((2*C.steps.length+3)+1)
          (.born sx jx) (.born sx jz) = _
      rw [uSourceFuel_born_born, if_pos rfl]
    · have hlt : sx < i := by omega
      show uSourceFuel C ((2*C.steps.length+3)+1)
          (.born sx jx) (.born i jz) = _
      rw [uSourceFuel_born_born, if_neg (by omega : ¬sx = i),
          if_pos hlt, hmp]

/-- A steered occurrence's value toward a fresh port is the steering
    function applied to its `pairVal` rows (uSource's U3 clause with
    the recursive rows collapsed by fuel irrelevance). -/
theorem steered_val {C : Cert} (hwf : Wellformed C) {i : Nat}
    (hi : i < C.steps.length) {x : Occ}
    (hxo : x ∈ existingBefore C i) (hmp : memberPort C i x = none)
    (jz : Nat) :
    pairVal C x (.born i jz)
      = C.f i (fun c => pairVal C x (.core c))
              (fun k => match (C.step i).slotTargets[k]? with
                        | some t => pairVal C x t
                        | none => Atom.dr) jz := by
  cases x with
  | core c => rw [memberPort_core] at hmp; simp at hmp
  | born sx jx =>
    have hsx : sx < i := (mem_existingBefore_born.mp hxo).1
    show uSourceFuel C ((2*C.steps.length+3)+1)
        (.born sx jx) (.born i jz) = _
    rw [uSourceFuel_born_born, if_neg (by omega : ¬sx = i),
        if_pos hsx, hmp]
    have hcrow : (fun c => uSourceFuel C (2*C.steps.length+3)
          (.born sx jx) (.core c))
        = fun c => pairVal C (.born sx jx) (.core c) := rfl
    have hsrow : (fun k : Nat => match (C.step i).slotTargets[k]? with
          | some t => uSourceFuel C (2*C.steps.length+3) (.born sx jx) t
          | none => Atom.dr)
        = fun k : Nat => match (C.step i).slotTargets[k]? with
          | some t => pairVal C (.born sx jx) t
          | none => Atom.dr := by
      funext k
      cases htk : (C.step i).slotTargets[k]? with
      | none => rfl
      | some t =>
        obtain ⟨hklen, hgk⟩ := List.getElem?_eq_some_iff.mp htk
        have htmem : t ∈ (C.step i).slotTargets :=
          hgk ▸ List.getElem_mem hklen
        obtain ⟨st, jt, hteq, hst⟩ := target_shape hwf hi htmem
        subst hteq
        show uSourceFuel C (2*C.steps.length+3) _ _
          = uSourceFuel C (2*C.steps.length+4) _ _
        have hfn : fuelNeed (.born sx jx) (.born st jt)
            ≤ 2 * C.steps.length + 3 := by
          simp only [fuelNeed]
          have hmx : max sx st ≤ C.steps.length :=
            Nat.max_le.mpr ⟨by omega, by omega⟩
          split <;> omega
        exact uSourceFuel_irrel C hwf (2*C.steps.length+4)
          (.born sx jx) (.born st jt) (by omega)
          (fun s j h => by injection h with hh _; omega)
          (fun s j h => by injection h with hh _; omega)
          _ _ (by omega) (by omega)
    rw [hcrow, hsrow]

end Round19

namespace Round19
open Atom

/-! ### The catalogue-level S-condition -/

/-- Steering applied to abstract list-rows (padding `DR`). -/
def fOn (C : Cert) (i : Nat) (r1 r2 : List Atom) (j : Nat) : Atom :=
  C.f i (fun c => r1.getD c Atom.dr) (fun k => r2.getD k Atom.dr) j

/-- The `pairVal` rows of an occurrence, as lists. -/
def rowsCore (C : Cert) (x : Occ) : List Atom :=
  (List.range C.nCore).map (fun c => pairVal C x (.core c))

def rowsSlot (C : Cert) (i : Nat) (x : Occ) : List Atom :=
  (List.range (C.template (C.step i).tmpl).nSlots).map
    (fun k => match (C.step i).slotTargets[k]? with
              | some t => pairVal C x t
              | none => Atom.dr)

theorem getD_map_range {α : Type} (f : Nat → α) {n c : Nat} (d : α)
    (hc : c < n) : ((List.range n).map f).getD c d = f c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hc]
  rfl

theorem rowsCore_mem (C : Cert) (x : Occ) :
    rowsCore C x ∈ atomLists C.nCore := by
  have h := mem_atomLists (rowsCore C x)
  rwa [show (rowsCore C x).length = C.nCore by
    simp [rowsCore]] at h

theorem rowsSlot_mem (C : Cert) (i : Nat) (x : Occ) :
    rowsSlot C i x ∈ atomLists (C.template (C.step i).tmpl).nSlots := by
  have h := mem_atomLists (rowsSlot C i x)
  rwa [show (rowsSlot C i x).length
      = (C.template (C.step i).tmpl).nSlots by simp [rowsSlot]] at h

/-- Steered value in list-row form (`f_reads_rows` bridges the frame
    rows and their list restrictions). -/
theorem steered_val_list {C : Cert} (hwf : Wellformed C) {i : Nat}
    (hi : i < C.steps.length) {x : Occ}
    (hxo : x ∈ existingBefore C i) (hmp : memberPort C i x = none)
    (jz : Nat) :
    pairVal C x (.born i jz) = fOn C i (rowsCore C x) (rowsSlot C i x) jz := by
  rw [steered_val hwf hi hxo hmp jz]
  exact hwf.f_reads_rows i hi _ _ _ _ jz
    (fun c hc => by
      unfold rowsCore
      exact (getD_map_range (fun c => pairVal C x (.core c))
        Atom.dr hc).symm)
    (fun k hk => by
      unfold rowsSlot
      exact (getD_map_range
        (fun k => match (C.step i).slotTargets[k]? with
                  | some t => pairVal C x t
                  | none => Atom.dr) Atom.dr hk).symm)

theorem mem_oldPorts_elim {T : Template} {nc : Nat} {p : TPort}
    (h : p ∈ oldPorts T nc) :
    (∃ k, k < T.nSlots ∧ p = .inl k) ∨
    (∃ c, c < nc ∧ p = .inr (.inl c)) := by
  unfold oldPorts at h
  cases List.mem_append.mp h with
  | inl hs =>
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hs
    exact Or.inl ⟨k, List.mem_range.mp hk, rfl⟩
  | inr hc =>
    obtain ⟨c, hcr, rfl⟩ := List.mem_map.mp hc
    exact Or.inr ⟨c, List.mem_range.mp hcr, rfl⟩

theorem slot_mem_oldPorts {T : Template} {nc k : Nat} (hk : k < T.nSlots) :
    (.inl k : TPort) ∈ oldPorts T nc :=
  List.mem_append.mpr (Or.inl
    (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))

theorem core_mem_oldPorts {T : Template} {nc c : Nat} (hc : c < nc) :
    (.inr (.inl c) : TPort) ∈ oldPorts T nc :=
  List.mem_append.mpr (Or.inr
    (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩))

theorem mem_atoms : ∀ a : Atom, a ∈ atoms := by
  intro a
  cases a <;> decide

/-- Membership at stage `i+1` decomposed: old or fresh. -/
theorem member_old_or_fresh {C : Cert} {i : Nat} {x : Occ}
    (hx : x ∈ existingBefore C (i+1)) :
    x ∈ existingBefore C i ∨
    ∃ j, j < (C.template (C.step i).tmpl).nFresh ∧ x = .born i j := by
  rw [existingBefore_succ] at hx
  cases List.mem_append.mp hx with
  | inl h => exact Or.inl h
  | inr h =>
    obtain ⟨j, hj, heq⟩ := List.mem_map.mp h
    exact Or.inr ⟨j, List.mem_range.mp hj, heq.symm⟩

theorem old_of_not_member {C : Cert} {i : Nat} {x : Occ}
    (hx : x ∈ existingBefore C (i+1)) (hmp : memberPort C i x = none) :
    x ∈ existingBefore C i := by
  cases member_old_or_fresh hx with
  | inl h => exact h
  | inr h =>
    obtain ⟨j, _, rfl⟩ := h
    rw [memberPort_fresh] at hmp
    simp at hmp

/-- `memberPort_spec` extended to stage `i+1` (covers fresh members). -/
theorem memberPort_spec' {C : Cert} (hwf : Wellformed C) {i : Nat}
    (hi : i < C.steps.length) {x : Occ} {p : TPort}
    (hx : x ∈ existingBefore C (i+1)) (h : memberPort C i x = some p) :
    p ∈ memberPortsList C i ∧ portOcc C i p = x := by
  cases member_old_or_fresh hx with
  | inl hxo => exact memberPort_spec hwf hi hxo h
  | inr hf =>
    obtain ⟨j, hj, rfl⟩ := hf
    have h2 := (memberPort_fresh C i j).symm.trans h
    injection h2 with h2
    subst h2
    exact ⟨freshPort_mem_memberPortsList hj, rfl⟩

/-- Pattern faithfulness: co-members that both pre-exist a step carry
    the step template's net entry as their recorded value.  (The
    thirteenth review's parent-pattern agreement, as a per-certificate
    condition; the round-23 catalogue generator discharges it by
    construction.) -/
def FaithfulAt (C : Cert) (i : Nat) : Prop :=
  ∀ p ∈ memberPortsList C i, ∀ q ∈ memberPortsList C i,
    portOcc C i p ∈ existingBefore C i →
    portOcc C i q ∈ existingBefore C i →
    portOcc C i p ≠ portOcc C i q →
    pairVal C (portOcc C i p) (portOcc C i q)
      = (C.template (C.step i).tmpl).net p q

def Faithful (C : Cert) : Prop :=
  ∀ i, i < C.steps.length → FaithfulAt C i

/-- Two members' mutual value is the current template's net entry. -/
theorem member_pair_val {C : Cert} (hwf : Wellformed C)
    (hcc : ∀ c c', C.coreNet c' c = conv (C.coreNet c c'))
    {i : Nat} (hi : i < C.steps.length) (hfa : FaithfulAt C i)
    {x y : Occ} {px py : TPort}
    (hx : x ∈ existingBefore C (i+1)) (hy : y ∈ existingBefore C (i+1))
    (hmpx : memberPort C i x = some px)
    (hmpy : memberPort C i y = some py) (hxy : x ≠ y) :
    pairVal C x y = (C.template (C.step i).tmpl).net px py := by
  obtain ⟨hpxm, hpxo⟩ := memberPort_spec' hwf hi hx hmpx
  obtain ⟨hpym, hpyo⟩ := memberPort_spec' hwf hi hy hmpy
  cases member_old_or_fresh hy with
  | inr hyf =>
    obtain ⟨jy, hjy, rfl⟩ := hyf
    have hpy_eq : py = (.inr (.inr jy) : TPort) := by
      have h2 := (memberPort_fresh C i jy).symm.trans hmpy
      injection h2 with h2
      exact h2.symm
    subst hpy_eq
    exact member_val hwf hi hx hmpx jy
  | inl hyo =>
    cases member_old_or_fresh hx with
    | inl hxo =>
      have h := hfa px hpxm py hpym (hpxo ▸ hxo) (hpyo ▸ hyo)
        (by rw [hpxo, hpyo]; exact hxy)
      rwa [hpxo, hpyo] at h
    | inr hxf =>
      obtain ⟨jx, hjx, rfl⟩ := hxf
      have hpx_eq : px = (.inr (.inr jx) : TPort) := by
        have h2 := (memberPort_fresh C i jx).symm.trans hmpx
        injection h2 with h2
        exact h2.symm
      subst hpx_eq
      have hyx : y ≠ Occ.born i jx := fun h => hxy h.symm
      rw [show pairVal C (.born i jx) y = conv (pairVal C y (.born i jx))
            from pairVal_conv C hwf hcc hyx
              (fun s j h => by
                subst h
                have := (mem_existingBefore_born.mp hyo).1
                omega)
              (fun s j h => by injection h with h4 _; omega),
          member_val hwf hi hy hmpy jx]
      exact (hwf.net_conv i hi _ _).symm

/-- The catalogue-level S-condition: no occurrences, no step targets —
    only `(coreNet, templates, f)` data quantified over abstract rows
    and ports.  (The step index `i` appears only to select which
    template/steering pair is in force; for template-determined
    steering — the round-23 generator's discipline — the conditions
    collapse to one check per template.) -/
structure SCat (C : Cert) : Prop where
  core_conv : ∀ c c', C.coreNet c' c = conv (C.coreNet c c')
  core_proper : ∀ c c', c < C.nCore → c' < C.nCore → c ≠ c' →
    C.coreNet c c' ≠ Atom.eq
  core_closed : ∀ c1 c2 c3, c1 < C.nCore → c2 < C.nCore → c3 < C.nCore →
    c1 ≠ c2 → c1 ≠ c3 → c3 ≠ c2 →
    C.coreNet c1 c2 ∈ comp (C.coreNet c1 c3) (C.coreNet c3 c2)
  core_rows : ∀ i, i < C.steps.length → ∀ c c', c < C.nCore → c' < C.nCore →
    c ≠ c' →
    (C.template (C.step i).tmpl).net (.inr (.inl c)) (.inr (.inl c'))
      = C.coreNet c c'
  net_r3 : ∀ i, i < C.steps.length →
    ∀ p ∈ memberPortsList C i, ∀ q ∈ memberPortsList C i,
    ∀ j, j < (C.template (C.step i).tmpl).nFresh → p ≠ q →
    (C.template (C.step i).tmpl).net p q ∈
      comp ((C.template (C.step i).tmpl).net p (.inr (.inr j)))
           (conv ((C.template (C.step i).tmpl).net q (.inr (.inr j))))
  net_proper : ∀ i, i < C.steps.length →
    ∀ p ∈ memberPortsList C i,
    ∀ j, j < (C.template (C.step i).tmpl).nFresh → p ≠ .inr (.inr j) →
    (C.template (C.step i).tmpl).net p (.inr (.inr j)) ≠ Atom.eq
  steer_member : ∀ i, i < C.steps.length →
    ∀ r1 ∈ atomLists C.nCore,
    ∀ r2 ∈ atomLists (C.template (C.step i).tmpl).nSlots,
    ∀ p ∈ oldPorts (C.template (C.step i).tmpl) C.nCore,
    ∀ j, j < (C.template (C.step i).tmpl).nFresh →
    conv (rowval r1 r2 p) ∈
      comp ((C.template (C.step i).tmpl).net p (.inr (.inr j)))
           (conv (fOn C i r1 r2 j))
  steer_member2 : ∀ i, i < C.steps.length →
    ∀ r1 ∈ atomLists C.nCore,
    ∀ r2 ∈ atomLists (C.template (C.step i).tmpl).nSlots,
    ∀ q ∈ oldPorts (C.template (C.step i).tmpl) C.nCore,
    ∀ j, j < (C.template (C.step i).tmpl).nFresh →
    rowval r1 r2 q ∈
      comp (fOn C i r1 r2 j)
           (conv ((C.template (C.step i).tmpl).net q (.inr (.inr j))))
  steer_two_fresh : ∀ i, i < C.steps.length →
    ∀ r1 ∈ atomLists C.nCore,
    ∀ r2 ∈ atomLists (C.template (C.step i).tmpl).nSlots,
    ∀ jx, jx < (C.template (C.step i).tmpl).nFresh →
    ∀ jz, jz < (C.template (C.step i).tmpl).nFresh → jx ≠ jz →
    conv (fOn C i r1 r2 jx) ∈
      comp ((C.template (C.step i).tmpl).net (.inr (.inr jx)) (.inr (.inr jz)))
           (conv (fOn C i r1 r2 jz))
  steer_two_fresh2 : ∀ i, i < C.steps.length →
    ∀ r1 ∈ atomLists C.nCore,
    ∀ r2 ∈ atomLists (C.template (C.step i).tmpl).nSlots,
    ∀ jy, jy < (C.template (C.step i).tmpl).nFresh →
    ∀ jz, jz < (C.template (C.step i).tmpl).nFresh → jy ≠ jz →
    fOn C i r1 r2 jy ∈
      comp (fOn C i r1 r2 jz)
           ((C.template (C.step i).tmpl).net (.inr (.inr jz)) (.inr (.inr jy)))
  steer_steer : ∀ i, i < C.steps.length →
    ∀ r1 ∈ atomLists C.nCore,
    ∀ r2 ∈ atomLists (C.template (C.step i).tmpl).nSlots,
    ∀ r1' ∈ atomLists C.nCore,
    ∀ r2' ∈ atomLists (C.template (C.step i).tmpl).nSlots,
    ∀ v ∈ atoms,
    (∀ a ∈ oldPorts (C.template (C.step i).tmpl) C.nCore,
      v ∈ comp (rowval r1 r2 a) (conv (rowval r1' r2' a))) →
    ∀ j, j < (C.template (C.step i).tmpl).nFresh →
    v ∈ comp (fOn C i r1 r2 j) (conv (fOn C i r1' r2' j))
  f_proper : ∀ i, i < C.steps.length →
    ∀ r1 ∈ atomLists C.nCore,
    ∀ r2 ∈ atomLists (C.template (C.step i).tmpl).nSlots,
    ∀ j, j < (C.template (C.step i).tmpl).nFresh →
    fOn C i r1 r2 j ≠ Atom.eq

end Round19

namespace Round19
open Atom

/-! ### The catalogue check certifies every step -/

/-- The heart of round-22: the catalogue-level check plus pattern
    faithfulness plus closure below the step yield the per-step
    triangle condition.  The steered-steered case is the joint
    steering of round 16: the old pair's value enters constrained
    through every separator member by `hclosed`. -/
theorem fresh_tri (C : Cert) (hwf : Wellformed C) (hcat : SCat C)
    (hfaith : Faithful C) {i : Nat} (hi : i < C.steps.length)
    (hclosed : ∀ a b c : Occ, a ∈ existingBefore C i →
      b ∈ existingBefore C i → c ∈ existingBefore C i →
      a ≠ b → a ≠ c → c ≠ b →
      pairVal C a b ∈ comp (pairVal C a c) (pairVal C c b)) :
    TriAt C i := by
  intro x hx y hy jz hjz hxy hxz hyz
  have hxb : ∀ s j, x = .born s j → s < C.steps.length := fun s j h => by
    subst h
    have := (mem_existingBefore_born.mp hx).1
    omega
  have hyb : ∀ s j, y = .born s j → s < C.steps.length := fun s j h => by
    subst h
    have := (mem_existingBefore_born.mp hy).1
    omega
  have hzb : ∀ s j, (Occ.born i jz) = .born s j → s < C.steps.length :=
    fun s j h => by injection h with h1 _; omega
  cases hmpx : memberPort C i x with
  | some px =>
    cases hmpy : memberPort C i y with
    | some py =>
      -- both members: pattern triangle
      obtain ⟨hpxm, hpxo⟩ := memberPort_spec' hwf hi hx hmpx
      obtain ⟨hpym, hpyo⟩ := memberPort_spec' hwf hi hy hmpy
      rw [member_pair_val hwf hcat.core_conv hi (hfaith i hi) hx hy hmpx hmpy
            hxy,
          member_val hwf hi hx hmpx jz,
          show pairVal C (.born i jz) y = conv (pairVal C y (.born i jz))
            from pairVal_conv C hwf hcat.core_conv hyz hyb hzb,
          member_val hwf hi hy hmpy jz]
      exact hcat.net_r3 i hi px hpxm py hpym jz hjz
        (fun h => hxy (by rw [← hpxo, h, hpyo]))
    | none =>
      -- x member, y steered
      have hyo : y ∈ existingBefore C i := old_of_not_member hy hmpy
      cases member_old_or_fresh hx with
      | inr hxf =>
        -- x fresh: same-source two-fresh check
        obtain ⟨jx, hjx, rfl⟩ := hxf
        have hpx_eq : px = (.inr (.inr jx) : TPort) := by
          have h2 := (memberPort_fresh C i jx).symm.trans hmpx
          injection h2 with h2
          exact h2.symm
        subst hpx_eq
        have hjxz : jx ≠ jz := fun h => hxz (by rw [h])
        rw [show pairVal C (.born i jx) y = conv (pairVal C y (.born i jx))
              from pairVal_conv C hwf hcat.core_conv
                (fun h => hxy h.symm) hyb hxb,
            steered_val_list hwf hi hyo hmpy jx,
            member_val hwf hi hx hmpx jz,
            show pairVal C (.born i jz) y = conv (pairVal C y (.born i jz))
              from pairVal_conv C hwf hcat.core_conv hyz hyb hzb,
            steered_val_list hwf hi hyo hmpy jz]
        exact hcat.steer_two_fresh i hi (rowsCore C y) (rowsCore_mem C y)
          (rowsSlot C i y) (rowsSlot_mem C i y) jx hjx jz hjz hjxz
      | inl hxo =>
        -- x old member
        obtain ⟨hpxm, hpxo⟩ := memberPort_spec' hwf hi hx hmpx
        have hpxold : px ∈ oldPorts (C.template (C.step i).tmpl) C.nCore := by
          cases mem_memberPortsList_elim hpxm with
          | inl h =>
            obtain ⟨k, hk, rfl⟩ := h
            exact slot_mem_oldPorts hk
          | inr h =>
            cases h with
            | inl hc =>
              obtain ⟨c, hc2, rfl⟩ := hc
              exact core_mem_oldPorts hc2
            | inr hf =>
              obtain ⟨j, hj, rfl⟩ := hf
              exfalso
              have h4 : Occ.born i j = x := hpxo
              have h3 : Occ.born i j ∈ existingBefore C i := by
                rw [h4]; exact hxo
              exact absurd (mem_existingBefore_born.mp h3).1
                (Nat.lt_irrefl i)
        have hxyval : pairVal C x y
            = conv (rowval (rowsCore C y) (rowsSlot C i y) px) := by
          rw [show pairVal C x y = conv (pairVal C y x) from
                pairVal_conv C hwf hcat.core_conv
                  (fun h => hxy h.symm) hyb hxb]
          congr 1
          cases mem_oldPorts_elim hpxold with
          | inl h =>
            obtain ⟨k, hk, rfl⟩ := h
            have hk' : k < (C.step i).slotTargets.length := by
              rw [hwf.targets_length i hi]; exact hk
            have hxt : (C.step i).slotTargets[k] = x := by
              rw [portOcc_slot_eq hk'] at hpxo
              exact hpxo
            show pairVal C y x = (rowsSlot C i y).getD k Atom.dr
            unfold rowsSlot
            rw [getD_map_range
                  (fun k => match (C.step i).slotTargets[k]? with
                    | some t => pairVal C y t
                    | none => Atom.dr) Atom.dr hk,
                List.getElem?_eq_getElem hk', hxt]
          | inr h =>
            obtain ⟨c, hc, rfl⟩ := h
            have hxc : Occ.core c = x := hpxo
            show pairVal C y x = (rowsCore C y).getD c Atom.dr
            unfold rowsCore
            rw [getD_map_range (fun c => pairVal C y (.core c))
                  Atom.dr hc, hxc]
        rw [hxyval, member_val hwf hi hx hmpx jz,
            show pairVal C (.born i jz) y = conv (pairVal C y (.born i jz))
              from pairVal_conv C hwf hcat.core_conv hyz hyb hzb,
            steered_val_list hwf hi hyo hmpy jz]
        exact hcat.steer_member i hi (rowsCore C y) (rowsCore_mem C y)
          (rowsSlot C i y) (rowsSlot_mem C i y) px hpxold jz hjz
  | none =>
    have hxo : x ∈ existingBefore C i := old_of_not_member hx hmpx
    cases hmpy : memberPort C i y with
    | some py =>
      -- x steered, y member
      cases member_old_or_fresh hy with
      | inr hyf =>
        -- y fresh: same-source two-fresh check, second orientation
        obtain ⟨jy, hjy, rfl⟩ := hyf
        have hjyz : jy ≠ jz := fun h => hyz (by rw [h])
        rw [steered_val_list hwf hi hxo hmpx jy,
            steered_val_list hwf hi hxo hmpx jz,
            show pairVal C (.born i jz) (.born i jy)
                = (C.template (C.step i).tmpl).net
                    (.inr (.inr jz)) (.inr (.inr jy)) from by
              show uSourceFuel C ((2*C.steps.length+3)+1) _ _ = _
              rw [uSourceFuel_born_born, if_pos rfl]]
        exact hcat.steer_two_fresh2 i hi (rowsCore C x) (rowsCore_mem C x)
          (rowsSlot C i x) (rowsSlot_mem C i x) jy hjy jz hjz hjyz
      | inl hyo =>
        obtain ⟨hpym, hpyo⟩ := memberPort_spec' hwf hi hy hmpy
        have hpyold : py ∈ oldPorts (C.template (C.step i).tmpl) C.nCore := by
          cases mem_memberPortsList_elim hpym with
          | inl h =>
            obtain ⟨k, hk, rfl⟩ := h
            exact slot_mem_oldPorts hk
          | inr h =>
            cases h with
            | inl hc =>
              obtain ⟨c, hc2, rfl⟩ := hc
              exact core_mem_oldPorts hc2
            | inr hf =>
              obtain ⟨j, hj, rfl⟩ := hf
              exfalso
              have h4 : Occ.born i j = y := hpyo
              have h3 : Occ.born i j ∈ existingBefore C i := by
                rw [h4]; exact hyo
              exact absurd (mem_existingBefore_born.mp h3).1
                (Nat.lt_irrefl i)
        have hxyval : pairVal C x y
            = rowval (rowsCore C x) (rowsSlot C i x) py := by
          cases mem_oldPorts_elim hpyold with
          | inl h =>
            obtain ⟨k, hk, rfl⟩ := h
            have hk' : k < (C.step i).slotTargets.length := by
              rw [hwf.targets_length i hi]; exact hk
            have hyt : (C.step i).slotTargets[k] = y := by
              rw [portOcc_slot_eq hk'] at hpyo
              exact hpyo
            show pairVal C x y = (rowsSlot C i x).getD k Atom.dr
            unfold rowsSlot
            rw [getD_map_range
                  (fun k => match (C.step i).slotTargets[k]? with
                    | some t => pairVal C x t
                    | none => Atom.dr) Atom.dr hk,
                List.getElem?_eq_getElem hk', hyt]
          | inr h =>
            obtain ⟨c, hc, rfl⟩ := h
            have hyc : Occ.core c = y := hpyo
            show pairVal C x y = (rowsCore C x).getD c Atom.dr
            unfold rowsCore
            rw [getD_map_range (fun c => pairVal C x (.core c))
                  Atom.dr hc, hyc]
        rw [hxyval, steered_val_list hwf hi hxo hmpx jz,
            show pairVal C (.born i jz) y = conv (pairVal C y (.born i jz))
              from pairVal_conv C hwf hcat.core_conv hyz hyb hzb,
            member_val hwf hi hy hmpy jz]
        exact hcat.steer_member2 i hi (rowsCore C x) (rowsCore_mem C x)
          (rowsSlot C i x) (rowsSlot_mem C i x) py hpyold jz hjz
    | none =>
      -- both steered: joint steering through the separator
      have hyo : y ∈ existingBefore C i := old_of_not_member hy hmpy
      rw [steered_val_list hwf hi hxo hmpx jz,
          show pairVal C (.born i jz) y = conv (pairVal C y (.born i jz))
            from pairVal_conv C hwf hcat.core_conv hyz hyb hzb,
          steered_val_list hwf hi hyo hmpy jz]
      refine hcat.steer_steer i hi (rowsCore C x) (rowsCore_mem C x)
        (rowsSlot C i x) (rowsSlot_mem C i x) (rowsCore C y)
        (rowsCore_mem C y) (rowsSlot C i y) (rowsSlot_mem C i y)
        (pairVal C x y) (mem_atoms _) ?_ jz hjz
      intro a ha
      cases mem_oldPorts_elim ha with
      | inl h =>
        obtain ⟨k, hk, rfl⟩ := h
        have hk' : k < (C.step i).slotTargets.length := by
          rw [hwf.targets_length i hi]; exact hk
        have htmem : (C.step i).slotTargets[k] ∈ (C.step i).slotTargets :=
          List.getElem_mem hk'
        obtain ⟨st, jt, hteq, hst⟩ := target_shape hwf hi htmem
        have hmex : (C.step i).slotTargets[k] ∈ existingBefore C i :=
          hwf.targets_exist i hi _ htmem
        have hxm : x ≠ (C.step i).slotTargets[k] := by
          intro h2
          have hs2 := memberPort_isSome_of_target hwf hi htmem
          rw [← h2, hmpx] at hs2
          simp at hs2
        have hym : y ≠ (C.step i).slotTargets[k] := by
          intro h2
          have hs2 := memberPort_isSome_of_target hwf hi htmem
          rw [← h2, hmpy] at hs2
          simp at hs2
        have hrx : rowval (rowsCore C x) (rowsSlot C i x) (.inl k)
            = pairVal C x ((C.step i).slotTargets[k]) := by
          show (rowsSlot C i x).getD k Atom.dr = _
          unfold rowsSlot
          rw [getD_map_range
                (fun k => match (C.step i).slotTargets[k]? with
                  | some t => pairVal C x t
                  | none => Atom.dr) Atom.dr hk,
              List.getElem?_eq_getElem hk']
        have hry : rowval (rowsCore C y) (rowsSlot C i y) (.inl k)
            = pairVal C y ((C.step i).slotTargets[k]) := by
          show (rowsSlot C i y).getD k Atom.dr = _
          unfold rowsSlot
          rw [getD_map_range
                (fun k => match (C.step i).slotTargets[k]? with
                  | some t => pairVal C y t
                  | none => Atom.dr) Atom.dr hk,
              List.getElem?_eq_getElem hk']
        rw [hrx, hry,
            show conv (pairVal C y ((C.step i).slotTargets[k]))
                = pairVal C ((C.step i).slotTargets[k]) y from
              (pairVal_conv C hwf hcat.core_conv hym hyb
                (fun s j h2 => by
                  rw [hteq] at h2
                  injection h2 with h3 _
                  omega)).symm]
        exact hclosed x y _ hxo hyo hmex hxy hxm (fun h2 => hym h2.symm)
      | inr h =>
        obtain ⟨c, hc, rfl⟩ := h
        have hxm : x ≠ Occ.core c := by
          cases x with
          | core c2 => rw [memberPort_core] at hmpx; simp at hmpx
          | born s j => exact fun h2 => Occ.noConfusion h2
        have hym : y ≠ Occ.core c := by
          cases y with
          | core c2 => rw [memberPort_core] at hmpy; simp at hmpy
          | born s j => exact fun h2 => Occ.noConfusion h2
        have hrx : rowval (rowsCore C x) (rowsSlot C i x) (.inr (.inl c))
            = pairVal C x (.core c) := by
          show (rowsCore C x).getD c Atom.dr = _
          unfold rowsCore
          rw [getD_map_range (fun c => pairVal C x (.core c)) Atom.dr hc]
        have hry : rowval (rowsCore C y) (rowsSlot C i y) (.inr (.inl c))
            = pairVal C y (.core c) := by
          show (rowsCore C y).getD c Atom.dr = _
          unfold rowsCore
          rw [getD_map_range (fun c => pairVal C y (.core c)) Atom.dr hc]
        rw [hrx, hry,
            show conv (pairVal C y (.core c)) = pairVal C (.core c) y from
              (pairVal_conv C hwf hcat.core_conv hym hyb
                (fun s j h2 => Occ.noConfusion h2)).symm]
        exact hclosed x y (.core c) hxo hyo
          (mem_existingBefore_core.mpr hc) hxy hxm (fun h2 => hym h2.symm)

end Round19

namespace Round19
open Atom

/-! ### Catalogue soundness assembled -/

/-- Closure below every stage, by induction: new triples contain a
    fresh occurrence, which the routes rotate into the middle where
    `fresh_tri` certifies it. -/
theorem closedBelow_all (C : Cert) (hwf : Wellformed C) (hcat : SCat C)
    (hfaith : Faithful C) :
    ∀ n, n ≤ C.steps.length →
      ∀ a b c : Occ, a ∈ existingBefore C n → b ∈ existingBefore C n →
      c ∈ existingBefore C n → a ≠ b → a ≠ c → c ≠ b →
      pairVal C a b ∈ comp (pairVal C a c) (pairVal C c b) := by
  intro n
  induction n with
  | zero =>
    intro _ a b c ha hb hc hab hac hcb
    cases a with
    | born s j =>
      exact absurd (mem_existingBefore_born.mp ha).1 (Nat.not_lt_zero s)
    | core ca =>
      cases b with
      | born s j =>
        exact absurd (mem_existingBefore_born.mp hb).1 (Nat.not_lt_zero s)
      | core cb =>
        cases c with
        | born s j =>
          exact absurd (mem_existingBefore_born.mp hc).1 (Nat.not_lt_zero s)
        | core cc =>
          exact hcat.core_closed ca cb cc (mem_existingBefore_core.mp ha)
            (mem_existingBefore_core.mp hb) (mem_existingBefore_core.mp hc)
            (fun h => hab (congrArg Occ.core h))
            (fun h => hac (congrArg Occ.core h))
            (fun h => hcb (congrArg Occ.core h))
  | succ n ih =>
    intro hn a b c ha hb hc hab hac hcb
    have hn' : n < C.steps.length := Nat.lt_of_succ_le hn
    have htri : TriAt C n :=
      fresh_tri C hwf hcat hfaith hn' (ih (Nat.le_of_lt hn'))
    cases member_old_or_fresh hc with
    | inr hcf =>
      obtain ⟨jc, hjc, rfl⟩ := hcf
      exact route_direct htri hjc ha hb hab hac (fun h => hcb h.symm)
    | inl hco =>
      cases member_old_or_fresh hb with
      | inr hbf =>
        obtain ⟨jb, hjb, rfl⟩ := hbf
        exact route_rotb hwf hcat.core_conv hn' htri hjb ha hc hac hab hcb
          (fun s j h => by
            subst h
            have := (mem_existingBefore_born.mp hco).1
            omega)
      | inl hbo =>
        cases member_old_or_fresh ha with
        | inr haf =>
          obtain ⟨ja, hja, rfl⟩ := haf
          exact route_rota hwf hcat.core_conv hn' htri hja hb hc hcb
            (fun h => hac h.symm) (fun h => hab h.symm)
            (fun s j h => by
              subst h
              have := (mem_existingBefore_born.mp hco).1
              omega)
        | inl hao =>
          exact ih (Nat.le_of_lt hn') a b c hao hbo hco hab hac hcb

/-- ROUND-22 MAIN THEOREM: the catalogue-level check plus pattern
    faithfulness yield the full per-unfolding S-condition — one
    step-count-independent check certifies every faithful unfolding,
    and all round-21 frame theorems apply downstream. -/
theorem scat_scond (C : Cert) (hwf : Wellformed C) (hcat : SCat C)
    (hfaith : Faithful C) : SCond C := by
  refine ⟨hcat.core_conv, hcat.core_proper, hcat.core_closed,
          hcat.core_rows, ?_, ?_⟩
  · intro i hi x hx y hy jz hjz hxy hxz hyz
    exact fresh_tri C hwf hcat hfaith hi
      (closedBelow_all C hwf hcat hfaith i (Nat.le_of_lt hi))
      x hx y hy jz hjz hxy hxz hyz
  · intro i hi x hx jz hjz hxz
    cases hmpx : memberPort C i x with
    | some px =>
      obtain ⟨hpxm, hpxo⟩ := memberPort_spec' hwf hi hx hmpx
      rw [member_val hwf hi hx hmpx jz]
      exact hcat.net_proper i hi px hpxm jz hjz
        (fun h => hxz (by rw [← hpxo, h]; rfl))
    | none =>
      have hxo := old_of_not_member hx hmpx
      rw [steered_val_list hwf hi hxo hmpx jz]
      exact hcat.f_proper i hi (rowsCore C x) (rowsCore_mem C x)
        (rowsSlot C i x) (rowsSlot_mem C i x) jz hjz

/-- Catalogue soundness, operational form: every frame entry triangle
    of a wellformed, catalogue-checked, faithful certificate is
    composition-closed. -/
theorem scat_frame_closed (C : Cert) (hwf : Wellformed C) (hcat : SCat C)
    (hfaith : Faithful C) {x y z : Occ} {v1 v2 v3 : Atom}
    (hx : x ∈ existingBefore C C.steps.length)
    (hy : y ∈ existingBefore C C.steps.length)
    (hz : z ∈ existingBefore C C.steps.length)
    (hxy : x ≠ y) (hxz : x ≠ z) (hzy : z ≠ y)
    (h1 : Frame.get? (unfoldAll C) x y = some v1)
    (h2 : Frame.get? (unfoldAll C) x z = some v2)
    (h3 : Frame.get? (unfoldAll C) z y = some v3) :
    v1 ∈ comp v2 v3 :=
  frame_closed C hwf (scat_scond C hwf hcat hfaith)
    hx hy hz hxy hxz hzy h1 h2 h3

/-! ### Kernel-checked catalogue witnesses -/

/-- `certC` passes the catalogue-level check (all values `DR`;
    `comp dr dr` is the full atom set). -/
theorem certC_scat : SCat certC := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c c' hc hc' hne
    have h0 : certC.nCore = 0 := rfl
    omega
  · intro c1 c2 c3 h1 h2 h3 h4 h5 h6
    have h0 : certC.nCore = 0 := rfl
    omega
  · intro i hi c c' hc hc' hne
    have h0 : certC.nCore = 0 := rfl
    omega
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

theorem certC_faithful : Faithful certC := by
  unfold Faithful FaithfulAt
  native_decide

/-- The catalogue route reproduces round-21's `SCond certC` — the
    finite abstract check certifies the unfolding. -/
example : SCond certC :=
  scat_scond certC certC_wellformed certC_scat certC_faithful

/-- `certD` FAILS the catalogue check at exactly the reachable row:
    `steer_member2` with the inherited slot's recorded value `DR`
    demands the steered value compose with the child pattern's `PO`
    through `comp(PPI, PO) = {PPI, PO}` — and `DR` is not in it. -/
theorem certD_scat_violated :
    ¬(rowval [] [Atom.dr] (.inl 0) ∈
      comp (fOn certD 1 [] [Atom.dr] 0)
           (conv ((certD.template (certD.step 1).tmpl).net
             (.inl 0) (.inr (.inr 0))))) := by native_decide

end Round19

namespace Round19
open Atom

/-! ## 10. Round-23: the catalogue generator

`SCat`/`Faithful` (round-22) certify a given certificate.  This
section makes "every unfolding of the catalogue" a theorem about a
syntactic object: a `Catalog` carries templates, N2 attachment rules
(child slots map to parent member ports — never core, which threads
through its own ports), and template-indexed steering; `buildCert`
turns a plan (a list of rule/parent choices) into a certificate; and
the round-23 theorems show every planned certificate is `Wellformed`
and `Faithful` BY CONSTRUCTION.  With `kscat_scat` transporting the
catalogue-level check, `catalogue_soundness` certifies every plan
from one finite check. -/

/-- An attachment rule: child template, expected parent template, and
    the N2 slot map (child slot `k` inherits the parent member at port
    `slotMap[k]` — a parent slot or a parent fresh port). -/
structure Attach where
  tmpl : Nat
  parentTmpl : Nat
  slotMap : List TPort

structure Catalog where
  nCore : Nat
  coreNet : Nat → Nat → Atom
  templates : List Template
  root : Nat
  attaches : List Attach
  F : Nat → (Nat → Atom) → (Nat → Atom) → Nat → Atom

def Catalog.tmpl (K : Catalog) (t : Nat) : Template :=
  K.templates.getD t ⟨0, 0, fun _ _ => Atom.dr⟩

def Catalog.rule (K : Catalog) (r : Nat) : Attach :=
  K.attaches.getD r ⟨0, 0, []⟩

/-- Step-local port reading (agrees with `portOcc` definitionally). -/
def portOccOf (st : Step) (i : Nat) : TPort → Occ
  | .inl k => st.slotTargets.getD k (.core 0)
  | .inr (.inl c) => .core c
  | .inr (.inr j) => .born i j

theorem portOcc_eq_portOccOf (C : Cert) (i : Nat) (p : TPort) :
    portOcc C i p = portOccOf (C.step i) i p := by
  cases p with
  | inl k => rfl
  | inr q => cases q with
    | inl c => rfl
    | inr j => rfl

/-- The child step created by a plan entry `(r, p)` on top of the
    accumulated steps. -/
def childStepOf (K : Catalog) (steps : List Step) (rp : Nat × Nat) : Step :=
  ⟨(K.rule rp.1).tmpl,
   (K.rule rp.1).slotMap.map
     (portOccOf (steps.getD rp.2 ⟨0, []⟩) rp.2)⟩

def extendSteps (K : Catalog) (steps : List Step) (rp : Nat × Nat) :
    List Step :=
  steps ++ [childStepOf K steps rp]

/-- The canonical step list of a plan: root first, then one child per
    plan entry. -/
def buildSteps (K : Catalog) (plan : List (Nat × Nat)) : List Step :=
  plan.foldl (extendSteps K) [⟨K.root, []⟩]

def buildCert (K : Catalog) (plan : List (Nat × Nat)) : Cert where
  nCore := K.nCore
  coreNet := K.coreNet
  templates := K.templates
  steps := buildSteps K plan
  f := fun i r1 r2 j =>
    K.F ((buildSteps K plan).getD i ⟨0, []⟩).tmpl r1 r2 j

theorem foldl_extend_length (K : Catalog) :
    ∀ (l : List (Nat × Nat)) (acc : List Step),
      (l.foldl (extendSteps K) acc).length = acc.length + l.length := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons e l ih =>
    intro acc
    show (l.foldl (extendSteps K) (extendSteps K acc e)).length = _
    rw [ih]
    show (acc ++ [childStepOf K acc e]).length + l.length = _
    rw [List.length_append]
    simp +arith

theorem buildSteps_length (K : Catalog) (plan : List (Nat × Nat)) :
    (buildSteps K plan).length = plan.length + 1 := by
  unfold buildSteps
  rw [foldl_extend_length]
  simp +arith

theorem foldl_extend_getD_stable (K : Catalog) :
    ∀ (l : List (Nat × Nat)) (acc : List Step) (i : Nat),
      i < acc.length →
      (l.foldl (extendSteps K) acc).getD i ⟨0, []⟩ = acc.getD i ⟨0, []⟩ := by
  intro l
  induction l with
  | nil => intro acc i _; rfl
  | cons e l ih =>
    intro acc i hi
    show (l.foldl (extendSteps K) (extendSteps K acc e)).getD i _ = _
    rw [ih (extendSteps K acc e) i
        (by show i < (acc ++ _).length
            rw [List.length_append]; omega)]
    show (acc ++ [childStepOf K acc e]).getD i _ = _
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hi]

theorem foldl_extend_getD_new (K : Catalog) :
    ∀ (l : List (Nat × Nat)) (acc : List Step) (m : Nat),
      m < l.length →
      (l.foldl (extendSteps K) acc).getD (acc.length + m) ⟨0, []⟩
        = childStepOf K ((l.take m).foldl (extendSteps K) acc)
            (l.getD m (0, 0)) := by
  intro l
  induction l with
  | nil => intro acc m hm; cases hm
  | cons e l ih =>
    intro acc m hm
    cases m with
    | zero =>
      show (l.foldl (extendSteps K) (extendSteps K acc e)).getD
        (acc.length + 0) _ = _
      rw [foldl_extend_getD_stable K l (extendSteps K acc e)
          (acc.length + 0)
          (by show acc.length + 0 < (acc ++ _).length
              rw [List.length_append]; simp)]
      show (acc ++ [childStepOf K acc e]).getD (acc.length + 0) _ = _
      rw [List.getD_eq_getElem?_getD]
      rw [show acc.length + 0 = acc.length from rfl]
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp
    | succ m' =>
      show (l.foldl (extendSteps K) (extendSteps K acc e)).getD
        (acc.length + (m' + 1)) _ = _
      have harith : acc.length + (m' + 1)
          = (extendSteps K acc e).length + m' := by
        show _ = (acc ++ _).length + m'
        rw [List.length_append]
        simp +arith
      rw [harith, ih (extendSteps K acc e) m' (by simp at hm; omega)]
      rfl

/-- Step 0 of every planned certificate is the root step. -/
theorem buildCert_step_zero (K : Catalog) (plan : List (Nat × Nat)) :
    (buildCert K plan).step 0 = ⟨K.root, []⟩ := by
  show (buildSteps K plan).getD 0 _ = _
  unfold buildSteps
  rw [foldl_extend_getD_stable K plan [⟨K.root, []⟩] 0 (by simp)]
  rfl

/-- Step `m+1` of a planned certificate: the child built by plan entry
    `m` on the step prefix — and by stability, its parent reference
    reads the FINAL step list. -/
theorem buildCert_step_succ (K : Catalog) (plan : List (Nat × Nat))
    {m : Nat} (hm : m < plan.length)
    (hp : (plan.getD m (0, 0)).2 < m + 1) :
    (buildCert K plan).step (m + 1)
      = ⟨(K.rule (plan.getD m (0, 0)).1).tmpl,
         (K.rule (plan.getD m (0, 0)).1).slotMap.map
           (portOccOf ((buildCert K plan).step (plan.getD m (0, 0)).2)
             (plan.getD m (0, 0)).2)⟩ := by
  show (buildSteps K plan).getD (m + 1) _ = _
  unfold buildSteps
  rw [show m + 1 = ([⟨K.root, []⟩] : List Step).length + m from by
        simp +arith,
      foldl_extend_getD_new K plan _ m hm]
  unfold childStepOf
  have hstable : ((plan.take m).foldl (extendSteps K)
        [⟨K.root, []⟩]).getD (plan.getD m (0, 0)).2 ⟨0, []⟩
      = (buildCert K plan).step (plan.getD m (0, 0)).2 := by
    show _ = (buildSteps K plan).getD _ _
    unfold buildSteps
    rw [show plan = plan.take m ++ plan.drop m from
          (List.take_append_drop m plan).symm]
    rw [List.foldl_append]
    rw [List.take_append_drop]
    rw [foldl_extend_getD_stable K (plan.drop m) _ _
        (by rw [foldl_extend_length]
            have h5 : (plan.take m).length = m := by
              rw [List.length_take]; omega
            simp only [h5, List.length_cons, List.length_nil]
            omega)]
  rw [hstable]

end Round19

namespace Round19
open Atom

/-! ### Catalogue wellformedness conditions -/

/-- Port translation along a rule: child slots to parent ports, core
    and fresh ports unchanged. -/
def mapPort (r : Attach) : TPort → TPort
  | .inl k => r.slotMap.getD k (.inr (.inl 0))
  | p => p

/-- Structural conditions on one attachment rule (all finite). -/
structure AttachOk (K : Catalog) (r : Attach) : Prop where
  tmpl_lt : r.tmpl < K.templates.length
  parent_lt : r.parentTmpl < K.templates.length
  map_len : r.slotMap.length = (K.tmpl r.tmpl).nSlots
  map_nodup : r.slotMap.Nodup
  map_member : ∀ p ∈ r.slotMap,
    (∃ k, k < (K.tmpl r.parentTmpl).nSlots ∧ p = .inl k) ∨
    (∃ j, j < (K.tmpl r.parentTmpl).nFresh ∧ p = .inr (.inr j))
  agree : ∀ p ∈ oldPorts (K.tmpl r.tmpl) K.nCore,
          ∀ q ∈ oldPorts (K.tmpl r.tmpl) K.nCore,
    (K.tmpl r.tmpl).net p q
      = (K.tmpl r.parentTmpl).net (mapPort r p) (mapPort r q)

/-- Structural conditions on the catalogue. -/
structure CatOk (K : Catalog) : Prop where
  root_valid : K.root < K.templates.length
  root_slots : (K.tmpl K.root).nSlots = 0
  net_conv : ∀ t, t < K.templates.length → ∀ p q,
    (K.tmpl t).net q p = conv ((K.tmpl t).net p q)
  F_reads : ∀ t r1 r1' r2 r2' j,
    (∀ c, c < K.nCore → r1 c = r1' c) →
    (∀ k, k < (K.tmpl t).nSlots → r2 k = r2' k) →
    K.F t r1 r2 j = K.F t r1' r2' j
  rules_ok : ∀ r ∈ K.attaches, AttachOk K r

/-- Plan validity: each entry names a real rule, an earlier parent,
    and the parent step's template matches the rule's expectation. -/
def PlanOk (K : Catalog) (plan : List (Nat × Nat)) : Prop :=
  ∀ m, m < plan.length →
    (plan.getD m (0, 0)).1 < K.attaches.length ∧
    (plan.getD m (0, 0)).2 < m + 1 ∧
    ((buildCert K plan).step (plan.getD m (0, 0)).2).tmpl
      = (K.rule (plan.getD m (0, 0)).1).parentTmpl

theorem mem_existingBefore_le {C : Cert} {m n : Nat} {x : Occ}
    (h : m ≤ n) (hx : x ∈ existingBefore C m) :
    x ∈ existingBefore C n := by
  cases x with
  | core c => exact mem_existingBefore_core.mpr (mem_existingBefore_core.mp hx)
  | born s j =>
    have h2 := mem_existingBefore_born.mp hx
    exact mem_existingBefore_born.mpr ⟨by omega, h2.2⟩

theorem pairwise_ne_map {α β : Type} {f : α → β} {l : List α}
    (hnd : l.Nodup)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → f a ≠ f b) :
    (l.map f).Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    rw [List.map_cons]
    cases hnd with
    | cons hne hnd' =>
      exact List.Pairwise.cons
        (fun b hb => by
          obtain ⟨a', ha', rfl⟩ := List.mem_map.mp hb
          exact hinj a (List.mem_cons_self ..) a'
            (List.mem_cons_of_mem _ ha') (hne a' ha'))
        (ih hnd' (fun a' ha' b' hb' =>
          hinj a' (List.mem_cons_of_mem _ ha')
            b' (List.mem_cons_of_mem _ hb')))

/-- Rules named by valid plans satisfy `AttachOk`. -/
theorem rule_ok_of_plan {K : Catalog} (hok : CatOk K)
    {r : Nat} (hr : r < K.attaches.length) : AttachOk K (K.rule r) := by
  apply hok.rules_ok
  show K.attaches.getD r _ ∈ K.attaches
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
  exact List.getElem_mem hr

/-- Reading a slot port of a step (getElem form). -/
theorem portOccOf_slot {st : Step} {i k : Nat}
    (hk : k < st.slotTargets.length) :
    portOccOf st i (.inl k) = st.slotTargets[k] := by
  show st.slotTargets.getD k (.core 0) = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

theorem portOccOf_fresh (st : Step) (i j : Nat) :
    portOccOf st i (.inr (.inr j)) = .born i j := rfl

/-- The per-step wellformedness bundle of built certificates. -/
def WfStep (C : Cert) (K : Catalog) (m : Nat) : Prop :=
  (C.step m).tmpl < K.templates.length ∧
  (C.step m).slotTargets.length = (K.tmpl (C.step m).tmpl).nSlots ∧
  (∀ t ∈ (C.step m).slotTargets,
    (∃ s j, t = Occ.born s j ∧ s < m) ∧ t ∈ existingBefore C m) ∧
  (C.step m).slotTargets.Nodup

theorem build_wfstep (K : Catalog) (hok : CatOk K)
    (plan : List (Nat × Nat)) (hplan : PlanOk K plan) :
    ∀ n m, m ≤ n → m ≤ plan.length → WfStep (buildCert K plan) K m := by
  intro n
  induction n with
  | zero =>
    intro m hmn _
    have hm0 : m = 0 := by omega
    subst hm0
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [buildCert_step_zero]
    · exact hok.root_valid
    · exact hok.root_slots.symm
    · intro t ht; cases ht
    · exact List.Pairwise.nil
  | succ n ih =>
    intro m hmn hmp
    by_cases hmn' : m ≤ n
    · exact ih m hmn' hmp
    · have hm : m = n + 1 := by omega
      subst hm
      have hnp : n < plan.length := by omega
      obtain ⟨hr, hp, hptmpl⟩ := hplan n hnp
      have hrok := rule_ok_of_plan hok hr
      have hpar : WfStep (buildCert K plan) K (plan.getD n (0, 0)).2 :=
        ih _ (by omega) (by omega)
      obtain ⟨hpt, hplen, hpborn, hpnd⟩ := hpar
      rw [hptmpl] at hplen
      have hstep := buildCert_step_succ K plan hnp hp
      -- abbreviations
      have hlen' : ((buildCert K plan).step
          (plan.getD n (0, 0)).2).slotTargets.length
          = (K.tmpl (K.rule (plan.getD n (0, 0)).1).parentTmpl).nSlots :=
        hplen
      have hinj : ∀ a ∈ (K.rule (plan.getD n (0, 0)).1).slotMap,
          ∀ b ∈ (K.rule (plan.getD n (0, 0)).1).slotMap, a ≠ b →
          portOccOf ((buildCert K plan).step (plan.getD n (0, 0)).2)
              (plan.getD n (0, 0)).2 a
            ≠ portOccOf ((buildCert K plan).step (plan.getD n (0, 0)).2)
              (plan.getD n (0, 0)).2 b := by
        intro a ha b hb hab
        cases hrok.map_member a ha with
        | inl h1 =>
          obtain ⟨k1, hk1, rfl⟩ := h1
          have hk1' : k1 < ((buildCert K plan).step
              (plan.getD n (0, 0)).2).slotTargets.length := by omega
          rw [portOccOf_slot hk1']
          cases hrok.map_member b hb with
          | inl h2 =>
            obtain ⟨k2, hk2, rfl⟩ := h2
            have hk2' : k2 < ((buildCert K plan).step
                (plan.getD n (0, 0)).2).slotTargets.length := by omega
            rw [portOccOf_slot hk2']
            have hkk : k1 ≠ k2 := fun h => hab (by rw [h])
            intro heq
            cases Nat.lt_or_ge k1 k2 with
            | inl hlt =>
              exact (List.pairwise_iff_getElem.mp hpnd k1 k2 hk1' hk2'
                hlt) heq
            | inr hge =>
              have hlt : k2 < k1 := by omega
              exact (List.pairwise_iff_getElem.mp hpnd k2 k1 hk2' hk1'
                hlt) heq.symm
          | inr h2 =>
            obtain ⟨j2, hj2, rfl⟩ := h2
            rw [portOccOf_fresh]
            obtain ⟨⟨s, j, hteq, hs⟩, _⟩ := hpborn _ (List.getElem_mem hk1')
            rw [hteq]
            intro heq
            injection heq with h3 _
            omega
        | inr h1 =>
          obtain ⟨j1, hj1, rfl⟩ := h1
          rw [portOccOf_fresh]
          cases hrok.map_member b hb with
          | inl h2 =>
            obtain ⟨k2, hk2, rfl⟩ := h2
            have hk2' : k2 < ((buildCert K plan).step
                (plan.getD n (0, 0)).2).slotTargets.length := by omega
            rw [portOccOf_slot hk2']
            obtain ⟨⟨s, j, hteq, hs⟩, _⟩ := hpborn _ (List.getElem_mem hk2')
            rw [hteq]
            intro heq
            injection heq with h3 _
            omega
          | inr h2 =>
            obtain ⟨j2, hj2, rfl⟩ := h2
            rw [portOccOf_fresh]
            have hjj : j1 ≠ j2 := fun h => hab (by rw [h])
            intro heq
            injection heq with _ h4
            exact hjj h4
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hstep]
      · exact hrok.tmpl_lt
      · show ((K.rule _).slotMap.map _).length = _
        rw [List.length_map]
        exact hrok.map_len
      · intro t ht
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
        cases hrok.map_member q hq with
        | inl h1 =>
          obtain ⟨k1, hk1, rfl⟩ := h1
          have hk1' : k1 < ((buildCert K plan).step
              (plan.getD n (0, 0)).2).slotTargets.length := by omega
          rw [portOccOf_slot hk1']
          obtain ⟨⟨s, j, hteq, hs⟩, hex⟩ := hpborn _ (List.getElem_mem hk1')
          constructor
          · exact ⟨s, j, hteq, by omega⟩
          · exact mem_existingBefore_le (by omega) hex
        | inr h1 =>
          obtain ⟨j1, hj1, rfl⟩ := h1
          rw [portOccOf_fresh]
          constructor
          · exact ⟨_, j1, rfl, by omega⟩
          · apply mem_existingBefore_born.mpr
            refine ⟨by omega, ?_⟩
            show j1 < (Cert.template _ ((buildCert K plan).step
              (plan.getD n (0, 0)).2).tmpl).nFresh
            rw [hptmpl]
            exact hj1
      · exact pairwise_ne_map hrok.map_nodup hinj

end Round19

namespace Round19
open Atom

/-! ### Wellformedness and faithfulness by construction -/

theorem build_wellformed (K : Catalog) (hok : CatOk K)
    (plan : List (Nat × Nat)) (hplan : PlanOk K plan) :
    Wellformed (buildCert K plan) := by
  have hwfs := build_wfstep K hok plan hplan plan.length
  have hlen : (buildCert K plan).steps.length = plan.length + 1 :=
    buildSteps_length K plan
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi t ht
    obtain ⟨_, _, hborn, _⟩ := hwfs i (by omega) (by omega)
    obtain ⟨⟨s, j, rfl, hs⟩, _⟩ := hborn t ht
    exact hs
  · intro i hi t ht
    obtain ⟨_, _, hborn, _⟩ := hwfs i (by omega) (by omega)
    exact (hborn t ht).2
  · intro i hi
    obtain ⟨_, hlen2, _, _⟩ := hwfs i (by omega) (by omega)
    exact hlen2
  · intro i hi
    obtain ⟨_, _, _, hnd⟩ := hwfs i (by omega) (by omega)
    exact hnd
  · intro i hi
    obtain ⟨ht, _, _, _⟩ := hwfs i (by omega) (by omega)
    exact ht
  · intro i hi p q
    obtain ⟨ht, _, _, _⟩ := hwfs i (by omega) (by omega)
    exact hok.net_conv _ ht p q
  · intro i hi r1 r1' r2 r2' j h1 h2
    exact hok.F_reads ((buildCert K plan).step i).tmpl r1 r1' r2 r2' j h1 h2

/-- `memberPort` inverts `portOcc` on member ports. -/
theorem memberPort_of_portOcc {C : Cert} (hwf : Wellformed C) {i : Nat}
    (hi : i < C.steps.length) {p : TPort}
    (hp : p ∈ memberPortsList C i) :
    memberPort C i (portOcc C i p) = some p := by
  have hs := memberPort_portOcc_isSome hwf hi hp
  cases hmp : memberPort C i (portOcc C i p) with
  | none => rw [hmp] at hs; simp at hs
  | some p2 =>
    obtain ⟨hp2m, hp2o⟩ := memberPort_spec' hwf hi
      (portOcc_mem_existing hwf hi hp) hmp
    rw [portOcc_inj hwf hi hp2m hp hp2o]

/-- Port transport into the parent: at a built step, every old child
    port reads the parent occurrence at its mapped port, which is a
    parent member port. -/
theorem built_port_parent (K : Catalog) (hok : CatOk K)
    (plan : List (Nat × Nat)) (hplan : PlanOk K plan)
    {n : Nat} (hnp : n < plan.length) {p : TPort}
    (hmem : p ∈ oldPorts (K.tmpl (K.rule (plan.getD n (0, 0)).1).tmpl)
      K.nCore) :
    portOcc (buildCert K plan) (n+1) p
      = portOcc (buildCert K plan) (plan.getD n (0, 0)).2
          (mapPort (K.rule (plan.getD n (0, 0)).1) p)
    ∧ mapPort (K.rule (plan.getD n (0, 0)).1) p
        ∈ memberPortsList (buildCert K plan) (plan.getD n (0, 0)).2 := by
  obtain ⟨hr, hp, hptmpl⟩ := hplan n hnp
  have hrok := rule_ok_of_plan hok hr
  have hstep := buildCert_step_succ K plan hnp hp
  cases mem_oldPorts_elim hmem with
  | inl h1 =>
    obtain ⟨k, hk, rfl⟩ := h1
    have hk_len : k < (K.rule (plan.getD n (0, 0)).1).slotMap.length := by
      rw [hrok.map_len]; exact hk
    have hmapk : mapPort (K.rule (plan.getD n (0, 0)).1) (.inl k)
        = (K.rule (plan.getD n (0, 0)).1).slotMap[k] := by
      show (K.rule (plan.getD n (0, 0)).1).slotMap.getD k _ = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_len]
      rfl
    constructor
    · rw [portOcc_eq_portOccOf, hstep]
      show ((K.rule (plan.getD n (0, 0)).1).slotMap.map
        (portOccOf ((buildCert K plan).step (plan.getD n (0, 0)).2)
          (plan.getD n (0, 0)).2)).getD k (.core 0) = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hk_len, hmapk]
      exact (portOcc_eq_portOccOf _ _ _).symm
    · rw [hmapk]
      cases hrok.map_member _ (List.getElem_mem hk_len) with
      | inl h2 =>
        obtain ⟨k', hk', heq⟩ := h2
        rw [heq]
        apply slotPort_mem_memberPortsList
        show k' < (Cert.template _ ((buildCert K plan).step
          (plan.getD n (0, 0)).2).tmpl).nSlots
        rw [hptmpl]
        exact hk'
      | inr h2 =>
        obtain ⟨j, hj, heq⟩ := h2
        rw [heq]
        apply freshPort_mem_memberPortsList
        show j < (Cert.template _ ((buildCert K plan).step
          (plan.getD n (0, 0)).2).tmpl).nFresh
        rw [hptmpl]
        exact hj
  | inr h1 =>
    obtain ⟨c, hc, rfl⟩ := h1
    exact ⟨rfl, corePort_mem_memberPortsList hc⟩

end Round19

namespace Round19
open Atom

/-- Faithfulness by construction: co-members of a built step carry the
    step template's net entry, by induction along parent chains using
    the rule agreement condition (the thirteenth review's
    parent-pattern agreement, discharged structurally). -/
theorem build_faithful (K : Catalog) (hok : CatOk K)
    (plan : List (Nat × Nat)) (hplan : PlanOk K plan)
    (hcc : ∀ c c', K.coreNet c' c = conv (K.coreNet c c'))
    (hcr : ∀ t, t < K.templates.length → ∀ c c', c < K.nCore →
      c' < K.nCore → c ≠ c' →
      (K.tmpl t).net (.inr (.inl c)) (.inr (.inl c')) = K.coreNet c c') :
    Faithful (buildCert K plan) := by
  have hwf := build_wellformed K hok plan hplan
  have hlen : (buildCert K plan).steps.length = plan.length + 1 :=
    buildSteps_length K plan
  have htmplEq : ∀ t, (buildCert K plan).template t = K.tmpl t :=
    fun _ => rfl
  suffices h : ∀ n i, i ≤ n → i < (buildCert K plan).steps.length →
      FaithfulAt (buildCert K plan) i by
    intro i hi
    exact h i i (Nat.le_refl i) hi
  intro n
  induction n with
  | zero =>
    intro i hin hi
    have hi0 : i = 0 := by omega
    subst hi0
    intro p hp q hq hpex hqex hne
    have htmpl0 : ((buildCert K plan).step 0).tmpl = K.root := by
      rw [buildCert_step_zero]
    cases mem_memberPortsList_elim hp with
    | inl h1 =>
      obtain ⟨k, hk, rfl⟩ := h1
      rw [htmpl0, htmplEq] at hk
      exfalso
      have := hok.root_slots
      omega
    | inr h1 =>
      cases h1 with
      | inr h2 =>
        obtain ⟨j, hj, rfl⟩ := h2
        exfalso
        exact absurd (mem_existingBefore_born.mp hpex).1 (Nat.lt_irrefl 0)
      | inl h2 =>
        obtain ⟨c, hc, rfl⟩ := h2
        cases mem_memberPortsList_elim hq with
        | inl h3 =>
          obtain ⟨k, hk, rfl⟩ := h3
          rw [htmpl0, htmplEq] at hk
          exfalso
          have := hok.root_slots
          omega
        | inr h3 =>
          cases h3 with
          | inr h4 =>
            obtain ⟨j, hj, rfl⟩ := h4
            exfalso
            exact absurd (mem_existingBefore_born.mp hqex).1
              (Nat.lt_irrefl 0)
          | inl h4 =>
            obtain ⟨c', hc', rfl⟩ := h4
            show K.coreNet c c' = (Cert.template _ ((buildCert K plan).step
              0).tmpl).net (.inr (.inl c)) (.inr (.inl c'))
            rw [htmpl0]
            exact (hcr K.root hok.root_valid c c' hc hc'
              (fun h => hne (congrArg Occ.core h))).symm
  | succ n ih =>
    intro i hin hi
    by_cases hin' : i ≤ n
    · exact ih i hin' hi
    · have hieq : i = n + 1 := by omega
      subst hieq
      have hnp : n < plan.length := by omega
      obtain ⟨hr, hp, hptmpl⟩ := hplan n hnp
      have hrok := rule_ok_of_plan hok hr
      have htmplS : ((buildCert K plan).step (n+1)).tmpl
          = (K.rule (plan.getD n (0, 0)).1).tmpl := by
        rw [buildCert_step_succ K plan hnp hp]
      have hpidx : (plan.getD n (0, 0)).2
          < (buildCert K plan).steps.length := by
        omega
      intro p hp' q hq' hpex hqex hne
      have holdport : ∀ p' ∈ memberPortsList (buildCert K plan) (n+1),
          portOcc (buildCert K plan) (n+1) p' ∈
            existingBefore (buildCert K plan) (n+1) →
          p' ∈ oldPorts (K.tmpl (K.rule (plan.getD n (0, 0)).1).tmpl)
            K.nCore := by
        intro p' hp'' hex
        cases mem_memberPortsList_elim hp'' with
        | inl h1 =>
          obtain ⟨k, hk, rfl⟩ := h1
          rw [htmplS, htmplEq] at hk
          exact slot_mem_oldPorts hk
        | inr h1 =>
          cases h1 with
          | inl h2 =>
            obtain ⟨c, hc, rfl⟩ := h2
            exact core_mem_oldPorts hc
          | inr h2 =>
            obtain ⟨j, hj, rfl⟩ := h2
            exfalso
            exact absurd (mem_existingBefore_born.mp hex).1
              (Nat.lt_irrefl (n+1))
      have hpold := holdport p hp' hpex
      have hqold := holdport q hq' hqex
      obtain ⟨hxp, hpmem⟩ := built_port_parent K hok plan hplan hnp hpold
      obtain ⟨hyq, hqmem⟩ := built_port_parent K hok plan hplan hnp hqold
      have hxE := portOcc_mem_existing hwf hpidx hpmem
      have hyE := portOcc_mem_existing hwf hpidx hqmem
      have hmpx := memberPort_of_portOcc hwf hpidx hpmem
      have hmpy := memberPort_of_portOcc hwf hpidx hqmem
      have hne' : portOcc (buildCert K plan) (plan.getD n (0, 0)).2
            (mapPort (K.rule (plan.getD n (0, 0)).1) p)
          ≠ portOcc (buildCert K plan) (plan.getD n (0, 0)).2
            (mapPort (K.rule (plan.getD n (0, 0)).1) q) := by
        rw [← hxp, ← hyq]
        exact hne
      have hval := member_pair_val hwf hcc hpidx
        (ih (plan.getD n (0, 0)).2 (by omega) hpidx)
        hxE hyE hmpx hmpy hne'
      rw [hxp, hyq, hval, htmplS, hptmpl]
      exact (hrok.agree p hpold q hqold).symm

end Round19

namespace Round19
open Atom

/-! ### Round-23 capstone: soundness from the catalogue -/

/-- ROUND-23 MAIN THEOREM: for a structurally sound catalogue, EVERY
    valid plan's certificate is wellformed and faithful BY
    CONSTRUCTION, so the catalogue-level check `SCat` alone yields the
    full per-unfolding `SCond`.  "Every unfolding of the catalogue" is
    now a theorem about a syntactic object (`buildCert`), not a
    hypothesis pair. -/
theorem catalogue_soundness (K : Catalog) (hok : CatOk K)
    (hcc : ∀ c c', K.coreNet c' c = conv (K.coreNet c c'))
    (hcr : ∀ t, t < K.templates.length → ∀ c c', c < K.nCore →
      c' < K.nCore → c ≠ c' →
      (K.tmpl t).net (.inr (.inl c)) (.inr (.inl c')) = K.coreNet c c')
    (plan : List (Nat × Nat)) (hplan : PlanOk K plan)
    (hscat : SCat (buildCert K plan)) :
    SCond (buildCert K plan) :=
  scat_scond _ (build_wellformed K hok plan hplan) hscat
    (build_faithful K hok plan hplan hcc hcr)

/-- Operational form: every planned certificate's frame is
    composition-closed on every distinct existing triangle. -/
theorem catalogue_frame_closed (K : Catalog) (hok : CatOk K)
    (hcc : ∀ c c', K.coreNet c' c = conv (K.coreNet c c'))
    (hcr : ∀ t, t < K.templates.length → ∀ c c', c < K.nCore →
      c' < K.nCore → c ≠ c' →
      (K.tmpl t).net (.inr (.inl c)) (.inr (.inl c')) = K.coreNet c c')
    (plan : List (Nat × Nat)) (hplan : PlanOk K plan)
    (hscat : SCat (buildCert K plan))
    {x y z : Occ} {v1 v2 v3 : Atom}
    (hx : x ∈ existingBefore (buildCert K plan) (buildCert K plan).steps.length)
    (hy : y ∈ existingBefore (buildCert K plan) (buildCert K plan).steps.length)
    (hz : z ∈ existingBefore (buildCert K plan) (buildCert K plan).steps.length)
    (hxy : x ≠ y) (hxz : x ≠ z) (hzy : z ≠ y)
    (h1 : Frame.get? (unfoldAll (buildCert K plan)) x y = some v1)
    (h2 : Frame.get? (unfoldAll (buildCert K plan)) x z = some v2)
    (h3 : Frame.get? (unfoldAll (buildCert K plan)) z y = some v3) :
    v1 ∈ comp v2 v3 :=
  frame_closed (buildCert K plan)
    (build_wellformed K hok plan hplan)
    (catalogue_soundness K hok hcc hcr plan hplan hscat)
    hx hy hz hxy hxz hzy h1 h2 h3

end Round19

namespace Round19
open Atom

/-! ### A kernel-checked catalogue witness (round-23)

`certK` mirrors `certC`'s geometry as a CATALOGUE: a root template
(2 fresh ports) and a child rule whose single slot inherits the root's
fresh port 1.  It is structurally sound (`certK_catok`); every plan is
wellformed and faithful by construction; and for a concrete plan the
catalogue check `SCat` holds, so the built certificate satisfies the
full `SCond` — obtained without any per-certificate wellformedness or
faithfulness proof. -/

def certK : Catalog where
  nCore := 0
  coreNet := fun _ _ => Atom.dr
  templates :=
    [ ⟨0, 2, fun _ _ => Atom.dr⟩,
      ⟨1, 1, fun _ _ => Atom.dr⟩ ]
  root := 0
  attaches := [⟨1, 0, [.inr (.inr 1)]⟩]
  F := fun _ _ _ _ => Atom.dr

theorem certK_attachok : AttachOk certK (certK.rule 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem certK_catok : CatOk certK := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · intro t ht p q
    match t with
    | 0 => rfl
    | 1 => rfl
    | n+2 =>
      have h2 : certK.templates.length = 2 := rfl
      omega
  · intro t r1 r1' r2 r2' j h1 h2
    rfl
  · intro r hr
    have hr' : r = ⟨1, 0, [.inr (.inr 1)]⟩ := by
      rw [show certK.attaches = [⟨1, 0, [.inr (.inr 1)]⟩] from rfl] at hr
      cases hr with
      | head => rfl
      | tail _ h => cases h
    subst hr'
    exact certK_attachok

/-- The one-child plan: rule 0 attached to the root (step 0). -/
def planK : List (Nat × Nat) := [(0, 0)]

theorem certK_planok : PlanOk certK planK := by
  intro m hm
  have hm0 : m = 0 := by
    have : planK.length = 1 := rfl
    omega
  subst hm0
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · native_decide

theorem certK_scat : SCat (buildCert certK planK) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c c'; rfl
  · intro c c' hc hc' hne
    have : (buildCert certK planK).nCore = 0 := rfl
    omega
  · intro c1 c2 c3 h1 h2 h3 h4 h5 h6
    have : (buildCert certK planK).nCore = 0 := rfl
    omega
  · intro i hi c c' hc hc' hne
    have : (buildCert certK planK).nCore = 0 := rfl
    omega
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- The whole round-19..23 pipeline on one object: a planned
    certificate whose wellformedness and faithfulness are free from
    the catalogue, whose catalogue check passes, and which therefore
    satisfies the per-unfolding S-condition. -/
theorem certK_scond : SCond (buildCert certK planK) :=
  catalogue_soundness certK certK_catok (fun _ _ => rfl)
    (fun t ht c c' hc _ _ => by
      have : certK.nCore = 0 := rfl
      omega)
    planK certK_planok certK_scat

/-- ... and every frame triangle of the built certificate is closed. -/
example {x y z : Occ} {v1 v2 v3 : Atom}
    (hx : x ∈ existingBefore (buildCert certK planK)
      (buildCert certK planK).steps.length)
    (hy : y ∈ existingBefore (buildCert certK planK)
      (buildCert certK planK).steps.length)
    (hz : z ∈ existingBefore (buildCert certK planK)
      (buildCert certK planK).steps.length)
    (hxy : x ≠ y) (hxz : x ≠ z) (hzy : z ≠ y)
    (h1 : Frame.get? (unfoldAll (buildCert certK planK)) x y = some v1)
    (h2 : Frame.get? (unfoldAll (buildCert certK planK)) x z = some v2)
    (h3 : Frame.get? (unfoldAll (buildCert certK planK)) z y = some v3) :
    v1 ∈ comp v2 v3 :=
  frame_closed _ (build_wellformed certK certK_catok planK certK_planok)
    certK_scond hx hy hz hxy hxz hzy h1 h2 h3

end Round19

namespace Round19
open Atom

/-! ## 11. Round-24: the logic layer (syntax, semantics, truth lemma)

Rounds 19-23 build a composition-closed, converse-coherent, EQ-free
atomic frame from a catalogue.  This section adds the DESCRIPTION LOGIC
on top: ALCI_RCC5 concepts in negation normal form, their semantics
over such a frame, Hintikka systems (locally coherent type
labellings), and the TRUTH LEMMA — every concept in an occurrence's
type is satisfied there.  The capstone `sat_from_hintikka` turns any
certificate carrying a root-anchored Hintikka labelling into an RCC5
MODEL of the target concept; `certInterp_rcc5` proves the pipeline
frame is a legitimate RCC5 interpretation frame.  (What round-25+ must
add: the catalogue generator PRODUCES such a Hintikka labelling for a
satisfiable input — the completeness/construction direction.) -/

/-- ALCI_RCC5 concepts in NNF.  Roles are the RCC5 atoms; inverse
    roles are absorbed (∃PP⁻.C = ∃PPI.C), per the project convention. -/
inductive Concept
  | top | bot
  | atom (a : Nat)
  | natom (a : Nat)
  | and (c d : Concept)
  | or (c d : Concept)
  | ex (r : Atom) (c : Concept)
  | all (r : Atom) (c : Concept)
deriving DecidableEq, Repr

/-- An interpretation: a domain predicate, the atomic RCC5 relation
    (a total single-valued function — a proper atomic network), and an
    atomic-concept extension. -/
structure Interp where
  dom : Occ → Prop
  rho : Occ → Occ → Atom
  val : Nat → Occ → Prop

/-- Satisfaction, structural on the concept. -/
def sat (I : Interp) : Occ → Concept → Prop
  | _, .top => True
  | _, .bot => False
  | x, .atom a => I.val a x
  | x, .natom a => ¬ I.val a x
  | x, .and c d => sat I x c ∧ sat I x d
  | x, .or c d => sat I x c ∨ sat I x d
  | x, .ex r c => ∃ y, I.dom y ∧ I.rho x y = r ∧ sat I y c
  | x, .all r c => ∀ y, I.dom y → I.rho x y = r → sat I y c

/-- The canonical interpretation induced by a type labelling: an atom
    holds exactly where its concept is in the type. -/
def typeInterp (dom : Occ → Prop) (rho : Occ → Occ → Atom)
    (τ : Occ → List Concept) : Interp :=
  ⟨dom, rho, fun a x => Concept.atom a ∈ τ x⟩

/-- A Hintikka system: a locally coherent type labelling.  Clash-free
    and bot-free literals; ∧/∨ decomposed; ∀ propagated to
    r-neighbours; ∃ fulfilled by an r-neighbour (one-step fulfilment
    — no promissory witnesses, so no eventuality/parity condition). -/
structure Hintikka (dom : Occ → Prop) (rho : Occ → Occ → Atom)
    (τ : Occ → List Concept) : Prop where
  clashfree : ∀ x a, dom x → Concept.atom a ∈ τ x → Concept.natom a ∉ τ x
  nobot : ∀ x, dom x → Concept.bot ∉ τ x
  and_c : ∀ x c d, dom x → Concept.and c d ∈ τ x → c ∈ τ x ∧ d ∈ τ x
  or_c : ∀ x c d, dom x → Concept.or c d ∈ τ x → c ∈ τ x ∨ d ∈ τ x
  all_c : ∀ x r c, dom x → Concept.all r c ∈ τ x →
    ∀ y, dom y → rho x y = r → c ∈ τ y
  ex_f : ∀ x r c, dom x → Concept.ex r c ∈ τ x →
    ∃ y, dom y ∧ rho x y = r ∧ c ∈ τ y

/-- THE TRUTH LEMMA: every concept in an occurrence's type is
    satisfied at that occurrence, under the canonical interpretation.
    Structural induction on the concept; each case is exactly one
    Hintikka clause plus the induction hypotheses. -/
theorem truth_lemma (dom : Occ → Prop) (rho : Occ → Occ → Atom)
    (τ : Occ → List Concept) (H : Hintikka dom rho τ) :
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

end Round19

namespace Round19
open Atom

/-! ### The pipeline frame is an RCC5 interpretation frame -/

/-- What makes an interpretation a legitimate ALCI_RCC5 model: the
    relation is reflexively EQ, strong-EQ is identity, converse-coherent
    (R2), and composition-closed (R3). -/
structure RCC5Interp (I : Interp) : Prop where
  refl_eq : ∀ x, I.dom x → I.rho x x = Atom.eq
  eq_id : ∀ x y, I.dom x → I.dom y → I.rho x y = Atom.eq → x = y
  conv_ : ∀ x y, I.dom x → I.dom y → I.rho y x = conv (I.rho x y)
  comp_ : ∀ x y z, I.dom x → I.dom y → I.dom z →
    I.rho x z ∈ comp (I.rho x y) (I.rho y z)

theorem comp_eq_left (b : Atom) : comp Atom.eq b = [b] := rfl
theorem comp_eq_right : ∀ a, comp a Atom.eq = [a] := by intro a; cases a <;> rfl
theorem eq_mem_comp_conv : ∀ a, Atom.eq ∈ comp a (conv a) := by
  intro a; cases a <;> decide

/-- The interpretation induced by a certificate: domain = existing
    occurrences, relation = `pairVal` off the diagonal and EQ on it,
    atoms from a type labelling. -/
def certInterp (C : Cert) (τ : Occ → List Concept) : Interp :=
  typeInterp (fun x => x ∈ existingBefore C C.steps.length)
    (fun x y => if x = y then Atom.eq else pairVal C x y) τ

/-- ROUND-24 BRIDGE: a wellformed, S-conditioned certificate's frame
    is a legitimate RCC5 interpretation frame — reflexive EQ, strong
    EQ = identity (`pairVal_proper`), R2 (`pairVal_conv`) and R3
    (`pairVal_closed`). -/
theorem certInterp_rcc5 (C : Cert) (hwf : Wellformed C) (hs : SCond C)
    (τ : Occ → List Concept) : RCC5Interp (certInterp C τ) := by
  constructor
  · intro x _
    show (if x = x then Atom.eq else pairVal C x x) = Atom.eq
    rw [if_pos rfl]
  · intro x y hx hy h
    by_cases hxy : x = y
    · exact hxy
    · exfalso
      have h2 : pairVal C x y = Atom.eq := by
        have hr : (certInterp C τ).rho x y = pairVal C x y := by
          show (if x = y then Atom.eq else pairVal C x y) = _
          rw [if_neg hxy]
        rw [hr] at h; exact h
      exact pairVal_proper C hwf hs x y hx hy hxy h2
  · intro x y hx hy
    by_cases hxy : x = y
    · subst hxy
      show (if x = x then Atom.eq else pairVal C x x)
        = conv (if x = x then Atom.eq else pairVal C x x)
      rw [if_pos rfl]
      rfl
    · show (if y = x then Atom.eq else pairVal C y x)
        = conv (if x = y then Atom.eq else pairVal C x y)
      rw [if_neg (fun h => hxy h.symm), if_neg hxy]
      exact pairVal_conv C hwf hs.core_conv hxy (birthBound hx) (birthBound hy)
  · intro x y z hx hy hz
    show (if x = z then Atom.eq else pairVal C x z)
      ∈ comp (if x = y then Atom.eq else pairVal C x y)
             (if y = z then Atom.eq else pairVal C y z)
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, comp_eq_left]
      exact List.mem_cons_self ..
    · by_cases hyz : y = z
      · subst hyz
        rw [if_pos rfl, comp_eq_right]
        exact List.mem_cons_self ..
      · by_cases hxz : x = z
        · rw [if_pos hxz, if_neg hxy, if_neg hyz,
              ← congrArg (pairVal C y) hxz,
              pairVal_conv C hwf hs.core_conv hxy (birthBound hx)
                (birthBound hy)]
          exact eq_mem_comp_conv _
        · rw [if_neg hxz, if_neg hxy, if_neg hyz]
          exact pairVal_closed C hwf hs x z y hx hz hy hxz hxy hyz

/-- Concept satisfiability over an RCC5 frame. -/
def Satisfiable (C0 : Concept) : Prop :=
  ∃ I : Interp, RCC5Interp I ∧ ∃ x, I.dom x ∧ sat I x C0

/-! ### Capstone: a certificate + a Hintikka labelling = a model -/

/-- ROUND-24 MAIN THEOREM: a wellformed, S-conditioned certificate
    whose frame carries a Hintikka labelling putting `C0` at an
    existing root yields an RCC5 model of `C0`.  Combined with
    `catalogue_soundness`, `SCat`/`Faithful` supply the S-condition; the
    remaining obligation — that the catalogue GENERATOR produces such a
    labelling for a satisfiable `C0` — is the round-25 construction. -/
theorem sat_from_hintikka (C : Cert) (hwf : Wellformed C) (hs : SCond C)
    (τ : Occ → List Concept)
    (H : Hintikka (fun x => x ∈ existingBefore C C.steps.length)
      (fun x y => if x = y then Atom.eq else pairVal C x y) τ)
    (root : Occ) (hroot : root ∈ existingBefore C C.steps.length)
    (C0 : Concept) (hC0 : C0 ∈ τ root) :
    Satisfiable C0 :=
  ⟨certInterp C τ, certInterp_rcc5 C hwf hs τ, root, hroot,
    truth_lemma _ _ τ H C0 root hroot hC0⟩

/-! ### Non-vacuity: a concrete satisfiable concept and model -/

/-- `A₀ ⊓ ∀DR.⊥` is satisfiable in a one-point RCC5 model (the point
    has no DR-neighbour, so the ∀DR is vacuous). -/
theorem sample_satisfiable :
    Satisfiable (Concept.and (.atom 0) (.all Atom.dr .bot)) := by
  refine ⟨⟨fun x => x = Occ.core 0, fun _ _ => Atom.eq,
           fun a x => a = 0 ∧ x = Occ.core 0⟩, ?_, Occ.core 0, rfl, ?_⟩
  · constructor
    · intro x _; rfl
    · intro x y hx hy _; rw [hx, hy]
    · intro x y _ _; rfl
    · intro x y z _ _ _
      show Atom.eq ∈ comp Atom.eq Atom.eq
      decide
  · refine ⟨?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · intro y _ hr
      exact Atom.noConfusion hr

end Round19

namespace Round19
open Atom

/-! ## 12. Round-25: completeness of the Hintikka abstraction

Round-24 proved the SOUNDNESS direction (a certificate + a Hintikka
labelling ⟹ a model).  This section proves the abstraction is also
COMPLETE: every model induces a Hintikka labelling, so
satisfiability and Hintikka-realizability COINCIDE — the type-system
certificate loses nothing.  Combined, the decidability of ALCI_RCC5
concept satisfiability reduces to ONE remaining obligation: that a
satisfiable concept admits a FINITE such labelling with a bounded
catalogue (`CompletenessObligation` below) — the standing open
mathematics F6 (width budgets) and W2′ (uniformization).  We do NOT
prove that obligation and we do NOT axiomatize it. -/

/-- Hintikka labelling as a predicate (subsumes the List version;
    used for the abstract completeness theorem where the domain need
    not be a certificate's occurrences). -/
structure HintikkaP (I : Interp) (τ : Occ → Concept → Prop) : Prop where
  val_atom : ∀ x a, I.dom x → τ x (.atom a) → I.val a x
  val_natom : ∀ x a, I.dom x → τ x (.natom a) → ¬ I.val a x
  nobot : ∀ x, I.dom x → ¬ τ x .bot
  and_c : ∀ x c d, I.dom x → τ x (.and c d) → τ x c ∧ τ x d
  or_c : ∀ x c d, I.dom x → τ x (.or c d) → τ x c ∨ τ x d
  all_c : ∀ x r c, I.dom x → τ x (.all r c) →
    ∀ y, I.dom y → I.rho x y = r → τ y c
  ex_f : ∀ x r c, I.dom x → τ x (.ex r c) →
    ∃ y, I.dom y ∧ I.rho x y = r ∧ τ y c

/-- Truth lemma, predicate form: every labelled concept is satisfied. -/
theorem truth_lemmaP (I : Interp) (τ : Occ → Concept → Prop)
    (H : HintikkaP I τ) : ∀ C x, I.dom x → τ x C → sat I x C := by
  intro C
  induction C with
  | top => intro x _ _; exact True.intro
  | bot => intro x hx hmem; exact absurd hmem (H.nobot x hx)
  | atom a => intro x hx hmem; exact H.val_atom x a hx hmem
  | natom a => intro x hx hmem; exact H.val_natom x a hx hmem
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

/-- COMPLETENESS of the abstraction: every interpretation's own
    satisfaction relation is a Hintikka labelling — the Hintikka
    clauses are literally the recursion clauses of `sat`. -/
theorem model_hintikkaP (I : Interp) :
    HintikkaP I (fun x C => sat I x C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x a _ h; exact h
  · intro x a _ h; exact h
  · intro x _ h; exact h
  · intro x c d _ h; exact h
  · intro x c d _ h; exact h
  · intro x r c _ h; exact h
  · intro x r c _ h; exact h

/-- Satisfiability and Hintikka-realizability COINCIDE.  `→` is
    completeness (`model_hintikkaP`); `←` is soundness
    (`truth_lemmaP`).  So the type-system certificate is a faithful
    abstraction of models — it loses nothing. -/
theorem satisfiable_iff_hintikkaP (C0 : Concept) :
    Satisfiable C0 ↔
      ∃ I, RCC5Interp I ∧ ∃ τ, HintikkaP I τ ∧ ∃ x, I.dom x ∧ τ x C0 := by
  constructor
  · rintro ⟨I, hI, x, hx, hsat⟩
    exact ⟨I, hI, (fun x C => sat I x C), model_hintikkaP I, x, hx, hsat⟩
  · rintro ⟨I, hI, τ, H, x, hx, hmem⟩
    exact ⟨I, hI, x, hx, truth_lemmaP I τ H C0 x hx hmem⟩

/-- A List-`Hintikka` labelling induces a `HintikkaP` labelling over
    the canonical interpretation — feeding round-24's certificate
    labellings into the abstract framework. -/
theorem hintikka_listP (dom : Occ → Prop) (rho : Occ → Occ → Atom)
    (τ : Occ → List Concept) (H : Hintikka dom rho τ) :
    HintikkaP (typeInterp dom rho τ) (fun x C => C ∈ τ x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x a _ h; exact h
  · intro x a hx h hval; exact H.clashfree x a hx hval h
  · intro x hx h; exact H.nobot x hx h
  · intro x c d hx h; exact H.and_c x c d hx h
  · intro x c d hx h; exact H.or_c x c d hx h
  · intro x r c hx h; exact H.all_c x r c hx h
  · intro x r c hx h; exact H.ex_f x r c hx h

/-! ### The completeness interface and the standing obligation -/

/-- COMPLETENESS INTERFACE: a generated catalogue (sound + valid plan
    + catalogue check + faithful) carrying a root-anchored Hintikka
    labelling yields a model — the exact output shape the round-25
    generator must produce. -/
theorem generated_satisfiable (K : Catalog) (hok : CatOk K)
    (hcc : ∀ c c', K.coreNet c' c = conv (K.coreNet c c'))
    (hcr : ∀ t, t < K.templates.length → ∀ c c', c < K.nCore →
      c' < K.nCore → c ≠ c' →
      (K.tmpl t).net (.inr (.inl c)) (.inr (.inl c')) = K.coreNet c c')
    (plan : List (Nat × Nat)) (hplan : PlanOk K plan)
    (hscat : SCat (buildCert K plan))
    (τ : Occ → List Concept)
    (H : Hintikka
      (fun x => x ∈ existingBefore (buildCert K plan)
        (buildCert K plan).steps.length)
      (fun x y => if x = y then Atom.eq
        else pairVal (buildCert K plan) x y) τ)
    (root : Occ)
    (hroot : root ∈ existingBefore (buildCert K plan)
      (buildCert K plan).steps.length)
    (C0 : Concept) (hC0 : C0 ∈ τ root) :
    Satisfiable C0 :=
  sat_from_hintikka (buildCert K plan)
    (build_wellformed K hok plan hplan)
    (catalogue_soundness K hok hcc hcr plan hplan hscat)
    τ H root hroot C0 hC0

/-- THE STANDING OPEN OBLIGATION (stated, NOT proved, NOT axiomatized):
    every satisfiable concept admits a finite catalogue + valid plan +
    root-anchored Hintikka labelling.  Its two hard sub-parts are the
    project's long-standing open items — F6 (the `K(C₀)` width budget
    bounding the catalogue) and W2′ (uniformization).  With this
    obligation, `satisfiable_iff_hintikkaP` + `generated_satisfiable`
    would close the completeness direction; the finite type space (≤
    `2^|closure(C₀)|`) then yields a decision procedure. -/
def CompletenessObligation : Prop :=
  ∀ C0 : Concept, Satisfiable C0 →
    ∃ (K : Catalog) (plan : List (Nat × Nat))
      (τ : Occ → List Concept) (root : Occ),
      CatOk K ∧
      (∀ c c', K.coreNet c' c = conv (K.coreNet c c')) ∧
      (∀ t, t < K.templates.length → ∀ c c', c < K.nCore → c' < K.nCore →
        c ≠ c' →
        (K.tmpl t).net (.inr (.inl c)) (.inr (.inl c')) = K.coreNet c c') ∧
      PlanOk K plan ∧ SCat (buildCert K plan) ∧
      Hintikka
        (fun x => x ∈ existingBefore (buildCert K plan)
          (buildCert K plan).steps.length)
        (fun x y => if x = y then Atom.eq
          else pairVal (buildCert K plan) x y) τ ∧
      root ∈ existingBefore (buildCert K plan)
        (buildCert K plan).steps.length ∧
      C0 ∈ τ root

end Round19

namespace Round19
open Atom

/-- Non-vacuity of the completeness direction with a REAL fulfilled
    existential: `A₀ ⊓ ∃DR.A₁` is satisfiable in a two-point DR model
    (the root has a genuine DR-neighbour carrying `A₁`).  This is the
    crux the no-automata thread never discharged — here the ∃-demand is
    met by an actual neighbour, one-step, with the frame's composition
    closure holding (all off-diagonal DR, `comp DR DR ∋ DR, EQ`). -/
theorem sample_satisfiable_ex :
    Satisfiable (Concept.and (.atom 0) (.ex Atom.dr (.atom 1))) := by
  refine ⟨⟨fun x => x = Occ.born 0 0 ∨ x = Occ.born 0 1,
           fun x y => if x = y then Atom.eq else Atom.dr,
           fun a x => (a = 0 ∧ x = Occ.born 0 0)
                    ∨ (a = 1 ∧ x = Occ.born 0 1)⟩,
          ?_, Occ.born 0 0, Or.inl rfl, ?_⟩
  · constructor
    · intro x _
      show (if x = x then Atom.eq else Atom.dr) = Atom.eq
      rw [if_pos rfl]
    · intro x y _ _ h
      by_cases hxy : x = y
      · exact hxy
      · exfalso
        have h' : (if x = y then Atom.eq else Atom.dr) = Atom.eq := h
        rw [if_neg hxy] at h'
        exact Atom.noConfusion h'
    · intro x y _ _
      by_cases hxy : x = y
      · subst hxy
        show (if x = x then Atom.eq else Atom.dr)
          = conv (if x = x then Atom.eq else Atom.dr)
        rw [if_pos rfl]
        rfl
      · show (if y = x then Atom.eq else Atom.dr)
          = conv (if x = y then Atom.eq else Atom.dr)
        rw [if_neg (fun h => hxy h.symm), if_neg hxy]
        rfl
    · intro x y z _ _ _
      show (if x = z then Atom.eq else Atom.dr)
        ∈ comp (if x = y then Atom.eq else Atom.dr)
               (if y = z then Atom.eq else Atom.dr)
      by_cases h1 : x = y
      · by_cases h2 : y = z
        · rw [if_pos h1, if_pos h2, if_pos (h1.trans h2)]; decide
        · rw [if_pos h1, if_neg h2, if_neg (fun hc => h2 (h1 ▸ hc))]; decide
      · by_cases h2 : y = z
        · rw [if_neg h1, if_pos h2, if_neg (fun hc => h1 (hc.trans h2.symm))]
          decide
        · by_cases h3 : x = z
          · rw [if_neg h1, if_neg h2, if_pos h3]; decide
          · rw [if_neg h1, if_neg h2, if_neg h3]; decide
  · refine ⟨?_, ?_⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact ⟨Occ.born 0 1, Or.inr rfl, by decide, Or.inr ⟨rfl, rfl⟩⟩

end Round19
