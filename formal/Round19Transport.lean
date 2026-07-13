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
def Faithful (C : Cert) : Prop :=
  ∀ i, i < C.steps.length →
    ∀ p ∈ memberPortsList C i, ∀ q ∈ memberPortsList C i,
    portOcc C i p ∈ existingBefore C i →
    portOcc C i q ∈ existingBefore C i →
    portOcc C i p ≠ portOcc C i q →
    pairVal C (portOcc C i p) (portOcc C i q)
      = (C.template (C.step i).tmpl).net p q

/-- Two members' mutual value is the current template's net entry. -/
theorem member_pair_val {C : Cert} (hwf : Wellformed C)
    (hcc : ∀ c c', C.coreNet c' c = conv (C.coreNet c c'))
    (hfaith : Faithful C) {i : Nat} (hi : i < C.steps.length)
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
      have h := hfaith i hi px hpxm py hpym (hpxo ▸ hxo) (hpyo ▸ hyo)
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
      rw [member_pair_val hwf hcat.core_conv hfaith hi hx hy hmpx hmpy hxy,
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
  unfold Faithful
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
