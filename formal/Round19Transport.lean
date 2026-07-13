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
