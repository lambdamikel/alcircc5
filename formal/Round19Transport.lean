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
  5. The U-characterization theorem `uSource_eq_frame` (STATED, sorry):
     on wellformed certificates, `uSource` agrees with the operational
     frame.  This is the exact statement that prose failed to render
     correctly in rounds 17 and 18; here it is a fixed, unambiguous
     proof obligation -- the mechanization frontier.
  6. The thirteenth review's witnesses A/B/D as kernel-checked
     examples: the co-birth value is reachable by uSource (A'), the
     mis-source distinction (B'), and the S4-critical pin (D').
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

/-- One attachment step: pattern values between the copy's members
    (only for pairs not already bound -- no overwrite structurally),
    then steering values from every pre-existing non-member to every
    fresh port.  The frame itself is the steering ledger. -/
def doStep (C : Cert) (F : Frame) (i : Nat) : Frame :=
  let T := C.template (C.step i).tmpl
  let memberPorts : List TPort :=
    (List.range T.nSlots).map .inl ++
    (List.range C.nCore).map (fun c => .inr (.inl c)) ++
    (List.range T.nFresh).map (fun j => .inr (.inr j))
  let patternVals : Frame :=
    memberPorts.flatMap (fun p =>
      memberPorts.filterMap (fun q =>
        let xo := portOcc C i p
        let yo := portOcc C i q
        if xo ≠ yo && (Frame.get? F xo yo).isNone
        then some ((xo, yo), T.net p q) else none))
  let steered := (existingBefore C i).filter
    (fun x => (memberPort C i x).isNone)
  let steeringVals : Frame :=
    steered.flatMap (fun x =>
      (List.range T.nFresh).flatMap (fun j =>
        let v := C.f i (coreRowOf C F x) (slotRowOf C F i x) j
        [((x, .born i j), v), ((.born i j, x), conv v)]))
  F ++ patternVals ++ steeringVals

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
    birth.  Hence depth ≤ 2·steps + 2; we take a safe margin.  Fuel
    adequacy on wellformed certificates is a stated obligation
    alongside `uSource_eq_frame` (WP34 exercises it empirically; its
    own development caught an insufficient `steps + 1` bound). -/
def uSource (C : Cert) (x y : Occ) : Atom :=
  uSourceFuel C (2 * C.steps.length + 4) x y

/-! ## 5. Wellformedness and the characterization obligation -/

/-- Minimal wellformedness (17.4 port discipline, N1/N2 skeleton):
    every slot target pre-exists its step, targets are pairwise
    distinct (injectivity), and template indices are valid. -/
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
  targets_injective :
    ∀ i, i < C.steps.length → (C.step i).slotTargets.Nodup
  tmpl_valid :
    ∀ i, i < C.steps.length → (C.step i).tmpl < C.templates.length

/-- THE mechanization frontier (the statement rounds 17 and 18 failed
    to render in prose): on wellformed certificates the source-oriented
    update agrees with the operational frame on all distinct existing
    occurrences.  Proving this (and the fuel-adequacy lemma it
    presupposes) is the round-20 task; here it is a fixed, unambiguous
    obligation that cannot drift from the definitions above. -/
theorem uSource_eq_frame (C : Cert) (_hwf : Wellformed C) :
    ∀ x y, x ≠ y →
      x ∈ existingBefore C C.steps.length →
      y ∈ existingBefore C C.steps.length →
      (∀ c c', ¬(x = .core c ∧ y = .core c')) →   -- core-core lives in coreNet
      Frame.get? (unfoldAll C) x y = some (uSource C x y) := by
  sorry

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
