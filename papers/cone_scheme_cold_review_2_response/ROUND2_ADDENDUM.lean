
/-! ############################################################
    ## COLD REVIEW 2 — ADDENDUM (reviewer's code, appended)

    Claim under test: `coneScheme_unsat_full` is a sound UNSAT test for the
    FULL logic.  It is.  The question is how much it can ever refute.

    This addendum proves, in the kernel:

    (1) `Cpo = ∃PO.⊤ ⊓ ∀PO.⊥` is UNSATISFIABLE (two lines of semantics), and
        NOT `∀PO`-free, so `coneScheme_correct` does not cover it — it is
        exactly the kind of concept the full-logic bonus theorem is for;
    (2) the shipped elimination NEVER removes a signature carrying `Cpo`, at
        ANY round.  So `coneScheme_unsat_full`'s hypothesis is unreachable for
        `Cpo`: the test is silent on it, permanently;
    (3) the reason is a MISSING CLAUSE, not an inherent limit: `∀PO` bodies
        propagate across a `PO` edge in both directions (`conv PO = PO`), and
        `compatB` drops that.  `compatB'` adds it back;
    (4) the addition is COMPLETE — `dkey_compat'` holds for real model edges,
        so `coneScheme_complete` and `coneScheme_unsat_full` survive verbatim
        with `pruneSig'` in place of `pruneSig`; and
    (5) with it, `Cpo` IS refuted, after ONE round, by an argument that
        enumerates nothing.
    ############################################################ -/

namespace POFreeLift

open Atom

section ColdReview2

variable {α : Type} {I : Interp α}

/-! ### (1) The witness concept -/

/-- `∃PO.⊤ ⊓ ∀PO.⊥`. -/
def Cpo : Concept := .and (.ex po .top) (.all po .bot)

/-- Outside the fragment `coneScheme_correct` decides. -/
theorem cpo_not_pofree : ¬ POFree Cpo := by
  intro h
  exact h.2.1 rfl

/-- Unsatisfiable: the `∃PO` witness is its own `∀PO` victim. -/
theorem cpo_unsat : ¬ Satisfiable Cpo := by
  rintro ⟨α, I, hI, x, hx, hsat⟩
  obtain ⟨⟨y, hy, hxy, -⟩, hall⟩ := hsat
  exact hall y hy hxy

/-! ### (2) The shipped test is permanently silent on it -/

theorem nil_mem_sublists {γ : Type} : ∀ l : List γ, ([] : List γ) ∈ sublists l := by
  intro l
  induction l with
  | nil => exact List.Mem.head _
  | cons a t ih =>
      show ([] : List γ) ∈ sublists t ++ (sublists t).map (a :: ·)
      exact List.mem_append.mpr (Or.inl ih)

/-- The support type that carries `Cpo`, as a sublist of `cl Cpo`
    (`cl Cpo = [Cpo, ∃PO.⊤, ⊤, ∀PO.⊥, ⊥]`; this drops only `⊥`). -/
def Tpo : List Concept := [Cpo, .ex po .top, .top, .all po .bot]

/-- The signature: that type, with an empty predecessor spectrum. -/
def Qpo : Sig := (Tpo, [])

theorem qpo_mem_keyEnum : Qpo ∈ keyEnum Cpo := by
  rw [keyEnum, List.mem_flatMap]
  refine ⟨Tpo, by decide, ?_⟩
  rw [List.mem_map]
  exact ⟨[], nil_mem_sublists _, rfl⟩

theorem qpo_mem_sigStatic : Qpo ∈ sigStatic Cpo :=
  mem_sigStatic Cpo Qpo qpo_mem_keyEnum (by decide)

/-- `Qpo` serves its own `∃PO.⊤` demand, because `compatB` at `PO` asks only
    that the target carry the body — and `Qpo` carries `⊤`. -/
theorem qpo_self_closed : ∀ q ∈ [Qpo], q ∈ pruneSig [Qpo] := by decide

/-- **THE BLIND SPOT.**  A signature carrying `Cpo` survives EVERY round of the
    shipped elimination.  So for `Cpo` the hypothesis of `coneScheme_unsat_full`
    is false at every `n`: the theorem is sound, and vacuous here. -/
theorem cpo_never_refuted (n : Nat) :
    ∃ q ∈ gfpIter pruneSig (sigStatic Cpo) n, Cpo ∈ q.1 :=
  ⟨Qpo,
   gfp_greatest pruneSig pruneSig_mono (sigStatic Cpo) [Qpo]
     (by intro q hq; cases List.mem_singleton.mp hq; exact qpo_mem_sigStatic)
     qpo_self_closed n Qpo (List.Mem.head _),
   by decide⟩

/-! ### (3) The missing clause -/

/-- `compatB` plus the `∀PO` propagation it drops.  `conv PO = PO`, so a `PO`
    edge carries `∀PO` bodies in BOTH directions. -/
def compatB' (r : Atom) (D : Concept) (q q' : Sig) : Bool :=
  compatB r D q q' &&
  (match r with
   | Atom.po => subB (allBodies po q.1) q'.1 && subB (allBodies po q'.1) q.1
   | Atom.pp => true
   | Atom.ppi => true
   | Atom.dr => true
   | Atom.eq => true)

def pruneSig' (X : List Sig) : List Sig :=
  X.filter (fun q => (sigDemands q).all
    (fun rd => X.any (fun q' => compatB' rd.1 rd.2 q q')))

theorem pruneSig'_red (X : List Sig) : ∀ q ∈ pruneSig' X, q ∈ X :=
  fun _ h => (List.mem_filter.mp h).1

theorem pruneSig'_mono (X Y : List Sig) (hXY : ∀ q, q ∈ X → q ∈ Y) :
    ∀ q, q ∈ pruneSig' X → q ∈ pruneSig' Y := by
  intro q hq
  obtain ⟨hqX, hall⟩ := List.mem_filter.mp hq
  refine List.mem_filter.mpr ⟨hXY q hqX, ?_⟩
  rw [List.all_eq_true] at hall ⊢
  intro rd hrd
  have h1 := hall rd hrd
  rw [List.any_eq_true] at h1 ⊢
  obtain ⟨q', hq'X, hcomp⟩ := h1
  exact ⟨q', hXY q' hq'X, hcomp⟩

/-! ### (4) The addition keeps BOTH directions -/

theorem compatB'_imp {r : Atom} {D : Concept} {q q' : Sig}
    (h : compatB' r D q q' = true) : compatB r D q q' = true := by
  rw [compatB'.eq_def, Bool.and_eq_true] at h
  exact h.1

theorem pruneSig'_sub_pruneSig (X : List Sig) :
    ∀ q ∈ pruneSig' X, q ∈ pruneSig X := by
  intro q hq
  obtain ⟨hqX, hall⟩ := List.mem_filter.mp hq
  refine List.mem_filter.mpr ⟨hqX, ?_⟩
  rw [List.all_eq_true] at hall ⊢
  intro rd hrd
  have h1 := hall rd hrd
  rw [List.any_eq_true] at h1 ⊢
  obtain ⟨q', hq'X, hc⟩ := h1
  exact ⟨q', hq'X, compatB'_imp hc⟩

/-- **THE STRENGTHENING COSTS NOTHING.**  A `pruneSig'`-fixed point is a
    `pruneSig`-fixed point, so `coneScheme_sound` — the whole soundness half,
    and with it the fragment decision procedure — applies verbatim. -/
theorem coneScheme_sound' {X : List Sig} {q0 : Sig} {C0 : Concept}
    (hXS : ∀ q ∈ X, q ∈ sigStatic C0) (hfix : ∀ q ∈ X, q ∈ pruneSig' X)
    (hpo : POFree C0) (hq0 : q0 ∈ X) (hC0 : C0 ∈ q0.1) : Satisfiable C0 :=
  coneScheme_sound hXS (fun q hq => pruneSig'_sub_pruneSig X q (hfix q hq))
    hpo hq0 hC0


open Classical in
/-- `dkey_compat` still holds for the strengthened relation: the extra `PO`
    conjunct is `mty_all` read along the edge and along its converse. -/
theorem dkey_compat' (hI : RCC5Interp I) (C0 : Concept) {x y : α}
    (hx : I.dom x) (hy : I.dom y) {r : Atom} {D : Concept}
    (hr : I.rho x y = r) (hD : D ∈ mty C0 I y) :
    compatB' r D (dkey C0 I x) (dkey C0 I y) = true := by
  rw [compatB'.eq_def, Bool.and_eq_true]
  refine ⟨dkey_compat hI C0 hx hy hr hD, ?_⟩
  cases r with
  | pp => rfl
  | ppi => rfl
  | dr => rfl
  | eq => rfl
  | po =>
      have hyx : I.rho y x = po := by
        have h2 := hI.conv_ x y hx hy
        rw [hr] at h2; rw [h2]; rfl
      rw [Bool.and_eq_true]
      exact ⟨subB_iff.mpr (fun E hE => mty_all (mem_allBodies hE) hy hr),
             subB_iff.mpr (fun E hE => mty_all (mem_allBodies hE) hx hyx)⟩

open Classical in
theorem modelSigs_survives' (hI : RCC5Interp I) (C0 : Concept) :
    ∀ q ∈ modelSigs C0 I, q ∈ pruneSig' (modelSigs C0 I) := by
  intro q hq
  obtain ⟨hqS, hex⟩ := List.mem_filter.mp hq
  obtain ⟨x, hx, rfl⟩ := of_decide_eq_true hex
  refine List.mem_filter.mpr ⟨hq, ?_⟩
  refine List.all_eq_true.mpr (fun rd hrd => ?_)
  obtain ⟨r, D⟩ := rd
  have hdem : Concept.ex r D ∈ mty C0 I x := mem_sigDemands hrd
  obtain ⟨y, hy, hxy, hD⟩ := mty_ex hdem
  refine List.any_eq_true.mpr ⟨dkey C0 I y, mem_modelSigs hI C0 hy, ?_⟩
  exact dkey_compat' hI C0 hx hy hxy hD

open Classical in
/-- Completeness, verbatim, for the strengthened elimination. -/
theorem coneScheme_complete' (hI : RCC5Interp I) (C0 : Concept) {x : α}
    (hx : I.dom x) (hC0 : sat I x C0) (n : Nat) :
    ∃ q ∈ gfpIter pruneSig' (sigStatic C0) n, C0 ∈ q.1 :=
  ⟨dkey C0 I x,
   gfp_greatest pruneSig' pruneSig'_mono (sigStatic C0) (modelSigs C0 I)
     (modelSigs_sub C0 I) (modelSigs_survives' hI C0) n _
     (mem_modelSigs hI C0 hx),
   mem_mty.mpr ⟨cl_self C0, hC0⟩⟩

/-- And so the full-logic UNSAT test, verbatim, for the strengthened one. -/
theorem coneScheme_unsat_full' (C0 : Concept) (n : Nat)
    (h : ∀ q ∈ gfpIter pruneSig' (sigStatic C0) n, C0 ∉ q.1) :
    ¬ Satisfiable C0 := by
  rintro ⟨α, I, hI, x, hx, hsat⟩
  obtain ⟨q, hq, hC0⟩ := coneScheme_complete' hI C0 hx hsat n
  exact h q hq hC0

/-! ### (5) With it, `Cpo` is refuted after one round -/

/-- **THE GAP, CLOSED.**  No survivor of ONE strengthened round carries `Cpo`.
    The argument enumerates nothing: any carrier's `∃PO.⊤` demand would need a
    target whose type contains `⊥`, and no support type does. -/
theorem cpo_refuted_at_one :
    ∀ q ∈ gfpIter pruneSig' (sigStatic Cpo) 1, Cpo ∉ q.1 := by
  intro q hq hC0
  have hq' : q ∈ pruneSig' (sigStatic Cpo) := hq
  obtain ⟨hqS, hall⟩ := List.mem_filter.mp hq'
  -- `Cpo` is a conjunction, so a support type carrying it carries both conjuncts
  have hsup : supportB q.1 = true :=
    (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp
      (sigStatic_ok Cpo q hqS)).1).1
  obtain ⟨-, -, hand, -, -, -⟩ := supportB_sound hsup
  obtain ⟨hex, hallpo⟩ := hand _ _ hC0
  -- so `(PO, ⊤)` is one of its demands
  have hdem : (po, Concept.top) ∈ sigDemands q :=
    mem_sigDemands_mk (by decide) hex
  -- which the strengthened test can only serve from a type containing `⊥`
  rw [List.all_eq_true] at hall
  have h1 := hall _ hdem
  rw [List.any_eq_true] at h1
  obtain ⟨q', hq'S, hcomp⟩ := h1
  rw [compatB'.eq_def, Bool.and_eq_true] at hcomp
  have hpo : (subB (allBodies po q.1) q'.1 && subB (allBodies po q'.1) q.1) = true :=
    hcomp.2
  have hbot : Concept.bot ∈ q'.1 :=
    subB_iff.mp (Bool.and_eq_true _ _ |>.mp hpo).1 _ (mem_allBodies_of hallpo)
  -- but no support type contains `⊥`
  have hsup' : supportB q'.1 = true :=
    (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp
      (sigStatic_ok Cpo q' hq'S)).1).1
  exact (supportB_sound hsup').1 hbot

/-! ### (6) The strengthening crosses the erasure barrier

Measured (3000/3000 forall-PO-containing concepts, reviewer's probe): the
SHIPPED test's verdict is invariant under replacing every `∀PO.D` by `⊤`.  The
erasure is always `POFree`, so on that evidence the shipped full-logic test
refutes nothing the FRAGMENT procedure does not already refute on a syntactic
weakening.  `compatB'` provably crosses that line: it refutes `Cpo` while
`Cpo`'s erasure is satisfiable. -/

/-- A two-point, all-`PO` interpretation. -/
def poI : Interp Bool :=
  ⟨fun _ => True, fun x y => if x = y then Atom.eq else Atom.po, fun _ _ => False⟩

theorem poI_rcc5 : RCC5Interp poI where
  refl_eq := fun x _ => by cases x <;> rfl
  eq_id := fun x y _ _ h => by
    cases x <;> cases y <;> first | rfl | exact absurd h (by decide)
  conv_ := fun x y _ _ => by cases x <;> cases y <;> rfl
  comp_ := fun x y z _ _ _ => by cases x <;> cases y <;> cases z <;> decide

/-- `erase Cpo = ∃PO.⊤ ⊓ ⊤` is satisfiable — so no test that ignores `∀PO`
    bodies can refute `Cpo`, and `compatB'` does. -/
theorem erase_cpo_satisfiable :
    Satisfiable (Concept.and (Concept.ex po Concept.top) Concept.top) :=
  ⟨Bool, poI, poI_rcc5, true, trivial,
   ⟨⟨false, trivial, rfl, trivial⟩, trivial⟩⟩

end ColdReview2

end POFreeLift

#print axioms POFreeLift.cpo_unsat
#print axioms POFreeLift.cpo_never_refuted
#print axioms POFreeLift.dkey_compat'
#print axioms POFreeLift.coneScheme_complete'
#print axioms POFreeLift.coneScheme_unsat_full'
#print axioms POFreeLift.cpo_refuted_at_one
#print axioms POFreeLift.erase_cpo_satisfiable
#print axioms POFreeLift.coneScheme_sound'
