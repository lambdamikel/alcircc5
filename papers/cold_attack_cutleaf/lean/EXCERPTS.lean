-- Excerpts from formal/POFreeLift.lean (31,783 lines, 0 sorries,
-- 0 warnings, 0 sorryAx).  Statements only in the sense that the proofs
-- are included but the surrounding 30k lines are not; these do not
-- compile standalone.

structure MultiTier (β κ : Type) where
  E : β → β → Atom
  K : κ → β → Atom
  Q : κ → κ → Atom
  up : κ → Bool
  tauE : β → List Concept
  p : κ → Nat
  phase : κ → Nat → List Concept

/-- The type labelling of the multi-kernel unfolding. -/

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

open Classical in
/-- The persistent `∃PP` demands at `x`: those whose guard also holds. -/
noncomputable def persistDs (C0 : Concept) (I : Interp α) (x : α) : List Concept :=
  (cl C0).filter (fun D => decide (Concept.ex pp D ∈ mty C0 I x ∧
    sat I x (Concept.all pp (Concept.ex pp D))))

open Classical in

/-- The depth-`k` model type: model-true formulas of modal depth `≤ k`. -/
noncomputable def mtk (C0 : Concept) (I : Interp α) (x : α) (k : Nat) :
    List Concept :=
  (mty C0 I x).filter (fun F => decide (mdepth F ≤ k))

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

/-- A kernel's data and its certificate properties. -/
structure KernelData {α : Type} (I : Interp α) (C0 : Concept)
    (Ds : List Concept) (L0 : Nat) (d : Bool) (x : α) where
  c : Nat → α
  i : Nat
  p : Nat
  cdom : ∀ n, I.dom (c n)
  cstep : ∀ n, I.rho (c n) (c (n + 1)) = cdir d
  base_ge : L0 ≤ i
  ipos : 0 < i
  croot : c 0 = x
  ppos : 0 < p
  cty : mty C0 I (c i) = mty C0 I (c (i + p))
  ccovers : ∀ D ∈ Ds, ∃ b, b < p ∧ D ∈ mty C0 I (c (i + b))

open Classical in
/-- **A NODE WITH PERSISTENT DEMANDS YIELDS ITS KERNEL'S DATA.** -/

/-- An ordered-disjoint structure: a strict partial order plus a symmetric,
    irreflexive, DOWNWARD-CLOSED disjointness disjoint from comparability.
    Mirrors `RCC5NormalForm.OrderedDisjoint`. -/
structure ODStruct (N : Type) where
  lt : N → N → Prop
  disj : N → N → Prop
  ltIrr : ∀ x, ¬ lt x x
  ltTr : ∀ x y z, lt x y → lt y z → lt x z
  djSym : ∀ x y, disj x y → disj y x
  djIrr : ∀ x, ¬ disj x x
  ltNotDj : ∀ x y, lt x y → ¬ disj x y
  djDown : ∀ x y x' y', disj x y → (x' = x ∨ lt x' x) → (y' = y ∨ lt y' y) →
    disj x' y'

variable {N : Type}

    Sixteen genuine cases (`wp93` part C): four are FORCED — `PP;PP` and
    `PPI;PPI` by `ltTr`, `PP;DR` and `DR;PPI` by `djDown` — three are absorbed,
    and the rest need one exclusion each, supplied by the inversion lemmas. -/
theorem odNet_frame (O : ODStruct N) : Frame (odNet O) where
  refl_eq := odNet_self O
  eq_id := fun x y h => odNet_eq_inv O h
  conv_ := by
    intro x y
    by_cases hxy : x = y
    · subst hxy; rw [odNet_self]; rfl
    · by_cases h2 : O.lt x y
      · rw [odNet_lt O h2, odNet_gt O h2]; rfl
      · by_cases h3 : O.lt y x
        · rw [odNet_gt O h3, odNet_lt O h3]; rfl
        · by_cases h4 : O.disj x y
          · rw [odNet_dj O h4, odNet_dj O (O.djSym x y h4)]; rfl
          · rw [odNet_po O hxy h2 h3 h4,
              odNet_po O (fun h => hxy h.symm) h3 h2 (fun h => h4 (O.djSym y x h))]
            rfl
  comp_ := by
    intro x y z
    by_cases hxy : x = y
    · subst hxy; rw [odNet_self]; simp [comp]
    by_cases hyz : y = z
    · subst hyz; rw [odNet_self O y]; cases h : odNet O x y <;> simp [comp]
    by_cases h1 : O.lt x y
    · by_cases h2 : O.lt y z
      · -- PP;PP forced by transitivity
        rw [odNet_lt O h1, odNet_lt O h2, odNet_lt O (O.ltTr x y z h1 h2)]; decide
      · by_cases h3 : O.lt z y
        · -- PP;PPI absorbed
          rw [odNet_lt O h1, odNet_gt O h3]
          rcases odNet_cases O x z with h|h|h|h|h <;> rw [h] <;> decide
        · by_cases h4 : O.disj y z
          · -- PP;DR forced by downward closure
            rw [odNet_lt O h1, odNet_dj O h4,
              odNet_dj O (O.djDown y z x z h4 (Or.inr h1) (Or.inl rfl))]; decide
          · -- PP;PO : exclude EQ and PPI
            rw [odNet_lt O h1, odNet_po O hyz h2 h3 h4]
            rcases odNet_cases O x z with h|h|h|h|h
            · exfalso; have e : x = z := odNet_eq_inv O h; subst e; exact h3 h1
            · rw [h]; decide
            · exact absurd (O.ltTr z x y (odNet_ppi_inv O h) h1) h3
            · rw [h]; decide
            · rw [h]; decide
    · by_cases h1' : O.lt y x
      · by_cases h2 : O.lt y z
        · -- PPI;PP : exclude DR (both sides above y)
          rw [odNet_gt O h1', odNet_lt O h2]
          rcases odNet_cases O x z with h|h|h|h|h
          · rw [h]; decide
          · rw [h]; decide
          · rw [h]; decide
          · exact absurd (O.djDown x z y y (odNet_dr_inv O h) (Or.inr h1') (Or.inr h2))
              (O.djIrr y)
          · rw [h]; decide
        · by_cases h3 : O.lt z y
          · -- PPI;PPI forced by transitivity
            rw [odNet_gt O h1', odNet_gt O h3, odNet_gt O (O.ltTr z y x h3 h1')]; decide
          · by_cases h4 : O.disj y z
            · -- PPI;DR : exclude EQ and PP
              rw [odNet_gt O h1', odNet_dj O h4]
              rcases odNet_cases O x z with h|h|h|h|h
              · exfalso; have e : x = z := odNet_eq_inv O h; subst e
                exact O.ltNotDj y x h1' h4
              · exact absurd (O.ltTr y x z h1' (odNet_pp_inv O h))
                  (fun hc => O.ltNotDj y z hc h4)
              · rw [h]; decide
              · rw [h]; decide
              · rw [h]; decide
            · -- PPI;PO : exclude EQ, PP, DR
              rw [odNet_gt O h1', odNet_po O hyz h2 h3 h4]
              rcases odNet_cases O x z with h|h|h|h|h
              · exfalso; have e : x = z := odNet_eq_inv O h; subst e; exact h2 h1'
              · exact absurd (O.ltTr y x z h1' (odNet_pp_inv O h)) h2
              · rw [h]; decide
              · exact absurd (O.djDown x z y z (odNet_dr_inv O h)
                  (Or.inr h1') (Or.inl rfl)) h4
              · rw [h]; decide
      · by_cases hd1 : O.disj x y
        · by_cases h2 : O.lt y z
          · -- DR;PP : exclude EQ and PPI
            rw [odNet_dj O hd1, odNet_lt O h2]
            rcases odNet_cases O x z with h|h|h|h|h
            · exfalso; have e : x = z := odNet_eq_inv O h; subst e
              exact O.ltNotDj y x h2 (O.djSym x y hd1)
            · rw [h]; decide
            · exact absurd (O.ltTr y z x h2 (odNet_ppi_inv O h))
                (fun hc => O.ltNotDj y x hc (O.djSym x y hd1))
            · rw [h]; decide
            · rw [h]; decide
          · by_cases h3 : O.lt z y
            · -- DR;PPI forced by downward closure
              rw [odNet_dj O hd1, odNet_gt O h3,
                odNet_dj O (O.djDown x y x z hd1 (Or.inl rfl) (Or.inr h3))]; decide
            · by_cases h4 : O.disj y z
              · -- DR;DR absorbed
                rw [odNet_dj O hd1, odNet_dj O h4]
                rcases odNet_cases O x z with h|h|h|h|h <;> rw [h] <;> decide
              · -- DR;PO : exclude EQ and PPI
                rw [odNet_dj O hd1, odNet_po O hyz h2 h3 h4]
                rcases odNet_cases O x z with h|h|h|h|h
                · exfalso; have e : x = z := odNet_eq_inv O h; subst e
                  exact h4 (O.djSym x y hd1)
                · rw [h]; decide
                · exact absurd (O.djSym z y (O.djDown x y z y hd1
                    (Or.inr (odNet_ppi_inv O h)) (Or.inl rfl))) h4
                · rw [h]; decide
                · rw [h]; decide
        · by_cases h2 : O.lt y z
          · -- PO;PP : exclude EQ, PPI, DR
            rw [odNet_po O hxy h1 h1' hd1, odNet_lt O h2]
            rcases odNet_cases O x z with h|h|h|h|h
            · exfalso; have e : x = z := odNet_eq_inv O h; subst e; exact h1' h2
            · rw [h]; decide
            · exact absurd (O.ltTr y z x h2 (odNet_ppi_inv O h)) h1'
            · exact absurd (O.djDown x z x y (odNet_dr_inv O h)
                (Or.inl rfl) (Or.inr h2)) hd1
            · rw [h]; decide
          · by_cases h3 : O.lt z y
            · -- PO;PPI : exclude EQ and PP
              rw [odNet_po O hxy h1 h1' hd1, odNet_gt O h3]
              rcases odNet_cases O x z with h|h|h|h|h
              · exfalso; have e : x = z := odNet_eq_inv O h; subst e; exact h1 h3
              · exact absurd (O.ltTr x z y (odNet_pp_inv O h) h3) h1
              · rw [h]; decide
              · rw [h]; decide
              · rw [h]; decide
            · by_cases h4 : O.disj y z
              · -- PO;DR : exclude EQ and PP
                rw [odNet_po O hxy h1 h1' hd1, odNet_dj O h4]
                rcases odNet_cases O x z with h|h|h|h|h
                · exfalso; have e : x = z := odNet_eq_inv O h; subst e
                  exact hd1 (O.djSym y x h4)
                · exact absurd (O.djSym y x (O.djDown y z y x h4 (Or.inl rfl)
                    (Or.inr (odNet_pp_inv O h)))) hd1
                · rw [h]; decide
                · rw [h]; decide
                · rw [h]; decide
              · -- PO;PO absorbed
                rw [odNet_po O hxy h1 h1' hd1, odNet_po O hyz h2 h3 h4]
                rcases odNet_cases O x z with h|h|h|h|h <;> rw [h] <;> decide


open Classical in
/-- **THE `qnet` OF AN ORDERED-DISJOINT STRUCTURE IS THAT STRUCTURE** (§41.4
    step 2) — the interface check that lets `odNet_frame` supply `frame_q`
    directly.  Taking ONE ordered-disjoint structure on the whole of `β ⊕ κ`
    (externals AND kernel bases as ordinary nodes) and reading `E`/`K`/`Q` off
    it, the assembled `qnet` is literally `odNet` again: the `inl/inr` case uses
    `conv`, which matches by `odNet`'s converse law, and the diagonal `inr/inr`
    case matches by `odNet_self`. -/

/-- **THE CUT ON A CHAIN.**  A demand at `u` served by `v` is equally served by
    any LATER chain member of the same type — so the segment between them can be
    dropped.  Both of `path_cut`'s obligations come out of `serveChain_rho`. -/
theorem chain_cut (hI : RCC5Interp I) {C0 : Concept} {u v : α} {t : List α}
    (hu : I.dom u) (hv : I.dom v) (huv : I.rho u v = pp)
    (hch : ServeChain I v t) {w : α} (hw : w ∈ t)
    (hty : mty C0 I v = mty C0 I w) {D : Concept} (hD : D ∈ mty C0 I v) :
    I.rho u w = pp ∧ D ∈ mty C0 I w := by
  have hvw : I.rho v w = pp := serveChain_rho hI t v hv hch w hw
  have hwd : I.dom w := serveChain_dom t v hv hch w hw
  exact path_cut hI hu hv hwd huv hvw hty hD

/-- The head type of a chain — the invariant the cut preserves, and the only
    thing the caller needs (a demand served by the old head is served by the new
    one precisely because the TYPE is the same). -/

/-- **THE SHORT CHAIN.**  Iterating the cut: every chain has a companion of
    length ≤ `|typeEnum C₀|` with the SAME HEAD TYPE — so a demand served by the
    original head is served by the new one.  This is §44's adequacy. -/
theorem short_chain (hI : RCC5Interp I) {C0 : Concept} :
    ∀ (n : Nat) (u : α) (ns : List α), ns.length ≤ n → I.dom u →
      ServeChain I u ns →
      ∃ ms, ServeChain I u ms ∧ ms.length ≤ (typeEnum C0).length ∧
        htype C0 I ms = htype C0 I ns := by
  intro n
  induction n with
  | zero =>
    intro u ns hlen hu hch
    cases ns with
    | nil => exact ⟨[], hch, Nat.zero_le _, rfl⟩
    | cons a t => exact absurd hlen (by simp)
  | succ m ih =>
    intro u ns hlen hu hch
    by_cases hshort : ns.length ≤ (typeEnum C0).length
    · exact ⟨ns, hch, hshort, rfl⟩
    · obtain ⟨pre, v, t, heq, w, hw, hty⟩ :=
        chain_long_has_dup C0 I ns (by omega)
      subst heq
      obtain ⟨ms, hms, hlt, hht⟩ := serveChain_cut hI pre u v w t hu hch hw hty
      obtain ⟨ms', hms', hshort', hht'⟩ := ih u ms (by omega) hu hms
      exact ⟨ms', hms', hshort', hht'.trans hht⟩

/-! #### The dichotomy: a short chain, or a kernel (§44.18)

`short_chain` gives EXISTENCE of a bounded chain; `mixNodes` is a CONSTRUCTION
using arbitrary (`Classical.choose`) witnesses.  Those are not the same thing,
and the seam between them is where the fuel can run out.

The seam is closed by a dichotomy, not by making the construction clever:

* if some node reachable by `∃PP` steps has NO `∃PP` demand, the chain
  TERMINATES, and `short_chain` bounds it;
* otherwise every reachable node has one, and iterating produces an INFINITE
  ascending chain — which is a KERNEL, and the campaign already handles those
  (`recurrent_tail`, `rr_segment_from`, `rr_covers`).

`ascend` is the second branch's generator. -/

/-- Iterating a step that stays inside a class: the generator for the kernel
    branch. -/

/-- **THE DICHOTOMY.**  For any class `P` closed under the `∃PP`-witness step,
    either some member has no `∃PP` demand at all, or `P` carries an infinite
    ascending chain from every member. -/
theorem pp_dichotomy (C0 : Concept) (P : α → Prop)
    (hcl : ∀ x, P x → ∀ D, Concept.ex pp D ∈ mty C0 I x →
      ∃ y, P y ∧ I.dom y ∧ I.rho x y = pp ∧ D ∈ mty C0 I y)
    (u : α) (hu : I.dom u) (hPu : P u) :
    (∃ x, P x ∧ ∀ D, Concept.ex pp D ∉ mty C0 I x) ∨
    (∃ c : Nat → α, c 0 = u ∧ (∀ n, I.dom (c n)) ∧
      ∀ n, I.rho (c n) (c (n + 1)) = pp) := by
  by_cases hall : ∀ x, P x → ∃ D, Concept.ex pp D ∈ mty C0 I x
  · refine Or.inr ?_
    have hstep : ∀ x, P x → ∃ y, P y ∧ I.dom y ∧ I.rho x y = pp := by
      intro x hx
      obtain ⟨D, hD⟩ := hall x hx
      obtain ⟨y, hy, hyd, hr, _⟩ := hcl x hx D hD
      exact ⟨y, hy, hyd, hr⟩
    exact ⟨fun n => (ascend P hstep u hPu n).val, rfl,
      fun n => ascend_dom P hstep u hu hPu n, fun n => ascend_step P hstep u hPu n⟩
  · refine Or.inl ?_
    rcases Classical.em (∃ x, P x ∧ ∀ D, Concept.ex pp D ∉ mty C0 I x) with h | h
    · exact h
    · exfalso
      refine hall (fun x hx => ?_)
      rcases Classical.em (∃ D, Concept.ex pp D ∈ mty C0 I x) with h2 | h2
      · exact h2
      · exact absurd ⟨x, hx, fun D hD => h2 ⟨D, hD⟩⟩ h

/-! #### The external order as a demand-step closure (§44.8)

§44.8 established that `elt` must NOT be all of the model's `PP` on the chosen
externals — that declares an edge between every model-`PP`-related pair, and two
externals reached by different routes can have budgets far apart, breaking
`ee_all`'s `bud e ≤ bud f + 1`.  It must be the transitive closure of the
extraction's OWN `PP`-demand steps, along which the budget is constant.

`tcl` is that closure, with the two facts `odSeed` needs (transitive,
irreflexive) and the one `mixLt_rho`/`hsep_of_model` need (contained in the
model's `PP`). -/

/-- Transitive closure of a step relation. -/
inductive tcl {β : Type} (step : β → β → Prop) : β → β → Prop
  | base {a b} : step a b → tcl step a b
  | tail {a b c} : tcl step a b → step b c → tcl step a c

/-- **THE VACUITY, AS A THEOREM.**  `kserU_sound`'s conclusion, derived from the
    demand's membership alone.  Kept in the file so the claim cannot drift back
    into the record as a soundness result. -/
theorem kserU_sound_is_vacuous (m : MTKNode I C0) (c : Concept)
    (hF : Concept.ex pp c ∈ mtk C0 I m.x m.k) :
    sat I m.x (Concept.ex pp c) :=
  (mem_mty.mp (mem_mtk.mp hF).1).2

/-- The same on the descending side. -/

/-- **A WITNESS SELECTOR.**  Everything the closure needs to know about how a
    vertical demand's witness is chosen: a real model witness at the same
    budget, carrying the demand's argument. -/
structure WitSel (I : Interp α) (C0 : Concept) where
  up : (n : MTKNode I C0) → {c : Concept} →
    Concept.ex pp c ∈ mtk C0 I n.x n.k → MTKNode I C0
  up_rho : ∀ (n : MTKNode I C0) {c : Concept}
    (hF : Concept.ex pp c ∈ mtk C0 I n.x n.k), I.rho n.x (up n hF).x = pp
  up_bud : ∀ (n : MTKNode I C0) {c : Concept}
    (hF : Concept.ex pp c ∈ mtk C0 I n.x n.k), (up n hF).k = n.k
  up_arg : ∀ (n : MTKNode I C0) {c : Concept}
    (hF : Concept.ex pp c ∈ mtk C0 I n.x n.k),
    c ∈ mtk C0 I (up n hF).x (up n hF).k
  dn : (n : MTKNode I C0) → {c : Concept} →
    Concept.ex ppi c ∈ mtk C0 I n.x n.k → MTKNode I C0
  dn_rho : ∀ (n : MTKNode I C0) {c : Concept}
    (hF : Concept.ex ppi c ∈ mtk C0 I n.x n.k), I.rho n.x (dn n hF).x = ppi
  dn_bud : ∀ (n : MTKNode I C0) {c : Concept}
    (hF : Concept.ex ppi c ∈ mtk C0 I n.x n.k), (dn n hF).k = n.k
  dn_arg : ∀ (n : MTKNode I C0) {c : Concept}
    (hF : Concept.ex ppi c ∈ mtk C0 I n.x n.k),
    c ∈ mtk C0 I (dn n hF).x (dn n hF).k

/-- The current behaviour, as ONE instance — so every §§85–108 result is the
    `defaultSel` case of what follows. -/

/-- The current behaviour, as ONE instance — so every §§85–108 result is the
    `defaultSel` case of what follows. -/
noncomputable def defaultSel (I : Interp α) (C0 : Concept) : WitSel I C0 where
  up := fun n {_c} hF => ppWitness n hF
  up_rho := fun n {_c} hF => ppWitness_rho n hF
  up_bud := fun n {_c} hF => ppWitness_bud n hF
  up_arg := fun n {_c} hF => ppWitness_arg n hF
  dn := fun n {_c} hF => ppiWitness n hF
  dn_rho := fun n {_c} hF => ppiWitness_rho n hF
  dn_bud := fun n {_c} hF => ppiWitness_bud n hF
  dn_arg := fun n {_c} hF => ppiWitness_arg n hF

variable (W : WitSel I C0)

/-- **THE CUTTING CLOSURE.**  Carries the types already seen on this path and
    stops when a step would repeat one.  Works for ANY selector. -/
noncomputable def cutNodes (W : WitSel I C0) (seen : List (List Concept))
    (n : MTKNode I C0) : Nat → List (MTKNode I C0)
  | 0 => [n]
  | fuel + 1 => n :: (mtk C0 I n.x n.k).attach.flatMap (fun p => match p with
      | ⟨.ex pp _, hF⟩ =>
          if mty C0 I (W.up n hF).x ∈ seen then [W.up n hF]
          else cutNodes W (mty C0 I (W.up n hF).x :: seen) (W.up n hF) fuel
      | ⟨.ex ppi _, hF⟩ =>
          if mty C0 I (W.dn n hF).x ∈ seen then [W.dn n hF]
          else cutNodes W (mty C0 I (W.dn n hF).x :: seen) (W.dn n hF) fuel
      | _ => [])

/-- **A FULL `seen` ADMITS NO NEW TYPE.**  If `seen` is repeat-free, drawn from
    the type enumeration, and already as long as it, then every model type is
    already in it — by `nodup_len_le` applied to the extended list, with no
    pigeonhole of its own. -/
theorem seen_full (seen : List (List Concept)) (hnd : seen.Nodup)
    (hsub : ∀ t ∈ seen, t ∈ typeEnum C0)
    (hlen : (typeEnum C0).length ≤ seen.length) (y : α) :
    mty C0 I y ∈ seen := by
  by_cases h : mty C0 I y ∈ seen
  · exact h
  · exfalso
    have hnd' : (mty C0 I y :: seen).Nodup := List.nodup_cons.mpr ⟨h, hnd⟩
    have hsub' : ∀ t ∈ (mty C0 I y :: seen), t ∈ typeEnum C0 := by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact mty_mem_typeEnum C0 I y
      · exact hsub t ht'
    have := nodup_len_le _ _ hsub' hnd'
    rw [List.length_cons] at this
    omega

/-- **THE FIXPOINT, UNCONDITIONALLY.**  Once the fuel plus what is already seen
    covers the type enumeration, more fuel changes nothing — for EVERY selector,
    with no hypothesis on it and no kernel-service test.

    This is what §110's `BoundedSel.bound` was assuming. It is a theorem. -/

    This is what §110's `BoundedSel.bound` was assuming. It is a theorem. -/
theorem cutNodes_stable (W : WitSel I C0) :
    ∀ (fuel : Nat) (seen : List (List Concept)), seen.Nodup →
      (∀ t ∈ seen, t ∈ typeEnum C0) →
      (typeEnum C0).length ≤ seen.length + fuel →
      ∀ n : MTKNode I C0,
        cutNodes W seen n (fuel + 2) = cutNodes W seen n (fuel + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro seen hnd hsub hlen n
    rw [cutNodes, cutNodes]
    congr 1
    refine flatMap_congr _ _ _ (fun p _ => ?_)
    rcases p with ⟨F, hF⟩
    cases F with
    | ex r c =>
      cases r with
      | pp =>
        show (if mty C0 I (W.up n hF).x ∈ seen then [W.up n hF]
              else cutNodes W (mty C0 I (W.up n hF).x :: seen) (W.up n hF) 1)
            = (if mty C0 I (W.up n hF).x ∈ seen then [W.up n hF]
              else cutNodes W (mty C0 I (W.up n hF).x :: seen) (W.up n hF) 0)
        rw [if_pos (seen_full seen hnd hsub (by omega) _),
            if_pos (seen_full seen hnd hsub (by omega) _)]
      | ppi =>
        show (if mty C0 I (W.dn n hF).x ∈ seen then [W.dn n hF]
              else cutNodes W (mty C0 I (W.dn n hF).x :: seen) (W.dn n hF) 1)
            = (if mty C0 I (W.dn n hF).x ∈ seen then [W.dn n hF]
              else cutNodes W (mty C0 I (W.dn n hF).x :: seen) (W.dn n hF) 0)
        rw [if_pos (seen_full seen hnd hsub (by omega) _),
            if_pos (seen_full seen hnd hsub (by omega) _)]
      | _ => rfl
    | _ => rfl
  | succ f ih =>
    intro seen hnd hsub hlen n
    rw [cutNodes, cutNodes]
    congr 1
    refine flatMap_congr _ _ _ (fun p _ => ?_)
    rcases p with ⟨F, hF⟩
    cases F with
    | ex r c =>
      cases r with
      | pp =>
        show (if mty C0 I (W.up n hF).x ∈ seen then [W.up n hF]
              else cutNodes W (mty C0 I (W.up n hF).x :: seen) (W.up n hF) (f + 2))
            = (if mty C0 I (W.up n hF).x ∈ seen then [W.up n hF]
              else cutNodes W (mty C0 I (W.up n hF).x :: seen) (W.up n hF) (f + 1))
        by_cases hc : mty C0 I (W.up n hF).x ∈ seen
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc]
          exact ih _ (List.nodup_cons.mpr ⟨hc, hnd⟩)
            (fun t ht => by
              rcases List.mem_cons.mp ht with rfl | ht'
              · exact mty_mem_typeEnum C0 I _
              · exact hsub t ht')
            (by rw [List.length_cons]; omega) _
      | ppi =>
        show (if mty C0 I (W.dn n hF).x ∈ seen then [W.dn n hF]
              else cutNodes W (mty C0 I (W.dn n hF).x :: seen) (W.dn n hF) (f + 2))
            = (if mty C0 I (W.dn n hF).x ∈ seen then [W.dn n hF]
              else cutNodes W (mty C0 I (W.dn n hF).x :: seen) (W.dn n hF) (f + 1))
        by_cases hc : mty C0 I (W.dn n hF).x ∈ seen
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc]
          exact ih _ (List.nodup_cons.mpr ⟨hc, hnd⟩)
            (fun t ht => by
              rcases List.mem_cons.mp ht with rfl | ht'
              · exact mty_mem_typeEnum C0 I _
              · exact hsub t ht')
            (by rw [List.length_cons]; omega) _
      | _ => rfl
    | _ => rfl

/-- **THE HEADLINE.**  From an empty `seen`, the closure is stable at fuel
    `|typeEnum C0|` — computable from `C₀` alone, for every selector, with NO
    hypothesis. -/

/-- **THE HEADLINE.**  From an empty `seen`, the closure is stable at fuel
    `|typeEnum C0|` — computable from `C₀` alone, for every selector, with NO
    hypothesis. -/
theorem cutNodes_stable_typeEnum (W : WitSel I C0) (n : MTKNode I C0) :
    cutNodes W [] n ((typeEnum C0).length + 2)
      = cutNodes W [] n ((typeEnum C0).length + 1) :=
  cutNodes_stable W (typeEnum C0).length [] List.nodup_nil
    (fun _ ht => absurd ht List.not_mem_nil) (by simp) n

/-! #### §114 — WIRING THE UNCONSUMED THEOREMS

§113 found three certified theorems with zero consumers. Two can be connected
now.

`cutNodes_up_mem` / `cutNodes_dn_mem` — every demand's witness is IN the closure,
whether the step recursed or was cut, because §113's fix makes a cut keep the
witness. No hypothesis, any selector.

`kernelData_of_chain` — `pp_dichotomy`'s infinite branch feeds `kernel_of_chain`
and out comes a `KernelData`. This is the construction §108.2 said was
impossible; §108.2 was cycling a FINITE segment, which does fail, while
`pp_dichotomy` hands over a genuinely infinite chain of real elements. -/

/-- **THE `∃PP` WITNESS IS ALWAYS PRESENT.**  Recursed into, or kept by the
    cut — either way it is in the list. -/

/-- **THE `∃PP` WITNESS IS ALWAYS PRESENT.**  Recursed into, or kept by the
    cut — either way it is in the list. -/
theorem cutNodes_up_mem (W : WitSel I C0) (seen : List (List Concept))
    (n : MTKNode I C0) {c : Concept}
    (hF : Concept.ex pp c ∈ mtk C0 I n.x n.k) (fuel : Nat) :
    W.up n hF ∈ cutNodes W seen n (fuel + 1) := by
  rw [cutNodes]
  refine List.mem_cons_of_mem _
    (List.mem_flatMap.mpr ⟨⟨Concept.ex pp c, hF⟩, List.mem_attach _ _, ?_⟩)
  show W.up n hF ∈
    (if mty C0 I (W.up n hF).x ∈ seen then [W.up n hF]
     else cutNodes W (mty C0 I (W.up n hF).x :: seen) (W.up n hF) fuel)
  by_cases hc : mty C0 I (W.up n hF).x ∈ seen
  · rw [if_pos hc]; exact List.mem_cons_self
  · rw [if_neg hc]; exact self_mem_cutNodes W _ _ fuel

/-- The `∃PPI` mirror. -/

    `Ds = []` — this produces the kernel OBJECT, not yet its coverage of a
    named demand. Coverage is `ccovers`, and that is what `rr_covers` does for
    the persistent case; the one-shot case is §114.1. -/
noncomputable def kernelData_of_chain (C0 : Concept) (c : Nat → α)
    (hdom : ∀ n, I.dom (c n)) (hstep : ∀ n, I.rho (c n) (c (n + 1)) = pp)
    (L0 : Nat) : KernelData I C0 [] L0 true (c 0) :=
  let h := kernel_of_chain C0 c (L0 + 1)
  { c := c
    i := Classical.choose h
    p := Classical.choose (Classical.choose_spec h)
    cdom := hdom
    cstep := hstep
    base_ge := by
      have := (Classical.choose_spec (Classical.choose_spec h)).1
      omega
    ipos := by
      have := (Classical.choose_spec (Classical.choose_spec h)).1
      omega
    croot := rfl
    ppos := (Classical.choose_spec (Classical.choose_spec h)).2.1
    cty := (Classical.choose_spec (Classical.choose_spec h)).2.2
    ccovers := fun D hD => absurd hD List.not_mem_nil }

/-! ##### §114.1 — what `ccovers` still needs

`kernelData_of_chain` produces a kernel at `Ds = []`. The certificate's
`he_ex` wants a kernel whose PERIOD carries the demanded `D`.

For PERSISTENT demands that is `rr_covers`, and it works because the guard
`∀PP.(∃PP.D)` keeps `D` available at every height, so the round-robin can serve
each demand in turn.

For ONE-SHOT demands the guard fails by definition, so `D` need not recur, and
`pp_dichotomy`'s chain — which picks an arbitrary demand at each step — has no
reason to meet a `D`-carrier inside its period.

**Which is why the design does not ask it to.** §44.27 serves one-shot demands
by an `elt` EDGE to a node in the set, not by a kernel — and
`cutNodes_up_mem`/`_dn_mem` above put exactly that node in the set. The kernel
is for the persistent half only.

So the remaining question is not "how does a kernel cover a one-shot demand"
(it does not, and should not) but: **do the CUT LEAVES' own demands get
served?** A cut leaf is kept but not expanded, so its witnesses are absent. Its
type equals an expanded ancestor's, which is what blocking exploits — and per
`wp8`'s round-7 lesson the lap must be `PP`-labelled, never `EQ`. -/

/-! #### §119 — THE DESIGN'S OWN DICHOTOMY, ASSEMBLED

§44.18 states it in prose, immediately above `ascend`:

> * if some node reachable by `∃PP` steps has NO `∃PP` demand, the chain
>   TERMINATES, and `short_chain` bounds it;
> * otherwise every reachable node has one, and iterating produces an INFINITE
>   ascending chain — which is a KERNEL.

Both halves have been certified for some time and neither was ever connected
(§113). `chain_or_kernel` is the connection.

Note what this does NOT do: it does not cut at a type repeat. §§112–118's
`cutNodes` is blocking, which the project has had since round 7 and which turns
out to cover only part of the residue (`wp112`: side leaves never continue,
0/44, structurally). The dichotomy below is the design's own mechanism and does
not have that gap — its second branch produces a kernel whenever the chain fails
to terminate, with no appeal to a type repeating. -/

/-- **THE DICHOTOMY.**  Along `∃PP` steps inside a class `P`, either some
    reachable node has no `∃PP` demand at all — the chain terminates, and
    `short_chain` bounds it — or a kernel exists at the start.

    `pp_dichotomy` supplies the split and `kernelData_of_chain` (§114) turns its
    infinite branch into the kernel. Both were certified and unconsumed. -/

    `pp_dichotomy` supplies the split and `kernelData_of_chain` (§114) turns its
    infinite branch into the kernel. Both were certified and unconsumed. -/
theorem chain_or_kernel (C0 : Concept) (L0 : Nat) (P : α → Prop)
    (hcl : ∀ x, P x → ∀ D, Concept.ex pp D ∈ mty C0 I x →
      ∃ y, P y ∧ I.dom y ∧ I.rho x y = pp ∧ D ∈ mty C0 I y)
    (u : α) (hu : I.dom u) (hPu : P u) :
    (∃ x, P x ∧ ∀ D, Concept.ex pp D ∉ mty C0 I x) ∨
      Nonempty (KernelData I C0 [] L0 true u) := by
  rcases pp_dichotomy C0 P hcl u hu hPu with hterm | ⟨c, hc0, hdom, hstep⟩
  · exact Or.inl hterm
  · refine Or.inr ⟨?_⟩
    have K := kernelData_of_chain C0 c hdom hstep L0
    rwa [hc0] at K

/-- The form a caller wants when it already knows every reachable node carries a
    demand: then the terminating branch is impossible and the kernel is
    unconditional. -/

/-- The descending mirror is `persistDsI`/`kernelDataI` territory and is NOT
    derived here: `pp_dichotomy` is stated for `pp` only, and its `ascend`
    generator climbs. Recorded rather than silently assumed. -/
theorem chain_or_kernel_note : True := trivial

/-! #### §121 — A CUT LEAF BELOW ITS BLOCKER IS SERVED FOR FREE

§120.1's second open row is the cut leaf whose lap does not continue and which
the set does not already serve. It splits by ORIENTATION, and one side is free.

If the leaf `v` sits BELOW its blocker `a` — `v ⊂ a`, which is what a descending
step produces — then `a`'s own server for a demand serves `v` too, by
`comp(PP,PP) = {PP}`: `v ⊂ a ⊂ s` gives `v ⊂ s`, and the demand is the same
demand because `mty v = mty a` is what made `v` a leaf.

So no new node, no kernel, and no appeal to the lap continuing. `path_cut_below`
(certified, previously used only inside `chain_cut`) is the whole proof.

The ASCENDING case — `v ⊃ a` — does not follow this way, and should not be
expected to: `comp(PPI,PP)` is `{PPI,PO,PP,EQ}`, so nothing is forced. That case
is the actual residue. -/

/-- **THE BLOCKER'S WITNESS SERVES THE LEAF.**  A leaf below its blocker
    inherits the blocker's servers, by `PP`-transitivity. -/

    What it does NOT supply is acyclicity — that `s` is not already an ancestor
    of `v` — which is a property of the extraction's step graph, not of the
    labels, and is the 5% `wp114` measures. -/
theorem declared_edge_package (C0 : Concept) {v a : α}
    (hty : mty C0 I v = mty C0 I a) {D : Concept}
    (hD : Concept.ex pp D ∈ mty C0 I v) :
    ∃ s, I.dom s ∧ I.rho a s = pp ∧ D ∈ mty C0 I s ∧
      ∀ E, Concept.all pp E ∈ mty C0 I v → E ∈ mty C0 I s := by
  obtain ⟨s, hs, has, hDs⟩ := declared_edge_serves C0 hty hD
  exact ⟨s, hs, has, hDs, fun E hE => declared_edge_all C0 hs hty has hE⟩

/-! #### §127 — THE READ-OFF `ODStruct`, CERTIFIED

`wp115`'s acceptance pass (§126) runs on a hybrid whose vertical order is READ
OFF the model rather than accumulated from the extraction's steps. `odOfModel`
is that structure, and every `ODStruct` axiom comes straight from composition —
no hypothesis, no choice of seed.

`ltNotDj` is free because `I.rho` is a FUNCTION: a pair cannot be both `pp` and
`dr`. `djDown` is the one with content, and it is two applications of
`rho_forced` on the cells `comp(PP,DR) = {DR}` and `comp(DR,PPI) = {DR}` — the
same two cells `RCC5NormalForm.lean` uses for `dr_downward_closed`.

§125.1's boundary is unaffected: this is the order at CONSTANT budget, which is
where `wp96` A's objection does not apply. -/

/-- **THE MODEL'S OWN ORDER, AS AN `ODStruct`.**  Carrier is the in-domain
    elements; `lt` and `disj` are read directly off `I.rho`. -/

/-- **THE MODEL'S OWN ORDER, AS AN `ODStruct`.**  Carrier is the in-domain
    elements; `lt` and `disj` are read directly off `I.rho`. -/
noncomputable def odOfModel (hI : RCC5Interp I) : ODStruct {x : α // I.dom x} where
  lt := fun x y => I.rho x.val y.val = pp
  disj := fun x y => I.rho x.val y.val = dr
  ltIrr := by
    intro x h
    rw [hI.refl_eq x.val x.2] at h
    exact absurd h (by decide)
  ltTr := by
    intro x y z h1 h2
    exact rho_forced hI x.2 z.2 y.2 h1 h2 (by decide)
  djSym := by
    intro x y h
    rw [hI.conv_ x.val y.val x.2 y.2, h]; rfl
  djIrr := by
    intro x h
    rw [hI.refl_eq x.val x.2] at h
    exact absurd h (by decide)
  ltNotDj := by
    intro x y h1 h2
    rw [h1] at h2
    exact absurd h2 (by decide)
  djDown := by
    intro x y x' y' hxy hx' hy'
    -- first push the LEFT endpoint down: comp(PP,DR) = {DR}
    have hx'y : I.rho x'.val y.val = dr := by
      rcases hx' with rfl | hlt
      · exact hxy
      · exact rho_forced hI x'.2 y.2 x.2 hlt hxy (by decide)
    -- then the RIGHT one: comp(DR,PPI) = {DR}
    rcases hy' with rfl | hlt
    · exact hx'y
    · have hyy' : I.rho y.val y'.val = ppi := by
        rw [hI.conv_ y'.val y.val y'.2 y.2, hlt]; rfl
      exact rho_forced hI x'.2 y'.2 y.2 hx'y hyy' (by decide)

/-- The frame is then free — `odNet_frame` with nothing discharged by hand. -/

/-- The frame is then free — `odNet_frame` with nothing discharged by hand. -/
theorem odOfModel_frame (hI : RCC5Interp I) :
    Frame (odNet (odOfModel hI)) := odNet_frame _

/-- **AND IT AGREES WITH THE MODEL** on every pair it decides.  So a demand the
    model serves is served in the read-off frame, which is exactly what §125's
    48 → 5 improvement was. -/

/-- **`e_ex`, ASCENDING, REDUCED TO MEMBERSHIP.** -/
theorem readoff_e_ex_pp (hI : RCC5Interp I) (C0 : Concept)
    {v : α} (hv : I.dom v) (S : α → Prop) {D : Concept}
    (hS : ∃ w, S w ∧ ∃ _hw : I.dom w, I.rho v w = pp ∧ D ∈ mty C0 I w) :
    ∃ (w : α) (hw : I.dom w), S w ∧
      odNet (odOfModel hI) ⟨v, hv⟩ ⟨w, hw⟩ = pp ∧ D ∈ mty C0 I w := by
  obtain ⟨w, hSw, hw, hr, hD⟩ := hS
  exact ⟨w, hw, hSw, odOfModel_pp hI hr, hD⟩

/-- **`e_ex`, DESCENDING.** -/

/-- **`e_ex`, DESCENDING.** -/
theorem readoff_e_ex_ppi (hI : RCC5Interp I) (C0 : Concept)
    {v : α} (hv : I.dom v) (S : α → Prop) {D : Concept}
    (hS : ∃ w, S w ∧ ∃ _hw : I.dom w, I.rho v w = ppi ∧ D ∈ mty C0 I w) :
    ∃ (w : α) (hw : I.dom w), S w ∧
      odNet (odOfModel hI) ⟨v, hv⟩ ⟨w, hw⟩ = ppi ∧ D ∈ mty C0 I w := by
  obtain ⟨w, hSw, hw, hr, hD⟩ := hS
  exact ⟨w, hw, hSw, odOfModel_ppi hI hr, hD⟩

/-- **AND `ee_all` IS AUTOMATIC TOO.**  A universal propagates along a read-off
    edge because the edge IS the model's relation — `mty_all`, with the `odNet`
    value inverted back to `I.rho` by `odNet_pp_inv`.

    So under read-off the two obligations that dominate the certificate are
    discharged by the frame itself, and what remains is entirely about WHICH
    NODES ARE IN THE SET. -/

    So under read-off the two obligations that dominate the certificate are
    discharged by the frame itself, and what remains is entirely about WHICH
    NODES ARE IN THE SET. -/
theorem readoff_ee_all_pp (hI : RCC5Interp I) (C0 : Concept)
    {v w : α} (hv : I.dom v) (hw : I.dom w)
    (h : odNet (odOfModel hI) ⟨v, hv⟩ ⟨w, hw⟩ = pp)
    {E : Concept} (hE : Concept.all pp E ∈ mty C0 I v) :
    E ∈ mty C0 I w :=
  mty_all hE hw (odNet_pp_inv _ h)

/-- The descending mirror. -/

/-- The descending mirror. -/
theorem readoff_ee_all_ppi (hI : RCC5Interp I) (C0 : Concept)
    {v w : α} (hv : I.dom v) (hw : I.dom w)
    (h : odNet (odOfModel hI) ⟨v, hv⟩ ⟨w, hw⟩ = ppi)
    {E : Concept} (hE : Concept.all ppi E ∈ mty C0 I v) :
    E ∈ mty C0 I w := by
  refine mty_all hE hw ?_
  have hwv : I.rho w v = pp := odNet_ppi_inv _ h
  rw [hI.conv_ w v hw hv, hwv]; rfl

/-- And for `DR`, the remaining non-`PO` case. -/
