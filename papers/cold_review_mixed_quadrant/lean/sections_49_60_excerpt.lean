-- EXCERPT: POFreeLift.lean sections 49-60 (the material under review).
-- Not standalone-compilable; read against lean/POFreeLift.lean.

/-! ### §49 — THE ONE-SHOT DICHOTOMY (from `wp101`)

`wp101` re-measured the one-shot vertical obligation over GENUINELY INFINITE
periodic models (`wp100` had measured it over finite ones, where the maximal
element has no `PP`-successor, so 100% of demands read as one-shot — a pure
boundary artifact).  The corrected measurement: of cofinally recurring one-shot
vertical demands, **89.2% are served IN-KERNEL** (the demanded concept recurs on
the chain itself, costing nothing), and the remaining 10.8% need **exactly ONE
external — flat across windows 2p / 4p / 8p / 16p, zero growing cases**.

The reason is a theorem rather than a measurement, and this section is it.
`comp pp pp = [pp]`, so a superpart of `x` is a superpart of everything under
`x`; hence a witness taken at the TOP of a window discharges the demand at EVERY
node of that window.  A demand recurring cofinally therefore does NOT need
cofinally many witnesses — it needs one per layer, and §46.28 bounds the layers
by the cut.

This is why the four routes of §48.1 all failed: they tried to bound a GENERIC
closure, when the obligation is a dichotomy whose two branches the campaign
already owns. -/

section OneShotDichotomy

variable {α : Type} {I : Interp α}

/-- **A `PP`-witness serves everything below.**  Forced by `comp pp pp = [pp]`. -/
theorem pp_witness_below (hI : RCC5Interp I) {x y w : α}
    (hx : I.dom x) (hy : I.dom y) (hw : I.dom w)
    (hyx : I.rho y x = pp) (hxw : I.rho x w = pp) : I.rho y w = pp :=
  rho_forced hI hy hw hx hyx hxw (by decide)

/-- Hence ONE witness discharges an `∃PP` demand at every node below its anchor. -/
theorem ex_pp_serves_below (hI : RCC5Interp I) {x y w : α} {D : Concept}
    (hx : I.dom x) (hy : I.dom y) (hw : I.dom w)
    (hyx : I.rho y x = pp) (hxw : I.rho x w = pp) (hD : sat I w D) :
    sat I y (Concept.ex pp D) :=
  ⟨w, hw, pp_witness_below hI hx hy hw hyx hxw, hD⟩

/-- **THE §49.1 THEOREM — one witness covers a whole window.**  Along an
    ascending chain, the witness supplied by the demand at `c N` discharges that
    same demand at EVERY `c j` with `j ≤ N`.

    This is exactly why `wp101` part D measures the external count as FLAT: a
    cofinally recurring one-shot demand does not need one witness per
    occurrence, it needs one per LAYER. -/
theorem oneshot_one_witness (hI : RCC5Interp I) {c : Nat → α} {D : Concept}
    (hdom : ∀ i, I.dom (c i))
    (hasc : ∀ i j, i < j → I.rho (c i) (c j) = pp) {N : Nat}
    (hex : sat I (c N) (Concept.ex pp D)) :
    ∃ w, I.dom w ∧ sat I w D ∧ I.rho (c N) w = pp ∧
      ∀ j, j ≤ N → sat I (c j) (Concept.ex pp D) := by
  obtain ⟨w, hw, hr, hD⟩ := hex
  refine ⟨w, hw, hD, hr, ?_⟩
  intro j hj
  rcases Nat.lt_or_ge j N with h | h
  · exact ex_pp_serves_below hI (hdom N) (hdom j) hw (hasc j N h) hr hD
  · have hjN : j = N := Nat.le_antisymm hj h
    subst hjN
    exact ⟨w, hw, hr, hD⟩

/-- The dichotomy's FREE branch, made explicit: if the demanded concept itself
    recurs on the chain above `j`, the kernel serves the demand with NO external
    at all.  `wp101` D measures this branch at **89.2%**. -/
theorem oneshot_in_kernel {c : Nat → α} {D : Concept}
    (hdom : ∀ i, I.dom (c i))
    (hasc : ∀ i j, i < j → I.rho (c i) (c j) = pp) {j k : Nat}
    (hjk : j < k) (hD : sat I (c k) D) :
    sat I (c j) (Concept.ex pp D) :=
  ⟨c k, hdom k, hasc j k hjk, hD⟩


/-- **NO MIDDLE CASE: a witness above arbitrarily high chain points is above the
    WHOLE chain.**  Transitivity closes downward, so "above cofinally many" and
    "above all" are the same condition.

    This is the structural fact behind `wp101` part D's flat count: a witness
    cannot serve an unbounded-but-proper part of a kernel. -/
theorem above_cofinal_is_above_all (hI : RCC5Interp I) {c : Nat → α} {w : α}
    (hdom : ∀ i, I.dom (c i)) (hw : I.dom w)
    (hasc : ∀ i j, i < j → I.rho (c i) (c j) = pp)
    (hcof : ∀ N, ∃ i, N < i ∧ I.rho (c i) w = pp) :
    ∀ j, I.rho (c j) w = pp := by
  intro j
  obtain ⟨i, hji, hi⟩ := hcof j
  exact pp_witness_below hI (hdom i) (hdom j) hw (hasc j i hji) hi

/-- **THE WITNESS DICHOTOMY.**  Every candidate witness for a kernel's vertical
    demand either serves the ENTIRE kernel, or serves only a bounded initial
    segment of it.  There is nothing in between.

    So a cofinally recurring one-shot demand is served either by ONE external
    (the first branch) or by witnesses that must keep ascending (the second) —
    and the ascending case is `pp_dichotomy`'s, which produces a kernel and is
    bounded layer-wise by the cut (§46.28). -/
theorem witness_bounded_or_all (hI : RCC5Interp I) {c : Nat → α} {w : α}
    (hdom : ∀ i, I.dom (c i)) (hw : I.dom w)
    (hasc : ∀ i j, i < j → I.rho (c i) (c j) = pp) :
    (∀ j, I.rho (c j) w = pp) ∨ (∃ N, ∀ i, N < i → I.rho (c i) w ≠ pp) := by
  rcases Classical.em (∃ N, ∀ i, N < i → I.rho (c i) w ≠ pp) with h | h
  · exact Or.inr h
  · refine Or.inl (above_cofinal_is_above_all hI hdom hw hasc ?_)
    intro N
    rcases Classical.em (∃ i, N < i ∧ I.rho (c i) w = pp) with h2 | h2
    · exact h2
    · exact absurd ⟨N, fun i hi hr => h2 ⟨i, hi, hr⟩⟩ h

/-- The good branch, named: ONE external above the whole kernel discharges the
    demand at EVERY kernel node.  This is the `(1,1,1,1)` of `wp101` D. -/
theorem cofinal_witness_serves_all {c : Nat → α} {D : Concept} {w : α}
    (hw : I.dom w) (hcof : ∀ i, I.rho (c i) w = pp) (hD : sat I w D) :
    ∀ i, sat I (c i) (Concept.ex pp D) :=
  fun i => ⟨w, hw, hcof i, hD⟩


/-- **THE FINITE-POOL PIGEONHOLE (§49.4) — the branch-closer.**

    If the witnesses for a kernel's vertical demand are drawn from a FINITE pool
    `W`, then one member of `W` is above the ENTIRE kernel.

    Proof: `recurrent_tail` says some pool member is chosen cofinally often, and
    `above_cofinal_is_above_all` upgrades "above cofinally many" to "above all".

    This is the branch `wp101` E could not reach by measurement: with finitely
    many externals available, genuine cofinality FORCES the good branch. And the
    certificate's external set is finite BY CONSTRUCTION — so this is not a
    hypothesis about models, it is a property of the object being built.

    It is also a UNIFORMIZATION of exactly the shape the campaign has wanted
    since W2′: pointwise serving from a finite pool upgrades, for free, to one
    uniform server. Transitivity plus pigeonhole is the whole proof. -/
theorem finite_pool_gives_cofinal_witness (hI : RCC5Interp I) {c : Nat → α}
    {D : Concept} (hdom : ∀ i, I.dom (c i))
    (hasc : ∀ i j, i < j → I.rho (c i) (c j) = pp)
    (W : List α) (hW : ∀ w ∈ W, I.dom w)
    (hpool : ∀ i, ∃ w, w ∈ W ∧ I.rho (c i) w = pp ∧ sat I w D) :
    ∃ w, w ∈ W ∧ (∀ j, I.rho (c j) w = pp) ∧ sat I w D := by
  have hfW : ∀ i, Classical.choose (hpool i) ∈ W :=
    fun i => (Classical.choose_spec (hpool i)).1
  have hfr : ∀ i, I.rho (c i) (Classical.choose (hpool i)) = pp :=
    fun i => (Classical.choose_spec (hpool i)).2.1
  have hfD : ∀ i, sat I (Classical.choose (hpool i)) D :=
    fun i => (Classical.choose_spec (hpool i)).2.2
  obtain ⟨M, hM⟩ := recurrent_tail W (fun i => Classical.choose (hpool i)) hfW
  refine ⟨_, hfW M, ?_, hfD M⟩
  refine above_cofinal_is_above_all hI hdom (hW _ (hfW M)) hasc ?_
  intro N
  obtain ⟨i, hi, heq⟩ := hM M (Nat.le_refl M) (N + 1)
  refine ⟨i, hi, ?_⟩
  rw [← heq]
  exact hfr i

/-- The payoff, stated as serving: a finite pool discharges the demand at EVERY
    kernel node, with ONE external. -/
theorem finite_pool_serves_kernel (hI : RCC5Interp I) {c : Nat → α}
    {D : Concept} (hdom : ∀ i, I.dom (c i))
    (hasc : ∀ i j, i < j → I.rho (c i) (c j) = pp)
    (W : List α) (hW : ∀ w ∈ W, I.dom w)
    (hpool : ∀ i, ∃ w, w ∈ W ∧ I.rho (c i) w = pp ∧ sat I w D) :
    ∃ w, w ∈ W ∧ ∀ i, sat I (c i) (Concept.ex pp D) := by
  obtain ⟨w, hwW, hall, hD⟩ :=
    finite_pool_gives_cofinal_witness hI hdom hasc W hW hpool
  exact ⟨w, hwW, cofinal_witness_serves_all (hW w hwW) hall hD⟩


/-- **ALL OR NOTHING (§49.5).**  A FINITE pool either contains a single member
    that serves the WHOLE kernel, or it fails outright at some kernel node.
    There is no configuration in which several partial servers between them
    cover a kernel.

    This is the exact statement behind `wp101` part D's `(1,1,1,1,1,1)`: the
    external count for a kernel's vertical demand is never 2, 3, … — it is 1 or
    the pool is inadequate. Together with `oneshot_in_kernel` it leaves a clean
    TRICHOTOMY for a cofinally recurring one-shot vertical demand:

    1. the demanded concept recurs on the chain — served IN-KERNEL, cost 0;
    2. one external sits above the whole kernel — cost 1;
    3. neither — and then NO finite external set can serve it, so the residual
       question is precisely whether a ∀PO-free concept can force case 3. -/
theorem finite_pool_all_or_nothing (hI : RCC5Interp I) {c : Nat → α}
    {D : Concept} (hdom : ∀ i, I.dom (c i))
    (hasc : ∀ i j, i < j → I.rho (c i) (c j) = pp)
    (W : List α) (hW : ∀ w ∈ W, I.dom w) :
    (∃ w, w ∈ W ∧ (∀ j, I.rho (c j) w = pp) ∧ sat I w D) ∨
    (∃ i, ∀ w, w ∈ W → I.rho (c i) w = pp → ¬ sat I w D) := by
  rcases Classical.em (∀ i, ∃ w, w ∈ W ∧ I.rho (c i) w = pp ∧ sat I w D) with h | h
  · exact Or.inl (finite_pool_gives_cofinal_witness hI hdom hasc W hW h)
  · rcases Classical.em (∃ i, ∀ w, w ∈ W → I.rho (c i) w = pp → ¬ sat I w D)
      with h2 | h2
    · exact Or.inr h2
    · exact absurd (fun i => Classical.byContradiction (fun hno =>
        h2 ⟨i, fun w hwW hr hD => hno ⟨w, hwW, hr, hD⟩⟩)) h


/-- **CASE 3 IS NEVER A CONSISTENCY FAILURE (§50).**  The type a cofinal server
    needs — every `∀PP` consequent holding at the demanding node, together with
    the demanded concept — is realized by the demand's OWN witness.

    So nothing has to be invented to serve a one-shot vertical demand: the
    required type already occurs in the model. The only thing missing is
    POSITION, and `odTop` below supplies exactly that. This is what turns §49's
    case 3 from "an unknown obstruction" into "a placement step". -/
theorem witness_realizes_requirement {x w : α} {D : Concept} (hw : I.dom w)
    (hr : I.rho x w = pp) (hD : sat I w D) (Cons : List Concept)
    (hcons : ∀ X ∈ Cons, sat I x (Concept.all pp X)) :
    sat I w D ∧ ∀ X ∈ Cons, sat I w X :=
  ⟨hD, fun X hX => hcons X hX w hw hr⟩

/-! ### §51.4 — THE CAP'S UNIVERSALS ARE SOUND, AND IT IS A THEOREM

§51.3 left the cap's LABELS open, and the danger was pinned by §50.4 to a single
universal: a label copied from the demand's witness `w` may carry `∀PPI.Y`,
which then fires downward on the WHOLE closure, while `w` guarantees `Y` only
below itself.

`wp103` measured this as sound at 100% — but on only **2 of 44** labels that
carried a `∀PPI` at all, so the rate was nearly vacuous and worth nothing.
Working out what an adversarial instance would need produced the proof instead.

**The demand is present at EVERY chain node** (that is what "cofinally
recurring" plus downward closure of the order gives). So every `c j` has its own
witness `w j`, and every one of those witnesses carries `∀PPI.Y`. A closure node
`u` lies below SOME `c j`; transitivity puts it below `w j`; and `w j`'s
universal delivers `Y`.

So the witnesses' universals BLANKET the closure. The cap may copy a witness's
label after all — no model extension needed for this obligation. -/

/-- **THE CAP'S `∀PPI` OBLIGATION HOLDS.**  See §51.4: every closure node is
    below some chain node, hence below that node's own witness, hence covered by
    the witness's universal. -/
theorem cap_all_ppi_sound (hI : RCC5Interp I) {c : Nat → α} {Y : Concept}
    (hdom : ∀ i, I.dom (c i))
    (hw : ∀ j, ∃ w, I.dom w ∧ I.rho (c j) w = pp ∧
      sat I w (Concept.all ppi Y))
    {u : α} (hu : I.dom u) {j : Nat} (hru : I.rho u (c j) = pp) :
    sat I u Y := by
  obtain ⟨w, hwd, hrw, hall⟩ := hw j
  have huw : I.rho u w = pp := pp_witness_below hI (hdom j) hu hwd hru hrw
  have hwu : I.rho w u = ppi := by rw [hI.conv_ u w hu hwd, huw]; rfl
  exact hall u hu hwu

/-- The same for the chain nodes themselves — the other half of the closure. -/
theorem cap_all_ppi_sound_chain (hI : RCC5Interp I) {c : Nat → α} {Y : Concept}
    (hdom : ∀ i, I.dom (c i))
    (hw : ∀ j, ∃ w, I.dom w ∧ I.rho (c j) w = pp ∧
      sat I w (Concept.all ppi Y)) (j : Nat) :
    sat I (c j) Y := by
  obtain ⟨w, hwd, hrw, hall⟩ := hw j
  have hwu : I.rho w (c j) = ppi := by
    rw [hI.conv_ (c j) w (hdom j) hwd, hrw]; rfl
  exact hall (c j) (hdom j) hwu

/-! ### §52 — THE LAYER RECURSION TERMINATES

§51.6 left exactly one item: a cap node's OWN `∃PP` demand, needing a cap above
the cap. That recursion is bounded, and for a reason that is worth stating
precisely because it is what §47.5's refuted construction could NOT arrange.

`path_cut` licenses reusing a node that is above in the ORDER. §47.2 tried to
reuse a node above in the TREE — a path accumulator — and the two are different,
which is why it was withdrawn. **Caps are stacked in the order.** So the cut
applies to them directly, with nothing to arrange.

Stack the caps `T 0 PP T 1 PP …`. Their model types are drawn from
`typeEnum C0`, so past any point two layers repeat. At a repeat `i < j` with
equal types, every demand of `T i` is a demand of `T j`, and `T j`'s server lies
above `T i` as well — so no layer beyond `j` is needed. -/

/-- **THE LAYER CUT.**  At a repeat, the higher layer's server also serves the
    lower layer, so the stack truncates there. -/
theorem layer_cut (hI : RCC5Interp I) {Ti Tj w : α}
    (hi : I.dom Ti) (hj : I.dom Tj) (hw : I.dom w)
    (hij : I.rho Ti Tj = pp) (hjw : I.rho Tj w = pp)
    {D : Concept} (hD : sat I w D) :
    sat I Ti (Concept.ex pp D) ∧ sat I Tj (Concept.ex pp D) :=
  ⟨ex_pp_serves_below hI hj hi hw hij hjw hD, ⟨w, hw, hjw, hD⟩⟩

/-- **THE RECURSION TERMINATES.**  Past ANY point the cap stack repeats a type,
    and at the repeat the higher layer's servers cover the lower one. So the
    layer count is bounded by `C₀` alone, via `typeEnum`. -/
theorem layer_recursion_terminates (hI : RCC5Interp I) {C0 : Concept}
    (T : Nat → α) (hdom : ∀ i, I.dom (T i))
    (hasc : ∀ i j, i < j → I.rho (T i) (T j) = pp) (L : Nat) :
    ∃ i j, L ≤ i ∧ i < j ∧ mty C0 I (T i) = mty C0 I (T j) ∧
      ∀ D w, I.dom w → I.rho (T j) w = pp → sat I w D →
        sat I (T i) (Concept.ex pp D) := by
  obtain ⟨i, j, hLi, hij, hty⟩ :=
    segment_exists (typeEnum C0) (fun k => mty C0 I (T k))
      (fun k => mty_mem_typeEnum C0 I (T k)) L
  exact ⟨i, j, hLi, hij, hty, fun D w hw hr hD =>
    ex_pp_serves_below hI (hdom j) (hdom i) hw (hasc i j hij) hr hD⟩

/-- The counting form: a cap stack with pairwise distinct types is no longer than
    the type enumeration. -/
theorem layer_stack_bounded {C0 : Concept} (Ts : List α)
    (hnd : (Ts.map (fun x => mty C0 I x)).Nodup) :
    Ts.length ≤ (typeEnum C0).length :=
  repeatfree_len_le C0 I Ts hnd

/-! ### §53 — WIRING THE CAP IN

§52.1's audit left two rows open, and they are one task: make the cap **just
another external**. `odSeed` already takes the order, the kernel attachment and
the disjointness seed abstractly, so nothing new about frames is needed — the
job is to extend `(elt, up, dn, seed)` from `β` to `β ⊕ M` and re-discharge
`odSeed`'s five hypotheses.

The cap sits above the downward-closed set `U` and above the kernels flagged by
`capOver`; it is below nothing and disjoint from nothing. Two side conditions
are what the construction has to supply, and both are exactly what §50–§51
established:

* `hUdown` — `U` is downward closed under `elt` (the placement rule, §50.2);
* `hcov` — anything below a kernel the cap covers is in `U` (the cap is above
  the kernel's whole closure, §51). -/

section CapWiring

variable {β κ M : Type}

/-- The extended order: old externals as before, everything in `U` below every
    cap node, and cap nodes below nothing. -/
def capElt (elt : β → β → Prop) (U : β → Prop) (P : M → M → Prop) :
    β ⊕ M → β ⊕ M → Prop
  | .inl e, .inl f => elt e f
  | .inl e, .inr _ => U e
  | .inr m, .inr m' => P m m'
  | .inr _, .inl _ => False

/-- No cap node lies below a kernel. -/
def capUp (up : κ → β → Bool) : κ → β ⊕ M → Bool
  | k, .inl e => up k e
  | _, .inr _ => false

/-- A cap node lies above exactly the kernels it is declared to cover. -/
def capDn (dn : κ → β → Bool) (capOver : κ → Bool) : κ → β ⊕ M → Bool
  | k, .inl e => dn k e
  | k, .inr _ => capOver k

/-- The embedding of the old index into the extended one. -/
def embC : β ⊕ κ → (β ⊕ M) ⊕ κ
  | .inl e => .inl (.inl e)
  | .inr k => .inr k

/-- The seed is untouched, and cap nodes are in no seed pair — so the cap is
    disjoint from nothing, as §51.1 showed a cap must be. -/
def capSeed (seed : β ⊕ κ → β ⊕ κ → Prop) :
    (β ⊕ M) ⊕ κ → (β ⊕ M) ⊕ κ → Prop
  | .inl (.inl e), .inl (.inl f) => seed (.inl e) (.inl f)
  | .inl (.inl e), .inr k => seed (.inl e) (.inr k)
  | .inr k, .inl (.inl e) => seed (.inr k) (.inl e)
  | .inr k, .inr k' => seed (.inr k) (.inr k')
  | _, _ => False

/-- **REFLECTION: on old nodes the extended order IS the old order.**  Adding the
    cap changes nothing below it — which is what makes the extension safe. -/
theorem capMixLt_old (elt : β → β → Prop) (up dn : κ → β → Bool)
    (U : β → Prop) (P : M → M → Prop) (capOver : κ → Bool) (x y : β ⊕ κ) :
    mixLt (capElt (M := M) elt U P) (capUp up) (capDn dn capOver)
        (embC x) (embC y) ↔ mixLt elt up dn x y := by
  cases x with
  | inl e =>
    cases y with
    | inl f => exact Iff.rfl
    | inr k =>
      constructor
      · rintro ⟨e', hup, hle⟩
        cases e' with
        | inl e'' => exact ⟨e'', hup, by
            rcases hle with h | h
            · exact Or.inl (Sum.inl.inj h)
            · exact Or.inr h⟩
        | inr _ => exact absurd hup (by simp [capUp])
      · rintro ⟨e', hup, hle⟩
        exact ⟨.inl e', hup, by
          rcases hle with rfl | h
          · exact Or.inl rfl
          · exact Or.inr h⟩
  | inr k =>
    cases y with
    | inl e =>
      constructor
      · rintro ⟨e', hdn, hle⟩
        cases e' with
        | inl e'' => exact ⟨e'', hdn, by
            rcases hle with h | h
            · exact Or.inl (Sum.inl.inj h)
            · exact Or.inr h⟩
        | inr _ =>
          rcases hle with h | h
          · exact absurd h (fun hh => inr_ne_inl _ _ hh)
          · exact h.elim
      · rintro ⟨e', hdn, hle⟩
        exact ⟨.inl e', hdn, by
          rcases hle with rfl | h
          · exact Or.inl rfl
          · exact Or.inr h⟩
    | inr k' =>
      constructor
      · rintro ⟨e, e', hdn, hup, hle⟩
        cases e' with
        | inr _ => exact absurd hup (by simp [capUp])
        | inl f' =>
          cases e with
          | inl f => exact ⟨f, f', hdn, hup, by
              rcases hle with h | h
              · exact Or.inl (Sum.inl.inj h)
              · exact Or.inr h⟩
          | inr _ =>
            rcases hle with h | h
            · exact absurd h (fun hh => inr_ne_inl _ _ hh)
            · exact h.elim
      · rintro ⟨e, e', hdn, hup, hle⟩
        exact ⟨.inl e, .inl e', hdn, hup, by
          rcases hle with rfl | h
          · exact Or.inl rfl
          · exact Or.inr h⟩


/-- **A CAP NODE IS BELOW NOTHING OLD.**  So any `mixLe` into an old node comes
    from an old node, and reflects. -/
theorem capMixLe_to_old (elt : β → β → Prop) (up dn : κ → β → Bool)
    (U : β → Prop) (P : M → M → Prop) (capOver : κ → Bool) {x : (β ⊕ M) ⊕ κ} {y : β ⊕ κ}
    (h : mixLe (capElt elt U P) (capUp up) (capDn dn capOver) x (embC y)) :
    ∃ x₀ : β ⊕ κ, x = embC x₀ ∧ mixLe elt up dn x₀ y := by
  cases x with
  | inr k =>
    refine ⟨.inr k, rfl, ?_⟩
    rcases h with heq | hlt
    · cases y with
      | inl _ => exact absurd heq (fun hh => inr_ne_inl _ _ hh)
      | inr k' =>
        have : k = k' := by
          have := heq
          simp only [embC] at this
          exact Sum.inr.inj this
        subst this; exact Or.inl rfl
    · exact Or.inr ((capMixLt_old elt up dn U P capOver (.inr k) y).mp hlt)
  | inl a =>
    cases a with
    | inl e =>
      refine ⟨.inl e, rfl, ?_⟩
      rcases h with heq | hlt
      · cases y with
        | inr _ => exact absurd heq (fun hh => inr_ne_inl _ _ hh.symm)
        | inl f =>
          have : e = f := by
            have := heq
            simp only [embC] at this
            exact Sum.inl.inj (Sum.inl.inj this)
          subst this; exact Or.inl rfl
      · exact Or.inr ((capMixLt_old elt up dn U P capOver (.inl e) y).mp hlt)
    | inr m =>
      exfalso
      rcases h with heq | hlt
      · cases y with
        | inl f =>
          have := heq
          simp only [embC] at this
          exact inr_ne_inl _ _ (Sum.inl.inj this)
        | inr _ => exact inr_ne_inl _ _ heq.symm
      · cases y with
        | inl f => exact hlt
        | inr k =>
          obtain ⟨e', hup, hle⟩ := hlt
          cases e' with
          | inr _ => exact absurd hup (by simp [capUp])
          | inl f' =>
            rcases hle with hh | hh
            · exact inr_ne_inl _ _ hh
            · exact hh

/-- The embedding is injective. -/
theorem embC_inj {x y : β ⊕ κ} (h : (embC x : (β ⊕ M) ⊕ κ) = embC y) : x = y := by
  cases x with
  | inl e =>
    cases y with
    | inl f =>
      simp only [embC] at h
      exact congrArg Sum.inl (Sum.inl.inj (Sum.inl.inj h))
    | inr _ => exact absurd h (fun hh => inr_ne_inl _ _ hh.symm)
  | inr k =>
    cases y with
    | inl _ => exact absurd h (fun hh => inr_ne_inl _ _ hh)
    | inr k' =>
      simp only [embC] at h
      exact congrArg Sum.inr (Sum.inr.inj h)

/-- `mixLe` between two OLD nodes reflects to the old order. -/
theorem capMixLe_old_old (elt : β → β → Prop) (up dn : κ → β → Bool)
    (U : β → Prop) (P : M → M → Prop) (capOver : κ → Bool) (x y : β ⊕ κ)
    (h : mixLe (capElt (M := M) elt U P) (capUp up) (capDn dn capOver)
      (embC x) (embC y)) : mixLe elt up dn x y := by
  rcases h with heq | hlt
  · have hxy : x = y := embC_inj heq
    subst hxy; exact Or.inl rfl
  · exact Or.inr ((capMixLt_old elt up dn U P capOver x y).mp hlt)

/-- `hirrE` for the extended order. -/
theorem capElt_irr (elt : β → β → Prop) (U : β → Prop) (P : M → M → Prop)
    (hirrE : ∀ e, ¬ elt e e) (hPirr : ∀ m, ¬ P m m) :
    ∀ e : β ⊕ M, ¬ capElt elt U P e e := by
  rintro (e | m)
  · exact hirrE e
  · exact hPirr m

/-- `htr` for the extended order — this is where `U` must be DOWNWARD CLOSED. -/
theorem capElt_trans (elt : β → β → Prop) (U : β → Prop) (P : M → M → Prop)
    (htr : ∀ a b c, elt a b → elt b c → elt a c)
    (hUdown : ∀ e f, elt e f → U f → U e)
    (hPtr : ∀ a b c, P a b → P b c → P a c) :
    ∀ a b c : β ⊕ M, capElt elt U P a b → capElt elt U P b c →
      capElt elt U P a c := by
  rintro (a | m) b c h1 h2
  · cases b with
    | inr m' =>
      cases c with
      | inl _ => exact h2.elim
      | inr _ => exact h1
    | inl b' =>
      cases c with
      | inl c' => exact htr a b' c' h1 h2
      | inr _ => exact hUdown a b' h1 h2
  · cases b with
    | inl _ => exact h1.elim
    | inr m' =>
      cases c with
      | inl _ => exact h2.elim
      | inr m'' => exact hPtr m m' m'' h1 h2

/-- `hud` for the extended data — this is where the cap must sit above the WHOLE
    closure of every kernel it covers. -/
theorem capElt_ud (elt : β → β → Prop) (up dn : κ → β → Bool)
    (U : β → Prop) (P : M → M → Prop) (capOver : κ → Bool)
    (hud : ∀ k x y, up k x = true → dn k y = true → elt x y)
    (hcov : ∀ k e, up k e = true → capOver k = true → U e) :
    ∀ (k : κ) (x y : β ⊕ M), capUp up k x = true → capDn dn capOver k y = true →
      capElt elt U P x y := by
  rintro k (e | m) (f | m') h1 h2
  · exact hud k e f h1 h2
  · exact hcov k e h1 h2
  · exact absurd h1 (by simp [capUp])
  · exact absurd h1 (by simp [capUp])

/-- `hsym` for the extended seed. -/
theorem capSeed_sym (seed : β ⊕ κ → β ⊕ κ → Prop)
    (hsym : ∀ x y, seed x y → seed y x) :
    ∀ x y : (β ⊕ M) ⊕ κ, capSeed seed x y → capSeed seed y x := by
  rintro (a | k) (b | k') h
  · cases a with
    | inr _ => exact h.elim
    | inl e =>
      cases b with
      | inr _ => exact h.elim
      | inl f => exact hsym _ _ h
  · cases a with
    | inr _ => exact h.elim
    | inl e => exact hsym _ _ h
  · cases b with
    | inr _ => exact h.elim
    | inl f => exact hsym _ _ h
  · exact hsym _ _ h


/-- `hsep` for the extended data.  Cap nodes are in no seed pair, so the only
    live case has both endpoints old — and then `capMixLe_to_old` reflects the
    hypotheses and the OLD `hsep` finishes it. -/
theorem capSeed_sep (elt : β → β → Prop) (up dn : κ → β → Bool)
    (U : β → Prop) (P : M → M → Prop) (capOver : κ → Bool)
    (seed : β ⊕ κ → β ⊕ κ → Prop)
    (hsep : ∀ x y z, mixLe elt up dn x y → mixLe elt up dn x z → ¬ seed y z) :
    ∀ x y z : (β ⊕ M) ⊕ κ,
      mixLe (capElt elt U P) (capUp up) (capDn dn capOver) x y →
      mixLe (capElt elt U P) (capUp up) (capDn dn capOver) x z →
      ¬ capSeed seed y z := by
  intro x y z h1 h2 hs
  have key : ∀ (y₀ z₀ : β ⊕ κ),
      mixLe (capElt (M := M) elt U P) (capUp up) (capDn dn capOver) x (embC y₀) →
      mixLe (capElt (M := M) elt U P) (capUp up) (capDn dn capOver) x (embC z₀) →
      seed y₀ z₀ → False := by
    intro y₀ z₀ hy hz hsd
    obtain ⟨x₀, hx0, _⟩ := capMixLe_to_old elt up dn U P capOver hy
    subst hx0
    exact hsep x₀ y₀ z₀ (capMixLe_old_old elt up dn U P capOver _ _ hy)
      (capMixLe_old_old elt up dn U P capOver _ _ hz) hsd
  cases y with
  | inr k =>
    cases z with
    | inr k' => exact key (.inr k) (.inr k') h1 h2 hs
    | inl b =>
      cases b with
      | inl f => exact key (.inr k) (.inl f) h1 h2 hs
      | inr _ => exact hs
  | inl a =>
    cases a with
    | inr _ => exact hs
    | inl e =>
      cases z with
      | inr k' => exact key (.inl e) (.inr k') h1 h2 hs
      | inl b =>
        cases b with
        | inl f => exact key (.inl e) (.inl f) h1 h2 hs
        | inr _ => exact hs

/-- The reverse of `capMixLe_old_old`: old order embeds. -/
theorem capMixLe_of_old (elt : β → β → Prop) (up dn : κ → β → Bool)
    (U : β → Prop) (P : M → M → Prop) (capOver : κ → Bool) (x y : β ⊕ κ)
    (h : mixLe elt up dn x y) :
    mixLe (capElt (M := M) elt U P) (capUp up) (capDn dn capOver)
      (embC x) (embC y) := by
  rcases h with rfl | hlt
  · exact Or.inl rfl
  · exact Or.inr ((capMixLt_old elt up dn U P capOver x y).mpr hlt)

/-- A seed pair in the extended structure is a seed pair of old nodes. -/
theorem capSeed_old (seed : β ⊕ κ → β ⊕ κ → Prop)
    {x y : (β ⊕ M) ⊕ κ} (h : capSeed seed x y) :
    ∃ x₀ y₀ : β ⊕ κ, x = embC x₀ ∧ y = embC y₀ ∧ seed x₀ y₀ := by
  cases x with
  | inr k =>
    cases y with
    | inr k' => exact ⟨.inr k, .inr k', rfl, rfl, h⟩
    | inl b =>
      cases b with
      | inl f => exact ⟨.inr k, .inl f, rfl, rfl, h⟩
      | inr _ => exact h.elim
  | inl a =>
    cases a with
    | inr _ => exact h.elim
    | inl e =>
      cases y with
      | inr k' => exact ⟨.inl e, .inr k', rfl, rfl, h⟩
      | inl b =>
        cases b with
        | inl f => exact ⟨.inl e, .inl f, rfl, rfl, h⟩
        | inr _ => exact h.elim

/-- **THE CAPPED FRAME.**  Assembling the five hypotheses: the extraction's
    structure EXTENDED BY A CAP is still ordered-disjoint, so `odNet_frame`
    supplies its RCC5 frame — the cap is now literally just another external. -/
def odSeedCap (elt : β → β → Prop) (up dn : κ → β → Bool)
    (U : β → Prop) (P : M → M → Prop) (capOver : κ → Bool)
    (seed : β ⊕ κ → β ⊕ κ → Prop)
    (hirrE : ∀ e, ¬ elt e e) (htr : ∀ a b c, elt a b → elt b c → elt a c)
    (hud : ∀ k x y, up k x = true → dn k y = true → elt x y)
    (hsym : ∀ x y, seed x y → seed y x)
    (hsep : ∀ x y z, mixLe elt up dn x y → mixLe elt up dn x z → ¬ seed y z)
    (hUdown : ∀ e f, elt e f → U f → U e)
    (hcov : ∀ k e, up k e = true → capOver k = true → U e)
    (hPirr : ∀ m, ¬ P m m) (hPtr : ∀ a b c, P a b → P b c → P a c) :
    ODStruct ((β ⊕ M) ⊕ κ) :=
  odSeed (capElt elt U P) (capUp up) (capDn dn capOver) (capSeed seed)
    (capElt_irr elt U P hirrE hPirr) (capElt_trans elt U P htr hUdown hPtr)
    (capElt_ud elt up dn U P capOver hud hcov) (capSeed_sym seed hsym)
    (capSeed_sep elt up dn U P capOver seed hsep)

/-- **THE TRANSFER THEOREM — adding a cap changes NOTHING below it.**

    On old nodes the capped net is the uncapped net, edge for edge. So every
    obligation already certified for the extraction's structure carries over to
    the capped one unchanged, and only the genuinely NEW edges (base↔cap,
    kernel↔cap, cap↔cap) need anything proved. -/
theorem odSeedCap_old (elt : β → β → Prop) (up dn : κ → β → Bool)
    (U : β → Prop) (P : M → M → Prop) (capOver : κ → Bool)
    (seed : β ⊕ κ → β ⊕ κ → Prop)
    (hirrE : ∀ e, ¬ elt e e) (htr : ∀ a b c, elt a b → elt b c → elt a c)
    (hud : ∀ k x y, up k x = true → dn k y = true → elt x y)
    (hsym : ∀ x y, seed x y → seed y x)
    (hsep : ∀ x y z, mixLe elt up dn x y → mixLe elt up dn x z → ¬ seed y z)
    (hUdown : ∀ e f, elt e f → U f → U e)
    (hcov : ∀ k e, up k e = true → capOver k = true → U e)
    (hPirr : ∀ m, ¬ P m m) (hPtr : ∀ a b c, P a b → P b c → P a c)
    (x y : β ⊕ κ) :
    odNet (odSeedCap (M := M) elt up dn U P capOver seed
        hirrE htr hud hsym hsep hUdown hcov hPirr hPtr) (embC x) (embC y)
      = odNet (odSeed elt up dn seed hirrE htr hud hsym hsep) x y := by
  have hlt : ∀ a b : β ⊕ κ,
      (odSeedCap (M := M) elt up dn U P capOver seed
        hirrE htr hud hsym hsep hUdown hcov hPirr hPtr).lt (embC a) (embC b)
        ↔ (odSeed elt up dn seed hirrE htr hud hsym hsep).lt a b :=
    fun a b => capMixLt_old elt up dn U P capOver a b
  have hdj : ∀ a b : β ⊕ κ,
      (odSeedCap (M := M) elt up dn U P capOver seed
        hirrE htr hud hsym hsep hUdown hcov hPirr hPtr).disj (embC a) (embC b)
        ↔ (odSeed elt up dn seed hirrE htr hud hsym hsep).disj a b := by
    intro a b
    constructor
    · rintro ⟨x₀, y₀, hx, hy, hs⟩
      obtain ⟨x₁, y₁, rfl, rfl, hs'⟩ := capSeed_old seed hs
      exact ⟨x₁, y₁, capMixLe_old_old elt up dn U P capOver _ _ hx,
        capMixLe_old_old elt up dn U P capOver _ _ hy, hs'⟩
    · rintro ⟨x₀, y₀, hx, hy, hs⟩
      exact ⟨embC x₀, embC y₀, capMixLe_of_old elt up dn U P capOver _ _ hx,
        capMixLe_of_old elt up dn U P capOver _ _ hy, by
          cases x₀ with
          | inl _ => cases y₀ with
            | inl _ => exact hs
            | inr _ => exact hs
          | inr _ => cases y₀ with
            | inl _ => exact hs
            | inr _ => exact hs⟩
  by_cases hxy : x = y
  · subst hxy; rw [odNet_self, odNet_self]
  · have hne : (embC x : (β ⊕ M) ⊕ κ) ≠ embC y := fun h => hxy (embC_inj h)
    by_cases h1 : (odSeed elt up dn seed hirrE htr hud hsym hsep).lt x y
    · rw [odNet_lt _ ((hlt x y).mpr h1), odNet_lt _ h1]
    · by_cases h2 : (odSeed elt up dn seed hirrE htr hud hsym hsep).lt y x
      · rw [odNet_gt _ ((hlt y x).mpr h2), odNet_gt _ h2]
      · by_cases h3 : (odSeed elt up dn seed hirrE htr hud hsym hsep).disj x y
        · rw [odNet_dj _ ((hdj x y).mpr h3), odNet_dj _ h3]
        · rw [odNet_po _ hne (fun hh => h1 ((hlt x y).mp hh))
              (fun hh => h2 ((hlt y x).mp hh)) (fun hh => h3 ((hdj x y).mp hh)),
            odNet_po _ hxy h1 h2 h3]

theorem odSeedCap_frame (elt : β → β → Prop) (up dn : κ → β → Bool)
    (U : β → Prop) (P : M → M → Prop) (capOver : κ → Bool)
    (seed : β ⊕ κ → β ⊕ κ → Prop)
    (hirrE : ∀ e, ¬ elt e e) (htr : ∀ a b c, elt a b → elt b c → elt a c)
    (hud : ∀ k x y, up k x = true → dn k y = true → elt x y)
    (hsym : ∀ x y, seed x y → seed y x)
    (hsep : ∀ x y z, mixLe elt up dn x y → mixLe elt up dn x z → ¬ seed y z)
    (hUdown : ∀ e f, elt e f → U f → U e)
    (hcov : ∀ k e, up k e = true → capOver k = true → U e)
    (hPirr : ∀ m, ¬ P m m) (hPtr : ∀ a b c, P a b → P b c → P a c) :
    Frame (odNet (odSeedCap (M := M) elt up dn U P capOver seed
      hirrE htr hud hsym hsep hUdown hcov hPirr hPtr)) := odNet_frame _

end CapWiring

section CapEdges

variable {β κ M : Type} {elt : β → β → Prop} {up dn : κ → β → Bool}
  {U : β → Prop} {P : M → M → Prop} {capOver : κ → Bool}
  {seed : β ⊕ κ → β ⊕ κ → Prop}
  {hirrE : ∀ e, ¬ elt e e} {htr : ∀ a b c, elt a b → elt b c → elt a c}
  {hud : ∀ k x y, up k x = true → dn k y = true → elt x y}
  {hsym : ∀ x y, seed x y → seed y x}
  {hsep : ∀ x y z, mixLe elt up dn x y → mixLe elt up dn x z → ¬ seed y z}
  {hUdown : ∀ e f, elt e f → U f → U e}
  {hcov : ∀ k e, up k e = true → capOver k = true → U e}
  {hPirr : ∀ m, ¬ P m m} {hPtr : ∀ a b c, P a b → P b c → P a c}

local notation "OC" => odSeedCap (M := M) elt up dn U P capOver seed
  hirrE htr hud hsym hsep hUdown hcov hPirr hPtr

/-- **THE CAP IS DISJOINT FROM NOTHING** — as §51.1 showed a cap must be. -/
theorem cap_not_disj (m : M) (x : (β ⊕ M) ⊕ κ) :
    ¬ (OC).disj x (Sum.inl (Sum.inr m)) := by
  rintro ⟨x₀, y₀, _, hy, hs⟩
  obtain ⟨x₁, y₁, rfl, rfl, _⟩ := capSeed_old seed hs
  obtain ⟨z, hz, _⟩ := capMixLe_to_old elt up dn U P capOver hy
  cases z with
  | inl e =>
    have := hz
    simp only [embC] at this
    exact inr_ne_inl _ _ (Sum.inl.inj this)
  | inr k => exact inr_ne_inl _ _ hz.symm

/-- An external inside the closure is `PP`-below every cap node. -/
theorem cap_above_U {e : β} (hU : U e) (m : M) :
    odNet (OC) (Sum.inl (Sum.inl e)) (Sum.inl (Sum.inr m)) = pp :=
  odNet_lt _ hU

/-- An external outside the closure is `PO` to every cap node — and `∀PO` is
    absent, so it constrains nothing. -/
theorem cap_po_outside {e : β} (hU : ¬ U e) (m : M) :
    odNet (OC) (Sum.inl (Sum.inl e)) (Sum.inl (Sum.inr m)) = po :=
  odNet_po _ (fun h => inr_ne_inl _ _ (Sum.inl.inj h).symm) hU (fun h => h)
    (cap_not_disj m _)

/-- A covered kernel is `PP`-below every cap node. -/
theorem cap_above_kernel {k : κ} (hk : capOver k = true) (m : M) :
    odNet (OC) (Sum.inr k) (Sum.inl (Sum.inr m)) = pp :=
  odNet_lt _ ⟨Sum.inr m, hk, Or.inl rfl⟩

/-- **THE LAYER EDGE.**  A cap node below another in the cap-internal order is
    `PP`-below it — which is what lets a cap node's OWN `∃PP` demand be served,
    by the next layer of §52's stack. This is the edge §53's first wiring
    lacked, found by writing `e_ex`. -/
theorem cap_pp_cap {m m' : M} (hP : P m m') :
    odNet (OC) (Sum.inl (Sum.inr m)) (Sum.inl (Sum.inr m')) = pp :=
  odNet_lt _ hP

/-- Cap nodes INCOMPARABLE in the cap order are `PO` — the §51.5 fan.  Taking
    `P` empty recovers a pure antichain, in which conflicting demands never
    constrain one another. -/
theorem cap_po_cap {m m' : M} (hmm : m ≠ m')
    (h1 : ¬ P m m') (h2 : ¬ P m' m) :
    odNet (OC) (Sum.inl (Sum.inr m)) (Sum.inl (Sum.inr m')) = po :=
  odNet_po _ (fun h => hmm (Sum.inr.inj (Sum.inl.inj h))) h1 h2
    (cap_not_disj m' _)


/-- **NO `DR` EDGE TOUCHES A CAP NODE** — so `∀DR` at a cap node fires
    vacuously, and no `∃DR` demand can be served BY a cap node either (it must
    be served from the base, §51.2). -/
theorem cap_no_dr_edge (m : M) (x : (β ⊕ M) ⊕ κ) :
    odNet (OC) (Sum.inl (Sum.inr m)) x ≠ dr := by
  intro h
  exact cap_not_disj m x ((OC).djSym _ _ (odNet_dr_inv _ h))

/-- The mirror: no `DR` edge INTO a cap node either. -/
theorem cap_no_dr_edge' (m : M) (x : (β ⊕ M) ⊕ κ) :
    odNet (OC) x (Sum.inl (Sum.inr m)) ≠ dr := by
  intro h
  exact cap_not_disj m x (odNet_dr_inv _ h)

end CapEdges


/-! ### §56 — THE CAPPED CERTIFICATE, BUILT AT THE LABEL LEVEL

§55 found that `mtkKernelsOD_of_debts` cannot serve a cap: its debts run through
`odLt_hEreal`, which produces **"the model relation EQUALS the declared
relation"**, and a cap node has no model realization above the whole closure.

But `MultiTierOk` itself is stated entirely at the **label** level — `∀`
propagation between `tauE`s, `∃` coverage by some node's `tauE`. Soundness
(`multiTier_sound`) builds a model FROM the certificate and never asks where the
labels came from. So a capped certificate can be built directly against
`MultiTierOk`, using model types only as CONSISTENT SETS.

The certificate itself needs no new constructor: it is `mtkKernelsOD` at
`β ⊕ M`, with the base and cap maps combined. -/

/-- The combined witness map: base externals keep their model node, cap nodes
    carry the model node whose TYPE serves as their label. -/
def gCap {β M : Type} {α : Type} (g : β → α) (w : M → α) : β ⊕ M → α
  | .inl b => g b
  | .inr m => w m

/-- The combined budget map. -/
def budCap {β M : Type} (bud : β → Nat) (cbud : M → Nat) : β ⊕ M → Nat
  | .inl b => bud b
  | .inr m => cbud m

/-- **`ee_all` ON THE BASE→CAP EDGE — the §55.3 stabilisation argument.**

    A cap node's label must absorb every `∀PP` obligation of the closure. It
    does, provided the cap's witness sits above a chain node whose `∀PP` content
    is MAXIMAL — which exists because that content is monotone up the chain
    (`sat_all_pp_up`) and lives inside the finite `cl C0`.

    Then: a closure element `e` lies at or below some `c j`; its `∀PP.X` rises to
    `c j`; maximality moves it to `c i₀`; and `c i₀ PP w` delivers `X` at `w`.

    This is the obligation §55 identified as the one that must be discharged at
    the LABEL level rather than through `odLt_hEreal`. -/
theorem cap_ee_all_pp {α : Type} {I : Interp α} (hI : RCC5Interp I)
    {C0 : Concept} {c : Nat → α} (hdom : ∀ i, I.dom (c i))
    {i₀ : Nat} {wm : α} (hwd : I.dom wm) (hrw : I.rho (c i₀) wm = pp)
    (hstab : ∀ (X : Concept) (j : Nat), Concept.all pp X ∈ mty C0 I (c j) →
      Concept.all pp X ∈ mty C0 I (c i₀))
    {e : α} (hed : I.dom e) {j : Nat} (hej : I.rho e (c j) = pp ∨ e = c j)
    {X : Concept} (hX : Concept.all pp X ∈ mty C0 I e) :
    sat I wm X := by
  have h1 : Concept.all pp X ∈ mty C0 I (c j) := by
    rcases hej with hr | rfl
    · exact mem_mty.mpr ⟨(mem_mty.mp hX).1,
        sat_all_pp_up hI hed (hdom j) hr (mem_mty.mp hX).2⟩
    · exact hX
  exact (mem_mty.mp (hstab X j h1)).2 wm hwd hrw

/-- A chain node past the maximum of the `∀PP` content EXISTS: the content is
    monotone going up and lives in the finite `cl C0`, so it stabilises. -/
theorem cap_stab_exists {α : Type} {I : Interp α} (hI : RCC5Interp I)
    (C0 : Concept) {c : Nat → α} (hdom : ∀ i, I.dom (c i))
    (hasc : ∀ i j, i < j → I.rho (c i) (c j) = pp) :
    ∃ i₀, ∀ (X : Concept) (j : Nat), Concept.all pp X ∈ mty C0 I (c j) →
      Concept.all pp X ∈ mty C0 I (c i₀) := by
  obtain ⟨M, hM⟩ := recurrent_tail (typeEnum C0) (fun i => mty C0 I (c i))
    (fun i => mty_mem_typeEnum C0 I (c i))
  refine ⟨M, fun X j hXj => ?_⟩
  rcases Nat.lt_or_ge j M with h | h
  · -- j below M: push X up to a recurrence of M's type above j
    obtain ⟨i, hi, heq⟩ := hM M (Nat.le_refl M) (j + 1)
    have hup : Concept.all pp X ∈ mty C0 I (c i) :=
      mem_mty.mpr ⟨(mem_mty.mp hXj).1, sat_all_pp_up hI (hdom j) (hdom i)
        (hasc j i (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hi))
        (mem_mty.mp hXj).2⟩
    rw [← heq]; exact hup
  · rcases Nat.eq_or_lt_of_le h with heq | hlt
    · rw [heq]; exact hXj
    · -- j above M: M's type recurs above j, and X rises to there
      obtain ⟨i, hi, heq⟩ := hM M (Nat.le_refl M) (j + 1)
      have hup : Concept.all pp X ∈ mty C0 I (c i) :=
        mem_mty.mpr ⟨(mem_mty.mp hXj).1, sat_all_pp_up hI (hdom j) (hdom i)
          (hasc j i (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hi))
          (mem_mty.mp hXj).2⟩
      rw [← heq]; exact hup

/-- Maximal `∀PP` content is preserved going UP the chain, so the stabilisation
    point of `cap_stab_exists` can always be raised — in particular past a
    kernel's phase window. -/
theorem cap_stab_up {α : Type} {I : Interp α} (hI : RCC5Interp I)
    {C0 : Concept} {c : Nat → α} (hdom : ∀ i, I.dom (c i))
    (hasc : ∀ i j, i < j → I.rho (c i) (c j) = pp) {i₀ : Nat}
    (hstab : ∀ (X : Concept) (j : Nat), Concept.all pp X ∈ mty C0 I (c j) →
      Concept.all pp X ∈ mty C0 I (c i₀))
    {i₁ : Nat} (h : i₀ < i₁) :
    ∀ (X : Concept) (j : Nat), Concept.all pp X ∈ mty C0 I (c j) →
      Concept.all pp X ∈ mty C0 I (c i₁) := by
  intro X j hXj
  have h0 := hstab X j hXj
  exact mem_mty.mpr ⟨(mem_mty.mp h0).1, sat_all_pp_up hI (hdom i₀) (hdom i₁)
    (hasc i₀ i₁ h) (mem_mty.mp h0).2⟩

/-- Everything at or below `c i₀` is `PP`-below a witness placed above `c i₀`. -/
theorem cap_reaches {α : Type} {I : Interp α} (hI : RCC5Interp I)
    {c : Nat → α} (hdom : ∀ i, I.dom (c i))
    (hasc : ∀ i j, i < j → I.rho (c i) (c j) = pp)
    {i₀ : Nat} {wm : α} (hwd : I.dom wm) (hrw : I.rho (c i₀) wm = pp)
    {z : α} (hzd : I.dom z) {a : Nat} (ha : a ≤ i₀)
    (hz : I.rho z (c a) = pp ∨ z = c a) : I.rho z wm = pp := by
  have hcw : I.rho (c a) wm = pp := by
    rcases Nat.eq_or_lt_of_le ha with rfl | hlt
    · exact hrw
    · exact pp_witness_below hI (hdom i₀) (hdom a) hwd (hasc a i₀ hlt) hrw
  rcases hz with hr | rfl
  · exact pp_witness_below hI (hdom a) hzd hwd hr hcw
  · exact hcw

/-- **`ee_all` / `ek_all` ON THE CAP→BASE EDGE.**  A cap node's `∀PPI` fires
    downward on the closure — and it is satisfied there, because the closure
    below `c i₀` is entirely `PP`-below the cap's witness.

    A kernel's PHASE WINDOW is finite, so raising `i₀` past it (`cap_stab_up`)
    puts every phase below the witness too. That is why this needs no
    periodicity argument: the phases are a bounded window, not a limit. -/
theorem cap_ee_all_ppi {α : Type} {I : Interp α} (hI : RCC5Interp I)
    {C0 : Concept} {c : Nat → α} (hdom : ∀ i, I.dom (c i))
    (hasc : ∀ i j, i < j → I.rho (c i) (c j) = pp)
    {i₀ : Nat} {wm : α} (hwd : I.dom wm) (hrw : I.rho (c i₀) wm = pp)
    {z : α} (hzd : I.dom z) {a : Nat} (ha : a ≤ i₀)
    (hz : I.rho z (c a) = pp ∨ z = c a)
    {Y : Concept} (hY : Concept.all ppi Y ∈ mty C0 I wm) : sat I z Y := by
  have hzw : I.rho z wm = pp := cap_reaches hI hdom hasc hwd hrw hzd ha hz
  have hwz : I.rho wm z = ppi := by rw [hI.conv_ z wm hzd hwd, hzw]; rfl
  exact (mem_mty.mp hY).2 z hzd hwz

/-! #### §59.2 — cap labels may be SUB-labels

Every `MultiTierOk` obligation has the form *"if `X ∈ tauE e` then …"*, so a
SMALLER label carries FEWER obligations: `e_ex` fires on fewer existentials and
`ee_all` on fewer universals. Consistency is inherited (any subset of a model
type is clash- and bot-free) and the decomposition fields hold as long as the
label is closed under `∧`/`∨`.

The one thing minimality does NOT buy: a label must still absorb everything
propagated INTO it. For a cap that means `D`, the stable `∀PP` consequents from
below, and the `∀PPI` consequents of any higher cap — but crucially NOT the
witness's own `∃DR` demands unless something forces them. That is what makes
§58.2's gap non-generic. -/

/-- A usable label: any decomposition-closed subset of a model type. -/
structure SubLabel {α : Type} (C0 : Concept) (I : Interp α) (x : α)
    (L : List Concept) : Prop where
  sub : ∀ c ∈ L, c ∈ mty C0 I x
  and_cl : ∀ c d, Concept.and c d ∈ L → c ∈ L ∧ d ∈ L
  or_cl : ∀ c d, Concept.or c d ∈ L → c ∈ L ∨ d ∈ L

section SubLabelFacts
variable {α : Type} {C0 : Concept} {I : Interp α} {x : α} {L : List Concept}

/-- The full model type is a `SubLabel`, so the notion is never vacuous and the
    existing construction is the maximal instance. -/
theorem subLabel_mty : SubLabel C0 I x (mty C0 I x) where
  sub := fun _ h => h
  and_cl := fun _ _ h => mty_and h
  or_cl := fun _ _ h => mty_or h

/-- Truncation is a `SubLabel` too — so `mtk` labels are covered. -/
theorem subLabel_mtk (k : Nat) : SubLabel C0 I x (mtk C0 I x k) where
  sub := fun _ h => (mem_mtk.mp h).1
  and_cl := fun _ _ h => mtk_and h
  or_cl := fun _ _ h => mtk_or h

/-- Clash-freeness is INHERITED — nothing to check per label. -/
theorem subLabel_clash (h : SubLabel C0 I x L) (a : Nat)
    (ha : Concept.atom a ∈ L) : Concept.natom a ∉ L :=
  fun h2 => mty_clash (h.sub _ ha) (h.sub _ h2)

/-- As is bot-freeness. -/
theorem subLabel_nobot (h : SubLabel C0 I x L) : Concept.bot ∉ L :=
  fun hb => mty_nobot (h.sub _ hb)

/-- Everything in a `SubLabel` is SATISFIED at the node — which is what lets the
    `∀`-propagation lemmas of §§56–57 fire on sub-labels unchanged. -/
theorem subLabel_sat (h : SubLabel C0 I x L) {c : Concept} (hc : c ∈ L) :
    sat I x c := (mem_mty.mp (h.sub c hc)).2

end SubLabelFacts

/-- **THE CAP LABEL SPEC (membership form).**  Everything a cap's label is
    REQUIRED to contain already lies inside its witness's model type.

    So a valid cap label exists — `mty (w m)` is one — and any
    decomposition-closed set between the required content and that type is
    equally valid, by §59.2. This is what turns "choose a minimal label" from a
    construction problem into a CHOICE inside a known interval. -/
theorem cap_required_in_mty {α : Type} {I : Interp α} (hI : RCC5Interp I)
    {C0 : Concept} {c : Nat → α} (hdom : ∀ i, I.dom (c i))
    {i₀ : Nat} {wm : α} (hwd : I.dom wm) (hrw : I.rho (c i₀) wm = pp)
    (hstab : ∀ (X : Concept) (j : Nat), Concept.all pp X ∈ mty C0 I (c j) →
      Concept.all pp X ∈ mty C0 I (c i₀))
    {e : α} (hed : I.dom e) {j : Nat} (hej : I.rho e (c j) = pp ∨ e = c j)
    {X : Concept} (hX : Concept.all pp X ∈ mty C0 I e) :
    X ∈ mty C0 I wm :=
  mem_mty.mpr ⟨cl_all (mem_mty.mp hX).1,
    cap_ee_all_pp hI hdom hwd hrw hstab hed hej hX⟩

/-- The mirror: a higher cap's `∀PPI` consequents also land inside the type of
    anything the cap reaches. -/
theorem cap_ppi_required_in_mty {α : Type} {I : Interp α} (hI : RCC5Interp I)
    {C0 : Concept} {c : Nat → α} (hdom : ∀ i, I.dom (c i))
    (hasc : ∀ i j, i < j → I.rho (c i) (c j) = pp)
    {i₀ : Nat} {wm : α} (hwd : I.dom wm) (hrw : I.rho (c i₀) wm = pp)
    {z : α} (hzd : I.dom z) {a : Nat} (ha : a ≤ i₀)
    (hz : I.rho z (c a) = pp ∨ z = c a)
    {Y : Concept} (hY : Concept.all ppi Y ∈ mty C0 I wm) :
    Y ∈ mty C0 I z :=
  mem_mty.mpr ⟨cl_all (mem_mty.mp hY).1,
    cap_ee_all_ppi hI hdom hasc hwd hrw hzd ha hz hY⟩

section CappedCert

variable {α : Type} {I : Interp α} {C0 : Concept} {β κ M : Type}

/-- **THE CAPPED CERTIFICATE AGREES WITH THE UNCAPPED ONE ON BASE NODES.**

    Labels are definitionally equal, and the three relation blocks agree by the
    §53 transfer theorem. So every `MultiTierOk` field that mentions only base
    indices is inherited, and only the cap rows need new proofs. -/
theorem capped_tauE_base (O : ODStruct ((β ⊕ M) ⊕ κ))
    (g : β → α) (w : M → α) (bud : β → Nat) (cbud : M → Nat)
    (bk : κ → Nat) (dir : κ → Bool) (ck : κ → Nat → α) (ik pk : κ → Nat)
    (b : β) :
    (mtkKernelsOD I C0 O (gCap g w) (budCap bud cbud) bk dir ck ik pk).tauE
        (Sum.inl b)
      = mtk C0 I (g b) (bud b) := rfl

/-- The cap nodes' labels, by definition. -/
theorem capped_tauE_cap (O : ODStruct ((β ⊕ M) ⊕ κ))
    (g : β → α) (w : M → α) (bud : β → Nat) (cbud : M → Nat)
    (bk : κ → Nat) (dir : κ → Bool) (ck : κ → Nat → α) (ik pk : κ → Nat)
    (m : M) :
    (mtkKernelsOD I C0 O (gCap g w) (budCap bud cbud) bk dir ck ik pk).tauE
        (Sum.inr m)
      = mtk C0 I (w m) (cbud m) := rfl

/-- The kernel phases are untouched by capping. -/
theorem capped_phase (O : ODStruct ((β ⊕ M) ⊕ κ))
    (g : β → α) (w : M → α) (bud : β → Nat) (cbud : M → Nat)
    (bk : κ → Nat) (dir : κ → Bool) (ck : κ → Nat → α) (ik pk : κ → Nat)
    (k : κ) (a : Nat) :
    (mtkKernelsOD I C0 O (gCap g w) (budCap bud cbud) bk dir ck ik pk).phase k a
      = mtk C0 I (ck k (ik k + a)) (bk k) := rfl

end CappedCert

/-! ### §60 — THE FRAGMENT'S DECISION PIPELINE, MODULO ONE NAMED PREMISE

Route 2 of §59.3. The decision pipeline for the ∀PO-free fragment is complete
except for one statement, and it is worth having that statement NAMED in the
artifact rather than described in prose:

* **soundness is unconditional** — `mtAcceptB_sound`: anything the checker
  accepts really is satisfiable, no premise, no hypothesis;
* **the search is finite and fixed** — `codesM C0 …` is an enumeration computed
  from `C₀` alone;
* **the premise** is that a satisfiable ∀PO-free concept has an accepted code in
  that enumeration. That is exactly the general mixed extraction of §§49–59:
  build the capped certificate, reindex onto `Fin`, encode.

Naming it makes the gap machine-checked in shape rather than asserted in prose:
`decidableSat_pofree` typechecks, so nothing else stands between the premise and
a genuine `Decidable (Satisfiable C0)`. -/

/-- **THE ONE REMAINING PREMISE OF THE ∀PO-FREE FRAGMENT.**  Every satisfiable
    concept has an accepted code inside the mixed enumeration at the `mixKT`
    bounds. -/
def MixedCompleteness (C0 : Concept) : Prop :=
  Satisfiable C0 →
    ∃ p ∈ codesM C0 (mixKT C0) (mixKT C0) (mixKT C0),
      (p.1).mtAcceptB p.2 C0 = true

/-- **THE ∀PO-FREE FRAGMENT IS DECIDABLE MODULO `MixedCompleteness`.**

    Soundness comes from `mtAcceptB_sound` and is unconditional; the enumeration
    is fixed and computed from `C₀`. So `MixedCompleteness` is the ONLY open
    item in the pipeline — and it is a statement about the fragment, not about
    this architecture: ANY accepted code in the enumeration discharges it. -/
def decidableSat_pofree (C0 : Concept) (h : MixedCompleteness C0) :
    Decidable (Satisfiable C0) :=
  decidableSat_of_codes C0 _ h

/-- Exhibiting one accepted code discharges the premise — so the premise is a
    statement about EXISTENCE of a certificate, never oracle-inhabitable by a
    `Satisfiable` proof. -/
theorem mixedCompleteness_of_code (C0 : Concept)
    (h : Satisfiable C0 → ∃ p ∈ codesM C0 (mixKT C0) (mixKT C0) (mixKT C0),
      (p.1).mtAcceptB p.2 C0 = true) : MixedCompleteness C0 := h

/-- An unsatisfiable concept discharges it vacuously — a sanity check that the
    definition is not malformed. -/
theorem mixedCompleteness_of_unsat (C0 : Concept) (h : ¬ Satisfiable C0) :
    MixedCompleteness C0 := fun hs => absurd hs h

/-! ### §50 — THE TOP-SERVER EXTENSION

§49 reduced the mixed quadrant to one question: can a ∀PO-free concept force
case 3 (a cofinally recurring one-shot vertical demand with neither chain
recurrence nor a cofinal external)?

The answer developed here is that case 3 is **never a consistency failure, only
a positioning one** — and positioning is repairable by construction.

* `witness_realizes_requirement`: the type a cofinal server needs — the stable
  `∀PP` consequents plus the demanded concept — is realized by the demand's OWN
  witness. Nothing has to be invented.
* `odTop`: that server can be PLACED. Adjoin a new top above a DOWNWARD-CLOSED
  set, disjoint from nothing; the result is still ordered-disjoint, so
  `odNet_frame` returns composition closure for free.

Downward-closedness is not a convenience — `wp102` Q1 measured the naive rule
(above the chain only) breaking on exactly one composition cell,
`comp(PO,PP) = {PO,PP}`, when an off-chain node sits BELOW a chain node; closing
downward repairs it, and the repaired rule placed the server in 3121 of 3121
random ordered-disjoint structures.

The new top is `PO` to everything outside the closure, and **`∀PO`-freeness is
exactly what makes that free**: a `PO` edge to the new node carries no universal
obligation, so nothing outside the closure constrains the server. -/

section TopServer

variable {N : Type}

/-- `Option.noConfusion` will not elaborate against a bare `False` goal in this
    Lean version, so the two constructor-clash facts get names. -/
theorem none_ne_some' {M : Type} {a : M} (h : (none : Option M) = some a) :
    False := by cases h

theorem some_ne_none' {M : Type} {a : M} (h : (some a : Option M) = none) :
    False := by cases h

/-- The extension's order: everything in the downward-closed set `U` sits below
    the new top; the new top is below nothing. -/
def topLt (S : ODStruct N) (U : N → Prop) : Option N → Option N → Prop
  | some x, some y => S.lt x y
  | some x, none => U x
  | none, _ => False

/-- The extension's disjointness: unchanged, with the new top disjoint from
    nothing — which is what lets `djDown` survive the extension. -/
def topDisj (S : ODStruct N) : Option N → Option N → Prop
  | some x, some y => S.disj x y
  | _, _ => False

/-- **THE TOP-SERVER EXTENSION.**  Adjoining a top above a downward-closed set
    keeps the structure ordered-disjoint — hence, by `odNet_frame`, keeps the
    induced net composition-closed.  No composition checking is needed: being an
    `ODStruct` is the whole obligation. -/
def odTop (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) : ODStruct (Option N) where
  lt := topLt S U
  disj := topDisj S
  ltIrr := by
    intro x
    cases x with
    | none => exact fun h => h
    | some a => exact S.ltIrr a
  ltTr := by
    intro x y z hxy hyz
    cases x with
    | none => exact hxy.elim
    | some a =>
      cases y with
      | none => exact hyz.elim
      | some b =>
        cases z with
        | none => exact hdown a b hxy hyz
        | some c => exact S.ltTr a b c hxy hyz
  djSym := by
    intro x y h
    cases x with
    | none => exact h.elim
    | some a =>
      cases y with
      | none => exact h.elim
      | some b => exact S.djSym a b h
  djIrr := by
    intro x
    cases x with
    | none => exact fun h => h
    | some a => exact S.djIrr a
  ltNotDj := by
    intro x y hlt
    cases x with
    | none => exact hlt.elim
    | some a =>
      cases y with
      | none => exact fun h => h
      | some b => exact S.ltNotDj a b hlt
  djDown := by
    intro x y x' y' hd hx hy
    cases x with
    | none => exact hd.elim
    | some a =>
      cases y with
      | none => exact hd.elim
      | some b =>
        cases x' with
        | none =>
          rcases hx with h | h
          · exact (none_ne_some' h).elim
          · exact h.elim
        | some a' =>
          cases y' with
          | none =>
            rcases hy with h | h
            · exact (none_ne_some' h).elim
            · exact h.elim
          | some b' =>
            refine S.djDown a b a' b' hd ?_ ?_
            · rcases hx with h | h
              · exact Or.inl (Option.some.inj h)
              · exact Or.inr h
            · rcases hy with h | h
              · exact Or.inl (Option.some.inj h)
              · exact Or.inr h

/-- The server really is above everything in the closure. -/
theorem odTop_above (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) {x : N} (hU : U x) :
    odNet (odTop S U hdown) (some x) none = pp :=
  odNet_lt _ hU

/-- And `PO` — hence UNCONSTRAINED in this fragment — to everything else. -/
theorem odTop_po (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) {x : N} (hU : ¬ U x) :
    odNet (odTop S U hdown) (some x) none = po :=
  odNet_po _ (fun h => some_ne_none' h) hU (fun h => h) (fun h => h)

/-- The payoff: the extended structure induces a genuine RCC5 frame, with no
    composition obligation discharged by hand. -/
theorem odTop_frame (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) :
    Frame (odNet (odTop S U hdown)) := odNet_frame _


/-- **THE OBLIGATION OF §50.3 IS EXACTLY `∀PPI`, AND NOTHING ELSE.**

    Every edge OUT of the new top is `PPI` (into the closure) or `PO` (outside
    it). So of the universals a label can carry, only `∀PPI` and `∀PO` can fire
    from the top — and `∀PO` is absent by hypothesis in this fragment. `∀PP`
    fires vacuously (nothing is above the top) and `∀DR` fires vacuously (the
    top is disjoint from nothing, by `odTop`'s construction).

    This bounds §50.3's remaining work to a single universal. -/
theorem odTop_out (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) (x : N) :
    odNet (odTop S U hdown) none (some x) = ppi ∨
    odNet (odTop S U hdown) none (some x) = po := by
  by_cases h : U x
  · exact Or.inl (odNet_gt _ (show (odTop S U hdown).lt (some x) none from h))
  · refine Or.inr (odNet_po _ (fun hh => (none_ne_some' hh).elim)
      (fun hh => hh) h (fun hh => hh))

/-- The top is disjoint from nothing — so `∀DR` at the top fires vacuously. -/
theorem odTop_no_dr (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) (x : Option N) :
    ¬ (odTop S U hdown).disj none x := fun h => h

/-- Nothing is above the top — so `∀PP` at the top fires vacuously. -/
theorem odTop_nothing_above (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) (x : Option N) :
    ¬ (odTop S U hdown).lt none x := fun h => h


/-- **§50.3 DISSOLVES ON THE MODEL-EXTENSION ROUTE.**

    §50.3 flagged an obligation: the top's label may carry `∀PPI.Y`, which then
    fires downward on the whole closure. That is a real obligation if the label
    is COPIED from the witness `w` — `w` guarantees `Y` only below itself.

    It disappears if the top's label is its own model type in the EXTENDED
    model, because `∀PPI.Y ∈ mty T` then says exactly that `Y` holds at
    everything below `T`. The clause and the obligation are the same statement.

    So the residue of §50 is not the universal at all; it is that the extension
    must place a region satisfying `D` together with the `∀PP` consequents —
    which `witness_realizes_requirement` shows is a type the model already
    realizes. -/
theorem top_all_ppi_automatic {T : α} {Y : Concept}
    (h : sat I T (Concept.all ppi Y)) {z : α} (hz : I.dom z)
    (hr : I.rho T z = ppi) : sat I z Y := h z hz hr


/-! ### §51 — CAPPING WITH A TOWER

`odTop` adjoins ONE node above the closure. That is not enough in general: the
new node's own label may contain `∃PP.Z` (the demanded `D` can itself be an
`∃PP`), and nothing sits above a single top, so such a demand could never be
served. The cap must therefore be an ASCENDING TOWER, which is also what lets a
single cap serve several CONFLICTING demands round-robin — the certified
`rr_covers` pattern from the vertical quadrant.

`odTower` is `odTop` with `Nat` many tops instead of one. The proof obligations
are the same shape; the only new case is transitivity inside the tower, which is
`Nat.lt_trans`. -/

/-- **WHY THE CAP CARRIES NO DISJOINTNESS — forced, not chosen.**  Two cap
    nodes both sit above the whole closure `U`, so `djDown` would push their
    disjointness down onto `U`'s elements and make them disjoint from
    themselves. So a cap is always a POSET-shaped structure: `PP`/`PPI`/`PO`/`EQ`
    only. A cap node's `∃DR` demand must therefore be served from the BASE, by a
    node disjoint from the entire closure — and `cofinal_dr_all` (already
    certified) supplies exactly that: a cofinally-`DR` external is `DR` to the
    whole chain, with no middle case, the mirror of
    `above_cofinal_is_above_all`. -/
def amLt (S : ODStruct N) (U : N → Prop) {M : Type} (P : M → M → Prop) :
    N ⊕ M → N ⊕ M → Prop
  | .inl x, .inl y => S.lt x y
  | .inl x, .inr _ => U x
  | .inr a, .inr b => P a b
  | .inr _, .inl _ => False

/-- Disjointness is untouched, and the cap is disjoint from nothing. -/
def amDisj (S : ODStruct N) {M : Type} : N ⊕ M → N ⊕ M → Prop
  | .inl x, .inl y => S.disj x y
  | _, _ => False

/-- **THE CAP AMALGAMATION (§51).**  Adjoin ANY strict order `P` above a
    downward-closed set. The result is ordered-disjoint, so `odNet_frame`
    supplies composition closure with nothing checked by hand.

    `odTop` (one node) and `odTower` (an ascending chain) are both instances. -/
def odAmalg (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) {M : Type} (P : M → M → Prop)
    (hPirr : ∀ a, ¬ P a a) (hPtr : ∀ a b c, P a b → P b c → P a c) :
    ODStruct (N ⊕ M) where
  lt := amLt S U P
  disj := amDisj S
  ltIrr := by
    intro x
    cases x with
    | inl a => exact S.ltIrr a
    | inr a => exact hPirr a
  ltTr := by
    intro x y z hxy hyz
    cases x with
    | inr k =>
      cases y with
      | inl _ => exact hxy.elim
      | inr j =>
        cases z with
        | inl _ => exact hyz.elim
        | inr m => exact hPtr k j m hxy hyz
    | inl a =>
      cases y with
      | inl b =>
        cases z with
        | inl c => exact S.ltTr a b c hxy hyz
        | inr _ => exact hdown a b hxy hyz
      | inr j =>
        cases z with
        | inl _ => exact hyz.elim
        | inr _ => exact hxy
  djSym := by
    intro x y h
    cases x with
    | inr _ => exact h.elim
    | inl a =>
      cases y with
      | inr _ => exact h.elim
      | inl b => exact S.djSym a b h
  djIrr := by
    intro x
    cases x with
    | inr _ => exact fun h => h
    | inl a => exact S.djIrr a
  ltNotDj := by
    intro x y hlt
    cases x with
    | inr _ => exact fun h => h
    | inl a =>
      cases y with
      | inr _ => exact fun h => h
      | inl b => exact S.ltNotDj a b hlt
  djDown := by
    intro x y x' y' hd hx hy
    cases x with
    | inr _ => exact hd.elim
    | inl a =>
      cases y with
      | inr _ => exact hd.elim
      | inl b =>
        cases x' with
        | inr _ =>
          rcases hx with h | h
          · exact (inr_ne_inl _ _ h).elim
          · exact h.elim
        | inl a' =>
          cases y' with
          | inr _ =>
            rcases hy with h | h
            · exact (inr_ne_inl _ _ h).elim
            · exact h.elim
          | inl b' =>
            refine S.djDown a b a' b' hd ?_ ?_
            · rcases hx with h | h
              · exact Or.inl (Sum.inl.inj h)
              · exact Or.inr h
            · rcases hy with h | h
              · exact Or.inl (Sum.inl.inj h)
              · exact Or.inr h

/-- The general payoff: any cap amalgamated above a downward-closed set induces
    a genuine RCC5 frame. -/
theorem odAmalg_frame (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) {M : Type} (P : M → M → Prop)
    (hPirr : ∀ a, ¬ P a a) (hPtr : ∀ a b c, P a b → P b c → P a c) :
    Frame (odNet (odAmalg S U hdown P hPirr hPtr)) := odNet_frame _

/-- The cap sits above the whole closure, at every one of its nodes. -/
theorem odAmalg_above (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) {M : Type} (P : M → M → Prop)
    (hPirr : ∀ a, ¬ P a a) (hPtr : ∀ a b c, P a b → P b c → P a c)
    {x : N} (hU : U x) (a : M) :
    odNet (odAmalg S U hdown P hPirr hPtr) (.inl x) (.inr a) = pp :=
  odNet_lt _ hU

/-- And is `PO` — unconstrained in this fragment — to everything outside it. -/
theorem odAmalg_po (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) {M : Type} (P : M → M → Prop)
    (hPirr : ∀ a, ¬ P a a) (hPtr : ∀ a b c, P a b → P b c → P a c)
    {x : N} (hU : ¬ U x) (a : M) :
    odNet (odAmalg S U hdown P hPirr hPtr) (.inl x) (.inr a) = po :=
  odNet_po _ (fun h => (inr_ne_inl _ _ h.symm).elim) hU (fun h => h) (fun h => h)

/-- **THE FAN CAP — an ANTICHAIN of servers.**  `odAmalg` at the EMPTY order.

    §51 introduced the tower for two reasons: (a) the cap's own `∃PP` demands
    need something above them, and (b) several CONFLICTING demands need several
    servers. Reason (b) dissolves here: two cap nodes with no order between them
    are `PO`, and **`∀PO` is absent from this fragment**, so neither constrains
    the other at all. Conflicting demands can simply be served by an antichain —
    no ordering decision, no propagation between servers.

    Only reason (a) still calls for the tower. -/
def odFan (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) (M : Type) : ODStruct (N ⊕ M) :=
  odAmalg S U hdown (fun (_ _ : M) => False) (fun _ h => h)
    (fun _ _ _ h _ => h.elim)

/-- Distinct servers in a fan are `PO` — hence mutually unconstrained. -/
theorem odFan_po (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) (M : Type) {a b : M} (hab : a ≠ b) :
    odNet (odFan S U hdown M) (.inr a) (.inr b) = po :=
  odNet_po _ (fun h => hab (Sum.inr.inj h)) (fun h => h) (fun h => h)
    (fun h => h)

/-- Every server of a fan sits above the whole closure. -/
theorem odFan_above (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) (M : Type) {x : N} (hU : U x) (a : M) :
    odNet (odFan S U hdown M) (.inl x) (.inr a) = pp :=
  odNet_lt _ hU

/-- And the fan induces a genuine RCC5 frame. -/
theorem odFan_frame (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) (M : Type) :
    Frame (odNet (odFan S U hdown M)) := odNet_frame _

/-- The ascending-tower cap: `odAmalg` at `(Nat, <)`. -/
def odTower (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) : ODStruct (N ⊕ Nat) :=
  odAmalg S U hdown (fun k j => k < j) Nat.lt_irrefl
    (fun _ _ _ h1 h2 => Nat.lt_trans h1 h2)

/-- The cap really ascends: every level is `PP`-below every higher one, so the
    tower can serve its own `∃PP` demands — the thing a single top cannot do. -/
theorem odTower_asc (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) {k j : Nat} (h : k < j) :
    odNet (odTower S U hdown) (.inr k) (.inr j) = pp :=
  odNet_lt _ h

/-- And it sits above the whole closure. -/
theorem odTower_above (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) {x : N} (hU : U x) (k : Nat) :
    odNet (odTower S U hdown) (.inl x) (.inr k) = pp :=
  odNet_lt _ hU

/-- `PO` — hence unconstrained in this fragment — to everything outside. -/
theorem odTower_po (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) {x : N} (hU : ¬ U x) (k : Nat) :
    odNet (odTower S U hdown) (.inl x) (.inr k) = po :=
  odNet_po _ (fun h => (inr_ne_inl _ _ h.symm).elim) hU (fun h => h) (fun h => h)

/-- The payoff, again with no composition discharged by hand. -/
theorem odTower_frame (S : ODStruct N) (U : N → Prop)
    (hdown : ∀ x y, S.lt x y → U y → U x) :
    Frame (odNet (odTower S U hdown)) := odNet_frame _

end TopServer

end OneShotDichotomy

#print axioms pp_witness_below
#print axioms ex_pp_serves_below
#print axioms oneshot_one_witness
#print axioms oneshot_in_kernel
#print axioms above_cofinal_is_above_all
#print axioms witness_bounded_or_all
#print axioms cofinal_witness_serves_all
#print axioms finite_pool_gives_cofinal_witness
#print axioms finite_pool_serves_kernel
#print axioms finite_pool_all_or_nothing
#print axioms witness_realizes_requirement
#print axioms cap_all_ppi_sound
#print axioms decidableSat_pofree
#print axioms mixedCompleteness_of_code
#print axioms mixedCompleteness_of_unsat
#print axioms cap_required_in_mty
#print axioms cap_ppi_required_in_mty
#print axioms subLabel_mty
#print axioms subLabel_mtk
#print axioms subLabel_clash
#print axioms subLabel_nobot
#print axioms subLabel_sat
#print axioms cap_ee_all_pp
#print axioms cap_stab_up
#print axioms cap_reaches
#print axioms cap_ee_all_ppi
#print axioms cap_stab_exists
#print axioms capped_tauE_base
#print axioms capped_tauE_cap
#print axioms capped_phase
#print axioms capMixLt_old
#print axioms capMixLe_to_old
#print axioms capElt_irr
#print axioms capElt_trans
#print axioms capElt_ud
#print axioms capSeed_sym
#print axioms embC_inj
#print axioms capMixLe_old_old
#print axioms capSeed_sep
#print axioms capMixLe_of_old
#print axioms capSeed_old
#print axioms odSeedCap
#print axioms odSeedCap_old
#print axioms odSeedCap_frame
#print axioms cap_not_disj
#print axioms cap_above_U
#print axioms cap_po_outside
#print axioms cap_above_kernel
#print axioms cap_pp_cap
#print axioms cap_po_cap
#print axioms cap_no_dr_edge
#print axioms cap_no_dr_edge'
#print axioms layer_cut
#print axioms layer_recursion_terminates
#print axioms layer_stack_bounded
#print axioms cap_all_ppi_sound_chain
#print axioms odTop
#print axioms odTop_above
#print axioms odTop_po
#print axioms odTop_frame
#print axioms odTop_out
#print axioms odTop_no_dr
#print axioms odTop_nothing_above
#print axioms top_all_ppi_automatic
#print axioms odAmalg
#print axioms odAmalg_frame
#print axioms odAmalg_above
#print axioms odAmalg_po
#print axioms odFan
#print axioms odFan_po
#print axioms odFan_above
#print axioms odFan_frame
#print axioms odTower
#print axioms odTower_asc
#print axioms odTower_above
#print axioms odTower_po
#print axioms odTower_frame

end POFreeLift
