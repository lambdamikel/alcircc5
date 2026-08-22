# The ∀PO-free assembly recursion — design sketch

*2026-07-23. A design note for the final construction of the ∀PO-free
fragment certification campaign (`formal/POFreeLift.lean`, rounds
A–E3g′). Not a proof; a map from the certified infrastructure to the
remaining `Decidable (Satisfiable C₀)` theorem, with the hard cases
located and their resolutions identified. Prose only — no Lean written
under-designed (the round-19/20 lesson).*

> ## ⚠ CURRENT ROUTE — read this before anything else
>
> **The live route is the HYBRID certificate `mtkKernelsOD` (§43).**
> `mtk` labels read off a model, over a DECLARED **ordered-disjoint** frame on
> `β ⊕ κ` built by `odMix`: externals pairwise `lt`-incomparable (so their block
> is the PO-default frame), each kernel entirely above or entirely below its
> externals, disjointness the downward closure of the externals' `DR` pattern.
> `frame_q` is free (`frame_q_of_odNet`).
>
> **Why not the read-off frame `mixKernels`/`mixKernelsK` (§42's route):**
> `wp96` A. With `E e f = I.rho (g e) (g f)` every external pair carries a real
> relation, so `ee_all` fires on ALL of them — while the node set that makes the
> certificate finite (`mtkNodes`) drops the budget at every step. A universal of
> depth `bud e - 1` then has to land in a label truncated below it. Measured
> break: **4.1%** of satisfiable ∀PO-free instances. Read-off is EXPRESSIVE (§42
> was right about that) but forces UNIFORM budgets, and uniform budgets forfeit
> the budget-decreasing finiteness the whole `codes` pipeline consumes.
>
> **Why not a PO DEFAULT either:** `wp96` C, `wp97` B/C. One external carrying
> both an `∃PP` and an `∃PPI` demand needs a kernel above and one below, and
> `comp(PP,PP) = {PP}` forces the two bases comparable; kernels under `DR`
> externals inherit disjointness by `djDown`. A PO-defaulted kernel block is
> composition-violating.
>
> **So `odNet_frame` IS on the critical path** — §42.2 said it was not, which
> was wrong. §41's ordered-disjoint work was right; §42's correction of it
> overshot. §42 remains correct that read-off EXPRESSES everything; what it
> missed is that read-off cannot be USED, for budget reasons.
>
> Before designing anything, consult **`CERTIFIED_INVENTORY.md`**. This session
> re-derived or mis-assessed existing machinery three times (§40's two
> architectures, §41.8's step-5 pipeline, and the §42 detour); the inventory
> exists to stop that.

---

## 0. The target

The decision reduction is already certified:

> **`decidableSat_of_codes`** — for a fixed candidate list
> `codes : List (FinMT × Nat)`, the premise
> `Satisfiable C₀ → (some code in codes is accepted)` yields
> `Decidable (Satisfiable C₀)`.

So the whole remaining problem is that ONE premise, for the ∀PO-free
fragment. It splits into:

- **D2d-enum** — a *computable* enumeration `codes` of candidate
  `FinMT` codes, with every dimension bounded by a computable function
  `K(C₀)` of `|cl C₀|` (finiteness/decidability of the search).
- **D2d-complete** — the **extraction**: `Satisfiable C₀` (with
  `POFree C₀`) ⟹ some enumerated code is accepted. This is the
  assembly recursion. It is the only genuinely-large piece left.

The extraction produces a valid FINITE certificate from a model and
then observes it is (equivalent to) one of the enumerated codes. The
soundness half (`multiTier_sound`, `finAccept_sound`, `mtAcceptB_sound`)
and the checker-completeness half (`mtOkB_iff`, `mtAcceptB_complete`,
`glueFam_ok`, `multi_kernel_block`) are done; extraction is the bridge.

---

## 1. Two layers: horizontal is finite, vertical is kernels

The single organizing idea. Split every demand by its relation:

- **Vertical demands** (`∃PP`, `∃PPI`) can *recur forever*
  (`∀PP.(∃PP.⊤)` reproduces `∃PP.⊤` at every rung). They are NOT
  unravelled; they are absorbed into **kernels** — a kernel is one
  quotient node standing for an entire infinite `PP`- or `PPI`-chain,
  with a finite *period* of phase-types. Certified: `persistPP`/
  `persistPPI` produce the chains (E3g/E3g′); `kernel_site`/
  `dkernel_site` select a type-recurrent, externally-stabilized
  segment (E2b); `mkBlock`/`multi_kernel_block` turn a family of
  kernels + externals into a valid block (E3d).

- **Horizontal demands** (`∃PO`, `∃DR`) *strictly shrink the
  requirement*: nothing propagates across `PO` (no `∀PO` in the
  fragment — `mty_no_all_po`/`pofree_cl_all`), and a `DR` step passes
  only strict subformulas. So the horizontal unravelling is
  well-founded and finite.

The forest structure that carries both:

```
   library pool  ──(∃PO, tag-decreasing)──►  library blocks
        ▲
        │ pending ∃PO
   glueFam family of BLOCKS  ──(cross-block = loose PO)──►  each other
        │
   one BLOCK = mkBlock over (externals β) ⊕ (kernels κ)
        ├── kernels: infinite PP/PPI chains (vertical demand)
        └── externals: single nodes (DR-witnesses, finite ladders,
                        PO-witness roots), each either a leaf or the
                        root of a child block
```

Top level = a `glueFam` family (E1) with cross-block edges loose `PO`
and a tagged `∃PO` pool. One block = a `mkBlock` (E3d). The recursion
builds the family.

---

## 2. Requirement types, and why not model types

A certificate node is labelled by a **requirement type**: the set of
formulas that MUST hold there, generated top-down, NOT the full model
type. Generation rules (each guided by a model element `m` with
`t ⊆ mty C₀ I m`, so choices are always model-realizable ⟹ clash-free):

- **root** requires `C₀`;
- **∧**: `c ⊓ d ∈ t` ⟹ add `c`, `d`;
- **∨**: `c ⊔ d ∈ t` ⟹ add whichever of `c`, `d` the guiding `m`
  satisfies (`mty_or`);
- **∀-fire**: `∀r.c ∈ t` and a declared edge `→r v` ⟹ add `c` at `v`;
- **∃-spawn**: `∃r.c ∈ t` ⟹ create/route an `r`-neighbour requiring
  `c`, guided by a model witness (`mty_ex`).

Requirement types live in the finite universe `sublists (cl C₀)`
(`mty_mem_sublists`), so there are `≤ 2^|cl C₀|` of them.

**Why requirement- not model-typing is load-bearing (twice):**

1. **The pool closes.** A `∃PO.D` library rooted at a *model* type
   could re-demand `∃PO.D` itself (a point satisfying `D` may also
   satisfy `∃PO.D`). A *requirement*-typed library for `D` requires
   only strict subformulas of `D`, so it can only demand *smaller*
   libraries. With the tag-inequality of `MTOkPool` (a pending `∃PO.D`
   is served by a pool entry with a DIFFERENT tag) the pool is
   well-founded. `glueFam_ok`'s `hreal` premise is then dischargeable.

2. **`K(C₀)` is a function of `|cl C₀|`.** Model types could in
   principle proliferate; requirement types are subsets of `cl C₀`,
   giving the clean double-exponential bound (matching the two-tier
   paper's 2-EXPTIME).

---

## 3. The recursion, by rank

`extract(t, m)` — `t` a requirement type, `m` a guiding model element,
`t ⊆ mty C₀ I m` — returns a block (or routes into an existing one),
discharging every demand of `t`:

- **propositional** `∧`/`∨`: resolve within `t` (model-guided), no new
  node.
- **`∃EQ.c`**: fulfil in place (`seg_ex_eq` — the EQ-witness is `m`
  itself under strong-EQ). No new node.
- **`∃PP.c` / `∃PPI.c` persistent** (guard `∀PP.(∃PP.c)` present):
  this is a KERNEL. `m` is `persistPP`/`persistPPI`; build its chain
  (E3g/E3g′) and segment (E2b); the kernel's phases are the segment
  types; the vertical demand is discharged chain-internally
  (`k_ex` branch `r = cdir (up k)`). NO recursion — the segment
  captures the whole infinite chain.
- **`∃PP.c` / `∃PPI.c` NON-persistent** (finite ladder): a bounded
  chain of external nodes ending in a leaf; each rung a horizontal-rank
  step (see termination). Finitely many.
- **`∃DR.c`**: a designated DR-witness external `w` (`hserve`/
  `kernel_site` gives `w` with `c ∈ mty(w)` and constant `DR` row to
  the whole segment via `backward_forcing_dr`). `w` is a SINGLE
  external node; `k_ex` external branch fulfils it. `w`'s OWN demands
  become `w`'s `e_ex` residual — `extract(req(c), w)` recursively.
- **`∃PO.c`**: pend against the pool (`MTOkPool` `k_ex`/`e_ex` `r = po`
  branch). A library block for `c` lives in the pool (built by the
  same recursion, one tag lower).

**Discharging the `e_ex` residual.** `BlockOk` (E3a/E3d) leaves exactly
the externals' own fulfilment `e_ex` open; `mtOkPool_of_block` restores
full validity once supplied. The recursion supplies it: an external
`w`'s demands are demands of the *model type* `mty(w)` (`mty_ex`/
`mty_all`), so each routes to another external (finite, terminating),
a kernel (`w` sits `PP`/`PPI`-below a kernel — `e_ex` branch
`conv(K k w) = r`), or the pool (`∃PO`). This is the recursion's
central obligation and its only real proof engineering.

---

## 4. Termination

A single well-founded measure closes it: **`rank(t)` = the multiset of
`t`'s formulas under the strict-subformula order** (equivalently: the
horizontal modal budget).

- `∧`/`∨` steps: same node, strictly fewer/smaller formulas.
- `∃PO` step: child requires subformulas of `c` only (no `∀PO`
  crosses) — strictly below the parent, which held `∃PO.c`.
- `∃DR` step: child requires `c` plus `{E : ∀DR.E ∈ parent}`, all
  strict subformulas — strictly below. (`∀DR` fires at most once per
  edge and does not compose transitively — `DR` is not transitive —
  so it cannot regenerate itself. The "`∀DR` flips once to `∀PPI`"
  fact, wp49: past one `DR` step the residual universals only feed
  vertical structure, absorbed by kernels.)
- `∃PP`/`∃PPI` steps: do NOT decrease `rank` — but they are absorbed
  by kernels (no recursion) or are finite ladders. Vertical recursion
  never spawns a new *horizontal* recursion at the same rank.

So horizontal recursion is well-founded on `rank`; vertical recursion
is captured by kernels; the two do not interleave upward. Finitely
many nodes total.

---

## 5. The tight skeleton, and why the rectangle problem is gone

The block's frame is the **two-sorted labelling** (E3c): declare a
value TIGHT (read off the model) only on the **ordered-disjoint
skeleton** — `PP` a strict order, `DR` downward-closed along `PP`
(E3b's `ordered_disjoint_frame`, the wp47 converse) — and **loose `PO`
everywhere else**. `multi_kernel_block` (E3d) proves this is a valid
`BlockOk` given:

- **closure** of the tight skeleton (`htpp`/`htdr`): certified for the
  maximal predicate `≠ PO` (E3e, `tightNePo_*`), purely from
  `comp(pp,pp)={pp}` and `comp(pp,dr)={dr}` — the assembly's
  sub-predicate reuses the same two facts;
- **rectangle constancy** (`hrectK`/`hrectQ`) of the TIGHT cross
  values only.

**Key design decision — declare only FORCED edges tight; everything
else loose `PO`.** Then:

- Forced tight edges are automatically rectangle-constant: they hold
  through singleton composition cells (`k1 DR w`, `w PPI w'` ⟹
  `k1 DR w'` via `comp(dr,ppi)={dr}`; `w PP w'`, `w' PP w''` ⟹
  `w PP w''` via `comp(pp,pp)={pp}`). Constancy comes free from the
  singleton cell, exactly the E3b/E3e observation.
- Non-forced cross edges are loose `PO`. **Sound**, because (i) `PO`
  fires no obligation in the fragment (`mty_no_all_po`), and (ii) the
  certificate need only unfold to SOME model of `C₀` — declaring `PO`
  where the model had `DR`/`PP` yields a *different* valid model, with
  demands still met by their designated witnesses, not by cross edges.

This **dissolves the rectangle problem** and — crucially — **avoids
joint (mutual) stabilization of several chains**, which would have been
the one genuinely new piece of hard mathematics. The `∃DR`-witness that
itself carries an ascending vertical demand (the case that looked like
it needed a non-forced tight `DR` between two kernels) is handled
instead by: a single DR-witness external at the base (tight, forced-
constant against `k1`'s own chain), whose ascending demand is fulfilled
by being `PP`-below its own kernel (forced-constant `PPI` row), with the
`k1`→that-kernel cross edge left LOOSE `PO`. No mutual stabilization
needed.

Residual care (not a new obstacle, just proof work): confirm the
recursion never *needs* a tight non-forced edge — i.e. every `∃DR`/`∃PP`
witness is served by a designated single-edge witness or a
composition-forced edge, never by a bare kernel-kernel relation the
model happens to carry. The `k_ex`/`e_ex` branch structure (§0's
readout) already only ever asks for `K`/`Q` values we control.

---

## 6. `K(C₀)` and the FinMT encoding (D2d)

Counting, all as functions of `n = |cl C₀|`:

- requirement types: `≤ 2^n`; kernels: `≤ 2^n · n` (one per
  (type, vertical-demand)); externals per phase: `≤ n` (one per
  demand); phase period: `≤ 2^n` (distinct segment types);
  library blocks: `≤ n` (one per `∃PO`-subformula); horizontal depth:
  `≤ n`.

Product ⟹ a computable `K(C₀)`. Then:

- **D2d-enum** — enumerate all `FinMT` codes within these dimensions
  (a finite `List (FinMT × Nat)`), computable from `C₀`.
- **D2d-complete** — the extraction of §§1–5 lands inside the
  enumeration (its dimensions are `≤ K(C₀)`), and its validity
  (`glueFam_ok` + pool realization ⟹ `MultiTierOk`; encode via the
  `FinMT` bridge `decodeB`/`mtOkB_iff`/`mtAcceptB_complete`) ⟹ the
  code is accepted. Feeds `decidableSat_of_codes`.

---

## 7. What each certified round discharges

| Need | Certified by |
|---|---|
| kernels exist from demand | `persistPP(_chain)`, `persistPPI(_chain)` (E3g/g′) |
| segment: type-recurrent + externally stabilized | `kernel_site`/`dkernel_site` (E2b) |
| block frame valid (tight + loose PO) | `ordered_disjoint_frame`, `twoSorted_frame` (E3b/c) |
| block validity for a kernel family | `multi_kernel_block`, `mkBlock` (E3d) |
| tight-skeleton closure | `tightNePo_symm/htpp/htdr` (E3e) |
| block fires from a real chain | `multiBlock_of_site/_of_chain` (E3f) |
| demand→kernel→certificate | `block_of_persistent` (E3g) |
| glue blocks, `∃PO` pool | `glueFam_ok`, `MTOkPool` (E0/E1) |
| soundness of the whole | `multiTier_sound`, `finAccept_sound` (A–C) |
| checker completeness | `mtOkB_iff`, `mtAcceptB_complete` (D1) |
| decision reduction | `decidableSat_of_codes` (D1) |
| no `∀PO` obligations | `mty_no_all_po`, `pofree_cl_all` (D2c) |

## 8. What is NOT yet certified (the remaining rounds)

1. **`dmultiBlock_of_site/_of_chain`** — the descending mirror of E3f
   (mechanical; needed so descending kernels enter blocks).
2. **Requirement types as a Lean object** + the generation rules +
   their landing in `cl C₀` (finite).
3. **The recursion** discharging `e_ex` — the central proof: define
   the block family from a model by rank recursion, prove every
   external/kernel demand routed (external / kernel / pool), guided by
   the model so clash-free. Termination on `rank` (§4).
4. **The loose-PO frame instance** — supply `hrectK`/`hrectQ` for the
   forced tight edges (composition-forced constancy, §5), loose PO
   elsewhere; the sub-predicate's closure via E3e's two facts.
5. **`K(C₀)` counting + FinMT enumeration** (D2d) and the final
   `Decidable (Satisfiable C₀)` for `POFree C₀`.

The order to attempt: 1 (quick mirror) → 2 → 4 (the concrete frame
instance, reusing E3e) → 3 (the recursion, the big one) → 5. The only
step with genuine mathematical risk is 3's termination/coverage
bookkeeping; the design above removes the two things that looked like
new hard mathematics (mutual stabilization, the rectangle problem for
DR-witnesses) by the loose-PO default. Everything else is proof
engineering on certified lemmas.

**Honest caveat.** This is a design, not a theorem. The project ledger
(17 reviews, a defect in all but two) says: presume step 3 hides a
snag the sketch missed — most likely in the `e_ex` coverage argument
(is EVERY demand of EVERY generated node really routed, with no node
left with an unfulfilled `∃`?), the analogue of the Coverage Lemma the
no-automata thread kept re-opening. Build it slowly, model-guided,
with the checker (`mtAcceptB`) as an executable oracle on witnesses at
each step.

---

## 9. Postscript (2026-07-24): what was built, and the lift analysis

The horizontal recursion of §§3–4 is now **built and certified**
(`rnodes` + `rnodes_covers`, round E3k) and the §8 "designated risk"
— coverage — is a kernel-checked theorem. On top of it the **∀-free
fragment** was closed end to end: `satisfiable_iff_allfree_cert`
(soundness ⟺ extraction). Honest caveats: (a) it is a *certificate
characterization*, not a certified finite-model property (β quantified
as an arbitrary `Type`, no `Fintype`); (b) `AllFree ⊊ POFree` — ∀-free
is a *proper* sub-fragment (bans **all** universals), tractable only
because every `∀`-condition is then vacuous.

**The lift to the real ∀PO-free target — the precise obstacle.** The
merged read-off frame that worked for ∀-free fails once universals
appear, and the tree-structural frame (round E3l, `symDrPo_frame`,
frame side done) exposes the true crux: **reverse `∀`-firing**.

A demand edge `m →r m'` is created with the *forward* `∀r`-consequences
threaded into the child (`childSeed = c :: fire(label m, r)`, so
`∀r.c' ∈ label m ⟹ c' ∈ label m'`). But an RCC5 frame edge is
converse-coherent, so the edge also carries `conv r` the other way, and
`ee_all` then demands the *reverse*: `∀(conv r).c'' ∈ label m' ⟹ c'' ∈
label m`. The recursion never put `m'`'s `∀`-consequences into its
**parent** `m`.

- For `r = PO`: `conv PO = PO`, and the fragment is ∀PO-free, so the
  reverse fires nothing. **Fine.**
- For `r = PP`/`PPI`: the reverse is `∀PPI`/`∀PP` back up/down the
  vertical chain — this is exactly what the **kernel** machinery
  (`kk_pp`/`kk_ppi`, segment coherence, E3d) already discharges, once
  kernels are spliced in. **Deferred to the vertical step, but solved.**
- For `r = DR`: `conv DR = DR`, so a `DR` demand edge fires `∀DR`
  **both ways**. The child's `∀DR`-consequences must land in the
  parent. This is the one genuinely new mechanism. **The crux.**

**Why it is a joint fixpoint.** The child's label is
`reqType(d :: fire(label m, DR))`, which depends on the parent's label;
the parent must absorb `fire(child label, DR)`, which depends on the
child's. So parent and child **share their `∀DR`-closure**. It
terminates: every added formula `c''` (from `∀DR.c''` in the child)
has `mdepth c'' < mdepth(∀DR.c'') ≤ mdepth(∃DR.d)`, strictly below the
demand that generated it — so the shared closure is bounded by the
same `lmd` measure the recursion already decreases on. Concretely, the
lift needs: (i) a `drSat` operation saturating a node's requirement set
so that for every `∃DR.d` it carries, the `∀DR`-consequences its
witness would require are present (a bounded fixpoint on the label,
`lmd`-decreasing); (ii) re-running coverage on the (finitely many)
formulas `drSat` adds — which are themselves smaller demands, so
`rnodes`/`rnodes_covers` apply unchanged; (iii) the tree-adjacency
predicate `d` for `symDrPo_frame`, marking exactly the `∃DR` demand
pairs. `∀EQ`/`∃EQ` fold reflexively into `expand` (mdepth-decreasing,
like the `∧`-closure). Nothing here re-opens coverage — it is the same
recursion over a `drSat`-saturated seed.

**Status.** The `∃`-side (coverage) and the frame side are done. The
`∀DR` reverse-firing (the `drSat` shared closure) is the remaining
mechanism for the horizontal universals; the vertical universals ride
on the existing kernel machinery. This is a well-scoped construction,
not an open problem — but a real one, to be built `lmd`-guided with the
checker as oracle, not rushed.

---

## 10. Postscript (2026-07-24): the ∀DR mosaic — both halves built, and
the composition condition

The `∀DR` reverse-firing of §9 is now **built and certified as two
halves** (round E3-slabel/snodes), each a well-founded recursion, 0
sorries:

- **Label side** — `slabel node = reqType node ++ ⋃_{∃DR.d ∈ reqType
  node} fire(slabel child, dr)` (child `= childNode`, i.e. seed
  `arg :: fire(reqType,dr)`). Proved: `slabel_sub_mty` (⊆ mty, via
  `fire_dr_reverse`), `slabel_sub_cl` (⊆ cl), `slabel_lmd_le` (stays in
  the `lmd` budget, via `revfire_lmd_lt`), **`slabel_reverse`** (∀DR.c
  in a child's saturated label ⟹ c in the parent's — reverse `ee_all`),
  `slabel_forward_reqType` (forward `ee_all` for required ∀DR).
- **Node side** — `snodes node = node :: ⋃_{∃r.c ∈ slabel node} snodes
  (schildNode …)` (child `= schildNode`, seed `arg :: fire(SLABEL,dr)`).
  Proved: termination (`schild_lmd_lt`), transitivity (`snodes_trans`),
  **`snodes_covers`** (every demand in a reachable node's *saturated*
  label is fulfilled by a reachable node).

**The composition point.** The two halves use different child seeds:
`slabel` fires from `fire(reqType,dr)`, `snodes` from
`fire(slabel,dr)`. The difference is exactly

    fire(slabel,dr) \ fire(reqType,dr)  =  { c : ∀DR.c ∈ reverse-batch },

i.e. the `∀DR`-**headed** formulas sitting inside the reverse batch. The
reverse batch consists of `∀DR`-*arguments* (`c` where `∀DR.c ∈ slabel
child`); such a `c` is `∀DR`-headed only when the original was
`∀DR.(∀DR.…)`. So:

**Composition holds directly when `∀DR` guards neither `∀DR` nor `∃DR`.**
Precisely: restrict to concepts where every `∀DR.c ∈ cl C₀` has `c` both
`∀DR`-free and `∃DR`-free. Then
- the reverse batch carries no `∀DR` ⟹ `fire(slabel)=fire(reqType)` ⟹
  `schildNode = childNode` on `∃DR` demands, so the frame's `DR` edges
  are exactly the `childNode` edges `slabel` fires reverse from —
  `slabel_reverse` gives reverse `ee_all` and `slabel_forward_reqType`
  gives forward `ee_all`;
- the reverse batch adds no new `∃DR` demand ⟹ no reverse-added `DR`
  edge to re-fire; reverse-added `∃PO`/`∃EQ` demands ride on `PO`
  edges (which fire nothing, ∀PO-free) / the `EQ` fold; and `snodes`
  degenerates to the `rnodes`-style coverage `snodes_covers` supplies.

This fragment is genuinely useful — it contains `∀DR.A`,
`∀DR.(∃PO.B ⊓ ∀PP.C)`, and the like (constraint-propagation `∀DR`),
excluding only `∀DR.(∃DR.…)` and `∀DR.(∀DR.…)`.

**Full generality** (`∀DR` guarding `∀DR`/`∃DR`) needs the **within-node
fixpoint**: `schildNode` fires forward from `slabel`, but for the
reverse direction `slabel` would then have to fire back from
`schildNode` — which needs `slabel` — a genuine circularity, resolved by
iterating the reverse firing to a fixpoint at each node (bounded by
`lmd`/`revfire_lmd_lt`, so terminating). That is the last piece of real
construction; everything up to it is proved.

**Plan for the assembly (no-`∀DR`-guarded-`DR` fragment):**
1. `GuardFreeDR` predicate + lemma `fire(slabel node,dr) = fire(reqType
   node,dr)` (reverse batch has no `∀DR`), hence `schildNode hF =
   childNode hF'` on `∃DR` demands (seed + witness equal by proof
   irrelevance).
2. Tree-structural `MultiTier` over `β = snodes root`: `E = symDrPo`
   frame with `d m m' = "∃DR-demand-adjacent"`; `tauE = slabel`.
3. `MultiTierOk`: frame `symDrPo_frame`; propositional from `slabel`
   saturation; `ee_all` on `DR` via `slabel_reverse`/`_forward`, on
   `PP`/`PPI` vacuous (`symDrPo_vals`), on `PO` vacuous (∀PO-free), on
   `EQ` via the fold; `e_ex` = `snodes_covers`.
4. `∃EQ`/`∀EQ` reflexive fold in `expand` (as for the ∀-free case's
   diagonal, now as a syntactic fold).

---

## 11. Resolution of the composition subtlety (2026-07-24)

Building the reconciliation lemmas (`slabel_alldr_reqType`,
`slabel_exdr_reqType` — under `noDR`-guard-freeness the saturated
label's `∀DR`/`∃DR` obligations equal the requirement type's) exposed a
concrete wiring subtlety and its fix.

`slabel` fires reverse from `childNode` (seed `arg :: fire(reqType,dr)`);
`snodes` currently covers via `schildNode` (seed `arg :: fire(slabel,dr)`).
For `ee_all` on the frame's `DR` edges (which are `snodes` edges) the
reverse direction needs `slabel_reverse`, which is proved against
`childNode`. So the two child notions must coincide on `∃DR` demands.

**Fix: define `schildNode` to fire from `reqType`, not `slabel`.**
`schildNode.s := arg :: fire(reqType node, r)`. Then:

- Under guard-freeness, forward `ee_all` still holds: `∀DR.c ∈ slabel
  node` ⟹ (`slabel_alldr_reqType`) `∀DR.c ∈ reqType node` ⟹ `c ∈
  fire(reqType node, dr) ⊆ schildNode.s ⊆ slabel(schildNode)`.
- On an `∃DR` demand `∃DR.d ∈ slabel node` (`= reqType node` by
  `slabel_exdr_reqType`), `schildNode` and `childNode` have the **same
  seed** (`d :: fire(reqType node, dr)`) and the **same witness**
  (`Classical.choose` of `mty_ex` of the *same* proposition `∃r.c ∈ mty
  node.x` — equal by proof irrelevance). `RNode`'s remaining fields are
  `Prop`s, so `schildNode hF = childNode hF'` as structures. Hence
  `slabel_reverse` (about `childNode`) *is* the reverse `ee_all` for the
  frame edge.
- Coverage (`snodes_covers`) is unaffected — it never used the seed's
  fire source, only that the child's argument lands in its own label
  (`schildNode_arg`), which still holds.
- Reverse-added non-`DR` demands (`∃PO`/`∃EQ`, allowed by `noDR`) are
  covered by `snodes`; their edges are `PO` (fire nothing, ∀PO-free) or
  the `EQ` fold. `schildNode.s = arg :: fire(reqType,po) = [arg]` for
  them (no `∀PO`), which is exactly right.

So the whole assembly runs on ONE child notion (`schildNode` firing from
`reqType`, `= childNode` on `∃DR`), `slabel` for labels, `snodes` for
the node set, `symDrPo_frame` for the frame, and the reconciliation
lemmas to route `ee_all`. No member-invariance lemma is needed — the
`reqType`-fire seed makes the two children *definitionally* the same on
`∃DR`. This is the last design point; the build is now mechanical
(refactor `schildNode`'s seed, then the tree-structural `MultiTierOk`).

---

## 12. One more requirement: `slabel` must be propositionally closed
(2026-07-24)

Checking `MultiTierOk`'s `e_and`/`e_or` on `tauE = slabel` exposed a
requirement. `slabel node = reqType node ++ ⋃ fire(slabel child, dr)`
adds RAW `∀DR`-arguments to the reverse batch; a `∀DR.(X ⊓ Y)` in a
child yields `X ⊓ Y` in the parent's reverse batch **without**
decomposing it. So `slabel` is not `∧`/`∨`-closed, and `e_and`
(`and c d ∈ tauE ⟹ c,d ∈ tauE`) fails on reverse-added conjunctions.

**Fix: `expand`-close the reverse batch.** Change the batch to

    ⋃_{∃DR.d ∈ reqType node} (fire(slabel child, dr)).flatMap (expand node.x)

i.e. add the guided *expansion* of each fired argument, not the raw
argument. Then:
- `slabel` is propositionally saturated — `reqType` is (`reqType_and/or`),
  and each `expand node.x c` is (`expand_and/or`), so their union is.
- It stays `⊆ mty` (each fired `c ∈ mty node.x` by `fire_dr_reverse`, and
  `expand node.x c ⊆ mty node.x` by `expand_sub_mty`) and `⊆ cl`
  (`expand_sub_cl_of`).
- `slabel_reverse` still holds: `∀DR.c ∈ slabel child ⟹ c ∈ fire(slabel
  child,dr)`, and `c ∈ expand node.x c` (`mem_expand_self`), so `c` is in
  the batch.
- It *strengthens* `slabel_dr_forward`: a reverse-added `∀DR.c` now sits
  in `slabel` directly (via `expand`), so the forward firing reaches it
  — this was the deeper reason `expand`-closing is the right move, not
  just a patch for `e_and`.
- The `∀DR`/`∃DR` reconciliation (`slabel_alldr_reqType`,
  `slabel_exdr_reqType`) still holds, now via `noDR_cl` (a `noDR`
  concept's closure has no `∀DR`/`∃DR`): a `∀DR`/`∃DR` in the batch would
  come from `expand(c')` with `c'` a `∀DR`-argument, hence `noDR c'`
  under guard-freeness, hence no `∀DR`/`∃DR` in `cl c' ⊇ expand c'`.
- `slabel_mdepth_le`/`_lmd_le` still hold (`expand` doesn't increase
  `mdepth`: `cl_mdepth_le`).

**Cost:** re-prove the ~8 `slabel` lemmas over the `expand`-closed batch
(each a local edit — the batch is now a `flatMap expand` of the old
one), plus a small `noDR_cl`. No new mathematics; all supporting lemmas
(`expand_and/or`, `expand_sub_mty/cl`, `mem_expand_self`,
`cl_mdepth_le`) are already proved. After that, the tree-structural
`MultiTierOk` assembly (§11 plan) goes through: `e_and/e_or` from the
now-saturated `slabel`, `ee_all` on `DR` via `slabel_dr_forward/reverse`,
`e_ex` via `snodes_covers`.

---

## 13. DONE (2026-07-24): the ∀DR-propagation fragment, certified

The §11–§12 plan is **built and certified**, 0 sorries:
`satisfiable_iff_podr_cert` — the **first fragment with genuine `∀`-firing
certified end-to-end**, both directions, no kernels.

**The fragment `DRFrag C₀`** (hypotheses on `cl C₀`): every existential
`∃DR`, every universal `∀DR` (hence `∀PO`-free), each `∀DR` DR-guard-free
(`noDR` body). Semantically: `∀DR`-constraint-propagation over a
`DR`/`PO`/`EQ` frame — `∀DR.A`, `∀DR.(A ⊔ B)`, `∃DR.(∀DR.A ⊓ C)`. A
**proper lift beyond `AllFree`** (which had NO `∀`-firing).

**What landed (all in `POFreeLift.lean`):**
- `qnet_empty_frame` (axiom-free): lift any `β`-frame through the
  `κ = Empty` quotient — `frame_q` for the kernel-free assembly, the
  analogue of `readoff_qnet_frame`.
- `sAdj` / `dadjB` / `dadjB_symm`: symmetric `DR`-adjacency (`m'` a
  `∃DR`-child of `m` or vice versa) as the frame's `DR` predicate.
- `mtDR` / `mtDR_frame`: the certificate + its frame validity
  (`symDrPo_frame` lifted via `frame_ext`, bridging the
  subtype-`DecidableEq` vs `Classical.propDecidable` instance gap).
- `mtDR_ok`: propositional from `slabel_and/or/clash/nobot`; `ee_all` on
  `DR` = the `∀DR` reverse-firing (`slabel_dr_forward/reverse`), on
  `PO`/`EQ` vacuous (no `∀PO`/`∀EQ`, from `DRFrag.hall`); `e_ex` from
  `schildNode` + `snodes_covers`, child `≠` parent by strong-EQ
  (`dr ≠ eq`); kernels vacuous (`Empty`).
- `extract_podr` / `satisfiable_iff_podr_cert`: soundness
  (`multiTier_sound`) + extraction ⟹ the iff.

Axioms: propext, Quot.sound, Classical.choice (choice model-side only).

**The one honest caveat (shared with `AllFree`).** This is a
**certificate characterization**, not a certified finite-model property:
`β` is quantified as an arbitrary `Type` (no `Fintype`, no cardinality).
Getting **Decidability** needs a `Fintype β` + a computable `K(C₀)` width
bound, then `decidableSat_of_codes`. That is the next step and is the
same remaining step the `AllFree` fragment faces — now with a genuine
`∀`-firing fragment underneath it.

**Roles beyond DR/PO (partly done).** `∃PO` **landed** (2026-07-24):
`DRFrag.hex` broadened to `r = dr ∨ r = po`; `e_ex` cases on the demand
relation, `∃PO` children routed to genuine `PO` frame edges via
`po_not_sAdj` (a `PO`-child is never `DR`-adjacent — `conv PO = PO ≠ DR`).
So the fragment is now **horizontal DR/PO** with `∀DR` propagation. The
frame stays tree-structural (no position indexing) because model
relations are functional + converse-coherent.

---

## 14. The remaining map (2026-07-24): three lifts, in difficulty order

The horizontal DR/PO `∀DR`-propagation fragment is **done**
(`satisfiable_iff_podr_cert`). What remains toward the FULL ∀PO-free
target, smallest-first:

**(A) `∃EQ`/`∀EQ` — low value, foundation-invasive.** EQ is the diagonal
(identity under strong-EQ), so `∃EQ.c` and `∀EQ.c` both reduce to `c` at
the same node — a reflexive fold. The natural home is `expand` (add
`.ex eq c ↦ ex eq c :: expand c`, `.all eq c ↦ all eq c :: expand c`).
BUT the soundness of the fold (`expand_sub_mty`) needs strong-EQ
(`hI.refl_eq` for `∀EQ`, `hI.eq_id` for `∃EQ`), and `expand`/`expand_sub_mty`
are currently `hI`-free — so this threads `hI : RCC5Interp I` through the
whole `_sub_mty` chain (`expand`→`reqType`→`slabel`). Invasive for a
degenerate feature; **deferred**.

**(B) `∀DR` guarding `∀DR`/`∃DR` — medium value, self-contained, intricate.**
Drop DR-guard-freeness (`hgf`). Then the reverse batch can carry `∀DR.c'`
(from `∀DR.(∀DR.c')`) and `∃DR.d'` (from `∀DR.(∃DR.d')`), so
`slabel_alldr_reqType`/`slabel_exdr_reqType` fail — `slabel`'s `∀DR`/`∃DR`
obligations exceed `reqType`'s, and `schildNode ≠ childNode`. The fix is
the **within-node fixpoint**: a node's fully-saturated label must be
closed under BOTH forward `∀DR`-firing (into `∃DR`-children, whose seeds
then fire from the SATURATED label) AND reverse `∀DR`-absorption (from
children's saturated labels) — a genuine mutual parent/child dependency.
It terminates (`revfire_lmd_lt`/`child_lmd_lt`: every fired formula is
strictly shallower), so it is a least fixpoint of a monotone,
depth-decreasing operator on the finite `cl C₀`. In Lean core (no
mathlib) that means a well-founded recursion on `lmd` computing the
saturated label directly, then re-proving `slabel_dr_forward/reverse`,
coverage, and the `schildNode = childNode` reconciliation over it — the
"last piece of real construction" for the horizontal fragment.
**~200–300 lines, multi-round, design-first.**

**(C) Vertical `∃PP`/`∃PPI` + `∀PP`/`∀PPI` — high value, THE big open
construction.** This is what makes "∀PO-free" a meaningful fragment
(vertical existentials/universals are the interesting content). The
kernel pieces are individually certified as BLOCKS (E3a–E3h:
`multiBlock_of_chain`, `block_of_persistent`, `kernel_site`, the
two-sorted ordered-disjoint frame, per-direction `kk_pp`/`kk_ppi`), but
**wiring them into the `snodes` assembly is the genuinely-open
multi-cluster recursion**: which model elements become kernels
(persistent `∃PP`/`∃PPI` towers) vs tree externals, the `κ ≠ Empty`
frame over `β ⊕ κ` mixing the tree-structural externals with kernel
chains, cross-cluster tightness, and the `e_ex` recursion routing every
demand. The design's "loose-PO default" dissolves the rectangle problem,
but the assembly itself is large and carries real design risk. **Do not
rush (round-19/20 lesson).**

Recommended order: **(B) then (C)** — (B) completes the horizontal
fragment and is self-contained; (C) is the summit. (A) is optional polish
whenever convenient.

---

## 15. The clean pivot (2026-07-24): model-type-truncated-by-depth labels

Designing (B) exposed a **much simpler architecture that dissolves (A) AND
(B) together** — and even the vacuous `∀PP`/`∀PPI` universals — with NO
fixpoint. The insight: the `reqType`/`slabel` machinery builds *syntactic*
labels that must be *explicitly closed* under `∀DR`-firing (the reverse
batch), and nested `∀DR` makes that a mutual fixpoint. But the label need
not be syntactic for a *certificate characterization* (the extraction has
the model `I` in hand). The **model type is already `∀DR`-closed both
ways** — the model satisfies every `∀DR` obligation — and the only reason
not to use it directly was termination (a witness satisfies unboundedly
deep formulas). **Truncating the model type by modal depth fixes exactly
that.**

**The label.** `mtk C₀ I x k := (mty C₀ I x).filter (mdepth · ≤ k)` —
model-true formulas of modal depth `≤ k`. Then:
- **Propositional** (`mtk_and`/`mtk_or`/`clash`/`nobot`): from `mty_*`;
  `mdepth` of a conjunct `≤ mdepth(and) ≤ k`.
- **Forward `∀`-firing** (`mtk_all_fwd`): `∀r.c ∈ mtk x k`, `ρ x y = r` ⟹
  `c ∈ mtk y (k-1)` — `mty_all` gives `c ∈ mty y`, and
  `mdepth c < mdepth(∀r.c) ≤ k` gives `mdepth c ≤ k-1`.
- **Reverse `∀DR`-firing** (`mtk_all_dr_rev`): `∀DR.c ∈ mtk y (k-1)`,
  `ρ x y = dr` ⟹ `c ∈ mtk x k` — **`dr_reverse_sat`** (already proved:
  `conv DR = DR` makes `x` a DR-neighbour of `y`) gives `c ∈ mty x`, and
  `mdepth c ≤ k-1 < k`. **This is the crux the whole project circled — and
  here it is free from the model.**
- **`∃`-witnessing** (`mtk_ex`): `∃r.c ∈ mtk x k` ⟹ a witness `y`,
  `ρ x y = r`, `c ∈ mtk y (k-1)` — `mty_ex` + depth drop.

**The recursion.** `MTKNode = (x, k, dom x)`; `mtkNodes` recurses on the
demands of `mtk x k`, each child at budget `k-1`. **Terminates on `k`
directly** (`k > 0` from any demand's `mdepth ≥ 1 ≤ k`) — no `lmd`
measure. `mtkNodes_covers` mirrors `snodes_covers`.

**The fragment `HFrag`.** `hex : ∃r.c ∈ cl C₀ ⟹ r ∈ {DR,PO,EQ}` (no
vertical existentials — those still need kernels), `hall : ∀r.c ∈ cl C₀ ⟹
r ≠ PO` (∀PO-free — the only real restriction). NO guard-freeness.

**What it certifies** (`satisfiable_iff_hfrag_cert`, both directions, same
tree-structural `symDrPo` frame): **the full ∀PO-free fragment MINUS
vertical existentials `∃PP`/`∃PPI`** — nested `∀DR.(∀DR.A)`, `∀DR.(∃DR.B)`
(B, done), `∀PP`/`∀PPI` (vacuous on the DR/PO/EQ frame, sound), `∀EQ`/`∃EQ`
(reflexive, A done), `∃PO`, `∃DR`. `ee_all`: `EQ` diagonal reflexive, `DR`
via `mtk_all_fwd`/`mtk_all_dr_rev`, `PO`/`PP`/`PPI` vacuous; `e_ex` via
`mtkNodes_covers` (+ `∃EQ` returns the same node). Strictly generalises
both `satisfiable_iff_allfree_cert` and `satisfiable_iff_podr_cert`.

**Why the project didn't use this before:** the focus was the *decidability*
path, where labels must be model-independent syntactic data (`reqType`, for
`K(C₀)` counting) — model types are unavailable there. For the
*characterization*, model types are ideal. So `reqType`/`slabel` are kept
for the eventual decidability layer; `mtk` is the clean characterization
route. This leaves ONLY `∃PP`/`∃PPI` (C, the vertical kernels) between here
and the full ∀PO-free characterization.

**DONE (2026-07-24): `satisfiable_iff_hfrag_cert`.** Built exactly as
above, 0 sorries, 0 warnings, axioms `propext`/`Quot.sound`/`Classical.choice`
(choice model-side). `HFrag`: `∃` ∈ {DR,PO,EQ}, `∀` ≠ PO. `mtk` label
layer + `mtkNodes` recursion (terminates on `k`) + coverage
`mtkNodes_covers` + the `mtHF`/`mtHF_ok` assembly (tree-structural frame,
`ee_all` three-way, `e_ex` three-way incl. `∃EQ` = same node). Designs (A)
and (B) are both discharged by this one route. **Only (C) — vertical
`∃PP`/`∃PPI` via kernels — now stands between here and the full ∀PO-free
characterization.**

### The vertical step (C), sharpened by the `mtk` route

The `mtk` idea should extend to the vertical case, and this reshapes (C).
The obstruction to putting `∃PP`/`∃PPI` on the tree-structural frame was
that `∀PP`/`∀PPI` fire along `PP`/`PPI` edges (unlike `∀PO`), so an
`∃PP`-child edge would impose real obligations both ways along an
unbounded vertical chain — which is why the design routed vertical demands
to *kernels* (cyclic phase towers). Two routes now:
1. **Kernels, as designed (E3a–E3h).** Splice the certified kernel blocks
   into the `mtkNodes` assembly: a *persistent* `∃PP`/`∃PPI` demand
   becomes a kernel chain (`block_of_persistent`), `κ ≠ Empty`, the frame
   over `β ⊕ κ`. The `mtk` label makes the *external* side clean; the
   kernel side already has `kk_pp`/`kk_ppi`. The open work is which demands
   become kernels and the `e_ex` routing — the multi-cluster recursion.
2. **A depth-AND-height budget?** Worth a look: whether a *two-budget*
   `mtk`-style label (modal depth for horizontal, a separate vertical
   bound) can absorb bounded vertical chains directly, deferring only the
   genuinely-infinite towers to kernels. Speculative; the `∀PP` transitive
   firing (`comp(PP,PP)={PP}`) is the thing to check. Not yet designed.

Route 1 is the safe, certified-pieces path; route 2 is a possible
simplification to scope before committing. Either way, (C) is the summit.

---

## 17. The vertical step (C), full analysis + first target (2026-07-24)

**The two sub-cases of `∃PP`, and why the frame is the obstruction.**
- **Infinite PP-chains** (persistent `∃PP`: `∃PP.G ⊓ ∀PP.(∃PP.G)`) — no
  finite model; represented by a **kernel** (cyclic phase tower). The
  certified `block_of_persistent` + the pigeonhole `segment_select`
  (E2a) build exactly this: an infinite model chain, its recurrent type
  cycled into `p` phases.
- **Finite PP-chains** (non-persistent `∃PP.A`) — satisfiable with a
  bounded chain, which needs **genuine `PP` edges** in the frame.

**The core obstruction (why `mtk`/tree-frame can't just add `PP`).** The
tree-structural `symDrPo` frame works because `{DR,PO}` is composition-
*free*: ANY symmetric `{DR,PO}` off-diagonal labelling is RCC5-valid
(`symDrPo_frame`). `PP`/`PPI` are NOT free — `comp(PP,PP)={PP}` forces
transitivity, `comp(PP,DR)={DR}` forces DR-inheritance down the order.
So `PP` edges cannot be sprinkled on a tree; a `PP`-structure must be a
genuine linear order. A **kernel represents one such order cleanly**;
multiple orders + horizontal links = the multi-cluster frame over `β ⊕ κ`
with `K` (external–kernel) and `Q` (kernel–kernel) values — the
`twoSorted`/`multi_kernel_block` machinery (E3d–E3f).

**Certified pieces in hand.** `block_of_persistent`/`_desc` (kernel from a
persistent `∃PP`/`∃PPI`); `multi_kernel_block` (`BlockOk` for a kernel
family via the `twoSorted` ordered-disjoint frame); `mtOkPool_of_block`
(`BlockOk` + the missing `e_ex` ⟹ `MTOkPool`); `glueFam`/`glueFam_ok`
(glue blocks, all-cross-`PO`); the pigeonhole segment toolkit.

**The gap = the EXTRACTION recursion.** Given a satisfiable full-∀PO-free
`C0`, decide per demand: `DR`/`PO` → tree external (the `mtk` machinery),
`∃PP`/`∃PPI` → kernel, `∃PO` cross-cluster → pool; then discharge each
block's `e_ex` and glue. This is "the multi-cluster recursion" — the
genuinely-open piece the whole project circled.

**FIRST TARGET (clean intermediate): the PERSISTENT-VERTICAL fragment.**
No `DR`/`PO`; existentials `∃PP` (persistent) + `∃EQ`; universals `∀PP`/
`∀EQ`. Every `∃PP` is persistent ⟹ always a kernel ⟹ **no finite-chain
problem, no horizontal mixing**. A single ascending kernel (`κ = Unit`)
via `block_of_persistent`, `e_ex` vacuous (no externals), pool empty (no
`∃PO`). This is the vertical analogue of the `podr` milestone — a clean
fragment with genuine `∀PP`-firing, certified from one kernel. It de-risks
the kernel side before the mixing. **The scoping question to answer first:
the exact `BlockOk → MultiTierOk` gap** (does an externals-free,
pool-free block give full `MultiTierOk` directly?) — investigate
`mtOkPool_of_block` before committing.

**Then, in order:** finite PP-chains (kernel-padding: pad a terminated
chain with the terminal type, or bounded `PP`-externals) → horizontal +
vertical mixing (the full `β ⊕ κ` frame, `K`/`Q` values from the model,
pool for cross-cluster `∃PO`) → the full ∀PO-free characterization.

---

## 18. The vertical investigation (2026-07-24): β=Empty path + the key gap

Investigated whether a **single kernel with `β = Empty`** (no externals)
could give a clean first vertical fragment — it's much simpler than
`block_of_persistent` (no `ctx`/witnesses/`BlockOk` layer). The result
sharply delimits what's possible.

**The β=Empty single-kernel `MultiTier`** (`κ = Unit`, `up = true`,
`phase () a = mty C₀ I (c (i+a))` from `segment_select`): nearly every
`MultiTierOk` field is FREE —
- externals `e_*`/`ee_all`/`ek_all`/`ke_all` vacuous (`Empty`);
- `k_clash`/`k_nobot`/`k_and`/`k_or` from `mty_*`;
- `kk_pp`/`kk_ppi` are EXACTLY `segment_kk_pp`/`segment_kk_ppi` (E2a);
- `kk_eq` reflexive (`mty_all` at `eq`, `refl_eq`);
- `kq_all` vacuous (no distinct `Unit` kernels);
- `frame_q` a one-point `eq` frame ⟹ `munf_is_frame`.

**The one hard field is `k_ex`.** A `∃r.c` demand at phase `a`:
- `r = pp` (`= cdir true`) routes to `∃ b<p, c ∈ phase b` — i.e. **`c`
  must be carried by a chain point**.
- `r = eq` in-phase; other `r` need externals (`Empty` — impossible).

**THE GAP (decisive).** `persistPP I C₀ G x` = `∃PP.G ∈ mty x ∧
∀PP.(∃PP.G) ∈ mty x`. The chain carries the **demand** `∃PP.G` at every
rung (via the guard, `mty_all`) but NOT its **argument** `G` — the witness
of `∃PP.G` is off-chain. `block_of_persistent`'s own comment confirms it:
"every rung carrying `∃PP.G`". So the chain fulfils `∃PP.G` internally
ONLY when `G` is already true at chain points — i.e. `G = ⊤` (the `Cinf`
shape). For a general `G`, the argument needs an **off-chain external
witness** ⟹ externals ⟹ the `e_ex`/`hserve` recursion ⟹ the block
machinery. There is no β=Empty shortcut past `Cinf`.

**Kept insight (`k_ex` routing).** A chain-carried `∃PP.c` at phase `a`
routes to phase `(a+1) mod p`; the recurrence `hty` wraps the `a+1 = p`
case to phase `0` (`c ∈ mty(c(i+p)) = mty(c(i)) = phase 0`).

**Conclusion.** β=Empty certifies only the `Cinf`-shape (essentially
`cinf_satisfiable` as a characterization — low marginal value). **The
general persistent-vertical fragment genuinely requires the
`block_of_persistent` integration**, whose crux is discharging the
externals' `e_ex` (the `hserve` witnesses for the off-chain `G`, which
themselves carry `∃PP.G` and recurse) — that IS the multi-cluster
recursion. So (C) has no shortcut; the next build is the block-integration
proper, best started with fresh context on the E3 `mkBlock`/`hserve`
contract. The paths are now precisely mapped.

---

## 19. The vertical kernel, CERTIFIED (2026-07-24): `vkernel_ok`

The β=Empty single-kernel milestone of §17/§18 is now **built and
kernel-checked** (`POFreeLift.lean`, section `VerticalKernel`), closing
the "de-risk the kernel side" step before the mixing.

**Correction to §18.** §18 concluded β=Empty "certifies only the
`Cinf`-shape (G=⊤)", reasoning that the chain carries the *demand*
`∃PP.G` but not its *argument* `G`. **That is wrong for the chain
`persistPP_chain` actually builds**: its `n+1` rung IS the `mty_ex`
witness of `∃PP.G` at rung `n`, so `G ∈ mty (c (n+1))` — the argument is
carried at every rung ≥ 1. `persistPP_productive` proves this and merely
*discards* it (the `_` in `obtain ⟨y, hdy, hr, _⟩`). So a chain-carried
`∃PP.G` routes to `k_ex` disjunct 2 (chain), needing only `G ∈ phase b`
for **one** `b` — take `b = 0`, i.e. `hG0 : G ∈ mty (c i)`. No external,
no `e_ex`, β = Empty.

**What `vkernel_ok` certifies.** For any RCC5 model `I`, any ascending
`PP`-chain `c` (`hstep : ρ (c n) (c (n+1)) = pp`), a type-recurrent
segment `[i, i+p]` (`hty : mty (c i) = mty (c (i+p))`), with
- `hG0 : G ∈ mty C0 I (c i)` (the argument lives in phase 0), and
- `hdemands : ∀ a r D, ∃r.D ∈ mty (c (i+a)) → (r = pp ∧ D = G) ∨ r = eq`
  (every phase existential is the single chain demand `∃PP.G`, or `∃EQ`),

the β=Empty κ=Unit `vkernel` is a full **`MultiTierOk`** — genuine
`∀PP`-firing (`kk_pp` via `segment_kk_pp`), cyclic phases, `∃PP` served
by the chain, `∃EQ` in-phase (`seg_ex_eq`), externals vacuous (`Empty`),
pool empty. `frame_q` is `readoff_qnet_frame` on the one-point
`{c i}` kernel. This is a GENERAL theorem (any such chain), not the one
hand-built `cinfTT`; it is the reusable kernel-certificate builder the
assembly instantiates per persistent demand — the externals-free case of
what `block_of_persistent` does with externals.

**Non-vacuity, strictly beyond `Cinf`.** `Cvert = A ⊓ ∃PP.A ⊓ ∀PP.∃PP.A`
(`A = atom 0`) has no finite model (forced ascending `PP`-tower) and
carries a real atom. Its ℕ-order model (`Ivert = ⟨_, chain, atom-0-
everywhere⟩`, RCC5 via `frame_rcc5 chain chainFrame`) feeds `vkernel_ok`
(chain `= id`, `i=0`, `p=1`, all `mty n = cl Cvert`), yielding
`MultiTierOk` and hence `Satisfiable Cvert` (`cvert_satisfiable`) THROUGH
the kernel machinery — demonstrating the hypotheses are jointly
satisfiable (the recurring "vacuous premise" defect class avoided).
`hdemands` is discharged by a decidable list check (`cvert_demands_b :
(cl Cvert).all okDemand`, `by decide`) — the single ∃ in the closure is
`∃PP.A`. Axioms: `propext`/`Quot.sound`/`Classical.choice` (model-side).

**What remains (unchanged, the summit).** The single-`∃PP` restriction is
essential to β=Empty: two distinct `∃PP.G₁`, `∃PP.G₂` have distinct
witnesses, only one of which is the chain's `n+1` rung — the other needs
an external, whose own `∃PP` recurses. That is the multi-cluster
`e_ex`/`hserve` recursion, `block_of_persistent` + `mtOkPool_of_block`
territory, still open. `vkernel_ok` de-risks the kernel interior; the
mixing is the next build.

### E3h′ (2026-07-24): the FIRST `e_ex` discharge — a root external

`vkernel1`/`vkernel1_ok` add ONE external `x0` sitting BELOW the chain
(`x0 PP c i`, hypothesis `hx0pp : ∀ a, ρ x0 (c (i+a)) = pp`), giving the
first `MultiTierOk` with a genuine external whose `e_ex` residual is
DISCHARGED — β = Unit, not vacuous. Two moves:
- **`x0`'s `∃PP.G` routes DOWN-UP into the kernel** — `e_ex` disjunct 2,
  `conv (K () x0) = pp` because `x0 PP c i` (so `ρ (c i) x0 = ppi`,
  `hKppi`), `G ∈ phase 0` (`hG0`). The external's demand is fulfilled by
  the EXISTING kernel — no new kernel needed.
- **`x0`'s `∃EQ` self-serves** (`e_ex` disjunct 1, `E x0 x0 = eq`).
- The external's `∀`-obligations (`ee_all`/`ek_all`/`ke_all`) fire by
  `mty_all` through the constant `pp`-row `x0 → segment` (`ek_all`
  `r = pp`; `ke_all` `r = ppi = ρ (c(i+a)) x0`, `hEK`).

It **carries `C0` at the external node** — the model root, where `C0`
actually holds — resolving the "far segment doesn't carry the root type"
problem of the β=Empty version. Witness `cvert_satisfiable_ext`: `Cvert`
at the root external `0`, chain `= id`, segment `[1,2]`; `0 PP` the whole
segment via `chain_lt`. Axioms `propext`/`Quot.sound`/`Classical.choice`.

This is the first stone of the mixing — **an external served by an
existing kernel**. The open summit is the OTHER external shape: one whose
`∃PP` argument is off the one chain, needing a NEW kernel (indexed by
recurrent type, with `Q` rectangle values and `K(C₀)` counting for
finiteness). `vkernel1` shows the down-into-kernel routing; the
up-into-a-fresh-kernel routing is the multi-cluster recursion proper.

### E3h″ (2026-07-24): the first MULTI-kernel certificate

`vkernel2`/`vkernel2_ok` add a SECOND kernel (`κ = Bool`, `β = Empty`):
TWO ascending `PP`-kernels, each serving its own `∃PP` via its own
chain. The genuinely new field is **`kq_all`** — a `∀`-obligation in
kernel `k`'s phase fires along the cross-kernel `Q`-edge into ALL of
kernel `k'`'s phases — discharged by `mty_all` through the cross-row
constancy `hrectQ` (the "rectangle" condition; supplied as a hypothesis,
trivial on the witness where the cross-value is a constant `DR`). Plus
the two-kernel FRAME (`readoff_qnet_frame` over two distinct bases,
`hbase` for injectivity). This is the shape `cbothMT` hand-built (two
DR-linked kernels), now a GENERAL lemma from two model chains.

**The two-tower model** `chain2` (`Bool × ℕ`, same-tower = `chain`,
cross-tower = `DR`) is a genuine RCC5 frame — `chain2_frame`, the cross
cases resting on `comp(·,DR) ∋ DR` and `comp(DR,DR) ⊇ {PP,EQ,PPI}`
(machine-checked against the table). `Cvert` holds at every point of both
towers, so `cvert2_satisfiable` produces a two-kernel certificate for
`Cvert`. Axioms `propext`/`Quot.sound`/`Classical.choice`.

**What's still missing toward the summit** (in increasing difficulty):
1. ~~**Cross-kernel `∃`** — `k_ex` disjunct 4~~ — **DONE (E3h‴ below).**
2. **Externals that spawn NEW kernels** — an external whose `∃PP`
   argument is off every existing chain, so a fresh kernel is created.
   This is the recursion (§§3–8).

**On "open" vs "mechanical" (correcting a slip).** This step is NOT open
mathematics *for the fragment*. Its counting is **mechanical**: §6 bounds
every dimension by a computable function of `n = |cl C₀|` (types `≤ 2ⁿ`,
kernels `≤ 2ⁿ·n`, …), precisely because ∀PO-freeness keeps PO loose
(`mty_no_all_po`) and so blocks the rigid-crowd blow-up that makes **F6**
hard. **F6 is a FULL-LOGIC obstruction** (the width barrier / M_n
identity-selector minors), and the fragment is designed to sit *below*
it. Per §8 the one item with "genuine mathematical risk" is step 3's
`e_ex` coverage/termination *bookkeeping* (is every generated node's
demand routed?) — a "presume-a-snag" concern from the 17-review ledger,
not new mathematics. So: mechanical-by-design, uncertified — which is
exactly why turning each move into a kernel-checked theorem (this
session's three) is the work that matters.

`vkernel2_ok` de-risks the two-kernel FRAME + cross-kernel `∀`; (1) and
(2) — cross-`∃` and kernel-spawning — remain.

### E3h‴ (2026-07-24): cross-kernel `∃` — the routing toolkit is COMPLETE

`vkernel2x_ok` adds the last routing primitive: a kernel's `∃DR.Gx`
demand served by the OTHER kernel (`k_ex` disjunct 4), via the cross-`DR`
value `Q k (!k)` (`hQdr`) and the argument living in the other kernel's
phase (`hGx`). This is `cbothMT`'s hand-built `∃DR.Dinf`-across, now a
GENERAL lemma. Witness `Cvert2x = Cvert ⊓ ∃DR.A` — a concept that
GENUINELY needs two clusters (`∃DR` cannot be served inside one PP-tower)
— `cvert2x_satisfiable`, the first *non-artificial* multi-kernel
certificate (each tower serves the other's `∃DR.A`).

**The routing toolkit is now complete.** Every `k_ex`/`e_ex` disjunct has
a certified GENERAL lemma:

| routing | disjunct | certified by |
|---|---|---|
| `∃PP` up the chain | `k_ex` 2 | `vkernel_ok` |
| `∃PPI` down the chain (descending) | `k_ex` 2 | `dvkernel_ok` (E3h⁗) |
| `∃EQ` in-phase | `k_ex` 3 | `seg_ex_eq` |
| external `∃PP` down-into-kernel | `e_ex` 2 | `vkernel1_ok` |
| cross-kernel `∀` | `kq_all` | `vkernel2_ok` |
| cross-kernel `∃` | `k_ex` 4 | `vkernel2x_ok` |

**E3h⁗** added the DESCENDING kernel `dvkernel_ok` (`up = false`,
`PPI`-chain), mirror of `vkernel_ok`, via a reversed-`ℕ` model
`dchainN i j := chain j i` (a genuine RCC5 frame, no `ℤ` needed) and
witness `Dvert = A ⊓ ∃PPI.A ⊓ ∀PPI.(∃PPI.A)` (`dvert_satisfiable`).  So
the toolkit now covers BOTH vertical directions, as the fragment's
`∃PP`/`∃PPI` demands require.

So the remaining summit (step 2, kernel-spawning) is **pure assembly of
certified routings + the coverage/termination bookkeeping** — no new
routing to invent. What the recursion must still do: (a) decide, per
model element, whether it is a kernel base or an external and which
kernel serves each demand; (b) prove every generated node's demand hits
one of the five routings above (the `e_ex` coverage argument — §8's one
"genuine risk"); (c) `K(C₀)`-bound the family (§6, mechanical). The
pieces are all theorems; the recursion that wires them for an arbitrary
∀PO-free `C₀` is the last build.

### E3i (2026-07-24): the cluster-glue operation

`glueMTOk` combines a FINITE FAMILY of independent `MultiTierOk`
no-`∀PO` clusters into ONE `MultiTierOk` — the assembly's "combine
independent clusters" step, built on the certified `glueFam_ok`
(all-cross-`PO`, empty pool).  Support: `mtOkPool_nil_of_mtOk`
(`MultiTierOk → MTOkPool []`, pure weakening, **axioms: `propext` only**)
+ vacuous pool realization + `vkernel_nopo` (the fragment's `∀PO`-vacuity
for a `vkernel`).  Witness `cvert_glue2`: `Cvert` via TWO independent
vkernels glued cross-`PO`.

So the assembly's PRIMITIVES are now all certified:

| primitive | lemma |
|---|---|
| per-cluster routing (both directions) | `vkernel_ok`/`vkernel1_ok`/`dvkernel_ok` |
| cross-cluster `∀` / `∃` | `vkernel2_ok` / `vkernel2x_ok` |
| combine INDEPENDENT clusters | `glueMTOk` (this round) |

**What `glueMTOk` does NOT do (still the summit):** (i) cross-`∃`-LINKED
clusters — a demand crossing clusters uses `vkernel2x_ok`'s read-off
routing, not `glueFam`'s loose cross-`PO`; (ii) the GENERATOR — deciding,
from a satisfiable `C₀`, WHICH model elements are kernel bases vs
externals and how many clusters, with the `e_ex` coverage proof (§8's
one "genuine risk") and the `K(C₀)` bound (§6, mechanical).  The
combine-step is now a certified theorem; the generate-and-cover step is
the remaining build.

### E3j (2026-07-29): the single-`∃PP` GENERATOR (extraction begins)

`satisfiable_of_persistPP` is the FIRST extraction on the vertical side —
the vertical analogue of `extract_hfrag`.  From a model element `x0`
carrying a persistent `∃PP.G` demand (`persistPP`), whose model types
carry only `∃PP.G`/`∃EQ` demands (`hdem`, a syntactic condition on
`cl C₀`), it BUILDS a finite certificate carrying `C₀`.  It threads the
generator's plumbing, now certified:
- **`persistPP_productive'`** — the `∃PP.G` witness carries `G` (the fact
  `persistPP_productive` discarded; §18's correction as a lemma).
- **`persistPP_chain'`** — a chain carrying `G` at EVERY rung (invariant
  `persistPP ∧ G ∈ mty`).
- **`segment_select`** — a type-recurrent segment.
- **`chain_model_pp`** — the root sits `PP`-below the whole segment.
- **`vkernel1_ok`** — the root is the below-external whose `∃PP.G` routes
  into the kernel; the single demand is chain-served, so NO `e_ex`
  recursion.

Fires on a real concept: `cvert_via_generator` recovers `Cvert` THROUGH
the generator (not the hand-built kernel).  Axioms
`propext`/`Quot.sound`/`Classical.choice`.

**Scope (honest).** This is the ONE-kernel extraction: a SINGLE
persistent `∃PP.G`.  What it does not yet do — the MULTI-demand case
(several `∃PP.Gₖ`, each spawning a kernel, glued by `glueMTOk`/cross-`∃`
links) with the coverage argument that every generated node's demand is
routed, and the `K(C₀)` bound.  That coupled generate-and-cover step is
the summit.  But the extraction SKELETON — witness → `G`-carrying chain →
recurrent segment → below-external + kernel → certificate — is now a
certified pipeline, ready to be iterated per demand.

### E3k (2026-07-30): the STAR frame — the multi-demand keystone

The multi-demand geometry forces a STAR: the witnesses of distinct
`∃PP.Gₖ` demands at one root are pairwise `PO`/`PP`/`PPI`/`EQ`
(composition forbids `DR` there), so the root is `PPI`-below every kernel
and the kernels are cross-`PO` (loose, `∀PO`-free ⟹ `kq_all` vacuous).
**`starNet`** declares exactly this
(`= qnet (fun _ _ => eq) (fun _ _ => ppi) (fun _ _ => po)` over
`Unit ⊕ N`), and **`starNet_frame`** proves it is a genuine RCC5 frame —
**axioms `propext` only** (a pure structural composition check via the
`rfl`-helpers `starNet_ll`/`lr`/`rl`/`diag`/`off`).  So a shared root can
sit below ARBITRARILY MANY cross-`PO` kernels.  Next: `starKernel` (the
`MultiTier` over this frame) + `starKernel_ok` (the root routes each
`∃PP.Gₖ` into kernel `k`; each kernel is self-served; `kq_all` vacuous),
then the extraction that enumerates the demands.

### E3l (2026-07-30): the multi-demand VALIDITY, certified

`starKernel` (the `MultiTier` over `starNet`: root `Unit` labelled
`mty x₀`, `N` ascending kernels) + **`starKernel_ok`** — the multi-demand
`MultiTierOk`, given the model data:
- `hbelow` (`x₀ PP` every chain), `hty` (each chain type-recurrent);
- `Gk : N → Concept`, `hchainG` (chain `k` carries `Gk k`);
- **`hphase_dem`** (kernel `k`'s phases demand ONLY `∃PP.(Gk k)`/`∃EQ` —
  this is why COVERAGE CLOSES: no cross-`∃`);
- **`hroot_dem`** (the root's demands are each some `∃PP.(Gk k)`/`∃EQ` —
  the demand→kernel map).

Every field discharged: `frame_q` via `frame_ext`+`starNet_frame`;
root↔kernel `∀`-obligations (`ee_all`/`ek_all`/`ke_all`) by `mty_all`
through the model's `x₀ PP`-chain rows (`hbelow`/`hbc`); `kq_all` vacuous
(`mty_no_all_po`); `e_ex` routes each `∃PP.(Gk k)` INTO kernel `k`
(disjunct 2), `∃EQ` self; `k_ex` each kernel chain-serves its own demand,
`∃EQ` in-phase.  Compiled first try; axioms
`propext`/`Quot.sound`/`Classical.choice`.

**This is the coupled coverage-closing multi-demand certificate** — the
piece the project flagged as the summit's genuine risk, now a certified
theorem MODULO its model-data hypotheses.  What remains is the
EXTRACTION: from a satisfiable multi-`∃PP` `C₀`, produce `ck`/`Gk`/… and
verify `hbelow`/`hphase_dem`/`hroot_dem` — enumerating the (finitely many)
demands of `cl C₀` and building one chain per demand, `x₀` below each.
The validity no longer has the coverage risk; the extraction is the
demand-enumeration + geometry (`x₀ PP` each witness's tower).

### E3m (2026-07-30): linear-nested `∃PP` — `vkernelG_ok` (cross-link, easy half)

A course-correction (Michael): the star handles only INDEPENDENT towers;
the full ∀PO-free logic has CROSS-LINKED `∃PP` (`∃PP.G` where
`G ⟹ ∃PP.G'`).  That splits geometrically:
- **linear nesting** (`∃PP.G₁`, `G₁ ⟹ ∃PP.G₂`, …): the witnesses form
  ONE ascending chain (`wᵢ₊₁` = `wᵢ`'s `∃PP.Gᵢ₊₁` witness), carrying
  every nested argument — "merge into one chain = one kernel";
- **branching nesting** (a tower demanding two INCOMPARABLE `∃PP`
  witnesses, `comp(ppi,pp) ∋ po`): a genuine `PP`-tree — the hard case.

**`vkernelG_ok`** does the linear half: a self-carrying kernel where
every phase's `∃PP.D` has `D` carried by SOME phase (`hdemands` weakened
from `D = G` to `∃ b, D ∈ phase b`); `k_ex` serves each nested demand at
the phase holding its argument.  Witness `clin_satisfiable`: `Clin =
∃PP.A₀ ⊓ ∃PP.A₁ ⊓ ∀PP.(…)` — two DISTINCT `∃PP` arguments on one chain,
which `vkernel_ok` cannot do (its `hdemands` forces a single `G`).

**Still open toward full ∀PO-free** (difficulty order): branching `∃PP`
(cross-`PP` kernels, `kq_all` FIRES — `∀pp` propagation, not vacuous
cross-`PO`); horizontal+vertical MIXING; `K(C₀)` COUNTING for
decidability.  The star (independent) + `vkernelG` (linear-nested) are
two of the three vertical sub-cases; branching is the hard third.

---

## 20. The branching case, RECONSIDERED (2026-07-30): sound, and it reduces to cross-`PP` kernels

A research round (prompted by Michael's "doesn't cross-linked `∃PP`
merge the towers into one?") **overturns the pessimistic reading** at the
end of §E3m. Branching is NOT the unsound rectangle-problem wall I
claimed; it is sound, and it reduces to the multi-kernel machinery
already in hand. Here is the corrected analysis, grounded in a certified
lemma.

### 20.1 The apparent wall (what I feared)

Branching: a main-tower element `aᵢ` demands `∃PP.C` for a side type `C`
not on the main chain, and the witnesses seemed to force a **staircase**
— pick `sᵢ` as `aᵢ`'s *own* `C`-witness, then `aᵢ PP sᵢ'` for `i ≤ i'`
but `aᵢ PO sᵢ'` for `i > i'` (`comp(ppi,pp) ∋ po`). That relation is
NON-constant, the `MultiTier` frame forces ONE constant `Q(k,k')`, and
declaring it `PP` is unsound (`aᵢ₊₁`'s `∀pp` obligation would demand
things at `sᵢ'` that the real model — where `aᵢ₊₁ PO sᵢ'` — doesn't
guarantee). That is the half-graph / M_n pattern of the F6 width
analysis (wp41–wp43), and it looked like the frontier.

### 20.2 The resolution: pick the witness ABOVE THE WHOLE SEGMENT

The staircase comes from picking `sᵢ` *just above `aᵢ`*. But the
certified `kernel_site` (E2b) already picks side-witnesses the OTHER way
— its `hserve` clause gives, for a `∃PP.D` demand on a recurrent-type
segment `[i, i+p]`, a witness `w` with

    D ∈ mty w  ∧  ∀ b ≤ p, ρ(c(i+b)) w = pp

i.e. `w` is `PP`-ABOVE THE ENTIRE SEGMENT, with a **constant** `pp`-row
(via `pp_witness_all_below` / late-picking — the "witness with the
constant demanded relation to all chain positions up to the bound").
So the rectangle IS constant: one `w` above the whole cyclic segment,
`Q`/`K` row `= pp` for every position. The staircase is an artefact of
the naive per-position witness; the recurrence lets us pick a high,
uniform one.

### 20.3 Why it is sound

`kq_all`/`ek_all` fire soundly through the MODEL, not by fiat: the
segment element `c(i+b)` genuinely satisfies `c(i+b) PP w` (that IS the
constant row), so `c(i+b) ⊨ ∀pp.X ⟹ w ⊨ X` in the model, hence
`X ∈ mty w`. The abstract unfolding then declares "every cyclic copy of
the segment `PP w`", which is frame-consistent (an infinite ascending
chain may have an upper bound; `comp(ppi,pp) ∋ pp`). So the certificate
unfolds to a valid model even though the ORIGINAL model's tower may be
unbounded — exactly the "unfold to SOME model" licence the soundness
pipeline already uses.

### 20.4 The reduction: branching ⟶ cross-`PP`-linked kernels

With the uniform high-witness, the geometry is **nesting**, not
staircase: the `a`-kernel sits `PP`-below a `C`-kernel (`w`'s tower). And
that is the machinery already certified:
- **`vkernel2_ok`** fires `kq_all` for a cross value via `hrectQ`
  (rectangle constancy) + `mty_all` — with `Q = pp` (constant, from the
  `hserve` row), it is the `∀pp`-across-the-nest propagation, sound as in
  20.3. My `cvert2` witness used `Q = dr` (making `kq_all` vacuous); the
  same lemma covers `Q = pp` with `kq_all` FIRING.  **Now WITNESSED**
  (`cnest_satisfiable`, the `nestNet` model — `false`-tower `PP`-below
  `true`-tower — where `∀pp.(∃pp.A)` propagates up the nest via `kq_all`).
- **`vkernel2x_ok`** routes cross-kernel `∃` (`k_ex` disjunct 4); the
  `a`-kernel's `∃PP.D` routes to the `C`-kernel via `Q(a,C) = pp`.
- If `C` is self-contained, the `C`-kernel serves its own `∃PP.D` by
  `vkernelG_ok` (self-carrying). If `C` branches again, recurse — and
  the recurrent TYPES are finite (`≤ 2^{|cl C₀|}`), so finitely many
  kernels.

So branching is **cross-`PP` multi-kernel**: `starKernel` with some
cross edges `PP` (forced, rectangle-constant via `hserve`) instead of
all `PO`. `kq_all` fires on the `PP` edges (sound), stays vacuous on the
`PO` edges.

### 20.5 What is actually left (and it is finite + sound, not a wall)

1. **A `Q = pp` cross-kernel variant** — combine `vkernel2_ok`'s
   `kq_all`-via-`hrectQ` (firing) with `vkernel2x_ok`'s cross-`∃`
   routing, at `Q = pp`. Mechanical: both halves exist; this is wiring
   them at a `PP` cross-value with the `hrectQ` supplied by `hserve`'s
   constant row.
2. **The extraction recursion** (the summit, still): enumerate the
   demands, build the tower per demand, pick the high `hserve` witnesses,
   type-quotient the witnesses into finitely many kernels, discharge
   `e_ex`. This is `one_kernel_block` + `mtOkPool_of_block` territory —
   the multi-cluster recursion — now with the branching links understood
   as rectangle-constant cross-`PP`.
3. **Finiteness / coverage bookkeeping** — §8's standing "genuine risk",
   unchanged (is every generated node's demand routed; does the
   type-quotient close). This is the real remaining mathematics, and it
   is a FINITENESS/coverage question, not the soundness wall of §20.1.

### 20.6 Correction to the record

§E3m called true branching "the hard third — the rectangle problem,
unsound to declare cross-`PP`". That was **wrong**: the E2b constant-row
high-witness makes it sound and rectangle-constant, and it reduces to
cross-`PP` kernels (machinery in hand). The honest remaining difficulty
is the SAME as it always was — the extraction recursion's coverage +
`K(C₀)` finiteness (§8), plus horizontal+vertical mixing — not a new
unsoundness frontier. The vertical geometry is now fully mapped: linear
(self-carrying, `vkernelG` ✓), independent (cross-`PO` star,
`starKernel` ✓), branching (cross-`PP` nest, reduces to the above). The
summit is the recursion that assembles them, and it is finite and sound.

## 21. Branching TERMINATES: the vertical structure is a finite poset of kernels (2026-07-31)

§20 established branching is *sound*. The question left open was whether
it stays *finite* — i.e. whether the extraction recursion terminates.
It does, and the argument pins down the exact shape of the vertical
extraction.

### 21.1 The termination argument

Take a main `∃PP`-tower with recurrent type `T`, and suppose `T` carries
a `∀PP`-guarded side-demand `∃PP.H` (i.e. `∀PP.(∃PP.H) ∈ T`). The guard
**propagates up the order**: every occurrence above a `T`-element
inherits `∃PP.H`. So the `H`-witness `w` (placed above the whole
`T`-segment by `hserve`) inherits *all of `T`'s `∀PP`-guarded
obligations* — in particular `∃PP.G-main`. Guarded branches therefore do
**not** stay disjoint: their obligation sets accumulate, and the
recurrent types converge.

Two exhaustive cases:

- **Guarded demand** (`∀PP.(∃PP.G) ∈ T`): re-forced at every level ⟹ the
  witnesses accumulate the whole guard set ⟹ a **recurrent type**
  (possibly a period-`p` cycle). Its tower is self-carrying for the
  same-type demands (`vkernelG`), or cross-`PP`-links to *another*
  recurrent type.
- **Unguarded demand** (`∃PP.G` without the `∀PP` guard): a **one-time**
  request, not re-forced up. Its witness starts a *separate* tower if
  `G` is itself persistent, else it is a bounded finite branch (padding,
  no kernel).

Since every type is a subset of `cl C₀`, there are `≤ 2^{|cl C₀|}`
distinct types, hence **finitely many kernels** — one per recurrent
type. The recursion terminates. (This matches the F6 probes wp42/wp43:
the horizontal "staircase" *collapses to finite-state* at recursive
interfaces.)

### 21.2 The shape: a finite poset of self-carrying kernels

The vertical extraction of a ∀PO-free concept is therefore:

> a **finite poset** `(K, <)` of kernels, one per recurrent type, where
> `k < k'` iff type-`k` occurrences are `PP`-below type-`k'` occurrences;
> each kernel **self-carries** its same-type `∃PP` demands (`vkernelG`)
> and **cross-`PP`-links** (`vkernel2x` at `Q = pp`, `kq_all` firing via
> the rectangle-constant `hserve` row) to the kernels above it;
> incomparable kernels are cross-`PO` (`kq_all` vacuous, ∀PO-free); the
> root `x₀` (carrying `C₀`) is `PP`-below every kernel.

There is **no genuine infinite branching**: the "merge into one" the user
anticipated is exactly the `∀PP`-accumulation collapse, and what does not
collapse is a *finite* poset of distinct-type kernels.

### 21.3 The frame is certified: `posetNet_frame`

The frame underlying that poset — root `PP`-below all, kernels ordered by
any strict partial order, `PO` for incomparable, **no `DR`** — is now a
kernel-checked theorem: `posetNet lt` (E3o) is a `Frame` for every
irreflexive-transitive `lt`, proved through the certified
`ordered_disjoint_frame` (its `DR`-downward-closure hypothesis is vacuous
because the frame has no `DR`). Axioms: `propext` only. `starNet` is the
special case `lt = ∅` (all `PO`). This is the general vertical frame the
finite kernel poset is built over.

### 21.4 What is genuinely left

The soundness question is settled and the frame is built. The residual
work is the ASSEMBLY over `posetNet`:

1. **The multi-kernel `MultiTierOk`** — ✅ **DONE (E3p, `posetKernel_ok`,
   2026-07-31).** Generalises `starKernel_ok` off the discrete
   (all-`PO`) star to `N` kernels with cross-values read off the model:
   the rectangle-constancy `hrectQ` makes `kq_all` FIRE across comparable
   (`PP`/`PPI`) kernels — `vkernel2`'s mechanism at arbitrary index `N`,
   with a root. The root machinery (`e_ex`/`k_ex`/`ee`/`ek`/`ke_all`) is
   `starKernel`'s; frame via `readoff` + `frame_ext`. **No `POFree`
   needed** — the rectangle transports every cross-`∀` uniformly, so
   `kq_all` is a single `mty_all` + `hrectQ` step regardless of the
   cross-value (the `∀PO`-vacuity of `starKernel` is subsumed). Axioms:
   `propext`/`Classical.choice`/`Quot.sound` (model-side, = `starKernel`).
   **Non-vacuity witnessed** (`crnest_satisfiable`, `rootNest` model —
   root `PP`-below the two nesting towers): `posetKernel_ok`'s hypotheses
   are jointly satisfiable AND the cross-`PP` `kq_all` fires over the
   root, the full §21 shape (root + finite poset of kernels) at `N = 2`.
   `rootNest_frame` is `propext`/`Quot.sound` only.
   **Self-carrying variant** (`posetKernelG_ok`, E3r): `hphase_dem`
   weakened to `∃ b, D ∈ phase b` (`vkernelG`-style) so a SINGLE kernel
   serves SEVERAL `∃PP` demands from its own chain — removes the
   single-demand-per-kernel limit inherited from `starKernel` (the root
   still routes to primary demands `Gₖ`). This is the shape the
   extraction actually produces: recurrent-type kernels each carrying
   multiple same-tower demands.
2. **The extraction** — from a satisfiable ∀PO-free `C₀`: enumerate the
   `∃PP` demands of `cl C₀`, build one tower per demand, take the high
   `hserve` witnesses, **quotient the witnesses by recurrent type** into
   the finite poset, read off `<`, discharge `e_ex`. The termination is
   §21.1; the one real subtlety is the type-quotient's exactness
   (uniformization / W2′ — do same-type occurrences carry the same
   cross-rows? the `hserve` constant-row discipline is designed to force
   yes, but this is the step to prove, not assert).
3. **Horizontal + vertical mixing** and **`K(C₀)` counting** — the
   finiteness bookkeeping of §8, unchanged.

### 21.5 Uniformization is NOT the open full-logic F6 (calibration)

An earlier framing (and some chat) called the uniformization step
"F6-hard". **That is wrong and must not be repeated.** Full-logic F6 (the
rigid horizontal crowd / `M_n` identity-selector minor) is forced BY
`∀PO`: universal PO-constraints pin the PO relations so the crowd cannot
be quotiented. The ∀PO-free fragment REMOVES that mechanism — PO stays
loose, crowds are mergeable, width is bounded by design. Concretely:

- Horizontal ∀PO-free is already certified (`satisfiable_iff_hfrag_cert`)
  and never touched width at all — it terminates by modal-depth
  truncation (`mtk`).
- Vertical ∀PO-free needs the kernel machinery, and the `hrectQ`
  uniformization needs only a bounded LIVE NEIGHBOURHOOD — the fragment's
  OWN width question, bounded by §21.1's finite-type kernels
  (`≤ 2^{|cl C₀|}`) and the collapse probes `wp41`–`wp43`.

So uniformization here is **fragment-level formalization**, categorically
easier than full-logic F6, which the fragment is *designed* to escape.
Honest caveat: the general "∀PO-free ⟹ bounded width" is strongly
supported (design + finite types + witness probes) but not yet a closed,
formalized theorem — so not trivially done, just NOT the open research
problem. The `wp39` "W2′ folds into F6" result is a FULL-logic statement;
it does not transfer to the fragment.

The frontier is now precise: **one general multi-kernel lemma over
`posetNet`, then the type-quotient extraction whose only open point is
uniformization — a fragment-level width fact, not full-logic F6.** No
soundness wall, no infinite branching, finite poset.

## 22. The decidability roadmap (2026-07-31)

Decision to pursue `Decidable (Satisfiable C₀)` for ∀PO-free `C₀`.
The picture, after scoping the existing artifact:

### 22.1 The decision layer is DONE

Already certified (rounds C–D2, 15th-review `finAcceptB` lineage):

- `FinMT` — the first-order certificate: pure list data (`tauE`, `E`/`K`/
  `Q` atom tables, `up`, `phases`), Gödel-numerable.
- `decodeMT : FinMT → MultiTier (Fin nE) (Fin nK)` — total decoder.
- `mtOkB : FinMT → Bool` + `mtOkB_iff` — the Boolean checker accepts
  EXACTLY the valid decoded certificates.
- `mtAcceptB_sound` — an accepted code yields a real RCC5 model.
- **`decidableSat_of_codes`** — given a FIXED `codes : List (FinMT × Nat)`
  and `hcompl : Satisfiable C₀ → ∃ p ∈ codes, mtAcceptB p C₀`, returns
  `Decidable (Satisfiable C₀)`. Soundness needs no premise.

So decidability of any fragment reduces to producing `codes` (a bounded,
model-independent enumeration) + `hcompl` (completeness of that
enumeration). Nothing else.

### 22.2 Horizontal ∀PO-free first — gap-free

`satisfiable_iff_hfrag_cert` already gives, for `HFrag C₀`, a certificate
`MultiTier β Empty` with `β = {n // n ∈ mtkNodes root}` (FINITE — a
subtype of a finite list), `κ = Empty` (NO kernels), `tauE = mtk` (labels
⊆ `cl C₀`), `E = eq/dr/po`. No width, no uniformization — the fragment
terminates by modal-depth truncation. The remaining arc, all plumbing:

1. **Encode** the finite `(β, Empty)` external network as a `FinMT`
   (`nK = 0`, `phases = []`, `tauE =` the node labels, `E =` the
   `eq/dr/po` table indexed by list position). Prove
   `mtOkB (encodeHF …) = true` — either transport `mtHF_ok` across the
   `Fin nE ≃ {n // n ∈ mtkNodes}` position bijection, or re-establish the
   obligations for the `Fin`-indexed decode. **This is the fiddly step**
   (index bijection + the four external obligations `propB`/`frameB`/
   `eAllB`/`eExB`).
2. **Bound `codes`**: `mtkNodes.length ≤ K(C₀)` (branching `≤ |cl C₀|`,
   depth `≤ md C₀`), labels are sublists of `cl C₀`. Enumerate all
   `FinMT`s with `nK = 0`, `tauE` entries ⊆ `cl C₀`, `nE ≤ K(C₀)` — a
   finite (huge, but computable — efficiency irrelevant) list.
3. **`hcompl`**: `Satisfiable C₀` →(`extract_hfrag`)→ the certificate →
   (encode) an accepted `FinMT` that lies in `codes` → `decidableSat_of_codes`.

Yields the project's FIRST kernel-checked `Decidable (Satisfiable C₀)`,
on the fragment with no open piece.

### 22.3 Then vertical + mixing

Same skeleton with kernels (`nK > 0`): the certificate is the
`posetKernel`/`posetKernelG` poset. The extra ingredient is the
extraction's **uniformization** — a FRAGMENT-level bounded-width fact
(§21.5), NOT full-logic F6. Do it with the width bound as an explicit
hypothesis first (isolating the one not-yet-closed fact), then discharge
it from the finite-type kernel count + the collapse probes.

The order is deliberate: front-load the gap-free horizontal decidability
(establishing the enumeration + completeness machinery on `nK = 0`), then
extend to the kernel case where the sole open fact is fragment-width.


## 23. Horizontal ∀PO-free is DECIDABLE — done (2026-08-02)

§22's plan is complete. `decidableSat_hfrag (C0) (hfrag : HFrag C0) :
Decidable (Satisfiable C0)` — the project's FIRST kernel-checked
decidability theorem, a genuinely **computable** `def` (the decision is
the finite search `codes.any (fun p => mtAcceptB p.1 p.2 C0)`;
`Classical.choice` appears only in the erased correctness proof, so this
is a real decision procedure, not a vacuous `Classical.dec`).

Pipeline, all certified (0 sorries/warnings):
- `encodeHF` / `encodeHF_mtOk` / `encodeHF_accepts` — encode the mtHF
  certificate as a `FinMT`, prove it valid + accepting (E3s).
- `mtkNodes_length_le` — the certificate is size-bounded by `K(C0) =
  mtkBound C0 (mdepth C0)` (E3t).
- `allListsLen`/`allListsLe`/`allAtoms`, `codes C0` — the fixed
  computable enumeration (labels `allListsLe (cl C0) |cl C0|`; no
  `List.sublists` needed since `mtk`'s elements ∈ `cl C0` and
  `|mtk| ≤ |cl C0|`).
- `encodeHF_mem_codes` — the encoded code lies in `codes`.
- `hfrag_hcompl` — satisfiable ⟹ an accepted code in `codes`.
- `decidableSat_hfrag = decidableSat_of_codes C0 (codes C0)
  (hfrag_hcompl …)`.

No width, no uniformization — the horizontal fragment terminates by
modal-depth truncation. Axioms: propext / Classical.choice / Quot.sound.

**Next (§24): the VERTICAL fragment's decidability** reuses this same
`codes` / `decidableSat_of_codes` machinery with kernels (`nK > 0`). The
assembly lemmas (`posetNet_frame`, `posetKernel_ok`, `posetKernelG_ok`)
and witnesses are already certified; the one open ingredient is the
fragment-level uniformization (§21.5) — a bounded-width fact, NOT the
open full-logic F6.

## 24. THE VERTICAL FRAGMENT IS DECIDABLE — both directions (2026-08-05/06, E4–E5)

§22.3's plan is complete for **both** the ascending (`∃PP`) and descending
(`∃PPI`) vertical fragments. Four `Decidable (Satisfiable C0)` theorems,
all certified (0 sorries/warnings, axioms propext / Classical.choice /
Quot.sound), each with a genuine SAT witness.

### 24.1 The round-robin CONSTRUCTIVE UNIFORMIZATION (the key result)

The §21.5 "uniformization" turned out **not** to require a bounded-width
oracle. The insight: `vkernel1G_ok`'s `k_ex` serves each demand `∃PP.D`
from **whatever phase carries `D`** (`∃ b, b < p ∧ D ∈ phase b`), not one
fixed `G`. So I do not need co-carrying at a point — I need the recurrent
**period** to carry each demand-arg at *some* phase. And that is
**constructible**: guard all demands (`∀PP.(∃PP.Dⱼ)`), then from any
point serve `D₀` (go to a `D₀`-witness), which inherits the guards and
demands `D₁`, serve that, … cycling. Pigeonholing only the sub-sequence
at multiples of `L = |Ds|` gives a recurrent period that is a *multiple*
of `L`, hence covers a whole cycle — every demand-arg. This is
`rr_covers`, and it is a **theorem**, not the open W2′.

So W2′ is discharged for the vertical case. Chain of lemmas (`persistAll`
→ `persistAll_productive` → `rrChain`/`rrPt_serves` → `rr_segment`
[period `= B·L`, multiple of `L`] → `mod_shift_cover` → `rr_covers`).

### 24.2 The four ascending sub-fragments

- `decidableSat_vtower` (E4) — single `∃PP.G` tower. Witness `Cvert`.
- `decidableSat_vtowerG` (E5a–d) — CO-CARRYING multi-demand (one
  self-carrying chain via `vkernel1G_ok`). Witness `Ccar`. The
  `persistAll` guard is **sat-based** (`sat x (∀PP.(∃PP.D))`, not mty),
  so combined-guard concepts (`Clin`'s `∀PP.(∃PP.A₀ ⊓ A₁)`) also fit.
- `decidableSat_vtowerRR` (E5e–l) — the round-robin, NON-CO-CARRYING
  case (distinct/incompatible demands). Witnesses `Calt` (`∃PP.A₀ ⊓
  ∃PP.¬A₀`), `Clin` (combined guard). Uses `codesVB` (the period bound
  parameterized to `B·L`, since round-robin periods exceed `codesV`'s
  single-demand `B`).

### 24.3 The descending mirror (E5n–r)

`decidableSat_vtowerRRI` — the `∃PPI` dual, witness `Cdesc`. Went fast
because the FOUNDATION pre-existed (`persistPPI`, `dbuildChain`,
`dchain_model_ppi/pp`, `dseg_ppi/pp`, `dsegment_kk_pp/ppi`). The one
new piece was `vkernel1GI_ok` (the `up=false` descending kernel: root
ABOVE the chain, `K` reads `pp`, chain serves `∃PPI` via
`cdir false = ppi`) — compiled first try. Then `persistAllI`, `rrChainI`,
`rr_segmentI`, `rr_coversI` were direct mirrors.

### 24.4 ARCHITECTURAL LESSON: the encoding side is direction-agnostic

`encodeMT` / `reindexMT` / `codesVB` / `unitTower_accepted` /
`unitTower_mem_codesVB` **do not care** about `up` (it is a free `boolCol`
field) or `pp` vs `ppi` (`E/K/Q` read the model into `atomTab1`). So
descending required mirroring ONLY the kernel + chain + persist/segment —
and those `d`-lemmas already existed. **No free duality**: `conv∘rho` is
NOT an RCC5 interpretation (composition fails order-wise — counterexample
`ρ(x,y)=ppi, ρ(y,z)=dr, ρ(x,z)=po ∈ comp(ppi,dr)` but `conv(po)=po ∉
comp(pp,dr)={dr}`). So the mirror was genuine, not a reduction.

## 25. MIXING — the design for the last quadrant (2026-08-06, E6)

**Goal:** `decidableSat_mix (C0) : Decidable (Satisfiable C0)` for the
FULL ∀PO-free fragment — concepts with BOTH horizontal existentials
(`∃DR`/`∃PO`/`∃EQ`) AND vertical ones (`∃PP`/`∃PPI`), all `∀` non-`PO`.
This is the one remaining quadrant, and it is a genuine COMBINATION, not a
mirror.

### 25.1 What is done (E6a–b, committed)

- `mixRho` + `mixRho_frame` — the carrier: a `PP`-tower plus one node `nb`
  that is `PO` to every tower point, proven a real RCC5 Frame.
- `cmix_satisfiable` — a genuinely mixed concept `Cmix = A₀ ⊓ ∃PO.A₁ ⊓
  ∃PP.A₀ ⊓ ∀PP.(∃PP.A₀)` is satisfiable in one model (SEMANTIC witness).
- `Cmix_pofree`, `cmix_demands`, `mixCert` (def), `nb_no_ex` — the mixed
  certificate's building blocks.

### 25.2 The KEY discovery: the mixed-CERT machinery is already PROVEN

`MTOkPool`'s `e_ex` has a THIRD disjunct `(r = po ∧ ∃ q ∈ P, q.1 ≠ myTag
∧ c ∈ q.2)` — the **pool `P` serves `∃PO` demands**. `block_of_persistent`
(ascending) / `block_of_persistent_desc` (descending) build a `BlockOk`
carrying BOTH a kernel (`∃PP`/`∃PPI`) AND `∃PO` (via the pool).
`mtOkPool_of_block` → `MTOkPool`; `glueFam_ok` combines clusters
(cross-`PO`, pools cross-reference); `multiTier_sound` → `Satisfiable`.
So a certificate mixing kernels and horizontal `∃PO` is NOT a remaining
task — it EXISTS.

### 25.3 TWO extraction architectures — pick the cleaner one

There are two ways to serve `∃PO` in a mixed certificate:

**(A) Direct external (one cluster, no pool).** If the `∃PO` target is a
DIRECT external in the SAME certificate, plain `MultiTierOk`'s `e_ex`
disjunct 1 (`∃ f, E e f = po ∧ c ∈ tauE f`) serves it — no pool. This is
what `mixCert` does (`∃PO.A₁ → nb`). **Cleaner for a single connected
mixed component.**

**(B) Pool + glue (many clusters).** For `∃PO` targets in OTHER clusters,
the pool routes cross-cluster and `glueFam_ok` combines. Needed when the
horizontal structure has multiple `PO`-separated pieces.

**Recommendation:** the horizontal fragment's own certificate `mtHF` is a
SINGLE `MultiTier {mtkNodes} Empty` that already serves `∃DR`/`∃PO`/`∃EQ`
among its externals via `E`. So the natural mixing certificate is
**`mtHF`-WITH-KERNELS**, architecture (A): the externals are the `mtk`
horizontal nodes (serving `∃DR`/`∃PO`/`∃EQ` directly), and each node that
demands `∃PP`/`∃PPI` gets a kernel. Route: `e_ex` sends `∃DR`/`∃PO`/`∃EQ`
→ externals (`E`), `∃PP`/`∃PPI` → kernels (`K`); `k_ex` sends the tower's
own horizontal demands (`∃PO` etc.) → externals (`K`) or other kernels
(`Q`). No pool, no glue — one certificate.

### 25.4 THE DECIDABILITY STRATEGY (the plan to execute)

Fit the `decidableSat_of_codes` template (as horizontal and vertical did):

1. **Fragment** `MFrag C0`: `∀PO`-free; every `∃` is `∃DR`/`∃PO`/`∃EQ`/
   `∃PP`/`∃PPI`; every `∀` is non-`PO`. (Decidable via `by decide` on a
   Boolean `all` over `cl C0`, like `hfragB`.)

2. **The mixed certificate** `MultiTier {externals} {kernels}` extending
   `mtHF` with kernels (architecture A). Its `MultiTierOk` combines
   `mtHF_ok`'s external handling (`ee_all` on `DR/PO/EQ` edges, `e_ex`
   horizontal routing) with `vkernel1G_ok`/`vkernel1GI_ok`'s kernel
   handling (`kk_*`, `k_ex` vertical), PLUS the cross fields `ek_all` /
   `ke_all` (external↔kernel `∀`-propagation) and `kq_all` (kernel↔kernel,
   VACUOUS in the ∀PO-free fragment since cross-kernel `Q` is `po`/`dr` and
   there is no `∀PO`, and cross-kernel `∀DR` handled by rank). This is the
   crux new construction — a genuine merge of the two `_ok` proofs.

3. **Extraction** (satisfiable ⟹ mixed certificate). This is where the
   HOMOGENEITY problem that blocked the *specific* `mixCert` DISSOLVES:
   the general extraction reads the MODEL's own `mty`s, and the tower `mty`
   recurs by `mty_segment_bounded` (the pigeonhole) — NO per-concept
   bisimulation needed. The horizontal skeleton comes from `mtk`
   (model-type-truncated by modal depth, already finite and certified);
   the towers come from `persistAll`/`persistAllI` + the round-robin.

4. **Codes** `codesM C0` — extend `codesVB` to enumerate mixed `FinMT`
   (both `nE > 1` externals with `DR/PO/EQ` tables AND `nK > 0` kernels).
   The encoder (`encodeMT`) already handles arbitrary `nE`, `nK`, so this
   is enumeration bookkeeping, like `codesV → codesVB`.

5. `decidableSat_mix = decidableSat_of_codes C0 (codesM C0) (mix_hcompl)`.

### 25.5 Difficulty assessment (honest)

- **Step 2 (the merged `MultiTierOk`)** is the crux — a genuine merge of
  `mtHF_ok` (horizontal) and the round-robin kernel proof (vertical),
  with the `ek_all`/`ke_all`/`kq_all` cross-fields. ~150–250 lines. The
  `∀PO`-free vacuity (`mty_no_all_po`) discharges all `PO`-edge
  obligations; the `DR`-edge cross-obligations are the real content.
- **Step 3 (extraction)** reuses `mtk` (horizontal) + `persistAll` +
  round-robin (vertical); the homogeneity problem is sidestepped by
  `mty_segment_bounded`. Moderate.
- **Step 4 (codes)** is bookkeeping.

The SPECIFIC `mixCert` (E6b) is NOT on the critical path — it is a
demonstration whose SAT is already witnessed by `cmix_satisfiable`, and
its homogeneity obstacle does not arise in the general extraction. **Do
not finish `mixCert_ok`; go straight to the general `MFrag` decidability
via architecture (A) + `mty_segment_bounded`.**

### 25.6 The one genuine open question — and its resolution (E6c)

Whether `mtk` (horizontal, modal-depth truncated) and the vertical
round-robin (period-bounded) compose into ONE finite certificate whose
size is computably bounded by `K(C0)`.

**Sharpening (E6c).** The merge is NOT a mechanical extension of `mtHF`,
because the two termination arguments are *different in kind*: `mtk`
truncates by MODAL DEPTH, which would CUT an `∃PP` tower (unbounded
depth); the vertical demands instead loop via PIGEONHOLE (period `B·L`).
And the demands INTERLEAVE: a horizontal node demands `∃PP` → a tower; the
tower points demand `∃PO` → new horizontal nodes; those demand `∃PP` →
new towers; … So a single measure does not obviously bound the whole.

**Resolution (the termination argument that works).** Use a **lexicographic
/ combined measure**:
- The `∃PP`/`∃PPI` steps (going up/down a tower) do NOT decrease modal
  depth — they are absorbed by the pigeonhole (a tower recurs within
  `B·L` rungs, `mty_segment_bounded`), so each tower is a FINITE kernel.
- The `∃DR`/`∃PO`/`∃EQ` steps (horizontal, and the tower points' own
  horizontal demands) DECREASE modal depth (`cl_ex_mdepth_lt`) — so the
  horizontal branching, INCLUDING branches spawned off tower points,
  is bounded by `mdepth C0`.

So the interleaving terminates: vertical loops are pigeonhole-finite,
horizontal descent (from anywhere, including off towers) is depth-finite.
The certificate is a horizontal skeleton (depth-bounded) each of whose
nodes may carry a kernel (period-bounded), and the kernels' horizontal
demands re-enter the skeleton at STRICTLY smaller depth. The size bound is
therefore the depth-`mdepth` unfolding of (nodes × ≤ `B·L`-kernels) —
finite, computable, NOT F6.

**So the last quadrant is tractable, not open.** The remaining work is the
FORMALIZATION (~200–250 lines): (i) generalize `mtk`/`mtkNodes` so a node
whose type carries an `∃PP`/`∃PPI` demand attaches a round-robin kernel
instead of recursing by depth; (ii) the merged `MultiTierOk` (`mtHF_ok`
externals + round-robin kernels + `ek/ke/kq` cross-fields, `PO`-edges
vacuous by `mty_no_all_po`); (iii) `codesM` + `mix_hcompl` +
`decidableSat_mix = decidableSat_of_codes`. The checker soundness
(`mtAcceptB_sound`) is already generic over `nE`/`nK`, so only the
COMPLETENESS side (the extraction above) is new.

### 25.7 Progress (E7, 2026-08-06/07): the merge's coordination is proven

The externals+kernels **soundness coordination** is now certified in three
landed lemmas (all 0-sorry, axioms propext/Classical.choice/Quot.sound):

- **`mixKernel_ok`** / **`mixKernelI_ok`** — arbitrary externals `g : β → α`
  (full `mty` labels) + a SINGLE ascending / descending kernel. The
  cross-fields `ek_all`/`ke_all` ride one stabilization `hstab` and are
  DIRECTION-AGNOSTIC (never mention pp/ppi), so the descending mirror is
  byte-identical.
- **`mixKernels_ok`** — the FULL multi-kernel form: arbitrary externals + a
  family of kernels `ck : κ → ℕ → α` with per-kernel `dir : κ → Bool`.
  Generalizes both `mixKernel` (κ=Unit) and `vkernel2` (β=Empty). `kq_all`
  NON-vacuous (cross-kernel ∀ via the rectangle `hrectQ`); `k_ex` with the
  cross-kernel disjunct; `kk_pp`/`kk_ppi` branch on `dir k`
  (`segment_*`/`dsegment_*`). This is exactly step-2's "merged `MultiTierOk`".

KEY finding: all three are **C0-general** (no `POFree` hypothesis) — `ee_all`
is pure `mty_all` (universal closure of `mty`). ∀PO-freeness is what makes the
demand hypotheses (`he_ex`/`hk_ex`) SATISFIABLE in the extraction, not what the
soundness needs.

**The remaining crux — the `mtk`/`mty` finiteness seam.** These lemmas use
UNIFORM full-`mty` externals, so `β` is arbitrary (not yet finite). The
extraction needs FINITE `β`, which (per §25.6) comes from `mtk`-truncated
externals (`mtk C0 I x k = (mty C0 I x).filter (mdepth · ≤ k)`, depth-bounded
node set). Porting the merge to `mtk` externals splits cleanly:
- `ek_all` (external `mtk`-∀ → kernel `mty`-phase): EASY — lift `mtk`→`mty` by
  `mem_mtk`, then `mty_all` (kernel phases are full `mty`, no truncation).
- `ke_all` (kernel `mty`-∀ → external `mtk`): the HARD seam — `mty_all` gives
  `c ∈ mty(g f)`, but the truncated external needs `c ∈ mtk(g f) kᶠ`, i.e.
  ALSO `mdepth c ≤ kᶠ`. This depth-accounting is the design's flagged "one
  genuine open question" (§25.6). It is NOT resolved by `mixKernels_ok`.

So E7 de-risks the COORDINATION (all cross-fields proven, both directions,
multi-kernel, C0-general) but the FINITENESS bridge (`ke_all` depth-matching
under `mtk` truncation) + the extraction remain. Two routes for the bridge:
(a) `mtk` truncation — avoids horizontal uniformization but has the `ke_all`
depth seam (the design's choice); (b) type-quotient externals — full `mty`
(no depth seam) but reintroduces horizontal uniformization (W2′-horizontal,
NOT obviously constructive, unlike the vertical round-robin). Route (a) is the
plan; the `ke_all` depth obligation is the next thing to pin down.

Commits: fe0c5be (`mixKernel_ok`), 4b43819 (`mixKernelI_ok`), 0db11e7
(`mixKernels_ok`).

### 25.8 The `ke_all` depth seam — RESOLVED (wp89, 2026-08-07): PO-default the kernel edges

`verification/python/wp89_keall_depth_seam.py` settles the "one genuine open
question" concretely. It builds a ∀PO-free villain
`C0 = (∀DR.∀DR.∀DR.∀DR.A) ⊓ ∃PP.⊤ ⊓ ∃DR.∃DR.⊤` (mdepth 4) and a genuine
finite-set RCC5 model (`R ⊂ T`, `R DR g1 DR g2`, `T DR g2`, A everywhere).

- **The naive route (K read off the model, as in `mixKernels`) is BROKEN.**
  The tower/kernel universal `∀DR.c` (`c` mdepth 3) fires at the grandchild
  `g2` via the real `K g2 = DR`, but `c` is DROPPED from `mtk(g2, 2)` (mdepth
  3 > budget 2). `ke_all` fails on a *satisfiable* concept — pure
  over-truncation (the naive frame is still closed). So node-set finiteness
  (§25.6) genuinely does NOT imply the truncated cert satisfies `ke_all`; it
  was a hidden clause.
- **The FIX: PO-default the kernel's `K`/`Q` to non-kernel-adjacent nodes**,
  exactly the trick `mtHF` already uses for its horizontal `E` (non-tree
  edges = PO, vacuous under ∀PO-freeness via `mty_no_all_po`). The probe
  confirms this makes `ke_all` VACUOUS and keeps the combined frame
  composition-closed on the villain.

**Architectural consequence for step 3 (extraction).** The extraction must
NOT read `K`/`Q` off the model. It should build the kernel edges like `mtHF`
builds `E`: real relation only on the bounded ADJACENT set (the attaching
node, and whatever the kernel genuinely needs for its own demand-service),
PO elsewhere. Then:
- `ee_all`/`ke_all`/`kq_all` are VACUOUS on all PO-defaulted edges (no ∀PO in
  closure) — the depth seam never bites, because deep externals connect to
  kernels by PO, not the real DR.
- the real-relation hypotheses of `mixKernels_ok` (`hstab`, `hrectQ`, the
  real `K`/`Q` reads) apply only to the small adjacent set, where budgets are
  adequate (adjacency = one step, budget = parent − 1 ≥ any firing depth).
- the new obligation is a `mtHF`-style FRAME lemma for the PO-defaulted
  combined network (like `mtHF_frame`/`symDrPo_frame`, now spanning externals
  AND kernel bases) — provable, not open.

So the seam is closed at the DESIGN level: the merge lemma stays as proven
(`mixKernels_ok`, real edges), and the extraction feeds it PO-defaulted far
edges so the truncation is harmless. Route (a) survives; route (b)
(type-quotient / horizontal uniformization) is not needed. Next Lean step: the
PO-default combined-frame lemma + the `mtk`-with-kernels node construction.

### 25.9 The full architecture, VALIDATED end-to-end (wp90, 2026-08-07)

`verification/python/wp90_mtk_kernel_architecture.py` validates the WHOLE
`mtk`-with-kernels extraction — for BOTH kernel directions and mixed — before
Lean. Uniforming observation: every `MultiTierOk` universal clause
(`ee_all`/`ek_all`/`ke_all`/`kk_*`/`kq_all`) is ONE property — a `∀r.c` at `x`
with `ρ(x,y)=r` forces `c ∈ label(y)` — and every existential clause is
`∃r.c` at `x` ⟹ a witness `y`. So a truncated cert is valid iff its completed
network is a FRAME and satisfies these two, which wp90 checks over all node
pairs. Results (all 0 mismatches): **ascending, descending, AND mixed
canonical certs are FULLY VALID** (frame-closed + ∀-prop + ∃-ful); the naive
certs (real edges + truncation) FAIL ∀-prop — the wp89 seam.

Three architectural facts the probe pinned down (these are the Lean spec):

1. **The far-edge policy is the CANONICAL COMPLETION, not naive PO-default.**
   A greedy "relax real → PO" gets stuck (order-dependent: `R→g2` can't relax
   until `g2→T0` does, and vice-versa). The correct rule: adjacency edges
   (demand tree + kernel-attaching) = real; then FORCE every
   singleton-determined edge to fixpoint (`comp(PP,PP)={PP}` forces tower
   transitivity `R→T1`; `comp(PP,DR)={DR}` forces the descending `B0→g1`); PO
   the genuinely-free rest. Closed BY CONSTRUCTION: a free edge sits in no
   singleton cell, and PO is in every non-singleton cell (the escape valve).
   So the Lean `frame_q` target is "the forcing completion is a frame" — a
   finite patchwork, NOT the simple symDrPo+kernel special case I first
   attempted (that case doesn't force the descending/tower edges).
2. **Descending works** (route (a) confirmed for `∃PPI`): the forced edge
   `B0→g1` (`B0` a part of `R`, `R DR g1`) is DR, and `g1`'s budget
   (`k_v − 1`) always covers the firing universal's argument (`mdepth ≤
   k_v − 1`); deeper nodes (`B0→g2`) relax to PO (`comp(DR,DR)` non-singleton).
   No forced-edge ever hits an under-budget node.
3. **Kernel phases SPAWN their own horizontal children** (§25.6's "re-enter the
   skeleton"): a tower point carrying `∃DR.∃DR.⊤` needs its own DR-witnesses
   added as externals adjacent to the phase (budget = phase budget − 1). Both
   `∃-ful` and the budget accounting then hold. Phases truncate at the
   ATTACHING node's budget.

Net: the architecture is sound in all quadrants; the Lean extraction spec is
(1)+(2)+(3) above. The remaining Lean work is faithful transcription — the one
non-trivial new lemma is the forcing-completion frame lemma (finite patchwork).

## 26. Completeness/extraction, and the precisely-localized general-theorem gap (2026-08-12)

The extraction (completeness) direction — `Satisfiable C0 → valid certificate`
— is now built end-to-end for the SINGLE-TOWER case, with the remaining gap
localized to one construction.

**What is certified (completeness side):**
- `extract_mtkKernel` — a model + its demand facts BUILD a valid `MultiTierOk`
  (the `mtk`-with-kernels single-tower cert): horizontal skeleton `mtkNodesH`
  + one ascending kernel, PO-default cross-edges. The routing lemmas
  `mtk_ee_all` / `mtk_e_ex` / `mtk_k_ex` discharge its hypotheses.
- `mtk_k_ex` routes a phase's HORIZONTAL `∃PO.D` OUT to a non-root external via
  the PO `K`-edge (route-1 of `k_ex`), sound because `∀PO`-free. This removed
  the "clean-phase" restriction: phases need not be horizontally trivial.
- `extract_from_tower` — the general single-tower theorem: from a `PP`-tower
  (root carrying `C0`) + syntactic `∃PPI`-freeness + a recurrence, discharges
  ALL structural inputs (`hv0pp` via `pp_chain_below`, `hno_ppi` via
  `no_ppi_demand`, root, read-off), leaving EXACTLY two model-side cleanliness
  obligations: `hpp_v0` (skeleton `∃PP`-free) + `hk_class` (phases demand only
  served `∃PP`/`∃PO`/`∃EQ`).
- Three witnesses span the mixing classes, all through the general
  `extract_from_tower`: `cvert_via_tower` (degenerate skeleton),
  `cmerge_via_tower` (non-degenerate, clean phases), `cmix_via_tower`
  (non-degenerate, HORIZONTAL phase demands).
- **`mtkKernel_nopo`** — the single-kernel certs are `MTNoPo`, hence GLUABLE
  by `glueMTOk`. Certificate-level patchwork (all-cross-`PO` amalgamation of a
  family of towers) was already certified (`glue_ok`/`glueFam_ok`/`glueMTOk`),
  gated on `MTNoPo`; `mtkKernel_nopo` brings the full horizontal+vertical certs
  under that gate (previously only pure `vkernel`s, via `vkernel_nopo`).

**The precisely-localized remaining gap (the general theorem).** The honest
`Satisfiable C0 → Decidable`-enabling theorem needs a certificate over a SINGLE
FINITE `β`. Two facts pin the gap:
1. `glueFam (F : Fin B → MultiTier β κ) : MultiTier (Fin B × β) (Fin B × κ)`
   requires a UNIFORM `β` across all towers. Extracting from one model's several
   towers gives per-tower node-subtypes `{n // n ∈ mtkNodesH root_b}` — DIFFERENT
   `β` per root. So gluing per-tower extractions is not immediate.
2. From an ARBITRARY (dirty) model, a skeleton node might carry `∃PP` (→ its own
   nested tower) or a phase might carry `∃DR` (→ the "summit": phases spawn
   adjacent DR-children as externals, §25.9 fact 3). So `extract_from_tower`'s
   cleanliness hypotheses are model-dependent.

So the remaining general-theorem work is the **uniform finite-`β`
multi-tower/multi-kernel node construction**: a single `β = ` (a finite node
set closed under BOTH horizontal demands AND kernel-spawning, bounded by
`K(C₀)`) that covers every tower of the model at once — then `glueMTOk` (with
`mtkKernel_nopo`) assembles, and cleanliness is discharged by the construction
(nodes are spawned exactly where demands need them). This is the same
"general `mtk`-with-kernels construction" flagged since E6 — now with BOTH its
halves' interfaces certified (gluability = `mtkKernel_nopo`; single-tower
extraction = `extract_from_tower`), so what remains is the finite uniform-node
assembly, not the per-tower soundness. It is formalization (bounded by `K(C₀)`
counting + the §25.9 forcing-completion frame), NOT the open `F6`/`W2′` problem
— that is the FULL logic's obstacle, which `∀PO`-freeness removes.

## 27. The multi-kernel machinery, DONE — and the precise summit (2026-08-12)

The whole **multi-kernel certificate machinery** is now certified (0 sorries/
warnings), and the general extraction is complete for the FLAT sub-fragment.

**Certified this round:**
- `po_default_multi_frame` — the multi-kernel PO-default frame (κ kernels over a
  `symDrPo` external skeleton, cross-`Q` PO-default). The cross-`Q` forcing that
  made the full-`mty` multi-kernel hard is DISSOLVED by PO-default (every
  cross-kernel triangle closes via `po_mem_comp_left/right` + `comp(po,po)=all`);
  two kernels may even share an attach point, no injectivity.
- `mtkKernels`/`mtkKernels_ok`/`mtkKernels_nopo` — the mtk-truncated multi-kernel
  certificate is valid + gluable. `kq_all` is VACUOUS (cross-`Q`=PO, no `∀PO` in
  mtk phases) — the payoff of `∀PO`-freeness.
- `cnest`/`cnest_generic_satisfiable` — the first genuine TWO-kernel extraction
  (nested two-tower `Cvert ⊓ ∃PO.Cvert` on the all-cross-PO carrier), validating
  `mtkKernels_ok` end-to-end.
- `extract_flat_towers` — `cnest` generalised to ARBITRARY `κ`: the "N cross-PO
  towers" extraction (analogue of `extract_from_tower` for κ kernels). Clean
  routing hyps; `cnest_via_flat` witnesses `cnest` as its `κ=Bool` instance.

**The precise remaining summit — the NESTED node construction.** `extract_flat_
towers` handles the FLAT case: bases only mutually PO, and kernel phases route
their horizontal demands BACK to existing bases. The general `decidableSat_
pofree` needs two things `extract_flat_towers` does not do:

1. **DR/PO structure AMONG skeleton nodes** (not just cross-PO). Concepts with
   `∃DR` between nodes need `dadj` = real DR-adjacency (the `dadjBK`/`symDrPo`
   machinery of `mtHF`), with the `dadj`↔model correspondence. The frame already
   supports it (`po_default_multi_frame` takes arbitrary `dadj`); the work is the
   `hee`/`he_ex` discharge over a DR skeleton (via `all_into` on the forced DR
   edge). This is a bounded extension.

2. **Phases spawning NEW nodes — the CRUX.** A kernel phase's `∃DR`/`∃PO`/`∃EQ`
   demand may need a node NOT in the root's horizontal closure. So the skeleton
   `β` must be closed under BOTH the horizontal demands of skeleton nodes AND the
   horizontal demands of kernel phases — a MUTUAL recursion (skeleton nodes with
   `∃PP` → kernels; kernel phases with horizontal demands → new skeleton nodes;
   those with `∃PP` → more kernels). The finiteness is by `mtk`-truncation: a
   phase at budget `k` has demands of `mdepth ≤ k`, its children have budget
   `k-1`, terminating at `0`; the total node+kernel set is `K(C₀)`-bounded. The
   **phase-horizontal-COVERAGE lemma** — every phase demand is served by a node
   in `β` — is the keystone, the multi-kernel analogue of `mtkNodesH_covers`.

3. **Finiteness for decidability.** `Fintype β`/`Fintype κ` + the `K(C₀)` size
   bound + a `codesM` enumeration → `Decidable (Satisfiable C0)` via
   `decidableSat_of_codes`. (The single-model → cert extraction is completeness;
   decidability additionally needs the finite code enumeration.)

So the summit is a well-defined recursive construction (the `mtkNodesH` skeleton
generalised to co-recurse with kernels, + the coverage lemma + finiteness), NOT
open mathematics — every ingredient's interface is certified (frame, cert
validity, gluability, flat extraction, single-tower routing `mtk_ee_all`/
`mtk_e_ex`/`mtk_k_ex`). It is the genuine remaining formalization toward
`decidableSat_pofree`.

## 28. Item 2, precisely: phase-∃DR and the forcing-completion frame (2026-08-12)

`extract_skel_towers` (item 1) gives a DR/PO skeleton among the bases with
`∃DR`-CLEAN phases. Item 2 is the phase-spawning case, and pinning down WHY it is
hard is itself progress.

**The obstruction — the phase→external edge.** In `mtkKernels` the kernel↔external
edge is `K k e = if e = v0 k then ppi else po` — the PO-default, deliberately in
`{ppi, po}`. A tower phase reaches an external only through `K` (composed with
`phase PPI base`). So a phase can serve `∃PO`/`∃EQ`/`∃PP` but **NOT `∃DR`** (no DR
`K`-edge). That is exactly why item 1 keeps phases `∃DR`-clean.

**The fork.** Serving phase-`∃DR` needs a DR `K`-edge to the phase's DR-witness.
Two `K` policies exist in the artifact:
- `mtkKernels` — PO-default `K` (`{ppi,po}`), `mtk`-TRUNCATED labels: finite
  (`Fintype β` reachable), `ke_all` clean (the wp89 seam avoided), but no
  phase-`∃DR`.
- `mixKernels` — `K := I.rho (ck k (ik k)) (g e)` READ OFF the model (can be DR),
  FULL `mty` labels: serves phase-`∃DR`, but `mty` is not truncated (the
  finiteness seam) and a naive read-off-`K` + `mtk`-truncation breaks `ke_all`
  (wp89: a deep kernel universal fires at a shallow external, its argument
  truncated away).

So item 2's phase-`∃DR` sits in genuine tension: **phase-DR needs read-off `K`;
decidability needs `mtk`-truncation; the two collide at the `ke_all` depth seam.**

**The resolution (wp90 / §25.9) — the forcing-completion frame.** The correct
`K`/`Q` far-edge policy is NEITHER naive read-off NOR blanket PO-default: it is
the CANONICAL COMPLETION. Adjacency edges (a phase's demand to an ADJACENT
budget-safe child) are REAL (so a phase-`∃DR` to a child at budget `k-1`,
`mdepth arg ≤ k-1`, is a genuine DR edge); then FORCE every singleton-determined
edge (`comp(PP,DR)={DR}` etc.) to a fixpoint; PO the genuinely-free rest (free
edges sit in no singleton `comp` cell, and PO ∈ every non-singleton cell). This
keeps labels `mtk`-truncated (finite) AND serves phase-`∃DR` at adjacency, with
the depth seam avoided because the DR edge is budget-safe by construction.

**So item 2's keystone is the FORCING-COMPLETION FRAME** — a frame lemma
generalising `po_default_multi_frame` where SOME kernel/cross edges are real
(adjacency + forced singletons) rather than all PO-defaulted. This is the "one
non-trivial new lemma" §25.9 flagged. It is strictly harder than
`po_default_multi_frame` (a real DR `K`-edge FORCES the child's other edges via
composition — the completion is a finite patchwork, not a free PO fill), and it
must interlock with the phase-child budget accounting (adjacency at `k-1`, deeper
edges PO-defaulted) and the coverage lemma (every phase demand served by an
adjacency child or an existing node).

**What is certified (the ingredients):** `po_default_multi_frame` (the all-PO
special case), `mtkKernels_ok` (the PO-default cert), `mixKernels_ok` (the
read-off cert, full `mty`), the finite `comp`-forcing facts (`po_mem_comp_*`,
`segment_kk_pp/ppi`), the single-tower routing. **What remains (the summit):** the
forcing-completion frame + phase-child spawning (adjacency-real DR `K`-edges) +
the coverage lemma + `Fintype`/`codesM`. This is the genuine research frontier —
a substantial construction, not a wrapper.

## 29. Item 2 — phase-∃DR, CERTIFIED END-TO-END (2026-08-13)

Item 2 (the phase-spawning summit) is now certified as a working mechanism.
`extract_skel_towers` (§ item 1) kept phases `∃DR`-clean because a tower phase
reaches externals only via `K`, and the PO-default `K` has no `DR` edge. Item 2
gives phases a `DR` edge — the forcing-completion frame — and wires it into a
valid certificate that serves phase-`∃DR`, demonstrated end-to-end.

**The certified chain (all 0-sorry, propext/Classical.choice/Quot.sound):**
1. **Forcing-completion frame** — `K` = `PPI` to attach `v0 k` / `DR` to `k`'s
   children (`kdr k e`) / `PO` else; cross-kernel `Q` = `PO`. Three bricks:
   - `po_dr_asc_frame` — one DR-child, one kernel. The DR edge is FORCED
     (`comp(PP,DR)=comp(DR,PPI)={DR}`): the child must be `DR`-adjacent to the
     attach (`hcoh`). Everything else lands in non-singleton comp cells.
   - `po_dr_multi_child_frame` — many DR-children (`kdr : β → Bool`), one kernel.
     Children's mutual relations FREE (`comp(DR,DR)=all`); only child↔attach
     forced.
   - `po_dr_multi_kernel_frame` — many kernels, each with its children, full
     generality. Cross-kernel triangles ABSORB any `K` values via PO-default
     (`hKr` + `decide`); ext-ext-through-one-kernel = the multi-child forcing.
2. **The `∀DR` propagation** — `podefault_ke_dr` (phase's `∀DR.cc` → child) and
   `podefault_ek_dr` (child's `∀DR.cc` → phase). Both via `all_into` (same-budget
   membership transfer) followed by `mem_mtk.mpr` + `omega` on `mdepth`. Enabled
   by the munf fact `munf (.inr(k,_)) (.inl f) = K k f`: every tower phase relates
   to external `f` via the base's `K`-edge, so a base-level DR-child is `DR` to
   ALL phases in munf; sound iff the child is `DR` to all phases in the
   label-model (`hdr`, geometrically a disjoint-region child).

   **Budget SLACK (2026-08-13, commit afb4262).** The two `_dr` lemmas were
   generalized from budget-EQUALITY (`bud f = bud v0`) to budget-SLACK:
   `podefault_ke_dr` needs only `bud v0 ≤ bud f + 1`, `podefault_ek_dr` only
   `bud e ≤ bud v0 + 1`. So a DR-served child may sit at a budget STRICTLY BELOW
   its phase. This is the termination prerequisite for the general recursion: a
   `∀DR.cc` at a phase of budget `b` carries `mdepth cc ≤ b−1`, so its DR-child
   fits at `b−1` and the skeleton→kernel→child recursion is well-founded on the
   budget. `mtkKernelsDR_ok`'s `hdr` now yields both slack bounds; the `Cpdr`
   witness supplies them by `omega` (trivially, at equality — the strict-`<` path
   is INFRASTRUCTURE, exercised by the coming general construction, not yet by a
   standalone witness).
3. **The certificate** — `mtkKernelsDR` / `mtkKernelsDR_ok` / `mtkKernelsDR_nopo`.
   `frame_q` = the multi-kernel forcing frame; `ke_all`/`ek_all` = the `_dr`
   lemmas; `kk_*`/`kq_all` as `mtkKernels_ok`; routing `hee`/`he_ex`/`hk_ex`
   with DR `K`-edges (phase's `∃DR.D` → child via `k_ex` disjunct-1). New model
   hypotheses: `hcoh` (frame coherence) + `hdr` (children `DR` to every phase,
   matching budget).
4. **The witness** — `cpdr_generic_satisfiable`. `Cpdr = Cvert ⊓ ∃DR.A₁ ⊓
   ∀PP.(∃DR.A₁)` on the cross-`DR` carrier `drRho` (a frame because
   `comp(PP,DR)={DR}` propagates DR down the tower). Every tower PHASE demands
   `∃DR.A₁` (via `∀PP`), served by the child `(true,0)` through the forced `DR`
   `K`-edge. The first phase-level `∃DR` extraction.

**What remains toward `decidableSat_pofree`.** The forcing mechanism is done; two
standing pieces remain:
- **The general node construction (coverage).** A single uniform FINITE node set
  that unifies the horizontal skeleton (`mtkNodesH`), the kernels (`∃PP`-nodes),
  and their DR-children (`∃DR`-at-phase witnesses), built from an ARBITRARY
  satisfiable ∀PO-free concept, `K(C₀)`-bounded by mtk-truncation. This is the
  mutual skeleton↔kernel↔child recursion + the coverage lemma (every demand
  served by a node in the finite set). Every INGREDIENT is now certified (frame,
  cert validity, gluability, all the extraction engines, the routing lemmas); the
  remaining work is the finite uniform assembly + coverage.
  - **`extract_dr_children` (2026-08-13, commit fda9413).** The phase-`∃DR`
    pipeline is now a REUSABLE ENGINE — parallel to `extract_skel_towers` but on
    `mtkKernelsDR_ok`: given the model correspondences + the `hee`/`he_ex`/`hk_ex`
    routing + a root, it discharges `Satisfiable C0` (β = all externals incl.
    DR-children via `kdr`; κ = kernels; `bud : β → Nat` per-node with the
    budget-slack). So the coverage step no longer has to re-thread the cert +
    `multiTier_sound`; it only has to PRODUCE β/κ + the routing. `Cpdr` now goes
    THROUGH the engine (non-vacuous against β=Bool/κ=Unit). The extract engines
    for the fragment are now: `extract_hfrag` (horizontal), `extract_flat_towers`
    / `extract_skel_towers` (base-`∃`/`∃PP` towers with a DR/PO skeleton),
    `extract_dr_children` (phase-`∃DR`). The missing engine is the one that
    UNIFIES them (a β-node with BOTH a horizontal subtree AND its own kernels)
    + coverage — the summit.
- **`Fintype`/`codesM`** — finite `β`/`κ`, the `K(C₀)` size bound, a `codesM`
  enumeration → `Decidable (Satisfiable C0)` via `decidableSat_of_codes`.

So the two conceptual hearts of the fragment (mtk truncation for the horizontal
width; the forcing-completion + same-budget children for phase-`∃DR`) are both
certified. The remainder is the finite-assembly engineering the whole campaign
has been converging on — NOT the open `F6`/`W2′` problem, which is the FULL
logic's obstacle that `∀PO`-freeness removes.

## 30. The summit, precisely: the unifier + coverage + decidability (2026-08-13)

With `extract_dr_children` (§29) the phase-`∃DR` pipeline is a reusable engine.
This section pins down EXACTLY what is left for `decidableSat_pofree`, grounded
in the concrete artifacts that already exist, so the remaining construction is a
known quantity rather than open research (the open research — `F6`/`W2′` — is the
FULL logic's, which `∀PO`-freeness removes).

### 30.1 The decidability skeleton already exists per-quadrant

Every certified quadrant is `decidableSat_of_codes C0 (<codes>) (<hcompl>)`:
- `decidableSat_hfrag` = `codes C0` + `hfrag_hcompl`.
- `decidableSat_vtower…` = `codesV C0` + `vtower_hcompl…`.
- `decidableSat_Cmix` = `codesMCmix` + the `Cmix`-specific completeness (the
  FIRST mixed one, but for the single witness `Cmix`).

`decidableSat_of_codes` runs `codes.any mtAcceptB`; soundness is
`mtAcceptB_sound` (done, general). The ONLY per-quadrant obligation is
`hcompl : Satisfiable C0 → ∃ p ∈ codes, (p.1).mtAcceptB p.2 C0 = true`.

So the summit = produce, for the FULL ∀PO-free fragment:
1. `codesM C0` — a `K(C₀)`-bounded `List (FinMT × Nat)` enumeration.
2. `pofree_hcompl : Satisfiable C0 → ∃ p ∈ codesM C0, mtAcceptB …` — the
   extraction + encoding.
Then `decidableSat_pofree C0 (h : POFree C0) := decidableSat_of_codes C0
(codesM C0) (pofree_hcompl C0 h)`.

### 30.2 What the engine already covers (so is NOT missing)

`mtkKernelsDR` / `extract_dr_children` are more general than the `Cpdr` witness
uses:
- `dadj : β → β → Bool` is an ARBITRARY symmetric DR/PO skeleton among externals
  — so externals may be a full horizontal `mtkNodesH`-style set, not just
  base+child.
- `v0 : κ → β` assigns each kernel its base — and NOTHING forces the base to be a
  "root": a kernel's base can be ANY external, including a DR-child. So NESTING
  (an external with its own `∃PP`-tower) is already expressible in the frame.
- `bud : β → Nat` is per-node with the budget-slack (§29), so DR-children (and,
  by the same token, deeper horizontal descendants) sit at a strictly decreasing
  budget — the well-founded measure.

Hence the missing content is NOT a new frame or a new merge theorem. It is:

### 30.3 The two genuinely-missing pieces

**(A) Coverage — produce β/κ + routing from a model.** Given `POFree C0`, a model
`I`, and `x0 ⊨ C0`, build a FINITE node set and discharge `hee`/`he_ex`/`hk_ex`/
`hdr`/`hcoh`:
- β = the mtk-truncated horizontal closure of the relevant nodes (root x0, each
  kernel phase, each DR-child), `mtkNodesH`-style, recursion on budget.
  `mtkNodesH_covers` is the horizontal template; the mixed recursion adds, at
  each node with a persistent `∃PP` (resp. `∃PPI`) demand, a kernel via
  `block_of_persistent` (resp. `block_of_persistent_desc`).
- The routing:
  - `he_ex` horizontal (`∃DR`/`∃PO`/`∃EQ`) → a sibling external (the mtkNodesH
    coverage); vertical (`∃PP`) → the node's own kernel (the `k`-disjunct, `conv
    K = pp`).
  - `hk_ex` phase (`∃DR` → a DR-child; `∃PO`/`∃EQ` → an external; `∃PP` → up the
    tower).
  - `hee` — `mty_no_all_po` kills every `∀PO`; `∀DR`/`∀PP`/`∀PPI`/`∀EQ` fire via
    `all_into` / the segment lemmas (already the shape inside `mtkKernelsDR_ok`).
- Termination: budget strictly decreases into horizontal descendants and
  DR-children (§29 slack); `∃PP`/`∃PPI` go to kernels whose PERIOD is finite
  (`mty_segment_bounded`), not into the budget recursion. So the node set is
  finite. This is the "which elements → externals vs kernels" decision the
  campaign has flagged since E3: the answer is LOCAL — a node's persistent
  vertical demand spawns a kernel, everything else is a budget-decreasing
  external.
- Descending (`∃PPI`) needs the descending-kernel arm: either extend
  `mtkKernelsDR` to `dir : κ → Bool` (mirror `mixKernels`' bidirectional
  `kk_pp`/`kk_ppi` + a PPI-forcing `K`-edge for descending kernels), or glue an
  ascending block and a descending block with `glueMTOk` (both are `MTNoPo` via
  `mkBlock_nopo`, so gluable). The bidirectional single-engine route is cleaner.

**(B) Encode + count.** `codesM C0`:
- Bound `|β|` by `K(C₀)` (the number of mtk-node-labels reachable within
  `mdepth C0`; `mtkNodes_length_le` is the horizontal precedent) and `|κ|`
  likewise (one kernel per persistent vertical demand type, `≤ K(C₀)`).
- Enumerate `FinMT` codes over (root label, external labels `≤ |β|`, kernel phase
  lists `≤ |κ|` each of period `≤ K(C₀)`) — `allListsLe` is the enumerator
  precedent; `codesMCmix` is the concrete mixed precedent.
- `pofree_hcompl` = (A) gives a finite `mtkKernelsDR`-cert ⟹ `encodeMT_mtOk`
  (reindex β/κ to `Fin`) ⟹ `mtAcceptB_complete` (the code is accepted) ⟹ the
  code ∈ `codesM C0`.

### 30.4 Order of work

1. Bidirectional `mtkKernelsDR` (add descending kernels) — bounded, mirrors
   `mixKernels`. Gives a single engine covering `∃PP` AND `∃PPI` at phases +
   bases.
2. `mixNodes` finite node set + `mixNodes_covers` (the coverage recursion on
   budget, spawning kernels at persistent vertical demands) — the hard piece, but
   `mtkNodesH_covers` is the template and the measure is in place.
3. `codesM` + `pofree_hcompl` + `decidableSat_pofree` — mechanical, `codesMCmix`/
   `encodeMT_mtOk`/`mtAcceptB_complete` are the templates.

None of (1)–(3) is `F6`/`W2′`. Each is finite-combinatorial assembly over
certified parts. The honest status stays: three quadrants + the mixing pipeline
certified GENERAL/end-to-end, UNREVIEWED; `decidableSat_pofree` is the assembly
of §30, not yet done; full-logic `ALCI_RCC5` decidability remains OPEN.

## 31. The AscMix coverage — refined design (2026-08-13)

`AscMix C0` (§ commit ea89598) = `POFree C0` ∧ ∃PPI-free. The first mixing
decidability target, because its coverage recursion is well-founded on the
BUDGET alone. This section records the coverage design worked out toward
`decidableSat_ascmix`.

### 31.1 Why budget-termination suffices (no §21)

Every kernel is ascending. Two ways a fresh kernel is reached:
- **horizontal** — a kernel base that is a `∃DR`/`∃PO`/`∃EQ` witness or a DR-child
  of a phase: at budget−1 (the horizontal measure decreases).
- **same-direction vertical nesting** — a kernel serving `∃PP.G` where `G` itself
  carries a persistent `∃PP.G'` (e.g. `∃PP.(∃PP.G')`). A phase carries `∃PP.G`
  (served up its own tower), but NOT `G`'s inner demand, so `∃PP.G'` at a phase
  spawns a SUB-kernel. This sub-kernel is at the SAME budget, but serves a
  demand of STRICTLY SMALLER `mdepth` (`mdepth G' < mdepth G`).

**Correction (2026-08-13) to an earlier over-claim here.** AscMix does NOT
terminate on the horizontal budget ALONE: same-direction nesting escalates at
fixed budget. Termination is LEXICOGRAPHIC **(budget, demand-`mdepth`)** — the
horizontal budget decreases on horizontal/DR-child steps, and the served
demand's `mdepth` decreases on each vertical nesting step (bounded by
`mdepth C0`). Both are finite, so the node/kernel structure is finite. What
AscMix genuinely avoids is the §21 finite-poset argument for OPPOSITE-direction
(`∃PP` vs `∃PPI`) nesting — that needs `∃PPI`, excluded here. Same-direction
nesting is governed by the clean `mdepth` measure, not by §21. So the cash-value
of isolating AscMix stands (no §21), but the measure is the lexicographic pair,
not a single budget.

### 31.2 The phase-`∃DR` child's `hdr` is AUTOMATIC (no W2′ here)

`mtkKernelsDR_ok`'s `hdr` wants each DR-child `DR` to EVERY phase of its kernel.
In a real model this is FREE: if the child is `DR` to one phase `q_a`, then for
any other phase, the tower is `PP`-linked, and

    comp(DR, PP) = {DR}   (child DR q_a, q_a PP q_{a+1}  ⟹  child DR q_{a+1})
    comp(DR, PPI) = {DR}  (child DR q_a, q_{a-1} PP q_a  ⟹  child DR q_{a-1})

so `DR` to one phase propagates to ALL phases. The phase-`∃DR` witness is `DR` to
its phase by definition, hence `DR` to the whole tower — `hdr` holds with no
uniformization/W2′ obligation. (W2′ is a FULL-logic obstruction; ∀PO-freeness +
this composition fact dissolve it for the fragment's phase-`∃DR`.)

### 31.3 `∃PP` splits: one-shot vs persistent

Not every `∃PP.G` needs a kernel:
- **One-shot** `∃PP.G` (the truncated tower's leaf carries no further `∃PP`
  obligation — no `∀PP` forces `G`'s continuation): served by a FINITE witness at
  budget−1, exactly as `mtkNodes` already does (`mtkWitness`). No cycle.
- **Persistent** `∃PP.G` (a `∀PP` guard reproduces the demand, so the truncated
  leaf WOULD violate `∀PP`): needs a kernel CYCLE. Only here does
  `mty_segment_bounded` apply (it needs the infinite model chain, which exists
  iff the demand persists), giving the period.

The node-set recursion must therefore, at an `∃PP.G` demand, either recurse on
the finite witness (one-shot) or spawn a kernel (persistent). Horizontal and
one-shot branches decrease the budget; the persistent branch recurses on the
phases' horizontal witnesses at budget−1 AND, for a phase's inner persistent
`∃PP.G'`, spawns a sub-kernel at the SAME budget but strictly smaller
demand-`mdepth` (§31.1). So termination is the lexicographic pair
**(budget, demand-`mdepth`)**, not a single measure.

### 31.4 The node set (lexicographic recursion)

`ascNodes (n : MTKNode) : List MTKNode`, `termination_by (n.k, <demand-mdepth>)`:
- `n ::` for each `∃r.c ∈ mtk n`:
  - `r ∈ {dr,po,eq}` → `ascNodes (mtkWitness n hF)` (budget−1);
  - `r = pp`, one-shot → `ascNodes (mtkWitness n hF)` (budget−1);
  - `r = pp`, persistent → the kernel's phase witnesses, each
    `ascNodes (·)` at budget−1; a phase's inner persistent `∃PP` recurses at the
    same budget with strictly smaller demand-`mdepth` (phases/towers internal to
    κ);
  - `r = ppi` → `[]` (dead in AscMix).

κ = the kernels spawned (persistent `∃PP` sites). β = `ascNodes root`. Then feed
`extract_dr_children` (dadj = the horizontal DR/PO skeleton; kdr = the phase-`∃DR`
children; `hdr` by §31.2; routing by the coverage) and encode into `codesM` for
`decidableSat_ascmix`.

### 31.5 Work remaining for `decidableSat_ascmix`

**DONE (2026-08-13) — the node set + coverage core.** `ascNodes` (terminating) +
`self_mem_ascNodes` + the three branch-inclusions (`sub_ascNodes_hwitness` /
`_phasewitness` / `_oneshot`) + `ascNodes_trans` (transitivity) +
`ascNodes_covers` (node `∃DR`/`∃PO`/`∃EQ` → he_ex horizontal disjunct) +
`ascNodes_covers_phase` (phase `∃DR`/`∃PO`/`∃EQ` → hk_ex horizontal disjunct).
All 0-sorry. The genuinely-hard recursive construction + its termination is
behind us.

**REMAINING.**
1. **Vertical routing** (∃PP → kernel). Design: for a node `e` with `persistPP G
   e`, the kernel base is NOT `e` but `e`'s G-CARRYING PP-witness `y`
   (`persistPP_productive'` already yields `y` with `e PP y ∧ persistPP G y ∧
   G ∈ mty y`). So phase 0 = `mty y ∋ G`, `v0 = e` (attach), `K = ppi` (`e PP`
   phase), `conv K = pp` = the demand relation, and `D = G ∈ phase 0` discharges
   the he_ex vertical disjunct. `ascKernel`/`ppPhaseNodes` are built on `e`
   itself (phases carry `∃PP.G`, not `G`); the routing wants the `y`-based chain
   (`persistPP_chain'`, phases carry `G`) — reconcile in the wiring.
2. **The `extract_dr_children` assembly** — β = `{n // n ∈ ascNodes root}`
   (Fintype), κ = the persistent-`∃PP` sites; discharge `hee` (via `mtk_ee_all` on
   the horizontal β-β frame), `he_ex` (horizontal by `ascNodes_covers`, vertical
   by (1)), `hk_ex` (horizontal by `ascNodes_covers_phase`, vertical up-tower,
   phase-`∃DR` by §31.2's automatic `hdr`), `hdr`/`hcoh`.
3. **`codesAM` + `ascmix_hcompl` + `decidableSat_ascmix`** — finiteness/size bound
   (`ascNodes` is a `List`, so β/κ are Fintypes; the phase count is `≤ K(C₀)` by
   `mty_segment_bounded`), the `FinMT` encoding (`encodeMT_mtOk`), completeness
   (`mtAcceptB_complete`), then `decidableSat_of_codes`.

Then descending (the ∃PPI mirror, `dascKernel` ready) and full mixing
(opposite-direction nesting = the §21 finite-poset-of-kernels) complete
`decidableSat_pofree`.

## 32. The AscMix integration — the concrete assembly blueprint (2026-08-13/14)

Every INGREDIENT for `decidableSat_ascmix` is certified (§31.5). What remains is
the integration, and studying the horizontal (`encodeHF`/`codes`/`hfrag_hcompl`/
`decidableSat_hfrag`) + vertical (`codesV`/`unitTower_mem_codesV`/`encodeMT`) +
mixing (`codesMCmix`/`decidableSat_Cmix`) certified paths gives the EXACT
template for each step. This section maps it.

### 32.1 The FinMT code shape

`FinMT = ⟨tauE, E, K, Q, up, phase⟩` (six list-of-lists / list fields).
- HORIZONTAL (`codes`): `⟨tauE, E, [], [], [], []⟩` — κ empty, only β.
- SINGLE KERNEL (`codesV`): all six populated, nE = nK = 1.
- ASCMIX (`codesAM`, to build): nE = |ascNodes root| ≤ `K(C₀)`, nK = |sites| ≤
  `K(C₀)`, per-kernel period ≤ `K(C₀)`. Generalise `codesMCmix` (already
  multi-external+multi-kernel) with the three bounds as `mtkBound`-style limits.

### 32.2 The six concrete steps (each mirrors a certified theorem)

1. **β size bound** `ascNodes_length_le` — mirror `mtkNodes_length_le`, but the
   kernel branch adds `pk · |cl C₀|` per level, so the bound is
   `mtkBound`-with-a-period-factor. (Only SOME computable bound is needed;
   loosen if the tight one is painful.) `ppPhaseNodes` length = `pk ≤
   (allListsLe (cl C₀) …).length` via `mty_segment_bounded`.
2. **κ definition** — `κ = {(n, G) // n ∈ ascNodes root ∧ ∃PP.G ∈ mtk n ∧
   persistPP G n.x}` (a finite sigma over ascNodes × cl C₀). Per-`k` kernel data
   from `ascKernelG` via `Classical` (like `ascKernelPack`): `ck k`, `ik k`,
   `pk k`, `v0 k = n`, `kdr k` = the phase-`∃DR` witnesses.
3. **The node-set MultiTier + `mtOk`** `encodeAM_mtOk` — THE HARD PIECE, mirror
   `encodeHF_mtOk` but with κ NON-empty. β-`hee` = adapt `mtk_ee_all` (it is
   node-set-agnostic — sAdjK + mtk, re-provable for ascNodes); `he_ex` horizontal
   = `ascNodes_covers`, vertical = `ascKernelG` (v0=e, phase 0 ∋ G, conv K = pp);
   `hk_ex` horizontal = `ascNodes_covers_phase`, up-tower + phase-`∃DR` via the
   automatic `hdr` (§31.2); `kk_*` = `segment_kk_*`; `kq_all` VACUOUS (PO-default,
   `mty_no_all_po`). Build via `mtkKernelsDR_ok` then `encodeMT`+`encodeMT_mtOk`
   (relate decoded FinMT to the node-set MultiTier by the encode lemmas).
4. **acceptance** `encodeAM_accepts` — mirror `encodeHF_accepts` (root index
   `< nE`, `mtAcceptB` true).
5. **membership** `encodeAM_mem_codes` — mirror `encodeHF_mem_codes` +
   `unitTower_mem_codesV` (the code is size-bounded, so ∈ `codesAM`).
6. **the theorem** `ascmix_hcompl` (mirror `hfrag_hcompl`) then
   `decidableSat_ascmix = decidableSat_of_codes C₀ (codesAM C₀) (ascmix_hcompl …)`.

### 32.3 Effort + risk

Step 3 (`encodeAM_mtOk`) is ~1–2 sessions (the routing discharge with kernels —
the largest new piece; roughly the size of this session's coverage work). Steps
1,2,4,5,6 are ~1–2 sessions (patterned on the certified horizontal/vtower code).
Total AscMix integration ≈ 2–4 sessions. Residual risk: the routing discharge or
the β/κ Fintype bookkeeping could surface a real adaptation need — Lean's 0-sorry
discipline would EXPOSE it (not hide it), but "all ingredients certified" ≠ "the
assembly goes through" until built. Then descending (∃PPI mirror, ~1–2 sessions)
+ full mixing (§21 opposite-direction nesting, ~3–6 sessions, the real unknown)
complete `decidableSat_pofree`. Full-logic F6 stays OPEN (separate).

## 33. The one-shot-∃PP finding — a genuine architectural gap (2026-08-14)

Pushing into the `he_ex` discharge for the AscMix assembly surfaced a REAL gap
the §31/§32 blueprint glossed. It is not mechanical wiring; it is a genuine
missing piece, and honesty requires flagging it.

### 33.1 The gap

`mtkKernelsDR` serves an `∃PP.D` demand at a node `e` ONLY through a KERNEL
(`conv(K k e)=pp`, `D ∈ phase`), and a kernel requires `persistPP` — an INFINITE
`PP`-chain reproducing the demand (`ascKernelG` needs it via `mty_segment_bounded`).
So it handles **persistent** `∃PP` (∀PP-guarded, vtower-style).

A **one-shot** `∃PP.D` (e.g. the bare `∃PP.A`, or `∃PP.(A ⊓ ∀PP.⊥)` where the
witness is a forced leaf) has NO infinite chain, hence no kernel. Can it instead
be a `PP` EDGE in the β-frame (`E e w = pp`)? **No** — and this is the crux:

    comp(PP,PP) = {PP}   (transitive: e⊂w⊂g ⟹ e⊂g)

so a `PP` edge CANNOT be PO-defaulted: `e PP w PP g` FORCES `e PP g`, but the
PO-default frame would set the non-adjacent `e–g` edge to `PO ∉ {PP}` —
composition VIOLATION. (This is exactly why DR-children work and PP-witnesses
don't: `comp(DR,DR)` ⊇ {PO}, so DR CAN PO-default; PP cannot.)

So one-shot `∃PP` is served by NEITHER a kernel NOR a PO-default β-edge. The
current architecture does not handle it. And one-shot `∃PP` is COMMON (any bare
`∃PP.A`), and IN SCOPE for the full ∀PO-free fragment.

### 33.2 Cross-check: the campaign's vertical results are all persistent

`decidableSat_vtower`/`…G`/`…RR`/`…RRI` and every vertical witness (`Cvert`,
`Ccar`, …) carry the `∀PP`-guard — they are PERSISTENT `∃PP`. One-shot `∃PP` was
never in the certified scope; this finding makes that explicit rather than
implicit.

### 33.3 What it costs

Two real options, both more than wiring:
- **Finite-PP-tower certificate** — a certificate with EXPLICIT `PP` edges (all
  transitive edges present, composition-closed) for the `∀PP`-free / one-shot case
  (finite towers bounded by `mdepth`). Distinct frame from `mtkKernelsDR` (PP has
  no PO-default). ~1–2 sessions.
- **Model-surgery ("persistify")** — show every satisfiable ∀PO-free concept has a
  model where every `∃PP` is persistent (pad each one-shot leaf into an infinite
  self-reproducing tower). FAILS when a `∀PP.⊥`-style guard forces a leaf, so it
  is NOT a complete fix by itself.

### 33.4 Honest revision

The AscMix milestone as blueprinted (arbitrary `∃PP`) is HARDER than the §32
estimate: it needs the one-shot handling (33.3) ON TOP of the kernel handling.
Revised: either narrow the first milestone to **persistent-`∃PP`-mixed** (the
kernel path, matching what's built — but its clean syntactic characterization is
itself a task), or add the finite-PP-tower certificate (~+1–2 sessions). The
frame-control resolution (§ ascDadj) and all the coverage/kernel machinery stand;
this is an ADDITIONAL mechanism, not a correction of what's built. The residual
risk I flagged ("ingredients certified ≠ assembly proven") materialized here —
which is exactly what pushing into the assembly is for.

## 34. The unified ordered-disjoint architecture — the general path (2026-08-14)

The one-shot-∃PP finding (§33) is not a special case to patch; it points at the
RIGHT general structure for the WHOLE vertical side. PP is a transitive strict
order, so the vertical skeleton is a PARTIAL ORDER, and RCC5 closure ⟺ the
ORDERED-DISJOINT normal form (PP = strict order, DR = downward-closed
disjointness, PO = residual) — already CERTIFIED forward in
`formal/RCC5NormalForm.lean` (wp47 the converse, n≤4). The frame for it is
already certified too: `posetNet_frame` (§ posetNet) proves the ordered-disjoint
read-off of ANY strict partial order is an RCC5 Frame. This is the general
foundation; the PO-default frame (`po_default_multi_frame`) is the special case
where the PP-order is empty and everything incomparable is PO.

### 34.1 One uniform representation of the vertical structure

Represent the vertical skeleton of a node as a FINITE POSET of "tower-tops",
where each tower-top is either
- a FINITE chain ending at a leaf (a one-shot `∃PP`, §33), or
- an INFINITE chain represented by a CYCLE (a persistent `∃PP` — the existing
  kernel/`mtkKernelsDR`),
and the frame among all β-nodes + tower-tops is the ordered-disjoint read-off
(`posetNet`-style): comparable ⟹ PP/PPI, incomparable-and-disjoint ⟹ DR
(downward-closed), incomparable-and-overlapping ⟹ PO. This SUBSUMES:
- the horizontal PO-default frame (empty PP-order),
- the DR-children skeleton (`ascDadj` — DR at consecutive budgets),
- the persistent kernels,
- and — the new piece — the FINITE PP-towers (one-shot).

So the whole ∀PO-free certificate is ONE ordered-disjoint frame, not three glued
mechanisms. This is the class-level solution.

### 34.2 The concrete building blocks (what's certified, what's to build)

CERTIFIED: `RCC5NormalForm.toOrderedDisjoint`; `posetNet_frame` (PP-order ⟹
Frame); `mtkNodesH`/coverage; the persistent kernels; `ascDadj`/`ascNodes_ee_all2`
(consecutive-DR hee); `ascKernelG`.

TO BUILD (the general vertical mechanism):
1. **Poset-of-model-nodes `MultiTierOk`** — a `MultiTierOk` over `posetNet` where
   the poset nodes carry their `mty`/`mtk` types, with `ee_all` for the PP-ORDER
   (`∀PP` propagates UP the order via `comp(PP,PP)={PP}`; `∀PPI` DOWN; budget via
   the tower depth) and `e_ex` serving `∃PP` by a comparable-above node. This is
   the finite-PP-tower certificate; `posetNet_frame` gives the frame for free.
2. **Finite-tower extraction** — from a one-shot `∃PP.D` at a node, the finite
   `mtkWitness`-chain (already in `ascNodes`) as poset nodes; the poset order =
   the PP-ancestry; leaves have no `∃PP`.
3. **Unify with kernels** — a poset element may itself be a cycle (kernel);
   `posetKernel_ok` already handles a poset OF kernels, so the unification is:
   poset elements = finite chains ⊎ kernels.
4. **Coverage + codesAM + decidability** — as §32, over the unified frame.

### 34.3 Why this is the productive general path

It (a) handles the one-shot `∃PP` CLASS (not a witness), (b) is grounded in TWO
certified results (`RCC5NormalForm` + `posetNet_frame`), (c) subsumes the
horizontal + DR-children + kernel machinery as special cases of one frame, and
(d) is the exact structure the overview paper's "ordered-disjoint normal form"
predicts. The first concrete Lean target is (1) — the poset-of-model-nodes
`MultiTierOk` — which is the finite-PP-tower certificate and the general vertical
`e_ex`/`ee_all` the whole fragment needs. Estimate stands revised (§33): this
adds ~2–4 sessions over the persistent-only path, but it is the path that
actually reaches ∀PO-free decidability rather than a persistent-only sub-fragment.

## 35. The extraction summit, pinned to `mixKernels_ok` (2026-08-15)

The general merged **soundness** is finished: `mixKernel_ok`/`mixKernelI_ok`
(one kernel + arbitrary externals) and `mixKernels_ok` (the FULL multi-kernel
merge, ascending⊎descending kernels via `dir k`, non-vacuous cross-kernel
`kq_all`) are all proven, 0-sorry. So the entire remaining task — the
extraction (model → certificate) — is exactly: **produce `mixKernels_ok`'s
hypotheses from a satisfiable ∀PO-free model.** That interface is the precise
spec of the summit:

```
mixKernels_ok (hI) (C0) (g : β→α) (hgdom) (ck : κ→ℕ→α) (hdom) (ik pk dir)
  (hstep) (hp) (hty)
  (hstab   : ∀ k e a, ρ (g e) (ck k (ik k + a)) = ρ (g e) (ck k (ik k)))   -- ✅ StabKernelPack / dStabKernelPack
  (hrectQ  : ∀ k≠k' a b, ρ (ck k (ik+a)) (ck k'(ik'+b)) = ρ (ck k ik)(ck k' ik'))  -- ⬜ (1)
  (hinj)                                                                    -- ⬜ (from distinctness of chosen nodes)
  (he_ex   : external ∃-demand → horizontal child ∨ into some kernel)       -- ⬜ (3)
  (hk_ex   : phase ∃-demand → external ∨ up-chain ∨ eq ∨ cross-kernel)      -- ⬜ (3)
  : MultiTierOk (mixKernels …)
```

### 35.1 What is now supplied

`StabKernelPack` (ascending) / `dStabKernelPack` (descending) bundle
`persistPP_chain`/`persistPPI_chain` + `segment_select`/`dsegment_select` into
`{c/i/p, dom, step, period, dem, stab, recur}`. The `stab` field IS
`mixKernels_ok`'s per-kernel `hstab` (external→chain orientation, via
`hI.conv_`); `recur` gives the cofinal phase recurrence for round-robin serving
of a kernel's own `∃PP`. So `hstab` is discharged for a kernel of either
direction, given a finite external list.

### 35.2 The four remaining pieces (in dependency order)

1. **`hrectQ` — the cross-kernel rectangle.** For two *moving* chains `ck k`,
   `ck k'`, the relation `F(a,b) = ρ (ck k (ik+a)) (ck k'(ik'+b))` must be
   constant past chosen bases. `F` decomposes into three monotone indicators —
   disjoint (`=DR`), `c⊆d` (`∈{PP,EQ}`), `d⊆c` (`∈{PPI,EQ}`):
   - **DR third — DONE** (`cross_dr_stabilizes`, commit 8e75a41): overlap
     (`≠DR`) between two ascending PP-towers is NE-closed, because
     `dr ∉ comp(PPI,X)` and `dr ∉ comp(X,PP)` for every non-DR `X` (pure comp
     table). So the DR-indicator is eventually constant on a NE-quadrant.
     Support bricks: `chain_pp_lt` (propext-only), `cross_overlap_mono_m/_n`.
   - **`⊆` thirds — TO BUILD.** `Q = c⊆d` is down-in-`m`, up-in-`n`; `R = d⊆c`
     is up-in-`m`, down-in-`n` — neither is NE-monotone, so pure-comp closure
     does NOT suffice. Route: the rank `ppi=3, dr=eq=2, po=1, pp=0` makes
     `comp(·,pp)` non-increasing (a `by decide` fact `rank_comp_pp_le`), so the
     per-row `n`-limit `φ(n)` has non-increasing rank hence eventually constant;
     mirror for the `m`-limit; the OPEN subtlety is upgrading the two per-margin
     limits to a single UNIFORM NE-quadrant value (the marginals stabilize only
     at per-external horizons — `externals_stabilize` gives no uniform horizon).
     This uniformity step, on the overlap region where the DR-third already
     pins `≠DR`, is the crux of the remaining ~150-line chunk.
   Finitely many kernel pairs (`κ` a Fintype) ⟹ a joint horizon; pick every
   `ik k` past it.
2. **Classification.** A `Classical.em`-driven split of each `β`-node's `∃PP`/
   `∃PPI` demand into persistent (→ a kernel via `ascKernelG`/`dascKernel`,
   `κ` = the persistent sites) vs served-in-`ascNodes`. Persistence is
   `persistPP`/`persistPPI` (already defined).
3. **`he_ex`/`hk_ex` routing.** Horizontal disjuncts from `ascNodes_covers` /
   `ascNodes_covers_phase` (built); vertical + cross-kernel disjuncts from the
   kernels' `dem`/`recur`. This is the coverage discharge over the chosen
   `β`,`κ`.
4. **`codesM` + `hcompl`.** Finite enumeration of merged codes (template =
   `codesMCmix` + `encodeMT`/`mtAcceptB_complete`) and the completeness premise
   for `decidableSat_of_codes`.

`hstab` (done) and `hrectQ` (piece 1) are the two *interface-stabilization*
obligations; once both are theorems, the remaining work (classification +
routing + codes) is coverage bookkeeping over the already-certified engines.
The honest next target is piece 1.

## 36. RESEARCH ROUND: `hrectQ` is FALSE in general — the cross-kernel staircase (2026-08-15)

Before writing more Lean for `hrectQ`, a research round. It overturns the §35
premise that `hrectQ` is "just a hard theorem": **`hrectQ` is false in general.**

### 36.1 The counterexample (airtight, from `chain_pp_lt`)

Take two kernels sharing a chain, `c = d`. Then
`F(m,n) = ρ(c m)(c n) = PP` for `m<n`, `EQ` for `m=n`, `PPI` for `m>n`
(exactly `chain_pp_lt`, already proved). Every NE-quadrant contains both `m<n`
and `m>n`, so `F` is a **staircase**, not constant — no `N` satisfies
`hrectQ`. This is not a pathology of equal chains: any two ascending towers
whose set-unions are ⊆-**comparable** (one inside the other, "racing" up)
staircase along the boundary `m ≈ αn` (machine-checked, `/tmp/staircase_check.py`:
`c={0..m}`, `d={0..2n}` staircases along `m=2n`).

### 36.2 The trichotomy (machine-confirmed on set models)

For two ascending PP-towers, `F(m,n)` is eventually constant on a NE-quadrant
**iff** their unions are not ⊆-comparable-and-distinct:

| union relation of `C_a=⋃aᵢ`, `C_b=⋃bⱼ` | eventual `F` | status |
|---|---|---|
| **disjoint** (`C_a ∩ C_b = ∅`) | `DR` | ✅ `cross_dr_stabilizes` (commit 8e75a41) |
| **incomparable + overlapping** (each has a permanent private part) | `PO` | ✅ `cross_po_stabilizes` (commit 1124c95) — no `eta` needed |
| **⊆-comparable, distinct** (`C_a ⊊ C_b`, racing) | **staircase** | ✗ `hrectQ` unsatisfiable — must MERGE |

Crucially, two `∃PP`-witnesses of a **common** node always overlap (both ⊇ that
node) so are **never** `DR`; they are `PO` (incomparable) or comparable — so the
`DR` case alone never suffices, and PO/comparable towers are unavoidable in the
∀PO-free fragment.

### 36.3 The resolution

1. **DR kernels** — `cross_dr_stabilizes` (done).
2. **Incomparable (PO) kernels** — `hrectQ` holds with constant value `PO`,
   provable via `cross_po_stabilizes`: incomparable unions ⟹ a **permanent
   private point**. The clean point (why this is provable where the general
   uniform-quadrant claim was not): a *point* of a directed union lies in *some*
   member (no compactness), whereas a *region* ⊆ a union needs compactness. Via
   the certified `eta` set-representation (`RCC5NormalForm`: `sub_iff_le`,
   `disj_iff_eta_disjoint`), `¬(⋃η(aᵢ) ⊆ ⋃η(bⱼ))` gives `P ∈ η(a_{i₀})`,
   `P ∉ η(bⱼ) ∀j`; symmetrically `Q`; plus overlap at the shared node ⟹
   `ρ(aᵢ)(bⱼ) = PO` for `i≥i₀, j≥j₀`. So `cross_po_stabilizes` is the PO analogue
   of `cross_dr_stabilizes`, provable but needing `eta` ported into POFreeLift.
3. **Comparable (nested/racing) towers** — cannot be two constant-`Q` kernels.
   They must be **MERGED**: a tower whose union is ⊆ another's is served *within*
   that tower. This is exactly **shared-tower round-robin serving** — the
   existing `rr_covers` / `decidableSat_vtowerRR` machinery (one tower discharging
   several nested `∃PP` demands over its recurrent period). So the merge is not
   new mathematics; it is routing nested demands to a shared kernel.

### 36.4 Revised summit plan (supersedes §35.2 piece 1)

`hrectQ` splits by the trichotomy, and the classification must guarantee that
**distinct kernels are pairwise ⊆-incomparable** (comparable ones merged via
round-robin). Then every surviving cross-pair is `DR` or `PO`, and `hrectQ` holds
via `cross_dr_stabilizes` ⊎ `cross_po_stabilizes`. Concretely:

- (a) **`cross_po_stabilizes`** — ✅ DONE (commit 1124c95), and it needed no
  `eta` at all: the private-part conditions are stated relationally
  (`ρ(c i0)(d j) ∉ {PP,EQ}`, `ρ(c i)(d j0) ≠ PPI`) and propagate up each tower
  by `chain_pp_lt` + `comp(PP,PP)={PP}` + `eq_id`. `propext`-only. This replaced
  the uncracked "uniform quadrant" of §35.2 with a *true, clean, proved* lemma.
- (b) **Comparability classification + merge** — the remaining `hrectQ` work,
  now folded into the extraction's classification piece: decide each kernel pair
  DR / incomparable / comparable (`Classical.em` on the private-part predicates —
  exactly `cross_po_stabilizes`'s `hc`/`hd`/`ho` hypotheses, or their negation);
  DR ⟹ `cross_dr_stabilizes`, incomparable ⟹ `cross_po_stabilizes`, comparable ⟹
  route to a shared round-robin kernel (`rr_covers`).
- (c) Then `hrectQ` (assembled from the two bricks over incomparable/DR pairs),
  `hstab` (done), `he_ex`/`hk_ex`, `codesM` as before.

**Status after this round:** both interface-stabilization *bricks* are proved —
`hstab` (`StabKernelPack`/`dStabKernelPack`) and both non-degenerate `hrectQ`
cases (`cross_dr_stabilizes`, `cross_po_stabilizes`) — AND the pairwise
**classification** `classify_cross` (commit 0f03401): for any two ascending
kernels' chains, a `Classical.em` split yields exactly one of
{cross eventually constant `v` (hrectQ-ready: `v=PO`/`DR` via the two bricks) ;
`c` embeds in `d` ; `d` embeds in `c`} — the whole §36 trichotomy in one lemma,
with `cprivate_up`/`dprivate_up` (private-part propagates up the tower) doing the
late-witness bump. What remains for the summit:

- **Merge** (comparable pairs → shared round-robin kernel `rr_covers`): consume
  `classify_cross` disjuncts 2/3 so that surviving distinct kernels are pairwise
  incomparable-or-disjoint.
- **Family `hrectQ`**: lift pairwise `classify_cross` disjunct-1 to all pairs at
  once — choose every base `ik k` past the joint horizon `N` (finite `max` over
  the `κ×κ` pairs, `κ` a Fintype), so every cross-pair is constant at its bases.
- **Coverage** (`he_ex`/`hk_ex`) and **`codesM`** + the `decidableSat_of_codes`
  premise.

No further interface-stabilization theorem is owed; the classification *decision*
is done; the remaining work is merge + family-lift + coverage + codes.

### 36.6 The `hrectQ` pipeline is now assembled (commits ec37cac, d4ea56b)

`family_hrectQ` + `exists_bound`/`exists_bound2` + `family_hrectQ_bounded` close
the family-lift: for `κ = Fin n` kernels, given per-pair constancy at a horizon
`hN` (`classify_cross` disjunct 1), `family_hrectQ_bounded` *exhibits* bases
(every `ik k := B = max hN`, via `exists_bound2`) for which `mixKernels_ok`'s
`hrectQ` holds verbatim. So the whole `hrectQ` obligation is certified for
pairwise-incomparable/disjoint kernels:

```
classify_cross          -- pairwise: constant-at-horizon v, OR comparable
  → cross_dr_stabilizes  -- v = DR  (disjoint)
  → cross_po_stabilizes  -- v = PO  (incomparable + overlapping)
  → family_hrectQ_bounded -- choose bases past the joint max  ⟹  hrectQ
```

**The single remaining `hrectQ`-side residue is the MERGE** (comparable pairs →
one shared tower) so that every surviving pair lands in `classify_cross`
disjunct 1. Everything else on the cross-kernel side is done.

### 36.7 The MERGE is NOT a poset-with-cycles (commit 6505314)

Scoping the merge overturned the §34/§36.6 assumption that it needs a
poset-with-cycles. It does not. The reason: a persistent demand's `∀PP`-guard
**propagates up the order**.

- `guard_propagates` — `z` `PP`-above `x`, and `∀PP.(∃PP.D) ∈ mty x`, gives `z`
  BOTH `∃PP.D` (`mty_all`) and the guard `∀PP.(∃PP.D)` (`sat_all_pp_up`).
- `merge_persistAll` — if `z` is `PP`-above a guard-carrier for every `D ∈ Ds`,
  then `persistAll I C0 Ds z`. So a node above the roots of a comparability class
  is a `persistAll` node for the whole class, and `rr_covers` serves all of `Ds`
  from `z`'s SINGLE tower by round-robin.

So comparable persistent towers merge into **one round-robin kernel** — the
larger tower, whose sufficiently-high node absorbs every smaller demand's guard.
No 2-D staircase needs finite representation; the staircase pair simply never
becomes two kernels. Distinct kernels then stay pairwise incomparable/disjoint,
which is exactly `hrectQ`-ready (`classify_cross` disjunct 1 → the two
stabilization bricks → `family_hrectQ_bounded`).

**The cross-kernel + merge story is therefore complete at the lemma level.** The
whole vertical/mixing pipeline reduces to:

```
classify_cross           pairwise: constant-at-horizon  OR  comparable
  ├─ constant → cross_dr_stabilizes / cross_po_stabilizes → family_hrectQ_bounded  (hrectQ)
  └─ comparable → guard_propagates → merge_persistAll → rr_covers  (one kernel)
```

**Residue for the general theorem** — now all model-side existence + wiring, no
new analytic obstacle:
- ✅ construct the common upper node `z` (pairwise) — DONE (`merge_pair`, commit
  5dc2cc8: `z = d(j0+1)` from the embedding `x_c PP d j0`; `embed_to_pp`, commit
  4a4feb4, axiom-free, bridges `classify_cross`'s `{PP,EQ}` output to the `PP`
  input). So the pairwise merge input chain is complete:
  `classify_cross (comparable) → embed_to_pp → merge_pair → persistAll → rr_covers`.
  The class case (a common node above ALL roots of a comparability class) folds
  the pairwise construction, or takes the top of the class's `⊆`-chain.
- partition persistent demands into comparability classes (`classify_cross`
  applied pairwise);
- coverage (`he_ex`/`hk_ex`) + `codesM` + the `decidableSat_of_codes` premise.

### 36.5 Why this is progress, not a setback

The research round converted a *false* obligation (general `hrectQ`) into a
*true* one (per-trichotomy-case), reused two already-built assets
(`cross_dr_stabilizes`, the round-robin kernels) exactly, and localized the one
genuinely new lemma (`cross_po_stabilizes`) to a clean `eta`-based argument. It
also re-vindicates §34's ordered-disjoint instinct: the vertical structure is a
poset of DR/PO-separated towers, comparable chains collapsed — the same normal
form. `cross_po_stabilizes` (with `eta`) is the honest next Lean target.

## 37. The partition = domination by MAXIMAL towers (2026-08-15)

Scoping the "comparability-class partition" surfaced a subtlety: **comparability
(embeds either way) is NOT transitive** (`c ⊆ d` and `e ⊆ d` leave `c`, `e`
possibly incomparable), so "comparability classes" is ill-defined. The correct
structure is **domination by maximal towers**, valid because *embedding* is:

- `embed_trans` (commit ce20857, `propext`-only): "tower `c` embeds in tower `d`"
  = `∀ i, ∃ j, ρ(c i)(d j) ∈ {PP,EQ}` (`classify_cross` disjunct 2) is a
  **transitive preorder** — `comp({PP,EQ},{PP,EQ}) ⊆ {PP,EQ}`.

So the finitely many persistent-demand towers form a finite preorder. Its
**maximal towers** are a dominating antichain:
- every tower embeds in some maximal tower (finite preorder ⟹ maximal-domination);
- each maximal tower `z` serves every demand below it: a high node of `z` is above
  all their roots, hence `persistAll` for the whole set (`merge_persistAll` +
  `merge_pair`/`embed_to_pp` per demand);
- distinct maximal towers are incomparable ⟹ `classify_cross` disjunct 1 ⟹
  constant cross-relation ⟹ `hrectQ` (`cross_po_stabilizes` + `family_hrectQ_bounded`).

So `κ` = the maximal towers; coverage routes each demand to the maximal tower
above it. This is why the merge partition is well-defined despite non-transitive
comparability.

> **CORRECTION (2026-08-15, §38.3).** The third bullet above is a LAYER ERROR and
> is superseded. The kernels are not the maximal *demand* towers — they are the
> ROUND-ROBIN re-towers built above each class's `persistAll` node — and
> incomparability does not transfer between the layers: `rrPt` ascends through
> chosen witnesses and can leave the demand tower, so two incomparable demand
> towers sitting inside a common region can have mutually embedding round-robin
> towers. `hrectQ` must therefore be established for the round-robin towers, and
> the merge must run on THEM, as the recursion of §38.3. The first two bullets
> (`embed_trans`, `maximal_dominated`, guard absorption) are unaffected and
> remain correct about the demand towers. No certified statement was wrong:
> `vtowers_or_comparable` applies `classify_cross` to `classChain`, the actual
> kernels.

### 37.1 `maximal_dominated` — DONE (commit f023cb9)

The one abstract fact the partition owed — **in a finite preorder every element
is `≤` a maximal element** (`∀ a : Fin n, ∃ m, le a m ∧ ∀ k, le m k → le k m`) —
is now proved in core Lean. Strong induction on `#{k : le a k}`: `a` maximal ⟹
done; else `∃ a', le a a' ∧ ¬le a' a`, and the count strictly drops. The two
`List.countP` steps are inline (`countP_mono`, `countP_lt`, `one_le_countP_of_mem`)
since core has no `Finset.exists_maximal` and a preorder has no total `max`.

**So the partition's abstract foundation is complete:** `embed_trans` (embedding
is a transitive preorder) + `maximal_dominated` (maximal domination) ⟹ `κ` = the
maximal demand-towers, a dominating antichain. What remains for the vertical
extraction is the **assembly**, no new abstract fact:
- instantiate `maximal_dominated` at `le :=` the embedding on the (finite) list
  of persistent demands — `DecidableRel` for the embedding is `Classical.dec`;
- for each maximal tower, gather the demands below it and build its `persistAll`
  node (`merge_persistAll` + `merge_pair`/`embed_to_pp`), then `rr_covers`;
- cross-pairs (distinct maximals) are incomparable ⟹ `classify_cross` disjunct 1
  ⟹ `family_hrectQ_bounded` gives `hrectQ`;
- coverage (`he_ex`/`hk_ex`) + `codesM` + the `decidableSat_of_codes` premise.

## 38. The partition assembly — progress (2026-08-15)

The partition foundation being complete (§37.1), the vertical-extraction assembly
has begun, connecting the certified bricks:

- `exists_maximal_tower` (commit 426ff4e) — `maximal_dominated` at the
  tower-embedding relation: every demand-tower embeds in a MAXIMAL tower, `κ` =
  the maximal towers (a dominating antichain up to mutual embedding).
- `common_upper_on_tower` (commit ae45aef) + `list_bound` — for the demands
  dominated by a maximal tower `d`, the single node `d(B+1)` (`B = max` of their
  embedding levels) is `PP`-above every root, and `B+1 > 0`. This is exactly the
  common node `merge_persistAll` consumes.

So the vertical chain is:
```
exists_maximal_tower   (κ = maximal towers)
  → common_upper_on_tower  (one node above a class's roots)
  → merge_persistAll       (⟹ persistAll for the class)
  → rr_covers              (one round-robin kernel serves the class)
  + family_hrectQ_bounded  (cross-pairs of maximal towers, hrectQ)
```

### 38.1 THE FIRST `mixKernels_ok` INSTANTIATION — DONE (2026-08-15)

The purely-vertical multi-tower certificate (`β = Empty`) is **certified**, and
it is **doubly witnessed** (chain-level and node-level). Chain:

```
class_tower           persistAll node  -> a FIXED chain + bases past ANY threshold
  → vtowers_ok        Fin n towers     -> ∃ ik pk, MultiTierOk (mixKernels … Empty …)
  → vtowers_or_comparable_gen          the dichotomy: certificate OR comparable pair
  → vtowers_or_comparable              the same, entered from persistAll NODES
```

**The one real obstacle the assembly hit, and its fix.** `hty` (per-kernel type
recurrence) and `hrectQ` (cross-kernel constancy) are produced by *different*
arguments choosing *different* bases: the pigeonhole picks a recurrence base,
`classify_cross` picks a constancy horizon, and `mixKernels_ok` needs both at
**one** base. `family_hrectQ_bounded` (§36.6) exhibits bases past the joint
horizon but then dictates them (`ik k := B`), which the recurrence cannot honor.
The fix is `rr_segment_from` — `rr_segment` with a THRESHOLD (the pigeonhole on
the sub-sequence at multiples of `L` started at `L0+1` rather than `1`), so the
recurrence base is available past *any* bound. Order of construction:

1. fix each class's chain (`class_tower` / `classChain`) — chains must exist
   *before* the classification, since `classify_cross` classifies chains;
2. join the per-pair horizons (`exists_bound2` ⟹ `B`);
3. only then pick each base via `hrec k B` (base `≥ B`, its own period);
4. `hrectQ` via `family_hrectQ` (not `…_bounded`, which fixes the bases).

So `family_hrectQ_bounded` is superseded here by `family_hrectQ` + a *chosen*
late base — the bounded form remains correct, just not the usable one.

**`hinj` is FREE.** `cross_const_ne_eq` (axiom-free): a constant cross-relation
between two towers is never `EQ`, since strong-EQ identity would force
`d N = d (N+1)` against the strict `PP` step. So distinct bases follow from the
constancy already in hand — no distinctness hypothesis is owed.

**What `vtowers_ok` assumes, stated honestly.** Beyond the chain data it takes
(i) `hrec` — recurrence + round-robin coverage of the tower's demand list past
any threshold (supplied by `class_tower`); (ii) `hconst` — per-pair cross-
constancy horizons, i.e. the towers are pairwise NON-comparable (`classify_cross`
disjunct 1); (iii) `hdem` — the *purely vertical* phase condition: every phase
`∃`-demand is `∃PP` with argument in that tower's own list, or `∃EQ`. (iii) is
what `β = Empty` means, and is exactly what the mixing quadrant will relax.

**Non-vacuity, both levels** (the ledger's standing discipline):
- `vtowers_two_nonvacuous` — in the two-region all-cross-`PO` model `Ipo`, the
  two regions' `PP`-chains give a `MultiTierOk` with `κ = Fin 2`: TWO kernels,
  cross-value a real `PO` (not `EQ`, not a disguised single kernel), so `hrectQ`
  and `cross_const_ne_eq` are both genuinely exercised.
- `vtowers_from_nodes_nonvacuous` — the same from `persistAll` NODES, with the
  dichotomy's escape branch REFUTED: `classChain_region` (an `Ipo` `PP`-step
  never leaves its region) forces every cross-value to `PO`, so neither
  comparability disjunct can hold and the certificate branch must fire. This
  rules out the degenerate reading in which `vtowers_or_comparable` is an
  always-comparable tautology.

### 38.2 THE LAYER ERROR that scoping the merge exposed

Closing the dichotomy's escape branch was planned (§37, §38 diagram) as: κ = the
maximal demand towers, which are pairwise incomparable, so `classify_cross`
disjunct 1 gives `hrectQ`. **That is wrong by one layer.** The kernels are the
ROUND-ROBIN re-towers `rrPt` built above each class's `persistAll` node, not the
demand towers, and incomparability does not transfer: `rrPt` ascends through
`Classical.choose`n witnesses and can leave its demand tower entirely, so two
*incomparable* demand towers both contained in a common region can have
*mutually embedding* round-robin towers.

Corroboration inside the code: `merge_persistAll` requires the guard as
`∀PP.(∃PP.D) ∈ mty C0 I x`, which `persistPP` ROOTS supply but `persistAll`
SITES do not (they carry it as `sat`). The existing bricks were built for exactly
ONE merge round. A second round needs `merge_persistAll_sat`, which did not
exist — precisely the missing piece the layer error concealed.

Nothing certified was wrong: `vtowers_or_comparable` classifies `classChain`,
the actual kernels, and honestly returns the comparable case as an escape.

### 38.3 THE MERGE, DONE (2026-08-15) — the vertical side is unconditional

The merge runs on the KERNELS, as a recursion whose measure is the site count:

```
vtowers_or_comparable_ex   dichotomy, both branches' chains abstracted
  ├─ non-comparable → vtowers_ok                        (the certificate)
  └─ comparable     → comparable_common_upper           (one node above both roots)
                    → persistAll_merge2                 (ONE site, both demand lists)
                      (via merge_persistAll_sat, the sat-form guard bridge)
                    → merge_step                        (site count STRICTLY drops)
                    → re-enter                          (induction on the count)
```

`merge_sites` is the recursion, `vtowers_merged` the capstone:

> **`vtowers_merged`** — every finite family of purely-vertical `persistAll`
> sites yields a `MultiTierOk` certificate that SERVES every demand of every
> site. No comparability hypothesis is owed.

Two details worth recording:

- **No double-erasure arithmetic.** `merge_step` builds the shorter list as
  `((finRange n).filter (· ≠ k)).map (fun i => if i = k' then merged else L.get i)`
  — index `k` filtered out, index `k'` overwritten by the merged site. Length
  strictly drops by `filter_length_lt`; membership is `mem_map`+`mem_filter`.
- **`SiteDem` survives the merge** because the merged node's `PP`-cone is
  contained in each parent's (`comp(PP,PP) = {PP}`), and each parent's demands
  land in the concatenated list.

**Non-vacuity.** `persistAll_merge2_nonvacuous` — the merge primitive fires on
two sites at different heights of one `Ipo` region, exercising exactly the
`sat`-form guard bridge that `merge_persistAll` could not reach.
`vtowers_merged_nonvacuous` — the unconditional certificate is delivered on that
same two-site family. Honest scope: the latter does not claim which branch the
recursion took (that needs §36.1's staircase argument); the former is airtight.

### 38.4 Remaining

- **Mixing** — replace `β = Empty` by the horizontal externals (`ascNodes`):
  `hstab` (`StabKernelPack`, done), `he_ex`/`hk_ex` with horizontal disjuncts,
  and dropping the purely-vertical `hdem`. The merge is a prerequisite and is
  now available: a mixed certificate with several vertical kernels needs the
  same pairwise non-comparability.
- **`codesM`** enumeration + the `decidableSat_of_codes` completeness premise.

**Scope correction to this section's own wording.** "The vertical side owes
nothing further" would be an overclaim: §38.1–§38.3 close the **persistent**
vertical side (`persistAll` sites, i.e. `∀PP`-guarded `∃PP`). **One-shot `∃PP`**
— §33's architectural gap — is still owed and is still vertical. Its FRAME
exists (`posetMT_ok`/`posetKernel_ok`, §34 item 1), but the EXTRACTION of finite
PP-towers from a model (§34 item 2) and their unification with kernels in one
certificate (§34 item 3) are unbuilt. So the honest label for the vertical side
is: **persistent-∃PP vertical is complete; one-shot `∃PP` is open.**


## 39. THE MIXED SELECTION — RESOLVED (2026-08-19)

> **ON THE CRITICAL PATH (restored 2026-08-20; see §42).** A banner added
> earlier the same day called this section off-path, on the strength of the §41
> pivot. That was wrong: the read-off certificate is the general one, and
> everything below — `hstab`, `hrectQ`, the banks, the merge, the base
> selection — is exactly what it needs.

*This section supersedes and consolidates the working notes of the 2026-08-19
session (formerly §§39–43: the ordering cycle, the staged plan, the collapse,
the union bound). It states the ANSWER first; §39.6 keeps the refuted routes as
a short ledger so they are not re-attempted.*

### 39.1 The problem

`mixKernels_ok` needs `hstab`: every β-external's row to every kernel chain must
be CONSTANT across that kernel's phase window. The apparent obstruction was an
ordering cycle — `externals_stabilize` supplies a horizon only for externals
known IN ADVANCE, while `kernel_site`'s `DR`/`PP` phase-witnesses are picked
AFTER the base (above the segment, so backward forcing covers the window). For
one kernel this is harmless; across kernels it appears circular, since a witness
of kernel `k` is an external of kernel `k'`.

### 39.2 The resolution: pick the whole bank ABOVE the candidate range

**The cycle was an artifact of picking witnesses too low.** `witness_sets_decreasing`
(certified) says `W_n = {w : ρ (c n) w = r}` SHRINKS as `n` grows — backward
forcing. So a witness picked at a level at or above the top of a window serves
EVERY position of that window. Therefore:

> fix the candidate range first, pick the entire witness bank ABOVE it, and the
> bank no longer depends on where the bases land.

The kernels then DECOUPLE: each base need only dodge the finitely many values
spoiled by the other kernels' already-fixed witnesses. No scheduling, no fixed
point, no product counting.

### 39.3 The two certified halves of `MixSelect`

`MixSelect` (the Lean `def`) asks, per kernel and per `DR`/`PP` phase demand, for
a witness that (i) serves the demand across that kernel's whole window and
(ii) has a constant row on EVERY kernel's window.

| half | theorem | content |
|---|---|---|
| (i) SERVING | `mixSelect_of_highBank` | a bank at or above each window's top serves the window outright, by `witness_sets_decreasing` |
| (ii) STABILITY | `exists_stable_base` | a `p`-spaced candidate list longer than `2·|ws|` contains a base whose window is constant for the WHOLE bank |

Supporting chain, all `propext`-only:

```
rank_eq_imp_value_eq      equal stabRank at i <= k PINS the value
  → row_no_return         equal values at two positions ⟹ constant between
  → ends_differ_rank_lt   differing endpoints ⟹ STRICT rank increase
  → three_spaced_not_all_bad   among 3 candidates spaced >= p, one window is
                               constant (3 bad ⟹ rank >= 3 > stabRank's ceiling)
  → spoiled_length_le_two      list form: each witness spoils <= 2 spaced candidates
  → exists_good_candidate      pigeonhole, survivors shrink by <= 2 per witness
  → exists_stable_base         the base choice
```

plus `window_const_iff_ends` (a window is constant iff its two ENDS agree),
`stab_window_family` / `stab_window_family_multi` (one horizon for a fixed finite
bank), and `window_stab_dichotomy` (stay-low ⊎ push-past, both branches).

### 39.4 Two interface facts worth remembering

- **`hstab` is on the PHASE WINDOW** (`a < pk k`), not the whole chain. The
  unrestricted form was strictly too strong to be discharged by the extraction's
  own machinery: `kernel_site` delivers only the window fact, so as originally
  stated `mixKernels_ok` REJECTED exactly the witnesses the extraction produces.
  Fixed; pre-known externals still give the stronger form via `StabKernelPack.stab`.
- **Period 1 makes `hstab` vacuous** (`a < 1` forces `a = 0`). The whole issue
  only ever concerned genuinely multi-phase (round-robin) kernels.

### 39.5 Instantiation — the per-kernel interface, DONE

The stability half is now discharged at real extraction data, not just as a
reusable lemma:

- `exists_spaced_list` — a cofinal predicate yields a list of any length,
  pairwise spaced `≥ p` (built by recursion above a running threshold).
- `cofinal_fixed_param` — `rr_segment_from`'s period varies with the base, but
  the periods are BOUNDED, so one period value still recurs cofinally. (This is
  why `rr_segment_from` now also returns its period bound `p ≤ |types|·|Ds|`,
  which the original statement discarded.)
- `exists_stable_recurrence` — among the cofinally many bases of that fixed
  period, one has a window constant for the entire bank.
- **`kernel_interface_of_persistAll`** — the capstone: from a `persistAll` site
  and a finite witness bank, a base `i` and period `q > 0` with
  `mty (c i) = mty (c (i+q))` (`mixKernels_ok`'s `hty`) AND constant external
  rows across the window (its `hstab`).

So per kernel, `hty` and `hstab` both come from model-side data. With
`mixSelect_of_highBank` giving the serving side and the high bank making the
kernels independent, the per-kernel interface is complete.

**The family, assembled.** `family_interface` discharges TOGETHER, from
model-side data, every per-kernel obligation of `mixKernels_ok` except the demand
routing: `hp`, `hty`, `hstab` and `hrectQ`. Given `n` `persistAll` sites whose
class towers are pairwise non-comparable (`classify_cross` disjunct 1 —
comparable ones merged away by §38) and a global witness bank, it produces bases
and periods satisfying all four.

The scheduling that made §39 look circular is handled by the THRESHOLD: the joint
cross-constancy horizon `B` is computed FIRST (`exists_bound2` over the finitely
many pairs), and each kernel's base is then chosen above `B` — possible because
`kernel_interface_of_persistAll` delivers its base past ANY threshold. So
`hrectQ` and `hty`/`hstab` hold at the SAME bases, with no iteration.

Non-vacuity: `family_interface_nonvacuous` runs it on the two-region `Ipo` model
with a NONEMPTY bank whose witness sits ON one of the chains — so that row is not
globally constant (`chain 0 5 = PP`, `chain 6 5 = PPI`) and the theorem must
actually place the window past the transition.

**The candidate range, exposed before the bank.** One subtlety had to be got
right for the high-bank construction to be formally coherent:
`exists_stable_base` needs a candidate list longer than `2·|ws|`, yet the bank
must be picked ABOVE the candidate range — circular if the list length is driven
by `|ws|`. It is not, because the bank size is bounded A PRIORI (kernels × phase
types × demands, all bounded by `C₀`). Taking a size bound `S` as input, the
range is built FIRST and its top exposed, and only then is the bank quantified:

```
stable_base_range          ∃ M, ∀ ws, |ws| ≤ S → ∃ i, i + p ≤ M ∧ P i ∧ stable
kernel_range_of_persistAll ∃ q M, ∀ ws, |ws| ≤ S → ∃ i, …  (period first, then M)
family_range               ∃ pk M, ∀ ws, |ws| ≤ S → ∃ ik, hty ∧ hstab ∧ hrectQ
                                                     ∧ every window ends ≤ M k
```

The quantifier order `M` **before** `ws` is the whole content: the caller picks
the bank at or above the `M k`, `mixSelect_of_highBank` then makes it serve every
window (all of which end at or below `M k`), and `family_range` has already
delivered stability, recurrence and the cross-rectangle.

**The bank, supplied.** `exists_bank`: for a chain whose types recur cofinally
past `T`, and any level `M`, a witness list of size at most `2·|cl C0|` such that
EVERY `DR`/`PP` demand occurring at any phase past `T` is served by a member
`r`-related to the chain at every level up to `M` — in particular AT `M` (what
`mixSelect_of_highBank` consumes) and at every lower level (so it serves any
window ending at or below `M`). One slot per `(D, r)` with `D ∈ cl C0`,
`r ∈ {DR, PP}`, filled by `dr_witness_all_below` / `pp_witness_all_below` at
bound `M` where possible and by the filler `c 0` otherwise — so the size bound is
STRUCTURAL, independent of the model. Covering uses `cl_ex` (a demand's argument
is itself in the closure, so it has a slot).

`family_range` also takes a threshold `L`, so the bases clear the bank's
recurrent-tail bound `T` as well as the cross-constancy horizon `B` (it uses
`max B L`). Without it the two halves would not have composed.

### 39.7 The final assembly — DONE: `mixSelect_assembled`

The five-step recipe is now a theorem. From `n` `persistAll` sites whose class
towers are pairwise NON-COMPARABLE (`classify_cross` disjunct 1; comparable ones
merged away by §38), `mixSelect_assembled` produces bases and periods satisfying
`hp`, `hty`, `hrectQ` **and** `MixSelect` — every per-kernel obligation of
`mixKernels_ok` except the demand routing.

```
1  recurrent_tail per chain     ⟹ threshold T (max over the finitely many kernels)
2  family_range … S T hN hconst ⟹ periods pk, range tops M     [S := n·2·|cl C0|]
                                   -- computed BEFORE any bank exists
3  exists_bank per kernel AT M k ⟹ banks ≤ 2·|cl C0|; concatenated over Fin n
                                   they stay within S (flatMap_length_le)
4  feed that bank back to family_range ⟹ bases ik with hty, hstab, hrectQ,
                                   windows ending ≤ M k, bases ≥ T
5  mixSelect_of_highBank        ⟹ MixSelect (the bank sits at the range top, so
                                   backward forcing serves every window)
```

`hinj` comes separately from `cross_const_ne_eq`.

**What the ordering buys.** Steps 2 and 3 are the resolution of §39 in executable
form: the range top `M` is fixed before the bank exists, the bank is then placed
at `M`, and only then are the bases chosen inside the range. Nothing is ever
chosen twice, and no iteration or fixed point appears anywhere.

### 39.8 Coverage — the external cases of `hk_ex`

`hk_ex` routes a phase demand `∃r.D` four ways: an external, up the kernel's own
chain, reflexively (`∃EQ`), or into another kernel. The external route needs a
bank per relation, and the two orientations need OPPOSITE picking disciplines:

| `r` | discipline | lemma |
|---|---|---|
| `DR`, `PP` | LATE — witness above the range, backward forcing down through the window | `exists_bank` |
| `PPI` | EARLY — witness with a uniform anchor, forward absorption keeping it inside every later position | `exists_bank_ppi` |
| `EQ` | reflexive, no external | `seg_ex_eq` |
| `PP` (chain) | up the kernel's own chain | `rr_covers` |
| `PO` | pool | open — see below |

`exists_bank_ppi` has the mirrored shape (`∀ b ≥ A` rather than `∀ b ≤ M`), with
ONE anchor `A` covering all types at once (`ppi_witness_bank`); its size bound is
again structural (one slot per `D ∈ cl C0`).

**Coverage status:**

- **`∃PO` demands — PROBED (`wp91` parts V/W); the external bank provably does
  NOT work.** `DR`/`PP` are carried across a whole window by ONE high pick
  because `comp(PP,DR) = {DR}` and `comp(PP,PP) = {PP}` force the window from
  above. `PO` has no such law: `comp(PP,PO) = {DR,PO,PP}`. Its only law is
  UPWARD and weak — `comp(PPI,PO) = {PO,PPI}`, certified as `po_up`: an
  overlapping external stays overlapping-or-swallowed later, but says nothing
  lower down.

  Part W makes this decisive with an adversarial family: chain `c_j = {e_0..e_j}`
  and witnesses `w_j = {e_j, e_{j+1}}` give `DR` at level `j-1`, `PO` at exactly
  level `j`, `PPI` at level `j+1`. So every witness is `PO` at a SINGLE level,
  the demand is live everywhere, and **no external is `PO` across a window of
  length ≥ 2, at any base.** Since `hk_ex`'s external disjunct needs the declared
  row (constant across the window by `hstab`) to BE the demanded relation, no
  β-external can serve such a demand.

  So `∃PO` at kernel phases cannot be served by a β-external **in the READ-OFF
  architecture** (`mixKernels`, whose `K k e := ρ (ck k (ik k)) (g e)` is the
  model's own relation), and there it requires the pool machinery.

  > **CORRECTION (2026-08-20).** This was first written as "`∃PO` requires the
  > pool machinery, an ARCHITECTURAL necessity" — too broad. Part W's mathematics
  > is right (no model-true `PO` relation is constant across a window), but
  > `hk_ex`'s external disjunct compares the DECLARED `K` value, not the model's.
  > The **PO-DEFAULT** architecture already in the file — `mtkKernelsDR`, with
  > `K k e := ppi | dr | po` and `Q := po` DECLARED rather than read off — serves
  > `∃PO.D` at a phase by any external carrying `D`, since its declared `K` is
  > already `PO`. Soundness is unaffected because `multiTier_sound` builds a NEW
  > model, and ∀PO-freeness (`mixKernels_noPo`/`mtkKernelsDR_nopo`) makes the
  > declared `PO` edges obligation-free. So the pool is needed for the read-off
  > route, not universally.

### 39.9 The pool interface, wired

Two lemmas connect the mixed construction to the pool machinery:

- **`mixKernels_pool_ok`** — `mixKernels_ok` with `∃PO` demands allowed to PEND:
  `e_ex`/`k_ex` may also discharge a demand by `r = PO` plus a pool entry with a
  DIFFERENT tag. This is exactly the interface part W forces — such a demand
  provably cannot stay inside the block.
- **`mixKernels_noPo`** — `glueFam_ok`'s side condition, FREE here: every label
  of `mixKernels` is an `mty`, and a ∀PO-free `C0` has no `∀PO` in its closure
  (`mty_no_all_po`). This is what lets the glue declare every cross-block edge
  `PO` without firing an obligation — the fragment's defining escape valve, doing
  real work.

**The intended shape of the remaining construction** (scoped, not built): blocks
= the main mixed block plus, for each `∃PO`-subformula `D` of `C0`, library
blocks rooted at model nodes carrying `D`; pool entries = (tag, that root's
label); `hreal` holds at the root by construction. Note the blocks are NOT
recursive — all are extracted from the SAME fixed model in parallel, so there is
no descent to justify. Two copies per `D` (distinct tags) handle the
self-reference case where `D`'s own library demands `∃PO.D`. And the glue's
declared `PO` need not match the model: `multiTier_sound` builds a NEW model, and
`mixKernels_noPo` makes the declared edges obligation-free.

**The pool bookkeeping, done.** Both halves are now certified, and neither
depends on HOW the individual blocks are built:

- `pool_two_copies` — COVERING. A pending `∃PO.D` is admissible only against a
  DIFFERENT tag, so a library for `D` cannot serve its own `∃PO.D`. Duplicating
  each concept's entry under tags `2i` and `2i+1` removes that outright:
  whichever tag is asking, the other copy answers. No well-founded descent
  between libraries is needed — the pool condition is only tag-difference, so
  mutually demanding libraries are fine.
- `pool_realized` — REALIZATION (`glueFam_ok`'s `hreal`). With `2n` blocks, block
  `b` rooted at a node whose label contains the entry for concept `b/2` (blocks
  `2j`, `2j+1` being two copies rooted at the SAME model node), every pool entry
  is realized in the block carrying its tag.
- `pool_two_copies_length` — the pool has exactly `2n` entries, the bound the
  finite-code layer will want.

**Remaining for mixing:** the per-root block extraction (each library block is
itself a mixed certificate for a model node carrying `D` — the same construction
applied in parallel, not a recursion), `he_ex` for β-externals, and `codesM`.
- **`he_ex`** — the same routing for β-externals rather than phases (horizontal
  disjuncts from `ascNodes_covers`).
- **`codesM`** + the `decidableSat_of_codes` completeness premise.
- Independently: **one-shot `∃PP`** (§33/§34), still open, still vertical.
2. **Coverage** (`he_ex`/`hk_ex`) and **`codesM`** + the `decidableSat_of_codes`
   premise.
3. Independently: **one-shot `∃PP`** (§33/§34) is still open and is still
   vertical.

### 39.6 Ledger of refuted routes (do not re-attempt)

Kept deliberately: each was refuted with a machine-checked witness in
`verification/python/wp91_mixing_order_cycle.py`, and the reasons are the useful
part.

| route | verdict | why |
|---|---|---|
| R4: witness cofinally `DR` from its own chain, free cross-constancy | **false** | part B — non-comparable chains, row `DR,DR,DR` vs `DR,PPI,PPI` |
| pre-commit bases past a bound | **false** | part C — the horizon is UNBOUNDED (family realizing horizon exactly `N` for every `N`) |
| R4′: witness cofinally `DR` from EVERY other chain | **false** | part F1 — evens/odds towers, every witness swallowed by the odd tower |
| base-independent witness bank | **false** | part F2 — a chain exhausting the universe swallows every fixed region |
| all windows at one common late level | **false** | part M — up to 35% failure (4 kernels, base 6, period 3) |
| fixed-order staged greedy | **false** | part O — up to 44.3% failure, while a valid vector exists ~always |
| some-order staged greedy | circular | part P — works empirically, but restates the existence claim |
| cofinal-witness collapse (`mixSelect_of_cofinal_bank`) | true but not general | part Q — sufficient, and CERTIFIED, but the escaping family has `⋂ W_n = ∅` |
| union bound over `Fin m → Fin R` | correct but unnecessary | superseded by the high bank, which decouples the kernels |

**Probe evidence for the resolution** (`wp91`, all parts PASS): existence never
failed in ~10,700 configurations (2–4 kernels, densities to 12 slots, `DR` and
`PP` demands, late bases, truncation excluded); solutions are ABUNDANT (mean
0.55–0.66 of base vectors valid, worst 0.36–0.50, never zero); and part U's
high-bank construction scored 400/400 on all three checks, with the spoil bound
`2(p-1)` tight.

**Two methodological traps this session hit, both worth remembering.** (a) The
FINITE-PREFIX trap, twice: a chain no longer than the witness list leaves the
last witness untested, which reads as a false "cofinal" or a false failure — run
the chain longer than whatever is being tested (parts K, Q). (b) Re-framing an
obstacle in new vocabulary is not progress: the bad-position bound was recorded
in the first working notes and then mis-framed as a fixed point, then as a staged
construction, before the high bank dissolved it.

## 40. ARCHITECTURE FORK: read-off vs PO-default (2026-08-20)

> **THE COMPARISON IN THIS SECTION IS INCOMPLETE — see §42.** It weighs
> read-off against PO-default and recommends PO-default on cost grounds, without
> checking that PO-default is EXPRESSIVE ENOUGH. It is not (§41.1). The correct
> conclusion is the opposite one: read-off is the general architecture, and its
> extra obligations are the price of that generality.

Scoping `he_ex` surfaced that the file contains TWO mixed-certificate
architectures, and the campaign's §35 pinned the summit to the more expensive one
without recording the comparison. Stating it now so the choice is deliberate.

| | **read-off** (`mixKernels`) | **PO-default** (`mtkKernelsDR`) |
|---|---|---|
| `E`/`K`/`Q` | the model's own relations | DECLARED: `E ∈ {eq,dr,po}`, `K ∈ {ppi,dr,po}`, `Q ≡ po` |
| labels | `mty` (full model type) | `mtk` (truncated by modal depth) |
| `hstab` | REQUIRED — the whole §39 apparatus | none |
| `hrectQ` | REQUIRED | none (`Q ≡ po`, and `∀PO`-free ⟹ vacuous) |
| `∃PO` at a phase | needs the POOL (part W) | FREE — declared `K = po` to any external carrying `D` |
| directions | BOTH (`up := dir`) | ASCENDING only (`up _ := true`) |
| model-side debts | `hstab`, `hrectQ`, banks | `hv0pp`, `hdr` (DR children genuinely `DR` to every phase), `hee`, closure |
| reaches | `MultiTierOk` | `Satisfiable C0` directly (`extract_dr_children`) |

**What this means for today's work.** §39's machinery (`hstab`, `hrectQ`, the
high bank, the base selection, `mixSelect_assembled`) is certified and general,
but it pays for the read-off frame. The PO-default route avoids those obligations
entirely — and its model-side debts are things already built (`exists_bank` gives
DR witnesses `DR` to everything below; the chain gives `hv0pp`).

**Why it is not simply better.** PO-default as built is ASCENDING-ONLY. The
∀PO-free fragment needs both directions (`∃PP` and `∃PPI` towers, §24). So either
(a) the PO-default certificate is generalized with `up := dir` — the frame is
independent of direction, and `kk_pp`/`kk_ppi` already branch on it in
`mixKernels_ok`, so this looks modest; or (b) the read-off route is carried
through as planned.

### 40.1 Option (c) probed — `wp92`, all parts PASS

Before committing to either route, the frame's CAPACITY was checked
exhaustively (`verification/python/wp92_podefault_frame_capacity.py`, composition
closure + converse coherence of the declared net):

- **B — arbitrarily many `PPI`-children.** `mtkKernelsDR` declares only one (to
  `v0`), but the frame is closed with any number: `u–u'` may be `PO`, while
  `u–d` is FORCED `DR` (`comp(PP,DR) = {DR}`). So `∃PPI` at a phase is coverable,
  which is exactly what a `dir`-generalization needs — and `exists_bank_ppi`
  already supplies such children.
- **C — the `DR` skeleton is free.** Every `dadj` pattern among the `DR`-children
  is closed (296 skeletons swept); the skeleton imposes no extra burden.
- **D — `PP` SIBLINGS are free; only `PP` CHAINS break.** Two `PP`-children of
  one phase are fine PO-defaulted (`comp(PPI,PP)` is unrestricted). The violation
  needs `e PP w PP g` with `e–g` defaulted, where `comp(PP,PP) = {PP}` forces the
  non-adjacent pair.
- **E — hence one-shot `∃PP` IS servable.** A `PP`-child attached at a phase,
  with the edge propagated DOWN the chain (`p_j PP w` for `j ≤ i`, forced) and
  `PO` above, is closed at every attachment point.

**A correction this forces to §33.** §33 recorded that a one-shot `∃PP` "cannot
be a `PP` edge in the β-frame" because `comp(PP,PP) = {PP}` forces the transitive
edge. That argument silently assumes the `PP`-child ITSELF has a `PP`-successor.
Without one there is no chain and no violation. So the gap is not "one-shot
`∃PP`" but specifically **NESTED `∃PP`** — which matches `ascNodes`' own deferred
"non-nested restriction", and is a materially smaller open item than §33 claims.

*(Method note: part D initially tested two `PP`-siblings, found no violation, and
I read that as the probe failing. It was the probe correcting me — siblings
really are fine, and the obstruction is chaining. The wrong model produced the
right information.)*

**Recommendation: (a), now better supported.** A `dir`-generalized PO-default
certificate is not blocked by frame capacity on any side the fragment needs. It
would put the §39 apparatus off the critical path (still correct, still reusable)
and remove the `∃PO` pool requirement at phases. The residual open item is nested
`∃PP`, which is independent of the architecture choice — it is a frame fact, not
an artifact of read-off vs PO-default.
### 40.2 Route (a) begun: the generalized PO-default frame

`po_dr_multi_kernel_frame'` — `po_dr_multi_kernel_frame` with ARBITRARILY MANY
`PPI`-children per kernel (`kppi : κ → β → Bool`) in place of the single root
`v0`. This is the foundation a `dir`-generalized PO-default certificate needs:
`∃PPI` at a phase is served by a `PPI`-child, and `exists_bank_ppi` already
supplies them.

`wp92` part B predicted the capacity; deriving the coherence conditions from the
composition table confirmed that **only ONE edge is forced** — `PPI`-child vs
`DR`-child must be `DR` (`comp(conv PPI, DR) = {DR}`). Nothing is owed between
two `PPI`-children, since `net(u,k) = PP` and `PP ∈ comp(DR,PP) ∩ comp(PO,PP)`,
so `dadj` may be either there. So `hcoh` generalizes to "every `DR`-child is
`dadj`-adjacent to every `PPI`-child" and the rest of the 212-line case analysis
ports mechanically. The three genuinely NEW branches are the two-`PPI`-children
cases, vacuous when there was a single `v0`.

*(A hand-derivation error caught by the table: I first reasoned that two
`PPI`-children must be non-adjacent, from `comp(DR,PPI) = {DR}`. That conflated
`K k u` — the kernel-to-child value `PPI` — with `net(u,k)`, which is its
converse `PP`. The frame condition uses the latter. Checking against the derived
table rather than trusting the hand argument is what caught it.)*

### 40.3 The `dir`-generalized certificate, CERTIFIED

`mtkKernelsDir` / `mtkKernelsDir_ok` — `mtkKernelsDR` with BOTH generalizations
the fragment needs:

- **kernels of either direction** (`up := dir`), so `∃PP` towers and `∃PPI`
  towers coexist — what `mtkKernelsDR` (ascending-only) could not express;
- **arbitrarily many `PPI`-children** per kernel (`kppi`) instead of the single
  root `v0`, so `∃PPI` demands at a phase are coverable.

`E`/`K`/`Q` stay DECLARED with `Q ≡ po`, so there is **no `hstab` and no
`hrectQ`**, and `∃PO` at a phase is served by any external carrying the argument
— no pool. The model-side debts are only `hup` (every `PPI`-child genuinely
inside every phase) and `hdr` (every `DR`-child genuinely disjoint from every
phase), which `exists_bank_ppi` and `exists_bank` already supply.

Supporting lemmas added:

| lemma | content |
|---|---|
| `po_dr_multi_kernel_frame'` | the frame, with many `PPI`-children (§40.2) |
| `dmtk_kk_pp`, `dmtk_kk_ppi` | descending mirrors at the `mtk` level |
| `mtk_kk_pp_dir`, `mtk_kk_ppi_dir` | direction-branching `∀PP`/`∀PPI` propagation |
| `podefault_ek_dir`, `podefault_ke_dir` | `∀`-propagation with many `PPI`-children and an explicit per-kernel phase budget `bk` |

`kq_all` remains vacuous — `Q ≡ po` and the fragment has no `∀PO`
(`mty_no_all_po`). That is the ∀PO-freeness doing the load-bearing work, exactly
as in the glue.

### 40.4 Entry point and witness

- `extract_dir_children` — the entry point mirroring `extract_dr_children`:
  valid PO-default data of either direction plus a root carrying `C0` gives
  `Satisfiable C0`, via `mtkKernelsDir_ok` and `multiTier_sound`.
- `mtkKernelsDir_two_ppi_children` — non-vacuity, exercising the generalization
  the OLD frame could not express: one ascending kernel with **two distinct
  `PPI`-children** (earlier positions of the same `Ipo` chain, both `PP`-inside
  every phase), `kdr` empty so `hcoh` is vacuous, `dadj` empty so the only
  external-external values are `EQ` on the diagonal and the `PO` default — the
  latter obligation-free by ∀PO-freeness. `Cvert`'s demand routes into the
  kernel from an external (`conv (K k e) = conv PPI = PP`) and up the chain from
  a phase.

**A model carrying BOTH directions — built.** `Ivert` ascends on ℕ and `Idalt`
descends on ℕ; neither does both, so `dir = false` had no witness. `Idir` fixes
that: two regions, one ordered by `chain` (ascending in the index), one by its
TRANSPOSE (descending in the index), cross-related `PO`, with `A₀` true in the
ascending region only. The transpose of a linear order is a linear order, so the
only new fact needed was `rchain_cc` (the reversed composition), and
`dirRho_frame`/`Idir_rcc5` follow by case analysis on the two region bits.

**An architectural limitation found while designing the witness.** In
`mtkKernelsDir`, `K` ranges over `{PPI, DR, PO}` and `E` over `{EQ, DR, PO}`.
So `conv (K k e)` ranges over `{PP, DR, PO}` — it is **never `PPI`**. Consequently
an EXTERNAL's `∃PPI` demand cannot be served at all: not by another external
(`E` has no `PPI`), and not by a kernel (`conv K` has no `PPI`). Externals may
therefore carry `∃PP`, `∃DR`, `∃PO`, `∃EQ` demands but not `∃PPI`.

That is a real constraint on which model nodes may be externals, and it is NOT
an artifact of the `dir` generalization — `mtkKernelsDR` has the same `K` range.
Adding a `PP`-valued `K` edge would fix it, but that re-enters the `PP`-chaining
obstruction (`wp92` part D), so it is not free. Recorded here rather than
discovered later during coverage.

**The `dir` generalization is now witnessed firing.**
`mtkKernelsDir_both_directions`: `κ = Bool` with `dir = id` — kernel `true` an
ASCENDING `PP`-chain through `Idir`'s ascending region, kernel `false` a
genuinely DESCENDING `PPI`-chain through the descending region. `mtkKernelsDR`
cannot state this at all (`up` is constantly `true`).

`β = Empty`, so every external obligation is vacuous and the cross-kernel
`Q ≡ po` is obligation-free by ∀PO-freeness. The ascending kernel serves its own
`∃PP.A₀` up its chain; the descending kernel's phases carry NOTHING (`dirempty`
— past the top of the descending region no closure concept holds, since `A₀`
lives only in the ascending region), so its `hk_ex` is vacuous while its
`kk_pp`/`kk_ppi` still run through the `dir = false` branch of `mtk_kk_*_dir`.

Supporting: `dirfull` (the ascending region realizes the whole closure, so the
type is constant there) and `dirempty` (the descending region past the top
realizes nothing, so the type is constant there too — both give `hty` for free).

So both halves of §40.3's generalization are now witnessed: many `PPI`-children
(`mtkKernelsDir_two_ppi_children`) and both directions
(`mtkKernelsDir_both_directions`).

### 40.5 Remaining on route (a)

- **Extraction into this certificate**: supply `g`/`bud`/`bk`/`dadj`/`kppi`/`kdr`
  and the routing hypotheses (`hee`, `he_ex`, `hk_ex`) from a model. The
  vertical side is in hand (`towers_from_persistPP`, `class_kernel`,
  `exists_bank`, `exists_bank_ppi`); the horizontal closure is `ascNodes` /
  `ascNodes_covers` at `mtk` budgets.
- **Nested `∃PP`** (§33, as narrowed by `wp92` part E) — the one frame-level
  obstruction, independent of the architecture choice.
- **`codesM`** and the `decidableSat_of_codes` premise.
## 41. THE ROUTE TO THE GENERAL FRAGMENT (2026-08-20)

Michael asked, rightly, whether the accumulated restrictions were preventing
real progress, and — if we backtrack — for a route established in advance to
reach the goal rather than the next milestone. This section is that audit and
that route. Research: `verification/python/wp93_ordered_disjoint_frame.py`
(all parts PASS).

### 41.1 The audit: what was blocking generality

| # | restriction | removable? |
|---|---|---|
| 1 | externals cannot carry `∃PPI` (`E` has no `PPI` value) | yes — two `PPI`-siblings PO-defaulted are composition-CLOSED |
| 2 | one-shot `∃PP` at a phase | yes — `wp92` part E |
| 3 | kernels need PERSISTENT (∀PP-guarded) demands | yes, given 1–2 |
| 4 | **nested** `∃PP`/`∃PPI` | **no** — `comp(PP,PP) = {PP}` and `comp(PPI,PPI) = {PPI}` force the transitive edge, which a PO default contradicts |

Three were artifacts of the certificate's edge repertoire; the fourth is
structural. `∃DR.(∃PPI.A)` is ∀PO-free and was NOT coverable.

### 41.2 Why neither existing frame can be the answer

| frame | expresses | fatally missing |
|---|---|---|
| `posetNet` (`posetMT_ok`) | EQ, PP, PPI, PO | **DR** — incomparable is always `PO`, so `∃DR` is inexpressible |
| PO-default (`mtkKernelsDir`) | EQ, DR, PO (+`PPI`/`DR` on `K`) | **PP/PPI among externals** — so nesting and externals' `∃PPI` are inexpressible |

Both are special cases of the same thing, and each is missing exactly what the
other has.

### 41.3 The frame that can carry the goal: ORDERED-DISJOINT

```
odNet x y = EQ         if x = y
          = PP / PPI   if x < y / y < x
          = DR         if disj x y
          = PO         otherwise
```

This is precisely the RCC5 normal form already certified FORWARD in
`formal/RCC5NormalForm.lean` (`toOrderedDisjoint`). `wp93` establishes:

- **A — expressiveness.** All FIVE relations are realized. `posetNet` realizes
  four, the PO-default frame realizes three among externals.
- **B — soundness.** Composition-closed for EVERY ordered-disjoint structure:
  exhaustive over all 962 structures on ≤ 4 elements.
- **C — the proof plan.** All 25 cells are reachable; only **13 are forced**,
  and after the trivial `EQ`-cells the whole content is FOUR facts:
  `PP;PP = {PP}` and `PPI;PPI = {PPI}` (from `lt_trans`), `PP;DR = {DR}` and
  `DR;PPI = {DR}` (from `disj_down`).
- **D — nesting is fixed.** A `PP`-chain with its transitive edge PRESENT is
  closed, as is a chain with a `DR`-child disjoint from all of it. The order
  carries transitivity EXPLICITLY instead of PO-defaulting the non-adjacent
  pair — which is exactly what killed both other frames.

### 41.4 The route, end to end

1. **`odNet_frame`** — ordered-disjoint ⟹ `Frame`. The missing brick; content is
   the four forced cells of §41.3C. Ingredients already certified on arbitrary
   domains in `RCC5NormalForm.lean` (`eta`, `sub_iff_le`, `eta_injective`,
   `disj_iff_eta_disjoint`), and that file has **no `Frame` theorem** today.
2. **The general certificate** — a `MultiTier` whose `qnet E K Q` is `odNet` on
   the whole of `β ⊕ κ`: externals AND kernel bases are ordinary nodes of ONE
   ordered-disjoint structure. `frame_q` then follows from (1) directly. Kernel
   phase conditions (`kk_pp`/`kk_ppi`/`kk_eq`) are about the chain and are
   already certified, direction-branching included (`mtk_kk_*_dir`).
3. **Extraction** — `toOrderedDisjoint` (certified) reads the structure off ANY
   model; restrict to the chosen finite node set. Restriction preserves every
   `OrderedDisjoint` axiom (each is universally quantified over the carrier), so
   this step is free.
4. **Coverage** — every demand has an edge to serve it: `∃PP` an `lt`-above
   node, `∃PPI` an `lt`-below, `∃DR` a `disj` node, `∃PO` an incomparable
   non-disjoint one, `∃EQ` reflexively. Nesting included, by (D).
5. **Finiteness / decidability** — budget-truncated labels (`mtk`) bound the
   node set; then `codesM` + `decidableSat_of_codes`.

### 41.5 What carries over, and the honest risks

Carries over unchanged: `exists_bank`, `exists_bank_ppi`, the §38 merge, the
selection machinery, `Idir`/`rchain_cc`, `mtk_kk_*_dir`, `mty_no_all_po`, and
every model-side stabilization lemma. Becomes a special case: `mtkKernelsDir`
and its frame (`odNet` with empty `disj` is `posetNet`; with empty `lt` it is the
PO-default frame).

Risks, named in advance rather than discovered:
- **(5) is the real remaining unknown.** Bounding the node set for a general
  ∀PO-free concept is the K(C₀) counting problem; it is NOT settled by this
  research, and it is where a further surprise would most likely live.
- (2) needs `K` and `Q` to be ordered-disjoint-derived too, not just `E` — a
  restatement of the certificate, not new mathematics.
- (4) needs the coverage recursion to terminate at `mtk` budgets, as `ascNodes`
  does.

**This route is chosen because it is the only one probed to express all five
relations and to survive nesting.** Steps 1–4 are bounded; step 5 is the honest
open item, and it is the same counting problem the campaign has always had.

### 41.6 Step 1 DONE: `odNet_frame`

The missing brick is built. `ODStruct` (mirroring `RCC5NormalForm`'s
`OrderedDisjoint`), the induced `odNet`, four inversion lemmas
(`odNet_eq_inv`/`_pp_inv`/`_ppi_inv`/`_dr_inv`), and

> **`odNet_frame`** — every ordered-disjoint structure induces an RCC5 `Frame`.

Sixteen genuine cases, exactly as `wp93` part C predicted: four FORCED
(`PP;PP`, `PPI;PPI` by `ltTr`; `PP;DR`, `DR;PPI` by `djDown`), three absorbed
(`PP;PPI`, `DR;DR`, `PO;PO`), and nine needing one or two exclusions each,
every one discharged by an inversion lemma plus a single structure axiom.

Note the proof needed no `eta` machinery: the frame follows DIRECTLY from the
`OrderedDisjoint` axioms, so `RCC5NormalForm`'s set-representation
(`eta`, `sub_iff_le`, `disj_iff_eta_disjoint`) is not on the critical path for
this step — it remains the independent justification that such structures are
realizable.

**Method note.** Two false starts, both worth remembering: the case analysis is
unmanageable with `▸` transports (use `have e : x = z := …; subst e`), and I
initially worked from a hand-recalled composition table whose `PO;PPI` cell was
wrong — the real table has `[ppi, po, dr]`, matching set semantics. Reading the
actual table first would have saved a pass.

### 41.7 DE-RISKING step 5 before building — `wp94`, both parts PASS

Asked whether the flagged risk could be reduced ahead of committing sessions.
Two cheap moves, both done.

**(a) The `qnet` interface, checked in Lean (cheap, decisive).** Taking ONE
ordered-disjoint structure on the whole of `β ⊕ κ` — externals AND kernel bases
as ordinary nodes — and reading `E`/`K`/`Q` off it, the assembled `qnet` is
literally `odNet` again (`qnet_odNet`): the `inl/inr` case matches by `odNet`'s
converse law, the `inr/inr` diagonal by `odNet_self`. Hence **`frame_q_of_odNet`
— `frame_q` is FREE** for an ordered-disjoint certificate. That was step 2's
hardest field, removed for the cost of one lemma.

**(b) End-to-end acceptance test (`wp94`), the wp16 pattern.** Build the
certificate on real ∀PO-free concepts and models by the intended recipe, then
check every obligation:

- **Part A — 3,833 satisfiable ∀PO-free concepts**, each given a model by a
  reference search, node set built as the demand closure at `mtk` budgets,
  structure read off the model. **Every obligation holds on every instance**:
  `lt_trans`/`disj_down` (the read-off really IS ordered-disjoint), composition
  closure of the induced net, `ee_all` (universals propagate along `odNet`
  edges), and `e_ex` (every existential is served inside the node set).
- **Part B — the counting, i.e. the flagged risk.** Node count against the
  syntactic bound `|cl C0|^mdepth(C0)`, tabulated by `(|cl C0|, mdepth)`: the
  bound holds in every bucket, with large headroom (mean node count 1.6, worst
  10). Every recursive step drops the budget, so the closure is finite and
  bounded by a function of `C0` alone.

**Scope, stated honestly:** finite models only, so KERNELS (infinite periodic
towers) are NOT exercised by `wp94`. That half is already certified separately
(segment lemmas, `rr_covers`, `mtk_kk_*_dir`, the whole §38–§39 vertical
apparatus). What this probe de-risks is the `odNet` certificate and the counting
— which is precisely where §41.5 said a surprise would most likely live.

**Residual risk after de-risking.** The kernel/external SEAM: a certificate with
both `odNet` externals and periodic kernels, where a kernel base is a node of the
ordered-disjoint structure while its phases are not. `qnet_odNet` shows the frame
side composes; what is untested is the demand routing across that seam. That is
now the narrowest remaining unknown, and it is a smaller target than "the
counting problem".
### 41.8 Step 5's status, corrected (2026-08-20)

Asked directly whether §41.4 step 5 ("finiteness / `K(C₀)` / `codesM`") had
changed status after `wp94`. Checking rather than answering from memory found
that I had been carrying it as more open than it is. **The whole step-5 pattern
already exists and is certified** — twice — and step 5 is a re-instantiation of
it, not open research.

The existing chain, all kernel-checked:

```
mtkNodes_length_le   (mtkNodes n).length ≤ mtkBound C0 n.k
                     mtkBound C0 (k+1) = 1 + |cl C0| · mtkBound C0 k
  → encodeHF_mem_codes   the encoded certificate IS in the fixed enumeration
                          `codes C0`, using exactly that bound
  → decidableSat_of_codes  fixed enum + completeness premise ⟹ Decidable
  → decidableSat_hfrag     Decidable (Satisfiable C0) for the horizontal fragment
```

and the same pattern again on the vertical side via `codesV`
(`decidableSat_vtower` and its three variants). So the node bound, the encoder,
the code enumeration and the completeness premise are a WORKING, CERTIFIED
pipeline — twice instantiated.

Note also that `wp94` part B's measured bound `|cl C0|^mdepth(C0)` is exactly
`mtkBound`'s shape (`1 + |cl C0|·prev`), so the probe was re-measuring a bound
the file already proves.

**Revised status of step 5.** Not "the honest open item where a surprise would
most likely live". It is: write `encodeOD`/`codesOD` for the ordered-disjoint
node set and its membership lemma, mirroring `encodeHF_mem_codes`. Known shape,
existing template, certified prerequisites.

**What genuinely remains open**, restated honestly:
1. **The kernel/external seam** (§41.7) — routing demands in a certificate that
   has BOTH `odNet` externals and periodic kernels. The frame side composes
   (`qnet_odNet`); the routing is untested. This is now the narrowest unknown.
2. Steps 2–4 as engineering: the certificate, the extraction, the coverage.
3. Counting for the COMBINED case — `mtkBound` counts externals, `codesV`
   counts kernel phases; the general certificate needs both at once. Mechanical,
   but not literally either existing instance.

The honest summary: what I had labelled the riskiest step turns out to have a
certified template, and the risk has migrated to the kernel/external seam, which
is a much smaller and more concrete target.
### 41.9 The kernel/external seam, probed — `wp95`

The narrowest remaining unknown from §41.8, probed on PERIODIC models (which
`wp94` could not reach, being restricted to finite ones).

- **Part A.** Over 27,000 (model, window) pairs, **every** external had a
  CONSTANT row across the phase window; not one non-constant case arose. That is
  not luck: the externals the generator builds are exactly the ones the certified
  banks produce — a `DR`-child disjoint from the whole tower, a `PPI`-child
  inside it, a `PO`-external meeting the base — and each is constant BY
  CONSTRUCTION.
- **Part B.** On the declarable externals the seam net is composition-closed in
  all 12,000 windows, and the declarables still cover ≥2 distinct child kinds in
  all of them. Closure is what the certificate needs; coverage is what the
  routing needs; there is no gap between the columns.
- **Part C — the structural reason.** A phase-to-external row is constant across
  a window iff it does not straddle a transition (`row_no_return`, certified).
  For an ascending tower the row is rank-monotone `DR/PP → PO/EQ → PPI`, so a
  `DR`-child picked ABOVE the window is `DR` at every phase, and a `PPI`-child
  picked BELOW it is `PPI` at every phase — free, in both cases. Those are
  exactly `exists_bank` (late picking) and `exists_bank_ppi` (early picking with
  a uniform anchor), **both already certified**.

**Conclusion.** The seam's routing requirement is supplied by machinery that
already exists; what is unwritten is the wiring, not a new fact. Combined with
§41.8 (the counting pipeline exists and is certified twice) and §41.7
(`frame_q` is free), the ordered-disjoint route has **no identified open
mathematical question** — every remaining item is assembly over certified parts.

That is a claim about identified risk, not a guarantee: the campaign's ledger
says a defect or overclaim has appeared in all but two of seventeen reviews, and
none of this is reviewed.

### 41.10 `CERTIFIED_INVENTORY.md` — against re-deriving what exists

Twice in one session I treated certified machinery as absent: the two
certificate architectures (§40) and the entire step-5 encoding pipeline (§41.8).
Each cost real work. `CERTIFIED_INVENTORY.md` now lists the load-bearing results
by ROLE — decidability results, soundness core, frames, certificate validity,
finiteness/encoding, extraction, model-side analysis — and is to be consulted
before designing anything.

It also serves the eventual SLIMMING: the file has 1,036 top-level declarations
and 364 `#print axioms` lines, of which the core needed for the fragment's
decidability is a small subset; the rest is scaffolding, superseded routes
(read-off `mixKernels`, PO-default `mtkKernelsDir`, `posetNet`) and witnesses.
## 42. CORRECTION: the §40–§41 pivot was unnecessary (2026-08-20)

**The read-off certificate `mixKernels` was already general. The pivot to an
ordered-disjoint frame answered a question about a different architecture.**

### 42.1 The error

§40 compared two certificate architectures and recommended PO-default
(`mtkKernelsDir`) because its obligations are cheaper — no `hstab`, no `hrectQ`,
`∃PO` free. §41 then audited PO-default, correctly found four restrictions (one
structural: NESTING), correctly concluded that neither PO-default nor `posetNet`
can reach the general fragment, and pivoted to `odNet`.

Every step of that is sound **about the frames it examined**. The error is what
it did not examine: **`mixKernels`, whose `E e f := I.rho (g e) (g f)` is the
MODEL's own relation.** Therefore

- externals CAN carry `∃PPI` — `E e f = ppi` is simply available;
- one-shot `∃PP` is fine — `E e f = pp` likewise;
- **NESTING is automatic** — for `e ⊂ w ⊂ g` the model already has
  `E e g = pp`, so there is no PO-default to contradict transitivity.

None of §41.1's four restrictions apply to it. They are restrictions of the
PO-default frame.

### 42.2 What `odNet` was for, and whether it is needed

`odNet_frame` proves: an ordered-disjoint structure induces an RCC5 `Frame`. It
was built to supply `frame_q` for a general certificate. But `readoff_qnet_frame`
ALREADY supplies `frame_q` for a read-off certificate, under a **weaker**
hypothesis — that the chosen representatives are distinct (`hinj`) — where
`odNet` needs the full ordered-disjoint axiom set.

So `odNet_frame`, `qnet_odNet` and `frame_q_of_odNet` are genuine certified
theorems that are **not on the critical path**. They would matter for a
certificate CONSTRUCTED rather than read off a model; that is not this route.

### 42.3 Restored route

The live route is §35–§39: read-off `mixKernels`, with `hstab`/`hrectQ`
discharged by the §39 apparatus — `exists_bank`, `exists_bank_ppi`,
`mixSelect_of_highBank`, `exists_stable_base`, `family_range`,
`mixSelect_assembled`, the §38 merge. Remaining: `he_ex`/`hk_ex` coverage,
`encodeM`/`codesM` (mirroring the certified `encodeHF_mem_codes` pattern), and
the `decidableSat_of_codes` premise.

### 42.3b The gap the restored route actually had: `mixKernelsK`

Back on the read-off route, classifying every `MultiTier` definition in the file
by (relation source, label kind) — by reading the definitions, per §42.4 —
showed a clean split with one empty cell:

| | `mty` labels (untruncated) | `mtk` labels (truncated) |
|---|---|---|
| **read-off** relations | `mixKernels`, `vkernel*`, `mixKernel*` | *(empty)* |
| **declared** relations | — | `mtkKernels*`, `posetMT`, `chainMT` |

Read-off gives generality (the model's own relations: all five values, nesting
for free); `mtk` truncation gives FINITENESS, which is what `mtkNodes_length_le`
and the `codes` pipeline consume. The route needs both, and the combination did
not exist — which is why step 5's certified counting did not yet apply to
`mixKernels`.

**`mixKernelsK` / `mixKernelsK_ok`** fill that cell: read-off `E`/`K`/`Q` with
`mtk` labels. Obligations are `mixKernels_ok`'s (`hstab`, `hrectQ` — the §39
apparatus) plus four BUDGET side-conditions, which are the whole price of
truncation. `frame_q` is `readoff_qnet_frame`, so it needs only distinct
representatives.

The budget arithmetic has one subtlety worth recording: a `∀`-membership costs
one level (`mdepth (all r cc) = 1 + mdepth cc`), so a source budget `b ≤ b' + 1`
suffices — the same trick `podefault_ek_dir` uses. A naive re-budgeting lemma
that ignores this is unprovable.

### 42.5 Coverage on the restored route, and the one design point it turns on

With `mixKernelsK`'s labels finally matching, the existing closure applies:

- **`mtkNodes_covers` covers EVERY relation**, not just the horizontal ones —
  for any `m` in the closure and any `∃r.c` in its label there is a closure node
  `m'` with `ρ m.x m'.x = r` and `c` in ITS label. With read-off `E` that is
  precisely `he_ex`'s horizontal disjunct, for all five values.
- **`mtkNodes_length_le`** bounds the closure by `mtkBound C0 k`, which is what
  the `codes` pipeline consumes.

So `he_ex` and finiteness both come from machinery that exists. The one design
point is the FRAME's hypothesis:

> `readoff_qnet_frame` needs the representatives to be DISTINCT (`hinj`), and
> `mtkNodes` may visit the SAME model element at several budgets.

The horizontal fragment never hit this because its frame is PO-default
(declared, via `dadjBK`), so it dedups on the PAIR `(x, k)` (`hfExt = cdedup …`)
and never needs injectivity on `x`.

**The fix, and why it is safe.** Deduplicate the external list by MODEL ELEMENT,
keeping the LARGEST budget at which the element was visited. Then:
- `g` is injective, so `hinj` holds and `readoff_qnet_frame` applies;
- a witness found at a smaller budget still lies in the larger label
  (`mtk_mono`, certified);
- coverage is taken at the max-budget occurrence, and `mtkNodes` did recurse on
  every demand present there — so no demand of the enlarged label is missed.

`mtk_mono` / `mtk_covers_at_max` are the certified enabling facts. What remains
is the dedup-by-element construction itself and its coverage transfer — ordinary
list engineering over certified parts, with the `hfExt`/`cdedup` pattern as the
template.

### 42.6 Reading, not probing: the two remaining risks located

Asked whether to research or probe before building the rest. Neither: the
remaining risks are about what the existing code SUPPORTS, not about
mathematical facts, so a Python probe cannot touch them — §42.4's lesson says
read the definitions. Doing so located both precisely.

**Risk 1 — `hinj` across `β ⊕ κ`.** `readoff_qnet_frame` needs the
representatives of externals AND kernel bases to be pairwise distinct. Dedup by
model element handles the externals; a kernel base could still coincide with an
external. **Discharged**: the externals form a FINITE list (the bounded closure)
while an ascending chain has pairwise distinct nodes
(`chain_model_distinct`), so all but finitely many indices avoid the list, and
`rr_segment_from` supplies a base past any threshold.
`exists_index_avoiding` (certified) is the general form: for a pairwise-distinct
sequence and any finite list, some index past any bound misses the list. Proof by
the pigeonhole already in the file (`nodup_len_le`).

**Risk 2 — the code enumeration.** `FinMT` already carries `K`, `Q`, `up`,
`phases`, so kernels are representable. But neither existing enumeration is the
general one:
- `codes` (horizontal) sets `K`/`Q`/`up`/`phases` to `[]` — externals only,
  though sized by `mtkBound C0 (mdepth C0)`;
- `codesV` carries both externals and kernels but is sized to **one** of each
  (`allListsLe labels 1`, `atomTab1`, `boolCol`).

So `codesM` is the same `allListsLe` pattern at the general bounds —
`mtkBound`-many externals, `K(C₀)`-many kernels — with two working templates and
the membership proofs (`encodeHF_mem_codes`, `unitTower_mem_codesV`) to mirror.
Mechanical, but not free.

**Net.** No mathematical unknown remains on the restored route; what is left is
the dedup construction, `codesM` at general bounds, and the assembly. Both risks
turned out to be answerable by reading — which is the third time today that
reading beat reasoning.

### 42.7 The max-budget external list — built

The dedup construction §42.5 called for, now certified:

- **`maxBudgetAt`** / **`extMax`** — the external list keeps, for each model
  element, the occurrence of LARGEST budget (`cdedup` of the filtered closure).
  Nodes are determined by `(x, k)`: `Interp.dom` is a `Prop`, so `MTKNode`'s
  `hx` field is proof-irrelevant.
- **`extMax_covers_elt`** — every visited element HAS a max-budget
  representative. The budgets for a fixed `x` form a finite list, so one is
  largest; the proof is a classical selection with `list_bound` supplying the
  contradiction if no maximum existed (an unbounded strictly increasing chain of
  budgets inside a finite list).
- **`extMax_inj`** — the representatives are DISTINCT: two max-budget nodes with
  the same element bound each other's budgets, hence are equal. This is exactly
  `readoff_qnet_frame`'s `hinj`.
- **`extMax_covers`** — coverage transfers: `mtkNodes_covers` supplies the
  witness, `mtk_mono` lifts its argument to the representative's larger budget.

So the read-off certificate now has, all certified: a general frame
(`readoff_qnet_frame` + `extMax_inj`), coverage at truncated labels
(`extMax_covers`), finiteness (`mtkNodes_length_le`, and `extMax` is a sublist of
`mtkNodes`), and a base disjoint from the externals (`exists_index_avoiding`).

**Remaining:** `codesM` at general bounds (template: `codes` + `codesV`), the
encoder and its membership lemma (template: `encodeHF_mem_codes`), and the final
assembly into `decidableSat_of_codes`.

### 42.8 `codesM` — the code enumeration at general bounds

`codes` enumerates externals only (kernel fields `[]`); `codesV` carries kernels
but is sized to ONE external and ONE kernel. The general certificate needs both
at once. **`codesM C0 NE NK P`** is the same `allListsLe` pattern at general
bounds — at most `NE` externals, `NK` kernels, periods `≤ P`, every label a
sublist of `cl C0` — with helpers `atomTabN` (square atom tables) and
`atomTabNM` (the rectangular `K` block).

**`mem_codesM`** discharges membership from the block bounds alone, mirroring
`encodeHF_mem_codes` / `unitTower_mem_codesV`. It is model-independent, so it
can be proved once and applied to whatever certificate the extraction produces.

Note `codesM` itself needs only `propext` — it is pure finite syntax.

**What remains — CORRECTED after reading (§42.9).** Items 1–2 of the list I
first wrote here are ALREADY DONE and GENERAL:

- `encodeMT : MultiTier (Fin nE) (Fin nK) → FinMT` — the general encoder;
- `encodeMT_mtOk` — validity transports across the encode
  (`mtOkB_complete` is itself fully general: any `FinMT` whose decode is valid is
  accepted);
- `encodeMT_accepts` — the checker accepts at a root index carrying `C0`.

So the encoder is not to be written. What was genuinely missing is the BRIDGE to
the enumeration, now built:

> **`encodeMT_mem_codesM`** — `encodeMT T` lies in `codesM C0 NE NK P` given
> `nE ≤ NE`, `nK ≤ NK`, periods `≤ P`, and labels/phase-types drawn from
> `cl C0`. Every block of `encodeMT` is a `finRange`-map, so its length is
> exactly the index count; the only real hypotheses are the label ones.

**Genuinely remaining:**
1. REINDEX the extraction's certificate onto `Fin nE` / `Fin nK` (there is a
   reindexing section in the file already);
2. supply the bounds — `NE` from `mtkNodes_length_le` (`extMax` is a sublist of
   `mtkNodes`), `NK` and `P` from the kernel side;
3. `hcompl` + `decidableSat_of_codes`, mirroring `hfrag_hcompl` (11 lines).

*(This was the FOURTH time this session that a piece I was about to build already
existed — but the first time I checked before building rather than after. The
habit is the mitigation; the inventory alone was not enough, because these are
questions about what a definition CONTAINS.)*

### 42.4 The pattern, recorded

This is the **third** time in one session that a conclusion rested on not
checking what already existed:

1. §40 — treated the two certificate architectures as needing comparison from
   scratch;
2. §41.8 — labelled step 5 open research when its pipeline was certified twice;
3. §42 — pivoted the whole route without checking the read-off frame's
   expressiveness.

Each was caught, but only after work. `CERTIFIED_INVENTORY.md` and the
route banner are the mitigation; the discipline is to **read the definition
before reasoning about what a component can express** — in all three cases the
answer was one `sed` away.

The `odNet` work is not wasted (it is a real theorem, and `wp93`–`wp95` are
genuine evidence about the fragment's structure), but it should be recorded as
what it is: a correct answer to a question the route did not need to ask.

## 43. THE BUDGET/FRAME TENSION, AND THE HYBRID THAT RESOLVES IT (2026-08-21)

**Probes: `verification/python/wp96_budget_frame_tension.py`,
`wp97_hybrid_frame_feasibility.py` (all parts PASS).** Written before
formalizing anything, per the standing directive. They found a defect in §42's
restored route that neither §41 nor §42 examined, and they fix the architecture.

### 43.1 The finding: read-off relations break the budgets

`mixKernelsK_ok` carries four budget side-conditions, the external one being
`hbEE : ∀ e f, bud e ≤ bud f + 1`. It is not an artefact of a strong hypothesis;
it is exactly what the obligation needs. With `mtk` labels,

```
tauE e = { c ∈ cl C0 : model-sat at g e, mdepth c ≤ bud e }
```

so in `ee_all` the SEMANTIC half is free — the model satisfies the universal —
and only the DEPTH half can fail:

> `ee_all` holds iff `mdepth cc ≤ bud f` whenever `all r cc ∈ tauE e`
> and `E e f = r`; and `all r cc ∈ tauE e` already gives `mdepth cc + 1 ≤ bud e`.

The node set that supplies finiteness is `mtkNodes`, whose `mtkWitness` has
budget `n.k - 1`. Budgets therefore span the whole range `N..0`. With **read-off**
relations every external pair carries a real relation, so `ee_all` fires across
those gaps. `wp96` A: **4.1%** of satisfiable ∀PO-free instances (mdepth ≥ 2)
have at least one violation; largest budget gap on a violating edge: 3.

The escape "use a uniform budget" is real but costly: at uniform budget the node
set must be closed under ALL demands at that budget, which is the infinite
unfolding — precisely the finiteness the `codes` pipeline was buying.

`wp96` D measured the other uniform-budget escape, type-blocking (one
representative per realized model type — finite in `C₀`, at most `2^|cl C₀|`):
representative sets are small (mean 1.4, max 5), but **8.4%** of instances have a
demand no read-off edge between representatives can serve. That is W2′
uniformization reappearing, and it is why the frame cannot be read off.

### 43.2 Why a declared frame fixes it, and why it cannot be a PO default

`wp96` B: over the SAME node sets, a declared PO-default frame has **0**
violations. The reason is structural, not statistical — the declared non-`PO`
edges are exactly the closure-tree edges, where the budget drops by exactly one,
and `PO` edges carry no obligation at all in the fragment (`pofree_cl_all`).
This is why the horizontal fragment's budgets worked out, and it was never
recorded as the reason.

But the declared frame cannot be a PO DEFAULT once kernels are present. `wp96`
C / `wp97` B, C: an external carrying both an `∃PP` and an `∃PPI` demand needs a
kernel above and a kernel below; `comp(PP,PP) = {PP}` forces the two bases
`PP`-comparable, and `PO` is not admissible there. Independently, kernels under
`DR`-separated externals inherit disjointness by `djDown`, and forcing `PO`
between them is both non-ordered-disjoint and composition-violating.

**So the frame must be an order-plus-disjointness structure.** `odNet_frame` is
on the critical path after all; §42.2's "not on the critical path" was wrong.

### 43.3 The hybrid, and what is now certified

`wp97` A: exhaustively, every configuration with ≤ 3 externals and ≤ 2 kernels
admits an ordered-disjoint completion (382/382); `wp97` D: every completion
realizes the attachment edges with the exact labels the demands need, and
preserves the externals' `DR` pattern.

Built and certified (0 sorries, 0 warnings):

- **`mtkKernelsOD` / `mtkKernelsOD_ok`** — the hybrid certificate. `frame_q` is
  FREE (`frame_q_of_odNet`); the kernel-internal obligations are the certified
  `mtk_kk_*_dir`; and the three propagation classes reduce to ONE uniform
  model-side debt:

  > wherever the DECLARED frame says something other than `PO`, the model
  > agrees, and the two budgets are within one.

  `PO` edges carry no obligation — the fragment's escape valve — which is what
  lets the declared frame be coarse everywhere except on the finitely many edges
  the demands actually use.

- **`odMix`** — the CANONICAL ordered-disjoint completion, so the extraction
  never searches. Externals pairwise incomparable; each kernel entirely on one
  `side` of its externals; order of HEIGHT TWO (down-kernel < external <
  up-kernel), so transitivity has one non-vacuous case and down-kernels are
  minima (`mixLt_no_below`), which terminates `djDown`'s analysis; disjointness
  the downward closure of `dadj`. Depends on **no axioms**.

  One coherence condition, and it is forced: a down-kernel's externals are
  pairwise non-disjoint (`hcoh`). A region below two disjoint regions would be
  empty; formally `djIrr` fails without it.

- **read-off**: `odMix_E` (the external block IS the PO-default frame, so
  `mtk_ee_all` / `mtk_e_ex` apply verbatim), `odMix_K_up`, `odMix_K_dn` (the
  `∃PPI`-at-an-external demand the PO-default frame could not express),
  `odMix_Q_forced`, `odMix_Q_dr` (the two edges that made the ordered-disjoint
  frame necessary, now discharged).

### 43.4 What this changes about the remaining work

The four-item list is unchanged in shape; item A is now much better supported.

1. **The extraction assembly.** Externals from `mtkNodesH` (budget-decreasing,
   horizontal-only recursion — vertical demands are the kernels' job), `dadj`
   from `sAdjK`, kernels from the persistent demands with `side` = their
   direction, `att` from the attachment, and `odMix` for the frame. The debts
   are then `hEreal`/`hKreal`/`hQreal` — the §39 apparatus (`exists_bank`,
   `exists_bank_ppi`, `mixSelect_of_highBank`, `family_range`) is exactly what
   supplies them, and `hcoh` is a condition on which externals share a kernel.
2. reindex onto `Fin nE`/`Fin nK`;
3. bounds for `encodeMT_mem_codesM`;
4. `hcompl` + `decidableSat_of_codes`.

### 43.5 The method note

§42.4 recorded "read the definition before reasoning about what a component can
express". That was the right lesson and it was applied here — but it was not
sufficient. §42 read `mixKernels`'s definition correctly and concluded correctly
that it expresses all five relations; what it did not do was check whether the
certificate could be INSTANTIATED at a node set that is finite. Expressiveness
and usability are different questions, and only the probe separated them.

The sharpened rule: **read the definition, then ask what it costs to satisfy —
and if that is a quantitative question, measure it.** `wp96` cost twenty minutes
and would have saved several sessions of building on a 4.1%-broken interface.

### 43.6 The frame, generalized: disjointness as a downward closure

Building the debt lemmas exposed a real limitation in the first version
(`odMix`): it inherited disjointness only DOWNWARD from the externals' `DR`
pattern, so it could not make an UP-kernel `DR` from an external. An ascending
tower whose rungs each carry an `∃DR` demand — an ordinary ∀PO-free concept —
forces exactly that: the kernel needs `side = true` to serve an external's
`∃PP`, and `side = false` to have a `DR`-external. Contradiction, so `odMix` was
too weak.

The fix generalizes AND simplifies. Take disjointness to be the downward closure
of an arbitrary symmetric seed:

```
disj x y  :=  ∃ x₀ y₀, x ≤ x₀ ∧ y ≤ y₀ ∧ seed x₀ y₀
```

Closing downward *by construction* means `djDown` is just transitivity of `≤`,
and `djIrr` and `ltNotDj` BOTH collapse into one condition —

> **`hsep`: no node lies below two seed-related nodes.**

(For `ltNotDj`: if `x < y` then `x` is below both `x₀ ≥ x` and `y₀ ≥ y`, so it is
an instance of the same condition.) Four `ODStruct` obligations for the price of
one, the seed is unconstrained, and every `wp97`-style completion is
expressible. `odSeed` depends on **no axioms**.

The debt lemmas are correspondingly stated for ANY `ODStruct` whose `lt` is
`mixLt`, with `disj` left ABSTRACT — so `hdrk` and `hqdr` are conditions on
`O.disj` and cover up-kernels. `odMix` and its read-off lemmas were removed
rather than kept as a weaker special case: net −74 lines.

**Method note.** This is the second time in two days that building the next
layer falsified the layer below (first `mixKernelsK`'s budgets, now `odMix`'s
disjointness). Both were found by *use*, not by review — which is an argument
for building the consumer early rather than perfecting the producer.

### 43.7 State after §43

| | piece | status |
|---|---|---|
| frame | `odSeed` + `frame_q_of_odNet` | **certified**, axiom-free |
| certificate | `mtkKernelsOD` / `_ok` | **certified** |
| debts → model conditions | `odLt_hEreal` / `_hKreal` / `_hQreal` | **certified** |
| external debt, discharged | `sAdjK_bud`, `sAdjK_irr`, `dadjOD_*` | **certified** |
| kernel debts | `hup`, `hdn`, `hdrk`, `hqpp`, `hqppi`, `hqdr` | the banks — NEXT |
| seed separation | `hsep` | with the banks |
| assembly | choose β, κ, `side`, `att`, `seed`; apply | after the banks |
| reindex / bounds / `hcompl` | small, templated | after the assembly |

### 43.8 The assembly interface, and the third catch

`mtkKernelsOD_of_debts` is the CONSUMER: a `MultiTierOk` from the model-side
conditions alone. Built before its inputs on purpose — §43.6's method note says
the layer below gets falsified by use, not by review, so pin the interface down
first.

It paid immediately, and in the same defect class as the first two. `hKreal` and
`hQreal` quantified over **all** `a`, while the banks deliver only a **window**
(`exists_bank`: `∀ b ≤ M`). That is `hstab` again — an interface demanding more
than the supplier can produce. Both are now bounded by the phase window, at zero
cost: `ek_all`/`ke_all`/`kq_all` all had `a < pk k` in scope and were discarding
it.

**Three for three.** `mixKernelsK`'s budgets, `odMix`'s disjointness, and now
`hKreal`'s range — each an over-strong interface, each invisible until something
tried to satisfy it. The generalizable rule is not "check the definition" (§42.4)
nor even "measure what it costs" (§43.5) but:

> **Write the consumer against the interface before believing the interface.**
> An obligation stated for a quantifier range wider than any supplier's is
> indistinguishable from a correct one until you try to supply it.

### 43.9 The bank seam

`exists_bank` gives `∀ b ≤ M, I.rho (c b) w = r` (LATE picking: witness above
the range, backward forcing down through the window). `exists_bank_ppi` gives
`∀ b ≥ A, I.rho (c b) w = ppi` (EARLY picking, uniform anchor, forward
absorption). `odLt_hKreal` wants the other orientation on the window only.
`bank_window` / `bank_window_ge` are that seam, and with `conv pp = ppi`,
`conv ppi = pp`, `conv dr = dr` definitional the three cases specialize free:

| debt | bank | why |
|---|---|---|
| `hup` | `exists_bank_ppi` | `conv ppi = pp` — the external is a proper part of every phase |
| `hdn` | `exists_bank`, `PP` branch | `conv pp = ppi` |
| `hdrk` | `exists_bank`, `DR` branch | `conv dr = dr` |

Both seam lemmas are `Classical.choice`-free.

### 43.10 Two structural facts the assembly will use

**`side = dir`.** An ASCENDING kernel discharges `∃PP` rung-to-rung, so its
`∃PPI` demands need an external `f` with `K k f = ppi`, i.e. `side k = true`;
and an external whose `∃PP` it serves needs `conv (K k e) = pp`, i.e.
`K k e = ppi`, i.e. `side k = true` again. Dually for descending. So the
attachment side is not a free choice — it is the kernel's own direction.

**Private banks.** `hsep` (no node below two seed-related nodes) becomes a
handful of coherence conditions on `att`/`seed`. Giving each kernel its OWN bank
externals — rather than sharing one pool — kills the cross-kernel cases: a bank
member of `k` is attached only to `k` and seeded only with `k`. The remaining
condition is the old `hcoh`: no down-kernel attached to two `DR`-adjacent
externals (a region below two disjoint regions would be empty).

**Budgets are free for bank externals.** They are NEW nodes, so set
`bud w := bk k`; then `hup`/`hdn`/`hdrk`'s budget conjuncts are trivial. And
bank-to-skeleton external pairs need no `DR` declaration at all — left `PO`,
they carry no obligation, which is exactly what the declared frame is for.

### 43.11 Restriction audit (asked for explicitly, 2026-08-21)

Michael asked to be told when a restriction is being introduced that could
become a roadblock. This is that audit, run against everything §43 has built.

**Not restrictions — checked, and each is forced or free.**

| choice | verdict |
|---|---|
| `side = dir` | FORCED, not a choice. An ascending kernel discharges `∃PP` rung-to-rung, so both its own `∃PPI` demands and any external whose `∃PP` it serves require `side = true`; dually for descending. A kernel that would need both sides is simply two kernels. |
| private bank externals per kernel | multiplies the external COUNT; does not restrict what is expressible. Buys away `hsep`'s cross-kernel cases. |
| bank externals at `bud w := bk k - 1` | needed for termination of the horizontal recursion, and the budget conjuncts `bud w ≤ bk k + 1 ∧ bk k ≤ bud w + 1` still hold. Free. |
| bank↔skeleton pairs left `PO` | carries no obligation (no `∀PO`). This is what a DECLARED frame is for; it is the mechanism, not a compromise. |

**The one large risk, now RESOLVED.** §36 showed `hrectQ` is false in general —
the cross-kernel staircase — and that was the likeliest blocker on this route.
It does not bite: `kq_all` is vacuous on `PO`, so a cross-kernel debt exists only
for pairs the frame declares non-`PO`, and `odSeed` declares that only for
kernels sharing an anchoring external (or seed-disjoint). For those the phase
relation is composition-forced (`cross_pp_of_shared`, `cross_ppi_of_shared`,
`cross_dr_of_shared` — all axiom-free). §36's staircase concerns ARBITRARY
kernel pairs, which this architecture never declares non-`PO`.

**Genuinely open, flagged now rather than on contact.**

1. **The kernel COUNT — this fragment's descendant of F6.** Externals are
   bounded (`mtkNodes_length_le`). Kernels are not yet. The budget-decreasing
   recursion (skeleton external at budget `b` ⟹ its kernels at `b`, their bank
   externals at `b-1`, their kernels at `b-1`, …) *suggests* a `mtkBound`-style
   bound, but this is NOT proved and it is the item most likely to be hard.
2. **`hup`/`hdn` for SKELETON externals is not a bank.** The banks serve KERNEL
   demands with externals. A skeleton external's `∃PP.D` needs a kernel ABOVE it
   whose phases carry `D` — that is the tower construction
   (`towers_from_persistPP` + the §38 merge), and its budget must land within one
   of `bud e`. Arrangeable in principle; not yet done.
3. **Coverage** (`he_ex`/`hk_ex`) is still entirely to be wired, though
   `mtkNodesH_covers` and the banks are the two halves.

Items 2–3 are construction work. Item 1 is the real unknown, and it is the same
counting problem the campaign has always had — now localized to the kernels
alone, which is progress over F6 in the full logic but not a solution.

## 44. ROADBLOCK FLAGGED: one-shot `∃PP` (2026-08-21)

Michael asked to be told when a restriction risks becoming a roadblock. **This is
one, and it is load-bearing.** Probe: `wp98`.

### 44.1 The finding

`odSeed`'s order `mixLt` makes externals pairwise `lt`-INCOMPARABLE, so
`E e f` is never `PP`. An `∃PP.D` at an external must therefore go to a KERNEL —
and a kernel needs an infinite `PP`-chain reproducing the demand.

`wp98` A: **88.8%** of `∃PP` demands with a witness are ONE-SHOT (the witness
starts no such chain), present in 12.2% of satisfiable ∀PO-free instances. This
is the common case, not a corner. `C0 = ∃PP.A ⊓ ∀PP.(A ⊓ ¬∃PP.⊤)` is satisfiable,
∀PO-free, and has no infinite `PP`-chain at all.

This is §33's finding, unresolved since 2026-08-14, and `odSeed` inherits it.
§43's work is not wasted — the frame, the certificate, the debt reduction and the
composition-forcing all stand — but the frame's ORDER is too flat.

### 44.2 Why explicit `PP` edges collide with the budgets

An ordered-disjoint frame FORCES transitive edges. With `e1 PP e2 PP e3` at
budgets `N, N-1, N-2`, the forced `e1 PP e3` has `ee_all` demanding
`bud e1 ≤ bud e3 + 1`, i.e. `N ≤ N-1`. `wp98` D constructs the witness:

```
C0 = ∀PP.(∃DR.∃DR.A) ⊓ ∃PP.∃PP.B      over  e1 ⊂ e2 ⊂ e3
```

the forced edge `e1 PP e3` carries a `∀PP` whose argument has depth 2 while a
decreasing budget leaves `e3` at 1. **1 violation decreasing, 0 uniform.**

### 44.3 The repair, and its one new ingredient

Keep the budget CONSTANT along `PP`-paths; drop it only on `DR`/`PO`/`EQ` steps.
Then every forced transitive edge has equal budgets and `ee_all` is satisfied.

Two things must then be supplied:

1. **The external order.** Read it OFF THE MODEL (`elt e f := I.rho (g e) (g f) = pp`)
   rather than declaring it — transitivity is then `comp(PP,PP) = {PP}` for free,
   and irreflexivity is `refl_eq`. Only `disj` stays declared (the seed closure),
   so the read-off budget problem of `wp96` A does NOT return: it was caused by
   read-off on ALL pairs, and here only the vertical block is read off.
2. **Termination.** The budget no longer decreases along `PP`, so the measure
   becomes lexicographic `(budget, remaining PP-path length)`. The path length is
   bounded by the DICHOTOMY the campaign already owns:

   > a `PP`-chain of demands either repeats a type — and a repetition gives a
   > periodic tower, hence a KERNEL (`recurrent_tail`, `rr_segment_from`,
   > certified) — or it does not, and is then shorter than the number of types.

   So: cut every `PP`-path at its first type repetition. Below the cut it is a
   finite explicit path at uniform budget; at the cut it becomes a kernel. This
   is the one-shot/persistent dichotomy made structural, and it also bounds the
   node count, which is §43.11 item 1.

### 44.4 Honest status

This is a genuine architectural change to the frame, not wiring: `mixLt` gains an
external order, transitivity and `hsep` need re-proving over a taller order, and
the dichotomy above needs to become a Lean construction. The ingredients
(`recurrent_tail`, `rr_segment_from`, `comp(PP,PP) = {PP}`, `odSeed`'s
seed-closure trick) are all certified; the assembly is not.

Estimated: comparable to §43's frame work, i.e. a substantial piece rather than a
session's wiring. Flagged BEFORE building on the flat order, which is the point.

### 44.5 The repair, built (2026-08-21)

§44.3's first ingredient is done and the whole stack follows it.

**`mixLt` now carries an external order `elt`.** Each kernel is entirely above
(`side = true`) or below (`side = false`) its attached externals and, by
transitivity, everything `elt`-comparable to them. Up-kernels stay maximal and
down-kernels minimal, so four of the eight transitivity cases remain vacuous by a
`side` clash and the rest are `elt` transitivity pushed through `leE`.
`mixLt_no_below` survives unchanged, which is what keeps `djDown` terminating,
and `odSeed` is unchanged in structure — still **no axioms**.

**`odSeed_E_pp` is the fix**: an `elt` edge IS a `PP` edge of the frame, so a
one-shot `∃PP` is served with no kernel at all.

**The order is read off the model**, which makes `odSeed`'s two order hypotheses
free — `eltOf_irr` is `refl_eq`, `eltOf_trans` is `comp(PP,PP) = {PP}` (axiom-free)
— and collapses the external debt: `hppE_of_bud` shows the relation half is
DEFINITIONAL, leaving only the budget condition.

**`wp96` A does not return.** That defect came from reading off ALL pairs, so
`ee_all` fired on every one. Here only the VERTICAL block is read off; `disj`
stays declared (the seed closure) and everything else is `PO`, carrying no
obligation. The two are not the same move.

Downstream, mechanically: `odLt_E_cases` (an off-diagonal non-`PO` external pair
is `PP`, `PPI` or `DR`), `odLt_hEreal`, `odLt_hKreal`, `odLt_hQreal` — `hup`,
`hdn`, `hqpp`, `hqppi` now stated with `leE`, since attachment reaches further —
and `mtkKernelsOD_of_debts`.

### 44.6 What §44 still owes

1. **The budget assignment.** `hppE`'s residue: `bud` constant along `elt`. Needs
   the assignment itself, plus `hb` for the `DR` block (`dadjOD_bud` already, but
   over the new node set).
2. **The cut.** The dichotomy — a `PP`-chain of demands either repeats a type
   (⟹ kernel, via `recurrent_tail`/`rr_segment_from`) or is shorter than the
   number of types — as a Lean construction. This bounds the path length, hence
   the lexicographic measure, hence the node count (§43.11 item 1).
3. **`hsep`** over the taller order: more cases, since externals can now lie below
   externals.
4. Coverage (`he_ex`/`hk_ex`), then reindex / bounds / `hcompl`.

Item 2 is the substantial one and is now the campaign's single open mathematical
step for this fragment.

### 44.7 THE CUT — §44.6 item 2 was wrong, and the correction (2026-08-21)

§44.6 stated the dichotomy as *a `PP`-chain either repeats a type — and a
repetition gives a periodic tower, hence a KERNEL — or is shorter than the number
of types*, and rested the node bound on it. **`wp99` refutes the bound.** Type
repeats DO occur on terminating paths (35 across 5,773 instances), and paths DO
exceed the type count and `|cl C₀|`. A repeat does not by itself produce an
infinite ascending chain, so it produces no kernel. The claim conflated two
different things.

**The correction.** A repeat on a FINITE path gives a **CUT**:

```
mty v = mty w,   u PP v PP w    ⟹    delete v, keep w
```

legitimate for exactly two reasons, both machine-checked (`wp99` E, 35/35) and
now certified (`path_cut`, `path_cut_mtk`):

* the re-linked edge survives — model `PP` is TRANSITIVE, `comp(PP,PP) = {PP}`;
* the deleted node's serving role is inherited — the survivor has the SAME TYPE,
  so it carries the same demand argument.

So the honest dichotomy is:

> a demand path either **TERMINATES** — and can then be CHOSEN repeat-free, which
> bounds its length by the number of types — or is **INFINITE**, and *that* is
> what yields a kernel (pigeonhole + `recurrent_tail`).

The kernel comes from the infinite branch, not from the repeat.

**Method note, and it is the same one again.** §44.6 was written from reasoning,
not measurement, and it was wrong in a way that would have been invisible until
the node-bound proof failed. Four for four now: `mixKernelsK`'s budgets, `odMix`'s
disjointness, `hKreal`'s range, and this. Every one was an over-strong or
over-hopeful claim about an interface or a bound, and every one fell to the first
thing that actually tried to use it.

### 44.8 `hsep` is free, and `elt` must stay abstract (2026-08-21)

**Item 3 is done and costs nothing.** `odSeed`'s only real hypothesis is `hsep`
— no node lies below two seed-related nodes — and over the taller order that
looked like more work. It is instead automatic, because the model supplies the
reason: *a node below two `DR`-related nodes would be a part of both, hence
empty*. Formally it needs one bridge and two composition facts:

* **`mixLt_rho`** — the declared order is SOUND for the model's `PP`. The
  external part is the hypothesis `helt`; the kernel parts are the attachment
  facts pushed through `comp(PP,PP) = {PP}`.
* **`hsep_of_model`** — then `comp(PP,DR) = {DR}` and `PP ≠ DR` close it.

Both **axiom-free**.

**`elt` must stay ABSTRACT — a restriction avoided.** The obvious move is
`elt := eltOf` (the model's own `PP` on the chosen externals). That would bake in
a real restriction: it declares a `PP` edge between EVERY model-`PP`-related pair
of externals, and two externals reached by different routes can have budgets far
apart, so `ee_all`'s `bud e ≤ bud f + 1` fails — for instance a node at budget `N`
and one at `N-3`.

With `elt` abstract (any sub-relation of the model's `PP`), the extraction takes
just the TRANSITIVE CLOSURE OF ITS OWN `PP`-demand steps. Budgets are constant
along that by construction (§44.3), and soundness survives because the closure
stays inside the model's `PP` — closure of model-`PP` edges is model-`PP` by
`comp(PP,PP) = {PP}`. `eltOf_sub` records that `eltOf` is the maximal choice.

This also collapses §44.6 item 1: `bud` constant along `elt` is now true by
construction rather than something to arrange.

### 44.9 §44 state

| item | status |
|---|---|
| the external order, one-shot `∃PP` served | **done** (§44.5) |
| the cut | **done** (§44.7, corrected) |
| `hsep` over the taller order | **done, free** (§44.8) |
| `bud` constant along `elt` | by construction, once `elt` is the demand-step closure |
| coverage `he_ex`/`hk_ex` | open — `mtkNodesH_covers` + the banks |
| reindex / bounds / `hcompl` | open, small, templated |

The open mathematical content is now concentrated in coverage plus the node
count, and the cut is the tool for the latter.

### 44.10 Coverage, restated in extraction terms (2026-08-21)

`he_ex`/`hk_ex` are stated on `odNet` VALUES, which the extraction does not think
in. Two routing lemmas now do the case analysis on the demanded relation once and
restate each branch in terms of the extraction's own data — `seed`, `elt`,
`side`, `att` — so what is left to supply is a WITNESS LIST, not a frame fact.

**`odSeed_he_ex`** (externals):

| `r` | served by |
|---|---|
| `EQ` | the node itself (`odNet_self` + `mtk_ex_eq`) |
| `DR` | a seed-related external (`odSeed_dr`) |
| `PO` | an external the frame leaves alone (`odNet_po`) |
| `PP` | an `elt`-successor — **the one-shot case, §44's whole point** — or an UP-kernel |
| `PPI` | an `elt`-predecessor or a DOWN-kernel |

**`odSeed_hk_ex`** (kernel phases) is routed by §43.10's structural fact
`side = dir`: an ASCENDING kernel discharges `∃PP` rung-to-rung and needs an
external only for `∃PPI`, which wants `side = true`; a DESCENDING one is the
mirror. So the vertical-to-external branches land exactly where the attachment
already puts them, and no case analysis on `side` beyond `dir` is needed.

**The cross-kernel branch of `hk_ex` is never used.** That is what keeps §36's
`hrectQ` staircase out of the picture, and it is now visible in the proof rather
than argued in prose (§43.11).

### 44.11 §44 state, updated

| item | status |
|---|---|
| external order, one-shot `∃PP` | **done** |
| the cut | **done** (corrected) |
| `hsep` | **done, free** |
| `bud` constant along `elt` | by construction |
| coverage `he_ex`/`hk_ex` | **done as routing**; the witness lists remain |
| reindex / bounds / `hcompl` | open, small, templated |

What remains for `Decidable (Satisfiable C₀)` on this fragment:

1. **The witness lists** — instantiate `rDR`/`rPO`/`rPP`/`rPPI` and
   `kDIR`/`kDR`/`kPO`/`kUP`/`kDN` from `mtkNodesH_covers`, the banks and
   `rr_covers`. Construction, with every ingredient certified.
2. **The node bound** — `|β|` and `|κ|` in terms of `C₀`, using the cut for the
   `PP`-path length. This is the one with real content left.
3. Reindex onto `Fin nE`/`Fin nK`, feed `encodeMT_mem_codesM`, then `hcompl` +
   `decidableSat_of_codes`.

### 44.12 The `PP`-path closure and its bound (2026-08-21)

§44.3 holds the budget constant along a `PP`-path, so the horizontal recursion's
budget can no longer measure it. The measure is lexicographic
`(budget, remaining path length)`; this is the inner component, built:

* **`ppWitness`** — a `PP`-demand's witness at the SAME budget. Legitimate
  because `mtk_ex` delivers the argument at `k-1` while the demand `∃PP.c` has
  `mdepth c + 1 ≤ k`, so `c` fits at every budget from `k-1` up.
* **`ppNodes`** — the `PP`-path closure, bounded by FUEL rather than budget.
* **`ppNodes_bud`** — every node of the closure keeps the SAME budget. This was a
  convention in §44.3 and is now a theorem, and it is precisely what `ee_all`
  needs on the forced transitive edges.
* **`ppNodes_length_le`** — bounded by `mtkBound C0 fuel`, the SAME bound the
  horizontal closure uses, with fuel in place of budget.

The fuel is what the cut supplies: a path can be chosen repeat-free, so the
number of distinct model types is enough.

**What the node bound still needs.** `ppNodes` bounds ONE path closure given
fuel. The outer recursion — horizontal steps dropping the budget, each of whose
nodes carries a `ppNodes` closure — has to be assembled and bounded in turn, and
the fuel has to be instantiated from the cut (i.e. the number of types realized
by `C₀`, which is at most `2^|cl C₀|`). Neither is written yet; both are now
pattern-matched to certified code (`mtkNodes_length_le` for the outer shape,
`path_cut` for the fuel).

### 44.13 The node bound, and exactly what it does not yet give (2026-08-22)

Built:

| | |
|---|---|
| `mixBound` / `mixNodes` | the full node set: `ppNodes` closures (constant budget, fuel-measured) nested inside horizontal steps (budget-dropping) |
| `mixNodes_length_le` | bounded by `mixBound C₀ fuel b`, computable from `C₀`, fuel and horizontal depth alone |
| `typeEnum` / `mty_mem_typeEnum` | the enumeration of possible model types — every `mty` is a filter of `cl C₀` |
| `repeatfree_len_le` | **the pigeonhole**: pairwise-distinct types ⟹ no longer than the enumeration |
| `mixKT` | `K(C₀)` for the mixed fragment, fuel pinned by the pigeonhole |

The horizontal depth is carried as its own recursion parameter rather than read
off `n.k`, because a `ppNodes` member's budget equals `n.k` only by the THEOREM
`ppNodes_bud`, which the equation compiler cannot see.

**What this does NOT give, stated before it can be mistaken for more.**
`mixNodes_length_le` is a bound for ANY fuel. Pinning the fuel to
`|typeEnum C₀|` does not prove the fuel SUFFICES. Adequacy is a separate claim:

> `ppNodes` follows `ppWitness`, i.e. the model's arbitrary `Classical.choose`
> witness, which need not give a repeat-free path. The CUT is what makes the
> choice repeat-free.

`path_cut` (the cut is legitimate) and `repeatfree_len_le` (repeat-free paths
are short) are both certified. **Joining them to the construction — a witness
selection that avoids already-seen types — is what remains**, and it is the last
piece with real content.

### 44.14 Remaining, in order

1. **Adequacy** — a repeat-avoiding `ppWitness`, so that `|typeEnum C₀|` fuel
   suffices. Ingredients certified (`path_cut`, `repeatfree_len_le`); the
   construction is not written.
2. **Witness lists** — instantiate `rDR`/`rPO`/`rPP`/`rPPI` and
   `kDIR`/`kDR`/`kPO`/`kUP`/`kDN` from `mtkNodesH_covers`, the banks, `rr_covers`.
3. **Reindex** onto `Fin nE`/`Fin nK`, feed `encodeMT_mem_codesM` with `mixKT`,
   then `hcompl` + `decidableSat_of_codes`.

3 is templated. 2 is construction over certified parts. 1 is the one to watch.

### 44.15 Adequacy: the three ingredients are in place (2026-08-22)

The `β` closure adds, for each node and each `∃PP` demand, one model witness;
the witnesses form a CHAIN, and its length is what the fuel must cover. Adequacy
= that chain can be kept inside `|typeEnum C₀|`. Three ingredients, all now
certified:

| | |
|---|---|
| `chain_long_has_dup` | a chain past `\|typeEnum C₀\|` nodes HAS a repeated type — pigeonhole via `exists_ordered_dup_map`, in ORDERED form |
| `chain_cut` | the repeat IS droppable — a demand at `u` served by `v` is equally served by any LATER member of the same type |
| `repeatfree_len_le` | a repeat-free chain IS short |

The order in `exists_ordered_dup_map` is not cosmetic: the cut needs the survivor
to come AFTER the node it replaces, because `serveChain_rho` only reaches upward
(`comp(PP,PP) = {PP}` gives `u PP w` from `u PP v PP w`, not the converse).

**`serveChain_rho` is the lemma that makes all this work**: every chain member is
a proper part of the START, not merely of its predecessor. Without it the cut's
first obligation (`I.rho u w = pp`) would not be available. It depends on
`propext` alone.

**What remains of adequacy:** the SPLICE — rebuilding the `ServeChain` across the
dropped segment — and the well-founded descent on length that iterates it to a
repeat-free chain. Both are list plumbing over certified parts; neither is
written.

### 44.16 State

| | |
|---|---|
| frame, certificate, debts, composition-forcing | done |
| the cut, `hsep`, coverage routing | done |
| node bound `mixNodes_length_le` / `mixKT` | done |
| adequacy — ingredients | done |
| adequacy — splice + descent | **open** |
| witness lists | open |
| reindex / bounds / `hcompl` | open, templated |

### 44.17 ADEQUACY, DONE (2026-08-22)

`short_chain`: **every serving chain has a companion of length ≤ `|typeEnum C₀|`
with the SAME HEAD TYPE.** That is §44's adequacy — a demand served by the
original head is served by the new one precisely because the type is the same,
so the fuel `|typeEnum C₀|` suffices.

The pieces:

| | |
|---|---|
| `mem_split` | a member splits its list (core has no `append_of_mem` here) |
| `serveChain_suffix` | a chain restricted to a suffix is a chain from the split |
| `serveChain_cut_head` | the HEAD cut — restart at the later same-type member; `serveChain_rho` supplies the re-linked edge |
| `htype` | the head type: the invariant the cut preserves |
| `serveChain_cut` | the cut ANYWHERE, by induction on the prefix |
| `short_chain` | the descent, by induction on a length bound |

**A near-miss worth recording as process.** The first insertion of `mem_split` /
`serveChain_suffix` / `serveChain_cut_head` landed INSIDE `chain_cut`'s
docstring, silently commenting all three out. **The build stayed green** — a
split docstring is a perfectly valid comment — and only a downstream "unknown
identifier" exposed it. So:

> A clean build is not evidence that what you wrote was compiled.

Two checks now run alongside each other: `#print axioms` (catches `sorryAx`
smuggled in by a recovered error) and an explicit declared-count grep (catches
text that never became a declaration at all). Both have now caught a real
problem this session.

### 44.18 State

| | |
|---|---|
| frame, certificate, debts, composition-forcing | done |
| the cut, `hsep`, coverage routing | done |
| node bound `mixNodes_length_le` / `mixKT` | done |
| **adequacy (`short_chain`)** | **done** |
| witness lists | open — construction over certified parts |
| reindex / bounds / `hcompl` | open, templated |

The remaining two items are construction and wiring. No open mathematical step
is currently identified for this fragment — which is a claim I have made
prematurely four times this session, so it should be read as "none identified",
not "none exists".

### 44.19 Testing whether §44.18 holds water — it did not, quite (2026-08-22)

Michael asked to see whether the adequacy claim holds. It exposed a real seam,
and the seam is now closed.

**The seam.** `short_chain` gives EXISTENCE of a bounded chain. `mixNodes` is a
CONSTRUCTION using arbitrary (`Classical.choose`) witnesses. Those are not the
same thing: `ppNodes` serves every `∃PP` demand EXCEPT at its fuel-exhausted
leaves, and nothing said those leaves carry no demand. `short_chain` does not
say the GREEDY chain is short — only that a short one exists.

**The closure, and it is a dichotomy rather than a cleverer construction:**

| | |
|---|---|
| `ascend` | iterating a step that stays inside a class — the kernel branch's generator |
| `ascend_step` | the iterate IS an ascending chain; this is literally the certificate's kernel `hstep` (`cdir true = pp`). Depends on `Classical.choice` alone |
| `pp_dichotomy` | for a class closed under the `∃PP`-witness step: EITHER some member has no `∃PP` demand — the chain terminates, `short_chain` bounds it — OR the class carries an infinite ascending chain from every member, i.e. a KERNEL |

The kernel branch is not new mathematics: `recurrent_tail`, `rr_segment_from`
and `rr_covers` already turn an infinite ascending chain into a periodic kernel,
and they are certified.

**Calibration note.** §44.18 said "no open mathematical step currently
identified", explicitly hedged as *identified* rather than *existing*. The hedge
earned its keep within one round. The lesson is not "hedge more" but that the
reliable way to find these is to try to USE the result — the same rule as §43.8,
now confirmed on a claim I had already flagged as suspect.

### 44.20 The frame side is complete (2026-08-22)

`extFrame` builds the extraction's ordered-disjoint frame from model data alone,
and both it and its two read-off lemmas are **axiom-free**.

| | |
|---|---|
| `elt := tcl step` | the extraction's OWN `PP`-demand steps, closed transitively (§44.8 — NOT all of the model's `PP`, which would break the budgets) |
| `seed := drSeed` | the model's own `DR`, so `hseed` is DEFINITIONAL |
| irreflexive / transitive | `tcl_ok`, from the steps being `PP`-steps |
| `hsep` | `hsep_of_model` |
| `extFrame_lt` | the order IS `mixLt` over the closure — `Iff.rfl`, exactly the debt lemmas' `hlt` |
| `extFrame_disj_dr` | disjointness IS the model's `DR`, by composition down both sides (`comp(PP,DR)={DR}` then `comp(DR,PPI)={DR}`) — so `hdr`/`hdrk`/`hqdr` are premises about a REAL relation |

**Remaining for `Decidable (Satisfiable C₀)` on this fragment:**

1. **The extraction proper** — choose `β` (from `mixNodes`), the step relation
   (the `∃PP`-demand steps), `κ` and the kernels (from `pp_dichotomy`'s second
   branch via `ascend` + `recurrent_tail`), `side := dir`, `att`.
2. **The witness lists** — `rDR`/`rPO`/`rPP`/`rPPI`, `kDIR`/`kDR`/`kPO`/`kUP`/`kDN`.
   With `extFrame_disj_dr` these are now model facts, not frame facts.
3. **Reindex** onto `Fin nE`/`Fin nK`, feed `encodeMT_mem_codesM` with `mixKT`,
   then `hcompl` + `decidableSat_of_codes`.

### 44.21 The seed must be abstract too, and the external debt closes (2026-08-22)

**The catch.** Writing `hb` (`disj` ⟹ budgets within one) exposed that
`seed := drSeed` — the model's FULL `DR` on the chosen nodes — is too generous.
This is exactly §44.8's mistake for `elt := eltOf`, now on the disjointness side.
The model relates many pairs by `DR`, including externals whose budgets are far
apart (`N` and `N-3`), and `ee_all` fires on every declared `DR` edge.

**The fix.** `seed` abstract — any symmetric sub-relation of the model's `DR`.
The extraction then declares only its own `DR`-demand steps, and

```
bud x = bud x₀        (x ≤ x₀ along tcl ppStep — budget CONSTANT)
      ≤ bud y₀ + 1    (a DR-demand step drops the budget by exactly one)
      = bud y + 1
```

`hseed` (⟹ model `DR`) is all `hsep_of_model` and `extFrame_disj_dr` ever needed,
and a sub-relation satisfies it just as well. `drSeed`/`drSeed_sym` are kept as
the record of the MAXIMAL choice, the way `eltOf_sub` records it for the order.

**The external debt is now closed**, both halves:

| | |
|---|---|
| `ppStep_rho` | a step IS a model `PP` edge |
| `tcl_ppStep_bud` | **the budget is CONSTANT along the order** — §44.3's discipline, now a theorem about the relation the certificate declares, not a convention about how the node set is walked |
| `ppStep_hppE` | `hppE` discharged: the budget conjuncts are consequences of an EQUALITY |
| `extFrame_disj_dr` | `hdr` |
| the display above | `hb` |

**Method.** Fourth time the same rule has paid: *write the consumer before
believing the definition*. §43.8 (`elt`), §44.19 (the existence/construction
seam), and now the seed. In every case the definition looked right in isolation
and failed the moment an obligation was written against it.

### 44.22 The external side of the extraction is COMPLETE (2026-08-22)

`mtkKernelsOD_of_debts` asks three things of the externals. All three are now
theorems about the extraction's own data:

| obligation | discharged by | content |
|---|---|---|
| `hppE` | `ppStep_hppE` | relation half from `ppStep_rho`; budget halves are consequences of an EQUALITY (`tcl_ppStep_bud`) |
| `hdr` | `extFrame_disj_dr` | `disj` IS the model's `DR`, by composition down both sides |
| `hb` | `seedMix_hb` | `sAdjK_bud` for the external seed block; one new input `hkb` for the kernel block |

with the two structural pieces underneath:

* **`elt := tcl ppStep`** — the extraction's own `∃PP`-demand steps, closed
  transitively. `tcl_ok` gives `odSeed` everything it asks; `tcl_ppStep_bud`
  makes §44.3's constant-budget discipline a theorem about the DECLARED relation.
* **`seed := seedMix`** — `sAdjK` (already in the campaign) on externals, a bank
  block for kernels, and NO kernel-kernel block: cross-kernel `DR` comes from
  `djDown` for free, and declaring it would be the `hrectQ` staircase again.

`hkb` is not a new unknown: §43.10 already fixes bank members one budget below
their kernel.

**Remaining:** the kernel side (`hup0`/`hdn0`, then `hup`/`hdn`/`hdrk` and
`hqpp`/`hqppi`/`hqdr` — the last three composition-forced by §43's
`cross_*_of_shared`), the coverage witness lists, and reindex / bounds /
`hcompl`.

### 44.23 Obligation ledger for `mtkKernelsOD_of_debts` (2026-08-22)

| obligation | status | by |
|---|---|---|
| `hppE` | **done** | `ppStep_hppE` |
| `hdr` | **done** | `extFrame_disj_dr` |
| `hb` | **done** | `seedMix_hb` (+ `mixLe_inl_bud`) |
| `hup` relation | **done** | `hup_reach` from the base fact |
| `hdn` relation | **done** | `hdn_reach` from the base fact |
| `hqpp` | **done** | `hq_pp_of_bases` — **not a model debt at all**, it follows from `hup`/`hdn`'s bases |
| `hqppi` | **done** | `hq_ppi_of_bases` |
| `hdrk`, `hqdr` | open | the `DR` bank's window (`exists_bank` + `bank_window`) |
| `hup`/`hdn` budgets | open | the extraction's budget assignment (§43.10: bank members one below their kernel) |
| `he_ex`, `hk_ex` | routing **done** (`odSeed_he_ex`/`odSeed_hk_ex`); witness LISTS open | `mtkNodesH_covers`, the banks, `rr_covers` |
| `hp`, `hstep`, `hty` | open | `ascend` + `recurrent_tail`/`rr_segment_from` |

The pattern that keeps recurring is worth naming: **almost every kernel
obligation is composition-forced rather than model-supplied.** `hqpp`/`hqppi`
are the sharpest case — they looked like two more model debts and turned out to
be consequences of `hup` and `hdn`. What the model genuinely has to supply is
much smaller than the interface suggests: the base attachments, the `DR` bank
windows, and the kernels' periodicity.

### 44.24 Every RELATION half is now done (2026-08-22)

`mtkKernelsOD_of_debts`'s obligations each split into a RELATION half (what the
model relation must be) and, for the kernel ones, a BUDGET half. All the relation
halves are now theorems:

| obligation | relation half | by |
|---|---|---|
| `hppE` | ✔ | `ppStep_hppE` (budget halves too — an equality) |
| `hdr` | ✔ | `extFrame_disj_dr` |
| `hb` | ✔ (whole) | `seedMix_hb` |
| `hup` | ✔ | `hup_reach` |
| `hdn` | ✔ | `hdn_reach` |
| `hqpp` | ✔ | `hq_pp_of_bases` — not a model debt |
| `hqppi` | ✔ | `hq_ppi_of_bases` |
| `hdrk` | ✔ | `disj_dr_ph` |
| `hqdr` | ✔ | `disj_dr_ph` |

`mixLt_rho_ph` / `disj_dr_ph` are the generalization that did it: reading each
kernel at an arbitrary phase `ph k` rather than at its base costs one parameter,
and the kernel–kernel case is exactly `hq_pp_of_bases`. Both **axiom-free**.

**What is left is now a short and homogeneous list:**

1. **The base attachment facts at every phase** — `hupP`/`hdnP`, i.e. an
   attached external is `PP`-inside / `PPI`-outside every phase of its kernel.
   This is what `exists_bank_ppi` and `exists_bank` deliver, via
   `bank_window_ge` / `bank_window`.
2. **The budget halves** — `bud e ≤ bk k + 1 ∧ bk k ≤ bud e + 1` and
   `bk k ≤ bk k' + 1`. The extraction's budget assignment (§43.10: bank members
   one below their kernel).
3. **The coverage witness lists** — the routing is done
   (`odSeed_he_ex`/`odSeed_hk_ex`); what remains is producing the witnesses from
   `mtkNodesH_covers`, the banks and `rr_covers`.
4. **The kernels themselves** — `hp`, `hstep`, `hty` from `ascend` +
   `recurrent_tail`/`rr_segment_from`.

Every item is now "produce a model fact from machinery that exists", with no
composition reasoning left in any of them.

### 44.25 Items 1 and 4 done (2026-08-22)

**Item 1 — the base attachment facts.** The bank output already IS the
attachment fact, in the orientation the obligations want; `conv ppi = pp` and
`conv pp = ppi` do the rest.

| | from | reading |
|---|---|---|
| `hupP_of_bank` | `exists_bank_ppi` (EARLY picking, uniform anchor) | an UP-kernel's external is inside every phase from the anchor on |
| `hdnP_of_bank` | `exists_bank`, `PP` branch (LATE picking, backward forcing) | a DOWN-kernel's external contains every phase in the window |
| `hdrP_of_bank` | `exists_bank`, `DR` branch | `conv dr = dr`, orientation free |

All three `Classical.choice`-free.

**Item 4 — the kernels.** `kernel_of_chain`: model types along an ascending
chain are drawn from `typeEnum C₀`, so `segment_exists` (already in the file)
returns a recurrent segment past any bound — a base and a POSITIVE period with
equal model types. That is `hty` and `hp`; `ascend_step` is `hstep`. So
`pp_dichotomy`'s infinite branch produces a kernel with **no new mathematics**:
the pigeonhole is the same one the fuel uses.

**Remaining: items 2 and 3.**

2. **The budget assignment.** Set `bk k := bud e` for the external whose `∃PP`
   the kernel serves, and bank members at `bk k - 1`. Then for any attached `e''`
   (budget constant along `elt`) `bud e'' = bk k`, and for a bank member `w`,
   `bud w = bk k - 1` — both satisfy `bud ≤ bk + 1 ∧ bk ≤ bud + 1`. This is a
   choice to make inside the extraction, not a fact to discover.
3. **The coverage witness lists.** Routing done (`odSeed_he_ex`/`odSeed_hk_ex`);
   what remains is producing the witnesses from `mtkNodesH_covers`, the banks and
   `rr_covers`.

### 44.26 The coverage witnesses, and a third parameter that had to stay abstract

**All four horizontal/vertical witness branches of `odSeed_he_ex` are now
supplied**, each from the model's own `mtkWitness`/`ppWitness`/`ppiWitness`:

| branch | witness | frame condition |
|---|---|---|
| `rDR` | `mtkWitness` | `sAdjK`-adjacent BY DEFINITION — the seed's external block |
| `rPO` | `mtkWitness` | `PO` is neither `PP` nor `DR`, so no `elt` edge and no `disj` (`po_not_elt`, `po_not_disj`) |
| `rPP` | `ppWitness` | one step — an `elt`-SUCCESSOR |
| `rPPI` | `ppiWitness` | one step — an `elt`-PREDECESSOR |

**The catch, found by writing `rPPI` against the routing lemma.** `ppStep` alone
does NOT cover `rPPI`: an `∃PPI` witness is a proper PART of the demanding node,
so it is an `elt`-predecessor, and no `∃PP` demand need point at it. The step
relation must be

```
stepAll e f := ppStep e f ∨ ppiStep f e
```

— an `∃PPI` demand contributes its step in the OTHER direction. Both still point
up the model's `PP`, so every `tcl` fact survives and the budget stays constant
(`tcl_stepAll_bud`).

**And the knock-on.** `mixLe_inl_bud` and `seedMix_hb` hard-coded `tcl ppStep`.
They now take the step abstractly with a budget-constancy hypothesis — the third
time a parameter had to be kept abstract rather than pinned to the first
plausible instance (`elt` §44.8, `seed` §44.21, `step` here). The pattern is the
same each time: **pin a parameter and the obligations written against it stop
being provable; keep it abstract and carry only the property actually used.**

### 44.27 The persistent / one-shot split — where the two halves meet (2026-08-22)

`rr_covers`, the certified round-robin coverage that discharges `kDIR`, consumes
`persistAll I C0 Ds x`: every demand in `Ds` carries BOTH `∃PP.D` and its guard
`∀PP.(∃PP.D)`. The bridge that was missing is simply *which* demands those are.

`persistDs C0 I x` is the answer, and `persistAll_persistDs` says multi-persistence
holds for it **by construction**. So at any node the `∃PP` demands split cleanly
and decidably (`persistDs_split`):

| demand | served by | machinery |
|---|---|---|
| **persistent** (guard holds) | a round-robin KERNEL | `rrPt` + `rr_segment_from` + `rr_covers` — all already certified |
| **one-shot** (guard fails) | an `elt` edge to an EXTERNAL | §44's whole point; terminates by `short_chain` |

**This is where the two halves of the campaign meet.** §33 found one-shot `∃PP`
unhandled; §44 built the external order to handle it; the vertical quadrant was
certified years-of-rounds ago for persistent demands. `persistDs` is the line
between them, and it is a filter of `cl C₀` — decidable, and computable from the
node's type.

The split also explains why the campaign kept finding one-shot `∃PP` awkward:
the certified vertical machinery is *correct* and *complete for its half*; the
missing half was never a defect in it, only in the assumption that it covered
everything.

### 44.28 State

| | |
|---|---|
| frame (`extFrame`), certificate, all relation halves | done |
| the cut, adequacy (`short_chain`), the dichotomy | done |
| node bound (`mixNodes_length_le`, `mixKT`) | done |
| bank → attachment (`h*P_of_bank`), kernels (`kernel_of_chain`) | done |
| horizontal witnesses (`rDR`/`rPO`/`rPP`/`rPPI`) | done |
| persistent/one-shot split (`persistDs`) | done |
| kernel witnesses `kDR`/`kPO`/`kUP`/`kDN` | open |
| the budget assignment | open — a choice, not a discovery |
| reindex / bounds / `hcompl` | open, templated |
