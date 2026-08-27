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

### 44.29 A kernel is something a node already HAS (2026-08-22)

`ascKernel_of_node` supplies, from one node with a nonempty `persistDs`,
everything `mtkKernelsOD_of_debts` asks of a kernel:

| certificate field | from |
|---|---|
| the chain, `hdom` | `rrPt`, `rrPt_dom` |
| `hstep` (`cdir true = pp`) | `rrPt_step` |
| base `ik`, period `pk`, `hp`, `hty` | `rr_segment_from` |
| `kDIR` | `rr_covers` |

with one detail that matters beyond bookkeeping: **`rr_segment_from` places the
base past ANY bound `L0`**, which is exactly what `hinj` needs to keep the kernel
base off the finite external list (`exists_index_avoiding`'s job in the earlier
design, now free).

So a kernel is not something the extraction has to build. Given the
persistent/one-shot split, it is something a node with persistent demands
**already has** — and every ingredient predates §44 by many rounds. What §44
added was not new vertical machinery but the boundary telling you when to reach
for it.

### 44.30 Remaining

| | |
|---|---|
| `kDR`/`kUP`/`kDN` witnesses | packaging — the bank member IS the witness, with `leE` reflexive |
| the budget assignment | a choice inside the extraction (§43.10) |
| reindex → bounds → `hcompl` → `decidableSat_of_codes` | templated on the certified horizontal path |

### 44.31 Coverage ledger CLOSED — all nine branches (2026-08-22)

`k_vert_witness` and `k_dr_witness` finish it. Both hand over the bank member
directly: `kUP`/`kDN` ask for a pair `f, e'` with `e'` attached and `f`
`leE`-comparable, and `leE` is REFLEXIVE, so `f = e' = w` serves both
orientations; `kDR`'s seed block is precisely "this external is a `DR`-bank
member of this kernel".

| routing | branches | all supplied from |
|---|---|---|
| `odSeed_he_ex` | `rDR`, `rPO`, `rPP`, `rPPI` | `mtkWitness` / `ppWitness` / `ppiWitness` + `po_not_elt`/`po_not_disj` |
| `odSeed_hk_ex` | `kDIR`, `kDR`, `kPO`, `kUP`, `kDN` | `rr_covers` (via `ascKernel_of_node`), the banks, `kPO_frame` |

**Nine for nine, and not one of them needed a new model fact** — every branch is
either the model's own witness function, a bank member, or a composition
already certified.

### 44.32 What is left, precisely

1. **The budget assignment.** `bk k := bud e` for the external whose `∃PP` the
   kernel serves; bank members at `bk k - 1`. A choice, with the arithmetic
   already checked (`mixLe_inl_bud`, `seedMix_bud`, `tcl_stepAll_bud`).
2. **The assembly** — bundle β (from `mixNodes`), κ (from `persistDs`-nonempty
   nodes, kernels by `ascKernel_of_node`), the frame (`extFrame`), and apply
   `mtkKernelsOD_of_debts`.
3. **The tail** — `reindexMT`/`reindexMT_ok` onto `Fin nE`/`Fin nK`, then
   `encodeMT` → `encodeMT_mem_codesM` → `hcompl` → `decidableSat_of_codes`. The
   template is `hfrag_hcompl`, which is eleven lines.

Artifact: 24,493 lines, 0 sorries, 0 warnings, 0 `sorryAx`; 435 axiom checks, of
which 25 results depend on **no axioms at all**.

## 45. FLAGGED: a kernel phase with a NON-persistent `∃PP` demand (2026-08-22)

Working toward the assembly, one question has to be settled before the pieces
can be bundled, and I do not think it is settled.

### 45.1 The question

§44.27's split routes a node's `∃PP` demands two ways: **persistent** ⟹ a
round-robin kernel, **one-shot** ⟹ an `elt` edge to an external. That split is
stated for EXTERNALS, where both routes exist.

A kernel PHASE has only one route. `odSeed_hk_ex`'s branches for `r = pp` at an
ASCENDING kernel are:

* the `cdir` branch — rung-to-rung, discharged by `rr_covers`, which needs
  `persistAll`;
* the external branch — needs `K k f = pp`, i.e. `mixLt (inr k) (inl f)`, i.e.
  **`side k = false`**. An ascending kernel has `side = true` (§43.10).

So **a phase carrying a non-persistent `∃PP` demand has nowhere to send it.**

### 45.2 Why the obvious escapes do not work

* *"Take the recurrent sub-chain."* Type recurrence does give a clean window: the
  last phase's chosen demand wraps to phase 0 because `mty (c n₁) = mty (c n₀)`.
  But that only covers the demand the chain was BUILT to serve. A phase with
  several `∃PP` demands needs all of them carried inside the period, which is
  exactly what round-robin provides and what `persistAll` is required for.
* *"Let the kernel be below some externals and above others."* That is `side`
  becoming per-external rather than per-kernel, which breaks the height-two
  order and `mixLt_no_below` — the lemma that makes `djDown` terminate.
* *"Make `att` do it."* `att` is already per-external; the obstruction is `side`
  in `mixLt`'s `inr/inl` clause, not the attachment.

### 45.3 Status

This is not a defect in anything certified. Every §44 result stands; the split
in §44.27 is correct as stated, **for externals**. What is not established is
that the split is EXHAUSTIVE once kernels are in play.

Three ways it could resolve, in the order I would try them:

1. **The case is unreachable** — a phase of a kernel extracted from a ∀PO-free
   model always has persistent `∃PP` demands. Plausible (the phase sits on an
   infinite ascending chain, which is close to what the guard asserts) but NOT
   proved, and "close to" is exactly the wording that has been wrong four times
   this session.
2. **Route it to a kernel-kernel edge** — `k_ex`'s fourth branch, unused so far
   (§43.11 deliberately kept it empty to avoid the `hrectQ` staircase). Using it
   reopens that question.
3. **Widen the order** — allow a kernel above some externals and below others,
   at the cost of re-proving `mixLt`'s transitivity and `djDown` over a taller
   structure.

Route 1 is the cheap one to test, and it is a crisp question a probe can attack:
*can a ∀PO-free concept force an infinite ascending chain on which some `∃PP`
demand is never persistent?*

### 45.4 The probe failed, and why that matters (2026-08-22)

`wp100` was written to test route 1 (*is the case unreachable?*). **It cannot
answer the question, and the run shows why.**

Over finite set models **100% of `∃PP` demands come out "non-persistent"** — not
because non-persistence is common, but because the guard `∀PP.(∃PP.D)` ALWAYS
fails at a maximal element, and every finite model has one. Persistence is by
definition a property of infinite ascending chains, so a finite-model probe
measures nothing about it. Part D confirms it from the other side: the
constructed persistent tower is UNSATISFIABLE over finite models — correctly,
since it forces an infinite chain.

The 100% figure is an artifact of the model class. Reading it as evidence — in
either direction — would have been wrong.

**Why record a failed probe.** Every earlier probe in this campaign
(`wp96`–`wp99`) worked over finite set models, and that was fine because every
earlier question was about composition, budgets or counting — all finite-model
questions. §45 is the first question about an *infinite* structural property,
and the standing probe technique silently does not apply. That boundary is worth
having written down: **the probe habit has a domain, and persistence is outside
it.**

Answering §45 needs either infinite models (intervals over ℚ, or a
finitely-presented infinite structure) or a proof. §45.3's routes 2 and 3 remain
available and are unaffected.

### 45.5 Persistence CLIMBS — §45 narrows to acquired demands (2026-08-22)

Rather than push route 1 speculatively after `wp100` failed, one fact settles
cheaply and narrows the target a long way.

**`persistDs_up`**: the guard `∀PP.(∃PP.D)` propagates upward (`sat_all_pp_up`,
via `comp(PP,PP) = {PP}`) and also DELIVERS `∃PP.D` at everything above its
holder. So

```
x PP y   ⟹   persistDs x ⊆ persistDs y
```

— the persistent set only GROWS along an ascending chain.

Two consequences:

* a demand persistent at a kernel's BASE stays persistent at every phase, so the
  `Ds` chosen at the base **never degrades** — not previously established;
* contrapositively (`persistDs_gap_is_acquired`), a demand non-persistent at a
  phase was already non-persistent at the base.

**So §45's open case is now:** the problematic demand must be one the phase
**ACQUIRED** — present at the phase, absent (or non-persistent) at the base, and
non-persistent at the phase. That is a far narrower target than "some phase has
a non-persistent demand", and it suggests where to look: a phase can only
acquire a demand if its type differs from the base's, so the case is confined to
phases strictly inside a period, never to the recurrent type itself.

**Judgment on how to proceed.** Route 1 is now worth a real attempt rather than
a probe, because the remaining case is small and structural. If it resists, route
3 (widen the order) is preferable to route 2, since route 2 reopens `hrectQ`,
which §43.11 closed by construction and would be a regression.

### 45.6 Route 1 analysed: the gap is TWO simultaneous one-shot demands (2026-08-22)

*Analysis, not yet Lean. Recorded because it sharpens §45 to a specific
configuration and changes which route to take.*

**Route 1 is false as stated.** The configuration is constructible: let the chain
be driven by a persistent `∃PP.B`, and put `c(1) ⊂ w ⊂ c(2)` with `A` at `w` and
no superpart of `c(2)` carrying `A`. Then `∃PP.A` holds at `c(1)` and fails at
`c(2)`, so `A` is non-persistent at the phase `c(1)`. Nothing forbids this.

**But the extraction chooses the chain**, and that changes the picture. If a
phase's demand is unserved, INSERT its witness as the next chain node. `w` is a
superpart of `c(1)`, so the chain `… ⊂ c(1) ⊂ w ⊂ …` is legitimate, and the
persistent demands survive the insertion by `persistDs_up`. So **one** one-shot
demand per phase costs one extra step and is served.

The wrap-around also works: if every phase's demand is served at the NEXT phase,
then `kDIR` holds with `b = a+1` for `a < p-1`, and for the last phase `b = 0` —
because `mty (c i) = mty (c (i+p))` makes the argument carried at phase 0 exactly
when it is carried at phase `p`.

**Where it actually breaks: TWO simultaneously-live one-shot demands at one
phase.** A linear chain has ONE successor. Serving `D₁` at `c(a+1)` is fine, but
`D₂`'s witness is a superpart of `c(a)` and need not be comparable with `c(a+1)`
— and `∃PP.D₂` need not survive to `c(a+1)`, precisely because `D₂` is not
persistent. Persistence is exactly what makes round-robin work
(`persistAll_productive`); without it there is nothing to cycle.

So §45's sharp form is:

> **can a satisfiable ∀PO-free concept force a kernel phase to carry two
> simultaneously-live NON-persistent `∃PP` demands?**

**Consequence for the route choice.** This is not a "widen the order" problem
(route 3 does not help: the phase still has one successor), and not a
cross-kernel problem (route 2 does not help either). It is a question about
whether the FRAGMENT can force that configuration — the same species as §33's
one-shot finding, one level up. The honest options are now:

1. **prove it unforceable** — plausible, since forcing two one-shot demands to be
   simultaneously live at a node that must also sit on an infinite chain is a
   strong requirement;
2. **restrict the certified claim** to concepts where it does not arise, which
   would be a real narrowing of the fragment and must be labelled as such;
3. **branch the kernel** — replace the linear chain by a tree, which is a
   different certificate shape (`MultiTier`'s kernels are `Nat`-indexed) and
   therefore a substantial redesign.

Option 1 is the one to attempt; option 2 is the honest fallback.

### 45.7 The lead for route 1: only ACCIDENTAL demands can be one-shot (2026-08-22)

Certified this round (`persistDs_of_guard_below`, `oneshot_no_guard_below`):

> If the guard `∀PP.(∃PP.D)` holds ANYWHERE BELOW `y`, then at `y` both the
> demand and its own guard hold — so `D` is persistent at `y`.

Contrapositive: **a one-shot demand at a chain node has no guard anywhere
strictly below it.**

So a chain node's `∃PP` demands come in exactly two kinds:

| origin | persistence |
|---|---|
| INHERITED — some node below carries `∀PP.(∃PP.D)` | **automatically persistent** |
| ACCIDENTAL — the model satisfies `∃PP.D` there with no guard beneath | may be one-shot |

§45.6 showed the gap needs TWO simultaneously-live one-shot demands at one
phase. §45.7 now says both of them must be ACCIDENTAL.

**Why that is the right target.** Completeness lets us CHOOSE the model. An
accidental demand is, by definition, not forced by the concept — so the natural
attack is a model-normalization: *every satisfiable ∀PO-free concept has a model
in which chain nodes carry no accidental `∃PP` demands*, or at most one. That is
a statement about models rather than about the certificate, and it does not touch
any certified result.

Note this is NOT §33.3's "persistify", which tried to turn one-shot demands INTO
persistent ones and failed on forced leaves. The direction here is the opposite —
REMOVE accidental demands rather than strengthen them — and forced leaves are
precisely the case it does not have to handle, because a forced leaf's demand is
inherited, hence already persistent.

**Next step:** formulate the normalization precisely and test whether the
certificate's own soundness direction already produces such a model — the
model built by `multiTier_sound` from a certificate satisfies exactly the
labels, so it has no accidental demands by construction. If that closes the
circle, route 1 succeeds.

### 45.8 The cheap route-1 check FAILS, and an honest cost table (2026-08-22)

**The check.** Does `multiTier_sound`'s built model have no accidental demands?
**No.** It builds the model from `mtLabel T` via `sat_from_hintikka_frame`, and
the truth lemma runs ONE way: `C ∈ label → sat`. The converse is not available,
and cannot be — a node of `munf` may satisfy `∃PP.D` because some `PP`-related
node satisfies `D`, whether or not `D` is in its label. So the circle does not
close, and route 1's cheap version is dead.

**Two further facts found while checking, both narrowing and both unwelcome:**

* Accidental demands cannot be escaped by raising the kernel base. Along the
  chain `persistDs` stabilizes (it grows, inside a finite set), and by type
  recurrence an accidental demand present at a recurrent type recurs
  **infinitely often**. There is no base above them all.
* `persistDs` is **not type-determined**: it depends on `sat x (∀PP.(∃PP.D))`,
  and that formula need not be in `cl C₀`. So two nodes of the same model type
  can differ in which demands are persistent — which also means the recurrence
  machinery (`hty`, stated on `mty`) does not control persistence.

**Cost table, honestly.**

| route | what it costs | risk |
|---|---|---|
| 1a — model normalization (every satisfiable ∀PO-free `C₀` has a model with ≤1 accidental `∃PP` per chain node) | unknown; a fresh model-theoretic argument | may be FALSE; nothing certified suggests it |
| 1b — FORCED labels instead of model types (drop accidental demands from the label) | touches `mtkKernelsOD`, `_ok`, all coverage routing, `mixNodes`, the bound, the encoder | multi-session; large parts of §44 reworked |
| 3 — BRANCHING kernels (a phase with several one-shot demands needs several successors — i.e. a tree) | `MultiTier`'s kernels are `Nat`-indexed; this changes `munf` and the SOUNDNESS core | multi-session; touches certified soundness, the one thing that has never had to move |

**Assessment.** 1b is the most principled — a certificate label *should* be what
the concept forces, not what a model happens to satisfy, and it is the reading
under which "accidental demand" stops being a category at all. But it is a
genuine refactor of the label layer, and the label layer is what everything else
is stated against.

**This is a decision point, not a step**, and it should be taken deliberately
rather than drifted into.

### 45.9 Route 1a: the mechanism, identified and certified (2026-08-22)

A guard `∀r.X` held at `z` reaches a node `w` only if `z` is `r`-related to `w`.
Going UP from `y` to a superpart `w`, the relation `z`-to-`w` lies in
`comp (z-to-y) PP`. The table decides which guards are unavoidable:

| cell | value | consequence |
|---|---|---|
| `comp PP PP` | `{PP}` — **forced** | a `∀PP` guard reaches every superpart of every node it reaches (`sat_all_pp_up`), so `∀PP`-inherited demands are **persistent** |
| `comp DR PP` | contains `PO` | a `∀DR` guard need NOT reach upward — the model may place `z PO w` |
| `comp PPI PP` | contains `PO` | same |
| `comp PO PP` | contains `PO` | same |

Certified as `dodge_cells`; `forced_cells` records the dual (`PP` forced upward,
`DR` forced downward via `comp DR PPI = {DR}`, nothing else forced either way).

**So route 1a's mechanism is identified.** The `∃PP` demands a chain node cannot
avoid are exactly the `∀PP`-inherited ones — and those are persistent
(`persistDs_of_guard_below`). Any `∃PP` demand delivered by a NON-`PP` guard can
be dodged: a model is free to choose `PO` above the chain where the table
permits.

**What 1a still needs.** The dodge is available cell-by-cell; making it a MODEL
CONSTRUCTION requires choosing `PO` consistently for all such pairs at once and
checking the result is still composition-closed and still a model of `C₀`. That
is a patchwork/amalgamation argument — the project's oldest tool (`wp6`,
`wp14`), and exactly the kind of thing the RCC5 patchwork property is for.

**Assessment.** This is a genuinely better position than §45.8: the target moved
from "unknown model-theoretic argument" to "a specific, local, composition-legal
edge choice, made globally consistent by patchwork". It is not finished, and I
am not claiming it will close — but it is now a concrete construction with a
named tool, rather than a hope.

## 46. CORRECTION: route 3 DOES work, and here is what it costs (2026-08-22)

### 46.1 The correction

§45.6 dismissed route 3 with "the phase still has one successor". **That is
wrong.** The accidental demand does not need a chain successor — it needs an
EXTERNAL. `k_ex`'s external branch serves `r = pp` via `K k f = pp`, i.e.
`mixLt (inr k) (inl f)`, i.e. the kernel BELOW `f`. So an accidental `∃PP.D` at a
phase is served by an external `f` ABOVE the kernel carrying `D`.

The only thing blocking that is `side` being **per-kernel**: `mixLt`'s `inr/inl`
clause reads `side k = false`, so a kernel that is above its `∃PP`-served
externals (`side = true`) can never be below anything.

### 46.2 The fix, precisely

Replace the per-kernel `side` by two per-external predicates, `up k e` and
`dn k e`. Then

```
inl e < inr k   iff  ∃ e', up k e' ∧ e ≤ e'
inr k < inl e   iff  ∃ e', dn k e' ∧ e' ≤ e
inr k < inr k'  iff  ∃ e e', dn k e ∧ up k' e' ∧ e ≤ e'
```

Transitivity goes through with **one** coherence condition —

> `up k x ∧ dn k y  ⟹  elt x y`

— which is semantically forced anyway (`x ⊂ kernel ⊂ y`). All eight cases check;
irreflexivity uses the same condition. `mixLt_no_below` becomes false but is NOT
used by `odSeed` (its `djDown` is free by downward closure — that was `odMix`'s
lemma).

**This closes §45**: accidental demands route to externals above the kernel, and
no phase needs two successors.

### 46.3 What it costs — the honest number

The order is what everything in §§43–44 is stated against. Changing it touches,
at minimum:

`mixLt`, `mixLt_trans`, `mixLe_trans`, `odSeed`, `odSeed_K_up`/`_K_dn`/
`_Q_forced`, `mixLt_rho`, `mixLt_rho_ph`, `hsep_of_model`, `disj_dr_ph`,
`odLt_E_cases`, `odLt_hEreal`, `odLt_hKreal`, `odLt_hQreal`,
`mtkKernelsOD_of_debts`, `hup_reach`, `hdn_reach`, `hq_pp_of_bases`,
`hq_ppi_of_bases`, `mixLe_inl_bud`, `seedMix_hb`, `kPO_frame`, `extFrame`,
`extFrame_lt`, `extFrame_disj_dr`, `odSeed_he_ex`, `odSeed_hk_ex`.

**Twenty-six declarations.** Every one is a mechanical re-statement — no new
mathematics, and the proofs are the same compositions — but it is the whole
frame layer, and it is a multi-session refactor by any honest count.

### 46.4 The choice

* **Do it.** §45 closes, the fragment stays fully general, and nothing in the
  soundness core moves. Cost: the refactor above.
* **Park §45.** Everything certified stands; the gap is precisely documented and
  the fix is specified, so a later session can execute it cold.

I do not think this is mine to decide unilaterally: it is a scope commitment, and
it is exactly the multi-session refactor that was flagged as unwelcome.

### 46.5 DONE — §45 is closed (2026-08-22)

The refactor is executed. `mixLt` now reads

```
inl e < inr k   iff  ∃ e', up k e' ∧ e ≤ e'
inr k < inl e   iff  ∃ e', dn k e' ∧ e' ≤ e
inr k < inr k'  iff  ∃ e e', dn k e ∧ up k' e' ∧ e ≤ e'
```

with the single coherence condition `hud : up k x → dn k y → elt x y`, which is
semantically forced (`x ⊂ kernel ⊂ y`). All eight transitivity cases go through;
irreflexivity uses the same condition. `mixLt_no_below` is dropped — false now,
and never used by `odSeed`, whose `djDown` is free by downward closure.

**§45 closes**: a phase's accidental `∃PP` demand is served by an external ABOVE
the kernel, through `k_ex`'s external branch (`K k f = pp`, i.e.
`odSeed_K_dn`). No phase needs two successors, and the persistent/one-shot split
is now exhaustive for phases as well as externals.

**Twenty-six declarations restated, exactly as costed in §46.3, with no new
mathematics** — every proof is the same composition, and the SOUNDNESS CORE was
not touched. Final state: 24,576 lines, 0 errors, 0 warnings, 0 sorries,
0 `sorryAx`; 439 axiom checks, 26 results depending on no axioms.

**What the refactor cost in practice.** Five build cycles, driven entirely by
destructuring arity: every `⟨hs, e', hae, hle⟩` became `⟨e', hae, hle⟩` because
the `side` conjunct is gone. No proof needed a new idea. That is the signature
of a well-chosen refactor, and it is worth recording against the fear that it
would be open-ended.

### 46.6 Remaining

1. **The budget assignment** — `bk k := bud e`, bank members at `bk k - 1`.
2. **The assembly** — bundle β (`mixNodes`), κ (`persistDs`-nonempty nodes,
   kernels by `ascKernel_of_node`), the frame (`extFrame`), apply
   `mtkKernelsOD_of_debts`. The new `hud` obligation joins the list, and is the
   forced fact `x ⊂ kernel ⊂ y`.
3. **The tail** — `reindexMT` → `encodeMT` → `encodeMT_mem_codesM` → `hcompl` →
   `decidableSat_of_codes`, on the `hfrag_hcompl` template.

### 46.7 `hud` costs one edge and one budget equation (2026-08-22)

The refactor's new coherence condition asks for `elt x y` whenever a kernel is
ABOVE `x` and BELOW `y`. Semantically forced (`x ⊂ kernel ⊂ y`) — but `elt` is
`tcl step`, a closure of DEMAND steps, and `x` and `y` need not be connected by
demands at all. **The edge is not derivable; it has to be added.**

`mixStep e f := stepAll e f ∨ ∃ k, up k e ∧ dn k f` adds it, and then:

| | |
|---|---|
| `mixStep_hud` | `hud` discharged, in ONE constructor |
| `mixStep_rho` | still a real model `PP` edge — vertical half `stepAll_rho`, up/dn half composition through the kernel base |
| `tcl_mixStep_bud` | budget still constant, given ONE new input: a kernel's up- and down-externals sit at the SAME budget |
| `mixStep_hppE` | `hppE` for the full relation |

So the whole price of §46's generalisation is **one extra edge in the step
relation and one budget equation** — and the budget equation is the same choice
§43.10 already makes by putting bank members one below their kernel.

Worth noting as a check on the refactor: this is the only obligation §46 added,
and it was found by writing the assembly against the new order rather than by
inspecting it — the same rule, once more.

### 46.8 `extFrameM` — nothing structural left to choose (2026-08-22)

Two steps, both small:

* **`mixStep` generalized** to an abstract index type via a node projection `nd`.
  So `β` can be the FINITE node subtype the encoding needs, rather than
  `MTKNode I C0` itself. (`MultiTierOk` never needed `β` finite; the encoder
  does.)
* **`extFrameM`** fixes every structural parameter `extFrame` still took: the
  step is `mixStep`, its `PP`-soundness is `mixStep_rho`, and `hud` is
  `mixStep_hud`.

| | |
|---|---|
| `extFrameM` | the frame; nothing structural left to choose |
| `extFrameM_lt` | its order IS `mixLt` over the full step closure — the debt lemmas' `hlt`, by `Iff.rfl` |
| `extFrameM_disj_dr` | its disjointness IS the model's `DR` |

**What remains as hypotheses is exactly the model-side list**: the attachment
relations `hup0`/`hdn0`, and the seed's `hsym`/`hseed`. Four facts about a model,
and every other input to the frame is now determined.

### 46.9 Remaining

1. **Choose the data** — `β` from `mixNodes`, `κ` from the `persistDs`-nonempty
   nodes with kernels by `ascKernel_of_node`, `up`/`dn` from the attachment,
   `seed` from `seedMix`, budgets by §46.7's rule.
2. **Apply** `mtkKernelsOD_of_debts` with `O := extFrameM`, discharging the
   coverage branches from the nine witness lemmas.
3. **The tail** — `reindexMT` → `encodeMT` → `encodeMT_mem_codesM` → `hcompl` →
   `decidableSat_of_codes`.

Step 1 is the last one with choices in it; 2 and 3 are application.

### 46.10 The κ side of the data, built (2026-08-22)

`κ` is the set of nodes carrying at least one PERSISTENT `∃PP` demand — the
`persistDs`-nonempty ones (§44.27). Each such node HAS its kernel
(`ascKernel_of_node`), so the family is a projection:

| | |
|---|---|
| `KernelData` / `kernelData` | a kernel's chain, base, period and five properties as a BUNDLE, not an existential |
| `KIdx` | the index type |
| `kFam`, `kCk`, `kIk`, `kPk` | the family, and the data as FUNCTIONS — the shape the certificate wants |
| `kCk_dom`, `kCk_step`, `kPk_pos`, `kCk_ty` | `hdom`, `hstep`, `hp`, `hty` — all four by projection |
| `kCk_covers` | `kDIR`'s content: every persistent demand of the kernel's own node is carried inside the period |
| `kIk_ge` | the base is past the caller's bound — what `hinj` consumes |

Direction is `true` throughout (ascending). **The descending mirror is the same
construction over `rrPtI` / `rr_coversI`**, which the campaign already certifies;
it is not built here, and the fragment needs it, so it is on the list.

**What step 1 still owes:** `β` from `mixNodes` with its projection, `up`/`dn`
from the attachment, `seed` from `seedMix`, the budget assignment, and the
descending mirror. Then step 2 is one application.

### 46.11 The descending mirror and the external index (2026-08-23)

**The descending mirror, flagged in §46.10, is closed.** Every piece mirrors the
ascending side; only ONE lemma was genuinely new.

| | |
|---|---|
| `persistDsI` / `mem_persistDsI` / `persistAllI_persistDsI` | the persistent `∃PPI` demands; `persistAllI` by construction |
| **`rr_segment_fromI`** | the descending recurrence PAST ANY BOUND — `rr_segmentI` existed but without the `L0` part, which `hinj` needs. The one new lemma. |
| `descKernel_of_node` | a descending kernel, over `rrPtI` / `rr_coversI`, `cdir false = ppi` |
| `kernelDataI` | the descending producer |

`KernelData` now carries the DIRECTION as a parameter, so both producers land in
one bundle and the assembly can hold ascending and descending kernels in a
single family.

**The external index** is built: `EIdx` (the bounded closure as an index type),
`eNd` (`Subtype.val`, the projection `mixStep` reads through), `eList`
(`List.attach`, the encoder's enumeration), and `eList_length_le_KT` — the
encoder's `nE`, bounded by `K(C₀)`.

**Three insertion hazards, all caught by checking rather than by the build.**
Two docstring splits (§44.17, §46.11) and now an `open Classical in` stranded
from the declaration it modified. The build reported a *downstream* instance
failure, not the real cause. The standing checks — `#print axioms` for `sorryAx`
and a declared-count grep — have each caught a real problem, and neither is
replaceable by reading the error message.

### 46.12 Step 1 remaining

`up` / `dn` from the attachment, `seed` from `seedMix`, and the budget
assignment. Then step 2 is one application of `mtkKernelsOD_of_debts`.

### 46.13 The bank as data (2026-08-23)

`exists_bank` is an existence statement; the extraction needs the witness list as
DATA, because **`dn` — which externals a kernel is BELOW — is defined from it**.

`BankData` bundles the witness list, its domain facts, its structural size bound
(`≤ 2·|cl C₀|`, independent of the model) and its serving property; `bankData`
produces it.

**This is what makes §45's fix operational.** The chain from §45 to here:

1. §45 — a phase's accidental `∃PP` demand has nowhere to go under per-kernel
   `side`;
2. §46 — per-external `up`/`dn` lets it go to an external ABOVE the kernel;
3. §46.7 — that costs one edge (`mixStep`) and one budget equation;
4. §46.13 — and the externals in question are exactly the `PP`-bank members,
   which are now nameable.

So `dn k e := e ∈ (bank of k).ws` is a definition that can now be written.

### 46.14 Step 1 remaining

Only the wiring of the pieces that now all exist:

| | from |
|---|---|
| `up` | `decide (e = k.val)` — a kernel is above its own node |
| `dn` | membership in `(bankData …).ws` |
| `seed` | `seedMix` with `kdr` the `DR`-bank members |
| budgets | `bk k := bud (k.val)`, bank members one below (§43.10, §46.7) |

then step 2 — one application of `mtkKernelsOD_of_debts` — and step 3, the tail.

### 46.15 The kernel records its root, and `hup0` follows (2026-08-23)

`rrChain`'s base case is literally the node, so `c 0 = x` is `rfl`. Both kernel
theorems now record it along with `0 < i`, and `KernelData` carries them
(`croot`, `ipos`) with the node as a parameter.

| | |
|---|---|
| `kCk_root_pp` | the node is a proper part of its own kernel's BASE — `chain_pp_lt` from `croot` and `ipos` |
| `kCk_root_pp_phase` | and of every PHASE, the form `hupP` wants since the obligations quantify over the window |

With `up k e := (e = k.val)` that is exactly `hup0`. `chain_pp_lt` was already in
the file — checked before building, which is now the default rather than the
exception.

**Step 1 remaining:** `dn` from `BankData.ws`, `seed` from `seedMix`, and the
budget assignment. `up` is done.

### 46.16 The attachment is the model relation (2026-08-23)

`up` and `dn` need not be bookkeeping over the bank's witness list. They can be
**the model relation itself, held across the window**:

* `upAt k e` — `e` is inside every phase of `k` from its base on;
* `dnAt k e` — every phase of `k` from its base on is inside `e`.

That turns four obligations into instantiations:

| obligation | now |
|---|---|
| `hup0`, `hdn0` | `upAt_base`, `dnAt_base` — the phase fact at `a = 0` |
| `hupP`, `hdnP` | `upAt_phase`, `dnAt_phase` — `decide` unfolded |
| `hud`'s model fact | `upAt_dnAt_pp` — `comp(PP,PP) = {PP}` |
| κ's attachment | `upAt_self` — `kCk_root_pp_phase` in `upAt` form |

**And it narrows the bank's role to what it is actually for.** The bank was
never needed to *define* the attachment; it is needed to guarantee that a
suitable external EXISTS for each demand — `hupP_of_bank`, `hdnP_of_bank`,
`hdrP_of_bank`. Defining `up`/`dn` from the bank conflated the two and would have
carried list-membership bookkeeping through every obligation.

`upAt_self` is the one that closes the loop on §44.27: κ is defined as the
`persistDs`-nonempty nodes, and each such index now *provably* has its
attachment, rather than being given one by fiat.

**Step 1 remaining:** `seed` from `seedMix` with `kdr` in the same
relation-defined style, and the budget assignment.

### 46.17 The budget lives in the attachment (2026-08-23)

The budget assignment turned out **not to be a separate step**. An attached
external sits at the kernel's OWN budget, and that condition belongs INSIDE
`upAt`/`dnAt` rather than alongside them:

| obligation | now |
|---|---|
| `hup`/`hdn` budget halves | `upAt_bud`, `dnAt_bud` — projections |
| `mixStep`'s `hudbud` | `upAt_dnAt_bud` — both ends at the kernel's budget, hence EQUAL |
| `hkdr` | `kdrAt_base` |
| `hdrk`'s relation | `kdrAt_phase` |

Constant budgets along `elt` are §44.3's design, and termination comes from the
lexicographic measure `(budget, path length)` rather than from a budget drop —
so requiring EQUALITY (not "within one") costs nothing and buys `hudbud` outright.

That also retires §43.10's "bank members one below their kernel": it was the
right instinct under the old budget-decreasing reading, and the wrong constant
under §44.3's. Recording the correction rather than leaving two rules in the
design.

### 46.18 Step 1 is DONE

| datum | definition |
|---|---|
| `β` | `EIdx` — the bounded closure as an index type; `nd := Subtype.val` |
| `κ` | `KIdx` — the `persistDs`-nonempty nodes |
| kernels | `kFam` / `kCk` / `kIk` / `kPk`, from `ascKernel_of_node` (and `kernelDataI` for the descending mirror) |
| `up`/`dn` | `upAt` / `dnAt` — the model relation across the window, budget folded in |
| `seed` | `seedMix` with `kdr := kdrAt` |
| `step` | `mixStep nd up dn` |
| frame | `extFrameM` |
| budgets | a conjunct of the attachment |

**Step 2** — one application of `mtkKernelsOD_of_debts` — and **step 3**, the
tail, remain.

### 46.19 The last shape mismatch (2026-08-23)

`seedMix`'s external block read `sAdjK` on `MTKNode` directly. With `β` an index
type it needs the same node projection `mixStep` took, so `seedMix`,
`seedMix_sym`, `seedMix_dr`, `seedMix_bud`, `mixLe_inl_bud` and `seedMix_hb` now
all read their nodes through `nd`.

**That was the last shape mismatch between step 1's data and step 2's
interfaces.** `β`, the order, the seed and the frame now all speak the same
index type:

| | |
|---|---|
| `β = EIdx`, `nd = Subtype.val` | the bounded closure, bounded by `K(C₀)` |
| `κ = KIdx` | the `persistDs`-nonempty nodes |
| `elt = tcl (mixStep nd up dn)` | vertical demand steps + the up/dn edges |
| `up`/`dn` = `upAt`/`dnAt` | the model relation across the window, budget folded in |
| `seed = seedMix nd kdrAt` | `sAdjK` externally, the kernel block by relation |
| frame = `extFrameM` | nothing structural left to choose |

Step 2 is the application; step 3 is the tail.

### 46.20 The predicted contact issue, confirmed and fixed (2026-08-23)

§46.19 predicted that step 2's contact between the nine witness lemmas and the
ACTUAL node set would surface something. It did, immediately.

**The defect.** `mixNodes` excludes `∃PP` and `∃PPI` from its horizontal
recursion and delegates both to `ppNodes` — but `ppNodes` followed only `∃PP`.
So a ONE-SHOT `∃PPI` witness was in **no node set at all**, and `rPPI_witness`
— which produces an `elt`-PREDECESSOR — had nothing to point at.

The order is `stepAll`, which carries both directions (§44.26). The node set has
to match it, and it did not.

**The fix.** `ppiWitness` and its three lemmas moved up next to `ppWitness`;
`ppNodes` now follows `∃PPI` as well.

**The bound is unaffected** — and that is the interesting part. `ppNodes_length_le`
bounds each `attach` element's contribution by `mtkBound C0 fuel`, per ELEMENT,
not per direction. So following both directions costs nothing in the counting.
`ppNodes_bud` likewise survives, because `ppiWitness_bud` keeps the budget just as
`ppWitness_bud` does.

**Why this one was findable in advance.** §44.26 already recorded that the order
needs both directions, and the node set is what realizes the order. Two objects
that must agree, changed at different times. The lesson is not new — it is
§43.8's rule again — but it is the first time the prediction was made BEFORE the
contact rather than after.

### 46.21 The descending family (2026-08-23)

`KIdxI` (nodes with a persistent `∃PPI` demand), `kFamI`, `kCkI`/`kIkI`/`kPkI`,
and the five certificate fields by projection — the exact mirror of the
ascending family, over `kernelDataI`.

**`kCkI_root_ppi_phase`** is the one with content: a descending kernel is BELOW
its own node, because the chain starts AT the node and descends, so every phase
is a proper part of it. That is the `dnAt` side of `upAt_self`. It uses
`dchain_model_pp`, which was already in the file.

So both directions now have their index type, their family, and their attachment
fact. `κ` for the assembly is `KIdx ⊕ KIdxI`, with `dir := Sum.elim (fun _ => true) (fun _ => false)`.

### 46.22 Effort remaining, honestly

| remaining | character | rounds |
|---|---|---|
| combine κ into the sum, `dir`, and the per-side dispatch | mechanical | 1–2 |
| **step 2 coverage** | **real content** — at a fuel-exhausted leaf, apply `pp_dichotomy`: no demand, or a kernel | 3–5 |
| step 3 tail | reindex onto `Fin`, encode, `hcompl`; templated, needs a list↔`Fin` bijection | 2–3 |

**Roughly 6–10 focused rounds** if nothing new surfaces. The character of the
recent findings has changed: the last several were "two objects that must agree
and don't", each caught in one build cycle, rather than architectural. Step 2's
coverage is the one place with genuine content left, because that is where the
dichotomy gets APPLIED rather than stated.

### 46.23 The combined kernel index (2026-08-23)

`κ` for the assembly is `KIdx ⊕ KIdxI`, with `dir` reading the tag.

| | |
|---|---|
| `KIdxM`, `kNode` | the index and its anchoring node |
| `mCk`, `mIk`, `mPk`, `mDir`, `mBk` | the data, dispatching on the tag |
| `mCk_dom`, `mCk_step`, `mPk_pos`, `mCk_ty` | the four certificate fields, over BOTH directions |
| `mUp`, `mDn` + phase/bud lemmas | the attachment |
| `mUp_self_asc`, `mDn_self_desc` | each kernel attached at its own node in the RIGHT direction |

**The attachment needs no dispatch at all** — the same relation-defined formula
(§46.16) covers a kernel sitting above its externals and one sitting below.
That is the payoff from defining `up`/`dn` by the model relation rather than by
bookkeeping over a witness list: had they been list-membership, the sum would
have required a case split in every downstream obligation.

The κ side of step 1 is now complete for both directions.

### 46.24 Remaining

1. **Step 2 coverage** — the one item with real content. At a fuel-exhausted
   leaf, apply `pp_dichotomy`: either the node has no vertical demand, or it has
   a kernel. 3–5 rounds.
2. **Step 3 tail** — reindex onto `Fin` (needs a list↔`Fin` bijection), encode,
   `hcompl`. 2–3 rounds.

### 46.25 Step 2: the coverage obligation, pinned (2026-08-23)

`odSeed_he_ex` reduces `he_ex` to four routing conditions. **Three are already
discharged for the extraction's data:**

| condition | discharged by |
|---|---|
| `rDR`, `rPO` | `rDR_witness` / `rPO_witness` — the horizontal witness is `mtkWitness`, which `mixNodes`' recursion contains |
| the KERNEL disjunct of `rPP`/`rPPI` | `kCk_covers`, `kCkI_covers`, `mUp_self_asc`, `mDn_self_desc`, and `persistent_has_kernel` — a node with a persistent demand really does index a kernel |

**What is left is exactly the ONE-SHOT disjunct.** A non-persistent vertical
demand must be served by an `elt` edge INSIDE the node set. `ppNodes` contains
the witness (`ppWitness`/`ppiWitness`) whenever fuel remains, so the obligation
reduces to: **the one-shot chain fits in the fuel.** `NodeCovered` names it.

**What is known about it.** `short_chain` (§44.17) says any serving chain has a
companion of length ≤ `|typeEnum C₀|` with the same head type; `pp_dichotomy`
(§44.19) says a demand path either terminates or yields a kernel. Both are
certified. What is NOT yet done is applying them to `ppNodes`' own greedy chain
— `ppWitness` picks an arbitrary `Classical.choose` witness, and nothing yet says
that choice is the short one. That is the same existence/construction seam
§44.19 identified, now at its last occurrence.

**Assessment.** This is one obligation, precisely stated, with both ingredients
certified and the gap between them named. It is not a new mathematical problem;
it is the last place where an existence result has to be turned into a choice.

### 46.26 Why the one-shot fuel obligation resists a direct construction (2026-08-23)

Working the obligation directly, three routes were tried and each fails in an
instructive way. Recording them so the next attempt does not repeat them.

**Route A — make `ppWitness` pick the short chain's head.** `short_chain` needs a
FINITE input chain, so feed it the greedy chain of length `|typeEnum C₀| + 1`.
It returns a chain of length ≤ `|typeEnum C₀|` whose head has the SAME TYPE,
hence still carries `D`. Good so far. **But the short chain's LAST node need not
be demand-free**, so the set is not closed — the obligation reappears one level
down.

**Route B — extend-and-cut to a fixed point.** Maintain a repeat-free serving
chain; to serve the last node's demand, extend by its witness; if the extension
repeats a type, cut. Length is non-increasing after the first `|typeEnum|` steps
(a cut drops `end - i ≥ 1` and the extension adds 1). **But nothing forbids
oscillation** — extend, cut, extend, cut — so there is no termination measure and
no fixed point is produced.

**Route C — quotient by type.** Reuse an existing set member of the same type
instead of adding a node. Bounded immediately. **But reuse needs the existing
member to be `elt`-ABOVE the current node**, and `wp96` D already measured this:
type-quotienting loses coverage on 8.4% of instances. It is the W2′
uniformization failure, and it is not repairable by being cleverer about which
representative to keep.

**What the three failures have in common.** Each tries to CONSTRUCT the bounded
set. The certified results in this area — `short_chain`, `pp_dichotomy` — are
EXISTENCE results, and §44.19 already showed that turning one into the other is
where this campaign's seams live.

**So the shape of the remaining argument is:**

> take a closed serving set of MINIMAL size; the cut shows it is repeat-free
> along `PP`-chains; hence it is bounded by `mixKT C₀`.

with the one wrinkle that minimality needs a starting finite set, which the
dichotomy supplies: where the closure is infinite, a chain is infinite, and that
branch yields a KERNEL rather than externals. So the induction is simultaneous
over the two branches rather than sequential.

**Honest status.** This is a well-defined argument of a shape the campaign has
executed before (`short_chain` is exactly this, one level down), but it is NOT a
mechanical step and it is NOT written. It is the last item, and it deserves to be
attacked as its own piece of work rather than as the tail of an assembly.

### 46.27 How far the analysis actually gets (2026-08-23)

Pushing past §46.26's three failures produces two real facts and one obstruction.

**Fact 1 — demands can BECOME persistent going up, and `persistDs` stabilizes.**
`persistDs_up` (§45.5) says the persistent set only grows along an ascending
chain. It is a filter of `cl C₀`, so its length is monotone and bounded by
`|cl C₀|` — hence along an infinite chain it STABILIZES. Past the stabilization
point, a one-shot demand stays one-shot forever: if it became persistent, the set
would grow.

So the problem is confined to the tail past stabilization, where the one-shot
demands are genuinely permanent.

**Fact 2 — an infinite one-shot chain IS a kernel, after §46.** Types recur by
pigeonhole, giving `hty`; and §46's per-external `up`/`dn` means a phase's
unserved one-shot demand goes to an external ABOVE the kernel (`dnAt`), which is
exactly the case §45 could not handle and §46 fixed. So the infinite branch is
not blocked.

**The obstruction — the regress is upward, and the budget does not fall.**
Those externals above the kernel are new nodes; §46.17 puts them at the kernel's
OWN budget, so nothing decreases. Their own demands recurse, going further up,
and can produce another infinite chain, another kernel, another bank. The bank
bounds each layer (`|ws| ≤ 2·|cl C₀|`) but nothing yet bounds the NUMBER of
layers.

**So the missing ingredient is precisely a bound on the layer depth**, and the
natural candidate is the same one that bounds everything else here: types are
finite, so layers whose types repeat should be identifiable — but the layers are
stacked upward, and the cut only ever reaches upward too, so it does not
obviously apply between layers.

**Assessment, honestly.** This is no longer "wiring with a hard step in it". It
is a genuine open sub-problem of the same species the campaign has faced before
(a finiteness bound on an upward recursion), it is precisely stated, and all the
local tools are certified. What is absent is the global measure. I do not have
one, and I would rather say so than produce a fourth route that fails in a fifth
way.

### 46.28 CORRECTION: the cut DOES apply between layers (2026-08-23)

§46.27 said the layer regress is unbounded because "layers stack upward and the
cut only reaches upward too, so it does not obviously apply between layers."
**That reasoning is backwards.** The cut needs the survivor to be ABOVE the node
it replaces (§44.15) — and later layers ARE above earlier ones. Reaching upward
is exactly the condition for applying it, not an obstacle.

Concretely: the layer anchors form an ascending chain `a₀ ⊂ a₁ ⊂ a₂ ⊂ …`, so
`path_cut` applies verbatim with `u := a_{i-1}`, `v := aᵢ`, `w := aⱼ`:

```
a_{i-1} PP aᵢ,  aᵢ PP aⱼ,  mty aᵢ = mty aⱼ
  ⟹  a_{i-1} PP aⱼ  and  aⱼ carries whatever aᵢ did
```

so layers `i … j-1` can be dropped. **A repeat-free layer sequence has at most
`|typeEnum C₀|` layers**, and the layer count is bounded by the same pigeonhole
as everything else.

**What this changes.** §46.27's "the global measure is absent" was too gloomy:
the measure is the same cut, applied one level up. Both the within-chain bound
and the between-layer bound come from `path_cut`.

**What it does NOT change.** The cut gives EXISTENCE of a short layer sequence,
not a construction — so the residual difficulty is exactly the seam §44.19 named
and §46.26 hit three times, and route B's oscillation problem applies at the
layer level too. The remaining item is therefore ONE thing, not two:

> obtain a finite closed structure to minimize over; then the cut, applied both
> within chains and between layers, bounds it by `mixKT C₀`.

That is a better position than §46.27 recorded, and the correction is worth more
than the pessimism it replaces.

## 47. THE ROUTE: local-above reuse, licensed by the cut (2026-08-23)

### 47.1 Why neither a probe nor a research round

**A probe cannot reach this.** The question is whether a closure is finite —
about INFINITE structure. Finite set models cannot exhibit an infinite chain, so
a finite-model probe measures nothing, exactly as `wp100` demonstrated (§45.4).
The probe habit has a domain and this is outside it.

**A research round is not needed either**, because the standard tool is already
known not to apply: the fragment has NO finite model property (a persistent
`∃PP` tower forces an infinite chain), so filtration is unavailable — which is
why kernels exist at all. The object being bounded is a finite CERTIFICATE, not
a finite model.

### 47.2 The construction

§46.26's route C failed because it reused a GLOBAL type representative, and
`wp96` D measured that losing coverage on 8.4%. But the cut does not license
global reuse — it licenses reuse of a node that is ABOVE the one it replaces.
Localizing accordingly:

> At node `n` with a one-shot demand whose witness `w` has type `T`: if some node
> `u` ALREADY IN THE STRUCTURE AND ABOVE `n` has type `T`, reuse `u`; otherwise
> add `w`.

Both of `path_cut`'s obligations hold for the reuse:

* `n PP u` — because `u` is above `n` by construction;
* `D ∈ mty u` — because `mty u = T = mty w` and `D ∈ mty w`.

Both are exactly what `path_cut` (certified, §44.15) requires.

### 47.3 The termination measure

**The set of types realized ABOVE the current node.** Adding a node consumes a
fresh one; reuse consumes none. Types are drawn from `typeEnum C₀`, so at most
`|typeEnum C₀|` nodes are added along any upward path. Branching is bounded by
`|cl C₀|` demands per node and the horizontal depth by `mdepth C₀` — which is
`mixKT C₀`'s shape exactly.

### 47.4 Why this is better than the three failed routes

It is a CONSTRUCTION with a measure, not an existence argument — so it does not
hit the §44.19 seam. Route B's oscillation cannot occur, because reuse never
adds a node and addition strictly consumes a type.

**Honest risk.** The correctness condition is certified (`path_cut`), and the
measure is elementary. What is untested is whether "above" is tracked correctly
across the horizontal recursion, where a node added above `n` must also count as
above `n`'s predecessors. That is transitivity of the model's `PP`, so it should
hold — but "should hold" is the phrasing that has been wrong before, and it will
be checked by building rather than asserted.

### 47.5 Building it exposes a flaw in §47.2 (2026-08-23)

§47.4 said the risk was whether "above" tracks correctly across the recursion,
and that it would be checked by building rather than asserted. Building it
checked it, and the answer is worse than a tracking bug.

**The accumulator points the wrong way.** The natural construction carries a
`seen` list of types along the upward path and reuses when a witness's type is
already in it. But `seen` accumulates the types of nodes on the path from the
START to `n` — and those are **below** `n`, not above. The cut licenses reuse of
a node **above** the one it replaces. So reuse against `seen` is reuse in the
wrong direction, and is not licensed.

Restating the cut makes the problem visible: `path_cut` replaces `v` by a LATER
`w`. Using it during an upward construction would mean serving a demand with a
node that has **not yet been built**. The cut is inherently a POST-HOC
shortening, not a construction rule — which is the existence/construction seam
again, and §47.2 did not escape it after all.

**What survives.** Cross-branch reuse is genuinely available and genuinely
licensed: if `n` has demands `D₁, D₂` and `w₁`'s subtree is built first, every
node in it is above `w₁`, hence above `n`, so serving `D₂` from that subtree
satisfies both of `path_cut`'s obligations. So reuse is real — it is the
tree-recursion-with-accumulator SHAPE that is wrong, not the idea of reuse.

**What that suggests, without claiming it works.** A worklist fixpoint that
consults the whole current set (testing the `above` relation) rather than a path
accumulator. Termination would have to come from each node's above-set being
type-bounded, and I have not checked that the measure closes — the total set
grows as later additions land above earlier nodes.

**Status.** §47.2's construction is withdrawn. `mem_of_saturated` (§47.3) stands
and is certified — it is the right saturation lemma whatever the construction
turns out to be. The remaining item is unchanged in substance and now has one
more refuted route attached to it.

## 48. WHERE THE CAMPAIGN STANDS (2026-08-23)

### 48.1 What the blocker actually is

The remaining obligation is: **for a satisfiable ∀PO-free `C₀`, produce a FINITE
closed node set.** Four routes are refuted, with one common cause:

| route | fails because |
|---|---|
| A — short-chain head | the short chain's last node need not be demand-free |
| B — extend-and-cut | oscillation; no termination measure |
| C — global type quotient | `wp96` D measured 8.4% coverage loss (W2′) |
| §47.2 — path accumulator | `seen` holds nodes BELOW; the cut licenses only ABOVE |

**Common cause:** `path_cut` is a POST-HOC shortening. Every construction needs a
forward choice, and the cut cannot supply one.

**This is the fragment's own version of F6.** §44.13 said so when the node bound
was first built, and four refuted routes later that reading is confirmed: the
campaign has arrived, by a long and productive route, at a fragment-level
instance of its oldest open problem.

### 48.2 But the position is far better than F6 in the full logic

| | |
|---|---|
| local RCC5 algebra | certified (normal form, amalgamation, cross-policies) |
| the frame | `extFrameM`, axiom-free |
| the certificate | `mtkKernelsOD` + `_ok` |
| every relation half of every obligation | certified, most composition-forced |
| coverage routing | all nine branches |
| three of four routing conditions | discharged for the extraction's data |
| the cut, the dichotomy, saturation | `path_cut`, `short_chain`, `pp_dichotomy`, `mem_of_saturated` |
| both kernel directions | `KIdx ⊕ KIdxI`, data and attachment |
| step 1 of the assembly | complete |

The gap is ONE precisely-stated finiteness premise, with every ingredient
certified and the obstruction understood.

### 48.3 The blocker's EXACT shape (sharpened)

Everything carrying a **budget** is already finite: `mtk` truncation drops the
budget at every serving step, so the external closure is bounded by
`|cl C0|^mdepth(C0)` — measured in `wp94` part B, and certified as `mixKT`.

**Kernels cannot carry a budget.** A kernel is periodic, and periodicity needs
the node labels to be the FULL model type `mty` — a truncated label would differ
between periods. So a demand at a kernel node has **no fuel**, and the externals
it spawns are the unbounded part. That is §43's budget/frame tension, and
`NodeCovered` is precisely its residue.

Within that, the demand classes split cleanly:

- **persistent** vertical demands at kernel nodes → `rr_covers` (certified);
- **one-shot** vertical demands at kernel nodes → need an external ABOVE, and a
  witness above position `i` serves every occurrence below it (transitivity), so
  one witness covers a whole down-set — but a demand recurring cofinally needs
  witnesses cofinally, those witnesses ascend, `pp_dichotomy` turns them into a
  kernel, and that kernel's own one-shot demands repeat the question.

§46.28 bounds the LAYER count by the cut. What is unbounded is the external set
WITHIN a layer.

### 48.4 What to investigate next — corrected ranking

**KÖNIG IS NOT THE ANSWER** (§48.3 above corrects my first ranking). König
converts "every branch finite" into "tree finite", but obtaining "every branch
finite" IS the problem, so it is packaging, not an input. Adding a type-repeat
stop rule makes branches finite by pigeonhole, but then the stopped leaf must
reuse its same-type ancestor — and §47.5 already refuted that: the ancestor is
above in the TREE, while `path_cut` licenses reuse only of a node above in the
ORDER. König lands back on the refuted route.

Corrected order:

1. **A PERIODIC-MODEL PROBE — is the obligation even non-vacuous?**
   `wp100` asked exactly the right question (are one-shot vertical demands at
   kernel nodes possible?) and was INVALID because over FINITE models the guard
   always fails at a maximal element, so everything reads as one-shot. The fix is
   to probe over **explicitly periodic ascending models** (a repeating set-family
   with no maximal element), where the guard is meaningful. Cheap, well-defined,
   and it either kills the obligation (every kernel demand persistent ⟹ done) or
   hands back a concrete witness to design against. **This is the first thing to do.**
2. **Build step 3 (the tail).** Mechanical: `reindexMT` → `encodeMT` →
   `encodeMT_mem_codesM` → `hcompl` → `decidableSat_of_codes`. The artifact then
   states *"decidability of the ∀PO-free fragment reduces to ONE named premise,
   everything else machine-checked"* — citable, and a clean handoff. 2–3 rounds.
3. **Cold review of §43–§47.** The campaign has never had this material reviewed,
   and the project's ledger (a defect in 15 of 17) says that is overdue.
4. **Worklist fixpoint** (§47.5's survivor) — reuse consulting the whole current
   set rather than a path accumulator. Needs a termination measure.

## 49. WP101 — the blocker is 89% VACUOUS, and the residue has a shape

`wp101` (periodic ascending models over finite/cofinite subsets of ℕ — a
genuinely infinite chain with NO maximal element, satisfaction in closed form
because every residue recurs cofinally above any `i`).

**A — validity.** 54.2% of chain-node `∃PP` demands are PERSISTENT, 45.8%
one-shot. `wp100`'s 100%-one-shot reading is confirmed as a pure boundary
artifact of finite models. The probe class is sound.

**D — the decisive measurement.** Of cofinally recurring one-shot vertical
demands:

| | |
|---|---|
| served IN-KERNEL (`X` recurs on the chain) | ~~89.2%~~ **RETRACTED, F1** — see §67 |
| need an EXTERNAL | 10.8% |
| external count at windows 2p / 4p / 8p / 16p | **(1, 1, 1, 1) in every case — FLAT** |
| cases needing an unbounded/growing set | **0** |

### 49.1 Why — and this half is a THEOREM, not a measurement

For an ascending kernel `c(0) PP c(1) PP …` with `∃PP.D` present cofinally:

**Case (a) — `D` recurs on the chain.** Served in-kernel; zero externals.
(The rate formerly quoted here is RETRACTED — F1, §67.)

**Case (b) — `D` fails on the chain above some `N`.** Every witness is off-chain.
Now the transitivity fact does the work: if `c(i) PP w` then `c(j) PP c(i) PP w`
for every `j ≤ i`, so **one witness above a high occurrence serves EVERY
occurrence below it**. So case (b) costs **ONE external**, and what remains is
the occurrences above `w` — the same question one layer up, which §46.28 bounds
by the cut.

That is a bound in `C₀` alone: **one external per (layer, demand)**, layers
cut-bounded, demands `≤ |cl C₀|`.

### 49.2 What this changes

`NodeCovered` was being attacked as *"bound an arbitrary construction"*. It is
really a **dichotomy** — chain-recurrence or one-witness-plus-push-up — and the
campaign already owns both branches' machinery (`rr_covers`-style in-kernel
serving; `path_cut`/§46.28 for the push-up). The four refuted routes (§48.1) all
failed because they tried to bound a *generic* closure. This does not.

**Scope, honestly:** the model class carries finitely many side regions, so the
flat `1` has a low ceiling by construction — the *measurement* cannot exhibit
unboundedness. The load is carried by the transitivity argument in 49.1, which
is model-independent. (The in-kernel rate formerly cited here is RETRACTED —
F1, §67: it measured persistence, on a population that was 100% artifact.)

### 49.3 Next

Formalize the dichotomy: `chain_recurs ∨ (∃ w, serves-all-below ∧ residue-above)`.
Branch 1 is in-kernel serving. Branch 2 is one external plus a cut-bounded
regress. This replaces §47.5's withdrawn construction.

## 49.4 The probe's own calibration — three artifacts, one robust number

Developing `wp101` caught **three** further artifacts of `wp100`'s family, all
inside this probe:

1. side regions drawn from a small range can never sit above a **high** bounded
   segment of the chain — so part E could not *reach* the bounded branch;
2. the bounded witnesses' reach was drawn to match part D's widest window, so
   one witness covered every window by construction;
3. "cofinally recurring" was tested on a `3p` window, which admits demands that
   simply die above the sides' reach — everything then looks flat vacuously.

~~**Only the IN-KERNEL rate is stable** across all four model-class variants:
**89.2 / 90.2 / 83.5 / 91.3%**.~~ **RETRACTED — F1, §67.** The stability was
evidence of a SHARED artifact, not of robustness: none of the four variants
touched the cofinite branch of the generator, so all four carried the same
maximum region ℕ at the same ~38% frequency.
Single rates from this probe are weak evidence; the load is on the theorems.

**Method, sharpened:** `probe-before-lean-churn` needs a companion rule —
*vary the model class and keep only what survives.* A rate that moves is a
property of the generator, not of the mathematics.

## 49.5 What §49 actually certified — and the residual question

Ten theorems, `formal/POFreeLift.lean`, clean build (25,649 lines, exit 0,
0 errors / 0 warnings / 0 sorries / 0 `sorryAx`):

| theorem | content | axioms |
|---|---|---|
| `pp_witness_below` | `comp pp pp = [pp]`: a superpart of `x` is a superpart of everything under `x` | none |
| `ex_pp_serves_below` | one witness discharges `∃PP` at every node below its anchor | none |
| `oneshot_one_witness` | the witness at `c N` covers every `c j`, `j ≤ N` | none |
| `oneshot_in_kernel` | the free branch: chain recurrence serves the demand | none |
| `above_cofinal_is_above_all` | **no middle case** — above cofinally many *is* above all | none |
| `witness_bounded_or_all` | every witness serves the whole kernel or a bounded segment | classical |
| `cofinal_witness_serves_all` | the good branch, named | none |
| `finite_pool_gives_cofinal_witness` | **finite pool ⟹ one member serves the whole kernel** | classical |
| `finite_pool_serves_kernel` | the same, stated as serving | classical |
| `finite_pool_all_or_nothing` | **1 or inadequate — never 2 or 3 partial servers** | classical |

`finite_pool_gives_cofinal_witness` is a **uniformization of exactly the shape
the campaign has wanted since W2′** — pointwise serving from a finite pool
upgrades, for free, to one uniform server. Transitivity plus `recurrent_tail` is
the entire proof.

### The residual question, now single and sharp

For a cofinally recurring one-shot vertical demand at a kernel, exactly one of:

1. **chain recurrence** → served in-kernel, cost 0 (~~~90% measured~~ —
   RETRACTED, F1, §67; there is no measurement behind this branch);
2. **one cofinal external** → cost 1;
3. **neither** → *no finite external set can serve it.*

So the whole mixed quadrant now rests on one question: **can a ∀PO-free concept
FORCE case 3?** A case-3 *model* is easy to write (`a_i = {0..i}`,
`w_i = a_i ∪ {big_i}` carrying `D`, `D` nowhere on the chain and not at `ℕ`).
What is unknown is whether a concept can force *every* model to look like that.

- If **no** → the extraction always lands in case 1 or 2, and the quadrant closes.
- If **yes** → the certificate architecture is provably incomplete as shaped, and
  that is a genuine, publishable negative result about this architecture.

Either way it is now a **decidable-shaped, single** question, which is a strictly
better position than §48's "bound an arbitrary closure" with four refuted routes.

## 50. THE TOP-SERVER EXTENSION — case 3 is a placement problem

§49 reduced the mixed quadrant to one question: can a ∀PO-free concept force
case 3? The answer developed here is that **case 3 is never a consistency
failure, only a positioning one.**

### 50.1 The required type always exists

`witness_realizes_requirement` (axiom-free): the type a cofinal server needs —
every `∀PP` consequent holding at the demanding node, plus the demanded concept
— is realized by **the demand's own witness**. If `∀PP.X` holds at `c i` and
`c i PP w`, then `X` holds at `w` by the meaning of `all`; and `w` carries `D`
by choice of witness.

So nothing has to be invented. An early revision of `wp102` "measured" this at
100% over 21 samples with mean consequent-set size **0.05** — i.e. it was
confirming a tautology on empty requirements. Working out why produced the
theorem instead.

### 50.2 The server can be placed

`odTop`: adjoin a new top above a **downward-closed** set, disjoint from
nothing. The result is still an `ODStruct`, so `odNet_frame` returns composition
closure **for free** — no composition obligation is discharged by hand.

Downward-closedness is not a convenience. `wp102` Q1 measured the naive rule
(above the chain only) breaking on exactly one cell, `comp(PO,PP) = {PO,PP}`,
whenever an off-chain node sits BELOW a chain node. Closing downward repairs it:
**3121 of 3121** random ordered-disjoint structures accepted the placement.

`odTop_po`: the new top is `PO` to everything outside the closure — and
**∀PO-freeness is exactly what makes that free**, since a `PO` edge carries no
universal obligation. This is the fragment paying for itself again.

### 50.3 The one new obligation this creates — stated, not glossed

The top's label is `w`'s model type, which may contain `∀PPI.Y`. The top sits
above the whole closure, so such a universal fires DOWNWARD on every node of the
closure — including nodes not below `w` in the original model, where `Y` need
not hold.

Three ways out, in order of promise:

1. **Truncate the label.** The certificate only needs the top to carry the
   demanded `D` and the `∀PP` consequents. `mtk`-style truncation that drops
   `∀PPI` conjuncts would need a soundness argument, since labels must be
   genuine types.
2. **Choose `w` low.** Pick the witness minimising its `∀PPI` content; the
   monotonicity direction is `sat_all_ppi_down` (already certified).
3. **Make the top a kernel** whose descending obligations are served by the
   closure itself — `persistDsI`/`rr_coversI`, the certified descending half.

### 50.4 §50.3 pinned, then dissolved

`odTop_out` / `odTop_no_dr` / `odTop_nothing_above` bound the obligation to a
SINGLE universal: every edge out of the new top is `PPI` (into the closure) or
`PO` (outside it); `∀PP` and `∀DR` fire vacuously by construction and `∀PO` is
absent by hypothesis. So only `∀PPI` could bite.

And pinning it showed it **dissolves on the right route** (`top_all_ppi_automatic`).
The obligation is real if the top's label is COPIED from the witness `w` — `w`
guarantees `Y` only below itself. If instead the label is the top's own model
type in the EXTENDED model, then `∀PPI.Y ∈ mty T` says *exactly* that `Y` holds
at everything below `T`. The Hintikka clause and the obligation are the same
statement.

### 50.5 What actually remains

Not the universal. The residue is the **extension step itself**: place a region
above the closure that satisfies `D` together with the stable `∀PP` consequents.
`witness_realizes_requirement` shows that type is already realized in the model
(by `w`); what is unproved is that it can be realized *in that position*.

Tools pointing at it, all already in the project:

- `wp48` — free amalgamation of ordered-disjoint structures (certified by probe);
- `wp71` — the exact one-point connector-extension criterion;
- `odTop` + `odTop_frame` — the structural half, now certified: the placement
  keeps the frame RCC5-closed with no composition check.

So the mixed quadrant reduces to a **one-point extension lemma at the concept
level**, with the structural half done and the RCC5-local half already probed.

### 50.6 Status, honestly

The obstruction has moved from *"an unknown case 3"* to *"a one-point concept-level
extension, with the structure certified and the universal obligation dissolved"*.
That is real progress and it is **not closure**. The ledger says to presume the
extension lemma hides something; it has not been attacked yet.

## 51. THE CAP AMALGAMATION — and why the cap carries no disjointness

`odTop` adjoins ONE node above the closure. That is not enough: the new node's
label may contain `∃PP.Z` (the demanded `D` can itself be an `∃PP`), and nothing
sits above a single top. The cap must be a structure, not a point.

**`odAmalg`** (certified, `propext` only): adjoin ANY strict order above a
downward-closed set. Ordered-disjoint again, so `odAmalg_frame` supplies
composition closure with nothing checked by hand. `odTop` and **`odTower`** (the
ascending cap, now literally `odAmalg` at `(Nat, <)`) are instances — the
duplicated 70-line proof was deleted rather than kept in parallel.

### 51.1 The cap has NO internal disjointness — forced, not chosen

Two cap nodes both sit above the whole closure `U`, so `djDown` would push their
disjointness down onto `U`'s elements and make them disjoint from *themselves*.
So `amDisj` is not a simplification: **a cap is always poset-shaped**
(`PP`/`PPI`/`PO`/`EQ` only). This is the ordered-disjoint normal form telling us
what a cap can be.

Consequence: a cap node's `∃DR.Z` demand cannot be served inside the cap. It
must be served from the BASE, by a node disjoint from the **entire** closure.

### 51.2 That consequence is already certified

`cofinal_dr_all` (line ~2848, in the file since the vertical quadrant): a
cofinally-`DR` external is `DR` to the *whole* chain. This is the exact mirror of
§49's `above_cofinal_is_above_all` — **no middle case on the DR side either**, by
downward closure of disjointness instead of transitivity of the order.

So both halves of the cap's interface have their "no middle case" lemma:

| side | lemma | mechanism |
|---|---|---|
| above | `above_cofinal_is_above_all` | `comp(PP,PP) = {PP}` closes downward |
| disjoint | `cofinal_dr_all` | `djDown` closes downward |

### 51.3 What remains

The **labels**. The cap's structure is certified; what is unproved is that its
levels can be labelled so that each satisfies the stable `∀PP` consequents, the
levels round-robin the (possibly conflicting) demands, and each level's own
demands are served — `∃PP` upward inside the cap, `∃PPI` into the closure,
`∃PO` free (no `∀PO` to fire), `∃DR` from a cofinally-DR base node.

That is a labelling problem over a certified structure, which is a better
position than §50 left it in, and still not closure.

### 51.4 The cap's universals are sound — a theorem, not a rate

`wp103` measured the copied-label obligation as sound at 100%. But only **2 of
44** labels carried a `∀PPI` at all, so that rate rested on two tests. Asking
what an adversarial instance would need produced the proof instead:

**The demand is present at EVERY chain node.** So every `c j` has its own witness
`w j` carrying `∀PPI.Y`; a closure node `u` lies below *some* `c j`, hence below
`w j` by transitivity, hence receives `Y`. The witnesses' universals **blanket
the closure**.

Certified axiom-free as `cap_all_ppi_sound` and `cap_all_ppi_sound_chain`. So the
cap may copy a witness's label — **no model extension is needed for this
obligation**, which is what §50.5 had listed as the residue.

### 51.5 The fan cap — conflicting demands need no order

§51 introduced the tower for two reasons: (a) a cap node's own `∃PP` needs
something above it, and (b) several *conflicting* demands need several servers.

**(b) dissolves.** `odFan` (= `odAmalg` at the EMPTY order): two cap nodes with
no order between them are `PO`, and **`∀PO` is absent from this fragment**, so
neither constrains the other. Conflicting demands are served by an ANTICHAIN —
no ordering decision, no propagation between servers, no round-robin needed for
this reason.

This is the third distinct place ∀PO-freeness has paid: the `PO` residual to
nodes outside the closure (§50.2), the cap's mutual independence (here), and the
original absence of `mty_no_all_po` obligations.

### 51.6 What is left

Only reason (a): a cap node's own `∃PP` demand. That is the recursion — a cap
above the cap — and it is bounded layer-wise by the cut (§46.28). Everything
else about the cap is now certified: the structure (`odAmalg`/`odFan`/`odTower`
+ their frames), the placement rule (downward closure), the `∀PPI` obligation
(§51.4), the `∃DR` route (`cofinal_dr_all`), and the mutual independence of
servers (§51.5).

## 52. THE LAYER RECURSION TERMINATES — and an honest audit

`layer_recursion_terminates`: stack the caps `T 0 PP T 1 PP …`; their model types
come from `typeEnum C0`, so past any point two layers repeat, and at a repeat the
higher layer's server covers the lower one (`layer_cut`). The layer count is
bounded by `C₀` alone.

Why this works where §47.2 failed, stated precisely: `path_cut` licenses reusing
a node above in the **ORDER**. §47.2's accumulator offered a node above in the
**TREE**. **Caps are stacked in the order**, so the cut applies with nothing to
arrange.

### 52.1 AUDIT — what the cap actually discharges, and what it does not

Marking "lemma ready" (the supporting theorem is certified but **not yet applied
to cap-indexed data**) separately from "done".

| `MultiTierOk` field | edge involved | status | lemma |
|---|---|---|---|
| `frame_q` | — | **lemma ready** | `odFan_frame` / `odAmalg_frame` |
| `e_clash/nobot/and/or` | — | **lemma ready** | label is a genuine `mty` |
| `ee_all` base→cap | `PP` | **lemma ready** | `witness_realizes_requirement` |
| `ee_all` cap→base | `PPI` | **lemma ready** | `cap_all_ppi_sound` |
| `ee_all` cap↔cap | `PO` | **lemma ready** | `odFan_po` + `mty_no_all_po` |
| `ee_all` cap→outside | `PO` | **lemma ready** | `odAmalg_po` + `mty_no_all_po` |
| `ee_all` cap `∀DR` | — | **lemma ready** | vacuous: `amDisj` |
| `ek_all` / `ke_all` kernel↔cap | `PP`/`PPI` | **lemma ready** | `cap_all_ppi_sound_chain` |
| `k_ex` persistent | — | **DONE** | `rr_covers` |
| `k_ex` one-shot | — | **lemma ready** | §49 trichotomy + the cap |
| `e_ex` for the CAP's own demands | all | **OPEN** | §52 gives termination, not a construction |
| the wiring | — | **OPEN** | `β`, `elt`, `mixNodes`, the bound |

### 52.2 So what is genuinely left

Two things, and neither is the mathematics that blocked §48:

1. **`e_ex` for cap nodes.** §52 proves the layer stack terminates; it does not
   yet *build* the stack as certificate nodes with their routing conditions.
   This is the same shape as the base case, one level up.
2. **Wiring.** Extend the external index `β` with the cap, extend `elt` with the
   cap edges, extend `mixNodes` and its bound.

Everything in the "lemma ready" rows is a certified theorem waiting to be applied
to cap-indexed data — real work, but not open mathematics.

**Calibration.** The session that produced §§49–52 refuted its own headline
reading four times (`wp100`'s 100%, `wp101` D's flatness twice, `wp102` Q1's
tautology, `wp103`'s 2-of-44). The ledger's standing presumption applies: read
this audit as *"no open step identified beyond rows 11–12"*, not as *"none
exists"*.

## 53. WIRING THE CAP IN — the frame level is done

§52.1's two open rows are one task: make the cap **just another external**.
`odSeed` takes the order, the kernel attachment and the disjointness seed
abstractly, so no new frame theory is needed — the job is to extend
`(elt, up, dn, seed)` from `β` to `β ⊕ M` and re-discharge its five hypotheses.

### 53.1 The extended data and its two side conditions

`capElt` / `capUp` / `capDn` / `capSeed`: everything in `U` sits below every cap
node; cap nodes are below nothing, lie above exactly the kernels flagged by
`capOver`, and are in no seed pair (as §51.1 showed a cap must be).

Exactly two side conditions fall out of the hypothesis proofs, and both are what
§§50–51 established:

| condition | where it is needed | supplied by |
|---|---|---|
| `hUdown` — `U` downward closed under `elt` | `capElt_trans` | the placement rule, §50.2 |
| `hcov` — anything below a covered kernel is in `U` | `capElt_ud` | the cap is above the kernel's whole closure, §51 |

That the *only* two conditions to appear are the two the construction already
guarantees is the interface behaving.

### 53.2 The transfer theorem

**`odSeedCap_old`**: on old nodes the capped net is the uncapped net, **edge for
edge**. Adding a cap changes nothing below it.

So every obligation already certified for the extraction's structure carries
over unchanged, and only genuinely new edges need anything proved. Those are
four, all now certified:

| edge | value | theorem |
|---|---|---|
| external in `U` → cap | `PP` | `cap_above_U` |
| external outside `U` → cap | `PO` (unconstrained) | `cap_po_outside` |
| covered kernel → cap | `PP` | `cap_above_kernel` |
| cap → cap | `PO` (the §51.5 fan) | `cap_po_cap` |
| cap disjoint from anything | never | `cap_not_disj` |

`odSeedCap_frame` then gives the RCC5 frame with nothing checked by hand.

### 53.3 Audit update

Of §52.1's two open rows, the **frame level of the wiring is now done**. What is
left is narrower and now precisely nameable:

1. **Cap LABELS.** Attach `mty w` to each cap node and check the label-side
   obligations against the four new edges. Every needed lemma exists
   (`witness_realizes_requirement`, `cap_all_ppi_sound`,
   `cap_all_ppi_sound_chain`, `mty_no_all_po`); none is applied yet.
2. **`e_ex` for cap nodes**, with the layer stack of §52 as actual nodes.
3. **Instantiation**: choose `M`, `U`, `capOver` from the extraction's data and
   discharge `hUdown`/`hcov` concretely.

Nothing here is open mathematics. The ledger's presumption still applies: this
is *"no open step identified"*, not *"none exists"*.

## 54. CONVERGENCE CHECK (2026-08-24)

### 54.1 What is DONE — general, no side condition beyond the fragment

| quadrant | theorem | status |
|---|---|---|
| horizontal (∃DR/PO/EQ, ∀ non-PO) | `decidableSat_hfrag` | **general** |
| ascending vertical | `decidableSat_vtower` / `…G` / `…RR` | **general** |
| descending vertical | `decidableSat_vtowerRRI` | **general** |
| mixed (∃PO + ∃PP) | `decidableSat_Cmix` | **witness only** |

The **tail is not a risk**: `reindexMT`, `reindexMT_ok`, `codesM`,
`encodeMT_mem_codesM`, `encodeMT_accepts` all exist, and the whole pipeline runs
end-to-end on the witness (`mixCert_ok` → `mixTower_accepted` →
`decidableSat_Cmix`). The template is demonstrated; only the general instance is
missing.

### 54.2 What is LEFT

| # | item | size | risk |
|---|---|---|---|
| A | cap LABELS: apply the 9 "lemma ready" rows of §52.1 to cap-indexed data | large | **highest** |
| B | `e_ex` for cap nodes, with §52's layer stack as actual nodes | medium | high |
| C | instantiate `M`, `U`, `capOver`; discharge `hUdown`/`hcov` concretely | medium | medium |
| D | reindex → encode → `mix_hcompl` → `decidableSat_mix` | small | low (templated) |
| E | the fragment theorem `∀ C0, POFree C0 → Decidable (Satisfiable C0)`; check the mixed extraction subsumes the other three | small–medium | medium |

### 54.3 Are we converging? — the honest reading

**For.** The obligation narrowed strictly every round this session: *generic
closure bound* → *trichotomy* → *placement* → *labelling* → *wiring* → three
named items. **No step this session needed new mathematics** — every one reused
a piece already in the file (`recurrent_tail`, `cofinal_dr_all`, `path_cut`,
`odNet_frame`, `sat_all_pp_up`). And twice an interface was satisfied by exactly
what the construction already guaranteed (`odSeed`'s five hypotheses; the cap's
two side conditions), which is what a fitting architecture looks like.

**Against.** Items A and B are the moment obligations are first *applied* — and
this campaign's own recorded method lesson is *"write the consumer before
believing the interface; four interfaces and three parameters failed exactly
when something first used them."* The highest-risk step is still ahead. This
session also refuted its own headline reading four times, and §§43–53 are
entirely **unreviewed** while the ledger stands at a defect in 15 of 17 reviews.

**Estimate.** 2–4 sessions of this session's size (~1,000 lines, ~67
declarations) if nothing breaks; realistically **3–6** with one or two genuine
setbacks. "Fully certified" would mean one Lean theorem,
`∀ C0, POFree C0 → Decidable (Satisfiable C0)`, 0 sorries, no premise — and
still **unreviewed**, which on this project has never yet meant correct.

## 55. CORRECTION — the cap cannot go through the existing extraction consumer

Writing the consumer before believing the interface (the campaign's own method
rule) found this immediately, and it corrects §54's estimate.

### 55.1 What the consumer demands

`mtkKernelsOD` attaches labels as **model types of positioned nodes**:

```
tauE e := mtk C0 I (g e) (bud e)          g : β → α
```

and `mtkKernelsOD_of_debts` therefore carries

```
hppE : ∀ e f, elt e f → I.rho (g e) (g f) = pp ∧ …
```

For the capped data `elt := capElt elt U`, and `capElt (inl e) (inr m) = U e`.
So `hppE` demands, **for every `e` in the closure**, a model node `g' (inr m)`
with `I.rho (g e) (g' (inr m)) = pp` — a model node `PP`-above the *entire*
closure.

**That is exactly what case 3 says does not exist.** So the capped structure
cannot be fed to this consumer, and §54's item A is not "apply nine lemmas".

### 55.2 What survives, and what this actually costs

Nothing in §§49–53 is wrong; the frame algebra is sound and will be needed. What
changes is the assembly route.

| result | status after this correction |
|---|---|
| §49 trichotomy, `finite_pool_*` | **stands** — statements about the model |
| `witness_realizes_requirement`, `cap_all_ppi_sound` | **stands**, and become more central |
| `odAmalg`/`odFan`/`odTower`/`odSeedCap` + transfer | **stands** as frame algebra |
| §54 item A ("apply the lemma-ready rows") | **withdrawn as stated** |

A capped certificate must be assembled **directly against `MultiTierOk`**, with
labels as *sets* (a `mty w` used as a consistent set, not as the type of a
positioned node). That is a NEW assembly path, not a use of the existing one.

### 55.3 Is that path open, or just work?

Encouraging: the label-side obligations look dischargeable by the same blanket
arguments already certified. In particular `ee_all` on the base→cap `PP` edge
needs `X ∈ mty w` whenever `∀PP.X ∈ mtk (g e)` for `e` in the closure — and
`sat_all_pp_up` plus the chain's `∀PP`-stabilisation gives it, PROVIDED `w` is
chosen above a chain node past the stabilisation point. That is
`witness_realizes_requirement` sharpened by a choice of `w`, not new mathematics.

Still genuinely open: `e_ex` for the cap (§54 item B), where the recursion lives.

### 55.4 Revised estimate

§54 said 2–4 sessions, realistically 3–6, with items A–E as assembly. With item A
reopened as a new assembly path and item B still carrying the recursion, the
honest figure is **4–8 sessions**, and the confidence that no further wall
appears should be lower than §54 implied — this is the second time in two
sessions that an interface failed at first contact, exactly as the method note
predicts.

## 56. THE CAPPED CERTIFICATE AT THE LABEL LEVEL

§55's correction says the cap must be assembled directly against `MultiTierOk`,
which is stated entirely in terms of labels — `∀` propagation between `tauE`s,
`∃` coverage by some node's `tauE`. `multiTier_sound` builds a model FROM the
certificate and never asks where the labels came from.

### 56.1 The certificate needs no new constructor

`capped_tauE_base`, `capped_tauE_cap`, `capped_phase` are all `rfl`: the capped
certificate is literally `mtkKernelsOD` at `β ⊕ M` with the combined maps `gCap`
and `budCap`. What changes is only which consumer validates it.

### 56.2 The base→cap obligation, discharged

`cap_ee_all_pp`: a cap node's label absorbs every `∀PP` obligation of the
closure, provided the cap's witness sits above a chain node whose `∀PP` content
is MAXIMAL. A closure element `e` lies at or below some `c j`; its `∀PP.X` rises
to `c j` by `sat_all_pp_up`; maximality moves it to `c i₀`; and `c i₀ PP w`
delivers `X` at `w`.

`cap_stab_exists`: **that chain node always exists.** `recurrent_tail` gives a
point past which every occurring type recurs cofinally; pushing any `∀PP.X` up
to a recurrence shows the type there contains every `∀PP` conjunct appearing
anywhere on the chain. So the hypothesis of `cap_ee_all_pp` is never an
assumption about the model — it is a theorem about it.

That is §55.3's plan, executed: the obligation §55 identified as needing the
label level is discharged at the label level.

### 56.3 Next: the cap→base `∀PPI` obligation

The mirror direction needs `Y ∈ mtk (g e)` for every closure element whenever
`∀PPI.Y ∈ mtk (w m)`. The argument is identified and uses the kernel's
PERIODICITY, not the blanket over witnesses:

`Y` holds at everything below `w m`, which includes `c 0 … c i₀`. If `i₀` spans
a full period, that is every PHASE of the kernel — and periodicity then extends
`Y` to `c j` for ALL `j`, hence to the whole closure.

So both directions rest on the same two facts the vertical quadrant already
owns: monotone `∀PP` content with a stabilisation point, and periodic phases.

## 57. BOTH `∀` DIRECTIONS FOR THE CAP, CERTIFIED

### 57.1 cap→base needs no periodicity

`cap_ee_all_ppi`: a cap node's `∀PPI` fires downward on the closure and is
satisfied there, because everything at or below `c i₀` is `PP`-below the cap's
witness (`cap_reaches`).

§56.3 predicted this would need the kernel's periodicity. It does not — **a
kernel's phase window is FINITE**, so raising `i₀` past it puts every phase below
the witness too. `cap_stab_up` supplies the raise: maximal `∀PP` content is
preserved going up the chain, so the stabilisation point of `cap_stab_exists`
can always be moved past a phase window.

That is a simpler argument than the one §56.3 recorded, and it is the one that
compiled.

### 57.2 The cap's `MultiTierOk` rows, current state

| row | status |
|---|---|
| Hintikka fields (`e_clash/nobot/and/or`) | label is a real `mtk` — existing lemmas |
| `ee_all` base→cap (`∀PP`) | **`cap_ee_all_pp` + `cap_stab_exists`** |
| `ee_all` cap→base (`∀PPI`) | **`cap_ee_all_ppi` + `cap_reaches` + `cap_stab_up`** |
| `ee_all` cap↔cap | **CORRECTED (F3)**: `PO` only when `P`-incomparable (`cap_po_cap`); when `P`-related the `pp`/`ppi` rows apply — `capcap_ee_all_pp` / `_ppi`, §68 |
| `ee_all` cap→outside (`PO`) | `cap_po_outside` + `mty_no_all_po` |
| `∀DR` at a cap | **`cap_no_dr_edge` / `cap_no_dr_edge'`** — no `DR` edge touches a cap |
| `ek_all` / `ke_all` kernel↔cap | same two lemmas, phases inside the window |
| frame | `odSeedCap_frame` |
| **`e_ex` for cap nodes** | **the one open row** |

### 57.3 So the mixed quadrant is down to one row

⚠ **CORRECTED (cold review, F3).** As written this was an overclaim: §58.1 later
introduced the cap-internal order `P`, creating cap↔cap `pp`/`ppi` obligations
that no lemma discharged. §68 supplies them (`capcap_ee_all_pp` / `_ppi`, using
§64's `capP_rho`). With those, the sentence below now holds.

Every `∀`-propagation obligation the cap creates is now certified, in both
directions, plus the frame and the vacuities. What remains is `e_ex`: the cap's
own existential demands, served by the layer stack whose termination §52 already
proved.

Standing caveat unchanged. Two interfaces failed at first contact in the last
three sessions; `e_ex` is where a third would show up.

## 58. `e_ex` FOR CAP NODES — two gaps, one closed

Writing `e_ex` found two gaps in §53's wiring at once. This is the third
interface to fail at first contact in three sessions, and §57.3 named this row
as where a third would appear.

### 58.1 Gap 1 — no cap-internal order. CLOSED

`e_ex` at `r = pp` needs `E (inr m) (inr m') = pp`, i.e. a cap node below
another. §53 defined `capElt (inr _) _ = False`: cap nodes were below nothing, so
a cap's OWN `∃PP` demand — which §52's layer stack is supposed to serve — had no
edge to be served along.

**Fixed.** `capElt` now carries a cap-internal order `P`, threaded through
`odSeedCap` and its companions with `hPirr`/`hPtr`. New:

* `cap_pp_cap` — `P m m'` gives a `PP` edge, the layer edge §52 needs;
* `cap_po_cap` — restated: cap nodes **incomparable in `P`** are `PO`. Taking `P`
  empty recovers §51.5's antichain exactly, so the fan is the `P = ∅` instance
  of one construction rather than a separate one.

The reflection and transfer lemmas were unaffected: cap–cap pairs never appear
in reasoning about old nodes.

### 58.2 Gap 2 — no `DR` edge at a cap. OPEN, and precisely specified

`cap_no_dr_edge` proves no `DR` edge touches a cap, so an `∃DR.D` in a cap's
label cannot be served — not by an external (no seed pair) and not by the kernel
branch (same reason).

The fix is to let `capSeed` carry cap↔base pairs `dseed : M → β → Prop`. Doing so
**breaks the transfer theorem**, and correctly: if `e ∈ U` and `dseed m f`, then
`e` is below the cap and the cap is disjoint from `f`, so `djDown` makes `e`
disjoint from `f` — a base-level `DR` edge the uncapped structure never declared.

So the extension needs a side condition, and it is exactly §51.2's:

```
hdbase : ∀ m f, dseed m f → ∀ e, U e → seed (Sum.inl e) (Sum.inl f)
```

— **the cap's `DR` partner must already be seed-disjoint from the entire
closure**, which is what `cofinal_dr_all` supplies on the model side. With
`hdbase` the transfer theorem survives, because the cap declares no base
disjointness that was not already there.

Work required: `capSeed` + `dseed`, reworked `capSeed_sym` / `capSeed_sep` /
`capSeed_old`, and `odSeedCap_old`'s disjointness direction routed through
`hdbase`. All mechanical; none of it is open mathematics.

**Not attempted in this session** — the half-applied refactor was reverted so the
artifact stays green (26,888 lines, 0 errors / 0 warnings / 0 sorries /
0 `sorryAx`) rather than left mid-surgery.

### 58.3 State of the open row

| `e_ex` case at a cap | status |
|---|---|
| `r = eq` | `mtk_ex_eq` + `odNet_self` — as for base nodes |
| `r = pp` | **closed** — `cap_pp_cap` (§58.1) |
| `r = ppi` | into the closure; `cap_reaches` gives the edge |
| `r = po` | the residual; `cap_po_outside` / `cap_po_cap` |
| `r = dr` | **open** — §58.2, specified above |

## 59. WHERE WE ARE, AND THE ROUTES FORWARD

### 59.1 Position

| | |
|---|---|
| horizontal / ascending / descending quadrants | **general, done** |
| mixed: frame, transfer, both `∀` directions (incl. cap↔cap, §68 — F3), `e_ex` at `eq`/`pp`/`ppi`/`po` | **done** |
| mixed: `e_ex` at `dr` | open, §58.2, fully specified |
| mixed: assemble `MultiTierOk`, instantiate, tail | not started |

### 59.2 A design insight that shrinks the remaining work

**Cap labels do not have to be full model types.** `MultiTierOk`'s obligations
are all of the form *"if `X ∈ tauE e` then …"*. A SMALLER label carries FEWER
obligations — `e_ex` fires on fewer existentials, `ee_all` on fewer universals —
while `e_clash`/`e_nobot` stay free (any subset of a consistent type is
consistent) and `e_and`/`e_or` hold as long as the label is closed under
decomposition.

So a cap node should carry not `mtk (w m)` but the **smallest
decomposition-closed subset of `mtk (w m)` containing `D` and the stable `∀PP`
consequents**. Consistency is inherited; Hintikka closure is by construction.

Consequence for §58.2: `∃DR` at a cap arises **only when the demanded concept or
a `∀PP` consequent actually forces it**, not merely because the witness happened
to have a disjoint neighbour. The gap does not disappear — it stops being
generic.

This also revisits §55: the label-level route is not just *available*, it is
strictly *better* than reading types off positioned nodes.

### 59.3 Routes

1. **Push through.** §58.2 (`dseed`/`hdbase`, mechanical) → assemble
   `MultiTierOk` → instantiate → tail → fragment theorem. Estimate 4–8 sessions;
   steps 3–4 are where interfaces get applied, and three of three such steps have
   found a gap.
2. **Land the tail first, gap as a named premise.** Do the tail now so the
   artifact states *"the ∀PO-free fragment is decidable modulo ONE named
   premise"* — citable, honest, a clean handoff, and it holds whatever happens to
   the remaining gaps. 1–2 sessions. Recommended at §48 and still not done.
3. **Cold review of §§43–59.** Never reviewed; the ledger stands at a defect in
   15 of 17. Reviewing before more building could save sessions or reshape them.
4. **Adopt §59.2 first**, then 1. Minimal labels reduce every remaining
   obligation, so the assembly gets easier rather than harder.

**Recommendation: 4, then 2, then 3.** Minimal labels are cheap and shrink the
work; the tail then locks in a citable position regardless; and a cold review is
worth most once there is a complete statement to attack.

## 60. ROUTES 4 AND 2, DONE

### 60.1 Route 4 — sub-labels (§59.2 made precise)

`SubLabel C0 I x L` = a decomposition-closed subset of a model type. Certified:

* `subLabel_mty` / `subLabel_mtk` — the existing labels are instances, so the
  notion is never vacuous and `mty` is the MAXIMAL choice;
* `subLabel_clash` / `subLabel_nobot` — consistency is **inherited**, nothing to
  check per label;
* `subLabel_sat` — everything in a sub-label is satisfied at the node, so the
  `∀`-propagation lemmas of §§56–57 fire on sub-labels unchanged.

And the interval theorem: `cap_required_in_mty` / `cap_ppi_required_in_mty` —
**everything a cap's label is required to contain already lies inside its
witness's model type**. So a valid cap label always exists, and minimality is a
CHOICE INSIDE A KNOWN INTERVAL rather than a construction problem.

What route 4 does *not* deliver: the minimal label itself. That is deliberate —
it is a choice, and deferring it costs nothing while the interval is certified.

### 60.2 Route 2 — the fragment's decision pipeline

**`decidableSat_pofree (C0) (h : MixedCompleteness C0) : Decidable (Satisfiable C0)`**
— axioms `propext`, `Quot.sound` only, **no `Classical.choice`**: a genuinely
computable decision procedure modulo one named premise.

```
MixedCompleteness C0 :=
  Satisfiable C0 → ∃ p ∈ codesM C0 (mixKT C0) (mixKT C0) (mixKT C0),
    (p.1).mtAcceptB p.2 C0 = true
```

* soundness (`mtAcceptB_sound`) is **unconditional**;
* the enumeration is fixed and computed from `C₀` alone;
* `mixedCompleteness_of_code` — exhibiting ONE accepted code discharges it, so
  the premise demands a certificate and is **not oracle-inhabitable** by a bare
  `Satisfiable` proof (the failure mode the 15th review found in round 26);
* `mixedCompleteness_of_unsat` — vacuous for unsatisfiable inputs, a check that
  the definition is not malformed.

**The position is now citable:** *the ∀PO-free fragment's decision pipeline is
machine-checked end to end, with completeness reduced to one named statement* —
and the gap's shape is typechecked rather than asserted in prose. That is what
§48 recommended and what §54–§55's estimate was really about.

### 60.3 Remaining, unchanged

`MixedCompleteness` is discharged by the general mixed extraction: §58.2's `dseed`
work, assembling `MultiTierOk`, instantiating, reindexing, encoding. Route 3 (a
cold review of §§43–60) is now worth more than before, because there is a
complete statement to attack.

## 61. §58.2 IMPLEMENTED — the cap's `DR` edge

`capSeed` now carries `dseed : M → β → Prop`, the cap↔base `DR` pairs, with two
side conditions that fall out of the proofs:

| condition | needed by | meaning |
|---|---|---|
| `hdsep` | `capSeed_sep` | nothing lies below both a cap and its `DR` partner |
| `hdbase` | `odSeedCap_old` | anything old below the cap is ALREADY seed-disjoint from the partner |

`hdbase` is not a technicality. Without it the cap would create base-level
disjointness the uncapped structure never declared, and the transfer theorem
would be **false** — `djDown` forces it semantically, and `cofinal_dr_all`
supplies it on the model side. §51.2 predicted exactly this condition.

### 61.1 What changed

* **`cap_dr_edge`** — a declared cap↔base pair really is a `DR` edge. This is the
  point: `∃DR` at a cap is now servable, from the base, as §51.2 said it must be.
* **`cap_above_is_cap`** (new, `propext` only) — anything above a cap node is a
  cap node. Cap nodes are below no base and no kernel.
* **`cap_disj_cap_false`** — §51.1's forced fact is now a theorem about the wired
  structure: two caps are never disjoint, because anything above a cap is a cap
  and the seed relates no two caps.
* **`capSeed_old`** restated as a disjunction (old pair, or a `dseed` pair).
* **`cap_not_disj` and `cap_no_dr_edge` are RETIRED** — both are now false, by
  design. A cap IS disjoint from its `DR` partner.
* **`cap_po_outside` weakened honestly**: with partners in play, "outside the
  closure" no longer implies `PO`, so the lemma takes the non-disjointness as a
  hypothesis. Taking `dseed` empty recovers the old statement.

### 61.2 §58.3's table, updated

| `e_ex` case at a cap | status |
|---|---|
| `r = eq` | `mtk_ex_eq` + `odNet_self` |
| `r = pp` | `cap_pp_cap` — the layer edge |
| `r = ppi` | `cap_reaches` |
| `r = po` | `cap_po_outside` / `cap_po_cap` |
| `r = dr` | **closed at the frame level** — `cap_dr_edge` |

All five relation cases now have their edge. What remains for `e_ex` is not a
missing edge but the **routing**: showing the extraction's data supplies a target
for each demand. That is the assembly, and it is where §55's lesson applies —
these edges are an interface, and it has not yet been consumed.

Build: 27,101 lines, 1,377 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 62. `e_ex` FOR CAP NODES — the routing consumer, and it HELD

`cap_he_ex`: five routing conditions, one per relation, each saying the model
witness for a cap's demand is matched by a certificate node carrying the demanded
concept. Given them, the `e_ex` disjunction follows from the edge lemmas:

| relation | routed by |
|---|---|
| `eq` | `odNet_self` — the cap serves itself |
| `dr` | `cap_dr_edge` — §61's new edge |
| `pp` | `cap_pp_cap` — §58.1's layer edge |
| `ppi` | `cap_ppi_U` (into the closure) or `cap_above_kernel` (the kernel branch) |
| `po` | `cap_po_cap` (a sibling) or `cap_po_out'` (outside the closure) |

Written **before** the extraction supplies the conditions, per the method rule.

### 62.1 The fourth interface-consumption, and the first that held

Three of the last three such moments found a gap:

| moment | outcome |
|---|---|
| §55 — feed the cap to `mtkKernelsOD_of_debts` | **failed** — demands model-realized nodes |
| §58 — write `e_ex`, gap 1 | **failed** — no cap-internal order |
| §58 — write `e_ex`, gap 2 | **failed** — no `DR` edge at a cap |
| §62 — write the routing consumer | **held** — all five cases routed cleanly |

That is worth recording as evidence, not as reassurance: the three failures were
all about MISSING EDGES, and §§58–61 added exactly those edges. The consumer
holding is what a repaired interface should look like. It is not evidence about
the conditions themselves, which the extraction has still to supply.

Two small edges were added while writing it — `cap_ppi_U` and `cap_po_out'`, the
reverse orientations of `cap_above_U` and `cap_po_outside`. Both one-liners.

Also `gCap_eq` / `budCap_eq`: the §56 certificate's maps ARE `Sum.elim`, so the
routing consumer (stated with `Sum.elim`, being earlier in the file) and the
certificate are literally the same object.

### 62.2 What is left for the mixed quadrant

1. **Supply the five routing conditions** from the extraction's data — the model
   witness for each cap demand, matched to a certificate node. This is where
   §49's trichotomy and §§56–57's `∀` machinery get consumed.
2. Assemble `MultiTierOk` for the capped certificate (every row now has its
   lemma; `e_ex` at caps has `cap_he_ex`).
3. Instantiate `M`, `U`, `P`, `capOver`, `dseed`, `w`, `cbud`; discharge
   `hUdown`, `hcov`, `hPirr`, `hPtr`, `hdsep`, `hdbase`.
4. Reindex → encode → discharge `MixedCompleteness`.

Build: 27,180 lines, 1,382 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 63. SUPPLYING THE ROUTING CONDITIONS — the structural finding

### 63.1 A cap needs no new closure construction

`mixNodes` already follows EVERY demand — `ppNodes` takes the `∃PP`/`∃PPI`
witnesses, the horizontal recursion takes the rest. So a cap's own node set is
`mixNodes` rooted at the cap's witness, with:

* the same size bound — `capNodes_length_le` is `mixNodes_length_le`;
* the same coverage — `capNodes_H_covers` is `mtkNodesH_covers`;
* the same index shape — `CapIdx` is `EIdx` at a different root, so the encoder
  and the `mixKT` bound consume it unchanged.

This is worth stating because §§50–62 kept treating the cap as a new kind of
object. Structurally it is not: **a cap is an external whose root happens to sit
above a kernel.** All the machinery built for `β` applies to it verbatim.

### 63.2 `rEQ` is free

`cap_rEQ`: strong `EQ` is identity, so a cap's `∃EQ` demand is served by the cap
itself — `mtk_ex_eq`, exactly as for base externals. One of five conditions
discharged outright.

### 63.3 What the remaining four actually need

The model-side half is already certified: `capNodes_H_covers` gives a witness
INSIDE the closure carrying the demanded concept, with the MODEL relation, for
every horizontal demand; `ppNodes` does the same vertically.

What is not free is matching that to the **DECLARED** relation:

| condition | model side | declared side, still to supply |
|---|---|---|
| `rDR` | `capNodes_H_covers` at `dr` | `dseed m f` for the witness, with `hdbase` |
| `rPO` | `capNodes_H_covers` at `po` | `¬ U f` and non-disjointness |
| `rPP` | `ppNodes` at `pp` | `P m m'` — the layer order on the cap index |
| `rPPI` | `ppNodes` at `ppi` | `U e`, or a covered kernel phase |

This is §43's read-off-versus-declared tension in its final form. The campaign's
standing answer — keep `elt`/`seed` abstract, because reading off breaks the
budgets (`wp96` A: 4.1%) — applies here too: `P`, `U` and `dseed` must be
DECLARED and the conditions proved, not read off the model.

That is the remaining work for the mixed quadrant, and it is now four named
implications rather than an open construction.

Build: 27,238 lines, exit 0, 0 errors / 0 warnings / 0 sorries / 0 `sorryAx`.

## 64. `rPP` DISCHARGED — two of five routing conditions supplied

### 64.1 The cap's layer order, declared not read off

`capP m m' := tcl stepAll m m'` — the transitive closure of the extraction's OWN
vertical step, which is exactly the declaration the base uses for `elt`, and for
the same reason: reading the model's `PP` off directly breaks the budgets (§43,
`wp96` A at 4.1%).

`capP_rho`: every `capP` step is a real model `PP` edge (`tcl_sub_pp`), so the
layer stack genuinely ascends and §52's cut applies to it.

### 64.2 `rPP` discharged

`cap_rPP`: a cap's `∃PP` demand is served by its own witness, which

* lies in the cap's closure — `ppWitness_mem` (new: the `∃PP` witness is in
  `ppNodes` at one more fuel), lifted through `mixNodes`;
* is `capP`-above it **by construction** — a single `tcl.base` step.

So §52's layer edge is now supplied, not just declared possible. Two small
lemmas were needed and did not exist: `ppWitness_mem` and `ppiWitness_mem`.

### 64.3 Routing conditions: 2 of 5

| condition | status |
|---|---|
| `rEQ` | **`cap_rEQ`** — free, strong `EQ` is identity |
| `rPP` | **`cap_rPP`** — §64.2 |
| `rPPI` | open — needs `U e`, or a covered kernel phase |
| `rDR` | open — needs `dseed m f` with `hdbase` |
| `rPO` | open — needs `¬ U f` and non-disjointness |

The three remaining all turn on the same thing: **`U` and `dseed` are the frame
data still to be declared.** `P` is now declared (`capP`); `U` and `dseed` are
not. Once they are, the three conditions are membership facts about the cap's
closure — the model half of which `capNodes_H_covers` and `ppNodes` already give.

Build: 27,287 lines, exit 0, 0 errors / 0 warnings / 0 sorries / 0 `sorryAx`.

## 65. `U` AND `dseed`, DECLARED — and the side conditions come out FREE

The last two pieces of frame data, declared so that their side conditions fall
out. That they DO fall out is the test of a right declaration.

### 65.1 `U`

```
capU elt up capOver e := ∃ f, leE elt e f ∧ ∃ k, capOver k = true ∧ up k f = true
```

— the downward closure (under `elt`) of the externals below a covered kernel.
Taking the closure EXPLICITLY is what makes it work:

* `capU_down` (`hUdown`) — **axiom-free**, one `lt_leE`;
* `capU_cov` (`hcov`) — **axiom-free**, reflexivity.

### 65.2 `dseed`

```
capDseed … m f := ∀ z : β ⊕ κ, mixLe … (embC z) (cap m) → seed z (Sum.inl f)
```

— `f` is a `DR` partner of cap `m` exactly when it is ALREADY seed-disjoint from
everything old below the cap. This turns §51.2's *condition* into the
*definition*:

* `capDseed_hdbase` — **axiom-free**, it IS the definition;
* `capDseed_hdsep` — two lines from the base's own `hsep`: anything below both
  the cap and `f` would be an old node seed-disjoint from `f` while also `≤ f`.

All four of `odSeedCap`'s cap-side hypotheses are now discharged by
construction. Three are axiom-free.

### 65.3 An interface gap found by supplying, not by writing

`cap_he_ex`'s `rPPI` offered two options — a closure external, or a kernel phase.
Trying to supply it showed a third is available and sometimes necessary: **a
LOWER CAP**. A cap is `PPI` to any cap beneath it in the layer order
(`cap_ppi_cap`, `odNet_gt` on `P m' m`).

Widening a hypothesis is a strict improvement — the consumer now demands less —
but it is worth recording that §62's consumer, which "held", was still missing an
option. The method rule catches missing EDGES when you write the consumer; it
catches missing OPTIONS only when you try to supply it.

### 65.4 Routing conditions: 2 of 5, with the third now nearly free

| condition | status |
|---|---|
| `rEQ` | ✓ `cap_rEQ` |
| `rPP` | ✓ `cap_rPP` |
| `rPPI` | model half certified; three declared options now available |
| `rPO` | needs `¬ capU f` and non-disjointness |
| `rDR` | **the substantive one** — needs the BASE's `seed` to already declare disjointness from everything below the cap. That is a condition on `seedMix` (§44), not on the cap. |

Build: 27,365 lines, exit 0, 0 errors / 0 warnings / 0 sorries / 0 `sorryAx`.

## 66. `capDseed` WEAKENED TO THE DOWNWARD CLOSURE — found by supplying `rDR`

### 66.1 What supplying `rDR` showed

The base's seed is `seedMix nd kdr`, whose external block is **`sAdjK`**: one
node is the other's `∃DR` witness. That is a narrow STEP relation — as it must
be, since declaring more is the read-off problem §43 refuted.

§65's `capDseed` demanded `seed z (Sum.inl f)` for **every** old `z` below the
cap. Against a step relation that is unachievable: `sAdjK` relates direct witness
pairs, not everything below a cap.

### 66.2 The fix was already in the architecture

`odSeed`'s disjointness is the **downward closure** of the seed:

```
disj x y := ∃ x₀ y₀, mixLe x x₀ ∧ mixLe y y₀ ∧ seed x₀ y₀
```

So `capDseed` should demand `disj z (Sum.inl f)`, not `seed z (Sum.inl f)` —
strictly weaker, and it is what the base's disjointness actually means. §43's
`odSeed` design (disjointness as a downward closure, which made `djDown` free)
pays a second time here.

Both side conditions survive the weakening:

* `capDseed_hdbase` — still **axiom-free**, still the definition;
* `capDseed_hdsep` — now via `djIrr` / `ltNotDj` (which `odSeed` derives from
  `hsep`) instead of `hsep` directly.

And `odSeedCap_old` still goes through: from `disj a (Sum.inl f)` and
`mixLe b (Sum.inl f)`, `mixLe_trans` gives `disj a b`.

### 66.3 Method note

This is the second thing found by SUPPLYING rather than writing a consumer
(§65.3 was the first). Both were mis-specifications on my side that a consumer
typechecks around: §62's `cap_he_ex` accepted an `rPPI` that was too narrow, and
§65's `capDseed` stated a condition too strong to hold. Neither is caught by
writing the consumer — only by trying to discharge it.

**Sharpened rule: write the consumer to find missing EDGES; supply the
conditions to find wrong STRENGTHS.**

Build: 27,385 lines, 1,400 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 67. THE COLD REVIEW OF §§43–61 — findings and corrections

The packet went out at §61; the report is
`papers/cold_review_mixed_quadrant/referee_report.zip`. The referee rebuilt the
artifact independently (clean, 537 `#print axioms` lines, no `sorryAx`), verified
`decidableSat_pofree`'s axiom profile, and re-derived the RCC5 composition and
converse tables from finite-set semantics (0/25 mismatches). **Three findings.
All three are accepted. None touches soundness.**

### 67.1 F1 — `wp101`'s in-kernel rate is retracted

`build_model`'s cofinite branch draws `Reg(True, rng.sample(range(6), rng.randint(0,3)))`,
and `randint(0,3) = 0` with probability ¼ yields `Reg(True, ∅)` = **ℕ, the whole
universe** — a region above every chain node with nothing above it. That is
`wp100`'s maximal element, reintroduced into the class built to escape it.

Reproduced locally (`rev2`, `rev3`):

| | |
|---|---|
| P(ℕ among the sides) | 37.8% |
| part D population drawn from ℕ-models | **173 / 173 = 100%** |
| part D population with ℕ-models refused | **0** |
| of the 173, still one-shot once ℕ is deleted | **0** |

So every case part D counted was one-shot *only* because ℕ sat on top; delete ℕ
and all 173 are persistent — which is exactly why "`X` recurs on the chain" and
why they scored in-kernel. **The 91.3% measured persistence.**

And the reasoning I built on it was backwards: §49.4 argued that stability across
four model-class variants was evidence of robustness. **None of the four variants
touched the cofinite branch**, so all four carried the same maximum at the same
frequency. Stability across variants was evidence of a SHARED ARTIFACT — stable
for the same reason `wp100`'s 100% was stable.

Also confirmed: `_stab = 11` is wrong for the class, since the bounded-segment
generator draws `M ∈ [stab+1, stab+5p]` by design. **295/300** models have a
side/chain relation still changing above index 11, highest observed 65 — so the
"exact, boundary-free" closed form is evaluated inside the unstable zone.

**Corrections made:** every quoted rate struck in place (§49.1, §49.2, §49.4,
§49.5). The self-correction count goes from four artifacts to **six**.

### 67.2 F2 — §51.1's "forced, not chosen" was false

The `djDown` argument establishes **no cap↔cap `DR`**, and nothing more. §51.1
generalised it to every edge at a cap, and `amDisj`/`capSeed` implemented the
general version via a catch-all — which is what made `∃DR` at a cap unservable.
So §58.2's gap was **self-inflicted**.

The referee's `odAmalgDR` (verified locally: compiles, **no axioms**) generalises
`odAmalg` with a cap↔base disjointness and stays an `ODStruct`; `witnessStruct`
is a concrete three-element instance where a cap is `PP`-above a downward-closed
`U` **and** `DR` to a base node, with `witness_frame : Frame (odNet …)`. Its side
condition `hBU` is literally §58.2's `hdbase`.

**Corrections made:** the `amLt` docstring rewritten to claim only cap↔cap and to
record that the generalisation is false; `amDisj` acknowledged as a
simplification; `cap_no_dr_edge` noted as a theorem about `odSeedCap`, not caps.

### 67.3 F3 — §58.1's fix opened a row §57.2 still called vacuous

Giving `capElt` the order `P` created `ee_all` obligations at `pp` and `ppi`
between caps. No lemma discharged them, and §57.2's table still recorded that row
as the `PO` case — correct for §51.5's antichain, stale for `P ≠ ∅`. §57.3 and
§59.1's "both `∀` directions done" were overclaims as written.

The referee also named the missing side condition
(`hPmodel : P m m' → I.rho (w m) (w m') = pp`) and gave a falsifier without it.
**§64's `capP_rho` is exactly that condition** — it postdates the reviewed
snapshot. Given it, §68 closes both rows in one line each.

### 67.4 F4/F5/F6 — accepted, smaller

* `mixedCompleteness_of_code` is `id`; its docstring restated as documentation.
* `finite_pool_gives_cofinal_witness`'s gloss ("not a hypothesis about models")
  was a category slip — trimmed.
* `odSeedCap_old`'s "every obligation carries over" → "every obligation on
  old×old edges".
* Status tables corrected (§57.2, §57.3, §59.1).

### 67.5 What the referee confirmed

Soundness unconditional; `MixedCompleteness` the right premise and **not**
oracle-inhabitable; `codesM`/`mixKT` genuinely `C₀`-computed (corroborated by
`decidableSat_pofree` excluding `Classical.choice`); the composition table
correct; **`odSeedCap_old` correct, read line by line**; and §49's ten theorems
correct — *"after F1, they are the only part carrying it."*

### 67.6 Ledger

Eighteen reviews, a defect or overclaim in sixteen. This one found a probe whose
headline was 100% artifact, a false structural argument with a machine-checked
counter-witness, and a stale status table — in a development whose author had
already recorded four self-corrections and believed the remaining risk was
elsewhere.

## 69. ROUTE B EXECUTED — case 3 IS reachable, and the artifact family is diagnosed

### 69.1 The general diagnosis behind all six probe artifacts

`wp100`, `wp101` and `wp104`'s first cut all reported ~100% one-shot. They share
one cause, and stating it generally is the main result of this round:

> **A finite set of regions above the chain always contains a MAXIMAL element; a
> maximal element satisfies no `∃PP.X`; so every chain node beneath one fails
> `∀PP.∃PP.D` VACUOUSLY.**

* `wp100` — finite model: the model's top is maximal.
* `wp101` — `Reg(True, ∅)` = ℕ drawn as a side (cold review F1): ℕ is maximal.
* `wp104` — refusing the top is **not enough**: measured **98.8%** of top-free
  models still have a *maximal side above the chain*.

The infinite chain escapes the problem; a finite side set cannot. This is why
three successive classes could not measure persistence at all.

### 69.2 What a class must satisfy to reach the case-3 question

Arrived at by three failures, and now checked per-model in `wp105` part R:

| condition | without it |
|---|---|
| no maximal element above the chain | 100% one-shot; persistence unmeasurable |
| a cofinal server family | branch 2 unrepresentable |
| bounded-reach regions **above** the chain | **branch 3 unrepresentable** |

`wp105` supplies all three: an ascending kernel chain `a_i`, an ascending server
chain `s_j` above all of it, a bounded-reach family `b_M` (above `a_i` exactly
for `i ≤ M`, and below every server so never maximal), and low sides never above
the chain. Regions are eventually-periodic subsets of ℕ — `(T, X)` with
`n ∈ R ⟺ (n mod P ∈ T) XOR (n ∈ X)`.

A fourth artifact was caught during construction: truncating the server chain at
the evaluation window `hi` recreates a maximal element (`s_{hi-1}`), so both
chains' `∃PP`/`∀PP` had to be closed by PERIODICITY rather than by a bounded
search.

### 69.3 The answer

With all three conditions holding (audit passes, 400/400 on each):

| | |
|---|---|
| persistent / one-shot | **77.5% / 22.5%** — the first meaningful split any class here has produced |
| branch 1, in-kernel | 89.7% |
| branch 2, cofinal server | 0.0% — *test-ordering, not structural*: branch 1 is tested first, so a demand served both on-chain and by a server counts as branch 1 |
| **branch 3, neither** | **10.3%** |

**Case 3 is reachable.** So the cap machinery of §§50–68 is NEEDED, not
optional — the question route B was run to settle. The alternative outcome
(branch 3 empty, mixed quadrant closing on branches 1–2) is refuted for this
class.

### 69.4 Honest scope

These are rates over one generator, and this project's record on generator-borne
rates is six artifacts in six attempts. What should be relied on is the
**structural** part: §69.1's diagnosis, §69.2's three conditions, and the
**existence** of branch-3 instances — the last of which is a witness question,
not a rate question, and 19 witnesses is 19 more than zero.

## 70. ROUTE C — `odAmalgDR` adopted

The cold reviewer's counter-witness to §51.1 (F2) is now part of the artifact,
attributed, adopted verbatim apart from a header. `odAmalgDR` depends on **no
axioms**.

### 70.1 What it gives

`odAmalg` generalised with a cap↔base disjointness `B : M → N → Prop`, still an
`ODStruct` — so `odAmalgDR_frame` gets composition closure free, exactly as
before. `odAmalgDR_dr` is the cap's `DR` edge; `odAmalgDR_pp` its `PP` edge to
the closure. `B = fun _ _ => False` recovers `odAmalg`, so nothing is lost.

Its four side conditions isolate what §61 discovered piecemeal:

| | |
|---|---|
| `hBnotU` | a cap is not disjoint from anything it is above |
| `hBdown` | `B` downward closed in the base |
| `hBP` | `B` downward closed along the cap order `P` |
| `hBU` | the partner is base-disjoint from the WHOLE closure — **literally §58.2's `hdbase`** |

`hBP` is the one §61 did not have, and it is needed precisely because §58.1 gave
the cap an internal order — the same interaction F3 found in the `∀` rows.

### 70.2 Relation to §61's `capSeed`/`dseed`

They are complementary, not redundant. `odAmalgDR` is the ABSTRACT cap structure
and is cleaner: disjointness lives in the `ODStruct` rather than in a seed that
must then be closed downward. `odSeedCap` is the WIRED one — it is the structure
whose order and seed are the extraction's `elt`/`up`/`dn`/`seed`.

Rebuilding `odSeedCap` on `odAmalgDR`'s `B` instead of `capSeed`'s `dseed` would
simplify §§61–66, but it is optional work and is recorded here as such rather
than done.

### 70.3 Routes B and C are complete

* **B** (§69) — case 3 is reachable, so the cap machinery is needed.
* **C** (§70) — the reviewer's structural half adopted.
* **A** — the assembly, now justified rather than assumed, is next.

Build: 27,660 lines, exit 0, 0 errors / 0 warnings / 0 sorries / 0 `sorryAx`.

## 71. ROUTE A — four of five routing conditions, and what `rDR` reveals

### 71.1 `rPPI` and `rPO` discharged

Both go the way `rPP` did, from the declared order `capP = tcl stepAll`:

* **`cap_rPPI`** — the `∃PPI` witness lies in the cap's closure
  (`ppiWitness_mem`) and is `capP`-BELOW it by construction: `stepAll f m` holds
  via its `ppiStep` disjunct, so one `tcl.base` step gives `capP f m`.
* **`cap_rPO`** — the `∃PO` witness lies in the closure (`mtkWitness_mem_mix`,
  new) and is `capP`-INCOMPARABLE to the cap, because every `capP` step is a
  model `PP` edge (`capP_rho`) while this one is `PO`. So the declared relation
  is `PO`, which in this fragment carries no obligation at all.

| condition | status |
|---|---|
| `rEQ` | ✓ `cap_rEQ` |
| `rPP` | ✓ `cap_rPP` |
| `rPPI` | ✓ `cap_rPPI` |
| `rPO` | ✓ `cap_rPO` |
| `rDR` | see below |

### 71.2 `rDR` says the cap should not be a separate index at all

Supplying `rDR` runs into this. Declaring `B m x := ∀ u, U u → S.disj x u` makes
**all four** of `odAmalgDR`'s side conditions free (`hBnotU` from `djIrr`,
`hBdown` from `djDown`, `hBP` because `B` ignores `m`, `hBU` by definition) — the
same trick that worked for `capU` and `capDseed`.

What is then required is base-level disjointness between the cap's `DR` witness
and every closure element. In the base, `disj` is the downward closure of
`seedMix`, so it would follow from **one** seed pair: `sAdjK (w m) (witness)` —
the cap's own `∃DR` witness edge — carried down to every `u ≤ w m`.

**But `w m` is not a base index, so `sAdjK` does not apply to it.** The seed pair
would have to be the cap↔base block we are trying to establish. Circular.

The way out is §63's finding, taken further than §63 took it: *a cap is an
external whose root happens to sit above a kernel.* If the cap's closure nodes
simply JOIN `β`, then `w m` and its witness are base nodes, `sAdjK` applies, and
`disj u witness` follows from the downward closure with nothing new declared.
What distinguishes a cap is then only its POSITION, which `up`/`dn` already
express.

### 71.3 Consequence, recorded not acted on

If that is right, the separate cap index — and with it `odSeedCap`, `capElt`,
`capUp`, `capDn`, `capSeed`, `odAmalgDR` as *applied to the extraction* — is
machinery the assembly does not need. `odAmalgDR` remains valuable as the
abstract statement that a cap MAY carry base disjointness (§70, and it refutes
§51.1), but the wired construction may be far smaller than §§53–66 assumed.

This is a restructure, not an increment, so it is recorded here rather than
started. The four discharged conditions (§71.1) are unaffected either way — they
are statements about `capNodes` and `capP`, both of which survive the merge.

Build: 27,720 lines, 1,413 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 72. THE MERGE — caps live in `β`, and all five routing conditions close

§71.2's finding, executed.

### 72.1 `rDR` needed nothing new

```lean
theorem cap_rDR_merged … (hup : up k u = true) (hdn : dn k w = true)
    (hs : sAdjK (nd w) (nd f)) :
    ∃ x₀ y₀, mixLe … (Sum.inl u) x₀ ∧ mixLe … (Sum.inl f) y₀ ∧ seedMix nd kdr x₀ y₀ :=
  ⟨Sum.inl w, Sum.inl f, Or.inr (tcl.base (Or.inr ⟨k, hup, hdn⟩)), Or.inl rfl, hs⟩
```

One term. Three existing pieces do the work:

* **`mixStep`'s own `up`/`dn` clause** — `up k u ∧ dn k w → mixStep u w`, so
  everything below the kernel is below the cap, in one `tcl.base`;
* **`sAdjK`** — now applies to the cap, because the cap is a base node;
* **`odSeed`'s downward closure** — carries that ONE seed pair to every node
  below the cap.

`cap_rDR_edge` puts it in the frame's terms. The condition that circled back on
itself in §71.2 is discharged.

**All five routing conditions are now done:** `cap_rEQ`, `cap_rPP`, `cap_rPPI`,
`cap_rPO`, `cap_rDR_merged`.

### 72.2 §§63–71 survive the restructure

`stepAll_to_elt` and `updn_to_elt`: the cap order used by §§64–71
(`capP = tcl stepAll`, on nodes) maps into the extraction's own `elt`
(`tcl (mixStep …)`, on indices), because a `stepAll` step IS a `mixStep` step by
its first disjunct. So every condition proved against `capP` transfers unchanged.

### 72.3 What the merge retires

§§53–66's separate-index layer — `odSeedCap`, `capElt`/`capUp`/`capDn`/`capSeed`,
the reflection and transfer lemmas, the `CapEdges` block — is **not on the
assembly's path**. It is marked SUPERSEDED in place rather than deleted:

* it is correct (the cold reviewer read `odSeedCap_old` line by line);
* `odAmalgDR` (§70) refutes §51.1 independently of whether it is used;
* and deleting certified work to make a diff smaller is not a trade this project
  makes.

A reader tracing the construction should skip §53–§66 and go to §63.

### 72.4 Where the mixed quadrant stands

| | |
|---|---|
| the five routing conditions | **done** |
| every `MultiTierOk` row's lemma | **exists** |
| assembling `MultiTierOk` for the merged certificate | not started |
| instantiation — the node set incl. caps, `up`/`dn` declaring cap position | not started |
| reindex → encode → `MixedCompleteness` | not started, templated |

Build: 27,804 lines, exit 0, 0 errors / 0 warnings / 0 sorries / 0 `sorryAx`.

## 73. THE MERGE RESTORES THE ORIGINAL CONSUMER

§55 reported that `mtkKernelsOD_of_debts` could not serve a cap: its debts run
through `odLt_hEreal` — *"the model relation EQUALS the declared relation"* — and
a cap had no model realization. That finding drove §56's rebuild at the label
level, and §54's estimate was revised upward because of it.

**With caps in `β` the obstruction is gone.** A cap IS a model node; `g` gives
it; and `hppE` — the specific debt §55 could not supply — is discharged by
`merged_hppE` from machinery that predates the entire cap discussion:

* relation half — `tcl_sub_pp` over `mixStep_rho`;
* budget half — `tcl_mixStep_bud`, which gives EQUALITY, since the budget is
  constant along `PP`-paths (§44.3).

### 73.1 Tally of what the separate index cost

Three findings, each recorded at the time as a discovery about the mathematics,
were artifacts of the separate-index design:

| finding | what it really was |
|---|---|
| §55 — the consumer cannot serve a cap | a cap wasn't in `β`, so had no `g` |
| §58.2 — `∃DR` at a cap is unservable | `capSeed`'s catch-all, which §51.1 wrongly called forced |
| §71.2 — `rDR` circles back on itself | the seed pair needed a base index the cap didn't have |

All three dissolve on the merge. The label-level route (§56) remains correct and
is a genuine alternative, but it was not necessary.

### 73.2 Overlap found while checking

`stepAll_hppE`, `rPP_witness` and `rPPI_witness` already existed. My `cap_rPP` /
`cap_rPPI` partially duplicate the latter two — mine add the closure-MEMBERSHIP
half (`capNodes`), which the originals do not have, so they are not redundant,
but the witness half was already there. `merged_hppE` is genuinely new:
`stepAll_hppE` covers `tcl stepAll` only, not the full `tcl (mixStep …)` with
the `up`/`dn` clause.

### 73.3 State

| | |
|---|---|
| the five routing conditions | done |
| `hppE` for the merged path | **done** (`merged_hppE`) |
| the remaining `mtkKernelsOD_of_debts` debts | `hdr`, `hb`, `hup`, `hdn`, `hdrk`, `hq*` — all pre-existing obligations of the uncapped extraction, unchanged by the merge |
| instantiation and the tail | not started |

The merged certificate uses the ORIGINAL consumer, so what remains for the mixed
quadrant is what remained for the extraction before caps were ever introduced,
plus the node set now including caps.

Build: 27,846 lines, exit 0, 0 errors / 0 warnings / 0 sorries / 0 `sorryAx`.

## 74. `MergedExtraction` — the mixed quadrant as ONE certificate statement

§60's `MixedCompleteness` names the pipeline's premise, but it mentions `codesM`
and `mtAcceptB` — the ENCODING. That is machinery, and it is certified. §74
factors it out.

```
MergedExtraction C0 :=
  Satisfiable C0 →
    ∃ nE nK (T : MultiTier (Fin nE) (Fin nK)) (e : Fin nE),
      MultiTierOk T ∧ C0 ∈ T.tauE e ∧
      nE ≤ mixKT C0 ∧ nK ≤ mixKT C0 ∧ (∀ k, T.p k ≤ mixKT C0) ∧
      labels drawn from cl C0
```

No encoder, no checker, no enumeration: just *a valid certificate exists, within
bounds computed from `C₀`*.

* `mixedCompleteness_of_merged` — the encoding step, certified
  (`encodeMT_accepts` + `encodeMT_mem_codesM`);
* `decidableSat_pofree_merged (C0) (h : MergedExtraction C0) :
  Decidable (Satisfiable C0)` — the composition.

### 74.1 What this settles

**Everything between a certificate and a decision procedure is now
machine-checked.** Soundness (unconditional), the fixed enumeration, the
encoder, the checker, the reduction. The fragment's remaining mathematics is
exactly one sentence: *a satisfiable ∀PO-free concept admits a valid bounded
certificate.*

The chain of named premises has been shrinking in the right direction:

| | premise | mentions |
|---|---|---|
| §60 | `MixedCompleteness` | codes, checker, enumeration |
| §74 | **`MergedExtraction`** | certificates and bounds only |

### 74.2 What remains, concretely

To discharge `MergedExtraction` for the merged construction:

1. the extraction's data — node set (with caps), kernels, `up`/`dn`, `kdr`;
2. the debts of `mtkKernelsOD_of_debts` — `hppE` done (§73), the rest
   (`hdr`, `hb`, `hup`, `hdn`, `hdrk`, `hq*`) all have their base facts
   (`seedMix_dr`, `seedMix_hb`, the banks, `cross_*_of_shared`);
3. `he_ex`/`hk_ex` — reduced to the five routing conditions, all discharged
   (§§63–72);
4. reindex onto `Fin` (`reindexMT`, `reindexMT_ok`) and the counting against
   `mixKT`.

Build: 27,884 lines, exit 0, 0 errors / 0 warnings / 0 sorries / 0 `sorryAx`.

## 75. ITEM 4 — indexing a node list by `Fin`

`reindexMT_ok` wants a BIJECTION onto `Fin`, and the extraction produces its
externals as a membership subtype `{n // n ∈ l}` of a `Nodup` node list. The
horizontal path (`encodeHF_mtOk`) does this inline with `getD`; the mixed path
needs it as a reusable brick, so §75 builds it once:

* `subOfFin` — position `i` ↦ the element there, with its membership;
* `subOfFin_inj` — injective on a `Nodup` list, via `List.getD_inj` and the
  `get`/`getD` bridge;
* `subOfFin_surj` — **axiom-free**, from `List.get_of_mem`;
* **`reindexMT_toFin`** — a valid certificate on two membership subtypes
  reindexes to a valid certificate on `Fin` of their lengths.

That is exactly the index shape `MergedExtraction` and `encodeMT` both want, so
the extraction may build over the node LISTS it naturally produces and convert.

### 75.1 §74.2's list, updated

| item | status |
|---|---|
| 1. the extraction's data (node set incl. caps, kernels, `up`/`dn`, `kdr`) | not started — **the construction proper** |
| 2. `mtkKernelsOD_of_debts`'s debts | `hppE` done (§73); the rest have their base facts |
| 3. `he_ex`/`hk_ex` | reduced to the five routing conditions, all discharged |
| 4. reindex onto `Fin` | **done** (`reindexMT_toFin`); the counting against `mixKT` remains, and `mixNodes_length_le_KT` bounds it |

So three of the four are done or reduced to assembly against existing lemmas.
Item 1 — producing the actual data from a model — is the construction, and it is
what `MergedExtraction` names.

Build: 27,942 lines, 1,426 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 76. THE CHAIN IS COMPLETE EXCEPT FOR ITS FIRST ARROW

`mergedExtraction_of_ok` (axioms `propext`, `Quot.sound` — no `Classical.choice`)
is the last link. A valid certificate over a `Nodup` node list, within the
`mixKT` bounds and with labels from `cl C0`, gives `MergedExtraction`'s body: it
reindexes by `reindexMT_toFinE` and the bounds transfer, because reindexing
changes only the indexing, not the labels (`reindexMT_tauE` / `_phase` / `_p`,
all `rfl`).

### 76.1 The chain

```
   extraction data + debts
        │  mtkKernelsOD_of_debts          ← the one remaining arrow
        ▼
   MultiTierOk T           (T over the extraction's own node list)
        │  mergedExtraction_of_ok         ← §76, certified
        ▼
   MergedExtraction C0
        │  mixedCompleteness_of_merged    ← §74, certified
        ▼
   MixedCompleteness C0
        │  decidableSat_pofree            ← §60, certified
        ▼
   Decidable (Satisfiable C0)
```

**Everything below the top arrow is machine-checked.** The remaining task of the
mixed quadrant is exactly: produce the extraction's data from a model, and
discharge `mtkKernelsOD_of_debts`'s debts — of which `hppE` is done (§73), the
coverage pair `he_ex`/`hk_ex` is reduced to the five routing conditions (all
discharged, §§63–72), and the rest (`hdr`, `hb`, `hup`, `hdn`, `hdrk`, `hq*`)
have their base facts already certified.

### 76.2 A Lean note worth keeping

`open Classical in` on `reindexMT_toFinE` made it conjure
`Classical.propDecidable` for `DecidableEq κ`, which then refused to unify with
`instDecidableEqFin` at the call site. Taking the instance as an argument fixed
it — and dropped `Classical.choice` from both theorems' axiom profiles.

Build: 28,008 lines, 1,431 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 77. CLOSING THE DEBTS — three more discharged

§76's remaining arrow is `mtkKernelsOD_of_debts`'s debt list. Progress this
round:

* **`mUp_hup`** — `hup`. The debt quantifies over a node at-or-BELOW an attached
  external, while `mUp_phase` speaks of the attached external itself; the gap is
  one `comp(PP,PP) = {PP}` and one budget equality.
* **`mDn_hdn`** — `hdn`, the mirror, at-or-ABOVE.
* **`hdr_of_model`** (**axiom-free**) — `hdr`. The declared disjointness is the
  DOWNWARD CLOSURE of the seed, and model `DR` descends: `comp(PP,DR) = {DR}` on
  the left, `comp(DR,PPI) = {DR}` on the right.

### 77.1 The debt list

| debt | status |
|---|---|
| `hppE` | ✓ `merged_hppE` (§73) |
| `hdr` | ✓ **`hdr_of_model`** — axiom-free |
| `hb` | ✓ `seedMix_hb` (pre-existing) |
| `hup` | ✓ **`mUp_hup`** |
| `hdn` | ✓ **`mDn_hdn`** |
| `hdrk` | base fact `hdrP_of_bank`; needs the closure version, like `hdr` |
| `hqpp`/`hqppi`/`hqdr` | `cross_pp_of_shared` / `cross_ppi_of_shared` / `cross_dr_of_shared` — need wiring |
| `he_ex`/`hk_ex` | ✓ reduced to the five routing conditions, all discharged (§§63–72) |

Five of nine done, three have their base facts, one is wiring.

### 77.2 Lean note

`nodeOf g ck ik (Sum.inl f)` and `g f` are definitionally equal but NOT
syntactically, and `rw` needs the latter. Type-ascribing a hypothesis does not
change its syntactic form — the fix is to state the `conv_` instance with an
explicit type and rewrite the GOAL, not the hypothesis. Cost this round: four
failed iterations on one rewrite.

Build: 28,112 lines, 1,434 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 78. THE SEED'S KERNEL BLOCK, BOTH DIRECTIONS — and an honest assessment

`kdrAt` (§46) covers the ascending index only. `mCk`/`mIk` are already
`Sum.elim`s over `KIdxM`, so the combined version is uniform in the direction:

* **`mKdr`** — every phase of `k` from its base onward is disjoint from `e`;
* **`mKdr_base`** — `seedMix_dr`'s `hkdr`;
* **`mKdr_phase`** — the orientation `hdrk` asks for, via `conv dr = dr`.

### 78.1 Can the gap be closed? — no roadblock, but not in one session

Asked directly, the honest answer:

**No roadblock has been identified.** Every remaining item has a route, and each
round of work has closed items at roughly the predicted cost. What remains:

| item | shape | risk |
|---|---|---|
| `hdrk` | the closure version, as `hdr_of_model` was, with the kernel side | moderate — the seed pair may be kernel↔external, needing the bank |
| `hqpp`/`hqppi`/`hqdr` | wiring `cross_*_of_shared` into `mixLt`'s kernel–kernel clause | moderate, mechanical |
| top-level assembly | instantiate `β := EIdx`, `κ := KIdxM`, `kdr := mKdr`, discharge all debts | large but routine |
| **the counting** | `mixNodes`' bound must cover the node set INCLUDING caps | **the one I would flag** |

### 78.2 Why the counting is the item to watch

It is F6's descendant. The node set is `mixNodes fuel b root`, finite by
construction — but its FUEL FRONTIER may carry unserved demands, and serving
them is what §49's trichotomy and §52's cut are for. Folding the cap layers into
the bound will likely require enlarging `mixKT`, which is a parameter change
that propagates to `codesM`'s arguments.

That is not a wall — §52 bounds the layer count by `|typeEnum C0|`, so the
enlarged bound is still computed from `C₀` alone. But it is the step where this
campaign has historically found what it did not expect, and I would not call it
mechanical.

**Estimate, unchanged from §77: 2–4 sessions.** Each of the last several rounds
has closed one or two debts, which is the rate that estimate assumes.

Build: 28,146 lines, 1,437 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 79. ALL NINE DEBTS DISCHARGED

`mtkKernelsOD_of_debts`'s debt list is complete.

| debt | discharged by | axioms |
|---|---|---|
| `hppE` | `merged_hppE` (§73) | classical |
| `hdr` | `hdr_of_model` (§77) | **none** |
| `hb` | `seedMix_hb` (pre-existing) | — |
| `hup` | `mUp_hup` (§77) | classical |
| `hdn` | `mDn_hdn` (§77) | classical |
| `hdrk` | **`hdrk_of_model`** (§79) | **none** |
| `hqpp` | **`hqpp_of_model`** | **none** |
| `hqppi` | **`hqppi_of_model`** | **none** |
| `hqdr` | **`hqdr_of_model`** | **none** |
| `he_ex`/`hk_ex` | the five routing conditions (§§63–72) | — |

Six of them depend on no axioms at all.

### 79.1 What the last three needed

* **`mixLt_inr_phase`** (axiom-free) — the missing brick: a phase is below
  anything its kernel is below, because both of `mixLt`'s kernel-source clauses
  route through a `dn` external that contains every phase.
* **`hqpp`/`hqppi`** — two applications of `comp(PP,PP) = {PP}` through the
  shared external chain; `hqppi` is `hqpp` transposed by `conv pp = ppi`.
* **`hqdr`** — a four-case split on which endpoints are the kernels themselves.
  The both-endpoints case is **vacuous**, because `seedMix` sends kernel↔kernel
  to `False`.

### 79.2 A design fact the proof forced out

`hdrk` cannot be derived from a base-level `DR` fact. For an ASCENDING kernel the
base sits BELOW its phases, and `comp(PPI,DR) = {DR,PO,PPI}` — **`DR` does not
travel upward**. So the seed's kernel block must itself be the COFINAL statement.

That is exactly how `kdrAt` was defined back in §46, and now there is a reason on
the record rather than a convention. `mKdr` (§78) is its both-directions form.

### 79.3 What is left

Only the top-level assembly and the counting:

1. instantiate `β := EIdx`, `κ := KIdxM`, `kdr := mKdr`, feed the nine;
2. the counting — `mixNodes`' bound over the node set including caps (§78.2's
   flagged item, F6's descendant).

Build: 28,342 lines, 1,442 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 80. EVERY INPUT IS NOW A LEMMA ABOUT THE EXTRACTION'S OWN DATA

§79 closed the nine debts as ABSTRACT lemmas — parameterised over `elt`, `seed`,
`up`, `dn`. §80 supplies the remaining inputs for the extraction's CONCRETE data
(`nd`, `mUp`, `mDn`, `mCk`, `mIk`, `mPk`, `mBk`, `mKdr`):

| input | lemma |
|---|---|
| `hup0` / `hdn0` — base-level attachment | **`mUp_base`** / **`mDn_base`** (`mUp_phase` at `a = 0`) |
| `hud`'s budget half | **`mUpDn_bud`** — both externals carry the kernel's budget |
| `hirrE` | **`mElt_irrefl`**, via **`elt_irrefl`**: every `elt` edge is a model `PP` edge and `PP` is irreflexive (`refl_eq` gives `EQ`) |
| `helt` | **`mElt_rho`** |
| `hp`, `hstep`, `hty`, `hdom` | `mPk_pos`, `mCk_step`, `mCk_ty`, `mCk_dom` (§46) |
| `hsym`, `hsep`, `hud` | `seedMix_sym`, `hsep_of_model`, `mixStep_hud` (pre-existing) |
| `hdnphase` / `hupphase` | `mDn_phase` / `mUp_phase` |
| `hseedPhase` | **`mKdr_phase`** (§78) |
| `hqq` | `seedMix`'s kernel↔kernel block is `False` |

### 80.1 Where that leaves the assembly

Nothing in `mtkKernelsOD_of_debts`'s signature now lacks a discharging lemma for
the extraction's data. The assembly is the instantiation itself — feeding ~25
arguments — plus the counting.

That is the first time in this campaign the remaining work has been purely
mechanical at the top level. Given the record, that claim deserves the standing
caveat: it means *no gap identified*, and the instantiation is exactly the kind
of step where §55, §58 and §71 each found one.

### 80.2 The counting, still outstanding

`mixNodes`' bound over the node set including caps — §78.2's flagged item, F6's
descendant, and the last piece that is not obviously routine.

Build: 28,400 lines, 1,447 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 81. THE ASSEMBLY GOES THROUGH — `mergedMT_ok`

`mtkKernelsOD_of_debts` fed with the extraction's own data
(`nd`, `mUp`, `mDn`, `mCk`, `mIk`, `mPk`, `mBk`, `mDir`, `mKdr`). It compiles.

```
mergedMT_ok … : MultiTierOk (mtkKernelsOD I C0 (odSeed …)
    (fun e => (nd e).x) (fun e => (nd e).k) (mBk nd) mDir
    (mCk …) (mIk …) (mPk …))
```

All nine debts discharged in place, from the §77–§80 lemmas. The five structural
inputs likewise (`mElt_irrefl`, `tcl_trans`, `mixStep_hud`, `seedMix_sym`, and
`hsepS`).

### 81.1 What remains as a hypothesis, and why

| hypothesis | why it is not discharged here |
|---|---|
| `he_ex` / `hk_ex` | coverage — `odSeed_he_ex`/`_hk_ex` plus the five routing conditions, which depend on the NODE SET |
| `hsepS` | `hsep_of_model` supplies it; it is left as a parameter so the theorem does not fix the seed's shape |
| `hbS`, `hbK`, `hbQ` | the BUDGET halves of the disjointness debts — `seedMix_hb` is the external one; the kernel ones are the counting's neighbours |

So the assembly is done and the residue is exactly the two things §80.2
predicted: **coverage and counting**, both of which are the node set.

### 81.2 Honest reading

This is the first time the top-level certificate has been assembled from the
extraction's data with every debt discharged rather than assumed. It is a real
milestone.

It is NOT the fragment. `mergedMT_ok`'s hypotheses still include coverage and the
budget bounds, and those are where F6's descendant lives. The chain from here is
short and certified (§§74–76), but its first link still needs a node set that is
finite, closed, and counted.

Build: 28,590 lines, 1,449 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 82. WHAT IS MISSING TOWARD THE FULL ∀PO-FREE FRAGMENT

Everything downstream of a valid, counted certificate is certified (§§74–76,
§81). This is the complete list of what is not.

| # | item | size | risk |
|---|---|---|---|
| **A** | **the node set** — a concrete `lE : List (MTKNode I C0)`, `Nodup`, serving as `β`, containing everything coverage needs | large | **highest — F6's descendant** |
| **B** | coverage: `he_ex`/`hk_ex` via `odSeed_he_ex`/`_hk_ex` and the five routing conditions, instantiated at `lE` | medium | medium — the conditions are discharged (§§63–72) but stated for `capNodes`/`capP` |
| **C** | the counting: `lE.length ≤ mixKT C0`, `nK ≤ mixKT C0`, `∀ k, T.p k ≤ mixKT C0` | medium | **high — `mixKT` may need enlarging** |
| **D** | **κ finiteness** — `KIdxM` as an explicit `Nodup` list for `reindexMT_toFinE`. No machinery exists | medium | medium — a missing brick, not a gap |
| **E** | the budget hypotheses `hbS`, `hbK`, `hbQ` | medium | low–medium (`seedMix_hb` covers the external one) |
| **F** | `hsepS` — wiring `hsep_of_model` | small | low |
| **G** | label conditions: `mtk` labels lie in `allListsLe (cl C0) …`, from `mtk_sub_cl` plus a length bound | small | low |
| **H** | the top-level theorem `∀ C0, POFree C0 → Decidable (Satisfiable C0)`, and whether the mixed extraction SUBSUMES the other three quadrants | small–medium | medium — subsumption is plausible but unchecked |

### 82.1 The shape of what is left

**A and C are one problem wearing two hats.** The node set must be finite (so it
can be counted) AND closed (so coverage holds at its frontier), and those pull
against each other — closing under demands grows the set, bounding it truncates.
§49's trichotomy and §52's cut exist precisely to resolve that tension, and
applying them to the concrete `mixNodes` bound is the remaining mathematics.

Everything else (B, D, E, F, G, H) is construction and wiring against lemmas
that exist.

### 82.2 Honest status line

*The ∀PO-free fragment's decision pipeline is machine-checked from a valid
counted certificate onward, and the certificate is now assembled from the
extraction's own data with every debt discharged. What remains is the node set:
finite, closed, counted.*

Three of the four quadrants have general decidability theorems already
(`decidableSat_hfrag`, `decidableSat_vtower*`, `decidableSat_vtowerRRI`); the
mixed one is what A–H would complete, and item H would then ask whether it
subsumes the other three.

## 83. ITEMS F, G, D DONE — and H resolved on inspection

Working §82's list from the low-risk end, so that nothing A depends on is left
unverified.

**F — `mSep`.** `hsep_of_model` instantiated at the extraction's data. Direct.

**G — `mtk_mem_allListsLe`.** `mtk` is a filter of `mty`, itself a filter of
`cl C0`, so every label is length-bounded over `cl C0` — exactly what
`encodeMT_mem_codesM` asks of `tauE` and `phase`.

**D — `subtypeList`.** The missing brick. `KIdxM = KIdx ⊕ KIdxI`, each a SUBTYPE
of the external index by a `persistDs`-nonemptiness predicate, so an enumeration
of the externals yields one of the kernels. Built with `subtypeList_val_mem`,
`mem_subtypeList` (covers) and `subtypeList_nodup`.

Defined by **structural recursion, not `filterMap`** — this Lean's core has
neither `List.Nodup.filterMap` nor `List.Nodup.map` nor `List.Nodup.pmap`
(probed; only `List.Nodup.sublist` exists), and the `Nodup` proof is the point of
the brick.

### 83.1 H — subsumption, resolved without new work

`POFree` is structural (no `∀PO` subconcept anywhere). `HFrag`'s `hall` says no
`∀PO` in `cl C0`, and `cl` is the subconcept closure — so **`HFrag → POFree`**,
and `HFrag` is strictly stronger, since it also forbids vertical existentials
(`hex`).

Therefore a decidability theorem for all `POFree C0` **subsumes**
`decidableSat_hfrag`, and the same argument covers the vertical quadrants. H is
a corollary of the target, not separate work — the fragment would collapse to
one theorem.

### 83.2 §82's list, updated

| item | status |
|---|---|
| A — the node set | **outstanding — the remaining mathematics** |
| B — coverage at that node set | outstanding, wiring |
| C — the counting | outstanding, with A |
| D — κ finiteness | **done** (`subtypeList`) |
| E — budget hypotheses | outstanding |
| F — `hsepS` | **done** (`mSep`) |
| G — label conditions | **done** (`mtk_mem_allListsLe`) |
| H — subsumption | **resolved** — a corollary, no work |

Next per the plan: a probe for A+C, then A+C.

Build: 28,700 lines, 1,455 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 84. THE A+C PROBE — `wp106`

Run before committing sessions to the node-set construction, per the standing
rule. It answered both questions and, more usefully, corrected the construction.

### 84.1 The finding that matters

**The first run showed the closure NOT closing — a plateau at ~93% that more
fuel did not fix.** Inspecting actual failures showed they were all the same
shape: a chain node `a_k` with a ONE-SHOT `∃PP` demand whose witnesses are
`a_{k+2}, a_{k+3}, …` — further up the SAME chain, forever.

The probe was modelling kernel service as **persistent demands only**. §49 gives
**two** branches, and the second — `oneshot_in_kernel`: a one-shot demand whose
demanded concept RECURS ON THE CHAIN is served by the chain, which IS the kernel
— was missing.

**That is a requirement on the assembly, not on the probe.** The construction
must route such demands to the kernel. Without it every ascending chain looks
like an unbounded closure; with it:

| fuel | cases | CLOSED | unserved |
|---|---|---|---|
| 1 | 222 | 216 | 7 |
| 2 | 222 | 220 | 2 |
| 3 | 222 | 221 | 1 |
| **4** | 222 | **222** | **0** |
| 6, 8 | 222 | 222 | 0 |

**A: closed at fuel 4.** **C: 0 of 220 exceed `(|cl C0|+1)^mdepth`**, worst
`|S| = 3` against bound 3 — and `mixKT C0` is far larger than that.

### 84.2 Two artifacts caught inside this probe

* **Truncation.** The chains are infinite and the domain truncated them at
  `na=8, ns=6`. Of 28 apparently unserved demands, **26 had their witness just
  outside the truncation**. Widened to 30/25 and made the check a permanent part
  (part T), which now reports 0 of each.
* **The construction-model error** above, which is the finding.

### 84.3 Honest scope

One model class (`wp105`'s, audited by part R each run), concepts of depth 2–3,
and mean `|S| = 1.3` — the closures are SMALL, so the counting result is weak
evidence and the closure result is the strong one. What should be relied on is
the STRUCTURAL fact: **branch 1 is required, and with it the closure terminates
at low fuel**.

### 84.4 What this de-risks

§82 rated A "highest risk — F6's descendant" and C "high — `mixKT` may need
enlarging". On this evidence C looks comfortable and A has a definite shape: the
construction is `mixNodes` with BOTH kernel-service branches, and the fuel needed
is small. That is not a proof — but it is the first evidence that the node set
closes at all.

## 85. KERNEL SERVICE, BOTH BRANCHES — the `wp106` correction, certified

`wp106` found the requirement the assembly had been missing. §85 names it so it
is checkable rather than remembered:

```
kernelServes I c i D :=
  sat I (c i) (∀PP.∃PP.D)              -- round-robin, rr_covers
  ∨ ∃ j, i < j ∧ sat I (c j) D          -- the concept recurs on the chain
```

* `kernelServes_recur` — the second branch really serves, with **no external at
  all**: the higher chain node IS the witness (`oneshot_in_kernel`);
* `kernelServes_guard` — under the first, the demand is served at every chain
  node above the guard's holder (`sat_all_pp_up`);
* `kernelServes_no_external` — **the point**: a kernel-served demand needs no new
  external, so the node closure may SKIP it.

All three **axiom-free**.

### 85.1 Why this is the difference between terminating and not

`wp106` measured it directly. Modelling kernel service as the FIRST branch only:
the closure plateaus and **no fuel suffices** — every ascending chain walks
forever, because each node's one-shot `∃PP` is served two nodes further up the
same chain. With both branches: **222/222 closed at fuel 4**.

So skipping is not an optimisation. It is what makes the node set finite.

### 85.2 §82's list

| item | status |
|---|---|
| A — the node set | shape now fixed: `mixNodes` skipping kernel-served demands; **the closure lemma is the remaining build** |
| B — coverage | follows from A's closure plus the routing conditions |
| C — the counting | probe says comfortable; `mixNodes_length_le` bounds it |
| D, F, G, H | done / resolved |
| E — budget hypotheses | outstanding |

Build: 28,762 lines, 1,459 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 86. §85.3 — the termination argument, and a correction

**Half 1, certified.** `ascPath_len_le` / `ascPath_repeats`: a repeat-free
ascending path is at most `|typeEnum C0|` long, and a longer one must repeat a
type.

**Half 2, corrected.** I first stated it as *a type repeat makes the demand
`kernelServes`*. **That is false.** Checking it against `kernel_of_chain` showed
why: a repeat yields a recurrent SEGMENT — the kernel's `hty` and `hp` — not a
guarantee about the original chain. A demand can stay one-shot with an off-chain
witness while the chain's types repeat perfectly well.

What a repeat gives is a **kernel at that point**, and then §49's trichotomy
applies: chain-recurrence (skip), one cofinal external (extend by one), or
neither. **So the closure's bound is the LAYER count of §52, not a property of
any single chain.**

### 86.1 Item A's remaining target, precisely

> the skipping closure's non-kernel-served steps form layers; within a layer a
> node contributes at most `|cl C0|` steps; and the layer count is bounded by
> `layer_recursion_terminates` (§52).

Every ingredient is certified — `kernelServes` (§85), the trichotomy (§49),
`layer_recursion_terminates` (§52), `ascPath_len_le` (§85.3),
`mixNodes_length_le_KT`. What is unwritten is their composition into a closure
definition and its coverage lemma.

No placeholder `def` is left in the artifact for this: a malformed Prop would be
worse than prose, and I wrote one before deleting it.

### 86.2 State

| item | status |
|---|---|
| A | shape fixed, half 1 certified, half 2 stated; **the composition is the build** |
| B | follows from A |
| C | probe says comfortable; `mixNodes_length_le_KT` bounds it |
| D, F, G, H | done / resolved |
| E | outstanding |

Build: 28,820 lines, 1,461 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 87. THE SKIPPING CLOSURE — item A's composition, built

`skipNodes` is `ppNodes` with the kernel-served demands DROPPED, which per
`wp106` is what makes it terminate. The kernel-service test is a PARAMETER
`kser`, so the definition fixes no particular kernel family; the extraction
supplies it and §85's `kernelServes_no_external` is its soundness.

| | |
|---|---|
| `skipNodes` | the closure |
| `self_mem_skipNodes` | the root is in it |
| `skipNodes_ppWitness_mem` / `_ppiWitness_mem` | **coverage step** — a demand the kernel does NOT serve has its witness in the closure at one more fuel |
| `skipNodes_length_le` | **bounded by `mtkBound C0 fuel`** — the same bound as `ppNodes`, since skipping only removes branches |

So at fuel `|typeEnum C0|` the closure is bounded by `mtkBound C0 (typeEnum C0).length`,
which is `mixKT`'s inner factor — item C's arithmetic, on the certified side.

### 87.1 What item A still needs

The two membership lemmas give coverage **one step at a time**. What is not yet
written is the induction that turns them into *"every demand at every member is
kernel-served or served inside the set"* — i.e. that the fuel `|typeEnum C0|`
suffices, which is §86's half 2 (the layer bound).

So A is now: definition ✓, bound ✓, coverage step ✓, **coverage induction
outstanding**.

### 87.2 A process note worth recording

Building this, a `python` string-index edit matched an identical passage in
`ppNodes_length_le` — the two proofs have the same shape — and replaced from
there, damaging ~1,500 lines. Caught immediately by the build (errors at line
10945, far from the edit site), restored with `git checkout`, redone with a
uniqueness assertion.

**Rule: assert `s.count(anchor) == 1` before every string-replace edit in this
file.** Two proofs of the same shape make bare `index` unsafe, and the artifact
is now large enough that identical passages are common.

Build: 28,925 lines, 1,466 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 88. THE COVERAGE INDUCTION — conditional, with the residue isolated

Item A's coverage lemma, built on three new pieces:

* **`skipNodes_mono`** — more fuel never removes a node;
* **`skipNodes_mono_le`** — the same in the fuel ORDER;
* **`skipNodes_step_sub`** — a member's own one-step closure lies inside the
  whole closure at one more fuel.

Then:

> **`skipNodes_covers_of_fixed`** — if one more fuel adds nothing (the closure
> has reached a FIXPOINT), the closure is CLOSED: every vertical demand at every
> member is either kernel-served or has its witness inside.

### 88.1 What this buys

The coverage induction is now **done modulo one hypothesis**, and that hypothesis
is exactly §86's half 2: *fuel `|typeEnum C0|` reaches a fixpoint*.

So item A has become a single, sharply stated question — the same shape the rest
of the campaign took when it went well:

| | |
|---|---|
| definition | `skipNodes` ✓ |
| bound | `skipNodes_length_le` ✓ |
| coverage step | `skipNodes_ppWitness_mem` ✓ |
| monotonicity | `skipNodes_mono`, `_mono_le` ✓ |
| transitivity | `skipNodes_step_sub` ✓ |
| coverage | `skipNodes_covers_of_fixed` ✓ **modulo the fixpoint** |
| **the fixpoint at `|typeEnum C0|`** | **outstanding — all that is left of A** |

### 88.2 Why the fixpoint is plausible and not yet proved

`wp106` measured the closure reaching a fixpoint at fuel 4 in every one of 222
cases. The theory says it must: the closure is bounded (`skipNodes_length_le`)
and monotone (`skipNodes_mono`), so the SIZES are non-decreasing and bounded,
hence eventually constant — but constant size does not give list equality
without `Nodup`, and `skipNodes` as defined can repeat nodes.

So the honest next step is either to dedup the closure (making size-stabilisation
give the fixpoint) or to bound the fuel directly by the layer argument. The first
is mechanical; the second is §86's half 2 proper.

Build: 29,062 lines, 1,471 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 89. THE DEDUP ROUTE FAILS — and why

§88.2 offered two ways to the fixpoint: dedup the closure so size-stabilisation
gives list equality, or bound the fuel by the layer argument (§86's half 2). The
dedup route was the cheaper-looking one. **It does not work.**

### 89.1 The argument, and where it breaks

The intended chain was:

1. dedup, so the closure is `Nodup`;
2. `S ⊆ step S` and both `Nodup`, so if `|step S| ≤ |S|` then `step S ⊆ S` —
   which is exactly **`mem_of_saturated`** (§47, built for this);
3. sizes are non-decreasing and BOUNDED, so some stage does not grow, giving (2)
   and hence the fixpoint.

**Step 3 is false here.** The only bound available is
`skipNodes_length_le : |skipNodes kser n f| ≤ mtkBound C0 f`, and

```
mtkBound C0 (k+1) = 1 + |cl C0| · mtkBound C0 k
```

**grows with the fuel** — exponentially. So the sizes are bounded at each stage
by a bound that outruns the stage count: running `K` stages permits size `K`
only if `K > mtkBound C0 K`, which never holds. The pigeonhole has nothing to
bite on.

### 89.2 What would fix it, and why it is half 2

`mem_of_saturated` needs a bound UNIFORM in the fuel. The only candidate is a
bound on the number of DISTINCT nodes the skipping closure can reach — and that
is precisely what §86's half 2 supplies via the layer argument.

Deduping by LABEL rather than by node would give a uniform bound
(`|typeEnum C0| · (mdepth C0 + 1)`), but it changes the object: two nodes with
the same label can have different relations to the rest, and the certificate
reads relations as well as labels. So that is not a shortcut either.

**Conclusion: half 2 is not avoidable by bookkeeping.** It is the remaining
mathematics of item A, and of the fragment.

### 89.3 State

Everything in §88's table stands; only the route to the fixpoint is narrowed.
`skipNodes_covers_of_fixed` remains the coverage lemma, and its hypothesis
remains the target.

## 90. HALF 2 — a second wrong formulation, and what it pins down

Attacking half 2 (a uniform bound on the skipping closure) produced a candidate
argument that **trivialises**, and the way it trivialises is informative.

### 90.1 The tempting argument

Take an ascending path `m₀ → m₁ → …` built by non-kernel-served `∃PP` steps.
Suppose two path nodes share a type. The segment then cycles into a kernel, the
demanded concept recurs along it, so the demand is kernel-served — contradiction.
Hence the types are pairwise distinct and the path is at most `|typeEnum C0|`
long, by `ascPath_len_le`.

### 90.2 Why it trivialises

Read `kernelServes` relative to **the path itself**:

```
kernelServes I c i D := sat (c i) (∀PP.∃PP.D) ∨ ∃ j, i < j ∧ sat (c j) D
```

The step at `mᵢ` uses a demand `D` whose witness is `mᵢ₊₁` — and `mᵢ₊₁` **carries
`D` by construction** and is above `mᵢ`. So the second disjunct holds at every
step, with `j = i+1`. **Every step would be kernel-served, and the closure would
never step at all.**

That is not what `wp106` measured, because there `kser` was read relative to the
node's OWN KERNEL CHAIN (the `rrPt` chain it lies on), not relative to the
closure's path.

### 90.3 What this pins

**`kernelServes`'s chain argument is load-bearing and must be the node's kernel
chain.** Relative to the path it is vacuous; relative to an arbitrary chain
(§86's first attempt) it is false. The only reading that both bites and holds is:

> `kser m D` = *`D` recurs above `m` along the kernel chain `m` lies on* — and a
> node on no kernel chain has `kser m D = false`.

So half 2 must relate the closure's PATH to the KERNEL CHAINS its nodes lie on.
That relationship is what neither §86's nor §90.1's formulation captured, and it
is the actual content of the remaining item.

### 90.4 Two wrong formulations now on record

| attempt | claim | why it fails |
|---|---|---|
| §86 | a type repeat on ANY ascending chain makes the demand kernel-served | a repeat gives a recurrent SEGMENT, not a guarantee about the chain; the witness can be off-chain |
| §90.1 | the closure's own path has distinct types | reading `kernelServes` on the path makes EVERY step kernel-served — vacuous |

Both were caught by checking the statement against what it would have to mean,
before any proof was attempted. The remaining item is unchanged in size but
better understood: **relate the skipping closure's path to the kernel chains.**

## 91. HALF 2, FIXED

The reading §90.3 identified, made into theorems.

### 91.1 The core

**`path_repeat_carries`** — if an ascending path repeats a type at `i < j`, the
demand taken at step `i` is carried INSIDE the segment `[i, j)`, i.e. by one of
the phases of the kernel obtained by cycling that segment (`kernel_of_chain`).
Two cases: `b = 1` when the witness is itself inside the segment, `b = 0` when
the segment has length one and the repeat identifies the witness's type with the
start's.

This is non-trivial where §90's version was vacuous, because the recurrence is
demanded **within a segment** — and a segment exists only where the path repeats
a type.

### 91.2 The consequence

**`skipPath_no_repeat`** — a path the closure EXTENDS has pairwise distinct
types. Its hypothesis `hext` is exactly what "extended rather than skipped at
step `i`" means: the demand there is not carried inside any segment starting at
`i`.

**`skipPath_len_le`** — such a path is at most `|typeEnum C0|` long. **This is
the uniform bound §89 showed bookkeeping could not supply.**

Supporting: `nodup_map_range` (this Lean has no `List.Nodup.map`, so by induction
through `List.range_succ`).

### 91.3 Item A

| | |
|---|---|
| definition, bound, coverage step | ✓ (§87) |
| monotonicity, transitivity | ✓ (§88) |
| coverage modulo a fixpoint | ✓ (§88) |
| **the uniform bound on extending paths** | ✓ **(§91)** |
| tying the bound to the fixpoint hypothesis | the remaining join |

The two ends now exist: `skipNodes_covers_of_fixed` wants a fixpoint, and
`skipPath_len_le` bounds how far the closure can extend. What is unwritten is
the step from "no extending path exceeds `|typeEnum C0|`" to "`skipNodes` at
fuel `|typeEnum C0|` is a fixpoint".

Build: 29,184 lines, 1,475 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 92. THE JOIN — and the subtlety it exposes

`skipPath_len_le'` (the bounded form) is in. Attempting the join — membership in
`skipNodes` means reachability by that many non-kernel-served steps — exposed
something the earlier sections had not.

### 92.1 The closure's path is not monotone

`skipNodes` follows **both** vertical demand kinds, and they point in **opposite
directions**:

* an `∃PP` step goes to `ppWitness`, which is **above**;
* an `∃PPI` step goes to `ppiWitness`, which is **below**.

But `skipPath_no_repeat` and `skipPath_len_le'` were proved for an **ascending**
path — `path_repeat_carries` reasons about the segment `[i, j)` of a chain, and a
chain is what an ascending path is. A mixed path is a walk, not a chain.

### 92.2 Three ways out

| route | idea | cost |
|---|---|---|
| 1. orient | `stepAll` already orients both kinds upward, at the cost of reversing `∃PPI` edges — the path becomes a WALK in the order | the repeat argument redone for walks |
| **2. split** | bound the `∃PP`-only and `∃PPI`-only sub-closures separately, each ascending in its own direction, and compose | **transcription — the descending mirror (`rr_coversI`, `persistDsI`, `kCkI`) exists throughout** |
| 3. interleaving | show a mixed path cannot alternate more than boundedly often | closest to §52's layer argument |

**Route 2 looks cheapest**, because the descending machinery has been a certified
mirror of the ascending one at every stage of this campaign, so the dual of §91
should be transcription rather than new mathematics.

### 92.3 Housekeeping

The `skipNodes_path` draft that exposed this was **removed, not patched** — a
half-working reachability lemma in the artifact would be worse than its absence,
and the finding is recorded here instead.

Build: 29,232 lines, 1,476 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 93. ROUTE 2 — the upward half works

§92's obstacle was that `skipNodes` mixes upward (`ppWitness`) and downward
(`ppiWitness`) steps, so its path is a walk and §91's chain argument does not
apply. Route 2 splits by direction. The upward half is now built:

* **`skipNodesU`** — the `∃PP`-only skipping closure;
* **`self_mem_skipNodesU`**;
* **`skipNodesU_path`** — membership at fuel `f` means reachability by at most
  `f` non-kernel-served `∃PP` steps, each recorded with the demand that produced
  it.

**`skipNodesU_path` is exactly the lemma §92 could not state for the mixed
closure**, and it holds here because every step goes to `ppWitness` — so the path
ASCENDS, and §91's `skipPath_no_repeat` / `skipPath_len_le'` apply to it.

### 93.1 What remains of the upward half

The converse direction — a path of length `k` gives membership at fuel `k` —
and then the composition:

> `m ∈ skipNodesU kser n (F+1)` gives a path of length `≤ F+1`; if `kser`
> satisfies §91's `hext`, the path's types are distinct, so `skipPath_len_le'`
> caps it at `F = |typeEnum C0|`; hence the path has length `≤ F`, hence
> `m ∈ skipNodesU kser n F`. **That is the fixpoint.**

### 93.2 And the downward half

The dual (`skipNodesD` following `∃PPI`, descending) should be a transcription:
`ppiWitness`, `persistDsI`, `rr_coversI` and `kCkI` are certified mirrors of the
ascending machinery throughout this file, and §91's repeat argument dualises by
reversing the order.

Then the mixed closure is bounded by composing the two — §92's route 2 in full.

Build: 29,321 lines, 1,478 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 94. THE UPWARD FIXPOINT — proven

```
skipNodesU_fixed :
  ∀ m ∈ skipNodesU kser n (|typeEnum C0| + 1), m ∈ skipNodesU kser n |typeEnum C0|
```

**That is `skipNodes_covers_of_fixed`'s hypothesis, for the upward half.**

The argument, now certified end to end:

1. `skipNodesU_path` — membership at fuel `F+1` gives an ASCENDING path of at
   most `F+1` non-kernel-served `∃PP` steps;
2. `hext` (§91's condition on `kser`) — that path's types are pairwise distinct;
3. `skipPath_len_le'` — so it is at most `F = |typeEnum C0|` long;
4. `skipNodesU_of_path` — a path that short puts its endpoint in the closure at
   its own length;
5. `skipNodesU_mono_le` — hence at fuel `F`.

Supporting this round: `skipNodesU_mono`, `skipNodesU_mono_le`,
`skipNodesU_of_path`.

### 94.1 What this closes

Item A's upward half is **complete**: definition, bound, coverage step,
monotonicity, transitivity, path characterisation both ways, and the fixpoint.
The bound `|typeEnum C0|` is computed from `C₀` alone, as `mixKT` requires.

### 94.2 What remains

* **the downward half** — `skipNodesD` following `∃PPI`. Transcription: every
  lemma above has a mirror to write, and the descending machinery
  (`ppiWitness`, `persistDsI`, `rr_coversI`, `kCkI`) is certified throughout;
* **the composition** — bound the mixed closure by the two halves (§92's route 2
  in full);
* then item A feeds `skipNodes_covers_of_fixed`, and B/C/E follow as §82 laid
  out.

Build: 29,419 lines, 1,482 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 95–96. THE DOWNWARD HALF, AND A CORRECTION TO §92

### 95 — the downward half

`skipNodesD` and its five lemmas — `self_mem`, `_path`, `_of_path`, `_mono`,
`_mono_le`, `_fixed` — transcribed from the upward block. **It compiled on the
first attempt**, which is what "certified mirror" was supposed to mean and this
time did.

### 96 — §92's diagnosis was too pessimistic

§92 concluded that the mixed closure's path is a walk, not a chain, so §91's
repeat argument would not apply — and proposed three routes around it.

**That was wrong, and the transcription exposed it.** `path_repeat_carries` and
`skipPath_no_repeat` take an **arbitrary** `path : Nat → α` and never mention the
order: they are index arithmetic plus a pigeonhole. Nothing in them needs ascent.

The real obstacle was much smaller: the draft path-characterisation recorded
`∃PP` steps alone. Recording **both** kinds handles the mixed closure directly —
`skipNodes_path` now does, and it compiled.

So the §§93–95 split is correct and harmless, but was **not necessary**. Cost:
two sections of transcription. The lesson is the same one §90 taught in the other
direction — check what a lemma actually assumes before designing around it.

### 96.1 State of item A

| | |
|---|---|
| upward: definition, bound, coverage, paths both ways, **fixpoint** | ✓ (§§93–94) |
| downward: the same six | ✓ (§95) |
| mixed: path characterisation (both step kinds) | ✓ (§96) |
| mixed: the converse (path ⟹ membership) | outstanding |
| mixed: the fixpoint | follows from the converse, as §94 did |

The mixed path gives `k ≤ |typeEnum C0|` already, via `hext` and
`skipPath_len_le'`. What is missing is only the converse direction, which for the
upward half was `skipNodesU_of_path`.

Build: 29,676 lines, 1,489 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 97. ITEM A, ASSEMBLED

```
skipNodes_covers_at_typeEnum :
  ∀ m ∈ skipNodes kser n |typeEnum C0|, ∀ c hF,
    kser m c = true ∨ ppWitness m hF ∈ skipNodes kser n |typeEnum C0|
```

**The skipping closure at fuel `|typeEnum C0|` is CLOSED** — every vertical
demand at every member is either kernel-served or has its witness inside — **and
bounded** by `mtkBound C0 |typeEnum C0|` (`skipNodes_length_le`).

This is what §48 first hit as a blocker, thirteen sections and five refuted
routes ago.

### 97.1 The chain

| | |
|---|---|
| `SkipStep` | one non-kernel-served vertical step, either kind |
| `skipNodes_path'` | membership ⟹ a path of at most that many `SkipStep`s |
| `skipNodes_of_path` | a path of `k` steps ⟹ membership at fuel `k` |
| `skipPath_len_le'` | a path with distinct types is at most `|typeEnum C0|` long |
| `skipNodes_fixed` | hence fuel `|typeEnum C0|` is a FIXPOINT |
| `skipNodes_covers_of_fixed` | hence the closure is CLOSED |

### 97.2 The one hypothesis

`hext`: along a path of `SkipStep`s the types are pairwise distinct. §91 proved
this is what a type repeat contradicts (`path_repeat_carries`), and §85's
`kernelServes` is the predicate that should supply it — **but the connection
from `kernelServes` to `hext` is not yet written.**

So item A is: **assembled modulo `hext`**, with `hext` an explicitly stated
property of the kernel-service test rather than a gap in the argument.

### 97.3 §82's list

| item | status |
|---|---|
| A — the node set | **assembled, modulo `hext`** |
| B — coverage | follows from A |
| C — the counting | `skipNodes_length_le` at `|typeEnum C0|` |
| D, F, G, H | done / resolved |
| E — budget hypotheses | outstanding |

Build: 29,942 lines, 1,497 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 98. `hext` DISCHARGED — item A closed on a named property of `kser`

```
KserSegment kser :=
  ∀ path i j, i < j → mty (path i).x = mty (path j).x →
    ∀ c, (∃ b, b < j - i ∧ c ∈ mty (path (i+b)).x) → kser (path i) c = true
```

* **`hext_of_KserSegment`** — a type repeat carries the demand inside the segment
  (`path_repeat_carries`), so `KserSegment` marks it kernel-served, contradicting
  the step, which was taken only because it was NOT.
* **`skipNodes_covers_of_KserSegment`** — item A, with `hext` gone: the closure at
  fuel `|typeEnum C0|` is closed for any kernel-service test with the segment
  property.

### 98.1 The remaining question, well-posed

`kser` must satisfy **two** conditions pulling in opposite directions:

| condition | wants `kser` to be | supplied by |
|---|---|---|
| `KserSegment` (§98) | **more true** — anything carried in a segment | the definition |
| soundness for `e_ex` | **less true** — only what a kernel really serves | `kernelServes_no_external` (§85) |

They meet exactly where §85 put them: `kernelServes` on the CYCLED segment. "`c`
carried in the segment" is "`∃ j > i, sat (chain j) c`" for the chain that cycles
it, which is `kernelServes`'s second branch — and `kernelServes_recur` is its
soundness.

So what remains for A is to EXHIBIT a `kser : MTKNode → Concept → Bool` meeting
both. The ingredients are certified (`kernel_of_chain` builds the cycled kernel;
`kernelServes_recur` shows it serves; `path_repeat_carries` is the bridge); what
is unwritten is the definition and its two proofs.

### 98.2 Why "too true" is safe for A but not for soundness

A more permissive `kser` only SHRINKS the closure — more demands skipped, fewer
nodes. So `KserSegment` is monotone in `kser` and cannot be violated by
over-approximation. Soundness is the binding constraint, and it is the one
`kernelServes` was designed for.

Build: 30,010 lines, 1,500 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 99. §96 CORRECTED — the split IS necessary, for SOUNDNESS

Working out `kser`'s definition exposes that §96's "the split was not necessary"
was right about one half of the problem and wrong about the other.

### 99.1 What §96 got right, and what it missed

§96 observed that `path_repeat_carries` and `skipPath_len_le'` never mention the
order, so the **counting** works for a mixed path. That is correct.

But `kser` must also be **sound**: `kser m c = true` has to mean a kernel really
serves the demand. And a kernel is not a type repeat — `KernelData` requires

```
cstep : ∀ n, I.rho (c n) (c (n + 1)) = cdir d
```

**a UNIFORM direction.** `kernel_of_chain` supplies only the type repeat; the
step structure has to come from the path itself. A mixed path does not have it,
so a type repeat on a mixed path yields **no kernel**, and `KserSegment` has
nothing to justify it.

### 99.2 So the split is vindicated

`skipNodesU` and `skipNodesD` (§§93–95) have paths that ARE chains — uniformly
ascending and uniformly descending — so a type repeat on one of them cycles into
a genuine kernel, and `kernelServes_recur` gives the soundness.

Both already have their fixpoints (`skipNodesU_fixed`, `skipNodesD_fixed`). The
route forward is to run §98's argument on each half separately, where
`KserSegment` is justified, and compose at the coverage level.

### 99.3 The corrected picture

| | |
|---|---|
| counting | direction-agnostic — §96 was right |
| **soundness of `kser`** | **needs a chain — §96 missed this** |
| consequence | the §§93–95 split is NECESSARY after all, and already built |

Two corrections now stand against each other: §92 said the split was needed for
counting (wrong), §96 said it was not needed at all (also wrong). It is needed,
for the reason neither identified.

### 99.4 What remains

Define `kser` per direction, prove `KserSegment` on chains and soundness from
`kernelServes_recur`, then compose the two halves' coverage. Every ingredient is
certified; the definition and its two proofs are unwritten.

Build: 29,989 lines, 1,500 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 100. `kserU` — the upward kernel-service test, with both properties

§99 established that the segment must be a CHAIN, so `kser` is defined per
direction. The upward one:

```
kserU C0 I m c := decide (∃ path, (∀ t, ρ (path t) (path (t+1)) = PP) ∧ path 0 = m ∧
                            ∃ j, 0 < j ∧ mty (path 0) = mty (path j) ∧
                              ∃ b, b < j ∧ c ∈ mty (path b))
```

*`m` has an ascending chain through it whose types repeat, with the demanded
concept carried inside the segment.*

Both required properties are certified:

* **`kserU_segment` : `KserSegmentU (kserU C0 I)`** — §98's property, restricted
  to chains as §99 requires. Proof: shift the chain to start at `i`.
* **`kserU_sound`** — if the test fires, the demand really IS served, by a node
  of the chain itself. The repeat puts the concept at or above the start (the
  `b = 0` case uses `mty (path 0) = mty (path j)`), and `oneshot_in_kernel`
  reads it off.

### 100.1 Where this leaves item A

`skipNodes_covers_of_KserSegment` (§98) needs the mixed `KserSegment`; `kserU`
supplies the chain-restricted `KserSegmentU`. Joining them is the composition
§99.2 described: run the coverage argument on `skipNodesU` with `kserU`, on
`skipNodesD` with the dual `kserD`, and combine.

`skipNodesU_fixed` and `skipNodesD_fixed` are already proved, so what remains is:

1. `kserD` and its two properties — the dual of §100, transcription;
2. the `KserSegmentU`-to-`hext` step for the upward closure specifically
   (`hext_of_KserSegment`'s chain-restricted analogue);
3. composing the two halves' coverage into the mixed statement.

Build: 30,053 lines, 1,504 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 101. `kserD` — the downward test, and an adjustment the join needs

`kserD` with both properties, transcribed from §100:

* **`oneshot_in_kernelI`** (**axiom-free**) — the `∃PPI` mirror: a lower chain
  node carrying `D` serves an `∃PPI` demand above it;
* **`kserD_segment` : `KserSegmentD (kserD C0 I)`**;
* **`kserD_sound`** — the descending chain's order comes from `hchain` by the
  same `comp(PP,PP) = {PP}` induction `chain_pp_lt` runs upward.

### 101.1 The adjustment

Joining `KserSegmentU` to the upward closure's `hext` exposes a mismatch:

* `KserSegmentU` (§100) requires a **total** chain — `∀ t, ρ (path t) (path (t+1)) = PP`;
* a `skipNodesU` path is a chain only on its **prefix** — the steps exist for
  `i < k` and the path is unconstrained beyond.

So `kserU` should be stated over a **finite** chain segment rather than a total
one:

```
kserU m c := decide (∃ path j, 0 < j ∧ (∀ t, t + 1 ≤ j → ρ (path t) (path (t+1)) = PP)
                       ∧ path 0 = m ∧ mty (path 0) = mty (path j)
                       ∧ ∃ b, b < j ∧ c ∈ mty (path b))
```

Soundness survives: from a prefix chain `0..j` with a type repeat, the same
bounded `chain_pp_lt` induction gives `ρ (path 0) (path t) = PP` for the `t`
carrying the concept, and `oneshot_in_kernel` reads it off.

This is a definitional adjustment to four declarations per direction
(`kserU`/`kserD` and their two properties each), not a change of argument. It is
recorded rather than made, so the artifact stays green at a clean point.

### 101.2 Item A's remaining list

| | |
|---|---|
| `kserU`, `kserD` with both properties | ✓ (§§100–101) — **pending the finite-chain adjustment** |
| `hext` per direction from `KserSegmentU`/`D` | needs the adjustment first |
| composing the two halves' coverage | after that |

Build: 30,136 lines, 1,509 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 102. UNCONDITIONAL FIXPOINTS, BOTH DIRECTIONS

The §101.1 adjustment made (finite chain segments, both directions), then `hext`
discharged per direction:

* `chain_pp_lt_bdd` / `chain_ppi_lt_bdd` — a chain on a PREFIX orders that
  prefix;
* `kserU` / `kserD` restated over finite segments, with `_segment` and `_sound`
  re-proved;
* `hextU_of_KserSegmentU` / `hextD_of_KserSegmentD` — a `skipNodesU` path's steps
  go to `ppWitness`, so `ppWitness_rho` makes it a chain on its prefix, which is
  exactly `KserSegmentU`'s hypothesis;
* **`skipNodesU_fixed_kserU`** and **`skipNodesD_fixed_kserD`** — §94's and
  §95's fixpoints **with their hypotheses discharged**.

```
skipNodesU_fixed_kserU (C0) (n) :
  ∀ m ∈ skipNodesU (kserU C0 I) n (|typeEnum C0| + 1),
    m ∈ skipNodesU (kserU C0 I) n |typeEnum C0|
```

**No hypothesis on `kser`.** The test is concrete, its soundness is
`kserU_sound`, and the closure provably stops growing at a fuel computed from
`C₀` alone.

### 102.1 The adjustment cost nothing

§101.1 predicted "a definitional adjustment to four declarations per direction,
not a change of argument". That is what it was: `kserU`/`kserD` and their two
properties each, plus two bounded-chain lemmas. **No earlier result needed
revisiting** — `skipNodesU_fixed`, `skipNodesD_fixed`, `skipNodes_covers_of_fixed`
and everything upstream took the new definitions unchanged.

### 102.2 Item A

| | |
|---|---|
| `kserU`/`kserD`, concrete, with segment property AND soundness | ✓ |
| upward fixpoint, unconditional | ✓ |
| downward fixpoint, unconditional | ✓ |
| composing the two halves' coverage into the mixed statement | the remainder |

Build: 30,231 lines, 1,515 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 103. COMPOSING THE HALVES — the remaining quantity is the RUN COUNT

Composing §102's two fixpoints into a mixed statement does **not** go through the
obvious route, and working out why localises what is actually left.

### 103.1 Why a combined `kser` does not work

Take `kserM m c := kserU m c || kserD m c`. Soundness is fine — both disjuncts
are sound. But the mixed `hext` still fails, for §99's reason: a type repeat on a
MIXED path gives a segment that is neither a `PP`-chain nor a `PPI`-chain, so
neither `kserU` nor `kserD` fires, and nothing marks the demand served.

### 103.2 Why the union of the two closures is not the node set

A node of the upward closure has `∃PPI` demands, whose witnesses lie in the
DOWNWARD closure **of that node** — not of the root. So the node set must be
closed under both step kinds, which is the mixed closure again.

### 103.3 The decomposition that does work

A mixed path is a sequence of maximal **runs**, each of one direction. Each run
is a chain, so §102's argument applies to it: **within a run the types are
distinct, so every run has length at most `|typeEnum C0|`.**

Hence

```
mixed path length  ≤  (number of runs) × |typeEnum C0|
```

and **the only open quantity is the number of runs** — the number of direction
switches along a path the closure extends.

### 103.4 What that localises

This is §92's route 3 ("bound the interleaving"), now the *only* remaining piece
of item A rather than one of three alternatives. Everything else is certified:
each run's bound (§102), the coverage given a fixpoint (§88), the counting
(§87), and both directions' machinery.

A switch point is a node carrying a non-kernel-served demand of one direction
having been reached by a step of the other. Nothing yet forces such points to be
few, and nothing yet forbids it — this is the honest open item.

Build: 30,231 lines, 1,515 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 104. THE COMPOSITION, CERTIFIED — down to one number

§103's hand argument is now a theorem, and the two halves are composed.

### 104.1 What was built

| | |
|---|---|
| `blocks_len_le` | `S` blocks each advancing by `≤ N` reach `≤ S·N`. **Axiom-free.** |
| `RunDecomp` | the decomposition as DATA: boundaries + each block same-direction |
| `mixedPath_len_le` | run-repeat-free path ⟹ `bnds S ≤ S · |typeEnum C0|` |
| `UniformBlocks` | each block's steps all `∃PP`-witnesses or all `∃PPI`-witnesses |
| **`mixedSkipPath_len_le`** | **the composition** — each block handed to §102's directional lemma, which is unconditional |
| `skipNodes_fixed_of_len` | fixpoint from a LENGTH BOUND, not from distinctness |
| `kserM` / `kserM_sound` | the mixed test: served up or served down |
| **`skipNodesM_fixed`** | **the mixed fixpoint** at `mixFuel C0 S = S · |typeEnum C0|` |
| **`skipNodesM_covers`** | **the mixed coverage** |

`skipNodes_fixed_of_len` is the piece that made the composition possible: §102's
fixpoints route through type-distinctness, which mixed paths do NOT have
(§103.1). Routing through a length bound instead accepts exactly what §104 can
prove.

### 104.2 The one remaining number

```
SwitchBounded C0 I S :=
  every mixed skip path decomposes into at most S same-direction runs
```

The decomposition is free — cut at each direction change. What is not free is
that `S` be a function of `C₀`.

### 104.3 What `wp107` measured

The probe runs the mixed closure with the Lean `persistDs`/`persistDsI` test
verbatim and counts direction switches.

* **Model size does not drive it.** Max switches 3 / 5 / 4 at universe sizes
  3 / 4 / 5 — noise, not growth.
* **`mdepth C₀` is REFUTED as the bound** — 55 violations in 11,469 samples,
  worst 4 switches at modal depth 1. This killed the hypothesis part D was
  built to support.
* `|vert-ex in cl C0|` violated 9 times; **`|cl C0|` never violated**, max
  switches 5, max path length 7.

The mechanism part D missed: a **cross-direction universal** (`∀PP.(∃PPI.E)`)
regenerates a demand of the OPPOSITE direction, whose own guard
(`∀PPI.∃PPI.E`) can fail — so the demand is regenerated AND one-shot. That is
the alternation engine, and it is why depth is not a measure.

### 104.4 The budget route is closed

Dropping the budget at a switch would bound the run count for free.
`hbS` does not forbid it — it constrains only DISJOINT pairs, and vertical
pairs are not disjoint. `ee_all` does: it fires on every pair of the declared
`odNet`, including transitively-related ones, so a node many switches down
would owe a universal body deeper than its budget. This is why `ppNodes_bud`
keeps budgets constant, and it is a real obstruction, not an oversight.

Build: 30,440 lines, 1,529 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 105. `SwitchBounded` PROBED TWO WAYS — bounded, and the bad case is real

`wp108` attacks §104.2's one number directly, since random sampling (`wp107`)
cannot force the adversarial case.

### 105.1 The alternation engine, built on purpose

§104.3 identified the mechanism, so the probe builds it:

```
A ⊓ ∀PP.(∃PPI.B) ⊓ ∀PPI.(∃PP.A) ⊓ ∃PP.⊤
```

Each cross-direction universal regenerates an opposite-direction demand whose
own guard can fail — regenerated *and* one-shot, so neither modal depth nor a
kernel touches it.

| universe | 3 | 4 | 5 | 6 |
|---|---|---|---|---|
| max switches | 4 | 5 | 4 | 4 |
| max path | 7 | 8 | 8 | 6 |

**No growth.** A hill-climbed champion (`mdepth 3`, `|cl C0| = 8`) reached 6
switches at universe 4 and then 5, 5 at universes 5 and 6 — also no growth.

### 105.2 But the bad case is NOT vacuous

**27.6%** of sampled concepts (1,079 of 3,912) exhibit a MIXED type repeat on a
reachable path — §103.1's configuration, where neither `kserU` nor `kserD`
fires. So the mixed closure genuinely walks past type repeats; it simply does
not do so unboundedly often.

### 105.3 Reading it

Evidence for `SwitchBounded`, not proof: finite set models, randomized search.
What it does establish is that the two obvious ways to refute it — grow the
model under a fixed concept, and build the engine that defeats the depth
measure — both fail.

Two routes remain, and the probe says the first is not doomed:

1. **Prove the bound.** `|cl C0|` was never violated across `wp107`+`wp108`
   (champion: 6 switches at `|cl C0| = 8`). No proof mechanism identified —
   modal depth is refuted (§104.3) and no other monotone quantity has been
   found.
2. **Fold.** Serve a mixed repeat from the existing same-type node. `ee_all` is
   free (equal types have equal labels), and the frame is declared rather than
   read off, so the relation is free too. The cost is re-proving acyclicity of
   the declared order — which is §39's mixing ordering cycle, the one the
   campaign has already paid for once.

A third, cheaper option worth noting: the extraction CHOOSES witnesses
(`Classical.choose`). Preferring a witness already in the closure would avoid
switches outright — the "late picking" discipline of `pp_witness_all_below`.
Untested.

## 106. LATE PICKING — a strengthener, not a finisher

`wp109` tests §105.3's route 3: when serving a one-shot demand, prefer a
witness ALREADY in the node set. Sound by construction — the preferred witness
is a genuine model witness with the real relation and the real label, just a
different choice than `Classical.choose` makes.

### 106.1 It helps everywhere, and never hurts

| | greedy depth | late depth | greedy switches | late switches | greedy nodes | late nodes |
|---|---|---|---|---|---|---|
| random (7,122) | 6 | **4** | 4 | **2** | 8 | **6** |
| engine, u=4 | 4 | 3 | 2 | 2 | 7 | 6 |
| engine, u=5 | 5 | 4 | 3 | **2** | 7 | **5** |
| engine, u=6 | 6 | **3** | 4 | **2** | 7 | **6** |
| champion, u=4 | 5 | 3 | 2 | **1** | 6 | 4 |
| champion, u=5 | 5 | 3 | 3 | **1** | 6 | 4 |
| champion, u=6 | 4 | 3 | 3 | **1** | 5 | 4 |

Demands served from the existing set: 26.9% (random), ~59% (engine), ~45%
(champion).

### 106.2 The finding that matters

**Under late picking the switch count is CONSTANT as the model grows; under
greedy it drifts up.** The engine goes 2 → 3 → 4 greedily across universes
4/5/6 and stays flat at 2 late; the champion goes 2 → 3 → 3 greedily and stays
flat at 1 late.

That drift is exactly the signal that would refute `SwitchBounded`. Late
picking removes it.

### 106.3 But it does not finish the job

Switches do not reach 0 — they settle at 1–2. So `SwitchBounded` is still a
hypothesis, not a triviality, and route 3 alone does not close the mixed
quadrant.

What it changes is the odds on route 1. `SwitchBounded` need only hold **for
the extraction we actually build**, not for arbitrary witness choice — and the
extraction is free to pick late. Proving a small constant bound for the
late-picking extraction is a strictly easier target than bounding switches over
all choices, and the only measurement that looked like growth was an artifact of
the choice discipline.

Secondary win: node counts drop by 20–35%, which feeds `mixKT` directly.

### 106.4 Scope

Finite set models, deterministic creation order, randomized search. "Constant
under growth" is three universe sizes, not a theorem.

## 107. THE CONSUMER — what it found

CLAUDE.md's method note, earned four times: **write the consumer before
believing the interface.** `skipNodesM_covers` was an interface; nothing had
used it. §107 makes the node set concrete (`MixCarrier` — the closure's own
members as a subtype) and derives the shape `mergedMT_ok`'s `he_ex` asks for.

### 107.1 It found a missing half immediately

`skipNodes` follows BOTH vertical directions — its match has a `.ex pp` arm and
a `.ex ppi` arm — but only the `∃PP` half had ever been read back out.
`skipNodes_covers_of_fixed` had no mirror. Added: **`skipNodes_covers_of_fixedI`**
and **`skipNodesM_coversI`**.

Six sections of machinery were built on a coverage lemma covering half the
demands. Nothing downstream was wrong, because nothing downstream existed.

### 107.2 The external disjunct comes out clean

```
mixCarrier_ex_pp  :  kserM e D = true  ∨  ∃ f, stepAll e f ∧ D ∈ mtk f
mixCarrier_ex_ppi :  kserM e D = true  ∨  ∃ f, stepAll f e ∧ D ∈ mtk f
```

with `mixStep_of_stepAll` putting the pair in the declared order, so `odNet`
reads `pp` with **no composition discharged by hand** — the same dividend
`odSeed` has paid throughout. The `∃PPI` case records the step in the other
orientation because `elt` always points up; `stepAll` already had both arms
(`ppStep e f ∨ ppiStep f e`), so this cost nothing.

### 107.3 The kernel disjunct does NOT come out — and why

`he_ex`'s other disjunct wants a KERNEL. `kserM` firing does not supply one:

* `KernelData` demands an **infinite** chain with `cstep : ∀ n, rho (c n) (c (n+1)) = cdir d`;
* `kserU` supplies a **finite** chain with a type repeat;
* cycling the finite chain fails at the wrap — `path 0` and `path j` have the
  same TYPE, not the same element, so `rho (path (j-1)) (path 0) = pp` is not
  available. This is exactly CLAUDE.md's standing note that `kernel_of_chain`
  gives a type repeat, NOT step structure.

**But the gap is bridgeable, and by an argument the type repeat makes cheap.**
If `∃PP.D ∈ mty(path 0)` and `mty(path 0) = mty(path j)`, then `∃PP.D ∈ mty(path j)`
too — so a D-witness exists above `path j`, and the segment can be re-run from
its own far endpoint. Iterating gives an infinite ascending chain meeting a
D-witness in **every** period, which is `ccovers`.

Note what this does NOT need: the guard `∀PP.(∃PP.D)`. The type repeat
substitutes for it. That is the whole point of the persistent/one-shot split
(§44.27) — persistent demands get their kernel from the guard, one-shot ones
from a repeat.

### 107.4 Next

**Segment iteration**: from a node whose type repeats along an ascending chain
carrying `D`, build `KernelData`. The ingredients are certified
(`rr_segment_from`, `rr_covers`, `seg_pp` and the descending mirrors); what is
new is the recursion that chains segments end-to-end, choosing each one
classically.

Build: 30,528 lines, 1,537 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 108. `kserU_sound` IS VACUOUS — §107.3 CORRECTED

§107.3 called the kernel gap "bridgeable cheaply". **That was wrong**, and
pursuing it exposed something worse than a missing lemma.

### 108.1 The finding

`kserU_sound : kserU C0 I m c = true → sat I m.x (∃PP.c)`.

But `∃PP.c ∈ mtk C0 I m.x m.k` **already** gives `sat I m.x (∃PP.c)`, by
`mem_mty`. `kserU_sound_is_vacuous` (now in the file, so the claim cannot drift
back into the record) proves exactly that conclusion with no mention of `kserU`.

**§102's fixpoint is real; its soundness is empty.** `kserU`/`kserD` TERMINATE
the closure but do not SERVE the demands they skip.

### 108.2 Why §107.3's bridge fails

The proposed bridge: `mty(path 0) = mty(path j)` so `∃PP.D ∈ mty(path j)` too,
hence re-run the segment from its far endpoint and iterate.

Equal types give the *first* step again — not the *segment*. The chain from
`path 0` followed demands `D_0, D_1, …`; at `path j` only `D_0` is guaranteed,
because the witness reached from `path j` need not have `mty(path 1)`. So the
segment is not repeatable and there is no period. This is uniformization (W2′)
in its original form, not a bookkeeping gap.

### 108.3 The tension, named

| test | serves the demand | terminates the closure |
|---|---|---|
| `persistDs` (the guard) | **yes** — certified kernel via `rrPt`/`rr_covers` | no |
| `kserU`/`kserD` (a repeat) | **no** (§108.1) | yes (§102) |

Neither test does both, and §§100–107 were built on the second.

### 108.4 Three independent lines now point the same way

1. **Late picking** (§106): switch drift disappears when the extraction chooses
   witnesses already in the set.
2. **This vacuity** (§108.1): the closure needs a test that both serves and
   terminates; `persistDs` serves, and termination would come from choosing
   short chains.
3. **`short_chain`** (already certified): any `ServeChain` can be replaced by
   one of length `≤ |typeEnum C0|` with the same `htype` — a "choose a better
   chain" theorem, useless while witnesses come from `Classical.choose`.

All three say: **witness selection must be a parameter of the construction, not
`Classical.choose`.**

### 108.5 What that refactor actually costs

65 declarations mention `ppWitness`/`ppiWitness`. But downstream uses **only
three properties** — `_rho`, `_bud`, `_arg` — plus the definition itself. So a
`WitSel` structure carrying those three fields, with the closures parameterized
by it, is a mechanical substitution rather than a re-proof: the existing
`ppWitness` becomes one instance, and every current result survives by
instantiating at it.

The risk is proportionate to 65 mechanical edits, not to 65 proofs.

Build: 30,556 lines, 1,539 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 109. WITNESS SELECTION IS NOW A PARAMETER

§108.4's conclusion, executed. `WitSel I C0` carries exactly the three
properties every downstream proof uses — `_rho`, `_bud`, `_arg`, in both
directions — and the closure is parameterized by it.

### 109.1 What landed

| | |
|---|---|
| `WitSel` | the selector: a real model witness, same budget, carrying the argument |
| `defaultSel` | the current behaviour as ONE instance |
| `skipNodesW` + 10 lemmas | the closure layer, parameterized |
| `SkipStepW` | the step relation, parameterized |
| `skipNodesW_covers_of_fixed` / `…I` | coverage, both directions |
| `skipNodesW_fixed_of_len` | §104's length-bound fixpoint, parameterized |
| **`skipNodesW_default`** | `skipNodesW (defaultSel I C0) = skipNodes` |
| **`SkipStepW_default`** | `SkipStepW (defaultSel I C0) = SkipStep` — by `rfl` |

The last two are the point: **every §§85–108 result is the `defaultSel` case of
what is now there.** Nothing was invalidated, nothing re-proved.

### 109.2 The cost claim, discharged by construction

§108.5 predicted "65 mechanical edits, not 65 proofs". The parameterized layer
was produced by textual substitution — `ppWitness` → `W.up`, `ppiWitness` →
`W.dn` — and every proof went through unchanged. The four fixes needed were all
syntactic:

* a lambda against an implicit binder must bind it (`fun n {_c} hF`);
* `rw [skipNodes]` unfolds by NAME, so it stays `rw [skipNodesW]`, not
  `rw [skipNodesW W]`;
* renamed lemmas take `W` first at their call sites;
* one grabbed line range ended inside the next declaration's docstring.

No mathematical content moved.

### 109.3 What this buys

`skipNodesW_fixed_of_len` now has a selector to quantify over. The two
selectors §108.4 identified can be built and their length bounds proved against
the same closure:

* **short** — witnesses on a chain of length `≤ |typeEnum C0|`, which is what
  `short_chain` already delivers for `ServeChain`;
* **late** — witnesses already in the set, which `wp109` measured as removing
  the switch drift entirely.

Neither is built yet. What changed is that building either is now possible: with
`Classical.choose` fixed, `short_chain` was certified and unusable.

Build: 31,055 lines, 1,558 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 110. THE DEBT, NAMED WHERE IT CAN BE DISCHARGED

`BoundedSel I C0 kser N` — a selector TOGETHER WITH the length bound its
choices earn:

```
sel   : WitSel I C0
bound : every path of non-served steps has length ≤ N
```

with `boundedSel_covers` / `boundedSel_coversI` deriving the closed closure at
fuel `N`, both directions.

### 110.1 Why the restatement is worth something

`SwitchBounded` (§104.2) quantified over ALL paths in a model — a claim about
the logic. `BoundedSel` is a claim about a **choice**, and `wp109` measured that
the choice changes the answer: switch drift vanishes under late picking.

**A hypothesis about a choice is discharged by making the choice. A hypothesis
about the logic is not.** That is the whole difference §109's parameterization
bought.

What is NOT claimed: that `defaultSel` extends to a `BoundedSel`. §108 is the
reason to doubt it.

### 110.2 Non-vacuity, honestly labelled

`boundedSel_of_no_vertical` — when `cl C0` has no vertical existential there are
no steps, so any selector is bounded at `N = 0`. **Axiom-free.**

This is a degenerate witness and is documented as one in the file. It certifies
that `BoundedSel` is inhabitable and that `bound` is a real obligation rather
than a contradiction. It does not suggest the interesting selectors are close.

### 110.3 Where the mixed quadrant now stands

| | |
|---|---|
| both directional fixpoints (§102) | certified |
| run decomposition + composition (§104) | certified |
| mixed fixpoint + coverage, given a bound (§104, §110) | certified |
| the consumer, external disjunct (§107) | certified |
| `∃PPI` coverage (§107.1, was missing) | certified |
| selector parameterization (§109) | certified, default case preserved |
| **a selector with a bound** | **open — `BoundedSel`, W2′-shaped** |
| the kernel disjunct (§108) | **open — same shape** |

The two open items are one item: both are the question of whether a choice can
be made uniformly enough. The campaign has known since 2026-07-15 that W2′ folds
into F6; §108 rediscovered it in the mixed setting, which is a consistency
check on the diagnosis rather than new bad news.

Build: 31,121 lines, 1,562 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 111. IS THE ROUTE BLOCKED? — no, and here is the check

A direct question deserves a checked answer rather than a characterization.

### 111.1 `short_chain` has never had a consumer

```
grep short_chain POFreeLift.lean
  6874  prose:  "...terminates by short_chain"
 20947  the theorem
 20972  prose
 20979  prose
 25376  #print axioms
 29752  §109 docstring
 30207  §110 docstring
```

**Every reference is prose or the statement itself.** `rr_covers`, by contrast,
is consumed — the persistent half genuinely works.

So the design (§44.27, and CLAUDE.md's summary of it) says one-shot demands
terminate by `short_chain`; `short_chain` was proved; and nothing ever used it.
§108 explains why — the witness was hard-wired, so "choose a shorter chain" had
nothing to act on. §109 removed that.

### 111.2 What is and is not blocked

**Not blocked.** W2′ for the PERSISTENT half is solved and used: `rr_covers` is
the campaign's real achievement, and it is a theorem precisely because dropping
∀PO lets the cross-relations coordinate.

**Open, and never claimed otherwise.** The ONE-SHOT half. Its intended
discharge is an `elt` edge inside a finite node set, bounded by `short_chain` —
not a kernel. §108's finding is that the implementation had drifted from that
design, substituting `kserU` for a serving test and getting a vacuous one.

So the diagnosis is "the design was not implemented", not "the design fails".

### 111.3 The real risk, named

`WitSel` is **per-demand and memoryless**; `short_chain` is **chain-valued**.
A selector that picks the head of a short chain does not remember to continue
along it. If threading `short_chain` through requires a chain-valued selector,
`WitSel` is the wrong shape and §109 needs a second pass.

That is cheap to find out and is the next step. It is a design question about
an interface, not a question about the logic.

### 111.4 Calibration

This project's ledger is seventeen reviews with a defect in all but two, and
this session alone refuted two of its own hypotheses (`mdepth` as the switch
bound, §104.3; "bridgeable cheaply", §108). "Not blocked" means no obstruction
has been identified — which on this project's record is a weaker statement than
it sounds.

## 112. THE CLOSURE THAT CUTS — termination with NO hypothesis

§110 named the debt as `BoundedSel.bound`. This section **proves it** for the
termination half.

### 112.1 The result

```
cutNodes_stable_typeEnum (W) (n) :
  cutNodes W [] n (|typeEnum C0| + 1) = cutNodes W [] n |typeEnum C0|
```

**For every selector `W`. No hypothesis. No kernel-service test.** The fuel is
computed from `C₀` alone.

### 112.2 Why it works where `skipNodes` could not

`skipNodes` is **node-indexed**: at a node it can only ask a test `kser n c`, so
"have I seen this type before on this path?" is unaskable — which is why §102
had to invent `kserU`, and why §108 found that invention vacuous.

`cutNodes` carries `seen`, the types already met on the current path, and stops
at a repeat. Then:

* `seen_full` — a repeat-free `seen` drawn from `typeEnum C0` and already as long
  as it admits no new type, by `nodup_len_le` on the extended list;
* the induction — each non-cutting step grows `seen` by one, so fuel plus `seen`
  covers the enumeration throughout.

No pigeonhole beyond `nodup_len_le`, which was already in the file.

### 112.3 What this does and does not settle

**Settles:** termination. §110's `bound` field is a theorem for the cutting
closure, so a `BoundedSel` no longer has to be assumed into existence.

**Does not settle:** that cutting loses nothing. `chain_cut` (certified) says a
demand served by `v` is equally served by any later chain member of `v`'s type —
which is exactly the coverage the cut needs — but it is not yet wired to
`cutNodes`. Until it is, the closure provably stops and is not yet proved to
stop *with everything served*.

That is the honest split: the half that was a hypothesis is now a theorem; the
other half is a wiring job against a certified lemma, not a new assumption.

Build: 31,272 lines, 1,568 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 113. THREE CERTIFIED THEOREMS, ZERO CONSUMERS — the actual diagnosis

Michael's redirect: *"you are inventing forms of blocking… just recall the
blocking experiences."* He was right, and checking it changes the diagnosis.

### 113.1 What I was re-deriving

`cutNodes` — stop expanding at a repeated type, keep the node — **is blocking**.
The project has had blocking since round 7, including the hard-won lesson
(`wp8_round7_blocking_chain.py`): blocking must be **occurrence-sensitive, not
equality**. Round 6 collapsed distinct laps via `L_Q(π,π) = EQ`; round 7's fix
tags laps `ι = up` and labels them `PP`, never `EQ`.

I re-derived the mechanism and then talked myself into calling its residue a W2′
obstruction.

### 113.2 The count

| theorem | real uses |
|---|---|
| `rr_covers` | **5** |
| `short_chain` | **0** |
| `pp_dichotomy` | **0** |
| `kernel_of_chain` | **0** |

Every reference to the bottom three is prose or `#print axioms`. `rr_covers` —
the persistent half — is genuinely consumed.

**Three certified theorems, all named in the design, none ever wired.**

### 113.3 Why this corrects §108

§108.2 argued the kernel gap is W2′-shaped because cycling a FINITE segment
fails at the wrap: `path 0` and `path j` share a type, not an element.

That argument is correct and irrelevant. `pp_dichotomy` does not cycle a finite
segment — its infinite branch produces `c : Nat → α` with `∀ n, I.rho (c n) (c (n+1)) = pp`,
a genuinely infinite chain of **real model elements**, which is exactly what
`KernelData.cstep` wants. `kernel_of_chain` then supplies `cty` at any depth.

So:

* **§108.1 stands** — `kserU_sound` is vacuous; that defect is real.
* **§108.3 / §110 / §111's framing was wrong** — the gap is not W2′. It is that
  `pp_dichotomy` was never connected to anything.

I reached for the wrong construction (cycle a finite segment) when the certified
one (take the infinite branch) was already in the file.

### 113.4 The corrected state

The mixed quadrant's vertical half is not blocked on new mathematics. It is
blocked on assembly: three certified theorems that the design calls for by name
and that nothing consumes. That is a different kind of work, and a much better
position than §§108–111 described.

Recorded as a process finding too: this is the fourth time this session I
called this gap something other than what it is (§107.3 "bridgeable cheaply",
§112.3 "wiring job", §§108/110/111 "W2′-shaped"). The corrective each time came
from checking the file rather than reasoning about it.

Build: 31,272 lines, 1,568 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 114. TWO OF THE THREE, WIRED

* `cutNodes_up_mem` / `cutNodes_dn_mem` — **every demand's witness is in the
  closure**, whether the step recursed or was cut (§113's fix makes a cut keep
  the witness). No hypothesis, any selector.
* `kernelData_of_chain` — `pp_dichotomy`'s infinite branch feeds
  `kernel_of_chain`, and out comes a `KernelData`. **This is the construction
  §108.2 called impossible.** §108.2 was cycling a finite segment, which does
  fail; `pp_dichotomy` hands over a genuinely infinite chain of real elements.

`short_chain` remains unconsumed.

## 115. WHAT `wp106` ALREADY SAID

Before building further, re-ran the probe that measures exactly this.

```
PART A -- is the closure CLOSED, and at what fuel?
   fuel   cases   CLOSED  unserved  mean |S|
      1     222      216         7       1.2
      2     222      220         2       1.3
      3     222      221         1       1.3
      4     222      222         0       1.3
```

**At fuel 4 the closure is closed in 222/222 cases** — every one-shot and
horizontal demand at every member has its witness inside the set — with
persistent vertical demands excluded because §49 serves those from the node's
own kernel. Worst `|S|` was 3 against a bound of 3.

Its own truncation audit reports 0 unserved-because-unreached and 0
unserved-because-outside, so the closure figure is not a truncation artifact.

### 115.1 What that does and does not license

It says the closure's one-shot half behaves: it closes, fast, small. It is
evidence the architecture is right, on finite set models.

It does not supply the Lean argument, and the reason is now sharp. In a finite
model the closure terminates because elements run out. In general the terminating
argument has to be `pp_dichotomy`: either some reachable node has no `∃PP`
demand, or there is an infinite chain — and the infinite chain is now a kernel
(§114).

### 115.2 The one item left in this half

`ccovers` for a NAMED demand. `kernelData_of_chain` builds the kernel at
`Ds = []`; the certificate wants `D` inside the period.

* **Persistent `D`:** `rr_covers` does it, because the guard keeps `D` available
  at every height so the round-robin can take each demand in turn. Certified and
  consumed.
* **One-shot `D`:** the guard fails by definition, so `D` need not recur, and a
  chain that picks an arbitrary demand per step has no reason to meet a
  `D`-carrier in its period. **The design does not ask a kernel to cover it** —
  §44.27 serves one-shot demands by an `elt` edge to a set member, and §114's
  `cutNodes_up_mem` puts that member in the set.

So the split is clean and the remaining question is narrow: **cut leaves.** A cut
leaf is kept but not expanded, so its own demands' witnesses are absent, and its
type equals an expanded ancestor's. That is precisely the blocking configuration,
and `wp8`'s round-7 lesson governs it — the lap is `PP`-labelled, never `EQ`.

Build: 31,375 lines, 1,571 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 116. CUT LEAVES, MEASURED — `wp110`

§115.2 named cut leaves as the narrow open item. Measured before building.

| | universe 5 | universe 6 | uniform rels |
|---|---|---|---|
| cut leaves arising | 379 | 288 | 159 |
| **A.** with UNSERVED demands | 12 (3.2%) | 13 (4.5%) | 20 (12.6%) |
| **B.** already served in-set | 367 (96.8%) | 275 (95.5%) | 139 (87.4%) |
| **C.** blocked lap CONTINUES | 1 (0.3%) | 2 (0.7%) | 1 (0.6%) |

### 116.1 A and B are actionable

Cut leaves with genuinely unserved demands **do arise** — 3–13%, not zero, so
§115's hope that the closure simply closes is wrong. But in 87–97% of cases the
set already contains a server with the right relation, so for those the repair
is a lookup, not a new node.

The residue is the remaining few percent.

### 116.2 C IS NOT TRUSTWORTHY, and the reason is in the memory file

C measures whether a blocked lap continues — i.e. whether from the cut leaf the
same demand path reaches another node of its own type. That is exactly what
turns a blocked lap into a kernel.

It reads ~0.5% and is stable across all three generators. **Stability across
generators is not evidence here, because all three are finite set models, and a
lap that continues indefinitely is precisely what a finite model cannot
represent.**

This is the `wp100` failure pattern recorded in memory verbatim: *a rate that
moves when the generator changes is a property of the generator — and before
believing any probe rate, ask what the model class CANNOT represent.* Finite set
models cannot represent the continuing lap. So C measures the model class, not
the logic, and **the conclusion "blocking-to-kernel fails" is NOT supported.**

### 116.3 The next step, precisely

Re-measure C over a model class that can carry infinite towers — the `wp101`
construction exists for exactly this reason and was built after `wp100` made the
same mistake.

Until then the honest statement is:

* cut leaves with unserved demands are real and rare (A);
* the set usually already serves them (B);
* whether the residue is rescued by blocking-to-kernel is **unmeasured**, and
  the number currently in hand does not bear on it.

No Lean was written against C. That is deliberate — §113's lesson was that four
misdiagnoses in one session all came from reasoning where checking was available,
and the check here is not yet valid.

## 117. `wp111` FAILED ITS OWN SANITY CHECK — numbers withheld

§116.3 called for re-measuring lap continuation over a class that can carry
infinite towers. `wp111` built one — an eventually periodic tower on its finite
quotient, aperiodic prefix `P_0 < … < P_{L-1}` below a periodic tail
`R_0 … R_{p-1}` — and declared in advance that the TAIL rate should read
near-100%, since residues recur cofinally by construction.

**It read 20.7% / 7.0% / 43.9%.**

### 117.1 The bug

The quotient orders residues by index: `R_s PP R_t` iff `s < t`. So from `R_s`
one can only reach residues of higher index and **can never return to residue
`s`** — which is precisely the cofinal recurrence the tail was supposed to
model. In the actual infinite tail every residue occurs above every residue; a
strict order on one copy per residue cannot express that.

So `wp111` is invalid for the same *kind* of reason as `wp100` and `wp110`: the
model class cannot represent the phenomenon being measured. Its prefix numbers
are not reported, because an instrument that fails its control does not get to
report its treatment.

### 117.2 Three instruments, three representational failures

| probe | class | why it could not measure lap continuation |
|---|---|---|
| `wp100` | finite set models | maximal element ⟹ no PP-successor |
| `wp110` | finite set models | a continuing lap needs an infinite tower |
| `wp111` | eventually periodic quotient | residues ordered by index ⟹ no return |

The question is genuinely hard to instrument. Each attempt failed differently,
and each failure was invisible until something forced it into the open.

### 117.3 What saved it this time

The expected tail rate was **written down before the run**. Had `wp111` reported
only a pooled figure — 38–44% prefix, which looks like a finding — nothing would
have flagged it.

Recorded as a probe-design rule: **state the control's expected value in advance,
and withhold the treatment when the control misses.** This is the companion to
the existing rule about varying the model class; varying the class does not help
when every class in the sweep shares the same blind spot.

### 117.4 Status of the question

Lap continuation is **unmeasured**. Nothing in §§110–111 bears on whether
blocking-to-kernel rescues the cut-leaf residue.

A correct instrument needs the tail's internal quantifiers computed in closed
form — `∃PP.X` at a tail node means *some residue satisfies X*, with no
representative order among residues — which is what `wp101` does for its chain
and what `wp111` discarded by imposing an index order.

No Lean has been written against any of these numbers.

## 118. LAP CONTINUATION, MEASURED AT LAST — `wp112`

Fourth instrument on one question. The first three failed on representation
(§117.2). This one's control held.

### 118.1 The control, and why the third attempt's was wrong

`wp112`'s first run also missed its control (89/98/75% where 100% was declared).
Diagnosing it showed the CONTROL was wrong, not the instrument: a node with no
ascending demand cannot continue by following demands however the tail is
represented — and such a node is not a problematic cut leaf either, since it has
nothing unserved.

So the two were separated:

* **control (representation)** — every tail residue has a `PP`-successor of its
  own type, namely itself at a higher lap. Pure structural check.
* **measurement** — among cut leaves that HAVE an unserved ascending demand,
  does the demand path reach a node of the leaf's own type? All witnesses
  explored; taking the first is a selector artifact.

**Control: 0 failures across all three shapes.** The closed-form tail is right.

### 118.2 The result

| shape | tail | prefix | side |
|---|---|---|---|
| L=4 p=3 | 98.1% | 55.6% | 0% |
| L=6 p=2 | 99.4% | 33.2% | 0% |
| L=2 p=5 | 94.0% | 52.4% | 0% |

### 118.3 What is and is not a finding

The prefix rate **moves with the model shape** (33–56%), so per the standing
rule it is a property of the generator and no single number should be quoted.
The pooled 67.9% is not a rate to cite.

What IS stable across all three shapes, and is the answer to §116.3:

> **Blocking-to-kernel is neither always available nor never available.** Tail
> leaves almost always continue (94–99%); prefix leaves often do not; side
> leaves never do (0/44).

So §114's `kernelData_of_chain` covers a large part of the cut-leaf residue and
**provably cannot cover all of it**. A cut leaf whose lap does not continue has
no infinite ascending chain through it, so there is no kernel to build — this is
structural, not a measurement artifact, and the side column (0%, three shapes,
44 leaves) shows it cleanly: a side node is not on the chain at all.

### 118.4 Consequence for the architecture

The cut-leaf residue splits again:

* **lap continues** ⟹ infinite chain ⟹ `kernelData_of_chain` (§114) ⟹ kernel.
  Needs `ccovers` for the named demand, which is `rr_covers` territory.
* **lap does not continue** ⟹ no kernel exists ⟹ must be served by an `elt`
  edge to a set member. `wp110` measured that 87–97% already are.

Neither branch is closed, but both are now the right shape, and neither is
"assume a hypothesis". The genuinely uncovered case is a cut leaf whose lap does
not continue AND which the set does not already serve.

## 119. THE DESIGN'S OWN DICHOTOMY, ASSEMBLED

§44.18 states it in prose, immediately above `ascend`:

> * if some node reachable by `∃PP` steps has NO `∃PP` demand, the chain
>   TERMINATES, and `short_chain` bounds it;
> * otherwise every reachable node has one, and iterating produces an INFINITE
>   ascending chain — which is a KERNEL.

Both halves were certified and neither was connected (§113).

```
chain_or_kernel (C0) (L0) (P) (hcl) (u) (hu) (hPu) :
  (∃ x, P x ∧ ∀ D, Concept.ex pp D ∉ mty C0 I x) ∨
    Nonempty (KernelData I C0 [] L0 true u)
```

plus `kernel_of_no_terminal` for callers that already know no reachable node is
demand-free. `pp_dichotomy` supplies the split; §114's `kernelData_of_chain`
turns its infinite branch into the kernel.

The descending mirror is **not** derived — `pp_dichotomy` is stated for `pp`
only and its `ascend` generator climbs. Recorded rather than silently assumed.

## 120. WHAT `short_chain` ACTUALLY SAYS — and why §112 was on-design

Reading `serveChain_cut` / `serveChain_cut_head` settles a question §§112–118
left open: the cut preserves only the chain's **head type**. Its docstring is
precise — "a demand served by the original head is served by the new one" — the
head is `u`'s SERVER, and shortening keeps a server of the same type.

So `short_chain`'s content is: **a chain with no droppable segment has pairwise
distinct types, hence length ≤ `|typeEnum C0|`.** That is an EXISTENCE statement
about chains.

`cutNodes` (§112) is the CONSTRUCTIVE version of the same content — it enforces
type-distinctness along every path instead of asserting a short path exists. So
§112 was not off-design after all; it is `short_chain` made into a construction,
which is exactly the gap §44.18 identifies ("`short_chain` gives EXISTENCE …
`mixNodes` is a CONSTRUCTION … the seam between them is where the fuel can run
out").

### 120.1 The consolidated picture

| step | status |
|---|---|
| closure terminates | **certified** — `cutNodes_stable_typeEnum`, any selector, no hypothesis |
| every demand's witness is in the closure | **certified** — `cutNodes_up_mem`/`_dn_mem` |
| cut leaves arise with unserved demands | measured, 3–13% (`wp110`) |
| 87–97% of those already served by a set member | measured (`wp110`) |
| lap continues ⟹ kernel | **certified** — `chain_or_kernel` (§119) |
| lap continues? | measured: tail 94–99%, prefix 33–56%, side 0% (`wp112`) |
| `ccovers` for a one-shot demand at a kernel | **open** |
| cut leaf, lap does not continue, set does not serve | **open** |

The two open rows are the whole remainder of this half. Both are narrow, both
are stated over certified surroundings, and neither is a hypothesis to assume.

Build: 31,433 lines, 1,574 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 121–122. THE ORIENTATION SPLIT — proved, and measured to cover 0% of the residue

### 121. Two of four combinations are free

A cut leaf `v` blocked by `a` with `mty v = mty a`. Four leaf/demand
combinations; two follow from `comp(PP,PP) = {PP}`:

| leaf sits | demand | |
|---|---|---|
| below blocker (`v ⊂ a`) | `∃PP` | **`blocked_below_inherits`** |
| above blocker (`v ⊃ a`) | `∃PPI` | **`blocked_above_inherits_ppi`** |
| above blocker | `∃PP` | residue |
| below blocker | `∃PPI` | residue |

`path_cut_below` — certified, previously used only inside `chain_cut` — is the
whole proof of both.

### 122. But `wp113` says they cover NONE of the residue

Classifying every unserved demand at a cut leaf by orientation:

**FREE: 0 (0.0%). RESIDUE: 100%.** All three sweeps.

The reason is not that §121 is wrong. Its cases were never IN the residue: if
`v ⊂ a` and `v` demands `∃PP.D`, then `a`'s own witness serves `v`, and `a` was
EXPANDED (that is what made `v` a leaf rather than `a`), so that witness is in
the set by `cutNodes_up_mem`. Such a demand is served before anything needs
repair.

So §121 explains the measured **"already served in-set" column (87–97%)** rather
than shrinking what is left. `blocked_below_served_in_set` /
`blocked_above_served_in_set` state that properly — conclusion is MEMBERSHIP in
the closure, not mere existence in the model.

### 122.1 The payoff: the residue is one shape, and the two open rows are one row

> a cut leaf `v`, blocked by `a`, carrying a demand pointing AWAY from `a` —
> `v ⊃ a` with `∃PP.D`, or `v ⊂ a` with `∃PPI.D`.

100% of what remains, structurally (not a rate). `comp(PPI,PP) = {PPI,PO,PP,EQ}`
forces nothing there, which is exactly why transitivity cannot reach it.

And for that shape `chain_or_kernel` (§119) applies at `v`: either some node
reachable from `v` is demand-free, or a kernel exists at `v` — landing on
§120.1's FIRST open row. **So the two open rows are the same question reached
two ways: `ccovers` for a one-shot demand at a kernel.**

That is a real consolidation. §120.1 listed two independent-looking gaps; there
is one.

Build: 31,557 lines, 1,578 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 123. THE DECLARED EDGE — serving the residue by label equality

§122.1 reduced everything to one shape: a cut leaf `v`, blocked by `a` with
`mty v = mty a`, carrying a demand pointing AWAY from `a`.

### 123.1 The route no earlier section used

**The frame is DECLARED, not read off the model, and `ee_all` reads only
LABELS.** Since `mty v = mty a`, leaf and blocker carry the SAME label — so a
universal at `v` imposes exactly the obligation it imposes at `a`, and `a` really
does have its witness `s` above it.

So declaring `v < s` discharges `ee_all` **even though the model may not relate
`v` and `s` at all**. That is round 7's blocking lesson in its proper form: the
lap is a `PP`-labelled edge between distinct occurrences, never an identification
(`wp8`).

Certified:

| | |
|---|---|
| `declared_edge_all` / `_ppi` | a universal at the leaf is satisfied at the blocker's witness |
| `declared_edge_serves` | the blocker's witness carries the leaf's demand |
| **`declared_edge_package`** | both, from `mty v = mty a` alone |

### 123.2 The obstruction, and `wp114`

The declared order is the transitive closure of the extraction's steps and must
stay a strict order (`mElt_irrefl`). Adding `v < s` cycles exactly when `s` is
already an ANCESTOR of `v`.

| | universe 5 | universe 6 | uniform rels |
|---|---|---|---|
| residue demands | 12 | 15 | 20 |
| declared edge AVAILABLE | **100%** | **100%** | **95%** |
| blocker has no witness (control) | 0% | 0% | 0% |
| only ancestors ⟹ cycle | 0% | 0% | 5% |

The control — "blocker has no `D`-witness at all", impossible when
`mty v = mty a` — read 0% as predicted. After §117's three failed instruments,
a probe whose control passed.

### 123.3 Where this leaves the vertical half

`declared_edge_package` supplies everything the edge needs **from label equality
alone**. What it does not supply is acyclicity, which is a property of the
extraction's step graph rather than of labels — the 5%.

So the single open question is no longer "how is a one-shot demand at a kernel
covered". It is:

> **can the extraction always choose a blocker-witness that is not an ancestor of
> the leaf?**

That is a statement about the step graph, it is measured at 95–100%, and it is
the kind of thing a witness-selection discipline decides — which §109 made a
parameter precisely so it could be decided.

Build: 31,633 lines, 1,582 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 124. THE DECLARED EDGE, FULLY TESTED — it did break something

Michael's caution (*"i hope the blocking thing goes through, given our bad luck
with blocking attempts earlier"*) was warranted, and acting on it found a real
break that §123's partial check missed.

§123 verified ONE obligation (`∀PP` propagation) and ONE obstruction
(acyclicity). `wp115` builds the whole certificate, adds the declared edges,
recomputes the ordered-disjoint closure and checks **every** obligation —
ODStruct axioms, composition closure, `ee_all` for every relation, `e_ex`.

### 124.1 The controlled result

Same 6,786 certificates, same seeds, edges off vs on:

| | unserved `∃PP` | unserved `∃PPI` | axiom violations |
|---|---|---|---|
| **control** (no edges) | 24 | 24 | 0 |
| **edges, as §123 stated** | 9 | 6 | **`ltNotDj` 1** |
| **edges + §124.2's condition** | 9 | 6 | **0** |

The edge fixes **33 of 48** unserved vertical demands (69%) across 34 uses.

### 124.2 What broke, and the repair

**`ltNotDj`** — comparable pairs must not be disjoint. The blocker's witness `s`
can be `DR` from the leaf `v` in the model; declaring `v < s` then makes a
comparable pair disjoint and the frame is no longer ordered-disjoint.

`declared_edge_package` does not see this, because it reasons from **labels**
and disjointness is not a label fact.

The repair is one more clause in the selection condition:

> choose a blocker-witness that is **neither an ancestor of the leaf nor
> disjoint from it**.

With it: `ltNotDj` 0, edge count unchanged at 34, coverage unchanged. The
condition costs nothing measured.

### 124.3 Two lessons, both already in the ledger

* **Partial checks pass.** §123 checked the obligation the route was designed
  around and the obstruction it anticipated. The break was in neither. This is
  the project's recurring shape — round 6's blocking passed its local checks too.
* **The control is what made it readable.** Edges-off gives 48 unserved and 0
  violations; without that column, "15 unserved, 1 violation" could have been
  read as the edge causing 15 failures rather than fixing 33.

### 124.4 Standing after this

* the declared edge is **not free** — it needs a two-clause selection condition,
  one of which was found only by full testing;
* with the condition it introduces **no measured violation** and removes 69% of
  the unserved residue;
* **15 unserved vertical demands remain** across 6,786 certificates — residue
  the edge does not reach.

Lean unchanged: 31,627 lines, 1,582 declarations, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 125. READ-OFF FOR THE VERTICAL ORDER — a regime distinction, not a reversal

The 15 demands still unserved in §124 turned out not to be residue at all: they
are demands the MODEL serves but the DECLARED frame does not, because the frame's
`lt` is the transitive closure of the extraction's own STEPS, so two nodes
related by real `PP` but never connected by a step come out `PO`.

Testing the obvious alternative — `lt` = the model's `PP` restricted to the node
set — over the same 6,786 certificates:

| mode | unserved `∃PP` | unserved `∃PPI` | other failures |
|---|---|---|---|
| control, no edges | 24 | 24 | none |
| declared edges (§124) | 9 | 6 | none |
| **read-off order + edges** | **3** | **2** | **none** |

48 → 15 → **5**. No ODStruct violation, no composition failure, no `ee_all`
failure in any mode.

### 125.1 Reconciling with `wp96` A

The design ledger rejects read-off (§42's route) on `wp96` A: 4.1% break. Its
stated reason is exact:

> Read-off is EXPRESSIVE (§42 was right about that) but forces UNIFORM budgets,
> and uniform budgets forfeit the budget-decreasing finiteness the whole `codes`
> pipeline consumes.

So the break is an interaction with **budget-dropping**, not with read-off as
such. And vertical steps **already** hold the budget constant — that is
`ppNodes_bud`, certified, and the reason §44.3 gives for keeping it.

So this is a **regime distinction**: read-off is safe exactly where the budget is
already uniform, which is the vertical closure, and the budget-dropping
horizontal recursion is untouched. The architecture that follows is a hybrid:

* **vertical order** — read off the model, at constant budget;
* **blocking laps** — declared edges, under §124.2's two-clause condition;
* **horizontal** — unchanged, budget-dropping, not read off.

### 125.2 Scope, stated plainly

`wp115` models only the constant-budget vertical part. Its "no `ee_all`
failures" is therefore a statement about that regime and **does not overturn
`wp96` A**, which measured the other one. Nothing here licenses read-off for the
horizontal closure.

### 125.3 What remains

**5 unserved vertical demands across 6,786 certificates**, down from 48. Not yet
characterised — and on this session's record, the characterisation is worth
measuring rather than reasoning out.

Lean unchanged: 31,627 lines, 1,582 declarations, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 126. THE VERTICAL EXTRACTION PASSES A FULL ACCEPTANCE TEST

```
certificates built and fully checked : 6786
of which carry a DECLARED EDGE       : 34
abandoned (no cycle-free choice)     : 0
closures that hit the step cap       : 0

ALL OBLIGATIONS HOLD:
  ODStruct axioms (ltIrr/ltTr/djSym/djIrr/ltNotDj/djDown)
  composition closure of odNet
  ee_all for EVERY relation
  e_ex for EVERY node
```

From 48 unserved demands in the control to **0**.

### 126.1 The three fixes it took, none of them reasoned out

Each surviving failure was diagnosed, not deduced, and each diagnosis named a
construction bug rather than a mathematical obstruction:

1. **`ltNotDj` (§124.2)** — the blocker's witness can be `DR` from the leaf.
   Fix: the selection condition gains "not disjoint from the leaf".
2. **read-off computed over the wrong node set** — declared-edge targets were
   added after the order was read off, so their relations were missing.
   Fix: read off over the FINAL node set.
3. **declared-edge targets never expanded** — a target is a node of the
   certificate and owes its own demands. Fix: run the closure from each target.

Bugs 2 and 3 were *my probe's*, not the design's; but both produced failures
that read exactly like residue, and §125 reported five of them as an open
question. They were not.

### 126.2 The cap check

`closures that hit the step cap: 0`. A silently-hit cap would have made the pass
empty — the closure would simply have stopped before generating the demands it
failed to serve. Worth stating because a passing acceptance test with a hidden
truncation is the most flattering possible artifact.

### 126.3 Scope — what this does NOT show

* **Vertical only.** The horizontal, budget-dropping recursion is not modelled.
  §125.2's boundary stands: nothing here licenses read-off horizontally.
* **34 edges.** The declared edge itself is lightly exercised. The pass is
  mostly evidence about the closure + read-off order, and only weakly about the
  blocking lap.
* **Finite set models.** Kernels — the infinite half — are not exercised at all;
  that half is certified separately (`rr_covers`, `chain_or_kernel`).
* **Not a proof.** It is the `wp16`/`wp94` acceptance pattern: build by the
  intended recipe, then check every obligation.

### 126.4 What it does show

On 6,786 instances the hybrid of §125 — read-off vertical order at constant
budget, blocking laps as declared edges under the two-clause condition, cut
closure for termination — produces certificates satisfying **every** obligation
`mtkKernelsOD` states, with no violation of the ordered-disjoint axioms and no
unserved demand.

That is the first end-to-end acceptance pass for the mixed quadrant's vertical
half.

Lean unchanged: 31,627 lines, 1,582 declarations, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 127. THE READ-OFF `ODStruct`, CERTIFIED

`wp115`'s acceptance pass runs on a hybrid whose vertical order is READ OFF the
model. `odOfModel` is that structure in Lean, and **it depends on no axioms at
all**:

```
odOfModel (hI : RCC5Interp I) : ODStruct {x : α // I.dom x}
  lt   x y := I.rho x y = pp
  disj x y := I.rho x y = dr
```

Every `ODStruct` axiom comes straight from composition:

| axiom | source |
|---|---|
| `ltIrr` / `djIrr` | `refl_eq` — a point is `eq` to itself, and `eq ≠ pp`, `eq ≠ dr` |
| `ltTr` | `comp(PP,PP) = {PP}` |
| `djSym` | `conv_`, and `conv dr = dr` |
| `ltNotDj` | **free** — `I.rho` is a FUNCTION, so a pair cannot be both `pp` and `dr` |
| `djDown` | two applications of `rho_forced`: `comp(PP,DR) = {DR}` then `comp(DR,PPI) = {DR}` |

`djDown` is the only one with content, and it uses exactly the two cells
`RCC5NormalForm.lean` uses for `dr_downward_closed` — the certified local algebra
harvested from the regular-cover pivot, now consumed here.

`odOfModel_frame` then gives composition closure of the whole net with nothing
discharged by hand, and `odOfModel_pp` / `_ppi` / `_dr` state the agreement with
the model that §125's 48 → 5 improvement was.

### 127.1 Why this does not reopen `wp96` A

This is the order at CONSTANT budget — the regime §125.1 identified, where
`wp96` A's objection (read-off forces uniform budgets, uniform budgets forfeit
budget-decreasing finiteness) does not bite, because `ppNodes_bud` already holds
the budget constant along vertical steps.

The horizontal, budget-dropping recursion neither uses `odOfModel` nor is
licensed to.

### 127.2 Standing

The Lean now carries every structural ingredient the §126 acceptance test uses:

| ingredient | Lean |
|---|---|
| closure terminates | `cutNodes_stable_typeEnum` |
| witness always present | `cutNodes_up_mem` / `_dn_mem` |
| read-off vertical order is an `ODStruct` | **`odOfModel`** (axiom-free) |
| its net is a frame | **`odOfModel_frame`** |
| declared edge's label obligations | `declared_edge_package` |
| lap continues ⟹ kernel | `chain_or_kernel` |

What is not yet in Lean: the two-clause SELECTION condition of §124.2 as a
proved side condition, and the assembly of these into a `MultiTierOk`.

Build: 31,703 lines, 1,587 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 128. WITH READ-OFF, THE CERTIFICATE REDUCES TO ONE QUESTION

The architectural payoff of §127, and what `wp115`'s 48 → 5 improvement
measured.

Under a DECLARED order (transitive closure of the extraction's steps), serving
`∃r.D` at `v` needs a node in the set AND a declared `v –r→ w` edge. Two nodes
the model relates but no step connects come out `PO`, so the demand goes
unserved even though the model serves it.

Under `odOfModel` the relation IS the model's, so the edge is automatic:

| obligation | now |
|---|---|
| `e_ex` ascending | `readoff_e_ex_pp` — reduced to MEMBERSHIP |
| `e_ex` descending | `readoff_e_ex_ppi` — likewise |
| `ee_all` `PP` | `readoff_ee_all_pp` — `mty_all` through `odNet_pp_inv` |
| `ee_all` `PPI` | `readoff_ee_all_ppi` |
| `ee_all` `DR` | `readoff_ee_all_dr` |
| `ee_all` `PO` | **absent** — `mty_no_all_po`, the fragment's defining property |

So every `ee_all` case and both vertical `e_ex` cases are consequences of the
FRAME rather than obligations to discharge.

### 128.1 What is left

> **which nodes are in the set?**

That is `cutNodes` plus the residue handling of §§123–126, and `wp115` answers
it affirmatively on 6,786 instances with every obligation checked.

It is also the one thing above that is **not** a theorem. The reduction is real
— the certificate no longer has five open obligations, it has one open question
— but the question is the constructive one, and constructive is where this
campaign's defects have always lived.

Build: 31,783 lines, 1,592 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 129. SESSION CLOSE — §§102–128 consolidated

### 129.1 The arc

| | |
|---|---|
| §§102–104 | the two directional halves COMPOSED, via a length bound rather than type-distinctness |
| §§105–107 | `SwitchBounded` probed; the consumer written, finding coverage existed for `∃PP` only |
| §108 | **`kserU_sound` is vacuous** — a real defect, now a theorem so it cannot drift back |
| §§109–110 | witness selection made a parameter; the debt named as `BoundedSel` |
| §§111–112 | `cutNodes` — termination with NO hypothesis, any selector |
| **§113** | **three certified theorems, zero consumers** — the diagnosis that reframed everything |
| §§114–120 | `chain_or_kernel` assembled; `short_chain` understood; the residue narrowed |
| §§121–122 | the orientation split — proved, covers 0% of the residue, and thereby merges the two open rows |
| §§123–124 | the declared edge; it broke `ltNotDj`, found only by full testing |
| §§125–126 | read-off as a regime distinction; **full acceptance pass, 6,786 certificates** |
| §§127–128 | `odOfModel` axiom-free; the certificate reduces to ONE question |

### 129.2 What is certified

Everything structural the acceptance test uses: termination, witness presence,
the read-off `ODStruct` and its frame, the declared edge's label obligations, the
dichotomy, and — under read-off — every `ee_all` case and both vertical `e_ex`
cases.

### 129.3 What is open

**Which nodes are in the set.** One constructive question, answered
affirmatively by `wp115` on 6,786 instances and not by a proof.

Also unchanged: the horizontal half's budget assignment (`hbS`/`hbK`/`hbQ`), the
encoding pipeline, and the descending mirror of `chain_or_kernel`.

### 129.4 Four corrections this session, all found by checking rather than reasoning

1. `mdepth C₀` as the switch bound — refuted by `wp107`.
2. "bridgeable cheaply" (§107.3) — wrong; the finite-segment cycle fails.
3. "W2′-shaped" (§§108/110/111) — wrong; the parts were merely unassembled.
4. Re-deriving blocking without consulting the project's own experience.

Plus three probe instruments that could not represent what they measured, and
two probe bugs that read exactly like residue.

**The pattern:** every correction came from grepping the file or re-running a
probe. None came from thinking harder about the mathematics.

### 129.5 Honest label

Unchanged. The ∀PO-free fragment is **not certified decidable**. Three quadrants
are; the mixed quadrant's vertical half now reduces to one constructive question
with an acceptance pass behind it, and its horizontal half and encoding remain as
before.

Build: 31,783 lines, 1,592 declarations, 676 `#print axioms` lines, exit 0,
0 errors / 0 warnings / 0 sorries / 0 `sorryAx`. `RCC5NormalForm.lean` and
`ForcingReduction.lean` still build.

## 130. THE WAY FORWARD — a five-step plan with the risk named

`wp115` run four ways settles which pieces are load-bearing:

| | unserved | diagnosis |
|---|---|---|
| declared order, no edges | 48 | mixed |
| declared order + edges | 15 | mostly "model relates them, frame says PO" |
| **read-off, no edges** | **37** | **ALL: cut leaf, witness in MODEL not in SET** |
| **read-off + edges + target expansion** | **0** | — |

So the two fixes are orthogonal and both required:

* **read-off** cures the RELATION problem — nodes the model relates that no
  extraction step connects;
* **declared edge + target expansion** cures the MEMBERSHIP problem — cut
  leaves whose witness was never added.

And the residual failure mode is now singular: *a cut leaf whose demand's
witness is not in the set.* Nothing else fails, in any configuration.

### 130.1 The plan

1. **`cutNodesR`** — `cutNodes` extended so that at each cut leaf, the blocker's
   witness is added AND expanded, chosen under §124.2's two-clause condition
   (neither an ancestor of the leaf nor disjoint from it).
2. **Termination of `cutNodesR`.** Each target's own expansion terminates by
   `cutNodes_stable_typeEnum`. What needs a measure is the NUMBER OF ROUNDS —
   targets generated at cut leaves of targets. **This is the risk.**
3. **`cutNodesR_covers`** — every member's vertical demand has a witness in the
   set: `cutNodes_up_mem` for expanded nodes, the target for cut leaves.
4. **Assemble `MultiTierOk`** from `odOfModel_frame` + `readoff_ee_all_*` +
   `readoff_e_ex_*` + (3). §128 already reduced every obligation but (3) to the
   frame.
5. **Run the existing pipeline**: `mergedExtraction_of_ok` →
   `mixedCompleteness_of_merged` → `decidableSat_pofree`.

Steps 1, 3, 4, 5 are assembly over certified parts. **Step 2 is the open
mathematics**, and it is the same shape as every previous open item in this
campaign: a termination measure for a construction that empirically terminates
(`wp115`: 0 cap hits on 6,786 instances).

### 130.2 What would falsify the plan

A concept forcing unbounded target rounds — cut leaves whose targets are
themselves cut leaves, indefinitely. `wp112`'s closed-form tower class is the
right instrument to look for one, since that is where laps genuinely continue.

Per §117.3, any such probe must state its control before the run.

## 131. STEP 2 IS REFUTED — `wp116`

§130 named step 2 as the risk and said to probe it before formalising. Done, and
it fails.

Over `wp112`'s closed-form eventually periodic tower, holding the period fixed at
`p = 3` and growing the aperiodic prefix `L`:

| prefix `L` | 4 | 8 | 12 | 18 | 26 | 40 |
|---|---|---|---|---|---|---|
| max rounds to close | 3 | 5 | 6 | 9 | 12 | **15+** |

Control held throughout (86–188 models per shape carried an unserved cut leaf in
round 0, so there was always something to expand). At `L = 40` **19 models hit
the round ceiling**, so 15 is a lower bound, not the maximum.

**The round count grows roughly linearly in the prefix length.** It does not
saturate.

### 131.1 What that kills

`cutNodesR` as specified in §130.1 — "at each cut leaf, add and expand the
blocker's witness" — does **not** terminate in a number of rounds computable from
`C₀`. The count is a property of the MODEL.

Note what it is NOT: it is not a type-count effect. The prefix's types are drawn
from three atoms, so at `L = 40` they repeat many times over, and the rounds grow
anyway. Each round's targets sit deeper in the prefix than the last, so the
construction tracks the model's depth.

### 131.2 What survives

Everything in §§127–128. The reduction of `ee_all` and vertical `e_ex` to the
frame is untouched — that was about `odOfModel`, not about the closure. So the
open question is still exactly "which nodes are in the set", and what is refuted
is one proposed answer.

§118's split predicted this: **tail** leaves' laps continue ~100%, **prefix**
leaves' 33–56%. Rounds grow with the PREFIX, which is where the laps do not
continue. The measurement is consistent with the structure already recorded.

### 131.3 Cost, and the reason to say so

One probe. §130 flagged step 2 as the risk and said to test it first; doing that
cost minutes instead of a session of Lean built on a false premise.

This is the third time in this campaign that probe-first has paid, and the first
time it has killed a plan I had already written down and committed.

### 131.4 Where to look next

Not another closure variant. The problematic leaves are exactly the prefix ones —
laps that do not continue — so the treatment has to come from the other two
branches already measured:

* **kernel** (`chain_or_kernel`), which covers leaves whose lap continues;
* **an existing set member**, which `wp110` measured at 87–97%.

The redesign question is whether those two together cover the prefix leaves
without spawning rounds. That is measurable before it is formalised.

## 132. THE REDESIGN — `wp117`: phases OR edge, and the rounds disappear

§131 killed target expansion because its round count grows with the model.
§131.4 said the treatment must come from branches that add nothing. `wp117`
measures exactly that.

### 132.1 Two treatments, neither of which adds a node

* **kernel phase** — a kernel contributes its PHASES to the certificate, so a
  leaf may be served by someone else's kernel. In the tower class the phases are
  the tail residues, and every tail residue is above every prefix node.
* **declared edge** — §123's, under §124.2's two-clause condition.

Measured separately and together, over `wp112`'s closed-form tower:

| | L=4 p=3 | L=8 p=3 | L=18 p=3 | L=8 p=6 | L=26 p=2 |
|---|---|---|---|---|---|
| phases alone | 96.7% | 91.6% | 91.1% | 95.9% | 87.3% |
| **phases OR edge** | **100%** | **100%** | **100%** | **100%** | **100%** |

Pooled: **3,218 / 3,218**. Control held throughout (tail leaves 100%, as
declared before the run).

The phases-alone column MOVES with shape (87–97%), so on its own it is a
generator property. The union does not move: it is 100% at every shape, which is
the strongest form this method produces.

### 132.2 The revised plan

1. `cutNodes` — certified terminating, any selector, no hypothesis
   (`cutNodes_stable_typeEnum`).
2. Cut leaves served by **kernel phase OR declared edge**. **Nothing is added,
   so there are no rounds** — §131's refutation does not apply.
3. Coverage theorem: every member's vertical demand is served by a set member, a
   kernel phase, or a declared edge.
4. Assemble `MultiTierOk` — §128 already reduced every other obligation to the
   frame.
5. `mergedExtraction_of_ok` → `mixedCompleteness_of_merged` →
   `decidableSat_pofree`.

The termination problem that killed §130 is **gone by construction**: the failing
step was "expand", and the redesign never expands.

### 132.3 What is still evidence rather than proof

Step 3. The 100% is an acceptance measurement over one model class with
randomized concepts, and the declared edge's two-clause condition is realised
approximately in the tower (ancestor via successor sets, disjointness via `DR`).

Two things make it stronger than the numbers §§105–118 produced: the control was
declared in advance and held, and the figure does not move across five shapes.
Two things keep it from being proof: it is one model class, and `wp115`'s
finite-set-model construction has not been re-run against the union.

### 132.4 Next

Re-run `wp115` — different model class, full obligation checking — with target
expansion replaced by phases-or-edge. If that also passes, step 3 is worth
formalising; if it does not, the disagreement between the two classes is itself
the finding.

### 132.5 "Nothing is added" — verified, not assumed

§132.2 claimed the redesign adds no node. That was worth doubting: `wp117`'s
`served_by_edge` searches the BLOCKER's witnesses, and nothing in it requires
the witness to be a set member. If the edge pulled in new nodes they would owe
their own demands, and §131's round problem would return by another door.

Measured over the same five shapes:

```
Of the demands the EDGE served (phases did not):
  witness ALREADY in the node set : 305
  witness is a NEW node           : 0
```

**305 of 305 in-set. Zero new nodes.**

And the reason is instructive rather than lucky: the witness `w` is an
`r`-successor of the BLOCKER, not of the leaf, so `w` sits in the closure
already — it was added when the blocker was expanded. What the demand lacks is
not a node but a RELATION, and that is precisely what the declared edge supplies.

So the redesign is better than §132.2 stated: the "declared edge" is not a new
node under a declared relation, it is an EXISTING set member under a declared
relation. `cutNodes_up_mem` already puts it there.

§131's refutation cannot recur, because there is nothing to expand.

## 133. §132.5 WAS WRONG — self-witnessing, and the redesign's "no rounds" is dead

Running the full `MultiTierOk` acceptance test (`wp118`) over the kernel-bearing
class exposed a defect in `wp117`, and it invalidates §132.5.

### 133.1 The defect

`wp118` reported `frame_q_conv` failures. Diagnosis, rather than guessing:

```
frame_q_conv (x, y, E[x,y], E[y,x], decl_xy, decl_yx):
  (('P', 1), ('P', 1), 'PPI', 'PPI', True, True)
```

**`x == y`.** The declared edge was picking the leaf ITSELF as its own witness.
`served_by_edge` searched the blocker's `r`-successors for a node carrying `D`,
and the leaf can be one — it is an `r`-successor of its own blocker.

That is round 6's lap collapse in miniature: a node identified with itself. The
project has had that defect on record since 2026-07, and my selection condition
permitted it.

### 133.2 What it invalidates

With `w ≠ v` forbidden, `wp117` re-run:

| | before | after |
|---|---|---|
| coverage, phases OR edge | 100% | **100%** |
| edge witness already in the set | 305 | **0** |
| edge witness is a NEW node | 0 | **305** |

**§132.5's "305 of 305 in-set, zero new nodes" was ENTIRELY self-witnessing.**
Every one of those 305 was `w = v`.

So **§132.2's "nothing is added, so there are no rounds" is FALSE.** All 305
edge-served demands require a new node, that node owes its own demands, and
§131's round problem returns exactly as before.

### 133.3 What survives

* **Phases alone, 87–97%** — unaffected. `served_by_phase` searches the TAIL,
  and a prefix leaf is never a tail residue, so self-witnessing was impossible
  there.
* **Coverage is real.** The residue IS coverable by phase-or-edge; what is dead
  is covering it *without adding nodes*.
* Everything in §§127–128 — the frame-level reduction — is untouched.

### 133.4 The control that caught it

`wp118` declared in advance: *if disabling the declared edges changes nothing,
the treatment is doing no work and a pass says nothing.* After the `w ≠ v` fix,
control and treatment became **identical** (37/42/336 both ways). The control
failed, and that failure is what sent me back to `wp117`.

Without that control the run would have read as five clean obligations and one
explicable DR artifact.

### 133.5 Standing

§130's plan and §132's redesign are **both refuted**, by the same mechanism:
serving a cut leaf needs a node that is not already there, and adding it spawns
rounds that track the model rather than `C₀`.

The open question is unchanged and now has two dead answers recorded against it.

## 134. REVISED PLAN — after two refutations

### 134.1 The methodological change, first

Both dead plans failed the same way: I found a coverage mechanism, measured
**coverage only**, and it collapsed when the full obligation set was checked.

* §130 → §131: coverage fine, TERMINATION grew with the model.
* §132 → §133: coverage 100%, but the witnesses were the leaves themselves, and
  `frame_q` caught it.

**Rule going forward: every candidate is measured with `wp118` — the full
`MultiTierOk` checker over the kernel-bearing class — not with a coverage
probe.** Coverage probes have now produced two false positives in two turns.
`wp117` should be treated as retired.

### 134.2 The one untested lever

`wp109` measured late picking's effect on DEPTH and SWITCHES. It never measured
the thing that matters here: **does a late-picking selector produce cut leaves
whose demands are already served?**

That is exactly what §109's `WitSel` parameterisation was built for, and the
infrastructure is certified:

* `WitSel` — the selector as a parameter, with `defaultSel` recovering current
  behaviour and `skipNodesW_default` proving nothing was invalidated;
* `cutNodes` takes any selector and terminates for all of them
  (`cutNodes_stable_typeEnum`).

So the selector can be changed without touching a single downstream proof. That
is the cheapest remaining move and it has never been tried on this question.

### 134.3 The plan

1. **Build a late-picking selector in the probe** — when serving a demand,
   prefer a witness already in the partial node set — and run **`wp118`**, not a
   coverage probe.
2. If cut leaves stop carrying unserved demands: define `lateSel : WitSel` in
   Lean and prove the coverage theorem. Everything downstream (§§127–128) already
   holds for any selector.
3. If they do not: the remaining degree of freedom is one this campaign has not
   used — **completeness lets the extraction choose its model.** It must produce
   SOME certificate for a satisfiable `C₀`, not one for every model of `C₀`. That
   would need a model-normalisation theorem (pass to a sub-model with bounded
   prefix), which is genuinely new mathematics, not assembly.

### 134.4 Calibration

Two plans refuted in two turns, both of which I reported with more confidence
than they deserved. Step 1 is worth doing because it is cheap and the
infrastructure is already certified — not because I expect it to work. Step 3 is
named so that a failure at step 2 has somewhere to go, not because it is
sketched.

## 135. THE COLD RESPONSE — two real contributions, both checked

`papers/cold_attack_cutleaf/` came back with a 14-page note and three new probes
(`wp119`–`wp121`). All three reproduce locally. The note explicitly claims no
decidability proof.

### 135.1 Contribution 1 — my §131 refutation was of the wrong construction

`wp120`, fixed `C₀ = ∃PP.B0 ⊓ (R ∨ junk)`, growing fence length `L`:

| `L` | 4 | 8 | 12 | 18 | 26 | 40 |
|---|---|---|---|---|---|---|
| model nodes | 9 | 17 | 25 | 37 | 53 | 81 |
| target rounds | 2 | 4 | 5 | 8 | 11 | 16 |
| full-`mty` nodes | 9 | 17 | 25 | 37 | 53 | 81 |
| **support nodes** | **2** | **2** | **2** | **2** | **2** | **2** |

The growth §131 measured is caused by **full-type overlabelling**, not by `C₀`.
`mty` puts every locally-true subformula in the label — including existentials
from disjuncts that were never selected — and those junk demands spawn the
rounds.

`MultiTierOk` never requires `tauE e = mty …`; it requires the Hintikka closure
conditions. So **support-generated labels are permitted by the literal
obligations**, and `wp121` checks every non-vacuous field for a two-external,
zero-kernel support certificate on the fence family, with a negative control
(remove the witness ⟹ exactly one `e_ex` failure).

§131 stands as stated — expanding under `mty` labels does grow — but its
conclusion, that expansion is hopeless, does not.

### 135.2 Contribution 2 — the measure §104.3 said did not exist

Certified here rather than taken on trust, all **axiom-free**:

| | |
|---|---|
| `extremal_drops` | a `D`-MAXIMAL carrier does not itself carry `∃PP.D` — a carrier above it would be a carrier above `x` |
| `spectrum_mono` | going up cannot create an ascending demand |
| `extremal_strict` | so the ascending spectrum strictly decreases at an extremal step |
| `extremal_drops_ppi` | the descending mirror, stated because §119 recorded the mirror must not be assumed |

Consequence: a run of extremal ascending services is bounded by
`|{D : ∃PP.D ∈ cl C₀}|` — **computable from `C₀` alone**. §104.3 recorded, after
`mdepth` was refuted, that "no other monotone quantity has been found". This is
one, and choosing the witness EXTREMALLY is what makes it work — a selector
discipline, which §109's `WitSel` already parameterises.

### 135.3 What is unchanged

The note's own warning: a `PP` step may enlarge the DOWNWARD spectrum and a
later `PPI` step the upward one, so **mixed alternation evades a lexicographic
combination**. That is §103's switch count, unmoved.

And `wp121` validates one fixed fence family, not a general construction.

### 135.4 Net

Two of my own conclusions are corrected — §131's scope, and §104.3's "no
monotone quantity" — by an outside look that cost one packet. The deep item is
where it was.

Build: 31,850 lines, 1,596 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 136. SUPPORT + EXTREMAL, UNDER THE FULL OBLIGATION SET — `wp122`

§135's two assets, tested together and under the full field list rather than a
coverage measurement (the §134.1 discipline, adopted after two coverage probes
produced two false positives).

### 136.1 Result

| | L=4 | L=8 | L=18 | L=40 |
|---|---|---|---|---|
| **CONTROL, full-type labels** — max nodes | 8 | 13 | 22 | 44 |
| **support + extremal** — max nodes | **4** | **5** | **4** | **4** |
| support + extremal — failures | `e_ex` 5 | none | none | none |
| fixpoint failed to settle | 0 | 0 | 0 | 0 |

Control 1 held: full-type labels reproduce `wp116`'s growth (8 → 44). Support
labels are **constant at 4–5** across a tenfold prefix increase, on the
kernel-bearing tower, with every expressible `MultiTierOk` field checked.

1,709 models. **Five `e_ex` failures, all at L=4.** Zero elsewhere.

### 136.2 The risk was real, and the fixpoint answers it

Named before running: support labels make `ee_all` non-trivial, because a
universal at `x` must land in the label of every `r`-related node, and a support
label seeded from its OWN parent need not carry it. Complete types get this free.

It fired — `ee_all_PP`/`_PPI` at low rate — and the repair is a **support-closure
fixpoint**: propagate each universal to every `r`-related node's label and
re-run the Hintikka closure until nothing grows.

**It settles in all 1,709 models**, and closing under it removes every `ee_all`
failure. That is direct evidence on the note's stated open item — *"a
`C₀`-computable bound, or regular compilation, for support generated by
universals"* — though evidence only: settling on 1,709 models is not termination.

A separate probe bug was found and fixed on the way: my Hintikka closure omitted
`∀EQ.E ⟹ E` (EQ is identity), which produced ~55 spurious `ee_all_EQ` failures
per shape. That is `MultiTierOk`'s `kk_eq` case, and it was mine, not the route's.

### 136.3 What extremality is and is not worth here

Control 2 (arbitrary selection) gives the SAME node counts as extremal. So
extremality is not what bounds the node set — **support labels are.**

Extremality's value is the MEASURE (`extremal_strict`, §135.2): it bounds a
same-direction run by `|Arg_PP(C₀)|`. That matters for a termination PROOF, not
for the node count, and this probe does not exercise it.

### 136.4 Next

1. Characterise the five L=4 `e_ex` failures — smallest tower only, so plausibly
   degenerate, but §133 is a standing reminder about believing that.
2. Lean: define support labels, prove the Hintikka closure and the fixpoint's
   termination. §§127–128's frame results are stated about `mty` and need
   restating for support labels — the underlying facts are about the frame, so
   this is restatement, not re-derivation.
3. The alternation bound, which the note and §103 agree is the real theorem.

## 137. THE JOINT FIXPOINT — `wp122` closes

| | L=4 | L=8 | L=18 | L=40 |
|---|---|---|---|---|
| **CONTROL, full-type** — max nodes | 8 | 13 | 22 | 44 |
| **support + extremal** — max nodes | **4** | **5** | **4** | **4** |
| failures | **none** | **none** | **none** | **none** |
| joint fixpoint failed to settle | 0 | 0 | 0 | 0 |

1,709 models. Every expressible `MultiTierOk` obligation holds, node count is
constant across a tenfold prefix increase, and the control still grows 8 → 44.

### 137.1 What the last fix was, and why it matters

The residual failures were prefix externals whose demand had a model carrier but
no certificate node carrying it. Diagnosed rather than assumed: **the support
closure adds universal BODIES to labels, and a body can itself be an
EXISTENTIAL** — a demand arriving after the worklist has drained, which therefore
never gets a witness.

So support closure and witness generation must run to a **joint** fixpoint, each
re-triggering the other. Interleaved, every failure disappears.

That joint fixpoint is precisely the cold note's stated open item — *"support
generated by universals and mixed `PP`/`PPI` alternation"*. **It settles in all
1,709 models.** Evidence on the exact open question, and evidence only.

### 137.2 Three probe bugs, all mine, all found by diagnosing

1. Hintikka closure omitted `∀EQ.E ⟹ E` — ~55 spurious `ee_all_EQ` per shape.
2. Tail residues checked as externals — 12 spurious `e_ex`; a residue is a
   KERNEL PHASE whose demands are `k_ex`, and the "no carrier" cases were
   excluding the residue's own higher lap.
3. The uninterleaved fixpoint above.

None was a finding about the route. Each looked like one until diagnosed, which
is the same pattern as §§126 and 133.

### 137.3 Scope — what this is not

* **Externals-only.** Kernel-phase demands are excluded here; `wp118` models
  `k_ex`/`ke_all`/`kk_*` properly and has NOT been re-run against this
  construction. That is the next instrument.
* **One model class.** The closed-form tower.
* **Settling ≠ terminating.** 1,709 models is not a bound.
* **No Lean.** §§127–128's frame results are stated about `mty`; support labels
  need their own statements.

### 137.4 Next

1. Re-run `wp118` — proper kernels, full field list — against support + extremal
   + joint fixpoint.
2. If it holds: Lean. Define support labels, prove the Hintikka closure, restate
   the frame results, and attack the joint fixpoint's termination with
   `extremal_strict` as the same-direction measure.
3. The alternation bound remains the theorem both the note and §103 point at.

## 138. `wp123` — the growth result replicates; the kernel side needs a different instrument

wp118's full field list, fed wp122's construction.

| | L=4 | L=8 | L=18 | L=40 |
|---|---|---|---|---|
| **CONTROL, full-type** — max externals | 5 | 10 | 19 | 42 |
| **support** — max externals | **4** | **5** | **4** | **4** |
| CONTROL failures | `ek_all` 60 | 55 | 94 | **185** |
| support failures, after phase seeding | `k_ex`/`kk_PPI` | ″ | ″ | ″ |

### 138.1 What replicated

**Support labels remove the growth under the full field list too.** Externals
constant at 4–5 against a control growing 5 → 42, and the control's `ek_all`
failures grow 60 → 185 while support's do not. That is `wp122`'s result
reproduced by an independent checker.

### 138.2 One real fix

`ek_all` failed at a steady rate until diagnosed: **every kernel phase is part of
the certificate and owes a label**, but `build_cert` only labels residues that
happen to become witnesses, so an unvisited phase came out EMPTY. Seeding all
phases and re-closing removes `ek_all` entirely.

### 138.3 Where the instrument runs out

The residue is `k_ex_PPI` and `kk_PPI`, and it is **not trustworthy**:

`kk_PPI` requires a `∀PPI` in one phase to reach all phases. My propagation uses
`erel`, which returns the FIRST relation found and checks `PP` first — so for two
tail residues it always answers `PP` and a `∀PPI` never propagates among them.

That is §117's failure exactly: **the tail is a quotient where a residue is both
above and below every residue, and `erel` is a function.** The quotient cannot
represent it.

`k_ex_PPI` is partly real — an ascending kernel's DESCENDING demands must be
served by an external below it — and partly contaminated by the same defect.

### 138.4 Standing, honestly

* **Replicated and solid:** support labels remove the growth, under two
  independent checkers, with controls that grow.
* **Fixed:** phase labelling (`ek_all`).
* **Not measurable here:** the kernel's internal `PPI` obligations. A faithful
  test needs phases related by `cdir` and `Q` as `MultiTier` actually defines
  them, not by a quotient `erel`.

Per §117's rule I am not reporting the `PPI` numbers as findings. Building the
faithful kernel instrument is the next step; patching `erel` again is not.

## 139. `wp124` — the faithful kernel instrument, and it closes

`MultiTier` never asks for a phase-to-phase ATOM. It states the obligations
directly, and they are exactly what a non-functional quotient relation needs:
`kk_pp`/`kk_ppi` propagate to the phase **block**, `ek_all` to every phase,
`ke_all` back to externals. So the fix for §138 was not to patch `erel` but to
stop computing a phase-to-phase relation at all.

| | L=4 | L=8 | L=18 | L=40 |
|---|---|---|---|---|
| **CONTROL, full-type** — max externals | 5 | 10 | 19 | **41** |
| CONTROL failures | `k_ex_PPI` 15 | 33 | 36 | 21 |
| **support + extremal + joint fixpoint** — max externals | **4** | **5** | **4** | **3** |
| **failures** | **none** | **none** | **none** | **none** |
| fixpoint failed to settle | 0 | 0 | 0 | 0 |

1,019 models, every `MultiTierOk` field the model can express, faithful kernel.

### 139.1 Two construction steps that were simply missing

Both were found by diagnosing residues, and neither is a label question:

1. **A kernel generates EXTERNAL witnesses.** `k_ex`'s first branch is an
   external `f` with `K k f = r`; for an ascending kernel a DESCENDING demand
   can only be served that way, and the construction never produced one. This
   failed in the CONTROL too (`k_ex_PPI` 15–36), so it was never a support-label
   defect.
2. **A demand can require a PHASE to carry its argument.** When an external's
   carrier lies in the tail, `e_ex`'s second branch wants some phase to carry
   `D` — so extend that phase's label rather than trying to make a residue into
   an external. Same for a kernel's own ascending demand via the `cdir(up)`
   branch.

With both, every failure disappears while the control keeps failing and growing.

### 139.2 What this now supports

The §135 route — support-generated labels, extremal selection, joint
support/witness fixpoint — produces certificates satisfying **every expressible
`MultiTierOk` obligation** on a kernel-bearing class, with the external count
CONSTANT (3–5) against a control growing 5 → 41, and the fixpoint settling in
every model.

### 139.3 Scope, unchanged and stated again

* One model class (the closed-form tower), randomised concepts.
* Settling in 1,019 models is **not** termination — that remains the theorem the
  cold note and §103 both point at.
* No Lean. §§127–128's frame results are stated about `mty` and need restating
  for support labels.
* This is the `wp16`/`wp94` acceptance pattern. Four earlier acceptance passes in
  this session looked conclusive and three of them had a defect found later.

### 139.4 Next

Lean. Define support labels, prove the Hintikka closure, restate the frame
results, and attack the joint fixpoint's termination with `extremal_strict` as
the same-direction measure.

## 140. SUPPORT LABELS, IN LEAN

The observation §§135–139 turn on: **`MultiTierOk` never requires
`tauE e = mty …`** — only the Hintikka closure conditions. `SupportOk` is that
label, defined locally:

```
SupportOk I C0 x L
  sub  : ∀ c ∈ L, c ∈ cl C0
  sat_ : ∀ c ∈ L, sat I x c
  and_ : and c d ∈ L → c ∈ L ∧ d ∈ L
  or_  : or  c d ∈ L → c ∈ L ∨ d ∈ L
  eq_  : all eq c ∈ L → c ∈ L
```

| | |
|---|---|
| `supportOk_clash` | clash-freedom from SOUNDNESS alone — a literal and its negation cannot both hold. **`propext` only.** |
| `supportOk_nobot` | likewise |
| `supportOk_sub_mty` | a support label sits INSIDE the model type |
| **`mty_supportOk`** | **`mty` IS a support label** |
| **`mtk_supportOk`** | so is the truncation |

### 140.1 The compatibility theorem is the point

`mty_supportOk` / `mtk_supportOk` say the existing construction is the SPECIAL
CASE where the label happens to be everything true. Support labels **generalise**
§§127–128 rather than replacing them, so nothing already built is at risk.

The `∀EQ` clause is the only one needing an argument: `rho x x = eq` at an
in-domain point, so `mty_all` fires on the node itself. That is `MultiTierOk`'s
`kk_eq`, and it is the clause `wp122` was missing — ~55 spurious failures per
shape until it was added (§137.2).

### 140.2 What this gives and does not

**Gives:** the propositional obligations (`e_clash`, `e_nobot`, `e_and`, `e_or`
and the `k_` mirrors) for ANY support label, from its own closure. No model-type
reasoning, no hypothesis.

**Does not give:** `ee_all`, `ek_all`, `ke_all`, `e_ex`, `k_ex`. Those are
conditions BETWEEN nodes, and for support labels they are exactly what §137's
joint fixpoint computes. Whether it terminates is the open theorem — untouched
here. This section only makes the labels definable.

Build: 31,939 lines, 1,603 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 141. THE LABEL CLOSURE TERMINATES ON A FIXED NODE SET

§137's joint fixpoint has two halves that re-trigger each other: LABEL CLOSURE
and WITNESS GENERATION. This section proves the first outright, which isolates
the second.

| | |
|---|---|
| `totalSize` | total label size over a node list |
| `totalSize_le` | repeat-free labels inside `cl C₀` total at most `\|nodes\| · \|cl C₀\|` |
| `totalSize_lt_of_grow` | a step growing one label strictly increases the total |
| **`closure_stops`** | **an iteration whose every step grows the total cannot run past `\|nodes\| · \|cl C₀\|`** |

All three: **`propext` / `Quot.sound` only — no `Classical.choice`.**

The argument is a size bound, not an induction on the construction, so it is
independent of WHAT the closure propagates: universals, or anything else drawn
from `cl C₀`.

### 141.1 What is now isolated

**Proved:** on a fixed finite node set, label closure terminates in at most
`|nodes| · |cl C₀|` steps — computable from `C₀` and the node count.

**Open, and now the only open half:** node generation. Each closure round can
introduce an existential — a universal's body — whose witness is a new node,
enlarging `nodes` and restarting the count.

So §137's joint fixpoint terminates **iff the node set stabilises**. That is the
same question §§130–133 attacked and that the cold note names. This section does
not answer it. It removes the label half from it, which is worth doing because
until now the two were entangled and a failure in either looked like a failure of
the route.

Build: 32,013 lines, 1,606 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 142. MODAL DEPTH IS THE MEASURE — for support labels

§104.3 refuted `mdepth` as a measure and recorded *"no other monotone quantity
has been found"*. That refutation was about **full model types**: a full type
carries everything locally true, so a universal's regenerated demand keeps the
depth up and nothing descends.

A **support** label carries only what is owed — a demand's ARGUMENT and a
universal's BODY — and both are strictly shallower than the formula that produced
them.

`wp124` measures it: **412 of 412 generation steps strictly decrease the label's
maximum modal depth. Zero equal, zero larger.**

Now a theorem, all `propext`/`Quot.sound` only:

| | |
|---|---|
| `maxDepth`, `mem_maxDepth_le`, `maxDepth_lt` | the measure and its two facts |
| **`seed_depth_lt`** | **a generation seed is strictly shallower than the label that produced it** |
| `closure_depth_le` | the Hintikka closure does not undo it |
| **`generation_depth_le`** | **a chain of generation steps is at most `maxDepth` of the root label** |

### 142.1 Why the same measure fails on `mty` and works here

The difference is exactly one thing: `mty` contains `∃r.D` whenever it is TRUE,
so a universal that re-establishes a demand at the witness restores the depth. A
support label contains `∃r.D` only when something OWES it, and the only way to
owe it is as a body or an argument — which cost a modal level.

That is why §104.3's refutation and this theorem are both correct.

### 142.2 What is closed and what is not

**Closed:** the generation DEPTH — at most `mdepth C₀`, computable from `C₀`
alone and **independent of the model**. This is what §131 found false for
full-type labels.

**Not closed:** the branching factor. A node's label can hold several demands,
each generating a witness; that count is bounded by `|cl C₀|` per node, so the
product is C₀-computable too — but the two facts are not yet assembled into a
single node-set bound in Lean.

So the open item has shrunk from *"does the node set stabilise"* to *"assemble
the depth bound with the per-node branching bound"* — arithmetic over two facts
rather than a search for a measure.

Build: 32,155 lines, 1,612 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 143. THE NODE-SET BOUND, ASSEMBLED

§142 bounds the generation DEPTH by `mdepth C₀`; a node's label holds at most
`|cl C₀|` demands, so BRANCHING is bounded too. This section multiplies them.

| | |
|---|---|
| `genBound b d` | size of a tree of depth `d`, branching `b` |
| `genNodes` | the generation closure, over an abstract child function |
| `genNodes_length_le` | depth `d`, branching `b` ⟹ size ≤ `genBound b d` |
| **`genNodes_le_C0`** | **node set ≤ `genBound \|cl C₀\| (mdepth C₀)`** |

Both `propext`/`Quot.sound` only. Nothing is specific to support labels — it is
the counting `ppNodes_length_le` already does, stated once over an abstract child
function so the instantiation is a one-liner.

**The bound is computable from `C₀` alone and independent of the model** — which
is exactly what §131 showed FAILS for full-type labels.

### 143.1 The vertical half, as it now stands

| step | status |
|---|---|
| label closure terminates on a fixed node set | **certified** (§141) |
| a generation step strictly decreases modal depth | **certified** (§142) |
| generation depth ≤ `mdepth C₀` | **certified** (§142) |
| branching ≤ `\|cl C₀\|` per node | **certified** (§143) |
| node set ≤ `genBound \|cl C₀\| (mdepth C₀)` | **certified** (§143) |
| support labels are definable, `mty` is one | **certified** (§140) |
| every `ee_all` / vertical `e_ex` from the frame | **certified** (§128) |
| the read-off `ODStruct` and its frame | **certified** (§127) |
| **the support-label EXTRACTION** | **open** |

**The counting is done.** What is not done is the construction: a Lean
definition that, from a model of `C₀`, emits support labels and witnesses
satisfying `seed_depth_lt`'s shape, plus a proof that the result is a
`MultiTierOk`.

`wp124` runs exactly that construction and finds every obligation holds on 1,019
models. **The gap between that and a theorem is the extraction, not the bound.**

That is a materially different position from §134, where the gap was a measure
nobody could find.

Build: 32,236 lines, 1,617 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 144. THE SEED FUNCTION — the measure now applies to the real thing

§142's `seed_depth_lt` is stated over an abstract seed satisfying a shape. This
section supplies the concrete seed and discharges that shape, so the depth
measure applies to the construction rather than to a hypothesis.

```
seedOf r D L  =  D :: allBodies r L
```

What a witness OWES: the demand's argument, and the body of every `∀r` the parent
carries. Nothing else — that is the whole content of "support" as against
"everything true".

| | |
|---|---|
| `bodyOf` / `bodyOf_some` / `mem_allBodies` | the universal-body extractor |
| `seedOf_shape` | the seed has `seed_depth_lt`'s shape, by construction |
| **`seedOf_depth_lt`** | **so the concrete seed is strictly shallower than its parent label** |
| `seedOf_sub` | the seed stays in `cl C₀` |
| `seedOf_sat` | every seed member is TRUE at the witness — via `mty_all`, the same fact `readoff_ee_all_pp` uses |

All `propext`/`Quot.sound` only.

`seedOf_sat` is the one that matters for the construction being possible at all:
it says a support label can actually be BUILT on the seed, because the parent's
universals really do propagate to the witness.

### 144.1 Position

The depth measure is no longer conditional on an unspecified seed. It applies to
`seedOf`, which is what `wp122`/`wp124` implement:

```python
seeds = [D] + [e[2] for e in lab[x] if e[0] == "all" and e[1] == r]
```

That is `seedOf r D (lab x)`, line for line.

Still open: the closure that iterates it, and the proof that its output is a
`MultiTierOk`. But every ingredient the iteration consumes — the seed, its depth
descent, its `cl C₀`-membership, its satisfaction — is now certified.

Build: 32,315 lines, 1,626 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 145. THE HINTIKKA CLOSURE, AND THE WITNESS LABEL

§144 gives the seed; this section closes it into an actual support label.

`hclose` is structural recursion on the concept — keep it, decompose a
conjunction, follow a TRUE disjunct, take an `∀EQ` body. **No fuel:** every
recursive call is on a proper subformula.

| | |
|---|---|
| `self_mem_hclose` | a concept is in its own closure |
| `hclose_sat` | everything in the closure is TRUE at `x` |
| `hclose_sub` | and stays inside `cl C₀` |
| `hclose_and` / `hclose_or` / `hclose_eqbody` | the three closure properties |
| `hclose_supportOk` | **closing a true, in-`cl` concept gives a SUPPORT LABEL** |
| `hcloseL` / `hcloseL_supportOk` | the same for a seed list |
| **`witnessLabel_supportOk`** | **serving `∃r.D` at a node labelled `L` gives the witness a genuine support label** |

`hclose_eqbody` is `MultiTierOk`'s `kk_eq` — the clause `wp122` was missing, and
which cost ~55 spurious failures per shape until §137.2 found it. It is now
proved rather than remembered.

### 145.1 What `witnessLabel_supportOk` composes

```
witnessLabel_supportOk : SupportOk I C0 y (hcloseL I y (seedOf r D L))
```

Its hypotheses are exactly what a construction step has in hand: the demand is in
the parent's label, the parent's label is in `cl C₀` and true at the parent, the
relation holds, and the witness carries the argument. `seedOf_sub` and
`seedOf_sat` (§144) supply the rest.

So a construction step **provably produces a well-formed label** — and by §144's
`seedOf_depth_lt` that label is strictly shallower, and by §143 the node set it
generates is bounded by `genBound |cl C₀| (mdepth C₀)`.

### 145.2 What is left

The iteration itself: a Lean definition that repeats this step, plus the proof
that its output satisfies the BETWEEN-node obligations (`ee_all`, `ek_all`,
`ke_all`, `e_ex`, `k_ex`). §128 discharges the first and the vertical `e_ex` from
the frame; the kernel-side ones are what `wp124` exercises.

Every LOCAL ingredient is now certified. What remains is the assembly and the
kernel obligations.

Build: 32,657 lines, 1,638 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 146–147. THE CONSTRUCTION STEP, CERTIFIED

### 146. The step

`SNode` carries an element, its label, and the proof the label is a support
label. `sChild` serves one demand, and the child is **well-formed by
construction** — §145's `witnessLabel_supportOk` is literally its fourth field.

| | |
|---|---|
| `hclose_depth_le` / `hcloseL_depth_le` | the closure never deepens a formula |
| `sChild_rho` | the step is a real `r`-edge |
| `sChild_arg` | the child carries the demand's argument |
| **`sChild_depth`** | **the child's label is strictly shallower** — §142's measure, on the real step |

### 147. Normalised labels

`hcloseL` can repeat a formula, so a label's LENGTH is not bounded by `|cl C₀|`
outright — and the length IS §143's branching factor.

`normL C0 L = (cl C0).filter (· ∈ L)` fixes it without changing what the label
means: a support label is inside `cl C₀` anyway, so membership is unchanged, and
the result is a filter of `cl C₀`.

| | |
|---|---|
| `normL_len` | **length ≤ `\|cl C₀\|`, with NO `Nodup` hypothesis** — `propext` only |
| `normL_supportOk` | normalising changes nothing a support label says |
| `maxDepth_le_of_sub` / `normL_depth_le` | and cannot deepen |
| `sChildN_rho` / `_arg` / `_depth` / **`_len`** | the step with all four properties |

Avoiding `Nodup` matters: `hcloseL` gives no such guarantee, and proving one
would have meant a dedup with its own equality reasoning. Filtering `cl C₀`
sidesteps it — the bound comes from the filter, not from the label.

### 147.2 Position

A construction step now has, certified:

* the child is a well-formed support label;
* the edge is real and carries the argument;
* the label is **strictly shallower** (bounds depth by `mdepth C₀`, §142);
* the label is **at most `|cl C₀|` long** (bounds branching, §143).

Those are exactly `genNodes_le_C0`'s two inputs. **The step is done; what remains
is the iteration that repeats it and the between-node obligations.**

Build: 32,856 lines, 1,656 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 148. THE ITERATION, AND THE COVERAGE THEOREM

| | |
|---|---|
| `sNodes` | the support-label closure: a node, then its vertical demands' children at one less depth |
| `self_mem_sNodes` | |
| **`sNodes_length_le`** | **size ≤ `genBound \|cl C₀\| d`** — branching from `sChildN_len` |
| `sNodes_child_mem_pp` / `_ppi` | a served demand's child is in the closure |
| `no_demand_of_depth_zero` | a label of depth 0 has no demand — `∃r.D` has depth ≥ 1 |
| `sNodes_sub_of_child_pp` / `_ppi` | a child's closure sits inside the parent's |
| **`sNodes_covers_pp`** | **THE CLOSURE IS CLOSED, at fuel `maxDepth n.lab`** |

```
sNodes_covers_pp :
  ∀ d n, maxDepth n.lab ≤ d →
    ∀ m ∈ sNodes hI d n, ∀ D (hD : Concept.ex pp D ∈ m.lab),
      sChildN hI m hD ∈ sNodes hI d n
```

**The fuel comes from the root label's depth** — not guessed, not a hypothesis,
not a parameter to be discharged later. `maxDepth` of the root label is bounded
by `mdepth C₀` whenever the root label is (which `hclose` of `C₀` is).

### 148.1 Why the induction goes through

At depth zero there are no demands (`no_demand_of_depth_zero`). At `d+1`, a
member is the node itself — whose child is present by `sNodes_child_mem_pp` — or
lies in a child's closure, where `sChildN_depth` gives
`maxDepth child ≤ d` and the induction hypothesis applies.

**`sChildN_depth` is the whole engine**, and it is the measure §104.3 recorded as
not existing — correctly, for complete model types (§142.1).

### 148.2 What this is, and is not

**Is:** a terminating, size-bounded, PROVABLY CLOSED vertical closure over
support labels, with every bound computable from `C₀`. That is what §§130–133
tried and failed to get for `mty` labels, twice.

**Is not:** a `MultiTierOk`. Still outstanding —

* the `∃PPI` mirror of `sNodes_covers_pp` (symmetric, not yet written);
* the BETWEEN-node obligations — `ee_all` and vertical `e_ex` come from the
  frame (§128), but that is stated about `mty` and needs restating for support
  labels;
* the kernel obligations (`ek_all`, `ke_all`, `kk_*`, `k_ex`), which `wp124`
  exercises but nothing proves.

Build: 33,011 lines, 1,665 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 149. WHAT IS LEFT — a field-by-field count

`mixedCompleteness_of_merged` is certified, so **`MergedExtraction` is the only
thing between the fragment and `Decidable (Satisfiable C0)`**. That means:
produce a `MultiTierOk` from a satisfiable `C₀`, within the `mixKT` bounds.

### 149.1 The 19 `MultiTierOk` fields, against support labels

| field | status |
|---|---|
| `hp` | trivial |
| `e_clash`, `e_nobot` | **certified** — `supportOk_clash`/`_nobot` |
| `e_and`, `e_or` | **certified** — `SupportOk` fields |
| `k_clash`, `k_nobot`, `k_and`, `k_or` | **certified** — same lemmas, once phases carry support labels |
| `kk_eq` | **certified** — `SupportOk.eq_` / `hclose_eqbody` |
| `frame_q` | **certified** — `odOfModel_frame`, modulo wiring the kernel into `qnet` |
| `e_ex`, vertical | **certified for the closure** — `sNodes_covers_pp`; needs the `∃PPI` mirror and restating §128 for support labels |
| `ee_all` | **OPEN** — the substantive one |
| `ek_all`, `ke_all`, `kk_pp`, `kk_ppi`, `kq_all`, `k_ex` | **OPEN** — the kernel side |

Ten fields have their support-label proof. One (`ee_all`) is the substantive
vertical gap. Six are kernel-side.

### 149.2 The three remaining pieces, by kind

**(a) Mechanical.** The `∃PPI` mirror of `sNodes_covers_pp`; restating §128's
frame results (`readoff_ee_all_*`, `readoff_e_ex_*`) for support labels; and the
`Fin`-indexed assembly into `MergedExtraction`'s exact shape. Each is a
transcription of something already proved.

**(b) `ee_all` for support labels — the substantive vertical item.** Under
read-off relations `E e f` fires on many pairs, and a support label seeded from
its own parent need not carry another node's universal. `wp122`/`wp124` fix this
with a joint label/witness fixpoint that SETTLES in 1,709 and 1,019 models.
§141 bounds the label half and §148 the node half; **the interleaving is not
formalised**, and that is the work.

**(c) The kernel side.** Six fields. `chain_or_kernel` (§119) produces kernels
and `rr_covers` serves persistent demands, but neither is connected to support
labels, and `wp124`'s two missing construction steps (§139.1) have no Lean
counterpart at all.

**(d) The horizontal half.** `mergedMT_ok`'s `hbS`/`hbK`/`hbQ` budget
hypotheses — CLAUDE.md calls them "a choice inside the extraction, not a fact to
discover". Untouched this session.

### 149.3 Calibration, which matters more than the count

This session produced four self-refutations, three retired instruments, two
plans killed after being committed, and one result reported confidently that its
own follow-up test destroyed. **Every estimate of remaining work I have made on
this problem has been wrong in the optimistic direction.**

So: (a) is small and I would say so. (b) has a measured construction and two
bounded halves, which is the best position any open item has had. (c) is
genuinely unexplored in Lean. (d) has been outstanding since 2026-08-22 and
nothing this session touched it.

I will not put a session count on (b), (c) or (d).

## 150. THE DESCENDING MIRROR, AND `ee_all` REDUCED TO TERMINATION

§149.2(a) first, then a real reduction of (b).

### 150.1 Mechanical, done

`sNodes_covers_ppi` — §148's coverage theorem mirrored. Same induction, same
engine (`sChildN_depth`), other direction.

### 150.2 `ee_all` is a TERMINATION question, not a soundness one

| | |
|---|---|
| `support_all_sat` | a universal in a support label holds at the source, so its body holds at every `r`-target — `mty_all`, nothing about the frame |
| `support_all_cl` | and the body is in `cl C₀` |
| **`support_extend`** | **so adding it to the target's label KEEPS a support label** |

Every step the §137 fixpoint takes is **legal**. What was never in doubt is now
proved; what remains is that it stops.

### 150.3 And propagation cannot escalate the generation measure

The obvious way termination could fail: propagation deepens a target's label,
which restarts §148's depth-bounded generation.

| | |
|---|---|
| **`support_extend_depth`** | a propagated body is strictly shallower than its SOURCE label, so extending cannot push the global maximum depth up |
| `depth_invariant` | so if every label starts within `M`, every label stays within `M` |

Stated as an invariant rather than a construction, so it holds for **any**
interleaving of generation and propagation.

### 150.4 Position on (b)

* **sound** — every propagation step keeps a support label;
* **depth-bounded** — propagation cannot deepen past the start, so with a root
  label of depth `≤ mdepth C₀` every label stays there;
* **open** — that the interleaved iteration STOPS.

§141 bounds the label half on a fixed node set. §148 bounds the node half for a
fixed label scheme. §150.3 now rules out the two escalating each other's measure.
**What is missing is the combined induction** — a smaller gap than §149.2(b)
described, because the escalation failure mode is excluded rather than merely
unobserved.

Build: 33,154 lines, 1,671 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 151. WHERE THE COMBINED INDUCTION CLOSES — and where it does not

§150.4 left one gap: that generation and propagation, interleaved, STOP. Both
halves are bounded and §150.3 rules out escalation. What is not bounded in
general is the NODE COUNT, because **a propagated body can itself be an
existential** — a new demand, hence a new child, hence a taller tree.

### 151.1 The case that closes

`ShallowAll C0` — no universal in `cl C₀` has an existential body. Decidable from
`C₀`.

| | |
|---|---|
| `shallowAll_no_new_demand` / `_extend_no_demand` | propagation adds no demand |
| **`shallowAll_closure`** | bounded, and closed in BOTH vertical directions |

Under `ShallowAll`, the closure computed once is already the final node set and
the interleaving question does not arise.

### 151.2 Honest scope, stated plainly

`shallowAll_closure` is **not** conditional on `ShallowAll` — §148's theorems
never were. What `ShallowAll` buys is only that the §150 fixpoint adds no demand.

**And `ShallowAll` excludes `∀PP.(∃PP.A)` — which is exactly the tower-building
shape.** So the sub-fragment is real but is not the interesting half. It is
recorded as a partial result, not dressed up as more.

### 151.3 The vertical half

| | |
|---|---|
| bounded, closed, both directions | **certified, unconditionally** |
| propagation sound | **certified** (§150) |
| propagation depth-bounded | **certified** (§150) |
| propagation adds no demand | **certified under `ShallowAll`** |
| propagation adds no demand, GENERAL | **open** |

The last row is the whole of §149.2(b) that remains, and it is now one sentence
rather than a region: *can propagation introduce unboundedly many demands?*
`wp124` says no on 1,019 models — external counts 3–5, constant while the control
grows 5 → 41 — but that is measurement.

Build: 33,231 lines, 1,675 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 152. WHY `ee_all` NEEDS TRANSITIVE INHERITANCE — and why the measure fails where it should

Chasing §151's one sentence turned it into something sharper, then resolved it.

### 152.1 What `ee_all` actually still needs

`seedOf` already gives a witness the bodies of its PARENT's matching universals,
so propagation from the parent is done at creation. What remains is propagation
from NON-parents — and under read-off relations the commonest is an
ANCESTOR-OF-ANCESTOR, since `PP` is transitive.

The grandparent's universal must reach the grandchild, but `seedOf` gave the
parent only the BODY `E`, not `∀PP.E`, so the parent has nothing to pass on.

The fix is forced and sound, and now certified **axiom-free**:

| | |
|---|---|
| `all_pp_inherits` | `∀PP.E` at `x` and `x PP y` ⟹ `∀PP.E` at `y` — `comp(PP,PP) = {PP}` |
| `all_ppi_inherits` | the mirror |

### 152.2 The cost, and why it is not a defect

`mdepth (∀PP.E) = mdepth E + 1` — the same depth it had in the parent. So an
inherited universal does NOT lose a modal level and **`seedOf_depth_lt` fails for
it.** That is the engine of every bound since §148.

Working the candidate measure through settles what that means. Take `x` carrying
`∀PP.(∃PP.A)` and a demand `∃PP.B`: the witness inherits the universal, receives
its body `∃PP.A`, and so has a demand at the SAME depth. No measure decreases.

**But that is the tower.** `∀PP.(∃PP.A)` is exactly the guard of `persistDs`, and
§44.27's persistent/one-shot split sends such a demand to a **kernel**, not to a
chain of externals. The measure fails precisely where the kernel takes over —
the design working, not the measure being wrong.

### 152.3 The synthesis

**Restrict the closure to non-persistent demands, and the depth measure survives
inheritance on what is left.**

That is what `cutNodes`/`skipNodes` were built to do (§§86.3, 112). What is new is
that with SUPPORT labels the measure actually works on the remainder — for `mty`
labels it did not (§§131, 142.1), which is why those closures needed `kserU` and
why `kserU_sound` turned out vacuous (§108).

Ingredients, all certified: `persistDs` and `mem_persistDs`, `all_pp_inherits`,
`seedOf_depth_lt`, `sNodes_covers_pp`/`_ppi`.

Two independent lines — the campaign's own persistent/one-shot split, and the
cold note's support labels — meet here.

Build: 33,300 lines, 1,677 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 153. AN INHERITED BODY IS PERSISTENT — the tension resolves

§152.2's counterexample to the depth measure: a parent carrying `∀PP.(∃PP.A)`
passes the witness a demand at the SAME depth, so nothing decreases.

It is not a counterexample. The witness also inherits `∀PP.(∃PP.A)` **itself**
(§152, `all_pp_inherits`), and that is exactly the guard `persistDs` tests.

| | |
|---|---|
| **`inherited_body_persistent`** | a `PP`-witness of a parent carrying `∀PP.(∃PP.D)` has `D ∈ persistDs` |
| `inherited_body_persistentI` | the descending mirror |
| `inherited_body_persistent_lab` | and a support LABEL sees it, so it applies to the construction |

**Every demand that could break the measure is persistent, hence kernel-served,
hence skipped by a closure obeying §44.27's split.** What the closure actually
follows comes from the demand's ARGUMENT, which is strictly shallower.

### 153.1 The tension, resolved in the split's favour

| | |
|---|---|
| transitive inheritance is needed for `ee_all` | §152, certified |
| inheritance breaks the depth measure | §152.2 |
| **the demands it breaks it on are persistent** | **§153, certified** |
| so the measure holds on what the closure follows | the construction to build |

The last row is a `sNodes` variant skipping `persistDs` members, plus its
coverage theorem in §148's shape. Every ingredient is certified.

### 153.2 What is NOT claimed

That persistent demands are **served**. They are kernel-served, and the kernel
side is §149.2(c) — six `MultiTierOk` fields, still untouched in Lean.

This section removes an obstruction to the vertical measure. It does not build a
kernel.

Build: 33,404 lines, 1,680 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 154. THE SPLIT CLOSURE — the vertical extraction

§153 showed every demand that breaks the depth measure is persistent. `pNodes`
acts on that: follow a vertical demand only when it is NOT kernel-served —
exactly §44.27's split, now over SUPPORT labels where the measure works.

| | |
|---|---|
| `pNodes` | the split closure |
| `self_mem_pNodes` | |
| **`pNodes_length_le`** | size ≤ `genBound \|cl C₀\| d` — skipping only removes branches |
| `pNodes_child_mem_pp` / `_ppi` | a NON-persistent demand's child is present |
| `pNodes_sub_of_child_pp` / `_ppi` | a child's closure sits inside the parent's |
| **`pNodes_covers_pp`** | **closed on the non-persistent half, at fuel from the root label's depth** |

### 154.1 The vertical half, assembled

| | |
|---|---|
| the split closure, size-bounded | **certified** |
| closed on the non-persistent half | **certified** |
| every label is a support label | **by construction** — `SNode`'s fourth field |
| the depth measure holds on what it follows | **certified** (§153) |
| transitive inheritance for `ee_all` | **certified** (§152) |
| persistent demands go to a kernel | **§149.2(c), no Lean at all** |

**This is the vertical extraction §§130–133 twice failed to get.** Both earlier
attempts died on termination; this one terminates because the measure survives —
and the measure survives because support labels carry only what is owed, and
because the demands it cannot handle are exactly the ones the split removes.

### 154.2 What is not done

* the `∃PPI` mirror of `pNodes_covers_pp` — mechanical, unwritten;
* the KERNEL side — six `MultiTierOk` fields, no Lean;
* the between-node `ee_all` fixpoint — §150 proved it sound and depth-bounded,
  §152 supplied inheritance, but the iteration is not written;
* the horizontal half's budget hypotheses — untouched since 2026-08-22.

Build: 33,543 lines, 1,688 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 155. THE MIRROR, AND THE FIRST KERNEL BRICKS

### 155.1 Mechanical, done

`pNodes_covers_ppi` — §154.2's mechanical item. The vertical extraction is now
closed in **both** directions on the non-persistent half.

### 155.2 Towards the kernel side

What already exists: `kernelData` (a node whose `persistDs` is nonempty HAS a
kernel — certified since the vertical campaign, via `rrPt`/`rr_segment_from`/
`rr_covers`), `chain_or_kernel` (§119), `persistent_has_kernel`.

What is missing is the **labels**. `MultiTierOk`'s six kernel fields are all
about `phase k a : List Concept`, and with support labels the phases need support
labels too — nothing yet says what seeds them.

| | |
|---|---|
| `phase_supportOk` | a phase is a model point, so `hcloseL` of anything true there is a support label — **the same construction as for externals**, no kernel-specific reasoning |
| `guard_along_chain` | `∀PP.(∃PP.D)` at one phase holds at EVERY later one — **axiom-free** |

`guard_along_chain` matters for `kk_pp`: the guard that made a demand persistent
does not lapse along the kernel, so the phase labels can carry it uniformly, which
is what phase-block propagation (§139's modelling insight) requires.

### 155.3 Where the kernel side stands

| | |
|---|---|
| a kernel exists when demands are persistent | **certified**, long-standing |
| a phase carries a support label | **certified** (§155) |
| the guard survives along the chain | **certified** (§155) |
| `ek_all`, `ke_all`, `kk_pp`, `kk_ppi`, `kq_all`, `k_ex` | **open** |

The six fields remain. What changed is that phases are no longer unlabelled: the
construction that gives externals their labels gives phases theirs, and the fact
`kk_pp` will lean on is proved.

Build: 33,700 lines, 1,691 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 156. THE `kk_*` OBLIGATIONS, AT MODEL LEVEL

| | |
|---|---|
| **`kk_pp_model`** | a `∀PP` universal at a chain point holds of every LATER point — **`propext` only** |
| **`kk_ppi_model`** | the mirror, via the converse — **`propext` only** |
| `kk_pp_next_lap` | the form the unfolding uses: every phase is reached one lap on |

These are the whole ORDER-THEORETIC content of the two obligations, and they are
unconditional: an ascending chain puts every point above every earlier one, so a
vertical universal reaches the whole chain in its direction. `chain_pp_lt` does
the work.

### 156.1 What they do NOT give — stated because it is the interesting part

`MultiTierOk`'s `kk_pp` is about the LABEL `phase k b`, not about satisfaction at
a chain point. Getting from one to the other needs the phase labels to be
**periodic**: `phase k b` must describe `c (i + b + m·p)` for EVERY lap `m`, not
one.

`KernelData.cty` supplies a single equation — `mty (c i) = mty (c (i + p))` — not
periodicity of the intermediate points. So the label statement needs either

* a periodicity lemma for `rrPt`'s chain, which is built cyclically and so may
  already have one; or
* phase labels defined as the INTERSECTION over laps — periodic by fiat, and
  still a support label by `phase_supportOk`.

Neither is attempted. **The model half is done; the label half is named.**

### 156.2 The kernel side, updated

| | |
|---|---|
| a kernel exists when demands are persistent | **certified** |
| a phase carries a support label | **certified** (§155) |
| the guard survives along the chain | **certified** (§155) |
| `kk_pp` / `kk_ppi`, model level | **certified** (§156) |
| `kk_pp` / `kk_ppi`, LABEL level | open — needs phase periodicity |
| `ek_all`, `ke_all`, `kq_all`, `k_ex` | open |

Build: 33,801 lines, 1,694 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 157. CORRECTION — the kernel side is NOT unexplored

§149.2(c) said the kernel side is "genuinely unexplored in Lean". **That is
wrong**, and grepping before writing it would have shown so.

### 157.1 What is actually there

`one_kernel_block` (and its mirror `done_kernel_block`) build a complete
`BlockOk` — the `MultiTierOk` field list for a single kernel block — with `mty`
labels and every kernel field discharged:

```
kk_pp  := segment_kk_pp  …
kk_ppi := segment_kk_ppi …
kk_eq  := seg_eq …
ek_all := …   ke_all := …   kq_all := …   k_ex := …
```

It is consumed (line 5547) and axiom-checked. `seg_pp`/`seg_ppi`/`seg_eq` — the
round-D2b segment-coherence lemmas — are its engine, and they do the job §156
was reaching for **better than §156 does**: the universal climbs to the top
endpoint and RE-ENTERS through the type-equal bottom, so `KernelData.cty`'s
single equation suffices and no phase periodicity is needed at all.

### 157.2 So §156 was partly redundant

`kk_pp_model`/`kk_ppi_model` are true and axiom-light, but `seg_pp`/`seg_ppi`
already covered the label-level statement I said was open. §156.2's
"needs phase periodicity" is **withdrawn** — the endpoint re-entry is why it
does not.

### 157.3 The kernel side, corrected

| | |
|---|---|
| a complete kernel block, `mty` labels | **certified** — `one_kernel_block` |
| all six kernel fields | **certified** there |
| segment coherence | **certified** — `seg_pp`/`seg_ppi`/`seg_eq` |
| the same for SUPPORT labels | **open** |
| `one_kernel_block`'s `hserve` / `hctx` hypotheses | the real obligations |

`hserve` asks that every phase demand have a witness uniformly related to ALL
phases; `hctx` that context elements relate uniformly to the whole chain. Those
are the substance, not the `kk_*` fields.

### 157.4 The pattern, third occurrence

§113 found `short_chain`, `pp_dichotomy` and `kernel_of_chain` certified and
unconsumed. §157 finds a whole kernel construction I described as absent.

**The rule recorded in §113 — when a gap resists, grep for what is already proved
— was not applied to my own status claim.** Writing §149's inventory from memory
rather than from the file is exactly the failure it warns about.

Build unchanged: 33,767 lines, 1,694 declarations, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 158. THE INVENTORY, RE-DERIVED FROM THE FILE

§157's correction demanded this: an audit read off the file rather than from
memory. It changes the picture substantially.

### 158.1 What is actually certified for the kernel side

| | |
|---|---|
| `one_kernel_block` / `done_kernel_block` | a complete `BlockOk`, both directions |
| `multiBlock_of_site` / `_of_chain` and duals | multi-kernel blocks |
| **`block_of_persistent`** | **a persistent `∃PP` demand PRODUCES a block** — `persistPP` in, `BlockOk` out |
| `block_of_persistent_desc` | the descending mirror |
| `glue_ok`, `glueFam_ok`, `glueMTOk` | gluing blocks into a `MultiTierOk` |
| `seg_pp` / `seg_ppi` / `seg_eq` | the segment coherence they run on |

All axiom-checked (`propext`/`Classical.choice`/`Quot.sound`); `glueMTOk` is
`propext` only.

**`block_of_persistent` is the theorem §149.2(c) said did not exist.** Its
hypotheses are `POFree C0`, a context list, and `hpoolcl` — that every `∃PO`
demand in `cl C₀` is served by some other block in the pool.

### 158.2 So the shortest path is not what §149 described

`MergedExtraction` needs a `MultiTierOk` within `mixKT` bounds. Two routes
exist and both are substantially built:

* **blocks + gluing** — `block_of_persistent` → `glueMTOk`. Kernel side done;
  what it needs is the POOL discipline (`hpoolcl`) and the bounds.
* **`mergedMT_ok`** — one certificate, six undischarged hypotheses: `hsepS`
  (separation), `hbS`/`hbK`/`hbQ` (budgets), `he_ex`/`hk_ex` (existential
  coverage).

`pNodes_covers_pp`/`_ppi` (§§154–155) are exactly `he_ex`-shaped for the
vertical part. That is where the session's work connects.

### 158.3 The corrected statement of what is left

Not "the kernel side is unexplored". Rather:

| | |
|---|---|
| kernel blocks, both directions, from persistence | **certified** |
| gluing blocks into a certificate | **certified** |
| the vertical support-label closure, bounded and closed | **certified** (§§154–155) |
| `mergedMT_ok`'s `he_ex` / `hk_ex` | the vertical work connects here |
| `mergedMT_ok`'s `hbS` / `hbK` / `hbQ` / `hsepS` | budgets and separation — untouched |
| `hpoolcl` on the blocks route | untouched |
| support labels through the kernel constructions | untouched |

### 158.4 Method note, recorded because it cost a section

§149's inventory was written from memory and was wrong in the direction that
mattered — it made the remaining work look larger and differently shaped than it
is. §157 caught it; this section replaces it.

**Any future status claim in this file should be produced by grepping, not by
recall.** That is now three separate occasions (§113, §157, §158) on which the
file knew more than the summary of it.

Build unchanged: 33,767 lines, 1,694 declarations, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 159. THE ASSEMBLY INTERFACE — read off the file

`glueFam` and `glueFam_ok` are the assembly, and reading them settles what the
mixed quadrant actually needs.

### 159.1 `glueFam` puts PO between blocks

```
E e f = if e.1 = f.1 then (F e.1).E e.2 f.2 else po
```

Cross-block relations are **`PO`** — and `∀PO` does not exist in the fragment,
so `ee_all` across blocks is vacuous by `MTNoPo`. **That is the ∀PO-free
fragment's defining freedom, used structurally.**

### 159.2 What `glueFam_ok` requires

| | |
|---|---|
| `hpool` | each block is `MTOkPool (F b) b.val P` — valid with PENDING `∃PO` demands against a pool |
| `hnopo` | each block has no `∀PO` — free from `POFree C0` |
| `hreal` | every pool entry is REALISED: some block with that tag has a node whose label contains the entry's concepts |

So the assembly is: **a block per kernel, a block per `∃PO` demand, glued with PO
between them.** `block_of_persistent` supplies the kernel blocks;
`one_kernel_block` and the horizontal extractions supply the rest.

### 159.3 A friction point, found by reading

`block_of_persistent` takes

```
hpoolcl : ∀ D, Concept.ex po D ∈ cl C0 → ∃ q ∈ P, q.1 ≠ myTag ∧ D ∈ q.2
```

— over **`cl C₀`**, not over the labels that actually occur. But `hreal`
requires every pool entry to be realised by a real node.

If some `∃PO.D ∈ cl C₀` has `D` unsatisfiable, `hpoolcl` demands a pool entry
that `hreal` cannot realise. The obligation never fires (`∃PO.D` is in no model
type), but the hypothesis as stated does not know that.

So `hpoolcl` is **conservative in a way that may be unsatisfiable**, and the
assembly likely needs it restricted to demands that actually occur — a
weakening of an existing hypothesis, not new mathematics.

### 159.4 What is left, from the file

| | |
|---|---|
| kernel blocks from persistence, both directions | **certified** |
| gluing with PO between blocks | **certified**, `propext` only |
| `MTNoPo` from `POFree` | **certified** |
| build the FAMILY and the POOL from a model | **open — the assembly** |
| `hpoolcl` restricted to occurring demands | **open — a hypothesis weakening** |
| support labels through the kernel constructions | **open** |

The assembly is the remaining substance, and it is construction over certified
parts rather than new mathematics — with the `hpoolcl` caveat, which is the
first thing to check when building it.

Build unchanged: 33,767 lines, 1,694 declarations, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 160. THE POOL HYPOTHESIS, WEAKENED

§159.3 flagged `hpoolcl` as conservative in a way that may be unsatisfiable: it
quantifies over `cl C₀`, while `glueFam_ok`'s `hreal` can only realise pool
entries that some node actually carries.

Reading further settled it — **the strengthening is in the wrapper, not the
mathematics.** `multiBlock_of_site` already takes the occurrence-restricted form;
`multiBlock_of_chain` merely converts with `mty_sub`.

| | |
|---|---|
| **`multiBlock_of_chain'`** | the chain block with the pool hypothesis over what the MODEL carries |
| **`block_of_persistent'`** | the persistent block, likewise — the form the assembly can supply |
| `block_of_persistent_of_cl` | the old form as the special case, so nothing that used it is disturbed |

A `D` that no model element carries is never demanded, so it never needs a pool
entry. The weakened hypothesis is exactly what `hreal` can meet.

### 160.1 Why this was worth doing before the assembly

The friction was found by READING the interface rather than by building on it and
failing. On this project's record — two plans killed after being committed, one
result reported confidently that its own follow-up destroyed — that ordering is
worth the section it costs.

Had the assembly been built against `hpoolcl`, the failure would have surfaced at
`hreal` with the construction already committed, and would have looked like the
assembly being wrong rather than one hypothesis being over-stated.

### 160.2 What is left

| | |
|---|---|
| kernel blocks from persistence, both directions | **certified** |
| pool hypothesis in a realisable form | **certified** (§160) |
| gluing with PO between blocks | **certified**, `propext` only |
| `MTNoPo` from `POFree` | **certified** |
| build the FAMILY and the POOL from a model | **open — the assembly** |
| support labels through the kernel constructions | **open** |

Build: 33,834 lines, 1,697 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 161. THE DEFINITIVE ASSEMBLY AUDIT — and a stop signal

§§159–160 re-derived machinery that was already in the file, for the FOURTH time
this session (§113, §157, §158, §161). That is a signal to stop building and
finish auditing, so this section does that and nothing else.

### 161.1 The chain to `Decidable`, traced

```
Satisfiable C0  →  MergedExtraction C0  →  MixedCompleteness C0  →  Decidable
                        ↑                        ↑                      ↑
                    THE GAP            mixedCompleteness_of_merged   decidableSat_pofree
                                            CERTIFIED                  CERTIFIED
```

Nothing produces `MergedExtraction`. Every reference to it is its definition, the
two theorems consuming it, or prose. **That is the single gap, and it has been
the single gap since §149 — correctly, that part of §149 was right.**

### 161.2 What is available to close it

`mergedMT_ok` produces the `MultiTierOk` that `mergedExtraction_of_ok` turns into
`MergedExtraction`. Its six hypotheses:

| | |
|---|---|
| `he_ex` / `hk_ex` | 47 / 45 mentions — extensive machinery, including the kernel witness branches `kDR` / `kUP` / `kDN` (line 20505ff) |
| `hsepS` | 9 mentions |
| `hbS` / `hbK` / `hbQ` | **2 / 2 / 4 mentions** — essentially only the statement |

The budget hypotheses are the thin ones. CLAUDE.md's 2026-08-22 status already
said so: *"the budget assignment (a choice inside the extraction, not a fact to
discover)"*.

### 161.3 Also available, and not yet connected

| | |
|---|---|
| `external_stabilizes` | an external's relation to a chain STABILIZES — the model-side fact `hstab` wants |
| the `hstab` dichotomy (§39.3) | "stay low" and "push past" branches, with machinery at lines 2796–2860, 4391 |
| `mixKernels_pool_ok` | the mixed block with `∃PO` demands PENDING |
| `pool_two_copies` / `pool_realized` | `glueFam_ok`'s `hreal`, **already discharged** for the two-copies layout |
| `glueFam_ok` / `glueMTOk` | the glue |

**The pool bookkeeping I set out to build in §159 is done.**

### 161.4 The honest remaining statement

Build the family and the budget assignment, and instantiate `mergedMT_ok`. Every
other ingredient — kernel blocks, pool covering, pool realisation, gluing,
stabilization, encoding, decision — is certified and in the file.

### 161.5 The stop signal, recorded

Four times in one session I have described as missing something the file already
had. The pattern is always the same: I reason about the architecture from the
design notes rather than grepping for the theorem.

**For the next session: before proposing ANY construction, grep for its
conclusion.** §113 recorded this rule for gaps; it applies equally to
sub-goals, and this session shows I do not apply it unprompted.

Build unchanged: 33,840 lines, 1,697 declarations, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 162. THE BUDGET ASSIGNMENT — discharged

§161.2 identified `hbS`/`hbK`/`hbQ` as the thin hypotheses. The choice is
**uniform budgets**, and since `mBk nd k = (nd (kNode k)).k`, all three become
`B ≤ B + 1`.

| | |
|---|---|
| `hbS_of_uniform` | disjoint externals within one |
| `hbK_of_uniform` | external and kernel base within one |
| `hbQ_of_uniform` | two kernel bases within one |
| **`budgets_of_uniform`** | **all three, in `mergedMT_ok`'s shape** |
| `uniform_of_ppNodes` | and the construction supplies it — `ppNodes_bud` |

### 162.1 Why uniform budgets are affordable now

`wp96` A rejected them: uniform budgets forfeit the budget-decreasing finiteness
the node bound needed.

**§143 removes that need.** `genNodes_le_C0` bounds the node set by DEPTH ×
BRANCHING, with no budget decrease anywhere — depth from `seedOf_depth_lt`,
branching from `normL_len`. So the objection is **answered, not evaded**: the
node bound no longer rests on budgets.

That is the second time the support-label machinery has paid for itself against a
previously-recorded obstruction (the first being §142 vs §104.3's "no monotone
quantity").

### 162.2 `mergedMT_ok`'s six hypotheses

| | |
|---|---|
| `hbS` / `hbK` / `hbQ` | **discharged** (§162) |
| `hsepS` | 9 mentions of machinery |
| `he_ex` / `hk_ex` | 47 / 45 mentions, incl. `kDR`/`kUP`/`kDN` |

Three of six done. The remaining three are the ones with substantial existing
support.

Build: 33,900 lines, 1,702 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 163. `hsepS` WAS ALREADY DONE — and the precise remaining list

Grepping before writing caught a FIFTH re-derivation: **`mSep` (§83, "ITEM F")
discharges `hsepS` completely**, as `hsep_of_model` instantiated at the
extraction's data, with no hypotheses beyond what the extraction has.

### 163.1 `mergedMT_ok`'s six

| | |
|---|---|
| `hsepS` | **done** — `mSep` |
| `hbS` / `hbK` / `hbQ` | **done** — §162 |
| `he_ex` / `hk_ex` | remaining |

**Four of six.** And the two remaining reduce further.

### 163.2 `he_ex` / `hk_ex` reduce to ROUTING CONDITIONS

`odSeed_he_ex` derives `he_ex` from `rDR`/`rPO`/`rPP`/`rPPI`;
`odSeed_hk_ex` derives `hk_ex` from `kDIR`/`kDR`/`kPO`/`kUP`/`kDN`.

| condition | discharge |
|---|---|
| `rDR` | `rDR_witness` (11121) |
| `rPO` | `rPO_witness` (11129) |
| `rPP` | `rPP_witness` (21199) |
| `rPPI` | `rPPI_witness` (21207) |
| `kPO` | `kPO_frame` (21908) |
| **`kDIR`** | **none found** |
| **`kDR`** | **none found** |
| **`kUP`** | **none found** |
| **`kDN`** | **none found** |

So the EXTERNAL side's routing is done, and four KERNEL-side routing conditions
are not. CLAUDE.md's 2026-08-22 status named exactly three of them —
*"the kernel witness branches `kDR`/`kUP`/`kDN`"* — and `kDIR` joins them.

### 163.3 The remaining work, as precisely as the file supports

**Four routing conditions:** `kDIR` (a kernel's own-direction demand is served
within its period), `kDR` (a kernel's `∃DR` demand is served by a seed-adjacent
external), `kUP`/`kDN` (a kernel's opposite-direction demand is served by an
external above/below it).

`kDIR` is `rr_covers` territory — round-robin coverage, certified. `kDR`/`kUP`/
`kDN` are the ones §139.1 found `wp124` needed as CONSTRUCTION steps: *a kernel
generates external witnesses*, measured there and unbuilt in Lean.

That is the whole remaining gap between the file and `MergedExtraction`.

Build unchanged: 33,906 lines, 1,702 declarations, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 164. `kDIR` FROM `rr_covers`

`kDIR_of_rr` — a kernel's own-direction demand is served within its period, given
two side conditions.

| condition | cost |
|---|---|
| `hdep` | free — `Ds ⊆ cl C₀`, budget uniform at `mdepth C₀` (§162), and every member of `cl C₀` has depth at most that |
| `hin` | **the real one** — every own-direction demand a phase carries must be one the kernel was built from |

`hin` is not automatic: §153 shows demands INHERITED from a universal are
persistent, but a demand in a phase's own type need not be.

So `kDIR` is `rr_covers` plus a construction discipline — **build the kernel from
the union of the own-direction demands its phases carry**. That union is finite
and computable (phase labels are drawn from `cl C₀`), but nothing constructs it
yet.

### 164.1 Remaining, updated

| | |
|---|---|
| `hsepS`, `hbS`, `hbK`, `hbQ` | **done** |
| `rDR`, `rPO`, `rPP`, `rPPI`, `kPO` | **done** |
| `kDIR` | **reduced to `hin`** — a construction discipline |
| `kDR`, `kUP`, `kDN` | open — §139.1's "a kernel generates external witnesses" |

Build: 33,957 lines, 1,704 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 165. `kDR` FROM COFINAL DISJOINTNESS — and the shape of what is left

`mKdr_of_cofinal` — an external `DR` from the chain COFINALLY is `DR` from it
everywhere, hence seed-adjacent to the kernel, which is what `kDR` needs.

### 165.1 Why cofinality is the condition

A `∃DR.D` demand at phase `a` gives a witness disjoint AT THAT PHASE.
Disjointness propagates DOWNWARD — `comp(PP,DR) = {DR}`, the cell `odOfModel`'s
`djDown` runs on. **Upward there is no law:** `comp(PPI,DR) = {PPI,PO,DR}`, and
`external_stabilizes` only says the relation settles somewhere, not at `DR`.

So `kDR` is a **selection condition**: choose the `∃DR` witness so its relation
to the chain stabilizes at `DR`. Same kind as §109's `WitSel`, and what §39's
`hstab` material is about.

### 165.2 The remaining four, reduced to two shapes

| | |
|---|---|
| `kDIR` | build the kernel from the demands its phases carry (§164) |
| `kDR` / `kUP` / `kDN` | choose witnesses whose relation to the chain is STABLE in the required direction |

Both are **selection disciplines on the extraction**, not facts about the logic —
the same character as the budgets (§162), which went through once the right
choice was made.

That is a reason for cautious optimism and **not more**: the analogous claim has
been wrong twice this session (§§131, 133), and both times the failure was in a
construction that looked like bookkeeping.

Build: 34,006 lines, 1,704 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 166. `wp126` — stable witnesses, measured, with two numbers withheld

Control held (0 phase demands without a witness) across all four shapes.

| | L=4 p=3 | L=8 p=3 | L=8 p=6 | L=18 p=3 |
|---|---|---|---|---|
| `∃DR` uniform | 100% | 100% | 100% | 100% |
| `∃PPI` uniform | 95.0% | 100% | 99.5% | 100% |
| `∃PP` uniform | 35.6% | 42.1% | 48.8% | 45.8% |

### 166.1 The `∃DR` 100% is an ARTIFACT of the class

`wp112`'s tower gives `dr`-sides that are disjoint from the WHOLE chain by
construction. So a uniform `DR` witness exists whenever any does — **the class
cannot exhibit §165.1's failure mode**, which is precisely a witness disjoint at
one phase and not at another.

Reported as a class property, not as evidence for `kDR`. §117's rule.

### 166.2 The `∃PP` 35–49% is measuring the WRONG obligation

The tower's kernel is ASCENDING, so `∃PP` at a phase is its OWN-direction demand
— served by `kDIR` **within the period**, not by an external. `kUP` is the
`dir k = false` case, which this class has no instance of.

So that column says nothing about `kUP`. It is withheld.

### 166.3 What the run does support

**`∃PPI` at an ascending kernel — the `kDN` obligation — has a uniform external
witness 95–100% of the time**, and the class CAN represent failure here (a
witness below one phase need not be below another). The residue is small but
nonzero: 5% at `L=4 p=3`, 0.5% at `L=8 p=6`.

So `kDN` is nearly a lookup and not quite one, which is §165.1's prediction
holding at a low rate.

### 166.4 Net

| | |
|---|---|
| `kDR` | untested — the class cannot exhibit the failure |
| `kDN` | 95–100%, real residue, class can exhibit failure |
| `kUP` | untested — no descending kernel in the class |
| `kDIR` | not this probe's subject (§164) |

**One of four conditions got a meaningful measurement.** A probe that can carry
a descending kernel and non-uniform `dr`-sides would be needed for the rest —
and building one is the same instrument problem §117 hit three times.

Two of the three headline numbers withheld is the correct outcome here, not a
failed run.

## 167. `wp127` — `kDR` MAY NOT BE A SELECTION DISCIPLINE AFTER ALL

Control held (W = 0 gives 100%).

| window W | 0 | 1 | 2 | 4 | 8 | 16 |
|---|---|---|---|---|---|---|
| an ARBITRARY `DR` witness survives | 100% | 82.9% | 70.3% | 52.8% | 32.6% | 13.8% |
| SOME stable carrier EXISTS | 100% | 92.9% | 85.9% | 72.7% | 50.9% | **24.7%** |

### 167.1 What the second row means

§165.2 called `kDR` a **selection discipline** — stable witnesses are there, they
just have to be chosen. If that were right, row 2 would stay flat while row 1
decayed.

**Both decay.** Some demands have no stable carrier at all, so `kDR` is a genuine
obligation that can FAIL, not merely a choice made badly.

### 167.2 The structural reason, and the caveat that limits it

An ascending chain `a_i = {0..i}` EXHAUSTS its universe. A region disjoint from
every `a_i` would have to be disjoint from their union, so in that model none
exists — and `base_ge` does not help, since pushing the kernel base UP removes
only low constraints and keeps every high one.

**So `kDR` is unsatisfiable whenever the kernel's chain exhausts the space.**

The caveat: finite set models exhaust by construction. A model with room outside
the chain's union — regions over `ℕ × ℕ` with the chain in one column — has
cofinally-disjoint externals throughout. **Whether models of satisfiable
∀PO-free concepts must have such room is not established**, and the decay
measured here is partly an artifact of a class that cannot provide it.

### 167.3 Net

`kDR` is not shown unsatisfiable. What is shown is that §165.2's optimistic
reading — a selection discipline like the budgets — **is not supported**, because
existence itself degrades in this class.

The next question is sharp: **must a kernel chain in a model of a satisfiable
∀PO-free concept leave room for a disjoint external?** That is a question about
the logic, not about the extraction, and it is the first such question this
session has produced.

§165.2 said "cautious optimism and not more", and flagged that the analogous
claim had been wrong twice. It was wrong a third time.

## 168. WHERE THIS LEAVES IT

### 168.1 What the session built

* **The vertical extraction** (§§140–155): support labels, the depth measure that
  works on them, the split closure `pNodes`, bounded and closed in both
  directions. This is what §§130–133 twice failed to get.
* **`mergedMT_ok`'s budgets** (§162), by choosing them uniform — affordable
  because §143's node bound no longer rests on budget decrease.
* **Reductions**: `kDIR` to `rr_covers` plus a construction discipline (§164);
  `kDR` to cofinal disjointness (§165).
* **Corrections**: three of my own claims withdrawn (§§157, 158, 167), each
  found by grepping or measuring rather than reasoning.

### 168.2 The pipeline

```
Satisfiable C0 → MergedExtraction → MixedCompleteness → Decidable
                       ↑                CERTIFIED         CERTIFIED
```

`MergedExtraction` needs `mergedMT_ok`, whose six hypotheses are:

| | |
|---|---|
| `hsepS` | **done** — `mSep`, found already present |
| `hbS`/`hbK`/`hbQ` | **done** — §162 |
| `he_ex` | reduces to `rDR`/`rPO`/`rPP`/`rPPI` — **all four done** |
| `hk_ex` | reduces to `kDIR`/`kDR`/`kPO`/`kUP`/`kDN` — `kPO` done, `kDIR` reduced, **`kDR`/`kUP`/`kDN` open** |

### 168.3 The new problem, and why it is different in kind

Everything open until §167 was a CONSTRUCTION: build the family, choose the
witnesses, wire the labels. `wp127` found something else.

`mKdr` asks for a **single** external disjoint from the kernel's **entire** chain.
If the chain exhausts its space, no such external exists — and each phase's
`∃DR` demand may have its own witness with no common one. The certificate cannot
express that: `K k f` is one relation per (kernel, external) pair and cannot vary
by phase.

**So this is a question about the architecture and the logic, not about the
extraction:**

> must a kernel chain in a model of a satisfiable ∀PO-free concept leave room for
> an external disjoint from all of it?

If yes, `kDR` is dischargeable and the remaining work is construction. If no,
`mKdr` is too strong and the kernel-DR route needs redesign.

It is also close to territory the campaign has been in: `wp96` C and §44's design
notes are about kernels under `DR` externals inheriting disjointness by `djDown`.

### 168.4 Honest position

The ∀PO-free fragment is **not certified decidable**, and this session did not
change that. What changed:

* three quadrants remain certified, unaffected;
* the mixed quadrant's VERTICAL half now has a terminating, bounded, closed
  extraction where it previously had two dead routes;
* the remaining gap is four routing conditions, of which one has just turned out
  to hide a possible architectural problem rather than a construction task.

Build: 34,004 lines, 1,704 declarations, 0 errors / 0 warnings / 0 sorries /
0 `sorryAx`. Probes `wp107`–`wp127`.

## 169. THE ANSWER — no, and the probe could not show it

`wp128` failed its control: `C0` holds at neither model's root. Both failures are
finite-truncation artifacts — `∀PP.(∃PP.⊤)` fails at the TOP chain element, and a
truncated "exhausting" chain does not exhaust. Fourth instrument to fail this way
(`wp100`, `wp110`, `wp111`, `wp128`), same cause each time.

The argument does not need one.

### 169.1 The counterexample, by hand

Regions = **nonempty** subsets of `ℕ`. Chain `a_i = {0..i}`, all `i ∈ ℕ`.

```
C0 = ∃PP.⊤ ⊓ ∀PP.(∃PP.⊤ ⊓ ∃DR.A)      A on singletons
```

* `∀PO`-free by inspection.
* `∃PP.⊤` at every `a_i`: witness `a_{i+1}`. The chain is genuinely infinite,
  no top element — so the guard `∀PP.(∃PP.⊤)` holds and the demand is
  **persistent**, i.e. a kernel.
* `∃DR.A` at every `a_i`: witness `{i+1}`, disjoint from `{0..i}`.
* So `C0` is satisfiable, with a kernel whose every phase carries `∃DR.A`.
* **No region is disjoint from every `a_i`**: it would have to be disjoint from
  `⋃ a_i = ℕ`, hence empty, and regions are nonempty.

**So `mKdr` is unsatisfiable in this model.** The answer to §168.3 is **no** — a
kernel chain need not leave room.

### 169.2 But the same concept has a roomy model

Regions over `ℕ × {0,1}`; the chain in column 0; `A` on `{(0,1)}`. That witness
is disjoint from the entire chain, so `mKdr` holds.

### 169.3 What this means for the architecture

`mKdr` is **not** a consequence of satisfiability. It is a property of the MODEL
the extraction is handed.

Since `MergedExtraction : Satisfiable C0 → ∃ … MultiTierOk …` only needs SOME
certificate, the extraction may build it from a different model than the one it
is given — the freedom named in §134.3 step 3 and never used.

So the gap moves once more, and to a statement about the logic:

> **does every satisfiable ∀PO-free concept have a model in which every kernel
> chain leaves room for a disjoint external?**

§169.2 shows it for one concept, by adding a spare dimension. Whether that
generalises is the question, and it is model-surgery — amalgamation territory,
where the campaign's `wp6`/patchwork material lives.

### 169.4 Calibration

This is the second time this session that a gap has moved from "construction" to
"a statement about the logic" (§167, §169). It is also the fourth probe whose
model class could not represent its subject.

`mKdr` being model-dependent is a genuine finding and is bad news for the direct
route. Whether it is bad news for the fragment depends entirely on §169.3's
question, which is open.

## 170. MODEL SURGERY — the fresh all-DR point

§169.3 asked whether the extraction can move to a model where kernel chains leave
room. The tools were already in the repository.

### 170.1 On the record about one-point extensions

Michael's recollection was that one-point extensions had failed. Checking: what
failed was a claimed **obstruction** — the 16th review found the overview paper's
one-point-extension example was FALSE, the extension actually succeeds
(`comp(DR,PO) ∩ comp(PPI,PO) = {PO}`, real set model exists). So the record is
the opposite of an impossibility.

`wp71` gives an EXACT criterion, exhaustive to `n = 4`, **234,496 extensions, 0
mismatches**. Its sample line settles the case that matters:

```
e relations ('DR','DR'): criterion=True  brute_closed=True
```

**A fresh point DR from everything is always a valid one-point extension.** Its
`U` and `L` are empty and `D` is everything, so every clause of the criterion is
vacuous or trivial.

### 170.2 The label half, measured (`wp129`)

The fresh point must satisfy the demand `D` and every `X` with `∀DR.X` true at
ANY chain point.

| | |
|---|---|
| CONTROL — bodies accumulate monotonically up the chain | **0 failures / 1182** |
| the accumulated body set is CONSISTENT (some point satisfies it) | **99.8%** |
| a point DR from the WHOLE chain already present | 19.7% |

The control confirms the downward-closure argument: disjointness is
downward-closed, so a witness disjoint from `c_j` is disjoint from every `c_i`
with `i ≤ j` and already meets their bodies. Bodies therefore accumulate, the
union is drawn from finite `cl C₀`, and it is reached at a finite height.

The 19.7% is exactly the §167 problem — models usually do NOT already contain the
point. **The 99.8% is the answer: the point they need is consistent, so it can
be added.**

### 170.3 What is not yet handled

A fresh point is a copy of a satisfying element MOVED to be DR from everything.
Its own demands must then be served from the new position — the recursion this
route does not yet close. And 2 of 1182 body sets were inconsistent.

So the surgery is **viable at the frame level** (`wp71`, exhaustive) and **near
viable at the label level** (99.8%), with the residue being the fresh point's own
obligations.

### 170.4 Position

§169 moved the gap from construction to a question about the logic. §170 answers
the frame half of that question outright and the label half at 99.8%. The
remaining piece is back to construction — the fresh point's own demands — which
is where the session's vertical machinery (§§140–155) applies.

## 171. THE DR-GLUE

§170's surgery needs a sub-model transplanted **disjoint** from the original.
Both existing glues put **PO** across — free for the fragment, since `∀PO` does
not exist — but **PO does not serve an `∃DR` demand**, which is the whole point
of the transplant.

So a DR-glue is genuinely new. Grepped first: neither `glueMT` nor `glueFam` has
a DR variant.

| | |
|---|---|
| `DRCompat` | each block's labels satisfy the other's `∀DR` bodies |
| `glueDRMT` | two certificates side by side, every cross pair `DR` |
| `dr_mem_comp_dr` | `DR ∈ comp(r, DR)` for every atom — `propext` only |
| `comp_dr_dr_all` | `comp(DR,DR)` is everything — `propext` only |

### 171.1 The frame is free; the obligations are not

`dr_mem_comp_dr` covers a triangle with two vertices in one block and one in the
other. `comp_dr_dr_all` covers the mirror. Between them that is the entire frame
content of the glue, and neither fact was in the file.

**The obligations are where the DR-glue differs from the PO-glue.** `∀PO` does
not exist in the fragment, so `glueFam`'s cross-block `ee_all` is vacuous by
`MTNoPo`. **`∀DR` is a real universal here**, so a `∀DR.c` on one side must reach
every label on the other — which is `DRCompat`, and which `wp129` measured as
consistent in **99.8%** of chains.

So the DR-glue costs a hypothesis where the PO-glue costs nothing, and that
hypothesis is measured to be usually satisfiable.

### 171.2 Left

`glueDRMT`'s `MultiTierOk`, whose cross-block clauses are exactly `DRCompat`.
The frame facts it needs are now proved; the clause-by-clause discharge is not
written.

Build: 34,079 lines, 1,708 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 172. THE GLUE, PARAMETERIZED BY ITS CROSS ATOM

`glueMT` and `glueDRMT` differ in ONE value: `po` versus `dr`. Rather than
duplicate `glue_frame`, this parameterizes the glue and proves the frame from
conditions on the atom. **`glueMT` is untouched.**

| | |
|---|---|
| `CrossAtom x` | five conditions: `ne_eq`, `conv_self`, `in_comp_right`, `in_comp_left`, `all_in_comp` |
| `crossAtom_dr` | `DR` qualifies — `propext` only |
| `crossAtom_po` | so does `PO`, recorded to show the parameterization is faithful to both |
| `glueNet` | two networks side by side, every cross pair `x` |
| **`glueNet_frame`** | **the frame, from `CrossAtom` alone** — `propext` only |

### 172.1 The five conditions are the whole content

* `ne_eq` — the cross value is not identity, so `eq_id` cannot merge blocks;
* `conv_self` — symmetric, so `conv_` holds across;
* `in_comp_right` / `in_comp_left` — a triangle with two vertices in one block,
  entered from either side;
* `all_in_comp` — a triangle with one vertex in each.

`in_comp_left` was missing from my first attempt and Lean caught it: the case
`(inl a, inr b, inr c)` needs `x ∈ comp x (N₂ b c)`, which the right-hand
condition does not give. Four conditions looked sufficient and were not.

### 172.2 Position

**The DR-glue's frame is proved**, and the PO-glue's falls out of the same lemma.
Both `dr` and `po` meet all five conditions, which is why both glues exist.

What still separates them is the OBLIGATION side (§171.1): `∀PO` is vacuous in
the fragment, `∀DR` is not. So the DR-glue's `MultiTierOk` needs `DRCompat`
where the PO-glue needs nothing — and that remains the open brick.

`glueNet_frame` is stated on bare networks, so it applies to `qnet` of either
glue once the projections are supplied.

Build: 34,158 lines, 1,713 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 173. THE 0.2% — and why recurrence rules it out

`wp129` refined: of the 2 inconsistent cases in 1182, **0 are fixed by raising
the kernel base** (which `base_ge` permits) and **2 are blocked at every base**.

So they are real for the chains the probe uses. The question is whether they are
real for KERNELS.

### 173.1 What a blocked case is

`need` is inconsistent exactly when some chain point carries `∀DR.X` with `X`
unsatisfiable — i.e. the point is **DR-isolated**, its universal vacuously true.
A fresh point DR from the whole chain would make it non-vacuous and require `X`,
which nothing satisfies.

### 173.2 Why a kernel cannot be in that position

A kernel chain is **recurrent**: `mty (c i) = mty (c (i+p))`, so every phase type
occurs at arbitrarily high AND low positions in the unfolding.

Suppose phase `a` is DR-isolated (`∀DR.X`, `X` unsatisfiable) and phase `b`
carries `∃DR.D`, with witness `w`.

* `w` is `DR` from `b`.
* `a`'s type recurs BELOW `b` — take that occurrence `a'`.
* Disjointness is downward-closed (`comp(PP,DR) = {DR}`), so `w DR b` and
  `a' PP b` give **`w DR a'`**.
* `a'` has `a`'s type, hence `∀DR.X`, so `X` holds at `w`.
* So `X` is satisfiable — contradicting the assumption.

**On a recurrent chain, a DR-isolated phase and an `∃DR` demand at any phase are
incompatible.** So if a kernel has any `∃DR` demand — which is the only case
where `kDR` fires — no phase is DR-isolated, and `need` is consistent.

### 173.3 Status of the argument

The probe's 2 cases use ARBITRARY maximal chains in finite models, which are not
recurrent, so the counterexample does not transfer. That is an argument, not a
proof: it is three composition steps and a use of recurrence, all of which have
certified counterparts (`path_cut_below` for downward closure, `cty` for
recurrence), but it is not written in Lean.

**What it does settle: the 0.2% is not evidence against the surgery.** It is
evidence that arbitrary chains can be blocked and that kernel chains, being
recurrent, cannot be — which is the same shape as §153, where recurrence also
turned an apparent counterexample into a non-case.

### 173.4 Honest caveat

Recurrence has now rescued two arguments in this session (§153, §173). That is a
pattern worth suspecting rather than trusting: both times the rescue was found
AFTER the obstruction, and I have not looked for a case where recurrence makes
things worse.

## 174. WHERE RECURRENCE MAKES THINGS WORSE — checked, and already handled

§173.4 flagged that recurrence had rescued two arguments and that I had not
looked for a case where it hurts. Looking:

### 174.1 It hurts `∃PO`

Recurrence puts every phase type above every phase type. `po_up` (certified) says
a `PO` external stays `PO`-or-`PPI` at every LATER chain position, because
`comp(PPI,PO) = {PO,PPI}` — and downward there is no law at all,
`comp(PP,PO) = {DR,PO,PP}`.

So a witness that is `PO` from one phase may be `PPI` from that phase's next
occurrence. The certificate has ONE `K k f` per (kernel, external) pair and
cannot express a relation that varies by lap.

**So recurrence genuinely makes `∃PO` at a kernel phase unservable by an
external.** That is the case §173.4 asked for, and it exists.

### 174.2 It is already handled

The file says so at line 17788, and names the probe:

> an `∃PO` demand at a kernel phase provably cannot be served by a β-external (a
> witness can be `PO` at a single level only), so it must leave the block

`mixKernels_pool_ok` is the interface: `∃PO` demands **pend** to the pool and are
realised in another block, the cross edge being `PO` by construction. That is
what `glueFam`'s PO-across is FOR.

### 174.3 What the check establishes

Recurrence helps `∃DR` (§173) and hurts `∃PO` (§174.1), and the campaign already
found the second and built around it. So the pattern §173.4 warned about is real
but not unexamined — the asymmetry between `DR` and `PO` under recurrence is
exactly why the fragment removes `∀PO` and why the glue is PO-across.

The caveat stands in a weaker form: recurrence is not uniformly benign, its
failure case is known, and my two rescues are on the side it helps.

Build unchanged: 34,172 lines, 1,713 declarations, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 175. THE DR-GLUE'S EMBEDDINGS AND LABELS

| | |
|---|---|
| `gdr1` / `gdr2` | the two side embeddings |
| `gdr_label_1` / `_2` | labels are literally the blocks' own — by `rfl` |
| `gdr_rep` | every node is on one side — **axiom-free** |
| `drCompat_cross` / `_cross'` | `DRCompat` restated over the glue's own nodes |

Because the labels transfer by `rfl`, **every propositional obligation** —
`e_clash`, `e_nobot`, `e_and`, `e_or` and the four `k_` mirrors — transfers
without argument. Only the RELATIONAL obligations see the cross value, and for
those `drCompat_cross` is the tool.

### 175.1 Position

The DR-glue now has its frame (§172) and its plumbing (§175). What remains is the
19-field `MultiTierOk` itself, where:

* 8 propositional fields transfer by `rfl` through the label lemmas;
* `kk_pp`/`kk_ppi`/`kk_eq` are block-internal — the glue does not relate phases
  of different kernels except by the cross value;
* `ee_all`/`ek_all`/`ke_all`/`kq_all` split by `gdr_rep` into block-internal
  (delegate) and cross (`drCompat_cross`);
* `e_ex`/`k_ex` are monotone — a demand served inside its block stays served.

Nothing there needs a new idea. It needs writing.

Build: 34,247 lines, 1,719 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 176. THE DR-GLUE IS A FRAME

`qnet` of the DR-glue is `glueNet dr` of the two blocks' `qnet`s, up to the
regrouping `(β₁⊕β₂) ⊕ (κ₁⊕κ₂) ≃ (β₁⊕κ₁) ⊕ (β₂⊕κ₂)`. So §172's lemma does the
work and no triangle analysis is needed.

| | |
|---|---|
| `frame_of_inj` | a frame pulls back along an injection |
| `gdrSwap` / `gdrSwap_inj` | the regrouping and its injectivity |
| `qnet_glueDR` | `qnet` of the glue IS `glueNet dr` of the parts |
| **`glueDRMT_frame`** | **the DR-glue is a frame** — `propext` only |

Two details Lean caught: the kernel diagonal is `if k = k' then eq else Q k k'`,
and the sum's `DecidableEq` instance makes the same-side case non-definitional —
`simp` handles it. And `conv dr = dr` had to be given explicitly.

### 176.1 The DR-glue, so far

| | |
|---|---|
| definition, `DRCompat` | §171 |
| cross-atom conditions, `glueNet_frame` | §172 |
| embeddings, labels, `gdr_rep` | §175 |
| **`frame_q`** | **§176** |
| the other 18 `MultiTierOk` fields | remaining |

Of those 18: 8 propositional transfer by `rfl`; `kk_*` are block-internal;
`ee_all`/`ek_all`/`ke_all`/`kq_all` split by `gdr_rep` into delegate and
`drCompat_cross`; `e_ex`/`k_ex` are monotone.

Build: 34,295 lines, 1,725 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 177. THE DR-GLUE IS COMPLETE

```
glueDRMT_ok (h1 : MultiTierOk T1) (h2 : MultiTierOk T2) (hc : DRCompat T1 T2) :
    MultiTierOk (glueDRMT T1 T2)
```

**`propext` only.** All 19 fields.

| how each field went | |
|---|---|
| 8 propositional | delegate by side — labels are the blocks' own |
| `frame_q` | §176 |
| `kk_pp` / `kk_ppi` / `kk_eq` | block-internal, delegate |
| `ee_all` / `ek_all` / `ke_all` / `kq_all` | same-side delegate, cross-side `DRCompat` |
| `e_ex` / `k_ex` | monotone — a demand served in its block is served in the glue |

### 177.1 What it cost that the PO-glue does not

Exactly the four cross-side cases, and each is one `DRCompat` application. `∀PO`
being absent makes those vacuous for `glueFam`; `∀DR` being present makes them
real here. **That is the entire difference between the two glues**, and it is
four lines.

Three Lean-caught details worth recording: `exacts` is not in core (bullets
instead); a `by` block's tactic must start on its own line for following bullets
to attach; and `mtLabel T (.inr (k,a))` needs retyping to `T.phase k (a % T.p k)`
by an ascribed `have` before `Nat.mod_eq_of_lt` will fire.

### 177.2 The DR-glue, done

| | |
|---|---|
| definition, `DRCompat` | §171 |
| cross-atom conditions, `glueNet_frame` | §172 |
| embeddings, labels, `gdr_rep` | §175 |
| `frame_q` | §176 |
| **the full `MultiTierOk`** | **§177** |

So §170's model surgery has its transplant tool: two certificates can be glued
disjoint, given `DRCompat` — which `wp129` measured as consistent 99.8% of the
time and §173 argues is automatic for recurrent kernel chains.

Build: 34,404 lines, 1,726 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 178. THE 0.2%, BELOW THE DEMAND — certified without any recurrence

§173 argued the residual inconsistent cases away by appealing to recurrence.
Before building recurrence machinery, this section asks how much of the argument
needs it. **Half of it does not.**

`DRCompat` needs: every `∀DR.X` obligation in the chain's labels is satisfied by
the fresh DR-point. The fresh point is the witness of some `∃DR.D` demand sitting
at chain height `j`. For a universal at height `i ≤ j` the argument is two moves,
both already certified:

* `dr_witness_below` — if `c j DR w` and `i ≤ j`, then `c i DR w`. This is
  disjointness read downward: `c i PP c j` and `c j DR w` force
  `comp(PP,DR) = {DR}`. Axiom-free.
* `dr_bodies_satisfied` / `need_consistent_below` — so `c i`'s own `∀DR.X` fires
  on `w` directly, and `X` holds there.

That is `wp129`'s control turned into a theorem: the body set contributed at or
below the demand's own height is *always* consistent, for every model, with no
periodicity assumption and no recurrence.

**What it left open.** A `∀DR.X` at a point *above* the demand. There
`comp(PPI,DR) = {PPI,PO,DR}` gives nothing — the witness need not be disjoint
from a higher chain point at all. §173's argument for that case wanted the type
to recur below an arbitrary height, which `KernelData.cty`'s single equation does
not directly supply.

The note flagged the shape as the same periodicity §156.2 wanted and §157 found
`seg_pp` already avoiding, and recorded: *check whether `seg_pp`'s
endpoint-re-entry trick applies here before building anything.* §179 checked.

## 179. IT DOES — `∀DR` CLIMBS, AND THAT CLOSES THE OTHER HALF

The trick applies, and the reason is one lemma that had not been noticed:

> **`all_dr_up` (axiom-free).** If `∀DR.X` holds at `x` and `x PP y`, then
> `∀DR.X` holds at `y`.

Anything `DR` from `y` is `DR` from `x` by downward closure, so `X` holds there
already. **The universal climbs even though its witnesses do not** — which is
exactly the asymmetry §178 ran into from the other side. `comp(PPI,DR)` being
wide is what makes the *witness* fail to transfer up; it is irrelevant to whether
the *obligation* transfers up, and the obligation does.

That is the `sat_all_pp_up` analogue `seg_pp` is built on, so the segment lemma
transposes directly:

* `seg_dr` — with a type repeat `mty(c i) = mty(c j)`, a `∀DR.X` anywhere in the
  segment holds at **every** point of it. Climb to the top endpoint, cross the
  repeat to the bottom, descend by `all_dr_up` again. (Two of `seg_pp`'s
  hypotheses turn out unnecessary here and are kept only for symmetry.)
* `need_consistent_seg` — so every `∀DR` body contributed anywhere in the segment
  is also contributed at the bottom, where §178's downward argument satisfies it
  from the demand's own witness.

**Net: the 0.2% is closed.** Under a type repeat — which is what a kernel *is*,
and what `seg_pp`/`seg_ppi` already assume everywhere else — the position of a
`∀DR` universal relative to the `∃DR` demand no longer matters, so `DRCompat`'s
obligation set is consistent unconditionally. No recurrence machinery was built;
the periodicity already present in the kernel was enough once the right
propagation direction was noticed.

**Method note, the fifth of its kind.** §157's rule ("grep before building") has
a sibling that fired here: *before building a new argument, check whether an
existing one transposes.* §178.1 wrote that instruction down for itself and §179
followed it — cost was one lemma and one segment lemma instead of a recurrence
theory. The check that made it work was asking which *direction* of propagation
the wide composition cell actually blocks.

Build: 34,581 lines, 1,736 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`. `all_dr_up` axiom-free; `seg_dr` /
`need_consistent_seg` / `need_consistent_below` = propext + Classical.choice +
Quot.sound.

## 180. ONE WITNESS FOR ALL THE BODIES — and what "closed" does and does not mean

§179 claimed the 0.2% closed. Checking that claim against what `DRCompat`
literally demands found the statement one notch too weak, and the scope one notch
too broad. Both are recorded here rather than quietly fixed.

### 180.1 The quantifier order was wrong

`need_consistent_seg` reads `∀ X, ∃ w` — every `∀DR` body is *separately*
satisfiable. That matches §173.1's characterization, which talks about a single
`∀DR.X` with `X` unsatisfiable. But `wp129` measured the consistency of the whole
body **set**, which is `∃ w, ∀ X`.

The proof already delivered the stronger form — the witness never depended on
`X`; it is the demand's own witness — so pulling the `obtain` outside the `intro`
was the whole fix. `need_set_consistent_seg` and `need_set_consistent_below` are
the corrected statements, and they also return `D ∈ mty C0 I w` rather than
`sat I w D`, since label membership is what the assembly consumes.

**One point satisfies every `∀DR` body contributed anywhere in a type-repeating
segment.** That is `wp129`'s 99.8% measurement as a theorem, at 100%.

### 180.2 What is still not `DRCompat`

`DRCompat T1 T2` demands `∀DR.c ∈ mtLabel T1 x → c ∈ mtLabel T2 y` for **every**
node `y` of `T2` — not just at the fresh witness. §180.1 gives it at the witness.

The rest is not another instance of the same difficulty: if `T2`'s nodes are
genuinely `DR` from `T1`'s in the model — which is exactly the read-off condition
that makes the DR-glue a faithful abstraction in the first place — then `T1`'s
`∀DR.c` fires on every `T2` node directly, with no argument at all. So the
remaining step is *establishing DR-separation of the two node sets*, not
re-litigating consistency.

That is a construction obligation on the extraction, and it belongs with the
other outstanding extraction items (the `kDR`/`kUP`/`kDN` routing, the family and
pool), not with the 0.2%.

### 180.3 Corrected scope of §179's claim

**Certified:** the body set the fresh DR-point must satisfy is consistent —
unconditionally, at one point, for both positions of the universal relative to
the demand, given a type repeat. The `∃DR`-demand-and-DR-isolated-phase
incompatibility §173.2 argued informally is now `need_set_consistent_seg`.

**Not certified:** `DRCompat` itself, which additionally needs the two blocks
DR-separated in the model.

§179's "the 0.2% is closed" is accurate for the 0.2% — the inconsistency `wp129`
measured — and was too broad if read as "the DR-glue's hypothesis is discharged".

Build: 34,626 lines, 1,738 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 181. THE FREE DR CONE — and what `wp130` says it costs

§180.2 filed "DR-separation of the glued node sets" with the extraction
obligations. This section asks how much of it is free, certifies that part, and
measures the rest.

### 181.1 Which directions preserve `DR`, certified

Starting from a witness `w` with `c DR w`:

| step from `w` | cell | forced? |
|---|---|---|
| descend (`w PPI y`) | `comp(DR,PPI) = {DR}` | **yes** |
| ascend (`w PP y`) | `comp(DR,PP)` wide | no |
| across (`w DR y` / `w PO y`) | wide | no |

`dr_desc_step` (axiom-free) and `dr_desc_chain` certify the first row; it is
§178's downward closure applied in the SECOND argument instead of the first.
`dr_cone_free` composes it with `dr_witness_below` — everything below the witness
is `DR` from every chain point at or below the demand — and `dr_cone_bodies`
lands the universals there in one statement.

### 181.2 `wp130`, and what it changed

Four measurements, two model classes each (`G1` a shared universe, `G2` with a
region the chain never enters — the generator artifact `wp127` was exposed to):

| | |
|---|---|
| A free cone, as proved | **100%**, both classes |
| A ascent/across nodes that happen to be `DR` | **~2%**, both classes |
| B `DRCompat` on an ARBITRARY block | ~36% |
| C ... choosing the witness inside the model | ~25–30%, i.e. **no better** |
| D ... letting the block come from a DIFFERENT model | **~48%** |
| E block-side failures ONLY above the demand's height | **91–97%** |

Three of these changed the picture:

**The free cone is free but small.** At ~2%, `DRCompat` is *not* inherited from
the model. The glue must declare the `DR` and discharge the label condition on
its own — which is what `glueDRMT` is for, so this is a confirmation of the
architecture rather than a problem with it.

**Selection is not the lever; provenance is.** C is the negative result:
searching the model's own witnesses does not help. D is the positive one: the
block may be a certificate of a *different* model, which §180 licenses (the body
set is consistent, so a model of `D ⊓ ⋀bodies` exists), and restoring that
freedom roughly doubles the rate.

**The residue is localized, and to a familiar place.** E confirms a prediction
stated before the run: the root is `DR` from everything at or below the demand
(`dr_witness_below`), so its own universals are already forced there — failures
must sit above. They do, 91–97%, and **every single at-or-below failure came from
a non-root node**, i.e. from outside §181.1's free cone. The diagnostic is fully
explained with nothing left over.

### 181.3 A methodological catch worth recording

Part B's first run reported **94%** — on a sample whose mean was **0.1** `∀DR`
bodies. It was measuring emptiness. Conditioning on non-vacuous instances and
weighting the generator toward `∀DR` dropped it to 36%.

That is the [[probe-before-lean-churn]] companion rule firing on a new axis:
`wp100`/`wp110`/`wp111` were blind spots in the model class; this was a blind
spot in the *instance filter*. **A high pass-rate on a mostly-vacuous sample is
indistinguishable from a finding until you count the non-vacuous instances.**

### 181.4 Position

`DRCompat` is a real obligation, not a formality: ~48% with full freedom. But its
failure mode is the **same "above the demand" shape §178 met and §179 closed for
the chain's own universals**, plus the non-root nodes §181.1 pins as outside the
free cone. Known shape, known tool, and a construction still to write — which is
a materially better position than "an unquantified hypothesis", and materially
worse than "free".

Build: 34,703 lines, 1,742 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`. `dr_desc_step` axiom-free; `dr_cone_free` propext only.

## 182. `DRCompat` IS FINITE — and the residue was in the presentation, not the logic

§181.2 part E localized `DRCompat`'s failures to chain points **above the
demand's height**, 91–97% of them, and §181.4 filed that as the remaining work.
Looking at where the measurement was taken changed the reading.

### 182.1 A certificate has no high kernel nodes

`mtLabel T (.inr (k,i)) = T.phase k (i % T.p k)`. A kernel node's label is one of
only `T.p k` many, and the node at index 1000 carries **literally the same label**
as the node at index `1000 % p`. `kernel_label_occurs_low` states it.

So "above the demand" is a property of the *model presentation*, where a chain
point at height 1000 carries whatever it carries — not of the certificate, where
there is no such node. `drCompat_of_phases` (**axiom-free**) makes the
consequence precise: `DRCompat`, whose statement quantifies over all of
`β ⊕ κ × Nat`, follows from its restriction to externals and to phases below the
period. Finitely many conditions whenever `β` and `κ` are finite.

### 182.2 The model-side discipline, and it is already implemented

The corresponding model-side requirement is that the `∃DR` witness be `DR` from
*every* phase, not merely from the demand's own point. That is exactly what
`kernel_site`'s last clause does — it picks **late**, via
`dr_witness_all_below … (i + p)`, yielding

    ∀ b, b ≤ p → I.rho (c (i + b)) w = dr

`drCompat_root_of_phasewise` turns that single fact into both directions of the
label condition: the chain's `∀DR` universals fire on `w` because `w` is `DR`
from every phase, and `w`'s own fire on every phase by the same fact in converse
orientation (`conv dr = dr`). `kernel_dr_drCompat` composes it against
`kernel_site`'s exact output shape, so the connection is **checked, not
asserted**.

### 182.3 `wp130` part F — the discipline, measured

The docstring first said `wp130` "took each demand at its first occurrence".
Checking the probe: it picks a *random* height and accepts any witness `DR` from
that one point. The accurate statement is that it never imposed the
**every-phase** requirement. So part F imposes it, with the prediction stated in
advance — root-level `DRCompat` must read 100%, since that is now a theorem.

| | G1 | G2 |
|---|---|---|
| root-level `DRCompat` (predicted 100%) | **100%** | **100%** |
| full `DRCompat` (whole block) | 90.9% | 74.2% |

Against part B's ~36% for an arbitrary witness. **The lever is the selection
discipline, and the file already has it.**

### 182.4 Position, corrected

§181.4 said the residue was the "above the demand" shape plus non-root nodes.
§182 removes the first half: it was an artifact of measuring in models rather
than certificates, and the discipline that removes it was already written.

What is left is **only the non-root block nodes** §181.1 pins as outside the free
cone — part F's 9–26%. That rate is generator-sensitive (16.7 points between the
two classes, on samples of 44 and 31), so no single number should be quoted for
it; what part F establishes is direction of travel, not a value.

Build: 34,833 lines, 1,746 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`. `drCompat_of_phases` axiom-free;
`kernel_label_occurs_low` propext only.

## 183. THE NON-ROOT NODES — probed, and the probe came back inconclusive

§182.4 left the non-root block nodes as the whole residue. Part F's lever at the
root was a **selection discipline**, so the obvious question is whether the same
lever works one level down: when building the block, prefer witnesses that stay
`DR` from the chain.

`wp130` part G measures it paired — same instances, block built both ways:

| | G1 | G2 |
|---|---|---|
| block witnesses arbitrary | 80.6% | 84.1% |
| chosen `DR`-preserving where possible | **80.6%** | **84.1%** |

Identical. The tempting read is "the discipline does not work below the root".
The instrumentation says otherwise: a `DR`-preserving option existed at ~19% of
steps and **the choice actually changed at 5/250 and 10/292 steps** — 2% and
3.4%. The probe never exercised the lever it was built to test.

**So part G is INCONCLUSIVE, not negative**, and the file records it that way.
Deciding it needs a model class with room for genuine alternatives; the current
generator (chains of length 3 over an 8-element universe) does not supply one.

This is the same discipline as §181.3's catch, applied to a null result instead
of a positive one: **an effect size of zero is only evidence when the treatment
was actually administered.** Both failures were caught by asking what the probe's
sample could not represent — §181.3 counted the non-vacuous instances, §183
counted the steps where the choice differed.

### 183.1 So the generator was changed, and now it decides

Rather than file it, `wp130` gained a third model class **G3** — wider universe
(11 elements), longer chains (4), more elements sampled — chosen so a demand
typically has several witnesses of which only some preserve `DR`.

| | G1 | G2 | **G3** |
|---|---|---|---|
| steps where the choice changed | 2.0% | 3.4% | **7.1%** |
| instances where the two blocks DIFFER | 2 | 1 | **10 of 67** |
| **verdict flips** | **0** | **0** | **0** |

The lever is now genuinely pulled and still flips nothing, in any class. On 13
differing instances the discipline never once fixed a failure — weak evidence in
isolation, but it comes with a mechanism.

### 183.2 The mechanism, which is the actual result

A `DR`-preserving witness exists at only **~20% of steps** in every class. So the
block **cannot be kept fully inside the free cone**, and *partial* preservation
is worthless: the chain's `∀DR.X` fires only on nodes that really are `DR`, so a
block that is 80% preserved discharges none of the obligation at the other 20%.

**That is a structural statement, not a rate.** It says `DRCompat` cannot be
obtained from model-side `DR`-separation of the block at all — which is precisely
why `glueDRMT` DECLARES the relation rather than reading it off. The declared
edge is doing real work here, and the label condition needs an argument of its
own rather than a selection discipline.

### 183.3 What that leaves

The root is a theorem (§182.2). The block interior is not reachable by selection.
So the remaining obligation is: **build `T2` so that the chain's finitely many
`∀DR` bodies hold at every one of its labels** — a construction on the block,
with `drCompat_of_phases` saying how few conditions that actually is, and §180's
consistency result saying the target is non-empty.

Build unchanged: 34,833 lines, 1,746 declarations, 0 errors / 0 warnings /
0 `sorryAx`.

## 184. THE GLUE ON THE FINITE HYPOTHESIS

`glueDRMT_ok` asks for `DRCompat`, which quantifies over all of `β ⊕ κ × Nat`.
No assembly ever has that directly — it has the labels, and §182 says those are
the externals plus the phases below the period.

`glueDRMT_ok_of_phases` is the callable form: four finite conditions in, a valid
`MultiTierOk (glueDRMT T1 T2)` out, `propext` only. It is `glueDRMT_ok` composed
with `drCompat_of_phases`, so nothing new is proved — the point is that the
interface now matches what the extraction can supply, which is the §33 lesson
("ingredients certified ≠ assembly proven") applied before the fact rather than
after.

Build: 34,857 lines, 1,747 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 185. SEPARATION GIVES `DRCompat` OUTRIGHT

§183 showed model-side `DR`-separation of the block cannot be reached by
*selecting* witnesses inside a given model. It did not show separation is
useless — it showed it has to be **built**. So first: what does building it buy?

`drCompat_of_separated` — if two regions really are `DR` from each other, each
side's `∀DR` universals fire on the other directly (`mty_all`), in both
orientations because `conv dr = dr`. No consistency argument, no selection, no
period. `sep_preserves_ex` records the other half: nothing about a cross-`DR`
relation can remove a witness, so the block keeps every demand it served.

## 186. THE SURGERY AS A CONSTRUCTION

`drUnion I1 I2` — the disjoint union of two interpretations with every cross pair
`DR` — and `drUnion_rcc5`: **it is a model** (`propext` only). The cross entries
need only `DR ∈ comp r dr`, `DR ∈ comp dr r`, and `comp dr dr = ⊤`, the first two
being §172's `dr_mem_comp_dr` and its new left-hand twin.

`drUnion_sat` (`propext` only) is the substantial one: **satisfaction survives
the union under exactly `DRCompat` and nothing else.** Every point keeps every
concept of `cl C0` it satisfied before, given that each side's `∀DR` universals
are met on the other. The statement is preservation rather than a biconditional
because the union can only *add* witnesses — a point may satisfy more afterwards,
which is harmless.

### 186.1 Where the obligation actually sits now

Three statements, and the difference between them is the point:

| | |
|---|---|
| `drUnion_rcc5` | the union IS a model — the frame never obstructs |
| `drUnion_drCompat` | `DRCompat` holds in the union — **unconditionally** |
| `drUnion_sat` | satisfaction is preserved — **only under `H1`/`H2`** |

The middle row is free precisely *because* the labels are read off the union: a
universal that cannot be met across is not there to be violated. That is not a
free lunch, and the docstring says so — the cost is paid in the third row, where
the chain must still satisfy `C0` afterwards.

**So the residue is one connective wide.** `∃` demands survive (`sep_preserves_ex`);
`∀PP`, `∀PPI`, `∀EQ` acquire no new neighbours to check, every cross pair being
`DR` — the `drUnion_sat` proof discharges those cases by deriving `r = dr` and
finding a contradiction. **Only `∀DR` can be broken by the surgery.**

That is much sharper than §183's "selection cannot reach the block", and it is
where §180 finally bites: the body set the block must satisfy is consistent, and
`drCompat_of_phases` says only finitely many labels need it. Stated as a
question:

> Given satisfiable `D` and a finite `B ⊆ cl C0`, when is there a model of `D`
> in which **every** point satisfies `⋀B`?

Build: 35,108 lines, 1,755 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`. `drUnion_rcc5` and `drUnion_sat` both `propext` only.

## 187. `hdrk` IS BOUNDED BY THE PERIOD

§165.1 read `kDR` as needing an external `DR` from the whole infinite chain —
that is what `mKdr` (`∀ b ≥ ik k`) demands — and concluded it was a genuine
selection condition `external_stabilizes` cannot supply at `DR`.

Reading the certificate's own obligation instead of the internal helper:

    hdrk : ∀ k e a, a < pk k → O.disj (Sum.inr k) (Sum.inl e) →
      I.rho (g e) (ck k (ik k + a)) = dr ∧ …

**`a < pk k`.** It only ever inspects phases below the period — exactly the range
`kernel_site`'s `DR` clause covers, and covers by construction (late picking,
§182). `hdrk_rel_of_site` (**axiom-free**) is the bridge; the orientation flips
through `conv dr = dr`.

## 188. THE UNBOUNDED QUANTIFIERS WERE NOT LOAD-BEARING

§187.1 left open whether `mKdr`'s unbounded form is needed, and said the way to
find out is to look at the consumers. Doing that:

`hdrk_of_model` concludes at an unbounded `a` and asks for `hseedPhase` and
(through `mixLt_inr_phase`) `hdnphase` at every index. Both proof bodies use
their premises **at exactly the index `a` in the conclusion, and nowhere else.**

So `mixLt_inr_phase_at` and `hdrk_of_model_at` take the premises at `a`. Both
**axiom-free**, and `hdrk_of_model_at_generalizes` checks — rather than claims —
that the original is the instance, so nothing was lost. The originals are
untouched: these are additions, not a refactor.

**Consequence.** A supplier covering one period discharges `hdrk`. §165.1's
framing ("choose the `∃DR` witness so its relation to the chain stabilizes at
`DR`") was reading an artifact of how a helper had been written as if it were a
demand of the logic — the third time this session that a residue turned out to
live in the presentation rather than the mathematics (§182 was the first, §187
the second).

**Still open on this line:** `hdrk`'s two budget conjuncts (`bud e ≤ bk k + 1`,
`bk k ≤ bud e + 1`), which §162's uniform assignment addresses separately; and
`mKdr` itself, which feeds `seedMix`/`odSeed`'s disjointness and is a different
consumer from `hdrk` — §188 does not touch it.

Build: 35,270 lines, 1,759 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 189. THE SAME WEAKENING, FOR THE FOUR REMAINING KERNEL PREMISES

`odSeed_hk_ex` has `hdrk_of_model`'s exact shape: it quantifies `kDIR`, `kDR`,
`kPO`, `kUP`, `kDN` over **all** phase indices, and its proof hands each of them
the single `a` from the conclusion and nothing else.

`odSeed_hk_ex_lt` bounds all five premises and the conclusion by `a < pk k` —
the range `kernel_site` covers. Same proof, `ha` threaded through.

## 190. AND THE OBLIGATION CHAIN ABOVE IT, WEAKENED IN PLACE

§189 is only useful if the consumer accepts the bounded form. Following the
chain — `mergedMT_ok` → `mtkKernelsOD_of_debts` → `mtkKernelsOD_ok` → the
certificate's `k_ex` field — the last step reads

    k_ex := fun k a _ r D hmem => hk_ex k a r D hmem

**The bound `a < T.p k` is available at every level and simply discarded.** So
this was not a limitation; it was an unused hypothesis.

Each of the three theorems has exactly **one** real call site (and `mergedMT_ok`
is the capstone, with none), so the weakening was done in place rather than by
duplication: `hk_ex` now reads `∀ k a r D, a < pk k → …` in all three, and the
forwarding names the bound instead of dropping it. **No call site needed
changing** — the pass-throughs matched automatically, which is itself evidence
the strength was never used.

### 190.1 What this unblocks

The kernel-existential obligation now needs model facts **only at phases below
the period**. That is exactly what `kernel_site` has supplied since round E2b:

    ∀ a r D, a ≤ p → (r = dr ∨ r = pp ∨ r = ppi) →
      Concept.ex r D ∈ mty C0 I (c (i + a)) →
      ∃ w, I.dom w ∧ D ∈ mty C0 I w ∧ ∀ b, b ≤ p → I.rho (c (i + b)) w = r

So `kDR`, `kUP`, `kDN` — three of §163.3's four, and the ones §165.1 called
selection disciplines requiring stability along an infinite chain — are now
range-matched to a tool the file already had.

**Two gaps remain between the two statements, and neither is the range.**

* `kernel_site` produces a model ELEMENT `w`; `kDR` wants an external INDEX `f`
  with `g f = w`, plus the `seed`/`up`/`dn` bookkeeping placing it correctly.
  That is the routing, and it is real work.
* `kernel_site` gives `D ∈ mty C0 I w`; `kDR` wants `D ∈ mtk C0 I (g f) (bud f)`
  — TRUNCATED membership, so a budget must be assigned with
  `mdepth D < bud f`. That is §162's uniform-assignment question, not a new one.

**What is settled is the existence of the witnesses**, which is what §165.1 said
was the obstruction.

### 190.2 The pattern, fourth and fifth instances

§182 found "above the demand" was a property of models, not certificates. §187
found `hdrk` bounded. §188 found `hdrk_of_model`'s quantifiers unused. §189 and
§190 are the same again, at the other four premises and then at the three
signatures above them.

**Five times in two sessions the obstruction was in how something was written
down, not in the mathematics.** The move that finds it is always the same: read
the obligation the consumer actually states, and check which hypotheses its proof
touches — rather than reasoning about the helper's statement.

Build: 35,365 lines, 1,760 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 191. ONE SEGMENT CARRYING BOTH — `ascKernel_serves`

§190.1 said what remains for `kDR`/`kUP`/`kDN` is routing, not existence. Tracing
where the witnesses would actually come from ran into a real-looking obstacle:

* the kernel's segment is chosen by `rr_segment_from`, so that `rr_covers` can
  supply `kDIR`;
* the witnesses come from `kernel_site`, which chooses its segment by
  `segment_select`.

**Two selectors, one kernel.** Reading the proofs rather than the statements
dissolved it, twice over:

1. `rr_covers`'s `hdvd : Ds.length ∣ p` is consumed **once**, as
   `Nat.le_of_dvd hp hdvd`, purely to get `Ds.length ≤ p`. Divisibility is never
   used. `rr_covers_le` takes the inequality instead, and
   `rr_covers_le_generalizes` checks the original is the instance. That is the
   §188 pattern for the **sixth** time.
2. The cofinal recurrence the witness branches run on comes from
   `recurrent_tail`, which is a property of a **TAIL, not of a segment** — so it
   survives any later segment choice, and `rr_segment_from`'s `L0` parameter
   pushes the base past its threshold.

So one segment carries both. `ascKernel_serves` returns, from a single node with
nonempty `persistDs`: the chain, base, period, `hty`, **`kDIR`** (every
persistent demand inside the period) **and** for every phase `a ≤ p` and every
`DR`/`PP`/`PPI` demand there, a witness `w` with `D ∈ mty w` and
`∀ b ≤ p, I.rho (c (i+b)) w = r`.

That last clause is `hdrk`'s bounded range exactly (§187), and by §§189–190 the
bounded range is all the obligation asks for.

### 191.1 Position

**Existence is now settled for all four kernel-existential premises.** `kDIR` was
already `ascKernel_of_node`'s; `kDR`, `kUP`, `kDN` now come from the same
construction on the same segment.

What remains for them is what §190.1 named and this section does not touch:
the **index routing** (a model element `w` must become an external index `f` with
`g f = w`, plus `seed`/`up`/`dn` placement — the shape `one_kernel_block` already
implements for a single kernel via its subtype `W`), and the **`mty`-to-`mtk`
budget** (`mdepth D < bud f`, §162's uniform assignment).

Build: 35,484 lines, 1,763 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 192. THE WITNESSES, CARRIED THROUGH TO THE KERNELS THE EXTRACTION BUILDS

§191 certified `ascKernel_serves` in the abstract. The certificate does not use
it directly — it uses `kFam`, which is `kernelData`, which was
`Classical.choose` of `ascKernel_of_node`. So the serving clause had to reach
that far or it was decoration.

**It reaches it with no new structure.** `kernelData` now chooses from
`ascKernel_serves` instead, so the *same* `Classical.choose` that fixes a
kernel's chain, base and period also fixes its off-direction witnesses;
`kernelData_serves` is another projection of that one choice. No field was added
to `KernelData` — deliberately, because there is a third construction site
(`kernelData_of_chain`, §114) built from an arbitrary chain, and a mandatory
field would have obliged it to supply something it has no source for.

`descKernel_serves` + `rr_coversI_le` mirror the ascending side exactly
(`ddrpp_witness_bank` for `DR`/`PP`, `dppi_witness_all_below` for the direction's
own `PPI`, as in `dkernel_site`), and `mKernel_serves` lifts both to `KIdxM` —
the shape the obligations consume.

### 192.1 Position

**Existence is settled for `kDR`, `kUP`, `kDN` on the kernels the extraction
actually builds**, not merely on an abstract kernel. What remains is what §190.1
named:

* the **index routing** — the witness is a model element, the certificate wants
  an external `f` with `g f = w` plus `seed`/`up`/`dn` placement.
  `one_kernel_block` implements exactly this for a single kernel, via a subtype
  `W` = context ∪ chosen witnesses, and its `hserve` premise is *literally*
  `mKernel_serves`'s conclusion. Lifting `W` to the merged family is the next
  brick.
* the **`mty`→`mtk` budget** — `mdepth D < bud f`, §162's uniform assignment.

### 192.2 On route churn, measured

Asked whether this work re-does abandoned routes. It does not, and the file says
so: of 1,758 declarations, 331 are never referenced elsewhere — but those are
overwhelmingly non-vacuity witnesses and capstones, and **only ~10 belong to the
abandoned frames** (`mixKernelsK`, `mtkKernelsDir`). Today's ingredients date
from 2026-07-23 (`kernel_site`, `one_kernel_block`), 08-05 (`rr_covers`) and
08-21/22 (`mtkKernelsOD_ok`, `ascKernel_of_node`) — `kernel_site` was built for
the original two-tier route and is consumed unchanged today, two frame pivots
later.

**The pivots changed the certificate FRAME, not the model-side analysis.** The
segment selectors, witness banks and round-robin machinery survived all of them.

What *is* a real cost is different and worth naming: the over-strong statements
§§188–191 keep weakening were written before their consumers existed. That is
rework, not backtracking — nothing was deleted, and the originals remain
instances (`hdrk_of_model_at_generalizes`, `rr_covers_le_generalizes`) — but it
is the 2026-08-22 lesson *write the consumer before believing the interface*
recurring for the sixth time.

Build: 35,633 lines, 1,768 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.

## 192.3 `mKdr` BOUNDED — the step the routing actually needed

The routing needs `seed (Sum.inr k) (Sum.inl f)`, and in `mergedMT_ok` that is
`mKdr`: `DR` from the chain at **every** `b ≥ ik k`. `mKernel_serves` gives `DR`
at `b ≤ p`. §165.1 was right that the unbounded form cannot be supplied from
below — a witness `DR` from an entire infinite chain needs cofinal `DR`, which
nothing produces. **So bounding `mKdr` was not an optimisation; it was
necessary.**

`seedMix` is parameterised by `kdr`, so `mKdr` is only an instantiation. It is
now

    ∀ b, b ≤ mPk … k → I.rho (mCk … k (mIk … k + b)) (nd e).x = dr

Everything downstream followed the §188 pattern once more. Two model-side
theorems asked for their premises at every index and used them at one:

* `hdrk_of_model` → `hdrk_of_model_at` (§188, already in place), with
  `mixLt_inr_phase_at` specialised to its own kernel;
* `hqdr_of_model` → `hqdr_of_model_at`, which uses its descent and seed facts at
  exactly `(k,a)` and `(k',b)` and now takes those four directly.

Both `mergedMT_ok` call sites had the bound available and discarded
(`intro k e a _ hdj`, `fun k k' a b _ _ hdj`) — the seventh and eighth instances.

## 193. THE INDEX ROUTING, ISOLATED

With `mKdr` bounded, the seed a kernel needs to an external is *exactly*
`mKernel_serves`'s output. The one thing still standing between the certified
witnesses and `kDR` is that the witness be **in** the family: a model element `w`
must be some `(nd f).x`.

`WitnessClosed hI C0 nd L0` says precisely that — every off-direction witness a
kernel of the family needs is itself indexed by the family. And then:

| | |
|---|---|
| `kDR_of_witnessClosed` | `∃f`, `mKdr k f` ∧ `D ∈ mty (nd f).x` |
| `kUP_witness_of_witnessClosed` | the `∃PP` half |
| `kDN_witness_of_witnessClosed` | the `∃PPI` half |

So the remaining construction has a **specification**, not a description: build a
family that is witness-closed. `one_kernel_block` does it for a single kernel via
its subtype `W` = context ∪ chosen witnesses; the merged case is a fixpoint,
because a witness with nonempty `persistDs` becomes a new kernel anchor
(`KIdxM` is a subtype of `β`) whose own witnesses must then be added.

**That fixpoint is the honest remaining item**, and it does not terminate by
budget decrease — kernel witnesses sit at the kernel's budget, not below it
(`hbK` puts them within one). Termination has to come from the support-label
depth measure of §§140–155, which is what that machinery was built for.

Build: 35,795 lines, 1,773 declarations, exit 0, 0 errors / 0 warnings /
0 sorries / 0 `sorryAx`.
