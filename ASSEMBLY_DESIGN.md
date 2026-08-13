# The ∀PO-free assembly recursion — design sketch

*2026-07-23. A design note for the final construction of the ∀PO-free
fragment certification campaign (`formal/POFreeLift.lean`, rounds
A–E3g′). Not a proof; a map from the certified infrastructure to the
remaining `Decidable (Satisfiable C₀)` theorem, with the hard cases
located and their resolutions identified. Prose only — no Lean written
under-designed (the round-19/20 lesson).*

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
