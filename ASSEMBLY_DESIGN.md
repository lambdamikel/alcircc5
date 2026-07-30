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
