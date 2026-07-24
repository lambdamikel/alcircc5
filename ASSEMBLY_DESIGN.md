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
