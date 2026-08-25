# ASSEMBLY_DESIGN sections 43-60 (excerpt for review)

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
| served IN-KERNEL (`X` recurs on the chain) | **89.2%** — FREE |
| need an EXTERNAL | 10.8% |
| external count at windows 2p / 4p / 8p / 16p | **(1, 1, 1, 1) in every case — FLAT** |
| cases needing an unbounded/growing set | **0** |

### 49.1 Why — and this half is a THEOREM, not a measurement

For an ascending kernel `c(0) PP c(1) PP …` with `∃PP.D` present cofinally:

**Case (a) — `D` recurs on the chain.** Served in-kernel; zero externals. 89.2%.

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
is model-independent, and by the 89.2% in-kernel rate, which is not.

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

**Only the IN-KERNEL rate is stable** across all four model-class variants:
**89.2 / 90.2 / 83.5 / 91.3%**. Every other rate moved when the class changed.
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

1. **chain recurrence** → served in-kernel, cost 0 (~90% measured);
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
| `ee_all` cap↔cap (`PO`) | `cap_po_cap` + `mty_no_all_po` |
| `ee_all` cap→outside (`PO`) | `cap_po_outside` + `mty_no_all_po` |
| `∀DR` at a cap | **`cap_no_dr_edge` / `cap_no_dr_edge'`** — no `DR` edge touches a cap |
| `ek_all` / `ke_all` kernel↔cap | same two lemmas, phases inside the window |
| frame | `odSeedCap_frame` |
| **`e_ex` for cap nodes** | **the one open row** |

### 57.3 So the mixed quadrant is down to one row

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
| mixed: frame, transfer, both `∀` directions, `e_ex` at `eq`/`pp`/`ppi`/`po` | **done** |
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
