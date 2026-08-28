# Attack request — the MIXED QUADRANT of the ∀PO-free fragment of ALCI_RCC5

You are a fresh, expert collaborator: strong in description logics, qualitative
spatial reasoning (RCC5/RCC8), modal/tableau methods, and finite combinatorics.
You have **no stake** in this development and have not seen it before.

**This is not a referee request.** Earlier documents in this line were
adversarial reviews ("find the defect"). This one is different: a decidability
argument has been driven down to **three named open problems**, and I want you to
**attack the mathematics**. A "gap" verdict is not the goal; *progress on any of
the three* is. A proof, a counterexample, a sharpened reduction, a decidable
sub-case, or a formal equivalence are all real wins. An honest "I could not move
it, and here is precisely why" is also useful.

Read **§0** before anything else. Several past reviewers lost findings to the
assumptions listed there, and **§4 lists routes that have already been refuted
with machine-checked witnesses** — proposing one of those is the main way to
waste your effort.

---

## 0. Primer — assumptions you must NOT misread

The object logic is **ALCI_RCC5**: ALCI with five role names interpreted as the
RCC5 base relations {EQ, PP, PPI, PO, DR}, under **abstract composition-table
semantics** (a model is a set with a total, converse-closed, composition-closed
labelling of ordered pairs — *not* a set of actual regions). Concept
satisfiability is open since Wessel 2002/2003.

We work in the **∀PO-free fragment**: no `∀PO.C` in the input's closure. `∃PO` is
allowed. This matters constantly — see (6).

1. **A certificate is a FINITE syntactic object; its model may be INFINITE.**
   A concept forcing an infinite model (`∃PP.⊤ ⊓ ∀PP.∃PP.⊤`) is perfectly
   satisfiable and within the framework. **Do not offer an infinite-model-forcing
   concept as a counterexample to anything.** The question is always about
   *finite width / finitely many node kinds*, never about depth.

2. **Strong-EQ semantics.** `EQ` is identity; it holds only on the diagonal.
   Between distinct elements only {DR, PO, PP, PPI} occur.

3. **Inverse roles are absorbed** (`PP⁻ = PPI`). Concepts are in NNF.

4. **Two axes.** `PP/PPI` are vertical (proper part / proper superpart). `DR/PO`
   are horizontal (discrete / partial overlap). `x PP y` means x is a proper part
   of y, so y is ABOVE x.

5. **Forced cells you will use constantly.**
   `comp(PP,PP) = {PP}`, `comp(PP,DR) = {DR}`, `comp(DR,PPI) = {DR}`.
   Every non-trivial cell containing EQ also contains PP, PPI and PO, so **EQ is
   never forced** between distinct elements.

6. **In this fragment a PO edge carries NO universal obligation.** Since `∀PO`
   never appears in the closure, a declared PO edge imposes nothing on either
   endpoint. This is what makes `∃PO` cheap and is used throughout.

7. **RCC5 has the patchwork property** (Renz–Nebel): composition-closed atomic
   networks amalgamate. Assume it.

---

## 1. Where the development stands

Machine-certified in Lean 4 core (no mathlib), ~41,400 lines, 0 sorries,
0 warnings, axioms `propext` / `Quot.sound` / `Classical.choice` only:

* **Three of the fragment's four quadrants are certified decidable in general** —
  horizontal (`∃DR/PO/EQ` + non-PO universals), ascending vertical (`∃PP`),
  descending vertical (`∃PPI`).
* The **mixed** quadrant (`∃PO` *and* `∃PP` together) is the open one. Its
  decision pipeline is proved end-to-end on a witness; what is missing is the
  general **extraction** — building a finite certificate from an arbitrary model.

The certificate is a **`MultiTier`**: a finite set of *external* nodes each with
a label, plus finitely many *kernels* (periodic infinite towers, each with a
finite list of phase labels), over a **declared** ordered-disjoint frame. See
`CERTIFICATE.md` for the exact 19 obligations.

**Extraction, current state.** Read labels off a model as full model types
(`mty x` = the subformulas of `cl C₀` true at `x`); take the node set to be the
demand closure; block by model type (a node whose type already occurs is not
expanded); serve blocked nodes' demands by a DECLARED edge to the blocker's
witness. Certified: the node set is finite, bounded by
`|ns₀| + |typeEnum C₀|·|cl C₀|`, reached in that many rounds, and every
existential of every node is served by a kernel or inside the set. Certified
also: propagation along declared edges, all four universal obligations given a
constant "row", and the kernels' own phase obligations.

**Three things are open. They are §§2–4 below.**

---

## 2. TARGET A — the GROUP problem  *(recommended; freshest and sharpest)*

### The statement

Blocking identifies nodes by **model type**. For each type, one node `a` (the
*gate-mate*) is expanded and spawns **one child per demand**; the other nodes of
that type are blocked and must borrow.

Let `T` be a model type with `∃PP.D ∈ T`, and let `G = {a, v₁, …, v_k}` be the
nodes of type `T` in the node set. Each `vᵢ` owes `∃PP.D`. The construction
declares the edge `vᵢ < w` where `w` is `a`'s child for that demand.

**For the declared order to be a strict order, `w` must not lie below any `vᵢ`.**
It is a THEOREM (certified) that for a *single* `vᵢ` such a `w` always exists:
if the greedy choice fails then `a < vᵢ`, so `vᵢ`'s own witness is also a witness
of `a` lying above `vᵢ` (`comp(PP,PP) = {PP}`).

**The open question is whether ONE `w` can serve the WHOLE group:**

> Given pairwise-incomparable elements `v₁, …, v_k` of the same model type, each
> satisfying `∃PP.D`, must there exist a single `w` with `vᵢ PP w` for all `i`
> and `D` true at `w`? If not, what bounded repair serves them all?

### What is measured (probe `wp131`, included)

On 1,040 instances across four model classes, conditioned to actually contain
borrowed edges:

| | random \|U\|=4 | random \|U\|=5 | chain \|U\|=6 | chain \|U\|=8 |
|---|---|---|---|---|
| one witness serves the whole group | 77.5% | 76.0% | 99.4% | 99.8% |

**91.8% overall — so the answer to the question as posed is NO.** And in
**0 of 140** failing groups is there *any* common PP-upper carrying `D` in the
model, and in **0 of 140** are the members pairwise comparable. So this is a
genuine model-level obstruction, not an artifact of how the witness is chosen.

(The comparable case is already solved: if the group is a chain, a high enough
element of the tower is above all of them — certified as `common_upper_on_tower`.
The residue is exactly the incomparable, no-common-upper case, and it is
concentrated in the *horizontal* model classes.)

### Why it is hard, and why it might not be

The obvious repair — give each `vᵢ` its own child — is exactly what blocking
exists to prevent: the node set is bounded only because blocked nodes do not
expand. Spawning per blocked node restores unbounded growth.

The lead we have not tested: **declare a fresh "class top"** — a single new node
`t` with `vᵢ < t` for all `i`, labelled with `D` plus every `∀PP`-body that any
`vᵢ` owes. Adding a common upper bound to a strict order is always
order-consistent, and in this fragment the horizontal relations among the `vᵢ`
impose nothing on `t` beyond composition. **The question is whether that label is
always realizable** — i.e. whether `D ⊓ ⨅{E : ∀PP.E ∈ T}` is satisfiable whenever
`∃PP.D ∈ T` and `T` is realized. Note every `vᵢ` has the SAME type `T`, so the
label is determined by `T` alone, which is a finite syntactic object. **We think
this is the most promising single question in the packet.**

### What would count as progress

- A proof that the class-top label is always realizable (⟹ the group problem is
  solved and the node cost is one node per (type, demand), which the existing
  bound absorbs).
- A counterexample: a satisfiable `C₀`, a type `T` with `∃PP.D ∈ T`, and a proof
  that `D ⊓ ⨅{E : ∀PP.E ∈ T}` is unsatisfiable.
- Any other bounded repair, or a proof that no bounded repair exists (which would
  refute this whole blocking architecture and be very valuable).

---

## 3. TARGET B — the CROSS-KERNEL RECTANGLE

Kernels are periodic ascending or descending towers. Two obligations concern a
kernel's relation to things outside it:

* `hke` / `hek` (kernel ↔ external) — **DISCHARGED**, because a finite list of
  externals fixed in advance has a uniform index past which every row from the
  chain is constant (`externals_stabilize`), so the declared edge can take that
  constant value.
* `hkq` (kernel ↔ kernel) — **OPEN**. It needs the row from kernel `K` constant
  over the *target* kernel `K'`'s phases. But `K'`'s phase points are determined
  only once `K'` is built, and `K'`'s construction may depend on `K`.

> **The question.** Given finitely many kernels extracted from one model, can
> their segments be chosen simultaneously so that every cross-kernel row is
> constant on both sides? Equivalently: is there a simultaneous stabilization
> theorem for finitely many interacting periodic towers?

Note the shape: `externals_stabilize` works because the externals are FIXED
POINTS. Here both sides move. A product/diagonal argument is the obvious first
try; a counterexample would be a pair of towers whose mutual rows cannot be
simultaneously stabilized.

**Target C is the same obstruction in different clothes**: the kernel's own
existential demands need witnesses placed in the *external* node set, but the
external list must be fixed BEFORE the segment is chosen. If you resolve B, say
whether your argument also resolves C.

---

## 4. ROUTES ALREADY REFUTED — do not re-propose these

Each has a machine-checked witness. Re-deriving one is the main failure mode.

1. **Identify the blocked node with its blocker** (`L_Q(π,π) = EQ`). Collapses
   laps into semantic equality and breaks `∃PP.⊤ ⊓ ∀PP.(∃PP.⊤)`. Blocking here
   must be occurrence-sensitive: a PP-labelled edge between DISTINCT occurrences,
   never an identification.

2. **Repeat-free chain selection to get acyclicity.** Refuted by `wp131`
   (included): 5 surviving cycles in 1,040 instances, and in every survivor there
   were ZERO repeat-free candidates, so the discipline could not even be applied.
   Four of five survivors had the borrowed witness EQUAL to the blocked node.

3. **Read-off relations everywhere with budget-truncated labels.** Makes
   `ee_all` fire on every pair while the finiteness recursion drops the budget
   (`wp96` A: 4.1% break).

4. **A PO-default frame** (comparable ⟹ PP/PPI, otherwise PO). Cannot express
   the order `comp(PP,PP) = {PP}` forces between two kernels sharing an external
   (`wp96` C, `wp97`).

5. **A poset frame with no DR.** `∃DR` becomes inexpressible (`wp93`).

6. **An algebra-only support-compression proof of bounded width.** Refuted for
   the FULL logic by `wp44`: for every n there is a composition-closed RCC5
   network with separator-cover number exactly n. (This concerns the full logic's
   open problem F6, not the fragment, but the same instinct recurs here.)

7. **Off-the-shelf guarded/clique-guarded covers.** RCC5 totality makes every
   Gaifman graph complete (`wp78`).

---

## 5. What is in this packet

```
ATTACK_PROMPT.md    this file
CERTIFICATE.md      the certificate's exact 19 obligations, self-contained
probes/             runnable, self-contained Python (no dependencies)
run_probes.sh       runs them
```

The probes re-derive the RCC5 composition table from finite set semantics, so
nothing is taken on trust. `wp131` is the one that matters for Target A: parts
N (non-vacuity), B (the certified dichotomy as a regression), D (cycles arise),
C/F (repeat-free vs model-agreeing selection), G (the fallback), and Q (the
group residue, with the 0/140 diagnosis).

**Scope honesty.** All probe evidence is finite randomized sweeps over finite set
models, so kernels are NOT exercised by them. The kernel facts cited above are
Lean-certified, not probe-measured. The 91.8% and the 0/140 are measurements, not
theorems.
