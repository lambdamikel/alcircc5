# The poset bridge: two-variable logic over partial orders inside ALCI_RCC5

*2026-11-11. Written by Claude Fable 5.2 at Michael Wessel's request ("see if you
can advance the decidability status for the full logic"), from the repository at
`52d392e`. **Unreviewed.** By this project's own ledger a defect or overclaim was
found in 19 of 22 reviews; presume this note has one.*

Artifacts: [`formal/PosetBridge.lean`](../../formal/PosetBridge.lean) (1,354 lines,
0 errors / 0 warnings / 0 `sorry`, imports the certified artifact) and
[`verification/python/wp137_poset_bridge_probe.py`](../../verification/python/wp137_poset_bridge_probe.py)
(27/27 checks pass).

---

## 0. What moved, and what did not

**Decidability of full ALCI_RCC5 is still open.** Nothing here settles it. Five
things changed around it.

1. **A cited theorem does not exist.** The overview, the fragment paper and the
   closing entry of `CONVERSATION.md` say that two-variable logic with one
   transitive relation "is decidable" (Szwast & Tendera, STACS 2013). The
   authors withdrew that claim in 2018; the problem is open. (§1)
2. **The full logic contains that open problem.** Read `∃PO.C ⊔ ∃DR.C` as "some
   incomparable region is a C" and `∀PO.C ⊓ ∀DR.C` as "every incomparable region
   is a C". The concepts that use `∃DR` and `∀PO` only in those two combinations
   form a syntactic fragment **L∥** of ALCI_RCC5, and satisfiability in L∥ is
   *exactly* satisfiability of two-variable first-order logic over strict
   partial orders with unary predicates (FO²_u1PO). Lean-checked, no fragment
   hypothesis on the RCC5 side. So a decision procedure for ALCI_RCC5 would
   settle FO²_u1PO, whose general satisfiability problem the FO² literature
   still lists as open; and undecidability there would settle ALCI_RCC5
   negatively. (§§2–3)
3. **Two new decided slices, both with `∀PO` constraints that bite** — by
   import, not by a new proof: L∥ with vertical witnesses only (2-NExpTime), and
   *finite* satisfiability for all of L∥ (2-NExpTime). (§4)
4. **An infinity axiom with no `∃PP` and no `∃PPI`.** Lean-checked: a concept
   whose only witnesses are overlaps and disjoint regions, and all of whose
   models are infinite. (§5)
5. **The cover-tree tableau returns a wrong verdict.** `K2 = ∃PO.(A ⊓ ∀PO.¬B ⊓
   ∀DR.¬B) ⊓ ∃PO.(B ⊓ ¬A)` has a three-region model (Lean-checked); the tableau
   answers UNSAT. The statement "no verdict of the cover-tree tableau has ever
   been shown wrong" (README ×2, overview ×5, slides, `CLAUDE.md`) is no longer
   true. (§6)

What did **not** move: F6, the cone scheme's architectural `∀PO` gap for *bare*
`∀PO` (`C_bad`, `C_joint`), and everything about how `DR`'s downward closure
interacts with `∀PO`. §7 says what the bridge suggests about them.

---

## 1. A correction: the 2013 theorem was withdrawn

Three places in the repository rely on this sentence or a variant of it:

> Two-variable first-order logic with one transitive relation is decidable
> [Szwast & Tendera 2013].

(`papers/pofree_fragment_arxiv.tex` §Related work, and again in its discussion;
`papers/overview_arxiv.tex` conclusion, "a decidable logic"; `CONVERSATION.md`
2026-09-14, "decidable, Szwast & Tendera 2013". It entered through GPT-5.6 Sol's
review, which states it the same way; that archive is left as it is, with an
erratum in its folder's README. The two papers are corrected in the same change
set; the `CONVERSATION.md` entry is history and stays, with a new entry after
it. The public record of both corrections is [`ERRATA.md`](../../ERRATA.md).)

The record is:

| year | result | source |
|---|---|---|
| 2013 | general satisfiability of FO² with one transitive relation claimed decidable | Szwast & Tendera, STACS 2013 |
| 2018 | claim **withdrawn** by its authors: the proof is flawed; decidable only when every existential quantifier is guarded by a transitive atom (2-NExpTime); the status of the full problem "remains open" | Szwast & Tendera, arXiv:1804.09447 |
| 2018 | **finite** satisfiability decidable: 3-NExpTime, and 2-NExpTime when the relation is a partial order | Pratt-Hartmann, Math. Log. Quart. 64(3) |
| 2026 | still open; with equality the problem reduces to a strict partial order; decidability *conjectured*; proved only for restricted fragments; even the unary-signature core with entanglements and incomparable witnesses is left open | Marzec & Tendera, J. Logic Comput. 36(2) |

So the lead "the two-copy encoding lands near a decidable logic" pointed at a
logic that is not known to be decidable. That weakens the lead. It also turns
out that the relationship runs the other way round, and exactly: §2.

---

## 2. The incomparability fragment and the bridge

In an RCC5 structure `PP` is a strict partial order (irreflexive by reflexive-EQ,
transitive by `comp(PP,PP) = {PP}`), and two distinct regions are incomparable in
it iff they are `PO` or `DR`. Write `x ∥ y` for that.

**Definition (L∥).** An NNF concept is in L∥ if every `∃DR.C` in it occurs as the
right disjunct of `∃PO.C ⊔ ∃DR.C`, and every `∀PO.C` as the left conjunct of
`∀PO.C ⊓ ∀DR.C`. A bare `∃PO.C` and a bare `∀DR.C` are allowed; a bare `∃DR.C`
and a bare `∀PO.C` are not. In Lean, L∥ is the image of `emb`.

For `C ∈ L∥` let `C♭` be its reading over a strict partial order `(Δ, <)`:

| in `C` | in `C♭` |
|---|---|
| `∃PP`, `∃PPI`, `∀PP`, `∀PPI`, `∃EQ`, `∀EQ` | `∃<`, `∃>`, `∀<`, `∀>`, `∃=`, `∀=` |
| `∃PO.D ⊔ ∃DR.D`, and a bare `∃PO.D` | `∃∥.D♭` |
| `∀PO.D ⊓ ∀DR.D` | `∀∥.D♭` |
| a bare `∀DR.D` | `⊤` |

**Theorem 1 (the bridge; `poset_bridge`, `poset_bridge_fin`).** A concept
`C ∈ L∥` is satisfiable in ALCI_RCC5 iff `C♭` is satisfiable over a strict
partial order. The same holds with "finite model" on both sides.

*Proof.* (⇐) Given `(Δ, <)`, declare every incomparable pair `PO` and leave `DR`
empty. That is an ordered-disjoint structure, so by the certified `odNet_frame`
it is an RCC5 frame. Truth is preserved by induction on the NNF concept: an
`∥`-witness is a `PO`-witness; `∀PO` ranges over exactly the incomparable
pairs; `∀DR` is vacuous. (⇒) Given an RCC5 model, keep its domain and take
`PP` as the order. A `PO`- or `DR`-witness is an `∥`-witness; `∀∥.D` holds
because *both* `∀PO.D` and `∀DR.D` did; a bare `∀DR` became `⊤`, which can only
help. Both constructions keep the carrier. ∎

The two excluded constructors are excluded for a reason, and the probe exhibits
it (`wp137` C5, C6): a bare `∀PO.⊥` holds at one of two disjoint regions but
`∀∥.⊥` fails there; and `∃∥.⊤` holds at one of two incomparable points but
`∃DR.⊤` fails in the `PO`-reading.

L∥ is therefore the part of ALCI_RCC5 that cannot see how incomparability
*splits* into overlap and disjointness. Everything else in the logic — bare
`∃DR`, bare `∀PO` — is what can.

---

## 3. The first-order face: FO² over strict partial orders

Lutz & Wolter (2006, Theorem 2 and its RCC5 analogue in §8) already show that the
modal language over the RCC5 relations has the expressive power of the
two-variable fragment over those relations with unary predicates. Restricting
that to the sublanguage of §2 gives the two-variable logic of a *single strict
partial order*:

**Theorem 2 (`patsys_bridge`, `patsys_to_rcc5`).** Let a *pattern system* be a
finite set of constraints of the two shapes

```
forbidden    ∀x∀y ¬( τ(x) ∧ r(x,y) ∧ τ'(y) )
required     ∀x ( τ(x) → ⋁ₒ ∃y ( rₒ(x,y) ∧ τₒ(y) ) )
```

with `τ, τ'` conjunctions of unary literals and `r ∈ {=, <, >, ∥}`. A pattern
system has a non-empty strict-partial-order model iff the concept
`emb(S.toConcept) ∈ L∥` is satisfiable in ALCI_RCC5.

Every sentence of FO²[<, =, unary] is equisatisfiable over strict partial orders
with a pattern system (Scott normal form, then expansion over 1-types — standard,
and *not* formalized here), and the basic normal form (B1)–(B10) that Marzec &
Tendera use for FO²_u1PO is of this shape once its unary conditions are written
as disjunctions of literal conjunctions. Conversely every L∥ concept
is a two-variable sentence by the standard translation. Hence:

> **SAT(FO²_u1PO) and SAT(L∥) are the same problem**, up to computable
> translations, for general and for finite satisfiability.

**Corollary 3 (`decidablePSat_of_full`, `decidablePatSat_of_full`).** A decision
procedure for ALCI_RCC5 concept satisfiability yields one for FO²_u1PO. An
undecidability proof for FO²_u1PO would make ALCI_RCC5 undecidable.

What is known on the FO² side (§1): general satisfiability of FO² with one
partial order is open and conjectured decidable; Marzec & Tendera prove it only
without "entanglements" — universal constraints `∀x∀y(α(x) ∧ β(y) → x<y ∨ y<x)`
between distinct 1-types — and single out the unary fragment with entanglements
and incomparable witnesses as the critical open core. In RCC5 words that core is

```
α ⊑ ∀PO.¬β ⊓ ∀DR.¬β          (an α and a β are never incomparable)
α ⊑ ∃PO.β ⊔ ∃DR.β            (every α has an incomparable β)
```

imposed globally. No `∃PP`, no `∃PPI`. That is a far smaller sublanguage than
the one this project has been treating as the hard part, and its difficulty
uses a single, deterministic cell of the composition table: two regions that
may be neither `PO` nor `DR` **must be nested**, and nesting is transitive.

Scope, stated exactly. (i) The Lean theorem is about pattern systems; the step
from an arbitrary FO² sentence to a pattern system is textbook and unformalized.
(ii) "Open" is the literature's status as of Marzec & Tendera (published online
January 2026); I found nothing later, and I could read only the abstract,
introduction and the 2024 workshop version of that paper in full. (iii) The
embedding covers the *unary* signature. Full FO² with one transitive relation
allows further binary predicates, and I do not see how to embed those.
(iv) There is no reduction in the other direction: `DR`'s downward closure is a
three-variable condition that a single transitive relation does not obviously
simulate. ALCI_RCC5 may be strictly harder.

---

## 4. What the literature then gives for free

These are *imports through Theorem 1*: decidability by reduction to a published
theorem. They are not Lean-checked beyond the bridge and they inherit whatever
the cited proofs are worth.

**(a) L∥ with vertical witnesses only is decidable, in 2-NExpTime.** Take
`C ∈ L∥` with no `∃PO` at all (so every existential is `∃PP`, `∃PPI` or `∃EQ`).
Then `C♭` translates to a two-variable sentence all of whose existential
quantifiers are guarded by the order, which is the fragment Szwast & Tendera
(2018) decide. One detail: "some element satisfies `C`" is an unguarded
existential. Remove it by adding a top element outside the domain:
`∀x(¬Dom(x) → ∃y(y<x ∧ Dom(y) ∧ P_C(y)))` and `∀x(Dom(x) → ∃y(x<y ∧ ¬Dom(y)))`,
with everything else relativized to `Dom`.

This slice is not `∀PO`-free, and — unlike in 𝒟 — its `∀PO` constraints are not
erasable. Write `W(P,Q) = P ⊓ ¬Q ⊓ ∀PO.¬Q ⊓ ∀DR.¬Q ⊓ ∀PPI.¬Q` ("I am a `P`, and
every `Q` is strictly above me"). Then

```
C_cyc = ∃PP.W(A,B) ⊓ ∃PP.W(B,C) ⊓ ∃PP.W(C,A)
```

is unsatisfiable: its three witnesses satisfy `a ⊂ b ⊂ c ⊂ a`. Each pair is
compatible on its own; the conflict is the cycle. Erase the three `∀PO`
conjuncts and it is satisfiable, by three pairwise overlapping regions
(`ccyc_unsat`, `ccycErased_sat`; `wp137` E4, E5). So this is the first decided
slice of ALCI_RCC5 in which a `∀PO` constraint can change the answer. It also
contains the coupled form of `C_sat`, `∃PP.(A ⊓ ∀PO.A ⊓ ∀DR.A) ⊓ ∃PP.¬A`.

It does **not** contain `C_bad` or `C_joint`, whose `∀PO` is bare. Coupling
`C_bad` (adding `∀DR.¬A`) keeps it unsatisfiable but for a trivial reason — the
root then tolerates no other `A` anywhere — so the coupled form no longer tests
what `C_bad` tests, namely that two regions with a common part cannot be
disjoint.

**(b) Finite satisfiability of L∥ is decidable, in 2-NExpTime** (Pratt-Hartmann
2018, partial-order case, through `poset_bridge_fin`). Lutz & Wolter call the
finite companions of the RCC5 substructure logics "one of the most intriguing
open problems" of their paper; for the L∥ slice that problem was, in effect,
settled in 2018.

**(c) Partial results for L∥ with incomparable witnesses** (Marzec & Tendera).
For sentences whose witnesses are all incomparable: every satisfiable one has a
model with bounded antichains; if in addition there are no entanglements, a
finite model; and for each `k` some satisfiable sentence forces every model to
embed lexicographically ordered `ℤᵏ`. With both kinds of witnesses but no
entanglements, satisfiability is decidable. (As reported in their abstract,
introduction and workshop version; see the scope note in §3.)

Where the slices now stand:

| slice of ALCI_RCC5 | status | by |
|---|---|---|
| `∀PO`-free | decided, kernel-checked | this repository |
| 𝒟 (no `∃PP`, `∃PO`, `∀DR`) | decided, kernel-checked | this repository (Astra 6) |
| L∥, no `∃PO` | decided, 2-NExpTime | Szwast–Tendera 2018 via Theorem 1 |
| L∥, finite models | decided, 2-NExpTime | Pratt-Hartmann 2018 via Theorem 1 |
| L∥, general | **open** — it *is* FO²_u1PO | Theorems 1–2 |
| full logic | **open**, and at least as hard as L∥ | Corollary 3 |

---

## 5. The spiral: infinity without a vertical witness

Marzec & Tendera's `Φ_spiral`, as a pattern system on five predicates
`A₀ … A₄` (indices mod 5):

```
every region carries some Aᵢ
Aᵢ ⊑ ∀PO.¬Aᵢ₊₂ ⊓ ∀DR.¬Aᵢ₊₂          (Aᵢ and Aᵢ₊₂ are never incomparable)
Aᵢ ⊑ (∃PO.Aᵢ₊₁ ⊔ ∃DR.Aᵢ₊₁) ⊓ (∃PO.Aᵢ₋₁ ⊔ ∃DR.Aᵢ₋₁)
```

**Proposition 4 (`spiralConcept_sat`, `spiralConcept_infinite`,
`spiralConcept_noExVert`).** The resulting ALCI_RCC5 concept is satisfiable,
every RCC5 model of it contains an injective ω-sequence of regions, and it
contains no `∃PP` and no `∃PPI`.

*Why.* Follow incomparable witnesses of colours `i, i+1, i+2, …`. Regions two and
three steps apart have colours that differ by `±2`, so they are comparable.
If `x₀ < x₂` then `x₁ < x₃` (were `x₃ < x₁`, comparing `x₀` with `x₃` either way
contradicts an incomparability), and likewise `x₀ < x₃`; so the direction
propagates and `xₖ < xₘ` for all `m ≥ k+2` (`walk_inj`). The model is the
integers with `a < b` iff `a + 2 ≤ b`, coloured mod 5. With four colours instead
of five there is a four-point model (`wp137` D4): the odd cycle matters, because
a pentagon of comparabilities has no transitive orientation (D5).

The project's known infinity axioms all ask for a proper superpart or a proper
part. This one asks only for overlaps (or disjoint regions) and then *forbids*
overlap and disjointness two steps on. The chain is forced by exclusion.

---

## 6. `K2`, and a wrong verdict of the cover-tree tableau

```
K2 = ∃PO.(A ⊓ ∀PO.¬B ⊓ ∀DR.¬B) ⊓ ∃PO.(B ⊓ ¬A)
```

The first witness tolerates no `B` among the regions it overlaps or is disjoint
from; the second witness is a `B` and a different region. So the two witnesses
are nested (`k2_witnesses_nested`). A model: `r = {1,3}`, `a = {1,4}`,
`b = {1,4,5}` with `A` at `a` and `B` at `b`; `r PO a`, `r PO b`, `a PP b`.
`k2_sat` proves `Satisfiable k2` in the artifact's own semantics; the probe
checks the set model and that there is no model on fewer than three points.

`src/cover_tree_tableau.py` answers **UNSAT** (`'all branches closed'`); the
quasimodel oracle answers SAT. The cause is one line of design, stated in the
file's header — "PP is NOT an open sibling cross-edge … only {DR,PO} remain open
between sibling subtrees" — and implemented in `check_cover_tree_siblings`, which
intersects the admissible relations between two `DR`/`PO` witnesses of one node
with `{DR, PO}`. `K2`'s witnesses need `PP`. The same happens with `DR`
witnesses (`K2dr`); dropping `∀DR.¬B`, so that the witnesses may be disjoint,
restores SAT (`wp137` E8). The file is as shipped: its built-in suite
(`python3 src/cover_tree_tableau.py`) passes 35/35, oracle cross-check
included, in the environment where it rejects `K2`.

Consequences for the text:

* "no verdict of the cover-tree tableau has ever been shown wrong" is false as
  of this note (README ×2, overview ×5, slides ×1, `CLAUDE.md` ×1; corrected, or
  in `CLAUDE.md` superseded by a new head paragraph, in the same change set).
  The accurate statement: its SAT answers are still unrefuted; it is
  **incomplete** on concepts whose horizontal witnesses must be nested, with
  `K2` as the witness.
* The wrong direction is UNSAT, and subsumption is tested as unsatisfiability.
  So the tableau's subsumption verdicts are evidence only where something
  independent agrees. The GIS taxonomy still matches the 2003 result edge for
  edge, and `wp87`'s agreement inside the ∀PO-free fragment is unaffected: the
  failure needs a `∀PO` between the two witnesses, and without one `PO` is
  always admissible between them.
* The tableau paper's "key insight" — `PP` is not an open sibling cross-edge —
  is true of nodes that are in sibling subtrees. It does not license treating
  two `DR`/`PO` witnesses of one node as siblings, which is what the
  implementation does. The paper now carries an erratum box.
* The 911-case agreement with the oracle did not exercise this pattern. That is
  the same lesson the April gap taught, from the other side: there the suite
  missed an unsoundness, here an incompleteness.
* `K2` is `C_sat` moved sideways. `C_sat`'s two witnesses are `PP`-witnesses;
  `K2`'s are `PO`-witnesses. The overview's sentence "a construction for the
  full logic has to reason about the relations among contemporaneous witnesses"
  should add: *including `PP`/`PPI` between witnesses that were both born
  horizontally.*

This is a defect in a prototype, not in a theorem. The certified fragment is
untouched: `K2` contains `∀PO`.

---

## 7. What this changes in the map

**Where the difficulty is.** The overview locates the obstruction in
"horizontal coordination" and names F6 for it. The bridge isolates one clean
component of that: the sublanguage `{α ⊑ ∀∥.¬β, α ⊑ ∃∥.β}` is already an open
problem with its own literature, its own partial results and its own
infinity axioms, and it involves neither `DR`'s downward closure nor any
non-singleton composition cell. Any proof of decidability for ALCI_RCC5 has to
go through it. Any proof strategy that would not, on its own, decide FO²_u1PO
can be set aside without trying it.

**A test for candidate architectures.** A finite-certificate scheme for the full
logic must (i) reject `C_bad` and accept `C_sat` — the existing gate — and now
also (ii) accept `K2` and the spiral concept, and reject `C_cyc`. The
fresh-occurrence unfolding with residual `PO` cannot produce a model of `K2` or
of the spiral: it never makes one horizontal witness a part of another.

**A different normal form to look at.** The split-forest picture makes models
maximally `PO`. Marzec & Tendera's finite-antichain theorem goes the other way:
for the horizontal part, models can be made maximally *comparable*, with
antichains bounded by `3·m·|types|`. The spiral is the smallest example — it has
width 2. Whether "bounded antichains over scattered orders" survives the
addition of `DR` is, as far as I can tell, an untried question, and it is a
different question from F6's bounded live width.

**What the bridge does not touch.** Bare `∀PO` and bare `∃DR`. In an L∥ concept
`DR` can always be emptied; outside L∥ it cannot, and then the rule
`x DR y, x' ≤ x, y' ≤ y ⟹ x' DR y'` carries information between four regions at
once. `C_bad` (bare `∀PO`: two regions with a common part cannot be `DR`) and
`C_joint` live there. The honest summary of the full problem is now: *FO²_u1PO,
plus a disjointness relation that is downward closed.*

**Three things I would do next**, in order of cost:

1. Fix or re-label the tableau (§6). Small.
2. Ask the FO² people. The authors of the papers in §1 have worked on exactly
   the L∥ core since 2013; the bridge gives them a description logic with a
   20-year-old open problem that contains theirs, and gives this project their
   techniques (narrow models via Ramsey; finite antichains; factorizations).
3. Try to extend the 2-NExpTime result of §4(a) from L∥ to *all* concepts with
   vertical witnesses only (bare `∀PO` and bare `∀DR` allowed). Without `∃PO`
   and `∃DR` a model needs a disjointness relation only to satisfy universals,
   and one exists iff no pair that must be `DR` has a pair that must be `PO`,
   a comparable pair, or a common part beneath it. That condition is not
   two-variable, so it is not a corollary — but it is one condition, and
   `C_bad` is its simplest instance.

---

## 8. Artifacts, and how to check them

```
cd formal
lean -o POFreeLift.olean POFreeLift.lean          # ~1 min, Lean 4.33.1
LEAN_PATH=. lean PosetBridge.lean                 # ~2 s
cd ../verification/python
python3 wp137_poset_bridge_probe.py               # ~30 s
```

`PosetBridge.lean` imports the artifact rather than copying its definitions, so
`Satisfiable` in its theorems is the `Satisfiable` of `decidableSat_cone`.
Capstones and their axioms:

| declaration | says | axioms |
|---|---|---|
| `poset_bridge` | `PSatisfiable c ↔ Satisfiable (emb c)` | propext, Classical.choice, Quot.sound |
| `poset_bridge_fin` | the same for finite models | same |
| `patsys_to_rcc5` | `S.Sat ↔ Satisfiable (emb S.toConcept)` | same |
| `decidablePSat_of_full`, `decidablePatSat_of_full` | decidability transfers downward | same |
| `decidablePSat_noAllInc` | the certified procedure decides the `∀∥`-free poset logic | same |
| `walk_inj` | the order-theoretic core of the spiral | propext, Quot.sound |
| `spiral_sat`, `spiral_infinite` | the spiral over strict partial orders | propext, Classical.choice, Quot.sound |
| `spiralConcept_sat`, `spiralConcept_infinite` | the same in ALCI_RCC5 | same |
| `spiralConcept_noExVert` | no `∃PP`, no `∃PPI` | none (`decide`) |
| `k2_sat` | `K2` is satisfiable | propext, Classical.choice, Quot.sound |
| `k2_witnesses_nested` | its witnesses are never `PO` or `DR` | none |
| `ccyc_unsat`, `ccycErased_sat` | `C_cyc` is unsatisfiable; satisfiable with its `∀PO` conjuncts erased | propext, Classical.choice, Quot.sound |

No `sorry`, no `axiom`, no `native_decide`.

`wp137` derives the composition table from set semantics and re-checks the bridge
by brute force: every strict partial order on ≤ 5 points is a closed network
under the `PO`-reading (4,473 orders); every closed atomic network on ≤ 4 points
has the right reduct (962 networks); truth transfers pointwise on 6,000 random
models with random concepts, both ways, with the two negative controls; the
spiral has no model on ≤ 6 points (built-in DPLL; ≤ 9 if `python-sat` is
installed) and the controls for that search fire; and part E checks `K2` and
`C_cyc` against explicit set models and exhaustive small-model search, and runs
the two reasoners on `K2`.

### What I did not do

* I did not formalize Scott normal form or the expansion over 1-types.
* I did not check the proofs of the imported theorems (§4).
* I could not run either reasoner on the spiral concept: its closure has 146
  members and both enumerate types. Neither returned a verdict on `C_cyc`
  (closure 60) within a 10-minute bound; so whether either reasoner wrongly
  accepts that unsatisfiable concept is untested.
* I did not attempt F6, and I did not find a reduction from ALCI_RCC5 back to a
  two-variable logic.

---

## References

* C. Lutz, F. Wolter. Modal logics of topological relations. *LMCS* 2(2:5), 2006.
  (Theorem 2 and §8: expressive completeness for the two-variable fragment;
  the open problems on RS and on finite companions.)
* D. Marzec, L. Tendera. On two-variable first-order logic with a partial order.
  *J. Logic Comput.* 36(2), exaf068, 2026. Workshop version: CILC 2024,
  CEUR-WS vol. 3733.
* I. Pratt-Hartmann. Finite satisfiability for two-variable, first-order logic
  with one transitive relation is decidable. *Math. Log. Quart.* 64(3):218–248,
  2018. arXiv:1707.05558.
* W. Szwast, L. Tendera. FO² with one transitive relation is decidable.
  STACS 2013. (**Main claim withdrawn** in the next item.)
* W. Szwast, L. Tendera. On the satisfiability problem for fragments of
  two-variable logic with one transitive relation. arXiv:1804.09447, 2018–19.
