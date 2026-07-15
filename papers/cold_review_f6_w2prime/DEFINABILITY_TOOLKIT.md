# Definability toolkit — the model-theoretic room for F6

The width barrier is a **definability** question: *can an 𝒜𝓛𝒞ℐ_RCC5
concept force an unbounded rigid horizontal ({DR,PO}) configuration?*
"Can a formula force structure X" is not a model-*construction* question
(the toolbox that built the certificate layer); it is a question about
the **expressive power** of the logic, whose natural tools are the ones
below. This note says, for each, **how it bears on the specific F6/W2′
questions** and **what a result using it would look like** — not just
that it exists.

A recurring theme: 𝒜𝓛𝒞ℐ_RCC5 is a **modal/guarded** logic (concepts are
bisimulation-invariant modal formulas over the RCC5 relations), so the
sharpest tools are the ones tuned to modal/guarded expressivity, not
full FO.

---

## 1. Locality (Gaifman, Hanf) — the primary lever

**The idea.** FO (and *a fortiori* modal) formulas are **local**: their
truth at a point depends only on a bounded-radius neighbourhood
(Gaifman); over structures of bounded degree, elementary equivalence
reduces to counting local neighbourhood-types up to a threshold (Hanf).

**Why it is the primary lever for F6.** A *rigid* horizontal crowd of
size `n` is a configuration in which `n` occurrences are pairwise
non-mergeable and must coexist at *one interface* — i.e. within a
*bounded radius* of a single point. But the only way the composition
table forbids a merge is a *horizontal anchor* (Prop. 6.3:
`u DR w, w PO v ⟹ u≠v`), and an anchor is itself a bounded-radius
witness. So "force `n` pairwise-rigid occurrences near one point" is a
demand for `n` distinct bounded-radius types **all present in one
neighbourhood** — exactly what Gaifman locality constrains.

**The proof shape you would aim for (proves F6).** *A modal concept of
modal depth `d` can distinguish only boundedly many (as a function of `d`
and |C|) local horizontal types; two crowd members with the same local
type up to the relevant radius are mergeable (nothing in a `d`-local view
separates them); hence any model can be folded to one where the live
horizontal width at each interface is bounded by that type count.* If you
can make "same local type ⟹ mergeable" precise for RCC5 (this is where
strong-EQ and the composition table enter — you must show the merge
preserves composition-closure), locality delivers the width bound
**directly**. This is the single most promising route to a *positive*
F6, and it is the one the report's §9 points at.

**The obstruction to watch.** Locality bounds *how many types* a formula
sees, not *how many elements* a model has. You must convert "boundedly
many types near a point" into "boundedly many *live* edges at an
interface" — i.e. argue that two same-local-type occurrences can be
identified *without breaking any far-away obligation*. Strong-EQ helps
(merging is identity, and identity is composition-transparent), but the
merge must respect every occurrence's *vertical* obligations too. This is
precisely the "mergeable in every model" clause of Obs. 7.5.

---

## 2. Ehrenfeucht–Fraïssé / bisimulation games — the counterexample tool

**The idea.** Two structures are `k`-round-EF-equivalent iff no
FO-formula of quantifier rank `k` separates them; for modal/description
logics the right game is the **bounded bisimulation game** (Spoiler
picks a role-successor, Duplicator matches, for `d` rounds ⟺
indistinguishable by modal depth `d`).

**Why it is the counterexample tool.** To show a concept **cannot** force
a size-`(n+1)` rigid crowd, exhibit two models — one with `n` live
horizontal neighbours, one with `n+1` — that are `d`-bisimilar (`d` =
modal depth of the concept). Then no concept of that depth tells them
apart, so none *forces* the larger crowd. A **Duplicator strategy that
works for all `n`** proves the *uniform* bound = **F6**. Conversely, a
concept + a **Spoiler** strategy that wins against every small-width model
would be the seed of a **forcing construction** (Target C).

**Concretely for RCC5.** The game moves are role-successor picks along
{DR, PO, PP, PPI}. The interesting asymmetry: PP/PPI moves change the
*vertical* level (and can be **blocked** — a PP-tower folds when a type
repeats), while DR/PO moves stay horizontal and (Prop. 7.3) *always fold*
(comp(PO,PO) ∋ EQ). So a Duplicator playing on the horizontal axis has a
*fold* available that a Duplicator on the vertical axis may not — this
asymmetry is exactly why horizontal crowds should be *harder* to force,
and an EF argument is how you would turn "should be" into "are not."

**For W2′ (Target A).** The game view of W2′: two cross-pairs `(y,b)` and
`(y′,b′)` with the *same interface states* but *different forced values*
in some joint assignment are a **local distinguishability** between
same-type occurrences. W2′ says this cannot happen after bounded
refinement — i.e. the state (the EF-type up to the relevant radius)
*determines* the safe value. If you can show the value of a cross-pair is
a **function of the `r`-local bisimulation type** for a computable `r`,
W2′ follows. The 3 measured failures are the test: are they same-`r`-type
with different values for *every* `r`, or does some bounded `r` separate
them?

---

## 3. The composition method (Feferman–Vaught, Shelah) — for the fold

**The idea.** The theory of a structure assembled from parts (disjoint
unions, sums, ordered sums, generalized products) is computable from the
theories of the parts. For chains/trees it gives **automata-like**
reductions of FO/MSO truth to the composition of finitely many local
theories.

**Why it bears here.** The certificate *is* a tree of interface bags
glued along separators — a **generalized sum over a tree**. The
composition method is the principled version of the path-automaton lemma
(`wp38`): instead of tracking single relation-sets along a path, track
the **full local theory** of each bag and compose along the tree. If the
composed theory stabilizes (finitely many bag-theories, closed under the
gluing operation), you get a **finite** description of the whole
unfolding — which is *bounded width in disguise*. The path-automaton
lemma is the rank-1, single-relation shadow of this; **lifting it to full
local theories over the tree is a concrete way to attack F6 positively**,
and it connects directly to Target D (formalizing the reduction as a
statement about a finite composition algebra).

**What to produce.** A **finite monoid / finite automaton** on interface
bag-types whose transitions are the gluing operations, such that the set
of realizable unfoldings is its (regular) behaviour. If the monoid is
finite, width is bounded. The open point is whether the *horizontal*
part of the bag-type is finite — which loops back to W2′ (state-uniform
steering = a finite horizontal component of the bag-type).

---

## 4. Bounded / finite model property machinery

**The idea.** Modal and many description logics have the (bounded) tree /
finite model property: satisfiable ⟹ satisfiable in a model of bounded
branching / bounded size, via **selection** (filtration, unravelling,
mosaic/type elimination).

**Why it bears here.** F6 *is* a bounded-branching statement restricted to
the horizontal axis. 𝒜𝓛𝒞ℐ without the RCC5 composition constraints has
the bounded-tree-model property (it is a notational variant of a
two-way modal logic); the composition table is what could *break* it by
forcing wide interfaces. So the question is sharp: **does adding the RCC5
composition closure to 𝒜𝓛𝒞ℐ preserve bounded horizontal branching?**
A **filtration** argument (quotient the model by concept-type, check the
quotient still satisfies composition closure) is the classic tool; the
danger is that filtration may **merge occurrences that a horizontal
anchor keeps apart**, breaking composition-closure — which is, once more,
the Obs. 7.5 clause. If you can design a **composition-respecting
filtration** that bounds horizontal branching, that is F6.

**Mosaic / type-elimination** is the dual: enumerate finite local pieces
("mosaics") consistent with the composition table, eliminate those with
unfulfillable obligations, and check a global tiling exists. The
project's own history converged on this (it is what the certificate
catalogue is). The open point is the same width bound: how many *live*
horizontal mosaic-neighbours a piece can have.

---

## 5. The grid-encodability analysis (where Wessel / Lutz–Wolter sit)

**The idea.** Undecidability of a modal/spatial logic is typically shown
by **forcing an ℕ×ℕ grid** (two commuting functional relations with a
coincidence/confluence condition) and reducing tiling or a Turing
machine. Lutz–Wolter 2006 do this for *topological* RCC8; Wessel 2003
observes it **fails** for the *abstract composition-table* semantics
because the coincidence condition — "the north-then-east cell = the
east-then-north cell" — requires forcing a relation to a **single**
value, and the abstract table never forces a horizontal value.

**Why it is the same room.** "Force a grid" = "force a rigid horizontal
coordinate system" = exactly the F6-counterexample of Obs. 7.5. So the
undecidability literature is not adjacent — it is the **same construction
seen from the other side** (Obs. 8.1). Practically:

- To attack **Target C** (force a grid), you are trying to *repair* the
  coincidence condition using some device Wessel's analysis missed —
  e.g. using the *vertical* determination (comp(PP,PP)={PP}) to
  discipline a horizontal grid. Study exactly where the Lutz–Wolter
  reduction uses topology and whether a composition-table gadget can
  substitute. If it can, undecidability; the report bets it cannot.
- To attack **Target B/F6-positive**, formalize *why* the coincidence
  condition is unforcible as a **preservation theorem**: a class of
  concept-definable relations closed under an operation ("horizontal
  merge") that any grid encoding would have to violate.

---

## 6. Why Ramsey theory did NOT fit (so you don't repeat it)

Ramsey-type results say: *every sufficiently large structure contains an
unavoidable substructure `X`*. F6 says: *no formula forces every model to
contain arbitrarily large `X`*. These are **opposite quantifier orders**
("∀ large object ∃ pattern" vs. "¬∃ formula ∀ model pattern"). Ramsey
gives you patterns you cannot avoid; F6 needs patterns you cannot
*compel*. The composition-table substrate is even *Ramsey-friendly*
(arbitrarily large irreducible {DR,PO} crowds exist — `wp37`), which is
precisely why Ramsey is the wrong tool: the crowds exist freely; the
question is whether a *formula* can *pin* them, and pinning is a
definability property, not an unavoidability one. The tools above are the
definability ones.

---

## 7. Suggested order of attack

1. **W2′ via §2 (EF/bisimulation)** — smallest, most self-contained; the
   3 measured witnesses give an immediate concrete test of "does a bounded
   local type determine the safe value."
2. **F6-positive via §1 (locality)** — the main event; "same local type
   ⟹ mergeable, and merge respects composition" is the crux.
3. **The finite composition algebra via §3** — the constructive form of
   the same bound; also discharges Target D.
4. **Target C via §5** only if §1 reveals a *gap* in the locality argument
   — that gap is where a grid could hide.

Everything reduces to one crux, stated three ways: *can two occurrences
with the same bounded local type always be identified without breaking
composition-closure?* Locality says how many types there are; the
composition table (Props. 6.1/6.3) says which merges are legal; the open
content is whether "same type" always licenses a legal merge. That is the
whole of F6.
