# Attack request — F6 (bounded live width) and W2′ (uniformization)

You are a fresh, expert collaborator: strong in description logics,
qualitative spatial reasoning (RCC5/RCC8), finite model theory, and the
model-theoretic machinery of definability (locality, games, the
composition method). You have **no stake** in this development and have
not seen it before.

**This is not a referee request.** The previous fourteen documents in
this line were adversarial reviews — "find the defect." This one is
different: two genuinely open sub-problems have been isolated from a
decidability argument, and I want you to **attack the mathematics**. A
"gap" verdict is not the goal; *progress on either sub-problem* is. The
best outcome is a proof or a counterexample; a sharpened reduction, a
provably-decidable sub-fragment, or a formal equivalence are all real
wins. Honest "I could not move it, and here is precisely why" is also
useful.

Read **Section 0** first — it is a primer on the assumptions you must
not misread. The fourteenth reviewer lost a finding to one of these.

---

## 0. Primer — assumptions you must NOT misread

The object logic is **𝒜𝓛𝒞ℐ_RCC5**: the description logic 𝒜𝓛𝒞ℐ with
five role names interpreted as the **RCC5 base relations**
{EQ, PP, PPI, PO, DR}, under **abstract composition-table semantics**
(a model is a set with a total, converse-closed, composition-closed
labelling of ordered pairs by RCC5 relations — *not* a set of actual
regions). Decidability of concept satisfiability is open since Wessel
2002/2003.

1. **A certificate is a FINITE syntactic generator; its model may be
   INFINITE.** The decision procedure looks for a finite certificate
   (a catalogue of interface patterns + a plan); its *unfolding* is the
   model and can be infinite. A concept that forces an infinite model
   (e.g. an unbounded PP-tower `∃PP.⊤ ⊓ ∀PP.∃PP.⊤`) is perfectly
   satisfiable and perfectly within the framework. **Do NOT offer an
   infinite-model-forcing concept as a counterexample to anything.** The
   open question is about *width*, never about *depth/infinity*.

2. **Strong-EQ semantics.** `EQ` is identity; it holds only on the
   diagonal. Between *distinct* elements only {DR, PO, PP, PPI} occur.
   Two same-typed elements may be **merged** (set EQ, identified) unless
   some constraint excludes EQ between them.

3. **Inverse roles are absorbed.** `PP⁻ = PPI` and back; there is no
   separate inverse constructor. Concepts are in NNF.

4. **The two axes.** `PP/PPI` are **vertical** (nesting: proper part /
   proper superpart). `DR/PO` are **horizontal** (side-by-side: discrete
   / partial overlap). This distinction is the whole subject.

5. **Shadows vs. live width.** A **shadow** edge is one whose value is
   *forced* by composition from other edges (e.g. `x PP y, y DR z ⟹
   x DR z`, since comp(PP,DR)={DR}). **Live width** at an interface =
   the number of edges there that are *not* shadows — the genuine
   branching the certificate must record. **F6 is about live width, not
   total degree.** An element can have unbounded total degree with
   bounded live width if all the extra edges are shadows.

---

## 1. What is settled (do not re-litigate)

The full status report is `width_barrier.pdf` (10pp — read it; it is the
main document). In one paragraph:

- **Conditional decidability is machine-checked (Lean 4, zero sorries).**
  IF live width is bounded by a computable function of the concept (this
  is **F6**), THEN satisfiability is decidable. The soundness half of
  this reduction (certificate ⟹ model) and the faithfulness of the
  finite Hintikka abstraction are kernel-certified. (Some finitary
  *interface* obligations on the completeness side remain
  under-formalized — a fifteenth review just corrected an overclaim
  there — but those are finishable formalization, **orthogonal** to the
  two mathematical sub-problems below. Ignore them; they are not your
  target.)

- **The composition table, exhaustively (finite computation):**
  Exactly **four** compositions of proper relations are *determining*
  (singletons): comp(DR,PPI)={DR}, comp(PP,DR)={DR}, comp(PP,PP)={PP},
  comp(PPI,PPI)={PPI}. **All four have a vertical (PP/PPI) leg. PO is
  never a forced value.** (Prop. 6.1 in the report; probe `wp36`.)
  So *determination is vertical*. But *distinctness* is horizontal:
  a shared horizontal anchor (`u DR w, w PO v`) gives
  comp(DR,PO)={DR,PO,PP} ∌ EQ — it forces `u≠v` yet pins nothing (the
  edge stays live). Determination and distinctness **come apart**, and
  F6 lives in the gap.

- **The reduction (Obs. 7.5, report §7).** The combinatorial substrate
  is free (every {DR,PO} graph is path-consistent and realizable, and
  irreducible {DR,PO} crowds exist at every size — `wp37`); merely
  *demanding* more horizontal occurrences blocks, because horizontal
  chains fold into finite loops (comp(PO,PO) is the whole algebra,
  contains EQ — `wp37`); and (path-automaton lemma, `wp38`) no non-EQ
  recurrence is ever horizontal. So **the entire width barrier
  concentrates into one question: can an 𝒜𝓛𝒞ℐ_RCC5 concept *force* an
  unbounded *rigid* {DR,PO} graph** — unboundedly many occurrences that
  must coexist at one interface and that *no* model may merge?

- **The knife's edge (Obs. 8.1).** That forcing question is *the same
  fact* as the undecidability obstruction. To prove the logic undecidable
  you would force a rigid coordinate grid; Wessel 2003 identified that
  the abstract composition table **cannot force the coincidence
  condition** (that "east-of-north" = "north-of-east") — which is exactly
  "no horizontal determination, PO never forced." So: **F6-proof** =
  no concept forces a rigid horizontal grid = the logic is decidable;
  **F6-counterexample** = some concept forces one = the logic is
  undecidable. One fact, two faces. Neither has moved in two decades.

**Consequence for you:** F6 *in full* is equivalent to resolving the
24-year-old open problem in one direction or the other. I am **not**
asking you to do that in one sitting. I am asking you to move one of the
tractable pieces below, or to sharpen the map.

---

## 2. Your targets, ranked by odds

### Target A (RECOMMENDED — best odds) — W2′, the uniformization lemma

This is a **much smaller** question than F6, on the *soundness-adjacent*
extraction side, and it is where a real closure is most plausible.

**Setup.** In the certificate, when a new "child" interface is glued to
an existing "parent," each *cross-pair* `(y, b)` — `y` an old occurrence
outside the shared separator, `b` a fresh child occurrence — must be
assigned an RCC5 value inside a **safe domain** `dom(y,b) ⊆ {DR,PO,PP,PPI}`
(the values consistent with everything already fixed). A choice of values
for all cross-pairs that path-completes (extends to a composition-closed
network) is a **joint assignment**; such steps are **jointly realizable**.

**The catalogue is finite only if the assignment factors through
STATES.** The certificate records one *steering function* per interface
*profile* (type + safe-set data), **not** one value per occurrence. So
extraction must produce a **state-uniform** steering function: a single
`f` that assigns each cross-pair a value depending only on the
*interface states* of `y` and `b`, and whose induced completion is
closed — the same states must get the same value everywhere.

**W2′ (Uniformization).** *Every jointly-realizable glue step admits a
state-uniform steering function.*

**Status.** Measured on random glue steps with selector-free safe
domains (`wp28`, in the Lean project): **208/211 = 98.6%** of
jointly-realizable steps are state-uniform. The **3** failures are
jointly-realizable-but-not-state-uniform — the honest size of W2′.
Soundness does **not** depend on W2′ (any joint assignment builds a
model); W2′ is what makes the *finite* extraction *faithful*. Its failure
mode is **over-rejection only** (the procedure might reject a satisfiable
concept), never unsoundness.

**What would close it (any one):**

1. **Prove W2′** — that joint realizability always implies a state-uniform
   solution, possibly after a *bounded refinement of the state
   granularity* (adding boundedly many bits to the interface profile).
   The natural shape: show that the 3 measured failures are artifacts of
   too-coarse states and that a canonical, boundedly-finer profile
   (e.g. "safe-set + the multiset of separator-relations" instead of
   "safe-set" alone) uniformizes them; then prove the refined profile
   *always* uniformizes. A **bounded-coalescing congruence** on
   occurrences (identify occurrences whose entire future is
   interchangeable, prove the quotient is finite and uniform) is the
   other sketched route.

2. **Prove W2′ is false but repairable** — exhibit a jointly-realizable
   step that no *bounded* granularity refinement can uniformize, then
   show the over-rejection it causes is itself decidable to detect and
   patch (so decidability survives with a side-procedure).

3. **Prove W2′ is false and fatal** — exhibit a satisfiable concept whose
   *only* certificates require non-uniform steering at unboundedly many
   interfaces, so no finite catalogue is faithful. (This would be a
   genuine defect in the completeness half — valuable, and honest.)

The three measured witnesses are the place to start: reconstruct a
minimal jointly-realizable-but-not-state-uniform glue step by hand from
the composition table, and decide whether a bounded finer state kills it.

### Target B (realistic partial win) — an unconditional decidable fragment

Independent of F6 in full: **name a syntactic restriction of
𝒜𝓛𝒞ℐ_RCC5 under which live width is provably bounded**, giving an
*unconditional* decidability result for that fragment. Candidates the
report's analysis suggests:

- **No horizontal universal under a horizontal existential** (forbid
  `∃{DR,PO}. … ∀{DR,PO}. …` nesting): plausibly kills the only mechanism
  that could pin a horizontal coordinate.
- **Bounded horizontal-quantifier alternation depth.**
- **Horizontal-acyclic** concepts (the DR/PO role graph of the concept
  is a DAG).

For any such fragment: prove live width is bounded by a computable
function of the concept (this *inhabits* F6 for the fragment), hence
decidability follows from the certified conditional theorem. Even one
clean fragment is a publishable, unconditional result.

### Target C (high-risk / high-reward) — the forcing construction itself

Attempt to **force an unbounded rigid {DR,PO} graph** with a concept —
i.e. attack F6 as a counterexample (= an undecidability proof). The
report claims (Prop. 6.1) this is impossible because horizontal relations
are never determined and PO is never forced, so no lever pins a
horizontal coordinate. Two honest outcomes:

- A construction that **defeats** Prop. 6.1's intuition (some *combination*
  of vertical determination and horizontal distinctness that rigidifies a
  horizontal crowd across unboundedly many levels) — if it survives the
  composition table and the fold-blocking, it is an **undecidability
  proof**. Extraordinary, and correspondingly unlikely; but the exact
  claim to break is narrow and stated.
- A **proof** that Prop. 6.1 genuinely blocks *all* such constructions
  (not just the obvious ones) — this **proves F6** and hence
  decidability. The path-automaton lemma (`wp38`, no non-EQ horizontal
  recurrence) is a fragment of this; extend it from *paths* to *width*.

### Target D (fallback — valuable regardless) — formalize the reduction

Observation 7.5 uses "forces" in an intuitive model-theoretic sense; the
report explicitly flags that making it a **formal equivalence** is itself
open. **Define "𝒜𝓛𝒞ℐ_RCC5 forces a rigid horizontal crowd" precisely**
(a bounded-model / definability statement) and **prove** F6-fails ⟺
forcing. This converts the central "observation" into a theorem, is a
clean finite-model-theory contribution, and is a prerequisite for
attacking C rigorously. This is the lowest-risk deliverable.

---

## 3. The toolbox (the "correct room")

`DEFINABILITY_TOOLKIT.md` is a pointer to the model-theoretic machinery
the report argues is the right one — **locality** (Gaifman/Hanf),
**Ehrenfeucht–Fraïssé games**, the **composition method**, the
**bounded/finite-model-property** apparatus, and the grid-encodability
analysis in which Wessel 2003 / Lutz–Wolter 2006 already sit. The report's
§9 argues (and I agree) that F6 is a *definability* question — "can a
formula force structure X" — which is the natural habitat of these tools,
and a *different* toolbox from the model-*construction* techniques that
built the certificate layer. Ramsey-type combinatorics were tried and
**do not fit** (wrong quantifier order: "every large graph contains X"
vs. "some formula forces every model to contain X"); the toolkit note
explains why, and what does fit. If you reach for a tool, reach here.

---

## 4. Materials

- `width_barrier.pdf` — **the main document** (10pp): the composition
  table, the four propositions (determination vertical / distinctness
  horizontal / substrate free / chains block), the path-automaton lemma,
  the reduction (Obs. 7.5) and the knife's edge (Obs. 8.1), plus the
  discussion of why the combinatorics did not fit.
- `WHY_ITS_HARD.md` / `why_its_hard.pdf` — plain-language companion; the
  fastest way to load the intuition before the formal report.
- `DEFINABILITY_TOOLKIT.md` — the model-theoretic pointer (Section 3).
- `probes/` — the four self-contained Python probes and their outputs:
  - `wp35` — the width attack: a concept with unbounded *total* DR-degree
    but bounded *live* width (all extra edges are shadows). Shows the
    naïve attack fails.
  - `wp36` — determination vs. distinctness (the four vertical singletons;
    PO never forced; horizontal distinctness stays live).
  - `wp37` — the reduction: substrate free + chains block ⟹ F6 reduces to
    horizontal forcing.
  - `wp38` — the path-automaton lemma (no non-EQ horizontal recurrence)
    and an unrelated completeness-side over-restriction (ignore the F4
    part).

  Each probe is runnable (`python3 wpNN_*.py`, no dependencies) and
  self-checks against the composition table derived from set semantics.
  You are encouraged to modify them to test a construction.

---

## 5. Deliverable

A short technical note, organized by which target(s) you engaged. For
each, one of:

- **a proof** (with the argument in enough detail to be checked, ideally
  Lean-transcribable for Target A/D);
- **a counterexample** (an explicit concept or glue step + why it defeats
  the claim, cross-checkable against the composition table);
- **a reduction / partial result** (e.g. "W2′ holds after this bounded
  refinement, modulo this remaining lemma"; "this fragment has bounded
  width"); or
- **a precise negative** ("this route fails because …", identifying the
  obstruction).

Rank by how far you got. If you engage only one target, make it **A**
(W2′) — it is the one where a definitive answer is realistically in
reach, and a positive answer would remove the last soundness-adjacent
question, leaving *only* the deep F6/undecidability dichotomy.

Do not pad a null result into a false positive. The project's discipline
is that overclaiming is the cardinal sin (a review just caught one);
"strongly supported, not certified" is the standing honest label and
nothing here should inflate it. If you move W2′, that is a real and
citable step; if you cannot, saying so cleanly is worth more than a
hedge.
