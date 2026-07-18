# Approach: The Lean formalization and the reduction to F6

**Idea.** Move the load-bearing soundness argument into the Lean 4 kernel,
which refuses to accept a gap — removing the "prose proof assumed the hard
step" failure mode that every cold review had exploited.

**Method, and where it came from.** The decision method is **not** an
automaton. The earlier route
([`../Automata_Parity/`](../Automata_Parity/Overview.md)) tried a two-way
parity **tree automaton**; a cold review found *acceptance without validity*
(the automaton's independent alternating run copies cannot be forced to guess
the missing horizontal relations consistently), so the project **pivoted off
the automaton** and back onto the semantic objects the split forest supplies.
What resulted is a **cluster-quasimodel** construction in the
**mosaic / type-elimination** tradition of modal and description logic: a
finite catalogue of interface **clusters** (mosaics), a consistency relation
for gluing them (controlled by the RCC5 **patchwork property**), and a
**Hintikka truth lemma** for correctness — the tableau-family argument, but
run on a *finite abstraction* instead of an unbounded tableau. The automaton
became *unnecessary* (not merely replaced) because of **one-step demand
fulfilment**: every `∃R.D` is fulfilled by a witness already present in the
catalogue, so there are no eventualities and hence no parity/acceptance
condition to decide — the one job only an automaton did well. Decidability
then reduces to enumerating finite catalogues and checking each by a finite
composition test. This is the construction formalized in Lean (rounds 19–30);
it rests on the **split-forest normal form**, the shared semantic foundation
([`../SplitForest/`](../SplitForest/Overview.md)) that the automata route also
consumed. (Unlike the retracted early quasimodel in
[`../FiniteModel_TwoTier/`](../FiniteModel_TwoTier/Overview.md), it enumerates
and checks rather than running an elimination fixpoint, so it does not inherit
that route's anti-monotone incompleteness.)

**Foundation.** The development is **Lean 4 core** — no `mathlib`, no
`lakefile`, no external libraries — so the trusted base stays small and the
axiom footprint is auditable (`propext` + `Quot.sound`, plus `native_decide`
in isolated witness lemmas only). Everything is built from first principles,
and the encoding is kept deliberately direct so the Lean statements read as
the mathematics they formalize:

- the five RCC5 atoms are an **inductive type**, with the composition table
  and converse as **total functions** (copied verbatim across all three
  files, so there is no table-input risk);
- **concepts** are an inductive type in negation normal form (inverse roles
  absorbed via the RCC5 converse);
- an **interpretation** is a domain predicate + a *total* relation function
  `rho : α → α → Atom` + an atomic valuation; **satisfaction** is defined by
  structural recursion (a role `R` is read directly as `rho x y = R`), and
  the **RCC5 frame conditions** (reflexive-EQ, strong-EQ, converse,
  composition closure) are a `structure` over `rho`;
- on top sit **Hintikka labellings** and the **certificate** objects: a
  *catalogue* (core network + attachment templates + a template-indexed
  steering function) plus a *plan* whose unfolding is the split-forest
  presentation. Live width is the count of live (non-shadow) occurrences at
  an interface — the quantity F6 must bound.

Toolchain: `elan`-installed Lean 4.31.0 at `~/.elan/bin`; build each file
directly with `lean <file>` (no build system). See [`../../LEAN.md`](../../LEAN.md)
for the per-file table and axiom list.

**What is certified** (zero `sorry`): the **soundness** pipeline (a valid
finite certificate unfolds to a genuine RCC5 model of the concept); the
**faithfulness** of the Hintikka abstraction (satisfiability ⇔
Hintikka-realizability); and a **non-oracular, decision-grade reduction**
whose one remaining premise is a computable, complete enumeration of bounded
finite certificates.

**What remains open.** That premise is exactly **F6** (bounded live width) —
the completeness direction, the open mathematics — now sharpened to the
*identity-selector-minor dichotomy*, with the uniformization property W2′
folded into it.

Full treatment: overview paper, §"The Lean line and F6"; the
artifact-by-artifact history (rounds 19–30 + the two cold reviews of the
Lean) is in [`../../LEAN.md`](../../LEAN.md).

**Artifacts**
- [`formal/Round19Transport.lean`](../../formal/Round19Transport.lean) — the normative development
- [width-barrier status report and F6/W2′ analysis](../../papers/fable5_width_barrier/)

**Probes:** WP34 (Lean mirror), WP39–WP44 (F6/W2′ cold attacks) in
[`verification/python/`](../../verification/python/).

**Result.** A *certified surround* for a still-open problem: it kernel-checks
the soundness half and the shape of the decision procedure, but does **not**
prove decidability — the antecedent F6 is untouched.
