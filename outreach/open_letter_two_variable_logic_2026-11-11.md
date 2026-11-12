# An open letter on two-variable logic over a partial order and the description logic ALCI_RCC5

*To Lidia Tendera, Dariusz Marzec, Wiesław Szwast and Ian Pratt-Hartmann.*
*Posted 11 November 2026 in <https://github.com/lambdamikel/alcircc5>. Drafted
by Claude Fable 5.2 (Anthropic) at Michael Wessel's request; like everything in
that repository, it says so.*

---

Dear Lidia Tendera, Dariusz Marzec, Wiesław Szwast and Ian Pratt-Hartmann,

I am writing about a connection between an open problem of yours and an open
problem of mine. I hope it is of use to you, and I would be grateful to be told
where it is wrong, or that it is already known.

## Who is writing

Between 2001 and 2003 I introduced a family of description logics, ALCI_RCC,
whose roles are the base relations of the region connection calculus. For the
member with the five RCC5 relations — equal, proper part, has proper part,
partially overlapping, disjoint — I could prove neither decidability nor
undecidability of concept satisfiability, and the question has been open since.
Lutz and Wolter (*Modal logics of topological relations*, LMCS 2006) study the
same logic as L_RCC5(RS). They show that it is recursively enumerable and that
its language has the expressive power of the two-variable fragment over the
RCC5 relations with unary predicates, and they prove undecidability for the
related logics of *full* structures; decidability over all structures is among
their open problems.

Over the past months I have had AI assistants from Anthropic and OpenAI attack
the problem under my direction. They did not settle it. One fragment is
decided, with a proof checked in Lean 4; the rest is a map of what remains.

## What I think concerns you

In an RCC5 structure the proper-part relation is a strict partial order, and
two distinct regions that are incomparable in it are related by exactly one of
*overlap* (PO) and *disjoint* (DR). Take the formulas of the modal language in
which ⟨DR⟩ occurs only in the combination ⟨PO⟩φ ∨ ⟨DR⟩φ and [PO] only in
[PO]φ ∧ [DR]φ. Such a formula cannot tell overlap from disjointness. It speaks
only of <, >, = and incomparability, which you write ∼.

> **Theorem.** Such a formula is satisfiable in an RCC5 structure if and only
> if its reading over <, >, = and ∼ is satisfiable in a strict partial order.
> The same holds with "finite" on both sides.

From right to left, declare every incomparable pair to be overlapping and no
pair disjoint; that is an RCC5 structure. From left to right, keep the domain
and forget the difference between PO and DR. The theorem is checked in Lean.
It is also checked for finite systems of constraints of two shapes,

```
forbidden    ∀x∀y ¬( τ(x) ∧ r(x,y) ∧ τ'(y) )
required     ∀x ( τ(x) → ⋁ᵢ ∃y ( rᵢ(x,y) ∧ τᵢ(y) ) )
```

with r among =, <, >, ∼ and τ a conjunction of unary literals. As far as I can
see this is the shape of the basic normal form that Dariusz Marzec and Lidia
Tendera use for FO²ᵤ1PO (CILC 2024, Definition 2), once its unary conditions
are written as disjunctions of literal conjunctions. The step from an
arbitrary two-variable sentence to such a system is *not* formalized; I take it
from Scott normal form and from Lemma 2 of that paper.

If this is right, three things follow.

1. **Your problem is inside mine.** Satisfiability for two-variable logic with
   one strict partial order and unary predicates reduces to concept
   satisfiability in ALCI_RCC5. A decision procedure for my problem would
   decide yours in the unary case, and an undecidability proof for yours would
   settle mine. I know of no reduction in the other direction.

2. **The critical fragment has a two-line form in RCC5.** At the end of the
   2024 paper Marzec and Tendera write that it suffices to concentrate on
   unary signatures with entanglements α ◁▷ β and incomparable witnesses, and
   that they believe that fragment decidable. In RCC5 it reads

   ```
   α ⊑ [PO]¬β ∧ [DR]¬β          every α and every β are comparable
   α ⊑ ⟨PO⟩β ∨ ⟨DR⟩β            every α has an incomparable β
   ```

   imposed globally: no proper-part witnesses at all.

3. **Your theorems give me results I did not have.** They are imports: I have
   not checked your proofs and claim nothing about them.
   * From the decidability of the fragment with transitive witnesses (Szwast
     and Tendera, J. Log. Comput. 2019): the formulas above with proper-part
     witnesses only are decidable in 2-NExpTime. It is the first decided slice
     of ALCI_RCC5 in which a [PO] constraint can change the answer.
   * From finite satisfiability over a partial order (Pratt-Hartmann, Math.
     Log. Quart. 2018): finite satisfiability of the formulas above is
     decidable in 2-NExpTime. Lutz and Wolter name the finite companions of
     their logics among their open problems; as I read them, for this slice
     the answer was there in 2018.
   * From the spiral of Marzec and Tendera: an RCC5 concept all of whose
     models are infinite and
     which asks for no proper part and no proper superpart. My 2003 report
     has one concept of that kind, built by excluding relations; the spiral is
     a second, and unlike mine it never separates overlap from disjointness.
     The Lean file proves that every model contains an infinite sequence of
     distinct regions.

## What the full logic adds, in your terms

By Lutz and Wolter's expressive-completeness result, as I read it, the full
logic is the two-variable logic, with unary predicates, of the class of RCC5
structures. And
that class has a simple description, checked in Lean in both directions: an
RCC5 structure is a set with a strict partial order < and a relation D
("disjoint") that is symmetric, irreflexive, never holds between comparable
elements, and is *downward closed*:

```
x D y,  x' ≤ x,  y' ≤ y   ⟹   x' D y'
```

Overlap is whatever remains. Up to reversing the order, this is the
order-and-conflict skeleton of a prime event structure, without the axiom of
finite causes.

So the problem I could not solve is: **two-variable logic with unary predicates
over strict partial orders with one additional downward-closed relation.** Your
problem is the case in which a formula may not mention D apart from
"incomparable". The formulas that do — a bare ⟨DR⟩ or a bare [PO] — are where
my examples of difficulty live. The simplest says that two regions with a
common part cannot be disjoint.

## Questions

1. Is the bridge correct, and is it known? We found no statement of it, but I
   do not know your literature the way you do.
2. Is general satisfiability for two-variable logic with one partial order
   still open, also for unary signatures?
3. Do your techniques — narrow models and the finite antichain property,
   blocks of equal one-types, the factorization of typed partial orders —
   tolerate one further binary relation with a downward-closure axiom? Is
   anything known for two-variable logic over event-structure-like classes?
4. Marzec and Tendera observe that the known undecidability proofs encode
   grids with unbounded antichains. On the RCC5 side every attempt to force a rigid grid
   has failed for a similar reason: no finite set of constraints seems to pin
   more than a bounded amount of side-by-side structure. Does that match your
   experience in the unary case?
5. Two small test cases, in case they are useful, written over a partial
   order. With `W(P,Q) = P ∧ ¬Q ∧ [∼]¬Q ∧ [>]¬Q` ("I am a P, and every Q is
   strictly above me"), the formula `⟨<⟩W(A,B) ∧ ⟨<⟩W(B,C) ∧ ⟨<⟩W(C,A)` is
   unsatisfiable, because its three witnesses would be ordered in a cycle,
   although every two of them are compatible. And
   `⟨∼⟩(A ∧ [∼]¬B) ∧ ⟨∼⟩(B ∧ ¬A)` is satisfiable, but only with its two
   incomparable witnesses comparable to each other. A model construction that
   treats the incomparable witnesses of one element as unrelated to each other
   gets the second wrong; one of my own reasoners did.

## A correction I owe you

Until this month the papers in the repository cited the 2013 STACS result as a
decidability theorem. The sentence came from a review of our work, and we took
it over without checking the later literature. It is corrected, and the
correction is recorded in `ERRATA.md` (E1). The 2019 paper says exactly what
the 2013 argument does and does not give, and I should have read it first.

## What this rests on

* The work was produced by AI assistants under my direction. I posed the
  problem and steered; I did not write the proofs.
* The bridge, the spiral's infinity and the two test cases are checked in
  Lean 4: `formal/PosetBridge.lean`, 1,354 lines, no `sorry`, built against the
  repository's certified development. The names are `poset_bridge`,
  `poset_bridge_fin`, `patsys_to_rcc5`, `spiralConcept_infinite`, `k2_sat`,
  `ccyc_unsat`.
* The bridge was found in a single session on 11 November 2026 and has **not
  been reviewed by anyone**. In this project's record, 19 of 22 reviews found
  a defect or an overclaim. Please presume there is one here.
* The normal-form step on the first-order side is not formalized. The bridge
  covers unary signatures only; I do not see how to embed further binary
  predicates.
* Nothing has been posted to arXiv.

Where to look: the note `papers/poset_bridge/README.md`; the overview paper
`papers/overview_arxiv.pdf`, §7.8 and §5; the probe
`verification/python/wp137_poset_bridge_probe.py`, which re-checks the bridge
by brute force on small structures; all at the tag `release-2026-11-11`.

I would be grateful for any reaction, including "this is folklore" and "this
is wrong, and here is why".

With respect,

Michael Wessel
miacwess@gmail.com
