# ALCI_RCC5 — reference semantics (for the adequacy review)

This sheet states, independently of the Lean artifact and its companion
papers, what ALCI_RCC5 concept satisfiability *is*. Use it as the
neutral yardstick: your job is to decide whether the Lean definitions
faithfully capture **this**, drawing also on your own knowledge of
description-logic and RCC semantics. Do **not** take the companion
papers' descriptions as ground truth — check the Lean against the logic
itself.

## RCC5

RCC5 is a region calculus with five base relations, jointly exhaustive
and pairwise disjoint (JEPD) over pairs of non-empty regions:

- **DR** — discrete (disjoint interiors; share no part)
- **PO** — partial overlap (share a part, neither part of the other)
- **PP** — proper part (x strictly inside y)
- **PPI** — inverse proper part (x strictly contains y)
- **EQ** — equal

Converse: `conv(DR)=DR`, `conv(PO)=PO`, `conv(EQ)=EQ`, `conv(PP)=PPI`,
`conv(PPI)=PP`. Composition is the standard RCC5 table (derivable from
the subset semantics on non-empty regions). RCC5 has the **patchwork
property** (Renz–Nebel): a path-consistent atomic network is globally
realizable.

An **atomic RCC5 network** on a set S assigns to each ordered pair of
distinct elements exactly one base relation, with `ρ(y,x)=conv(ρ(x,y))`
(R2) and composition-closure `ρ(x,z) ∈ comp(ρ(x,y),ρ(y,z))` for all
distinct triples (R3). Under **strong EQ semantics**, EQ holds only on
the diagonal (EQ = identity), so distinct elements never carry EQ.

## ALCI_RCC5 syntax (negation normal form)

Roles are the RCC5 relations. ALCI allows inverse roles; since each RCC5
relation's inverse is again an RCC5 relation (`PP⁻ = PPI`, etc.), inverse
roles are **absorbed** into the base set — there is no separate inverse
constructor. Concepts (in NNF):

```
C, D ::= ⊤ | ⊥ | A | ¬A | C ⊓ D | C ⊔ D | ∃R.C | ∀R.C
```

where `A` is a concept name and `R ∈ {DR, PO, EQ, PP, PPI}`. (Negation
appears only on concept names; general negation is pushed in.)

## Semantics

An interpretation `I = (Δ, ρ, ·^I)`:
- `Δ` a non-empty domain of regions,
- `ρ` a total function assigning to each ordered pair the base relation
  between them, forming an atomic RCC5 network with EQ = identity (R1
  reflexive EQ, R2 converse, R3 composition-closure),
- `A^I ⊆ Δ` for each concept name.

Concept extensions:
```
⊤^I = Δ            ⊥^I = ∅
(¬A)^I = Δ \ A^I
(C ⊓ D)^I = C^I ∩ D^I      (C ⊔ D)^I = C^I ∪ D^I
(∃R.C)^I = { x | ∃y. ρ(x,y)=R ∧ y ∈ C^I }
(∀R.C)^I = { x | ∀y.  ρ(x,y)=R → y ∈ C^I }
```

Note the role reading: `R(x,y)` holds **iff `ρ(x,y) = R`** — because the
network is atomic (exactly one base relation per pair), the role
extension of `R` is exactly the set of pairs labelled `R`.

**C0 is satisfiable** iff there is such an interpretation with
`C0^I ≠ ∅`. Concept satisfiability of ALCI_RCC5 is the open decision
problem (Wessel 2002/2003). Weak-EQ reduces to strong-EQ via TBox
internalization; the artifact commits to strong EQ.

## What the artifact claims

The Lean file builds a certificate → frame → model pipeline and claims:

1. **Soundness** (rounds 19–24): a well-formed, S-conditioned,
   faithful, Hintikka-labelled certificate yields an interpretation `I`
   satisfying (R1,R2,R3) with the root satisfying C0 — i.e. C0 is
   satisfiable.
2. **Abstraction completeness** (round 25): satisfiability and
   Hintikka-realizability coincide (`satisfiable_iff_hintikkaP`).
3. **The one open target**: `CompletenessObligation` — every satisfiable
   C0 admits a *finite* certificate — stated, not proved, not
   axiomatized. Its sub-parts are the open items F6 (width) and W2′
   (uniformization).

Your review is about whether **the statements 1–3 mean what this sheet
describes**, and whether the definitions are non-vacuous. The proofs
themselves are Lean-kernel-checked (zero `sorry`, no added axioms), so
you need not re-verify them — attack the *definitions and theorem
statements*.
