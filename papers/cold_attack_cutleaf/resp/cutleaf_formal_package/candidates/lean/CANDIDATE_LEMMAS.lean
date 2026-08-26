/-
CANDIDATE_LEMMAS.lean
======================

STATUS: interface and proof-plan sketch only.  This file is intentionally one
block comment and therefore makes no compilation claim.  It must be adapted to
the names and witness lemmas in the complete POFreeLift development.

The two local proof targets are intended to precede any global support-graph
termination theorem.

1. Carrier-specific dichotomy
-----------------------------

For hD : Concept.ex pp D ∈ mty C0 I x, define the D-carriers above x:

  CarrierPlus x D y :=
    I.dom y ∧ I.rho x y = pp ∧ D ∈ mty C0 I y

Suggested target:

  theorem pp_carrier_extremal_or_covering_kernel
      (hI : RCC5Interp I) (C0 : Concept) (L0 : Nat)
      (x : α) (hx : I.dom x) (D : Concept)
      (hD : Concept.ex pp D ∈ mty C0 I x) :
    (∃ y,
        I.dom y ∧
        I.rho x y = pp ∧
        D ∈ mty C0 I y ∧
        ∀ z, I.dom z → I.rho y z = pp → D ∉ mty C0 I z)
    ∨ Nonempty (KernelData I C0 [D] L0 true x)

Proof plan:

  * obtain a real D-carrier from hD;
  * split on existence of a PP-maximal D-carrier;
  * in the negative branch, use Classical.choice/dependent choice to build

        c 0 = x,
        rho (c n) (c (n+1)) = pp,
        D ∈ mty C0 I (c n) for every n > 0;

  * call kernel_of_chain with lower bound L0 + 1;
  * copy its recurrence data into KernelData with Ds = [D];
  * discharge ccovers by choosing phase offset b = 0, using i > 0 and p > 0.

2. Same-defect elimination at an extremal carrier
-------------------------------------------------

  theorem pp_extremal_drops_same_demand
      (hI : RCC5Interp I) (C0 : Concept)
      {x y : α} {D : Concept}
      (hxy : I.rho x y = pp)
      (hDy : D ∈ mty C0 I y)
      (hmax : ∀ z, I.dom z → I.rho y z = pp → D ∉ mty C0 I z) :
    Concept.ex pp D ∉ mty C0 I y

Proof plan: if the existential were in mty at y, its semantic witness would
contradict hmax.

3. Spectrum descent
-------------------

Let ArgPP C0 be the finite list/set of D such that ex pp D occurs in cl C0, and
let UpSpec x contain those D for which ex pp D is in mty at x.

Targets:

  * x PP y -> UpSpec y ⊆ UpSpec x, by PP transitivity;
  * if y is a D-maximal carrier selected for x, then UpSpec y ⊂ UpSpec x;
  * consecutive extremal PP selections have length at most |ArgPP C0|.

4. Support labels
-----------------

The certificate construction should use labels Gamma that satisfy

  Gamma occurrence ⊆ mty C0 I representedPoint

rather than equality.  Saturate only:

  * both conjuncts of a labelled conjunction;
  * one model-true disjunct of a labelled disjunction;
  * consequences of labelled universals along every qnet edge class;
  * the argument of each labelled existential at its recorded service.

The decisive remaining theorem is a C0-computable bound, or a compilation of
all repeated contextual support profiles into the existing kernel/Q
architecture.  The local lemmas above do not establish that theorem.
-/
