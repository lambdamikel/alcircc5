# Proposed Lean 4 module map

The final decision theorem must not import `Legacy/MultiTier`.

```text
AlciRcc5/
  RCC5/
    Atom.lean
    CompTable.lean
    Network.lean
    OrderedDisjoint.lean
    TokenRepresentation.lean

  Logic/
    Syntax.lean
    NNF.lean
    Prepared.lean
    PositiveClosure.lean
    POFree.lean
    Semantics.lean
    SupportType.lean
    Demand.lean

  ConeScheme/
    State.lean
    StateEnum.lean
    LocalRules.lean
    Transition.lean
    Scheme.lean
    Occurrence.lean
    VerticalComponent.lean
    BaseOrder.lean
    DisjointClosure.lean
    ProtectedPO.lean
    Frame.lean
    Model.lean
    SpectrumInvariant.lean
    TruthLemma.lean
    SchemeSoundness.lean
    FiniteGfp.lean
    Elimination.lean
    StrategyExtraction.lean
    SourceSignature.lean
    SourceTransitions.lean
    Soundness.lean
    Completeness.lean
    Decision.lean

  Regression/
    NoFiniteModel.lean
    MixedVerticalCycle.lean
    ProtectedPO.lean
    DRDownward.lean
    RoleAwareDemand.lean
    D1MultiGroupCycle.lean
    D2SevenPoint.lean
    EAnchorCompatibility.lean

  Legacy/
    MultiTier/
      ...

  Audit/
    PublicTheorems.lean
    AxiomReport.lean
    ExecutableDeps.lean
```

## Public interfaces

```lean
def Formula.ForallPOFree : Formula -> Prop
def Formula.forallPOFreeB : Formula -> Bool
theorem forallPOFreeB_reflect :
  C.forallPOFreeB = true <-> C.ForallPOFree

structure Prepared (C : Formula) where
  nnfC    : NNFConcept
  closure : Finset NNFConcept
  rootIx  : ClosureIx closure
  nnf_eq  : nnfC = nnf C
  cl_eq   : closure = positiveClosure nnfC
  root_eq : decode rootIx = nnfC

theorem sat_nnf_iff : Satisfiable (nnf C) <-> Satisfiable C
theorem inverseRole_nnf_conv : ...

abbrev TypeCode (p : Prepared C) := Finset (ClosureIx p.closure)

structure ConeState (p : Prepared C) where
  ty    : TypeCode p
  lower : Finset (TypeCode p)

def SupportTypeOK : TypeCode p -> Prop
def supportTypeOKB : TypeCode p -> Bool
theorem supportTypeOKB_reflect :
  supportTypeOKB p T = true <-> SupportTypeOK p T

abbrev DemandCode (p : Prepared C) := ClosureIx p.closure
def demands (p : Prepared C) (s : ConeState p) : Finset (DemandCode p)
theorem mem_demands_iff : ...

def StateLocalOK : ConeState p -> Prop
def TransitionOK :
  ConeState p -> DemandCode p -> ConeState p -> Prop

structure ConeScheme (p : Prepared C) where
  live     : Finset (ConeState p)
  root     : ConeState p
  root_mem : root ∈ live
  root_has : p.rootIx ∈ root.ty
  next     : ConeState p -> DemandCode p -> ConeState p
  next_mem : ...
  next_ok  : ...

def prune (X : Finset (ConeState p)) : Finset (ConeState p) :=
  X.filter fun s => viableInB p X s

def survivors (p : Prepared C) : Finset (ConeState p)
theorem survivors_fixed :
  prune p (survivors p) = survivors p

theorem demandsB_complete : ...
theorem hasTargetB_reflect : ...
theorem viableInB_reflect : ...
theorem prune_mem_iff : ...
theorem acceptingB_reflect : ...

theorem survivors_to_scheme :
  p.rootIx ∈ q.ty -> q ∈ survivors p -> ConeScheme p

theorem occurrence_orderedDisjoint :
  OrderedDisjointFrame (World cs) (Lt cs) (Disj cs)

theorem protectedPO_residual :
  ProtectedPO cs x y -> occRel cs x y = .po

theorem truth_lemma
    (hfree : C.ForallPOFree)
    (hD : d ∈ worldType x) :
  OccModel cs |=[x] decode d

theorem scheme_sound (hfree : C.ForallPOFree) :
  Satisfiable C

noncomputable def sourceSig (p : Prepared C) (M : Model W) (x : W) :
  ConeState p

theorem sourceSig_survives (hfree : C.ForallPOFree) :
  sourceSig p M x ∈ survivors p

def coneSatCoreB (C : Formula) : Bool
theorem coneSatCoreB_correct (hfree : C.ForallPOFree) :
  coneSatCoreB C = true <-> Satisfiable C

inductive CheckResult | sat | unsat | outOfScope
def coneCheck (C : Formula) : CheckResult
theorem coneCheck_sat_iff :
  coneCheck C = .sat <->
    C.ForallPOFree /\ Satisfiable C
theorem coneCheck_unsat_iff :
  coneCheck C = .unsat <->
    C.ForallPOFree /\ Not (Satisfiable C)
theorem coneCheck_outOfScope_iff :
  coneCheck C = .outOfScope <-> Not C.ForallPOFree

def satisfiableDecidable (hfree : C.ForallPOFree) :
    Decidable (Satisfiable C) :=
  if h : coneSatCoreB C = true then
    isTrue ((coneSatCoreB_correct hfree).mp h)
  else
    isFalse (fun hs => h ((coneSatCoreB_correct hfree).mpr hs))
```

## Reuse policy

Audit and reuse only narrow foundational results whose exact source and
dependencies are available:

- NNF and positive closure;
- normalized-root preparation and inverse-role normalization;
- RCC5 converse and composition table;
- the forced singleton cells used by source completeness;
- support/model-type coherence;
- the general ordered-disjoint normal form.

The reported `MultiTier`, kernel-fusion, borrowed-edge, and anchor-placement
modules may remain as independent work, but they are not proof dependencies of
`ConeScheme/Decision.lean`.

## Release rules

- `set_option autoImplicit false` in release modules.
- No `sorry`, `admit`, `sorryAx`, new `axiom`, or unsafe proof dependency.
- Boolean checkers have the complete two-way reflection spine through
  `acceptingB_reflect`.
- `#print axioms` is checked against an exact allowlist for every public theorem;
  a separate declaration scan catches unused custom axioms.
- Release regressions use kernel `by decide`, or explicitly document any
  additional trust introduced by `native_decide`.
- Generated-code evaluation of `coneCheck` is tested.
- The executable import graph may not reach `SourceSignature`, `Completeness`,
  or `Legacy`.
- Warnings are errors.
- Python probes are differential regressions only and never theorem inputs.
