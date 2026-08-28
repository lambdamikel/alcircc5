# ConeScheme decision procedure

## 1. Prepared input, positive closure, and support types

The public wrapper accepts a raw concept. A `Prepared C` object stores `nnf C`,
its positive subformula closure, and the closure index of the normalized root.
The load-bearing normalization theorem is
`Satisfiable (nnf C) <-> Satisfiable C`; inverse-role syntax is normalized to
the RCC5 converse atom at the same boundary. Define `ForallPOFree C` by
inspecting `positiveClosure (nnf C)`.

Do not Boolean-dual-complete the closure. Complete dual types would force
preservation of negative PO information such as
`not (exists PO.D) = forall PO.(not D)`, which residual PO does not support.

Let `m = |Cl+(nnf C)|`. A raw type code is a bitset over this closure.
`SupportTypeOK` requires exactly:

1. bottom is absent and top is present when it occurs in the closure;
2. complementary concept literals are not both present;
3. conjunction membership implies both conjuncts;
4. disjunction membership implies at least one disjunct.

Types are not maximal or Boolean-complete. Only membership-to-truth is proved.
There are at most `N = 2^m` support types.

For a type `T` define:

```text
A_r(T) = { D | forall r.D belongs to T }.
```

## 2. Cone signatures

A signature is `q = (T,S)`, where `T` is a raw type code and `S` is a finite
set of raw type codes. Enumeration ranges over raw bitsets and powersets, then
filters by reflected support/local predicates. This keeps the executable free
of proof-carrying data. `S` is an upper bound on the types of strict
PP-predecessors.

```text
cone(q) = S union {T}.
```

Local admissibility requires:

1. every code in the state is a coherent support type;
2. EQ universals and existentials are local;
3. for every `U in S`:
   - `A_PP(U) subseteq T`;
   - `A_PPI(T) subseteq U`.

The number of signatures is bounded by:

```text
K = N * 2^N <= 2^(m + 2^m).
```

## 3. Transition compatibility

For `q=(T,S)` and `q'=(T',S')`:

- PP: `cone(q) subseteq S'`;
- PPI: `cone(q') subseteq S`;
- DR: for all `U in cone(q)` and `V in cone(q')`,
  `A_DR(U) subseteq V` and `A_DR(V) subseteq U`;
- PO: no structural label condition;
- EQ: no child; the body must already belong to `T`.

For every non-EQ demand `exists r.D in T`, the target type must contain `D`.
A demand code is the full closure index of `exists r.D` (or an explicit
`(r, bodyIx)` pair), never the body alone. The demand enumerator must prove a
two-way membership theorem so equal bodies under different roles remain
distinct.

## 4. Greatest fixed point

Let `Static` be the finite set of locally admissible signatures. Use a
reductive executable operator:

```text
prune(X) = { q in X | every non-EQ demand at q has
                      a compatible target in X,
                      and every EQ demand is local }
```

Starting from `X0=Static`, iterate `Xi+1=prune(Xi)`. Prove monotonicity,
`prune(X) subseteq X`, stabilization within `K` rounds, and greatest
post-fixedness. Accept exactly when a survivor contains the prepared normalized
root code, not the raw input syntax.

An abstract `ConeScheme` should precede the GFP implementation. Its target
function has the proof-independent type
`ConeState -> DemandCode -> ConeState`; correctness fields are conditional on
state and demand membership. `StrategyExtraction` later turns survivors into
such a scheme. A selected target is a control pointer only.

## 5. Fresh-occurrence semantics

Unfold the finite control graph into the tree of finite demand words.

- Every non-EQ demand creates a distinct fresh child occurrence.
- A PP birth edge is oriented parent < child.
- A PPI birth edge is oriented child < parent.
- A DR or PO birth edge starts a fresh vertical component.
- EQ remains at the current occurrence.

Let `lt` be the transitive closure of PP/PPI birth edges. Let `disj` be the
symmetric downward closure of DR birth edges. Define RCC5 by identity, `lt`,
its converse, `disj`, and residual PO, in that priority order.

Backpointers never identify occurrences. An occurrence is an indexed inductive
path because the available demand set changes with its current control state.
This preserves strong EQ and turns a control self-loop into a genuine infinite
chain.

## 6. Soundness obligations

The proof must establish:

1. every base order edge raises an integer occurrence height by one;
2. `lt` is transitive and irreflexive;
3. removing horizontal births yields vertical components, and contracting each
   vertical component yields a tree of unique horizontal bridges;
4. `disj` is symmetric, irreflexive, downward closed, and disjoint from `lt`;
5. a PO birth edge remains residual PO after all closures;
6. actual lower occurrence types are contained in each declared spectrum;
7. the RCC5 relation is strong, total, converse-closed, and
   composition-closed;
8. the support-type truth lemma holds at every occurrence.

No Buchi or parity condition is required: ALCI has no fixpoint eventualities,
and every existential is realized immediately at every occurrence.

## 7. Completeness obligations

From a satisfying source model define, in a `noncomputable section`:

```text
T_x = { D in Cl+(C) | x satisfies D }
S_x = { T_y | y PP x }.
```

Each `(T_x,S_x)` is locally admissible. A PP edge gives
`cone(q_x) subseteq S_y`; PPI is dual. A DR edge makes the two inclusive lower
cones pairwise DR by the singleton composition cells
`PP o DR = DR` and `DR o PPI = DR`, giving DR-cone compatibility.

Define realized signatures as a predicate/`Set`
`RealizedSig s := exists x, sourceSig x = s`, never as a computable `Finset`
over the possibly infinite source carrier. Prove that this predicate is closed
under source witness transitions, or prove `sourceSig_mem_iterate` directly by
induction. Hence every satisfying root survives descending elimination.

## 8. Public correctness theorem

```lean
def coneSatCoreB (C : Formula) : Bool

theorem coneSatCoreB_correct
    (C : Formula) (hfree : C.ForallPOFree) :
  coneSatCoreB C = true <-> Satisfiable C
```

`coneSatCoreB` has no promised semantics outside the fragment and should stay
internal. The public three-valued wrapper must export all three characterizing
theorems:

```lean
theorem coneCheck_sat_iff :
  coneCheck C = .sat <->
    C.ForallPOFree /\ Satisfiable C

theorem coneCheck_unsat_iff :
  coneCheck C = .unsat <->
    C.ForallPOFree /\ Not (Satisfiable C)

theorem coneCheck_outOfScope_iff :
  coneCheck C = .outOfScope <-> Not C.ForallPOFree
```

For callers that already carry the fragment proof, expose:

```lean
def satisfiableDecidable
    (C : Formula) (hfree : C.ForallPOFree) :
    Decidable (Satisfiable C)
```

The command-line or library-facing wrapper should return a three-valued
`CheckResult` (`sat`, `unsat`, or `outOfScope`) after running
`forallPOFreeB`. An out-of-fragment formula must be reported as out of scope,
not UNSAT.

## 9. Boolean reflection spine

The executable theorem must be connected to the Prop specification through:

- `supportTypeOKB_reflect` and `stateLocalOKB_reflect`;
- `demandsB_complete` and `transitionOKB_reflect`;
- `hasTargetB_reflect` and `viableInB_reflect`;
- `prune_mem_iff` and `survivors_fixed`;
- `acceptingB_reflect` and `coneSatCoreB_correct`.

Source-signature files are noncomputable proof modules and must not occur in
the import graph or generated evaluator for `coneCheck`.

## 10. Conservative bound

A naive implementation precomputes compatibility and performs at most `K`
pruning rounds. Its deterministic running time is bounded by
`2^(2^O(m))`. This is a 2EXPTIME upper bound only; no optimality or lower-bound
claim is made.
