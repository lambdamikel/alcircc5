# The MiDeLoRa calculus for ALCI_RCC5: sound, complete, not terminating

*2026-11-11. Written by Claude Fable 5.2 at Michael Wessel's request. **Unreviewed.**
The proofs below are on paper; only the last step of Lemma 2 is Lean-checked. The
implementation is tested, not verified.*

*The same material — the system, the calculus, the theorem and its proof — is
typeset in the overview paper, §8.1
([`overview_arxiv.pdf`](../overview_arxiv.pdf)), with the statements about
MiDeLoRa's source checked against the public repository.*

Artifacts: [`src/midelora_tableau.py`](../../src/midelora_tableau.py) (the reasoner)
and [`verification/python/wp139_midelora_reference.py`](../../verification/python/wp139_midelora_reference.py)
(33/33 checks pass).

---

## 0. What this is

Michael's question: why not take the tableau of the dissertation and show that it
is sound and complete for unsatisfiability, without asking it to terminate?

That can be done, and this note does it. The result does **not** move
decidability: that unsatisfiability is recursively enumerable is Lutz & Wolter's
Theorem 28, and it also follows from the hybrid-logic axiomatization in Wessel's
2003 report (report7, §5). What is new is that the fact now has a concrete
calculus with a proof, and a reasoner that runs:

* the project had no runnable reasoner whose UNSAT answers could be trusted on
  their own — the quasimodel oracle and the cover-tree tableau are both
  incomplete (`ERRATA.md`, E2), and the certified `coneScheme_unsat_full` does
  not run beyond toy sizes;
* it returns a verdict in milliseconds on `C_cyc`, on which neither existing
  reasoner returns within ten minutes, and it passes the project's gate
  (`C_bad`, `C_joint`, `C_dir` rejected; `C_sat`, `K2` accepted);
* on the 911-case suite it decides every concept — 775 with a finite model that
  an independent function re-checks, 136 by a finite closed tableau — and agrees
  with the oracle, the tableau and the suite's labels on all of them.

Termination is the one property it lacks. Termination is blocking, and a sound
blocking condition is the open problem.

## 1. Where the calculus comes from

Dissertation: M. Wessel, *Flexible und konfigurierbare Software-Architekturen für
datenintensive ontologiebasierte Informationssysteme*, TU Hamburg-Harburg 2008.
The rules are in §6.2.7.2, the prover in §6.4.4; the source is
`github.com/lambdamikel/midelora`. Read for this note: those two sections and
§3.1.5 of the dissertation, as extracted text, and the source files named below.
MiDeLoRa itself was not run (it is LispWorks/Allegro code).

The ALCI_RA_JEPD prover (`prover/alci-ra-jepd-prover.lisp`), which is also the
prover for `alci-rcc`, runs this loop, with no blocking:

| MiDeLoRa | what it does |
|---|---|
| `abox-completion` (`add-missing-edges`, `compute-minimal-label`) | every pair of individuals without an edge gets the disjunction of all base relations; the composition table is propagated |
| `abox-enumeration` with `role-consistent-p` | each disjunction is resolved to one base relation; only relationally consistent configurations are kept |
| `deterministic-expansion` | the ⊓-rule and the ∀-rule |
| `or-expansion` | the ⊔-rule |
| `some-expansion` (`prover/some-expansion2.lisp`) | the ∃-rule; with `*reuse-nodes-p*` it first tries each existing R-successor as the witness, then a fresh node |

So it is a tableau on a **complete graph**: every two nodes are related by exactly
one base relation and every triangle satisfies the table. That is the property
the cover-tree tableau lacks, and the reason this calculus gets `K2` right.

**The one point that needs a decision is EQ.** The role box declares `eq` as the
reflexive role, the completion offers `eq` between any two nodes, and nothing in
the prover merges the labels of two nodes that are EQ. As implemented, MiDeLoRa
therefore reasons under *weak* EQ (an equivalence relation). The merge for
*strong* EQ exists — `eq-collapse` and `join-nodes` in
`thematic-substrate/jepd-substrate4.lisp` — but the prover does not call it.
This project's semantics is strong EQ (EQ is identity). Two ways to get it, both
already in the code:

* keep the EQ edge and share the labels of its two ends (`join-nodes`); or,
  equivalently,
* never relate two different nodes by EQ, and let the ∃-rule reuse existing
  successors (`*reuse-nodes-p*`), always.

The second is what is stated and proved below. The two semantics differ on small
concepts: `K2x = ∃PO.(A ⊓ ∀PO.¬B ⊓ ∀DR.¬B ⊓ ∀PP.¬B ⊓ ∀PPI.¬B) ⊓ ∃PO.(B ⊓ ¬A)` is
unsatisfiable under strong EQ and satisfiable under weak EQ, by two witnesses
that are EQ and carry different labels (`wp139` F1). Every strong model is a
weak model, so UNSAT under weak EQ implies UNSAT under strong EQ, not conversely.

**Two statements of the dissertation are outdated.** Page 156 says that Lutz and
Wolter showed ALCI_RCC5 and ALCI_RCC8 undecidable; for the abstract
composition-table semantics that is not what they showed, and the question is
open (overview, §"Lutz & Wolter (2006)"). §6.4.4 gives that undecidability as the
reason for having no blocking; the true reason is that no sound blocking
condition is known. Neither affects the calculus.

## 2. The calculus

Concepts are in negation normal form over the roles DR, PO, PP, PPI (and EQ,
which under strong EQ is the identity: `∃EQ.C` and `∀EQ.C` both mean `C` here).
`cl(C₀)` is the set of subconcepts of `C₀`.

A **state** is `S = (V, L, ρ)`: a finite set of nodes `V` with a root `x₀`; a label
`L(x) ⊆ cl(C₀)` for each node; and `ρ`, which gives every ordered pair of
*different* nodes one of DR, PO, PP, PPI, such that `ρ(y,x)` is the converse of
`ρ(x,y)` and `ρ(x,z) ∈ comp(ρ(x,y), ρ(y,z))` for all different `x, y, z`.
The start state is `({x₀}, L(x₀) = {C₀}, ∅)`.

Deterministic rules, applied to a fixpoint after every step:

* **⊓** if `C ⊓ D ∈ L(x)`, add `C` and `D` to `L(x)`;
* **∀** if `∀R.D ∈ L(x)` and `ρ(x,y) = R`, add `D` to `L(y)`;
* **clash** the state is *closed* if some `L(x)` contains `⊥`, or `A` and `¬A`.

Nondeterministic rules, on a state that is not closed:

* **⊔** if `C ⊔ D ∈ L(x)` and neither is in `L(x)`: add `C`, or add `D`;
* **∃** if `∃R.D ∈ L(x)` and no `y` has `ρ(x,y) = R` and `D ∈ L(y)`:
  * *reuse*: choose a node `y` with `ρ(x,y) = R` and add `D` to `L(y)`; or
  * *fresh*: add a new node `y` with `L(y) = {D}` and `ρ(x,y) = R`, and choose
    `ρ(y,z)` for **every** other node `z` so that `ρ` is again closed under
    converse and composition.

The ⊔-rule has priority over the ∃-rule. A state to which no rule applies is
*saturated*. A **strategy** picks the ∃-demand to expand; it is **fair** if on
every infinite branch every demand that stays unsatisfied is eventually
expanded. "Oldest node first" is fair, because each label is a subset of the
finite set `cl(C₀)`, so each node raises finitely many demands in total.

The **tableau** of `C₀` is the tree of states under these rules. Each state has
finitely many successors: at most two for ⊔, and at most `|V| + 4^|V|` for ∃.

## 3. The theorem

> **Theorem.** Let `C₀` be an ALCI_RCC5 concept in negation normal form, under the
> composition-table semantics with strong EQ, and fix a fair strategy.
>
> 1. *(soundness of SAT)* If the tableau contains a saturated state that is not
>    closed, `C₀` is satisfiable, and that state is a finite model.
> 2. *(soundness of UNSAT)* If the tableau is finite and all its leaves are
>    closed, `C₀` is unsatisfiable.
> 3. *(completeness for UNSAT)* If `C₀` is unsatisfiable, the tableau is finite and
>    all its leaves are closed.
> 4. *(completeness for finite models)* If `C₀` has a model with `n` elements, the
>    tableau restricted to states with at most `n` nodes contains a saturated
>    state that is not closed.
>
> Consequently the procedure "for N = 1, 2, 3, …: search the tableau depth-first,
> refusing a fresh node beyond N" returns UNSAT on every unsatisfiable concept,
> returns SAT with a model on every concept that has a finite model, and runs
> forever exactly on the satisfiable concepts all of whose models are infinite.

That last class is not empty: `∃PP.⊤ ⊓ ∀PP.∃PP.⊤`, and the spiral concept of
`formal/PosetBridge.lean`, which has no `∃PP` and no `∃PPI` at all.

### Lemma 1 (a model guides a branch)

Call a state `S` *realized* in a model `I` by `π` if `π : V → Δ` is injective,
`ρ(x,y) = ρ^I(π x, π y)` for different `x, y`, and every concept in `L(x)` holds
at `π(x)`.

*If `S` is realized, then `S` is not closed; the deterministic rules keep it
realized by the same `π`; and whenever a nondeterministic rule applies, one of
its alternatives is realized, by an extension of `π`.*

*Proof.* A clash would put `⊥`, or `A` and `¬A`, at one element. The ⊓- and
∀-rules add concepts that hold at the image, by the semantics and because `π`
preserves relations. For ⊔: `C ⊔ D` holds at `π(x)`, so one disjunct does. For ∃:
`∃R.D` holds at `π(x)`, so some `w` has `ρ^I(π x, w) = R` and satisfies `D`. If
`w = π(y)` for a node `y`, then `ρ(x,y) = R` and the *reuse* alternative with `y`
is realized by `π`. Otherwise take the *fresh* alternative, map the new node to
`w`, and copy its relations from `I`. They are proper relations, because `w` is
not in the image of `π` and EQ is identity; and `ρ` stays closed because `I` is
an RCC5 frame. Injectivity is kept. ∎

Strong EQ is used exactly once, in "they are proper relations". Without the
*reuse* alternative the case `w = π(y)` has no realized successor, which is why
reuse cannot be switched off under strong EQ.

### Lemma 2 (an open fair branch is a model)

*Let `S₀, S₁, …` be a finite or infinite branch, none of whose states is closed,
which ends in a saturated state if it is finite and is fair if it is infinite.
Let `V = ⋃ Vᵢ`, `L(x) = ⋃ Lᵢ(x)`, `ρ = ⋃ ρᵢ`. Then `(V, ρ)` with EQ on the diagonal
is an RCC5 frame, and `C₀` holds at `x₀` under the valuation `A ↦ {x : A ∈ L(x)}`.*

*Proof.* Rules only add nodes, add concepts to labels and relate new nodes; a
relation once given never changes. So the unions are well defined. Converse and
composition are conditions on pairs and triples of nodes; each pair and triple
is present from some stage on, where the condition holds. So `ρ` is a converse-
closed, composition-closed atomic network, proper off the diagonal.

`L` is a Hintikka labelling of that frame:

* no clash: two clashing members of `L(x)` are both in some `Lᵢ(x)`, and `Sᵢ`
  would be closed;
* ⊓ and ∀: the premises are present at some stage, and the deterministic rules
  are applied to a fixpoint after every step;
* ⊔: the ⊔-rule has priority, so a disjunction present at a stage is resolved
  before the next ∃-step; in the finite case the last state is saturated;
* ∃: if `∃R.D ∈ L(x)`, the demand is satisfied at some stage — by saturation in
  the finite case, by fairness in the infinite case — and satisfied demands stay
  satisfied, because labels and relations only grow.

A Hintikka labelling of an RCC5 frame is a model of every concept in its
labels. That step is the theorem `satisfiable_iff_hintikkaP` (with `truth_lemmaP`)
of `formal/Round19Transport.lean`. ∎

### Proof of the theorem

(1) is Lemma 2 for a finite branch. (2): if `C₀` had a model, the start state
would be realized (map `x₀` to an element satisfying `C₀`), and by Lemma 1 the
tableau would contain a branch of realized states, none of them closed; a finite
tableau would end that branch in a leaf that is not closed. (3): the tableau is
finitely branching. If it were infinite, König's lemma would give an infinite
branch; none of its states is closed, since a closed state has no successors;
the strategy makes it fair; Lemma 2 would give a model. So the tableau is
finite. A leaf that is not closed is saturated, and by (1) would give a model.
So all leaves are closed. (4): follow Lemma 1 from the start state. The
realization is injective, so no state on the realized branch has more than `n`
nodes; with at most `n` nodes and labels inside `cl(C₀)` only finitely many
steps are possible, so the branch ends, in a state that is saturated and not
closed. For the consequence: for a bound `N` the restricted tableau is finite,
so each round ends. If `C₀` is unsatisfiable, take `N` at least the largest
state of the finite full tableau: no branch is refused a node, and all leaves
are closed. If `C₀` has a model with `n` elements, round `n` finds a saturated
open state unless an earlier round did. If neither, no round can end with a
verdict, by (1) and (2). ∎

## 4. The implementation, and what was tested

`src/midelora_tableau.py`, about 300 lines. `check(C, max_nodes, eq, reuse,
time_limit)` returns `SAT` with a model, `UNSAT`, or `UNKNOWN` when the node bound
or the time limit is reached. It derives the composition table from sets and
copies it from nowhere. Three liberties with §2, none of which changes the
tableau's verdict: the fresh node's relations are chosen one existing node at a
time with the deterministic rules run in between, so that a clash prunes early;
a disjunction one of whose sides is a literal that clashes is resolved without
branching; and under `eq='weak'` the relations include EQ between different
nodes, which is MiDeLoRa as implemented and is outside the theorem above.

`wp139` (33/33, about three minutes):

* **The table.** Derived from sets, the same for universes of 4, 5 and 6 points;
  equal in all 25 cells to MiDeLoRa's `rcc5-rolebox`; equal on proper relations
  to the table of the existing reasoner.
* **Named concepts**, each with an independent reason for its status:
  `K2`, `K2dr`, `C_cyc` and its erasure, the horizontal 3-cycle and 3-chain,
  `C_bad`, `C_joint`, `C_dir`, `C_sat`, `C_force`, `C_recursive`, `C_optional`,
  the strong-EQ PO-loop, three of MiDeLoRa's own test concepts, and the 4-colour
  spiral (a 4-point model, on a closure of 122 members). All as expected.
* **Exact ground truth.** 1,000 random concepts of a class for which exhaustive
  search over closed networks on at most four points is a decision procedure:
  no error (634 satisfiable, 366 not). 300 under weak EQ against the weak truth:
  no error.
* **The 911-case suite.** Every concept decided; 775 SAT, each with a model that
  passes an independent check; 136 UNSAT; no disagreement with the oracle, the
  cover-tree tableau or the labels.
* **No answer where there is none.** `∃PP.⊤ ⊓ ∀PP.∃PP.⊤`, its dual, `Cdchain`, and
  the 5-colour spiral: `UNKNOWN` at the node bound, neither a false refutation
  nor a false model.

## 5. Limits

* **Unreviewed**, and the theorem is a paper proof. Only the final step of
  Lemma 2 is Lean-checked. Formalizing the rest — Lemma 1 and König's lemma over
  a concrete tableau — is the natural next step; refutation soundness alone
  would already turn closed tableaux into kernel-checkable UNSAT certificates.
* The implementation is tested against exact ground truth on one class and
  against known verdicts elsewhere. It emits no proof object for UNSAT, so an
  UNSAT answer is as trustworthy as the code.
* It is exponential and blind: no caching, no dependency-directed backjumping
  (MiDeLoRa has both). The 5-colour spiral exhausts 4 nodes in 15 seconds and
  5 nodes not within 100.
* The calculus proved here is MiDeLoRa's with the EQ treatment fixed to strong.
  For MiDeLoRa exactly as implemented (weak EQ) the same argument goes through
  with `π` not required injective; that is not written out, and `wp139` C2 is
  the evidence.
* It says nothing about ALCI_RCC8, for which MiDeLoRa has the role box too.

## References

* M. Wessel. *Flexible und konfigurierbare Software-Architekturen für
  datenintensive ontologiebasierte Informationssysteme.* Dissertation, TU
  Hamburg-Harburg, 2008. `tore.tuhh.de/handle/11420/834`.
* MiDeLoRa source: `github.com/lambdamikel/midelora`.
* M. Wessel. Qualitative spatial reasoning with the ALCI_RCC family — first
  results and unanswered questions. Memo FBI-HH-M-324/03, 2003
  (`papers/report7.pdf`): the axiomatization (§5), and the remark that the
  prototype's calculus "can be shown to be sound and complete" (end of §3).
* C. Lutz, F. Wolter. Modal logics of topological relations. *LMCS* 2(2:5), 2006.
  Theorem 28.
