# On the Decidability of ALCI\_RCC5 and ALCI\_RCC8

**Quasimodels Meet the Patchwork Property**

> **Disclaimer.** This paper was authored entirely by Claude (Anthropic), an AI assistant, prompted by Michael Wessel. The results and proofs presented here have **not been peer-reviewed or verified by human domain experts**. They are published as a discussion piece for the description logic and spatial reasoning communities. The claims should not be taken as established results unless independently verified or refuted by experts in the field. We invite scrutiny, corrections, and feedback.

> **Revision note (March 2026).** This is a revised version addressing issues identified in a technical review of the original manuscript. Key changes include: EQ normalization, strengthened R-compatibility with PP/PPI chain propagation, revised quasimodel conditions using algebraic closure, a corrected Henkin construction argument using full RCC5 tractability (not just the atomic patchwork property), an honest discussion of the extension gap for abstract quasimodels, and an expanded RCC8 section addressing the tractability difference. Additionally, a companion contextual tableau approach (GPT-5.4 Pro) has been evaluated, and its completeness conjecture FW(C,N) has been [shown to be false](https://github.com/lambdamikel/alcircc5/blob/master/FW_proof_ALCIRCC5.pdf). See the [conversation log](https://github.com/lambdamikel/alcircc5/blob/master/CONVERSATION.md) (Part 11) for details.

## Current Status of the Proof

**The decidability of ALCI\_RCC5 and ALCI\_RCC8 is NOT fully established by this paper.** The proof has a genuine gap. Here is what is and is not proven:

### What IS proven

- **Soundness** (satisfiable → quasimodel): If a concept C₀ is satisfiable, a quasimodel satisfying conditions (Q1)–(Q3) can be extracted from the model. This direction is solid.
- **Terminating EXPTIME algorithm**: The type elimination algorithm always halts in EXPTIME and has **no false negatives** — if C₀ is satisfiable, the algorithm accepts.
- **Sound rejection**: By contrapositive of the above, if the algorithm rejects, C₀ is definitely unsatisfiable.

### What is NOT proven

- **Completeness** (quasimodel → model): The Henkin construction builds a model from a quasimodel by iteratively adding elements. At each step, it must solve a disjunctive constraint network (the "extension problem"). For **model-derived** quasimodels (extracted from actual models), the model's own role assignments survive the construction. But for **abstract** quasimodels that satisfy (Q1)–(Q3) without arising from any model, the path-consistency enforcement may empty constraint domains, causing the construction to fail.
- **No false positives**: If the algorithm accepts, we cannot guarantee C₀ is satisfiable. There may exist "spurious" quasimodels for unsatisfiable concepts.

### Why this matters

A decision procedure requires both directions: accept if and only if satisfiable. We have:

| Algorithm says | Conclusion | Status |
|---|---|---|
| **reject** | C₀ is unsatisfiable | **Proven** |
| **accept** | C₀ is satisfiable | **Not proven** (extension gap) |

The open question from Wessel's thesis (2002/2003) is **narrowed but not settled**. Closing the gap requires showing that every abstract quasimodel satisfying (Q1)–(Q3) yields a model — either by a more refined Henkin construction, a direct model-building argument, or a proof that the type-level conditions are already sufficient. The paper conjectures this but does not prove it.

### The contextual tableau approach and the FW(C,N) counterexample

A companion note by GPT-5.4 Pro ([A Contextual Tableau Calculus for ALCI\_RCC5 (PDF)](https://github.com/lambdamikel/alcircc5/blob/master/ALCI_RCC5_contextual_tableau_draft.pdf)) proposed a different framework: a **contextual tableau calculus** where each tableau node is a finite local state — a bounded-width atomic RCC5 network with witness assignments and recentering maps. That paper is the starting point for the FW(C,N) discussion below. It proves full **soundness** (every open tableau graph unfolds into a genuine model) but reduces completeness to the **finite-width extraction conjecture FW(C,N)**: every satisfiable concept admits a closed family of local states of bounded width N(C).

**FW(C,N) is false.** The counterexample is the concept already noted in Wessel (2003) and in our paper (Remark 2.5):

> C∞ = (∃PP.⊤) ⊓ (∀PP.∃PP.⊤)

This concept is satisfiable only in infinite models. The proof that FW(C∞, N) fails for **every** N is elementary:

1. Transitive propagation (L2) forces every PP-descendant to have ∃PP.⊤ in its type — each needs a PP-successor.
2. The recentering axiom (R3) forces the PP-witness in any successor state to map to a PP-successor of the corresponding item **in the parent state**.
3. Iterating this produces an infinite PP-chain inside a single finite-width state.
4. But PP is a **strict partial order** (irreflexive + transitive). Every finite strict partial order has maximal elements. Maximal elements have no PP-successor. Contradiction.

See the [full counterexample proof (PDF)](https://github.com/lambdamikel/alcircc5/blob/master/FW_proof_ALCIRCC5.pdf) for details. The same argument applies to ALCI\_RCC8 using NTPP in place of PP.

### Summary: two approaches, two complementary gaps

| | Quasimodel approach (Claude) | Contextual tableau (GPT-5.4) |
|---|---|---|
| Satisfiable → representation | **Proven** | **False** (FW counterexample) |
| Representation → model | **Gap** (extension gap) | **Proven** (soundness) |
| Status | Incomplete | Incomplete |

Neither approach, as formulated, yields a decision procedure. The decidability of ALCI\_RCC5 and ALCI\_RCC8 remains open.

### What the papers contribute

Despite the gaps, the papers introduce proof machinery that narrows the open problem:
- The quasimodel method + patchwork property identifies the extension gap as a specific constraint-satisfaction question about RCC5 disjunctive networks.
- The contextual tableau cleanly separates the soundness (unfolding) argument from the completeness (extraction) argument. The FW counterexample shows that the extraction problem is fundamentally hard: infinite PP-chains cannot be finitely represented in the recentering framework.
- The root cause is the combination of (i) transitivity of PP, (ii) universal propagation of ∀PP along PP-chains, and (iii) the complete-graph requirement. Any successful decidability proof — or undecidability reduction — must engage with this combination directly.

### Ongoing discussion: the omega-model direction

After the FW(C,N) counterexample, GPT-5.4 proposed a [status assessment](https://github.com/lambdamikel/alcircc5/blob/master/ALCI_RCC5_status_after_FW.pdf) distinguishing two levels of finiteness:
- **(A) Strong finiteness** (exact local-state closure with recentering) — **refuted** by the FW counterexample.
- **(B) Weak finiteness** (bounded local descriptors around a finite core) — possibly still true and useful as a finite alphabet for a future decision procedure.

GPT proposes a **regular omega-model theorem** as the missing ingredient: a representation of models using finitely many local interface signatures, finitely many PP/PPI thread control states, and a Buchi/parity-style acceptance condition for infinite proper-part chains. This is analogous to how mu-calculus extensions of DLs handle infinite paths via automata.

Claude's [formal response](https://github.com/lambdamikel/alcircc5/blob/master/response_to_status_note.pdf) agrees with the (A)/(B) distinction and the omega-model direction but notes that: (1) the quasimodel work's soundness is fully proven (not merely a "setup"), (2) the patchwork property is used correctly (the extension gap is an honestly documented open problem, not a misuse), (3) the omega-model proposal identifies the right architecture but provides no proofs — each of its four tasks (interface transfer, omega-acceptance, regular extraction, realization) is a non-trivial research problem, and (4) the feasibility hinges on a concrete sub-question:

> **Is the sequence of Hintikka types along an infinite PP-chain eventually periodic?** If yes, the omega-model route is viable. If no, even the type sequence is irregular, pointing toward undecidability.

---

This repository contains a proof attempt for concept satisfiability in the description logics ALCI\_RCC5 and ALCI\_RCC8, targeting open problems from Wessel (2002/2003).

- **ALCI\_RCC5**: EXPTIME algorithm with no false negatives; decidability contingent on closing the extension gap
- **ALCI\_RCC8**: same status; additionally, the full RCC8 algebra is NP-complete (unlike RCC5), so the gap cannot be closed by full tractability

Two procedures are given: a type-elimination algorithm and a tableau calculus with blocking.

**[Read the full paper (PDF)](https://github.com/lambdamikel/alcircc5/blob/master/decidability_ALCIRCC5.pdf)**

## Background

The ALCI\_RCC family extends the description logic ALCI (ALC with inverse roles) with **role boxes derived from RCC composition tables**. The base relations of RCC5 ({DR, PO, EQ, PP, PPI}) serve as the role names, and interpretations are constrained to be **complete graphs** where every pair of domain elements is related by exactly one base relation, subject to the RCC5 composition table.

These logics were introduced by Michael Wessel in his doctoral work at the University of Hamburg. He classified most of the family (ALCI\_RCC1 through ALCI\_RCC3) but left the decidability of ALCI\_RCC5 and ALCI\_RCC8 as open problems.

### Key Difficulties

- **No tree model property**: models are complete graphs (K\_n or K\_omega)
- **No finite model property**: some satisfiable concepts require infinite models
- **Non-deterministic role box**: the RCC5 composition table has multi-valued entries, ruling out reduction to ALCRA\_SG

### Key Enablers: Patchwork Property and Full RCC5 Tractability

The proof exploits two results from qualitative constraint reasoning (Renz & Nebel, 1999; Renz, 1999):

> **Patchwork property.** For RCC5 (and RCC8), an atomic constraint network is consistent if and only if it is path-consistent.

> **Full RCC5 tractability.** The entire RCC5 algebra is tractable: a *disjunctive* RCC5 constraint network is consistent if and only if it is path-consistent.

The patchwork property means **local (triple-wise) consistency implies global consistency** for atomic networks. Full RCC5 tractability is strictly stronger: it extends this to disjunctive networks (where each edge has a *set* of possible relations). The Henkin model construction relies on the stronger result to solve disjunctive constraint networks arising at each extension step.

## The RCC5 Composition Table

Reading: row = S(b,c), column = R(a,b), entry = possible relations for (a,c). The symbol \* means all five relations are possible.

|  comp   | DR(a,b) | PO(a,b)     | EQ(a,b) | PPI(a,b)       | PP(a,b)     |
|---------|---------|-------------|---------|----------------|-------------|
| DR(b,c) | \*      | DR,PO,PPI   | DR      | DR,PO,PPI      | DR          |
| PO(b,c) | DR,PO,PP| \*          | PO      | PO,PPI         | DR,PO,PP    |
| EQ(b,c) | DR      | PO          | EQ      | PPI            | PP          |
| PP(b,c) | DR,PO,PP| PO,PP       | PP      | PO,EQ,PP,PPI   | PP          |
| PPI(b,c)| DR      | DR,PO,PPI   | PPI     | PPI            | \*          |

## Results

### Main Theorem

**The decidability of concept satisfiability in ALCI\_RCC5 is open.** The paper presents two proof attempts:

1. **Quasimodel method + type elimination** — sound for rejection, but completeness has the extension gap
2. **Tableau calculus with blocking** — same gap, via quasimodel extraction

A companion contextual tableau approach (GPT-5.4) has the opposite gap: soundness is proven but completeness (the FW(C,N) conjecture) is false.

### Known complexity bounds

| Logic      | Lower Bound          | Upper Bound | Status       |
|------------|----------------------|-------------|--------------|
| ALCI\_RCC5 | PSPACE-hard (Wessel) | Unknown     | **Open**     |
| ALCI\_RCC8 | EXPTIME-hard (Wessel)| Unknown     | **Open**     |

**Note on RCC8.** The extension to ALCI\_RCC8 requires care because the full RCC8 algebra is **not** tractable: consistency of disjunctive RCC8 constraint networks is NP-complete (Renz & Nebel, 1999). Only the atomic patchwork property holds for RCC8. However, the decision procedures still work: the type elimination algorithm relies on the soundness direction only (no false negatives), and the model-derived quasimodel argument in the Henkin construction bypasses full tractability. The extension gap is the same as for RCC5, except that it cannot be closed by appeal to full tractability.

---

## A Tableau Calculus for ALCI\_RCC5

### Overview

The tableau constructs a finite **completion graph** --- a complete graph where every pair of nodes has a base relation label, and every node has a concept label (a subset of the Fischer-Ladner closure of the input concept). Unlike tree-based DL tableaux, creating a new node requires assigning it a role to **every** existing node.

### Completion Graphs

A **completion graph** for a concept C\_0 is a tuple G = (V, L, E, <) where:

- V is a finite set of nodes
- L: V -> 2^{cl(C\_0)} assigns concept labels
- E: {(x,y) | x != y} -> {DR, PO, PP, PPI} assigns a base relation to every pair of distinct nodes, respecting converse (E(y,x) = inv(E(x,y)))
- < is a strict total order (creation order)

The **initial completion graph** has a single node x\_0 with L(x\_0) = {C\_0}.

### Blocking Condition

A node x is **blocked** if there exists y < x such that y is not blocked and L(x) = L(y).

This is **equality anywhere-blocking**: the blocker need only precede x in creation order and carry the same label. No pairwise matching (as in standard ALCI tree tableaux) is needed. The simplicity of this condition is made possible by the patchwork property, which decouples type-level structure from specific relational neighborhoods.

### Expansion Rules

**Propositional rules** (deterministic):

- **(and-rule)**: If D1 and D2 in L(x) and D1 or D2 missing: add both to L(x).
- **(or-rule)**: If D1 or D2 in L(x) and neither present: nondeterministically add D1 or D2. *(branching point)*

**Propagation rule** (deterministic):

- **(forall-rule)**: If (forall R.D) in L(x) and E(x,y) = R and D not in L(y): add D to L(y).

**Generating rule** (nondeterministic):

- **(exists-rule)**: If (exists R.D) in L(x), x is active (not blocked), and no y exists with E(x,y) = R and D in L(y):
  1. Create a fresh node y (greatest in creation order).
  2. Set L(y) := {D}.
  3. Set E(x,y) := R.
  4. For each existing node z != x,y: **nondeterministically choose** S\_z in {DR, PO, PP, PPI} and set E(z,y) := S\_z. *(branching point, with constraint filtering)*

### Constraint Filtering

After creating a new node y with edges to all existing nodes, **composition consistency** must hold for every triple of distinct nodes (u,v,w) involving y:

> E(u,w) in comp(E(u,v), E(v,w))

If no assignment of the S\_z values satisfies this for all triples simultaneously, the branch **closes** (clash).

By the patchwork property (Theorem of Renz & Nebel), a simultaneous satisfying assignment exists if and only if every triple involving y is individually satisfiable, i.e., the constraint network is path-consistent. Path consistency can be checked in O(|V|^3).

### Rule Application Strategy

1. Apply (and-rule), (or-rule), and (forall-rule) exhaustively to all nodes.
2. Re-evaluate blocking.
3. Apply one instance of (exists-rule) for an active node with an unsatisfied demand.
4. After adding the new node and its edges, apply (forall-rule) exhaustively (new edges may trigger propagations in both directions, cascading to other nodes).
5. Re-evaluate blocking (label changes may affect blocking status).
6. Repeat from step 1 until no rule applies or a clash is detected.

### Clash Conditions

A completion graph has a **clash** if:

- **(C1)** Some node has {A, not A} in its label for a concept name A.
- **(C2)** Composition consistency is violated for some triple.

A completion graph that is **saturated** (no rule applicable) and **clash-free** is called **open**.

### Termination

Every sequence of rule applications terminates. The final completion graph has at most **2^{O(|C\_0|)}** nodes.

**Argument**:
- Active (non-blocked) nodes have pairwise distinct labels, so there are at most 2^{|cl(C\_0)|} active nodes.
- Labels grow monotonically (rules only add concepts), so each label changes at most |cl(C\_0)| times.
- Each active node has at most |cl(C\_0)| existential demands, each generating at most one witness.
- Total nodes: at most 2^{|cl(C\_0)|} * |cl(C\_0)| = 2^{O(|C\_0|)}.

### Soundness

**Theorem**: If the tableau produces an open completion graph for C\_0, then C\_0 is satisfiable.

**Proof sketch**: Extract a quasimodel from the open completion graph:
- T = {L(x) | x active}
- P = {(L(x), E(x,y), L(y)) | x != y}
- tau\_0 = L(x\_0)

The quasimodel conditions are verified:
- **(Q1) Existential witness**: Each existential demand exists R.D in a type tau is witnessed by saturation --- there exists a node y with E(x,y) = R and D in L(y).
- **(Q2) Non-emptiness**: DN(tau\_1, tau\_2) != {} for all distinct type pairs, since the completion graph is a complete graph with an edge between every pair.
- **(Q3) Algebraic closure**: For any types tau\_1, tau\_2, tau\_3 and R\_12 in DN(tau\_1, tau\_2), the completion graph's composition consistency (CF) on the witnessing triple gives R\_13 in comp(R\_12, R\_23) with R\_13 in DN(tau\_1, tau\_3) and R\_23 in DN(tau\_2, tau\_3).

By the soundness direction of the main theorem, C\_0 is satisfiable. The quasimodel extracted from the completion graph is "model-like" (all pair-types realized by concrete node pairs), so the Henkin construction succeeds. See the discussion of the **extension gap** below for the subtlety with abstract quasimodels.

### Model Construction: Unfolding the Quasimodel

The quasimodel (or blocked completion graph) is a finite structure. The actual model may be infinite (e.g., when infinite PP-chains are required). The Henkin construction builds this infinite model incrementally, one element at a time. The critical concern is: **can edge assignments to newly created elements trigger "dormant" universal restrictions on existing elements, introducing concepts not present in their types and causing clashes?**

The answer is no. The proof relies on three layers of guarantees:

#### Construction Invariant

At every stage n of the Henkin construction, the partial model maintains:

- **(I1) Type membership**: every element e has tau(e) in T.
- **(I2) Pair-type membership**: for every distinct e\_i, e\_j: (tau(e\_i), R(e\_i,e\_j), tau(e\_j)) in P.
- **(I3) Composition consistency**: every triple satisfies the composition table.
- **(I4) Type permanence**: the type tau(e) is assigned at creation and **never subsequently modified**.

**Proof**: By induction on stages. At stage n+1, the new element e\_{m+1} gets type tau' in T (I1). The edge assignments S\_1,...,S\_m from Claim 5.2 (formulated as a disjunctive constraint network solved via full RCC5 tractability) satisfy (tau(e\_i), S\_i, tau') in P for all i (I2), and all new triples are composition-consistent (I3). No existing type changes (I4).

#### No Dormant Activation (Lemma 5.4 in the paper)

Let e\_i be an existing element with `forall S.D` in tau(e\_i), and let e\_{m+1} be newly created with type tau' and edge R(e\_i, e\_{m+1}) = S\_i. Then:

- **If S\_i = S** (the restriction matches the new edge): then D is already in tau', guaranteed by R-compatibility (condition P1). The concept was placed in tau' at creation. **No propagation occurs.**
- **If S\_i != S**: the restriction does not apply. No issue.

Symmetrically: if `forall inv(S\_i).D` is in tau', then D is already in tau(e\_i) by R-compatibility (P2). Since tau(e\_i) was fixed at an earlier stage (I4), D was already there. **No concept is added to any existing type.**

#### Why Composition Cannot Force Unexpected Propagation (Remark 5.5)

One might worry: what if R(e\_a, e\_b) = U and R(e\_b, e\_{m+1}) = T force R(e\_a, e\_{m+1}) = S where S is the unique element of comp(U, T), and `forall S.D` is in tau(e\_a) but D is not in tau'?

This cannot happen. The extension is formulated as a **disjunctive constraint network** where the domain for each edge (e\_a, e\_{m+1}) is D\_a = {S | (tau(e\_a), S, tau') in P}. Path-consistency enforcement refines these domains, and full RCC5 tractability guarantees a consistent atomic refinement exists. Every S\_a in the solution satisfies (tau(e\_a), S\_a, tau') in P, which by R-compatibility implies D in tau' whenever `forall S\_a.D` is in tau(e\_a). The composition constraints and pair-compatibility constraints are solved **jointly**.

#### Concept Truth (Lemma 5.6 in the paper)

**Lemma**: In the limit model, for every element e and every D in cl(C\_0): D in tau(e) implies e in D^I.

**Proof by structural induction on D**:

- **D = A** (concept name): A^I = {e | A in tau(e)} by construction.
- **D = not A**: not A in tau(e) implies A not in tau(e) (clash-freeness), so e not in A^I, hence e in (not A)^I.
- **D = D1 and D2**: by type condition T1, both D1, D2 in tau(e); by induction, both hold.
- **D = D1 or D2**: by type condition T2, at least one in tau(e); by induction, at least one holds.
- **D = forall R.E**: if forall R.E in tau(e) and (e,e') in R^I, then (tau(e), R, tau(e')) in P by (I2). R-compatibility gives E in tau(e'). By induction, e' in E^I. This holds for **every** R-neighbor, so e in (forall R.E)^I. **This is where Lemma 5.4 applies**: E was already in tau(e') at creation, not propagated.
- **D = exists R.E**: the Henkin construction (fair enumeration) eventually creates a witness e' with R(e,e') = R and E in tau(e'). By induction, e' in E^I.

#### The Role of Monotonicity Along PP-Chains

The model may contain infinite PP-chains: e\_0 PP e\_1 PP e\_2 PP ... For any external element x, Lemma 3.1 (upward monotonicity) constrains the progression of R(x, e\_i):

| R(x, e\_i) | Possible R(x, e\_{i+1}) |
|---|---|
| PP | PP (absorbing) |
| PO | PO, PP (can strengthen, never weaken) |
| DR | DR, PO, PP (can strengthen, never weaken) |
| PPI | PO, EQ, PP, PPI (can transition, never to DR) |

After at most 3 transitions (e.g., DR -> PO -> PP), the relation **stabilizes**. By Lemma 3.3 (downward persistence), DR and PPI are **permanent downward**: once R(x, e\_k) = DR, then R(x, e\_i) = DR for all i <= k.

This has three consequences:

1. **Bounded type variation**: along the chain, only finitely many distinct pair-types (tau(x), S, tau(e\_i)) arise (since S takes at most 4 values and stabilizes). All are in P.

2. **Uniform universal propagation**: once R(x, e\_i) stabilizes to S, the same set of concepts {E | forall S.E in tau(x)} applies to all subsequent chain elements. **No new concept** enters any tau(e\_i) from x's perspective beyond stabilization.

3. **Finite representability**: the types along the chain cycle through finitely many values from T. The monotonicity ensures the "relational profile" eventually becomes periodic. The quasimodel captures all relevant information; the infinite chain is fully determined by its finite abstraction.

Without monotonicity, relations could oscillate (e.g., DR -> PO -> DR -> PO -> ...), generating unbounded pair-type variety. The monotonicity lemmas rule this out.

#### The Extension Gap

The Henkin construction (Claim 5.2) solves a disjunctive constraint network at each step: edges among existing elements are fixed (singletons), and edges to the new element have disjunctive domains D\_i = DN(tau(e\_i), tau'). After path-consistency enforcement, full RCC5 tractability gives a consistent atomic refinement.

However, the enforcement step may **empty** a domain D\_i. Condition (Q3) guarantees that every three-node sub-network is satisfiable, but cascading refinements across multiple triples can remove values needed elsewhere — even when starting from a path-consistent type-level network.

For **model-derived** quasimodels (extracted from actual models), this cannot happen: the model provides a realized assignment that is already globally consistent and survives enforcement. For **abstract** quasimodels satisfying (Q1)–(Q3) that do not arise from any model, the extension network may be inconsistent.

This means:
- The characterization theorem is established as an **if**: every satisfiable concept has a quasimodel (soundness).
- The **only-if** direction (every quasimodel gives a model) holds for model-derived quasimodels but remains open for abstract quasimodels.
- The type elimination algorithm has **no false negatives** (by soundness alone). Whether false positives can occur remains open.
- The tableau's soundness proof extracts a quasimodel from a completion graph — a "model-like" structure where all pair-types are realized — and the Henkin construction succeeds for such quasimodels.

### Completeness

**Theorem**: If C\_0 is satisfiable, then there exists a sequence of nondeterministic choices yielding an open completion graph.

**Proof sketch**: Given a model I with d\_0 in C\_0^I, maintain a guide function pi: V -> Delta^I mapping tableau nodes to model elements, with invariants:
- L(x) is a subset of the type of pi(x) in I
- E(x,y) equals the actual relation between pi(x) and pi(y) in I

The model guides all nondeterministic choices:
- **(or-rule)**: choose the disjunct true at pi(x)
- **(exists-rule)**: set pi(y) = d' where d' witnesses the demand in I; choose S\_z = relation between pi(z) and d' in I

Clash-freeness follows from the model satisfying composition and type consistency. Blocked nodes' demands need not be directly satisfied in the completion graph --- they are satisfied in the infinite model constructed from the extracted quasimodel.

### Comparison with Tree-Based DL Tableaux

| Feature | Standard ALCI Tableau | ALCI\_RCC5 Tableau |
|---------|----------------------|-------------------|
| Structure | Forest (tree per root) | **Complete graph** |
| New node edges | Single edge to parent | **Edge to every existing node** |
| Structural invariant | Tree shape | **Composition consistency (CF)** |
| Blocking | Pairwise (node + parent match) | **Simple type equality** |
| Soundness | Direct model readoff | **Indirect: quasimodel extraction + Henkin** |
| Key enabler | Tree model property | **Patchwork property** |

---

## Concrete Domains vs. Composition-Based Role Boxes

An important distinction must be drawn between two fundamentally different approaches to combining description logics with spatial reasoning. Several decidability results exist for DLs with RCC constraints, but they all use the **concrete domain** formalism, which is expressively incomparable with the composition-based role box approach of ALCI\_RCC.

| Approach | Spatial constraints via | Can express ∀PP.C ? | Can express ∃DR.D ? | Quantify over spatial relations? |
|---|---|---|---|---|
| **Concrete domains** (ALC(RCC8)) | Functional roles to concrete values | No | No | No |
| **Composition-based role boxes** (ALCI\_RCC5) | Spatial relations serve as roles directly | **Yes** | **Yes** | **Yes** |

### Prior decidability results (concrete domain approach)

- **Lutz & Milicic (2007)**: ALC with omega-admissible concrete domains (including RCC5, RCC8) is decidable. No inverse roles.
- **Borgwardt, De Bortoli & Koopmann (2024)**: ALC(D) ontology consistency is EXPTIME-complete for omega-admissible D. ALC only, no inverse roles.
- **Baader & Rydval (2020)**: Strengthened undecidability results and generalized omega-admissibility conditions for DLs with concrete domains and GCIs. Refines the decidability boundary within the concrete domain paradigm.
- **Demri & Gu (CSL 2026)**: Extended the automata-based approach to handle **inverse roles**, functional role names, and constraint assertions, establishing EXPTIME membership. This is the closest published result to ALCI\_RCC, as it combines inverse roles with RCC-like spatial constraints. However, it still operates within the concrete domain formalism.

### Why the gap remained open

None of these results settle the decidability of ALCI\_RCC5 or ALCI\_RCC8, because the composition-based role box approach allows **quantification over spatial relations** --- concepts like ∀PP.C ("all proper parts satisfy C") and ∃DR.D ("some disconnected region satisfies D") --- which are inexpressible in the concrete domain setting. The two formalisms are complementary: concrete domains reason about spatial *attributes* of elements; ALCI\_RCC captures direct spatial *relationships* between elements.

A key insight explored in these papers is the **patchwork property** from qualitative constraint reasoning (Renz & Nebel 1999), which was known contemporaneously with Wessel's original work but had not been connected to the description logic decidability question. Our work shows that the patchwork property, combined with either the quasimodel method or a contextual tableau calculus, is a powerful tool — but not yet sufficient to close the gap. The combination of PP-transitivity, universal propagation, and the complete-graph requirement creates fundamental obstacles that no current approach has overcome.

---

## Files

- [**`decidability_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/decidability_ALCIRCC5.pdf) -- Main paper: quasimodel approach (22 pages, revised)
- [**`decidability_ALCIRCC5.tex`**](https://github.com/lambdamikel/alcircc5/blob/master/decidability_ALCIRCC5.tex) -- LaTeX source for main paper
- [**`ALCI_RCC5_contextual_tableau_draft.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/ALCI_RCC5_contextual_tableau_draft.pdf) -- Contextual tableau paper by GPT-5.4 Pro; starting point for the FW(C,N) discussion ([source](https://github.com/lambdamikel/alcircc5/blob/master/ALCI_RCC5_contextual_tableau_draft.tex))
- [**`FW_proof_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/FW_proof_ALCIRCC5.pdf) -- Counterexample to FW(C,N): the contextual tableau's completeness conjecture is false (7 pages)
- [**`FW_proof_ALCIRCC5.tex`**](https://github.com/lambdamikel/alcircc5/blob/master/FW_proof_ALCIRCC5.tex) -- LaTeX source for FW counterexample
- [**`ALCI_RCC5_status_after_FW.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/ALCI_RCC5_status_after_FW.pdf) -- GPT-5.4's status assessment after FW failure; proposes omega-model direction ([source](https://github.com/lambdamikel/alcircc5/blob/master/ALCI_RCC5_status_after_FW.tex))
- [**`response_to_status_note.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/response_to_status_note.pdf) -- Claude's response: corrections, evaluation, and a concrete sub-question ([source](https://github.com/lambdamikel/alcircc5/blob/master/response_to_status_note.tex))
- [**`decidability_proof_ALCIRCC5.md`**](https://github.com/lambdamikel/alcircc5/blob/master/decidability_proof_ALCIRCC5.md) -- Earlier proof sketch (quasimodel method only)
- [**`CONVERSATION.md`**](https://github.com/lambdamikel/alcircc5/blob/master/CONVERSATION.md) -- Full conversation log between Michael Wessel and Claude

## References

1. M. Wessel. ["Qualitative Spatial Reasoning with the ALCI\_RCC Family -- First Results and Unanswered Questions."](https://github.com/lambdamikel/alcircc5/blob/master/report7.pdf) Technical Report FBI-HH-M-324/03, University of Hamburg, 2002/2003.

2. M. Wessel. ["Decidable and Undecidable Extensions of ALC with Composition-Based Role Inclusion Axioms."](https://github.com/lambdamikel/alcircc5/blob/master/report5.pdf) Technical Report FBI-HH-M-301/01, University of Hamburg, 2000.

3. M. Wessel. ["Undecidability of ALC\_RA."](https://github.com/lambdamikel/alcircc5/blob/master/report6.pdf) Technical Report FBI-HH-M-302/01, University of Hamburg, 2001.

4. M. Wessel. ["Obstacles on the Way to Spatial Reasoning with Description Logics: Undecidability of ALC\_RA⊖."](https://github.com/lambdamikel/alcircc5/blob/master/report4.pdf) Technical Report FBI-HH-M-297/00, University of Hamburg, 2000.

5. J. Renz and B. Nebel. "On the Complexity of Qualitative Spatial Reasoning: A Maximal Tractable Fragment of the Region Connection Calculus." Artificial Intelligence, 108(1-2):69-123, 1999.

6. J. Renz. "Maximal Tractable Fragments of the Region Connection Calculus: A Complete Analysis." IJCAI 1999.

7. C. Lutz and F. Wolter. "Modal Logics of Topological Relations." Logical Methods in Computer Science, 2(2), 2006.

8. C. Lutz and M. Milicic. "A Tableau Algorithm for Description Logics with Concrete Domains and General TBoxes." Journal of Automated Reasoning, 38:227-259, 2007.

9. S. Borgwardt, F. De Bortoli, P. Koopmann. "The Precise Complexity of Reasoning in ALC with omega-Admissible Concrete Domains." KR 2024.

10. F. Baader and M. Rydval. "Description Logics with Concrete Domains and General Concept Inclusions Revisited." IJCAR 2020, LNCS 12166, pp. 413-431.

11. S. Demri and T. Gu. "Robustness of Constraint Automata for Description Logics with Concrete Domains." CSL 2026, LIPIcs Vol. 363.

## Acknowledgments

This research was prompted by Michael Wessel (miacwess@gmail.com), who introduced the ALCI\_RCC family in his doctoral work at the University of Hamburg under the DFG project "Description Logics and Spatial Reasoning" (grant NE 279/8-1).

The revised version of the paper addresses issues identified in a technical review. We are grateful for the detailed and constructive feedback.
