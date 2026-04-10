# Outdated and Superseded Material

This file contains detailed documentation of approaches and investigations that have been **disproved, retracted, or superseded** by later work. They are preserved here for reference and transparency. See [README.md](README.md) for the current status and active approaches.

---

## A Tableau Calculus for ALCI\_RCC5 (Original, Now Superseded)

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

### Soundness (NOT ESTABLISHED)

**Claimed theorem**: If the tableau produces an open completion graph for C\_0, then C\_0 is satisfiable.

**Status: NOT PROVEN.** The proof sketch below extracts a quasimodel and invokes the Henkin construction, which has the **extension gap** (see below). The quasimodel extraction is correct, but converting the quasimodel to an actual model requires solving a disjunctive constraint network at each Henkin step, and global solvability is not guaranteed (1,911 counterexamples at m=3).

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

#### Computational investigation of the extension gap

A suite of exhaustive checkers (`extension_gap_checker.py`, `extension_gap_checker_v2.py`, `q3_implies_q3s_check.py`, `model_derived_q3s_fast.py`) systematically tests the extension gap over all small RCC5 configurations. The checkers encode the full RCC5 composition table for the 4 base relations {DR, PO, PP, PPI} (EQ excluded for distinct elements) and enumerate all composition-consistent atomic networks, domain assignments, and type-assignment models.

**Result 1: Q3 (existential) is insufficient.** The extension CSP (arc-consistency enforcement) empties domains for Q3-satisfying configurations. Failures grow rapidly:

| Existing elements m | Configurations tested | Failures (Q3 passes, AC empties domain) |
|---|---|---|
| 2 | 960 | 61 |
| 3 | 319,200 | 1,575 |
| 4 | 21,547,500 | 806,094 |

**Result 2: Q3s (strong/universal) eliminates ALL failures.** Q3s requires: for all R₁₂ ∈ DN(τ₁,τ₂) and **all** R₁₃ ∈ DN(τ₁,τ₃), there exists R₂₃ ∈ DN(τ₂,τ₃) with R₁₃ ∈ comp(R₁₂, R₂₃). This is equivalent to arc-consistency of the extension CSP. Computationally verified: **zero** failures through m=4 (21.5 million configurations).

**Result 3: Q3s is genuinely not extractable from models.** The "representative mismatch" problem identified in the paper's Remark after Q3 is confirmed by exhaustive search. Model-derived DN networks (extracted from concrete, composition-consistent RCC5 models with type assignments) can violate Q3s:

| Model elements | Models tested | Models where DN violates Q3s |
|---|---|---|
| 3 | 492 | 0 |
| 4 | 68,276 | 7,560 (11.1%) |

Violations require ≥ 2 elements of the same type with different relational profiles. Concrete counterexample: 4 elements d₁(A), d₁'(A), d₂(B), d₃(C) with relations d₁-d₂=PP, d₁-d₃=PP, d₁'-d₂=DR, d₁'-d₃=DR, d₂-d₃=PP, d₁-d₁'=DR. The model is composition-consistent, but DN(A,B)={PP,DR}, DN(A,C)={PP,DR}, DN(B,C)={PP}, and Q3s fails: for R₁₂=PP and R₁₃=DR, comp(PP,PP)={PP} which does not contain DR.

**Summary:**

| Property | Sufficient for extension? | Extractable from models? |
|---|---|---|
| Q3 (existential) | **No** (1,575 failures at m=3) | **Yes** |
| Q3s (strong/universal) | **Yes** (0 failures through m=4) | **No** (7,560 model-derived violations) |

The extension gap is **genuine and unavoidable** within the quasimodel framework as formulated. No condition on the DN sets is simultaneously sufficient for the Henkin construction and extractable from models. Moreover, the type elimination algorithm is **unsound** even before the extension gap is reached — see the next section.

#### Computational discovery: the type elimination algorithm is unsound (rejects satisfiable concepts)

A systematic computational investigation ([`extension_gap_concrete.py`](https://github.com/lambdamikel/alcircc5/blob/master/extension_gap_concrete.py)) reveals that the type elimination algorithm described in Section 6 of the paper is **unsound** — it can reject satisfiable concepts (false negatives). This is a stronger result than the extension gap: the algorithm itself is broken, not just the Henkin construction.

**Concrete counterexample.** The concept

> C₁ = ∃PO.D ⊓ ∃DR.(B ⊓ ∀PO.¬D) ⊓ ∀DR.¬D ⊓ ∀PP.¬D ⊓ ∀PPI.¬D

is satisfiable with 3 elements:

| Element | Atoms | Role to e₀ | Role to e₁ | Role to e₂ |
|---|---|---|---|---|
| e₀ (root) | ∅ | — | DR | PO |
| e₁ (B-filler) | {B} | DR | — | DR |
| e₂ (D-element) | {D} | PO | DR | — |

Composition consistency verified for all 6 directed triples. C₁ satisfaction at e₀ verified. Yet the type elimination algorithm rejects C₁: **0 types survive** from the initial 128.

**Root cause: Q2 + Q3 cascade elimination.** The algorithm starts with all 128 valid Hintikka types for cl(C₁) and applies three conditions:
- **(Q1)** existential witnesses — every ∃R.D in a type has a witness type reachable via R
- **(Q2)** completeness — every pair of distinct types in the surviving set has non-empty DN
- **(Q3)** algebraic closure — every triple of types has a composition-consistent extension

The cascade:
1. **Q3 is anti-monotone in T**: the condition "for EVERY τ₃ ∈ T" becomes harder to satisfy as T grows. Starting with 128 types, Q3 aggressively prunes DN entries because many type pairs have incompatible ∀-constraints (e.g., types with D and ∀DR.¬D have DN=∅ with other D-types).
2. **Q3 kills valid pairs**: the model pair (τ₀, DR, τ₁) is pruned because some type τ₃ ∉ {τ₀,τ₁,τ₂} has DN(τ₁,τ₃)=∅, failing Q3's universal requirement.
3. **Q1 cascades**: types that lose their Q1 witnesses (due to Q3 pruning DN entries) are eliminated.
4. **Q2 cascades**: types eliminated by Q1 cause Q2 failures for types that depended on them.
5. **Result**: the greatest fixpoint converges to the empty set.

**The model types form a valid quasimodel among themselves.** When the type elimination is restricted to just the 3 model-extracted types {τ₀, τ₁, τ₂} with compatible DN:

| Pair | DN |
|---|---|
| DN(τ₀, τ₁) | {DR, PO, PPI} (after Q3 prunes PP) |
| DN(τ₀, τ₂) | {PO} |
| DN(τ₁, τ₂) | {DR} |

All conditions pass: Q1 ✓ (witnesses exist), Q2 ✓ (all pairs non-empty), Q3 ✓ (pairwise-distinct triples consistent). **The algorithm cannot find this valid subset because the greatest fixpoint approach starts with all types and Q3's anti-monotonicity poisons the elimination.**

**The fundamental algorithmic flaw.** For standard ALCI (without spatial constraints), type elimination uses only Q1 (existential witnesses). Q1 is anti-monotone (removing types hurts Q1), so the greatest fixpoint correctly finds the largest self-sustaining type set. For ALCI\_RCC5, Q3 adds a cross-cutting condition: larger T makes Q3 harder (more types to satisfy universally), but Q1 still needs more types for witnesses. These opposing forces make the greatest fixpoint approach incorrect:

- A valid quasimodel S ⊆ Tp(C₀) exists (the model types)
- S satisfies Q1+Q2+Q3 internally
- But the greatest fixpoint starting from Tp(C₀) ⊋ S eliminates all of S
- Because Q3 with types from Tp(C₀) \ S kills DN entries needed by S

A correct algorithm would need **subset search** (find S ⊆ Tp(C₀) where Q1+Q2+Q3 hold internally), which is computationally harder than greatest-fixpoint elimination and unlikely to be EXPTIME.

**Additional bug: Q3 soundness proof (lines 882-888 of the paper).** The proof of Q3 for the case τ₂ = τ₃ with a unique element uses R₂₃ = EQ, asserting that comp(R₁₂, EQ) = {R₁₂}. But DN is defined over NR \ {EQ}, so EQ ∉ DN(τ₂, τ₂). The proof silently places EQ in DN, contradicting the definition. This means the soundness direction (model → quasimodel) also has a gap for Q3 with "not necessarily distinct" types when a type has singleton multiplicity.

**Computational verification** ([`extension_gap_concrete.py`](https://github.com/lambdamikel/alcircc5/blob/master/extension_gap_concrete.py), [`quasimodel_debug.py`](https://github.com/lambdamikel/alcircc5/blob/master/quasimodel_debug.py)):

| Test | Result |
|---|---|
| Model validity (3 elements, composition consistency) | ✓ All 6 triples consistent |
| C₁ satisfaction at e₀ | ✓ |
| Q1-only elimination (128 types, no Q2/Q3) | 128 types survive, 4 root types |
| Q1+Q2 elimination (no Q3) | 0 types survive (Q2 cascade) |
| Q1+Q2+Q3 elimination (paper's algorithm) | 0 types survive |
| Model types only, Q1+Q2+Q3 (restricted) | **3 types survive, 1 root type** ✓ |

#### Earlier implications (extension gap only)

The extension gap results (prior to the type elimination unsoundness discovery) showed:
- The characterization theorem is established as an **if**: every satisfiable concept has a quasimodel (soundness — modulo the Q3 bug for singleton-multiplicity types).
- The **only-if** direction (every quasimodel gives a model) holds for model-derived quasimodels but remains open for abstract quasimodels.
- The tableau's soundness proof extracts a quasimodel from a completion graph — a "model-like" structure where all pair-types are realized — but the subsequent Henkin construction has the extension gap (global solvability of the disjunctive constraint network is not guaranteed).

#### Possible paths forward

1. **Strategic Henkin construction**: instead of proving the extension CSP is always solvable, show that with careful ordering of element creation and relation assignment, unsolvable CSPs can always be avoided. This would be a game-theoretic argument.
2. **Model saturation**: enrich the type system so that every element realizes all pair-types of its type (condition "Q4"), making Q3s extractable at the cost of (doubly) exponentially more types.
3. **Compactness + patchwork**: argue model existence without explicit construction, using the fact that every finite sub-problem of the Henkin construction is satisfiable.
4. **Alternative proof architecture**: the contextual tableau approach (GPT-5.4) avoids the extension gap entirely, with the gap on the other side (completeness/extraction).

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

## Intricacies of blocking in complete-graph semantics

In standard DL tableaux with tree-shaped models, blocking is straightforward: a blocked node x has the same type as an earlier node y, and unraveling works because the only connection between a subtree and the rest of the model is the single parent edge. In ALCI\_RCC5, the model is a complete graph — every element is related to every other — and this fundamentally changes the blocking/unraveling dynamic.

**The naive expectation.** If x is blocked by y (same concept label), no new ∀-qualifications fire at x, and all triangles in the completion graph are already consistent. One might expect that copying y's witness structure for x produces only triangles already observed — so unraveling should succeed without introducing new triangle types.

**Where this breaks down: a concrete trace.** Consider a PP-chain with alternating types:

d₀(τ\_A) PP d₁(τ\_B) PP d₂(τ\_A) PP d₃(τ\_B) PP d₄(τ\_A) PP ...

where ∃PO.A ∈ τ\_A and ∀PO.¬A ∈ τ\_B.

d₀ needs a PO-witness w₀ for ∃PO.A: ρ(d₀, w₀) = PO, A ∈ tp(w₀).

**Can d₂ reuse w₀?** Trace composition forward:

- ρ(d₁, w₀) ∈ comp(PPI, PO) = {PO, PPI}. But ∀PO.¬A ∈ τ\_B and A ∈ tp(w₀) exclude PO. So **ρ(d₁, w₀) = PPI**.
- ρ(d₂, w₀) ∈ comp(PPI, PPI) = {PPI}. So **ρ(d₂, w₀) = PPI**.

Since ρ(d₂, w₀) = PPI ≠ PO, w₀ does not satisfy d₂'s ∃PO.A demand.

**w₁ must exist as d₂'s PO-witness.** ρ(d₂, w₁) = PO, A ∈ tp(w₁). Its relations:

Forward from d₂:
- ρ(d₃, w₁) ∈ comp(PPI, PO) = {PO, PPI}. ∀PO.¬A excludes PO → **ρ(d₃, w₁) = PPI**.
- ρ(d₄, w₁) ∈ comp(PPI, PPI) = {PPI}. **PPI forever after.**

Backward from d₂:
- ρ(d₁, w₁) ∈ comp(PP, PO) = {DR, PO, PP}. ∀PO.¬A excludes PO → **ρ(d₁, w₁) ∈ {DR, PP}**.
- Taking DR: ρ(d₀, w₁) ∈ comp(PP, DR) = {DR} → **ρ(d₀, w₁) = DR**.

Similarly, **w₂ is d₄'s PO-witness** (same pattern shifted by 2), and so on. The full relation table:

| | w₀ | w₁ | w₂ |
|---|---|---|---|
| d₀ | **PO** | DR | DR |
| d₁ | PPI | DR | DR |
| d₂ | PPI | **PO** | DR |
| d₃ | PPI | PPI | DR |
| d₄ | PPI | PPI | **PO** |
| d₅ | PPI | PPI | PPI |

Each wₖ is PO to exactly one chain element (d₂ₖ), DR to all earlier ones, and PPI to all later ones. Every ∀PO.¬A at τ\_B positions is vacuously satisfied — no element is PO to any τ\_B position.

**What happens in the tableau with type-equality blocking.** The finite completion graph has d₀(τ\_A), d₁(τ\_B), d₂(τ\_A) — blocked by d₀. Witness w₀ exists with ρ(d₀, w₀) = PO. Composition forces ρ(d₂, w₀) = PPI.

During unraveling, we create w₀' (a copy of w₀) for d₂ with ρ(d₂, w₀') = PO (copying the demanded relation). Composition then forces:

- ρ(d₁, w₀') ∈ comp(PP, PO) = {DR, PO, PP}; ∀PO.¬A excludes PO → ρ(d₁, w₀') ∈ {DR, PP}
- ρ(d₀, w₀') ∈ {DR, PP} (not PO)

So d₀ is DR or PP to the copy w₀' — but in the completion graph, d₀ was PO to w₀. **The triangle (d₀, w₀', d₂) has a shape that may not appear in the finite completion graph**, because d₀ was never DR-related to a tp(w₀)-type node. This is a potentially new triangle type.

**The blocking dilemma.** This reveals a fundamental tension:

| Blocking condition | Termination | Unraveling |
|---|---|---|
| Type-equality (weak) | Always terminates | May produce new triangle types |
| Triangle-profile (strong) | May not terminate (PO-incoherent case) | Always locally correct |

This is the tableau-theoretic manifestation of the **PO gap** from the two-tier quotient paper.

---

## Observation: abstract triangle-type sets stabilize for interior nodes

The blocking dilemma above appears to force a choice between termination and correct unraveling. The abstract-triangle-type approach was motivated by a subtle observation: the non-termination argument uses **node-identity profiles** (which specific witnesses a node is related to), while the correctness argument only needs **abstract triangle-type sets** (which abstract relational patterns a node participates in). The abstract version stabilizes for **interior** chain nodes — but as the full implementation later revealed, **frontier nodes never stabilize** because they lack successor-edge triangles.

**The key distinction.** A node-identity profile records, for each pair of neighbors (b, c), the concrete identity of b and c together with the RCC5 relation. An abstract triangle type is a tuple (τ₁, R₁₂, τ₂, R₂₃, τ₃, R₁₃) — three Hintikka types and three pairwise RCC5 relations, with no node identities. The abstract triangle-type set of a node d is the set of all abstract triangle types that d participates in.

**Why node-identity profiles never match.** In the PO-incoherent chain, each τ\_A node d₂ₖ has a unique concrete relational context: PO to its own witness wₖ, DR to all earlier witnesses w₀,...,wₖ₋₁, and PPI to all later witnesses. Since k increases without bound, every d₂ₖ sees a different number of DR-related witnesses. The node-identity profile grows monotonically and never repeats.

**Why abstract triangle-type sets DO match.** The abstract triangle-type set strips away node identities and retains only the relational pattern. Even though d₄ is DR to {w₀, w₁} while d₆ is DR to {w₀, w₁, w₂}, both see the same *abstract patterns*: both participate in triangles of the form (τ\_A, DR, σ, DR, σ, PPI), (τ\_A, PO, σ, DR, τ\_B, PPI), etc. The additional concrete witness at d₆ contributes only triangle types that d₄ already has via its own witnesses.

**Computational verification** ([`triangle_type_saturation_check.py`](https://github.com/lambdamikel/alcircc5/blob/master/triangle_type_saturation_check.py)). The script builds the full PO-incoherent model (24-element PP-chain with 12 PO-witnesses), verifies composition consistency, and computes abstract triangle-type sets for every node. Results for the all-DR-backward branch:

| Node type | Stabilizes at | Interior range (all identical) | Set size |
|---|---|---|---|
| τ\_A | d₄ (k=2) | d₄ = d₆ = d₈ = d₁₀ = d₁₂ = d₁₄ = d₁₆ = d₁₈ | 68 types |
| τ\_B | d₅ (k=2) | d₅ = d₇ = d₉ = d₁₁ = d₁₃ = d₁₅ = d₁₇ = d₁₉ | 56 types |
| σ | w₂ (k=2) | w₂ = w₃ = w₄ = w₅ = w₆ = w₇ = w₈ = w₉ | 57 types |

The growth phase (d₀ → d₂ → d₄: 25 → 55 → 68 types for τ\_A) reflects the start boundary where early nodes have fewer backward neighbors. Nodes near the end of the finite model (d₂₀, d₂₂) have fewer types due to the end boundary — an artifact that would not exist in the infinite tableau construction. All interior nodes are **exactly identical**.

The same stabilization holds for the all-PP-backward branch (verified in the script). This is not branch-dependent.

**The full comparison matrix** (= means identical abstract triangle-type sets, numbers show symmetric-difference size):

```
τ_A:     d0    d2    d4    d6    d8   d10   d12   d14   d16   d18   d20   d22
  d0      ·    30    43    43    43    43    43    43    43    43    50    54
  d2     30     ·    13    13    13    13    13    13    13    13    20    48
  d4     43    13     ·     =     =     =     =     =     =     =     7    35
  d6     43    13     =     ·     =     =     =     =     =     =     7    35
  d8     43    13     =     =     ·     =     =     =     =     =     7    35
  ...    ...   ...    =     =     =     =     =     =     =     =    ...   ...
  d18    43    13     =     =     =     =     =     =     =     ·     7    35
```

**Why stabilization occurs.** The abstract triangle-type set of a node depends on the menu of Hintikka types and RCC5 relations available among its neighbors — not on the number of neighbors of each kind. Once d₄ has at least one predecessor of each relevant type at each relevant relation (PPI to τ\_B, DR to σ, PPI to σ, etc.) and at least one successor of each relevant type at each relevant relation, its abstract triangle-type menu is complete. Additional predecessors or successors of the same abstract kind contribute no new triangle types. The transient phase (d₀ through d₂) simply reflects the time needed for the backward neighborhood to include all relevant abstract patterns.

**Implication for the blocking dilemma.** The interior-node stabilization suggests that abstract-triangle-type matching is the right level of abstraction for correct unraveling. However, a full implementation ([`triangle_calculus.py`](https://github.com/lambdamikel/alcircc5/blob/master/triangle_calculus.py)) revealed that **stabilization of interior nodes is insufficient for termination**: frontier nodes (chain endpoints without successors) always have a strictly smaller Tri (|Tri|=8 vs 16), so they are never blocked. The blocking dilemma remains open:

| Blocking condition | Terminates? | Correct unraveling? |
|---|---|---|
| Type-equality (LL only) | Yes | Not always (novel triangles risk) |
| LL + Tri | **No** (frontier advancement) | Yes |
| LL + Tri + TNbr | **No** (frontier advancement) | Yes |

Any blocking condition using Tri inherits the frontier problem. Resolving the dilemma requires a mechanism that handles the PP/PPI asymmetry at chain endpoints (see conjectured directions in the [tableau paper](https://github.com/lambdamikel/alcircc5/blob/master/tableau_ALCIRCC5.pdf), Section 7.1).

**Strengthened condition: Tri-neighborhood equivalence.** Michael Wessel proposed strengthening the blocking condition to require not only Tri(x) = Tri(y), but also that for each (relation, type) pair, the *set of Tri-values among neighbors* matches:

> For each pair-type (L(x), R, τ), {Tri(b) : E(x,b)=R, L(b)=τ} = {Tri(b') : E(y,b')=R, L(b')=τ}

This ensures the copy is faithful not just from x/y's perspective but from **every neighbor's perspective**. Computational verification ([`tri_neighborhood_check.py`](https://github.com/lambdamikel/alcircc5/blob/master/tri_neighborhood_check.py)) confirms this stronger condition also stabilizes, at a slightly later point:

| Node type | Basic Tri stabilizes | Tri-nbr stabilizes |
|---|---|---|
| τ\_A | d₄ (k=2) | **d₆ (k=3)** |
| τ\_B | d₅ (k=2) | **d₇ (k=3)** |
| σ | w₂ (k=2) | **w₃ (k=3)** |

The one-step delay occurs because d₄'s PPI-neighbors include boundary nodes (d₂, w₁) with different Tri sets than the corresponding PPI-neighbors of d₆ (which are all interior). Once all neighbors are also in the stabilized interior (at d₆), full Tri-neighborhood equivalence holds. The comparison matrix shows the pattern clearly (= means full Tri-nbr equivalence, T means Tri-only match):

```
τ_A:     d4    d6    d8   d10   d12   d14   d16   d18
  d4      ·     T     T     T     T     T     T     T
  d6      T     ·     =     =     =     =     =     T
  d8      T     =     ·     =     =     =     =     T
  ...     T     =     =     =     =     =     =     T
  d16     T     =     =     =     =     =     ·     T
  d18     T     T     T     T     T     T     T     ·
```

The strengthened condition makes the soundness proof (specifically the T-closure argument in Lemma 5.5) substantially more robust: triangles are guaranteed to be in T from **every participating node's perspective**, not just the blocked/blocker pair. This directly addresses scrutiny point 1 (intra-subtree T-closure) from the tableau paper.

---

## Eighth approach: Tri-neighborhood tableau — TERMINATION DISPROVED

Building on the saturation finding above, a complete tableau calculus with Tri-neighborhood blocking is presented in [**A Tableau Calculus for ALCI\_RCC5 with Tri-Neighborhood Blocking (PDF)**](https://github.com/lambdamikel/alcircc5/blob/master/tableau_ALCIRCC5.pdf) (16 pages, third revision, two rounds of GPT-5.4 Pro review).

**The blocking condition.** A node x is blocked by an earlier node y when three conditions hold: (i) L(x) = L(y) (same concept label), (ii) Tri(x) = Tri(y) (same abstract triangle-type set), and (iii) TNbr(x) = TNbr(y) (same Tri-neighborhood signature — for each (relation R, type τ) pair, the set of Tri-values among R-neighbors of type τ matches). This is strictly between type-equality blocking (condition (i) alone) and node-identity profile blocking (which requires matching concrete relational contexts). Condition (ii) ensures first-person perspective equivalence; condition (iii) ensures third-person perspective equivalence.

**The proof structure:**
- **Termination** (Theorem 4.1): **FALSE.** A [full implementation](https://github.com/lambdamikel/alcircc5/blob/master/triangle_calculus.py) demonstrates non-termination on `A ⊓ ∃PP.A ⊓ ∀PP.(∃PP.A ⊓ ∃DR.B)` via frontier advancement. 18/20 test concepts show non-termination. The local per-node bounds (bounded branching, permanent demand satisfaction, monotone Tri-growth) are individually correct but insufficient.
- **Soundness** (Theorem 5.8): **NOT FULLY PROVEN.** The model construction goes via tree unraveling + triangle-type-filtered disjunctive constraint network. The critical step is Lemma 5.5 (non-empty domains after T-filtering and arc-consistency), which the paper's own honest assessment (Section 7.2, item 1) acknowledges is "supported by computational verification on completion graphs of size 8, 10, and 12, but not by a general formal argument." This is structurally the same issue as the extension gap: a disjunctive constraint network must be shown solvable. The mechanism differs (triangle-type filtering rather than Henkin/Q3), and the computational evidence is stronger (zero failures found), but a complete formal proof is missing.
- **Completeness** (Theorem 6.1): **Valid.** A model guides all nondeterministic choices, maintaining invariants that the labels are subsets of model types and edges match model relations.

**The mirror triangle issue and its resolution.** An earlier version of the soundness proof used a map-based assignment ρ(d₁,d₂) = E(map(d₁), map(d₂)). Computational investigation ([`intra_subtree_tclosure_check.py`](https://github.com/lambdamikel/alcircc5/blob/master/intra_subtree_tclosure_check.py)) revealed that this assignment is NOT T-closed: when two elements both map to the same node (a "same-map pair"), they both carry the same PO relation to a shared witness, creating "mirror triangles" like (τ\_A, R, τ\_A, PO, σ, PO) that never appear in T(G) — because each σ witness is PO to exactly one τ\_A node. An earlier revision fixes this by working with disjunctive domains throughout: the constraint network's arc-consistency step removes the problematic PO from cross-subtree edges and replaces it with DR or PPI (which are type-safe alternatives from P(G)). Computational verification confirms all domains remain non-empty for completion graphs of size 8, 10, and 12.

**Honest assessment.** The paper identifies four specific points:
1. **Intra-subtree T-closure (Lemma 5.5)**: **Formal gap.** The proof that arc-consistency preserves non-empty domains is supported by computational verification on completion graphs of size 8, 10, and 12, but not by a general formal argument.
2. **Initial domains for same-map pairs**: GPT's [second review](https://github.com/lambdamikel/alcircc5/blob/master/review6/response_to_tableau_ALCIRCC5_second_revision.pdf) identified that the P(G)-only domain is empty when two unraveling elements both map to the sole node of a given type. Fixed by extending D₀ with Safe(τ₁,τ₂). The degenerate case Safe(τ,τ)=∅ is handled by identifying same-map copies.
3. **Termination**: **Disproved.** The concept `A ⊓ ∃PP.A ⊓ ∀PP.(∃PP.A ⊓ ∃DR.B)` causes unbounded node creation. The mechanism is frontier advancement, not oscillation: the frontier node's Tri is always strictly smaller than interior nodes' Tri (|Tri|=8 vs 16) because it lacks PP-successor triangles. Two reviewers correctly predicted this gap.
4. **Stabilization depth**: The earlier computational evidence remains correct for interior nodes. The issue is that frontier nodes never stabilize before their ∃-demands fire.

**Complexity.** Since the calculus does not terminate, complexity analysis is moot. A terminating variant would need separate analysis.

---

## The alternating-type trick: ALCI\_RCC8 may be structurally stronger than ALCI\_RCC5

In RCC5, PP is a single undifferentiated "proper part" relation — there is no way to distinguish immediate from non-immediate successors on a PP-chain. In RCC8, PP splits into **TPP** (tangential proper part) and **NTPP** (non-tangential proper part), and concept-level constraints can force TPP to act as an **immediate-successor relation**.

**The trick.** Consider a TPP-chain x₀ TPP x₁ TPP x₂ TPP ... with alternating concepts A, B (where A ⊓ B ⊑ ⊥):

- x₀ satisfies A ⊓ ∀TPP.B
- x₁ satisfies B ⊓ ∀TPP.A
- x₂ satisfies A ⊓ ∀TPP.B, ...

Now suppose TPP(x₀, x₂). Then x₂ must satisfy B (from x₀'s ∀TPP.B). But x₂ satisfies A, and A ⊓ B = ⊥. Contradiction. So **NTPP(x₀, x₂) is forced**. This makes TPP effectively functional on the chain.

**Consequence.** This observation suggests that **ALCI\_RCC5 and ALCI\_RCC8 may have different decidability status**.

---

## The two-chain construction: a 2×∞ ladder with functional operators

The alternating-type trick gives one functional chain (TPP as immediate successor). For undecidability reductions, we typically need **two dimensions**. A natural construction uses two parallel TPP-chains connected by PO rungs.

```
Chain A:  a₀ —TPP→ a₁ —TPP→ a₂ —TPP→ a₃ —TPP→ ...
           |         |         |         |
          PO        PO        PO        PO
           |         |         |         |
Chain B:  b₀ —TPP→ b₁ —TPP→ b₂ —TPP→ b₃ —TPP→ ...
```

This gives two functional "axes" (∀TPP = horizontal, ∀PO = vertical in the ladder) plus a broadcast channel (∀NTPP = "all future"). Counter encoding works on each chain independently but cross-chain synchronization fails without counting.

## PCP encoding attempt on the two-chain structure

The **Post Correspondence Problem** (PCP) is a natural undecidability candidate for this structure. Symbol matching via PO works; pair-index synchronization fails because |u_i| ≠ |v_i| creates misaligned pair boundaries, and the running lag can grow unboundedly.

## The ∀NTPP queue investigation

The ∀NTPP broadcast mechanism is fundamentally monotonic: announcements accumulate but cannot be consumed. This makes it insufficient for the unbounded synchronization required by general PCP.

## Assessment of the two-chain approach

The 2×∞ ladder provides one-dimensional computation on each chain, cross-chain symbol matching, and monotonic broadcast — but lacks cross-chain synchronization, consumable communication, and counting. This provides further evidence for decidability.

---

## Ongoing discussion: the omega-model direction

After the FW(C,N) counterexample, GPT-5.4 proposed a [status assessment](https://github.com/lambdamikel/alcircc5/blob/master/ALCI_RCC5_status_after_FW.pdf) distinguishing two levels of finiteness:
- **(A) Strong finiteness** (exact local-state closure with recentering) — **refuted** by the FW counterexample.
- **(B) Weak finiteness** (bounded local descriptors around a finite core) — possibly still true and useful as a finite alphabet for a future decision procedure.

GPT proposes a **regular omega-model theorem** as the missing ingredient: a representation of models using finitely many local interface signatures, finitely many PP/PPI thread control states, and a Buchi/parity-style acceptance condition for infinite proper-part chains.

> **Is the sequence of Hintikka types along an infinite PP-chain eventually periodic?** If yes, the omega-model route is viable. If no, even the type sequence is irregular, pointing toward undecidability.

---

## Ramsey theory and graph-theoretic undecidability: the complete-graph connection

ALCI\_RCC5 models are edge-colored complete graphs (4 colors: DR, PO, PP, PPI for distinct pairs) subject to the RCC5 composition table. This is natural Ramsey territory.

**The Bodirsky-Bodor dichotomy (2020/2024).** Every CSP of first-order expansions of RCC5 basic relations is either in P or NP-complete — never undecidable. The Ramsey property of finite RCC5 models is the key tool.

**Why Ramsey theory favors decidability.** Ramsey's theorem guarantees that any infinite ALCI\_RCC5 model must contain large monochromatic substructures, forcing **uniformity** — exactly the opposite of the **positional diversity** needed for encoding computation.

**Conclusion.** The Ramsey-theoretic analysis provides strong evidence for decidability. No known undecidable graph-coloring, Ramsey, or CSP problem has a plausible reduction to ALCI\_RCC5 satisfiability.

---

## What the earlier papers contribute

Despite the gaps, the papers introduce proof machinery that narrows the open problem:
- The quasimodel method + patchwork property identifies the extension gap as a specific constraint-satisfaction question about RCC5 disjunctive networks.
- The contextual tableau (GPT) cleanly separates the soundness (unfolding) argument from the completeness (extraction) argument.
- The profile-cached blocking series (GPT) develops correct local machinery that may be useful components for a future proof.
- The direct construction attempt (Claude) correctly identifies the forced DR edge phenomenon (Lemma 4.1) and the self-safety theorem.
- **Computational verification** pinpoints the gap precisely: condition Q3s (arc-consistency) would suffice but is not extractable from models — a **structural impossibility** (11.1% of concrete models produce DN networks violating Q3s).

**Why the two proven results don't compose.** The chain satisfiable → quasimodel exists (Claude) and open contextual tableau → model exists (GPT-5.4) cannot be composed because they operate on different intermediate representations with gaps on opposite sides.
