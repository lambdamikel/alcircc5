# Outdated and Superseded Material

This file contains detailed documentation of approaches and investigations that have been **disproved, retracted, or superseded** by later work. They are preserved here for reference and transparency. See [README.md](README.md) for the current status and active approaches.

---

## A Tableau Calculus for ALCI\_RCC5 (Original, Now Superseded)

### Overview

The tableau constructs a finite **completion graph** --- a complete graph where every pair of nodes has a base relation label, and every node has a concept label (a subset of the Fischer-Ladner closure of the input concept). Unlike tree-based DL tableaux, creating a new node requires assigning it a role to **every** existing node.

### Completion Graphs

A **completion graph** for a concept C₀ is a tuple G = (V, L, E, <) where:

- V is a finite set of nodes
- L: V -> 2^(cl(C₀)) assigns concept labels
- E: {(x,y) | x != y} -> {DR, PO, PP, PPI} assigns a base relation to every pair of distinct nodes, respecting converse (E(y,x) = inv(E(x,y)))
- < is a strict total order (creation order)

The **initial completion graph** has a single node x₀ with L(x₀) = {C₀}.

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

Every sequence of rule applications terminates. The final completion graph has at most **2^(O(|C₀|))** nodes.

**Argument**:
- Active (non-blocked) nodes have pairwise distinct labels, so there are at most 2^(|cl(C₀)|) active nodes.
- Labels grow monotonically (rules only add concepts), so each label changes at most |cl(C₀)| times.
- Each active node has at most |cl(C₀)| existential demands, each generating at most one witness.
- Total nodes: at most 2^(|cl(C₀)|) * |cl(C₀)| = 2^(O(|C₀|)).

### Soundness (NOT ESTABLISHED)

**Claimed theorem**: If the tableau produces an open completion graph for C₀, then C₀ is satisfiable.

**Status: NOT PROVEN.** The proof sketch below extracts a quasimodel and invokes the Henkin construction, which has the **extension gap** (see below). The quasimodel extraction is correct, but converting the quasimodel to an actual model requires solving a disjunctive constraint network at each Henkin step, and global solvability is not guaranteed (1,911 counterexamples at m=3).

**Proof sketch**: Extract a quasimodel from the open completion graph:
- T = {L(x) | x active}
- P = {(L(x), E(x,y), L(y)) | x != y}
- tau₀ = L(x₀)

The quasimodel conditions are verified:
- **(Q1) Existential witness**: Each existential demand exists R.D in a type tau is witnessed by saturation --- there exists a node y with E(x,y) = R and D in L(y).
- **(Q2) Non-emptiness**: DN(tau\_1, tau\_2) != {} for all distinct type pairs, since the completion graph is a complete graph with an edge between every pair.
- **(Q3) Algebraic closure**: For any types tau\_1, tau\_2, tau\_3 and R\_12 in DN(tau\_1, tau\_2), the completion graph's composition consistency (CF) on the witnessing triple gives R\_13 in comp(R\_12, R\_23) with R\_13 in DN(tau\_1, tau\_3) and R\_23 in DN(tau\_2, tau\_3).

By the soundness direction of the main theorem, C₀ is satisfiable. The quasimodel extracted from the completion graph is "model-like" (all pair-types realized by concrete node pairs), so the Henkin construction succeeds. See the discussion of the **extension gap** below for the subtlety with abstract quasimodels.

### Model Construction: Unfolding the Quasimodel

The quasimodel (or blocked completion graph) is a finite structure. The actual model may be infinite (e.g., when infinite PP-chains are required). The Henkin construction builds this infinite model incrementally, one element at a time. The critical concern is: **can edge assignments to newly created elements trigger "dormant" universal restrictions on existing elements, introducing concepts not present in their types and causing clashes?**

The answer is no. The proof relies on three layers of guarantees:

#### Construction Invariant

At every stage n of the Henkin construction, the partial model maintains:

- **(I1) Type membership**: every element e has tau(e) in T.
- **(I2) Pair-type membership**: for every distinct e\_i, e\_j: (tau(e\_i), R(e\_i,e\_j), tau(e\_j)) in P.
- **(I3) Composition consistency**: every triple satisfies the composition table.
- **(I4) Type permanence**: the type tau(e) is assigned at creation and **never subsequently modified**.

**Proof**: By induction on stages. At stage n+1, the new element e_(m+1) gets type tau' in T (I1). The edge assignments S\_1,...,S\_m from Claim 5.2 (formulated as a disjunctive constraint network solved via full RCC5 tractability) satisfy (tau(e\_i), S\_i, tau') in P for all i (I2), and all new triples are composition-consistent (I3). No existing type changes (I4).

#### No Dormant Activation (Lemma 5.4 in the paper)

Let e\_i be an existing element with `forall S.D` in tau(e\_i), and let e_(m+1) be newly created with type tau' and edge R(e\_i, e_(m+1)) = S\_i. Then:

- **If S\_i = S** (the restriction matches the new edge): then D is already in tau', guaranteed by R-compatibility (condition P1). The concept was placed in tau' at creation. **No propagation occurs.**
- **If S\_i != S**: the restriction does not apply. No issue.

Symmetrically: if `forall inv(S\_i).D` is in tau', then D is already in tau(e\_i) by R-compatibility (P2). Since tau(e\_i) was fixed at an earlier stage (I4), D was already there. **No concept is added to any existing type.**

#### Why Composition Cannot Force Unexpected Propagation (Remark 5.5)

One might worry: what if R(e\_a, e\_b) = U and R(e\_b, e_(m+1)) = T force R(e\_a, e_(m+1)) = S where S is the unique element of comp(U, T), and `forall S.D` is in tau(e\_a) but D is not in tau'?

This cannot happen. The extension is formulated as a **disjunctive constraint network** where the domain for each edge (e\_a, e_(m+1)) is D\_a = {S | (tau(e\_a), S, tau') in P}. Path-consistency enforcement refines these domains, and full RCC5 tractability guarantees a consistent atomic refinement exists. Every S\_a in the solution satisfies (tau(e\_a), S\_a, tau') in P, which by R-compatibility implies D in tau' whenever `forall S\_a.D` is in tau(e\_a). The composition constraints and pair-compatibility constraints are solved **jointly**.

#### Concept Truth (Lemma 5.6 in the paper)

**Lemma**: In the limit model, for every element e and every D in cl(C₀): D in tau(e) implies e in D^I.

**Proof by structural induction on D**:

- **D = A** (concept name): A^I = {e | A in tau(e)} by construction.
- **D = not A**: not A in tau(e) implies A not in tau(e) (clash-freeness), so e not in A^I, hence e in (not A)^I.
- **D = D1 and D2**: by type condition T1, both D1, D2 in tau(e); by induction, both hold.
- **D = D1 or D2**: by type condition T2, at least one in tau(e); by induction, at least one holds.
- **D = forall R.E**: if forall R.E in tau(e) and (e,e') in R^I, then (tau(e), R, tau(e')) in P by (I2). R-compatibility gives E in tau(e'). By induction, e' in E^I. This holds for **every** R-neighbor, so e in (forall R.E)^I. **This is where Lemma 5.4 applies**: E was already in tau(e') at creation, not propagated.
- **D = exists R.E**: the Henkin construction (fair enumeration) eventually creates a witness e' with R(e,e') = R and E in tau(e'). By induction, e' in E^I.

#### The Role of Monotonicity Along PP-Chains

The model may contain infinite PP-chains: e₀ PP e\_1 PP e\_2 PP ... For any external element x, Lemma 3.1 (upward monotonicity) constrains the progression of R(x, e\_i):

| R(x, e\_i) | Possible R(x, e_(i+1)) |
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

**Theorem**: If C₀ is satisfiable, then there exists a sequence of nondeterministic choices yielding an open completion graph.

**Proof sketch**: Given a model I with d₀ in C₀^I, maintain a guide function pi: V -> Delta^I mapping tableau nodes to model elements, with invariants:
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

---

## Historical material moved from README (May 2026)

The following subsections were originally in README.md but were moved here as part of a May 2026 cleanup to keep the README focused on the current proof machinery. They document superseded approaches, comparison narratives between completion attempts, adversarial review history, and pointers to older verification scripts. References back to the README (e.g., `[Round-2 review section](#round-2-review-and-repaired-proof-adoption-may-2026)`) refer to anchors that still exist in `README.md`.

### Evolution of the split-tree forest model: what survived and what had to change

> **Note (May 2026, post Option 4).** This subsection compares Claude's v2.1 completeness extraction against Wessel's whiteboard. v2.1 has since been **superseded** by GPT-5.5's repaired proof (see the Round-2 review section in README). The "v2.1 (current)" column below reflects the v2.1 era; the actual current pillar is GPT-5.5's repaired proof, which is structurally close to v2.1 but uses **occurrence-level equality** (not port-equality), **multi-parent mate classes** (not single-parent), and **request-closed cycles** (not Mate-class reachability) — fixing v2.1's gaps G1, G3, G4. The four whiteboard ideas (PPI-tree, EQ-splitting, congruence quotient, DR rigidity) survive unchanged in the repaired proof.

Comparing v2.1 of the completeness extraction back to Wessel's original whiteboard sketch, four passes of formalization (Wessel → GPT-5.4 → Claude v1 → GPT-5.5 review → Claude v2 → v2.1 obligation discharges) preserved the *core ideas* but rebuilt almost every *technical instantiation* of them.

**What survived from Wessel's whiteboard, unchanged in spirit:**

1. **PPI-as-tree orientation.** Every revision keeps Wessel's central move: orient the proper-part order so PPI is "immediate child" and the cover tree carries the PP/PPI hierarchy. The split tree T in v2.1 (Construction 1.x) is still a PPI-rooted oriented tree.
2. **Splitting joins into EQ-mates.** Wessel's "DAG-node splitting via weak EQ" survived as the construction of T: occurrences with the same `orig` image are EQ-mates, and the `Mate(σ)` class is the formal carrier for that intuition.
3. **Congruence quotient back to strong EQ.** Restoring strong EQ via a typed congruence is still the route, but it is now anchored by the explicit equality relation ≡_EQ,Q on declared *equality ports* Π_σ (introduced to fix obligation O1 — the v1 collision between blocking equivalence and semantic EQ).
4. **DR rigidity → {DR, PO} cross-edges only.** Wessel's observation that comp(PP, DR) = {DR} forces DR to propagate rigidly downward, leaving only {DR, PO} open between sibling subtrees, is *exactly* the three-way status partition (Core / Out / Front) that GPT-5.4 formalized and that v2.1 inherits verbatim. The {DR, PO} arc-consistency triviality (every triangle composes) is still the engine.
5. **Patchwork as glue.** Renz–Nebel's path-consistency theorem for atomic RCC5 networks is the same theorem in every revision — v2.1 just states it explicitly as `fact:renz-nebel`.

**What had to change between revisions:**

| Aspect | Original / GPT-5.4 / v1 | v2.1 (current) | Why it changed |
|---|---|---|---|
| Cover-edge orientation | **Hasse covers** of the PP-order | **Generated cover edges** (relative to the chosen witness set) | v1 Hasse construction breaks on infinite PP-chains (e.g.\ ∃ PP.⊤ ⊓ ∀ PP.∃ PP.⊤); GPT-5.5 review |
| Domain | Full model I | **Witness-generated submodel** I_w ⊆ I | v1 needed density and an ambient root to stitch witnesses globally; I_w removes both |
| Ambient root | Required for the global side-check | Replaced by **self-loops on the parent function** | I_w may have multiple roots; self-loops absorb degenerate PP-fixed-points |
| Pair tables | Raw M_k(s, t) pair tables | **Support-closed mosaics** Mos_k(s, t) (descriptors) | v1 C5 triple-coherence proof conflated witnesses across the three pairs; mosaics are bounded-arity labelled graphs that handle this correctly |
| Local coherence axioms | (C1)–(C5) on pair tables | **(M1)–(M7) on mosaics + (SC1)–(SC4) closure** | The mosaic shift; (M7) explicitly axiomatizes the typed-EQ congruence |
| Arity bound | Implicit | **Explicit constant N(C₀) = 5** (independent of C₀) | v2-review obligation O4: 3-locality of (M1)–(M7) + 5-locality of (SC1)–(SC4) + Renz–Nebel patchwork |
| DR/PO witness placement | Stated globally | **Bounded side context** Side(u, v) of size ≤ 5 | v2-review obligation O5: every DR/PO witness is realized inside {u, v, par(u), par(v), lca_T(u,v)} |
| Eventuality discharge | Sketched via König or implicitly via Büchi-automaton machinery in GPT-5.5's parallel route | **Finite-graph reachability** over `Mate(σ)`, no ω-words | Reachability is decidable on the finite quotient; v2-review obligation O2 forced this to be EQ-aware (multiple-incomparable-upward-witness pattern C_AB) |
| EQ modalities | Treated as part of the descriptor | **Eliminated by preprocessing** (∃ EQ.D, ∀ EQ.D are normalized away under strong EQ semantics) | v2-review obligation O3: simpler than handling them as a separate edge type |
| Simultaneous realization | Implicit in v1 Thm 1.20 sketch | **Explicit projection** π : T → U(Q) + `lem:simul-realization` (SR1/SR2/SR3) | v2-review obligation O6: T itself is a concrete realization of the canonical unfolding U(Q) in which all PP/PPI eventualities at all occurrences fire simultaneously |

**Net effect.** Wessel's four whiteboard ideas (PPI-tree, EQ-splitting, congruence quotient, DR rigidity) all carry through to v2.1 unchanged in spirit, but the *technical machinery* enacting them was rebuilt around (a) witness-generated submodels in place of full models, (b) support-closed mosaics in place of pair tables, and (c) reachability in place of ω-acceptance. The "DR is rigid → only {DR, PO} between siblings" observation is still the reason the whole approach works — and it is still the reason the closing arc-consistency check is trivial.

### Two routes to the same conclusion: reachability (Claude) vs. parity automaton (GPT-5.5)

> **Note (May 2026, post Option 4).** This subsection compares two May-2026 completion attempts against v1. Both have since been **superseded**: Claude's reachability route (v2.1) was found to have three load-bearing gaps in the GPT-5.5 round-2 review; the current pillar is GPT-5.5's no-automata [repaired proof](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.pdf) (May 2026), which is closer in spirit to Claude's reachability route but with cleaner foundations (occurrence-level equality, multi-parent mates, request-closed cycles). The comparison below is kept for historical perspective.

After GPT-5.5's review of v1, two parallel completion paths emerged. Both close the model-to-quotient gap; they differ in how they discharge transitive PP/PPI eventualities (the part that needs a fixpoint argument):

- **Claude's reachability route.** [`completeness_extraction_ALCIRCC5_v2.pdf`](https://github.com/lambdamikel/alcircc5/blob/master/papers/completeness_extraction_ALCIRCC5_v2.pdf) (31 pages, v2.1). Reduces eventuality discharge to *finite-graph reachability* over Mate(σ) classes on the rank-d quotient. No ω-words, no parity automata.
- **GPT-5.5's parity-automaton route.** [`ALCIRCC5_coherent_generated_split_forest_decidability.pdf`](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt5.5/ALCIRCC5_coherent_generated_split_forest_decidability.pdf) (10 pages). Discharges eventualities via a *deterministic parity ω-word automaton* whose emptiness is checked by standard parity-acceptance machinery.

**Tradeoffs.** A 3× page-count gap (10 vs 31) is real and tells most of the story:

| Aspect | Reachability route (Claude) | Parity-automaton route (GPT-5.5) |
|---|---|---|
| External prerequisites | Renz–Nebel patchwork only | Renz–Nebel + parity-automaton emptiness, complementation, acceptance |
| Faithfulness to Wessel's whiteboard | Stays in the geometric "graph world" the sketch lives in | Translates everything into ω-word semantics, one abstraction layer away from the picture |
| Where the risk lives | Six discrete combinatorial obligations (O1–O6), each independently checkable | Concentrated in the translation to ω-words being faithful — fewer pieces, each more load-bearing |
| Decidability proof length | 31 pages (self-contained) | 10 pages (modulo automata theory) |
| Effective complexity bound | Reachability over an exponential-sized graph | Parity-automaton emptiness, comparable order |

**Why both are kept.** GPT-5.5's route is genuinely lighter to *read* if you accept parity automata as standard machinery — it's a textbook completion via well-established results. Claude's route trades that brevity for self-containedness and proximity to the original combinatorial intuition. The two papers are not in competition; they are alternative completions of the same soundness chain (GPT-5.4's Thms 1.17–1.19), and having both in the repo lets a reader pick the route that matches their background.

**Corrections by Wessel.** GPT's initial formalization incorrectly included PP as an open sibling cross-edge value. Wessel corrected this: after EQ-splitting, if x PP y then x lies below y in the tree, placing x in the Core of the sibling pair — PP is NOT an open cross-edge. This correction is essential; without it, the open domain would be {DR,PO,PP} and the arc-consistency argument breaks down. With it, the open domain is just {DR,PO}, and the {DR,PO} network is trivially arc-consistent (comp(R,S) ∩ {DR,PO} ≠ ∅ for all R,S ∈ {DR,PO}).

**Why this handles the cyclic-model concepts.** The 7 concepts that lack tree models (e.g., ∃PO.A ⊓ ∃PP.¬B ⊓ ∀DR.A) work naturally: the PP-witness is an ancestor in the cover tree, the PO-witness is a cross-edge in a sibling subtree. The ∀DR.A universal fires only on DR-related nodes — the ancestor is PP-related (not DR), so no conflict. The cover tree separates these two witnesses into different mechanisms (tree vs. cross-edge), avoiding the problematic mixed compositions.

**How PP edges are forced by composition (no explicit ∃PP needed).** The concept X = ∃DR.∃PO.C ⊓ ∀DR.¬C ⊓ ∀PO.¬C ⊓ ∀PP.X illustrates a remarkable feature of ALCI\_RCC5: PP edges can be forced without any explicit ∃PP demand, purely through composition propagation. A root node r satisfying X has a DR-neighbor a (satisfying ∃PO.C) and a's PO-neighbor b (satisfying C): r --DR→ a --PO→ b(C). The relation between r and b must lie in comp(DR, PO) = {DR, PO, PP}. But r has ∀DR.¬C and ∀PO.¬C, and b satisfies C — so DR and PO are blocked, leaving **only PP**. The PP edge is forced entirely by composition + universal filtering.

The recursive conjunct ∀PP.X then forces infinite models: since r PP b, node b must also satisfy X (by ∀PP.X), creating its own DR→PO chain and forcing another PP-ancestor above it, ad infinitum. In the cover tree, b sits ABOVE r (since r PP b means b is an ancestor of r), creating an infinite ascending PP-chain: r PP b PP b' PP b'' ... The cover-tree tableau handles this finitely: the type for C-elements can serve as its own PP-ancestor type (different domain elements, same abstract type), so the finite type set {τ₀(C, X), τ₁(¬C, ∃PO.C), τ₂(¬C, root)} represents an infinite model. Verified SAT by both reasoners.

**The "PO-loop" trick — 2-element SAT model via symmetric cycles.** Consider C ⊓ ∃PO.∃PO.C ⊓ ∀PO.¬C ⊓ ∀DR.¬C ⊓ ∀PP.¬C ⊓ ∀PPI.¬C. Naive reasoning suggests this should be UNSAT: d has C, the existential chain d→PO→a→PO→b demands b ∈ C, but d's universals seemingly require b ∈ ¬C for every possible d-b relation in comp(PO, PO) = {DR, PO, PP, PPI}. However, the concept is **SAT** via a 2-element loop: {d, a} with C = {d} and ρ(d,a) = PO. Because PO is symmetric (PO(d,a) ⟹ PO(a,d)), the chain d→PO→a→PO→d loops back to the root itself — the "third node" in the ∃PO.∃PO formula is **d** under strong EQ identity. The universals ∀R.¬C constrain d's *outgoing* R-neighbors (a has ¬C ✓), but don't prevent d from *being* a C-neighbor of a (a doesn't have ∀PO.¬C — it has ∃PO.C instead, satisfied by d). Two syntactic positions in ∃PO.∃PO can thus map to the same semantic element. The cover-tree tableau correctly reports SAT for this concept.

**The "clash-out to EQ" trick — genuine UNSAT via strong EQ.** The complementary pattern C ⊓ ∃PO.∃PO.¬C ⊓ ∀PO.C ⊓ ∀DR.C ⊓ ∀PP.C ⊓ ∀PPI.C **is** UNSAT. With the chain d→PO→a→PO→c: d's ∀PO.C forces a ∈ C, and a's ∃PO.¬C forces c ∈ ¬C. The relation ρ(d,c) must lie in the full RCC5 composition comp(PO, PO) = {DR, PO, PP, PPI, EQ}. d's four universals ∀R.C (for R ∈ {DR, PO, PP, PPI}) kill all non-EQ options — each forces c ∈ C but c ∈ ¬C ✗. Only EQ remains. Under **strong EQ semantics** (EQ = identity), this forces d = c, giving d ∈ C ∧ d ∈ ¬C → clash. The loop escape of the previous example doesn't work here: the endpoint requires ¬C but d has C, so d ≠ c is forced, and the universals then block every non-EQ relation, while strong EQ delivers the final contradiction. This example illustrates why strong EQ semantics is essential — under weak EQ (equivalence class), collapsing d and c would not immediately clash and extra machinery would be needed to derive UNSAT.

### Ninth approach: MSO encoding via interval semantics

Reduces ALCI\_RCC5 satisfiability to the **Borel monadic second-order theory of (R, <)**, which is decidable by Manthe's theorem (2024). RCC5 has a faithful interpretation over open intervals on the real line, making **composition consistency automatic**. The encoding is complete except for one technical gap: MSO-definability of endpoint pairing (Dyck matching) over scattered subsets of R.

See [**MSO Encoding (PDF)**](https://github.com/lambdamikel/alcircc5/blob/master/papers/MSO_encoding_ALCIRCC5.pdf) for the full paper (16 pages).

### Summary: twelve approaches

**Promising and partially successful:**

| Approach | Author(s) | Key idea | Gap | Status |
|---|---|---|---|---|
| Cover-tree tableau (eleventh) | Wessel/GPT/Claude | PPI-tree + EQ-splitting + {DR,PO}-only cross-edges + patchwork; GPT-5.5 round-2 no-automata proof closes completeness | None (current pillar) | **Current best statement of decidability**; 911 concepts, 0 errors; 100% CT models |
| GPT-5.5 automata-flavored split-forest (twelfth) | GPT-5.5 | Same split-forest skeleton + ultimately periodic branches `u_0…u_m(v_0…v_{k-1})^ω` + cycle-realization condition; both directions proved | None | **Alternative route**: independent self-contained decidability proof, retained as a second witness |
| Quadruple-type | Claude | 4-element star path-consistency for cross-branch edges | Formal sufficiency proof pending | **713 concepts, 0 errors** |
| Two-tier quotient | Claude | Period descriptors + PP-kernels + full RCC5 tractability | **PO gap** | **PO-coherent fragment decidable** |
| MSO encoding | Claude | Reduce to Borel-MSO(R,<) via interval semantics | MSO-definability of Dyck matching | One technical gap |
| Triangle-type | Claude | Triangle-filtered arc-consistency | Extension Solvability Conjecture | Conditional |

**Disproved, retracted, or incomplete:**

| Approach | Author(s) | Key idea | Gap | Status |
|---|---|---|---|---|
| Quasimodel theory (type elimination) | Claude | Greatest-fixpoint type elimination + original tableau | Type elimination rejects satisfiable concepts (Q3 anti-monotonicity); tableau soundness unproven (extension gap, 1,911 counterexamples at m=3) | **Retracted** |
| Quasimodel reasoner (constructive, `alcircc5_reasoner.py`) | Claude | Bottom-up construction + disjunctive path-consistency + sibling/role-path checks | Role-path check assumes tree unfolding; wrongly rejects SAT concepts whose only witnesses are cycles via symmetric roles (PO/DR) | **Known incomplete** (used as a cross-validation tool only) |
| Direct construction | Claude | Tree unraveling + DN\_safe | Theorem 5.5 false | **Retracted** |
| Tri-nbr tableau | Claude | Tri-neighborhood blocking + filtered unraveling | Termination false; soundness gap | **Termination disproved** |
| Contextual tableau | GPT | Local states + recentering | FW(C,N) false | Incomplete |
| Profile-cached blocking | GPT | Coherent predecessor blocks | Color structure changes in unraveling | Incomplete |
| Meet-based replay | GPT | Meet-semilattice on labels | Same unraveling gap | Incomplete |

### Direct attacks on the patchwork property (April 2026, Claude)

Beyond the standard reductions, three direct probes were mounted against the **patchwork property** itself — the load-bearing assumption behind every decidability proof in this repository (Renz & Nebel 1999 for atomic RCC5; Renz 1999 for full RCC5 tractability). The idea: if patchwork fails once augmented with an ALCI TBox, that failure could be a seed for undecidability. Three papers form a cascade, each refuting the previous paper's simplified propagation with a strictly smaller counterexample, and converging on split-forest rank-d validity as the minimum viable structure.

| Paper | Propagation attempted | Gap exposed | Counterexample size |
|---|---|---|---|
| [`patchwork_augmentation_ALCIRCC5.pdf`](https://github.com/lambdamikel/alcircc5/blob/master/papers/patchwork_augmentation_ALCIRCC5.pdf) | Weak arc-consistency (composition + TypeSafe over existing V) | None found in three probes; conjectured Proposition 7.1 | — |
| [`typed_patchwork_counterexample_ALCIRCC5.pdf`](https://github.com/lambdamikel/alcircc5/blob/master/papers/typed_patchwork_counterexample_ALCIRCC5.pdf) | Strong arc-consistency (+ existential extensibility against V) | V-to-pending-witness conflicts not caught | **2 nodes, 7 axioms** |
| [`inter_witness_counterexample_ALCIRCC5.pdf`](https://github.com/lambdamikel/alcircc5/blob/master/papers/inter_witness_counterexample_ALCIRCC5.pdf) | Stronger arc-consistency (+ inter-witness pair-domains) | Pending-witness-to-pending-witness conflicts not caught | **1 node, 7 axioms** |

**Pattern.** Each simplification of split-forest validity has a counterexample. The counterexamples shrink as propagation strengthens, because each layer catches more local failures and leaves only purer versions of the missing gap. The three-paper cascade conjecturally terminates at split-forest rank-d validity: recursing the inter-witness pair-domain check up to modal depth d is equivalent to the split-forest soundness conditions. There is no simpler propagation that works.

**What this says about decidability.** Decidability is unaffected: the split-forest paper already uses the full rank-d machinery, not any of the simplified propagations. The cascade strengthens the decidability case by concretising the "no k-ary synthesis" argument from the probe paper — every TBox-expressible constraint decomposes through the witness-extension hierarchy into unary, binary, or pair-local checks. ALCI cannot force genuinely k-ary (k ≥ 4) constraints.

**What this says about undecidability.** The case for decidability keeps strengthening. Every direct attack on patchwork has failed (the cascade), and every standard undecidability reduction is documented as blocked. The remaining plausible undecidability angles are:

1. **ALCI\_RCC8 with a non-grid reduction shape** — unexplored; Lutz-Wolter's L_RCC8 undecidability gives a target, and the coincidence obstruction is what blocks naive grid transfer. A non-grid reduction that exploits NTPPI/TPPI transitivity asymmetry differently hasn't been tried.
2. **Counter-machine simulation via PP-chains** — classical, but ALCI\_RCC5 lacks number restrictions (no zero-test). The cascade's "no k-ary synthesis" argument suggests this is exactly what's blocked.
3. **Encode via infinite structure (ω-automata, infinite PP-chains)** — speculative; ALCI\_RCC5 has infinite models in general, and forcing specific infinite structure without counting looks unavailable.

**Recommendation (April 2026, Claude).** Further probes have low expected yield. The productive remaining direction is to **prove the cascade's termination theorem** (stronger arc-consistency at depth d = split-forest rank-d validity) as a positive result, and to **audit the cover-tree implementation** against split-forest validity to resolve the open theory-vs-implementation gap.

### Discussion of failed and incomplete approaches

The following approaches have been **disproved, retracted, or shown incomplete**.

**1. Original quasimodel paper (Claude): RETRACTED.** Type elimination algorithm rejects satisfiable concepts (Q3 anti-monotonicity causes cascade elimination — an **incompleteness**, not unsoundness). The original tableau's soundness is unproven (extension gap: 1,911 counterexamples at m=3). RCC8 results retracted.

**1b. Constructive quasimodel reasoner (`alcircc5_reasoner.py`): KNOWN INCOMPLETE.** A bottom-up replacement that avoided the non-monotonicity of type elimination, and was used extensively as a cross-validation oracle. It has now been found to wrongly reject the PO-loop SAT concept C ⊓ ∃PO.∃PO.C ⊓ ∀PO.¬C ⊓ ∀DR.¬C ⊓ ∀PP.¬C ⊓ ∀PPI.¬C. The role-path compatibility check in `check_role_path_compatibility` implicitly assumes tree unfoldings: it cannot close a chain g→R→j→S→g through a symmetric role. The reasoner's **SAT answers remain sound**, but the claim that UNSAT answers are sound is **withdrawn for concepts requiring cycles via symmetric roles**. The decidability proof is unaffected — it now goes through GPT-5.4's v1 split-forest paper (soundness, Thms 1.17–1.19) plus GPT-5.5's [repaired split-forest decidability proof](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.pdf) (both directions, no automata).

**2. Contextual tableau (GPT-5.4): INCOMPLETE.** Proves full soundness but reduces completeness to FW(C,N), which is **false** — C∞ = (∃PP.⊤) ⊓ (∀PP.∃PP.⊤) is a counterexample. See the [FW counterexample proof (PDF)](https://github.com/lambdamikel/alcircc5/blob/master/papers/FW_proof_ALCIRCC5.pdf).

**3. Direct model construction (Claude): RETRACTED.** Two errors found by GPT-5.4: algebraic error in Lemma 3.2 and Theorem 5.5 is false.

**4–5. Profile-cached blocking and meet-based replay (GPT-5.4): INCOMPLETE.** Both fail at the unraveling step where the color structure changes.

**6. Triangle-type blocking (Claude): CONDITIONAL.** Decidability conditional on the Extension Solvability Conjecture (unproven). See [triangle-type paper (PDF)](https://github.com/lambdamikel/alcircc5/blob/master/papers/triangle_blocking_ALCIRCC5.pdf).

**7. Tri-neighborhood tableau (Claude): TERMINATION DISPROVED.** Non-termination via frontier advancement: frontier nodes have Tri ⊂ interior Tri and are never blocked. The blocking dilemma (soundness requires Tri-matching; termination requires ignoring Tri) remains open. See [tableau paper (PDF)](https://github.com/lambdamikel/alcircc5/blob/master/papers/tableau_ALCIRCC5.pdf).

**8. MSO encoding (Claude): ONE GAP.** Reduces to decidable Borel-MSO(R,<) but MSO-definability of Dyck matching is unresolved.

**The structural wall (approaches 1–5).** All five fail at global edge assignment in complete-graph models. The cover-tree tableau avoids this wall by decomposing models into trees with {DR,PO}-only cross-edges.

### Independent review and assessment of the decidability proof and calculus (April 2026, Opus 4.7)

In April 2026, Anthropic's **Claude Opus 4.7** was commissioned by Michael Wessel to perform an adversarial review of the decidability proof for ALCI\_RCC5 and the accompanying cover-tree tableau calculus. The review was run in two rounds, with the repository authors free to apply fixes between rounds.

#### Round 1 — twelve structural counterexamples

The reviewer ran an audit of the cover-tree tableau implementation and identified a **soundness failure** affecting the `check_tree_cross_interaction` stage (CT4). The defect was a short-circuit (`if len(all_dems) <= 1: continue`) that skipped composition propagation across three-type chains whose intermediate types each carried only a single demand. A family of **twelve** minimal UNSAT concepts of modal-depth 2 exposed the bug:
```
C_{R₁, R₂}  ≡  ∃R₁.∃R₂.A  ⊓  ⨆_{R ∈ comp(R₁, R₂)} ∀R.¬A      (R₂ ≠ inv(R₁))
```
for each pair (R₁, R₂) ∈ {DR, PO, PP, PPI}² excluding the four EQ-admitting diagonals, including the simplest transitive-role instance `∃PP.∃PP.A ⊓ ∀PP.¬A`. The cover-tree reported SAT on all twelve; the cycle-aware quasimodel reasoner correctly reported UNSAT on all twelve. The review paper [`review_paper/review_cover_tree_tableau.pdf`](https://github.com/lambdamikel/alcircc5/blob/master/review_paper/review_cover_tree_tableau.pdf) (11 pages, LaTeX source [here](https://github.com/lambdamikel/alcircc5/blob/master/review_paper/review_cover_tree_tableau.tex)) documents the counterexamples, the root cause, a repair sketch, and four independent verification strands.

The reviewer explicitly *did not* refute the decidability theorem itself — which now rests on GPT-5.4's v1 split-forest paper (soundness) plus GPT-5.5's [repaired split-forest decidability proof](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.pdf) (both directions, May 2026) — only the soundness of the committed cover-tree code.

#### Round 2 — re-assessment after the fix

The repository authors applied two calculus-level fixes:
1. A new `check_role_path_compatibility` stage (**CT5**) in [`src/cover_tree_tableau.py`](https://github.com/lambdamikel/alcircc5/blob/master/src/cover_tree_tableau.py), a fixed-point arc-consistency pruner over all three-type chains g →R→ j →S→ w, with a strong-EQ cycle-close clause for the four EQ-admitting pairs {(DR,DR), (PO,PO), (PP,PPI), (PPI,PP)} — exactly the check recommended by Round 1.
2. Transitive universal propagation in [`src/alcircc5_reasoner.py`](https://github.com/lambdamikel/alcircc5/blob/master/src/alcircc5_reasoner.py) (`compute_safe`): when R ∈ {PP, PPI}, ∀R.D must propagate as a whole (not just its body D) into R-successor types — the standard ALCH\_tr transitive-role rule.

The reviewer re-audited the post-fix repository and ran a second attack round. Results:

- **All 12 Round-1 counterexamples** are now correctly reported UNSAT by the cover-tree tableau (0/12 mismatches with QMc). Reproducible via [`review_paper/test/verify_twelve_counterexamples.py`](https://github.com/lambdamikel/alcircc5/blob/master/review_paper/test/verify_twelve_counterexamples.py).
- **25+ fresh targeted attacks** (4-role-chain stressors, tree/cross mixes at depth 2, EQ-admit boundary cases, sibling-universal interactions with singleton and non-singleton compositions, grandchild–grandparent–sibling triangle constructions) agree with QMc in every case.
- **300 pseudo-random depth-3/4 concepts** across two seeds (seeds 1 and 7, role alphabet {DR, PO, PP, PPI}, 2–3 atomic concepts) produce 0 mismatches.

The reviewer **withdraws the Round-1 soundness-failure claim with respect to the current repository state**. No adversarial concept constructed during the second round produces a mismatch between the cover-tree tableau and the cycle-aware quasimodel reasoner.

#### Verdict (Opus 4.7 review)

On the available evidence, the decidability claim for ALCI\_RCC5 is **plausibly intact** (no complexity bound is asserted; the PO-coherent fragment's quotient is already 2-EXPTIME). The most tangible empirical obstacle — a concrete small concept on which the two procedures disagree — has been removed. Two residual caveats remain, both acknowledged in the review paper:

- Structural and random testing cannot certify soundness; a proof-level argument that **CT1…CT5** jointly entail the patchwork property should come from the companion [cover-tree tableau paper](https://github.com/lambdamikel/alcircc5/blob/master/papers/cover_tree_tableau_ALCIRCC5.pdf).
- The Round-1 counterexamples remain historically valid as a reminder that test-distribution blind spots can mask calculus-level bugs for arbitrarily long. The pre-fix 911-concept cross-validation suite reported zero mismatches for exactly such a blind-spot reason.

#### Artefacts (Opus 4.7 review)

- [`review_paper/review_cover_tree_tableau.pdf`](https://github.com/lambdamikel/alcircc5/blob/master/review_paper/review_cover_tree_tableau.pdf) — the review paper (11 pages, CEUR-ART template). Sections 5–8 document the Round-1 counterexamples; Section 10 is the Round-2 reassessment.
- [`review_paper/review_cover_tree_tableau.tex`](https://github.com/lambdamikel/alcircc5/blob/master/review_paper/review_cover_tree_tableau.tex) — LaTeX source.
- [`review_paper/test/`](https://github.com/lambdamikel/alcircc5/blob/master/review_paper/test/) — adversarial test harness (5 Python scripts + a README). Complements the repository's own cross-validation in [`src/stress_test_cover_tree.py`](https://github.com/lambdamikel/alcircc5/blob/master/src/stress_test_cover_tree.py) and [`src/test_cyclic_reasoner.py`](https://github.com/lambdamikel/alcircc5/blob/master/src/test_cyclic_reasoner.py).

### GPT-5.5 review and v2 completeness extraction (May 2026)

> **Status note (post Option 4).** This subsection describes Claude's v2.1 completeness extraction, which was the current pillar in early May 2026 but has since been **superseded** by GPT-5.5's no-automata [repaired proof](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.pdf) after a Round-2 review found three load-bearing gaps in v2.1 (G1, G3, G4 — see the Round-2 section in README). Preserved for historical record.

In May 2026, **GPT-5.5** (a reasoning-engine variant of GPT) reviewed all four argument-bearing files (the v1 sibling-interface paper, the patched cover-tree tableau note, Claude's v1 completeness extraction, and Claude's implementation paper). The review identified **two structural defects**: one in the v1 completeness extraction directly, and the same two defects in adjacent material in the v1 sibling-interface paper itself (Def 1.5's ambient-root requirement, Def 1.7's witness-menu treatment of PP/PPI, and the Thm 1.20 proof sketch). GPT-5.5 then produced its own repaired proof using Büchi automata over a cycle-realization condition (`papers/gpt5.5/ALCIRCC5_coherent_generated_split_forest_decidability.pdf`). Claude subsequently produced two v2 papers:

- [`papers/completeness_extraction_ALCIRCC5_v2.pdf`](https://github.com/lambdamikel/alcircc5/blob/master/papers/completeness_extraction_ALCIRCC5_v2.pdf) (31 pages, v2.1) — closes the model-to-quotient gap **without** ω-acceptance machinery, by reducing GPT-5.5's cycle-realization condition to finite-graph reachability.
- [`papers/trees/sibling_interface_descriptors_ALCIRCC5_v2.pdf`](https://github.com/lambdamikel/alcircc5/blob/master/papers/trees/sibling_interface_descriptors_ALCIRCC5_v2.pdf) (10 pages) — preserves GPT-5.4's Thms 1.17–1.19 (soundness) verbatim and reinterprets v1 Def 1.5 (parent self-loops, generated witness-cover edges), v1 Def 1.7 (PP/PPI eventualities by reachability discharge, not witness-menu slots), and v1 Thm 1.20 (proof sketch dropped, model-to-quotient delegated to the v2 completeness extraction paper).

#### Two defects in v1

**Defect 1 — Hasse construction breaks on infinite PP-chains.** The v1 split-tree construction assumed the model's PP/PPI partial order had a well-founded ambient root, then built a Hasse-like tree by walking up immediate PP-predecessors from a designated root element. This works for tree-shaped models but breaks for concepts that force infinite ascending PP-chains. The standard witness is

> *C↑* ≡ ∃PP.⊤ ⊓ ∀PP.∃PP.⊤

every model of *C↑* has an infinite PP-chain *x*₀ PP *x*₁ PP *x*₂ PP …, with no PP-maximal element. The v1 construction has nowhere to root the tree.

**Defect 2 — Witness conflation in C5 (triple coherence).** The v1 proof of the C5 triple-coherence axiom for extracted descriptors implicitly identified the *role-witness* of an existential at one rank with the *concrete element* witnessing the same demand at a different rank along the same trunk. When witness sets at different ranks differ (which is generic), this conflation invalidates the C5 verification step.

#### Seven repairs in v2 (without automata)

The v2 paper applies GPT-5.5's structural ideas but **without** any Büchi or ω-language machinery. Seven concrete repairs:

1. **(R1) Witness-generated submodel.** Restrict to the submodel generated by selected existential witnesses from the root — logic-generated, sparse, no density issue, no ambient-root dependence.
2. **(R2) Generated cover edges.** Cover edges are *selected witness-cover* edges in the generated submodel — not semantic Hasse covers.
3. **(R3) Self-loops on the parent function.** The finite quotient's parent map permits self-loops, so ultimately periodic ancestor trunks (such as those forced by *C↑*) are first-class. No ambient root is required.
4. **(R4) Containment orientation made explicit.** Parent = proper superpart, child = proper part — fixes the orientation ambiguity in v1.
5. **(R5) Support-closed mosaics replace raw pair tables.** The C5 fix: store joint atomic networks (triples), not pairs, so witness identities are preserved across rank steps.
6. **(R6) Typed-EQ congruence as an explicit axiom.** Separated from blocking equivalence; corrects a v1 conflation between the two.
7. **(R7) Reachability discharge for PP/PPI eventualities.** Transitive ∃PP.*D* / ∃PPI.*D* existentials are discharged by *finite-graph reachability* on the finite quotient — not Büchi acceptance. For each eventuality at state *σ*, check whether some *σ′* reachable from *σ* along parent edges (including self-loops) satisfies the witness condition. Decidable in *O*(|*S*|²) per eventuality.

The crucial observation: GPT-5.5's cycle-realization condition reduces to ordinary reachability over the finite quotient, because the parent function is total and may self-loop, so eventualities discharged on a self-loop are automatically witnessed.

#### Net effect on the decidability argument (v2.1 era)

Combined with the v1 soundness chain (split-forest → unfolding → König → canonical refinements → strong-EQ model), the two v2 papers were claimed to yield decidability of concept satisfiability in ALCI\_RCC5. The argument stood at v2.1 on three files (v1 sibling, v2 sibling delta, v2 completeness extraction); v2 sibling is explicitly a delta paper and does *not* restate the v1 soundness proofs. v2.1 has since been superseded (see the Round-2 section in README).

### Round-2 review and repaired-proof adoption — full prose (May 2026)

This is the verbose version of the README's compressed Round-2 section, preserved here for the full audit trail.

A week after v2.1, GPT-5.5 produced a **second formal review** of v2.1 itself, archived under [`papers/gpt5.5_round2/`](https://github.com/lambdamikel/alcircc5/tree/master/papers/gpt5.5_round2). The review identified **eight critical structural gaps (G1)–(G8)** in v2.1, of which three are genuinely load-bearing for the decidability argument. GPT-5.5 also produced a self-contained **repaired proof** that fixes all three load-bearing gaps without recourse to ω-acceptance machinery.

The decision (Wessel + Claude): **v2.1 is marked superseded**; GPT-5.5's repaired proof is adopted as the current best statement of the decidability argument; Claude's contribution shifts to **verification** of the repaired proof's combinatorial claims.

#### Three load-bearing gaps in v2.1

**Gap G1 — profile-level equality ports contradict vertical separation.** v2.1 defines the equality relation ≡_EQ,Q at the *profile* (equality-port) level: two states σ, τ are EQ-equivalent iff a port-bijection matches their declared equality ports. Axiom M1 (reflexivity of equality) and Axiom M7 (typed-EQ congruence) together imply σ ≡_EQ,Q σ via the identity port-map. Combined with the vertical-separation axiom (which forbids ≡_EQ,Q along any strict PP/PPI path), this yields a contradiction on **self-loops**: a state σ with a PP self-edge (which v2.1 allows, to absorb infinite PP-chains) is simultaneously reflexively EQ-related to itself (by M1+M7) and forbidden from being EQ-related along a strict PP path (by vertical separation). v2.1 has no consistent reading.

**Gap G3 — multiple upward PP witnesses with different parents.** v2.1 builds the mate construction (the EQ-equivalence class Mate_Q(σ)) such that every mate of σ shares a single semantic parent state. The stress formula
`C_AB ≡ A ⊓ B ⊓ ∃PP.A ⊓ ∃PP.B ⊓ ∀PP.(A → ¬B) ⊓ ∀PP.(B → ¬A)`
admits a model with two distinct upward PP witnesses for the root (an A-only superpart and a B-only superpart), which by Wessel's containment orientation forces two mate occurrences with **different parents**. v2.1's single-parent mate construction cannot accommodate this.

**Gap G4 — rootless orientation incompatible with the depth-from-u_* projection.** v2.1 retains a projection π: T → U(Q) that depends on depth from a distinguished occurrence u_*, but the rootless orientation (Section "Self-loops on the parent function") allows occurrences that are *proper-superparts* of u_*, for which depth-from-u_* is undefined. The simultaneous-realization lemma (`lem:simul-realization`) silently assumes u_* is a root.

#### GPT-5.5's repaired proof — three structural fixes

GPT-5.5's [`repaired_split_forest_no_automata_proof.pdf`](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.pdf) (16 pages) addresses all three:

1. **Occurrence-level equality.** Definition 4.1 (S5) sets u ≡_EQ v ⇔ orig(u) = orig(v), i.e., two occurrences are EQ-mates iff they project to the same semantic element. This is *not* a port-bijection condition on profiles; it is a concrete identification on occurrences. M1 reflexivity then trivially holds and vertical-separation contradictions vanish — a self-loop occurrence is its own (and only) mate, and there is no need for a strict PP path.
2. **Mates with different parents.** Mate_Q(σ) is redefined via the port-equivalence relation, not via a single semantic-parent witness. The two mate occurrences for C_AB live in different mate classes with different parents — fully accommodated.
3. **Request-closed cycles replace ω-acceptance.** Transitive PP/PPI eventualities are discharged by **request-closed cycles** in the rank-d quotient graph: a state σ with a deferred PP-request is realized iff the request is closed by a finite cycle of σ-reachable states. No parity, no Büchi. The decidability check is reachability + cycle-closure, both standard finite-graph operations.

The repaired proof formulates **ten finite-checkable validity conditions (V1)–(V10)** on rank-d quotients, gives a coarse upper bound B(C₀) = 2^(2^(p(n))) on certificate size for a polynomial p, and establishes decidability via guess-and-check.

#### Verification work (Claude's contribution) — full table

GPT-5.5's [`verification_recommendations_for_claude.pdf`](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt5.5_round2/verification_recommendations_for_claude.pdf) lists six Python work packages and seven Lean targets. The Python work lives under [`verification/`](https://github.com/lambdamikel/alcircc5/tree/master/verification):

| WP | Title | Status | Output |
|---|---|---|---|
| WP1 | RCC5 composition table | **PASS** | [`rcc5_composition_check.py`](https://github.com/lambdamikel/alcircc5/blob/master/verification/python/rcc5_composition_check.py), [report](https://github.com/lambdamikel/alcircc5/blob/master/verification/reports/rcc5_composition_table.txt) |
| WP2 | Bounded certificate soundness fuzzer | **PASS** | [`certificate_checker.py`](https://github.com/lambdamikel/alcircc5/blob/master/verification/python/certificate_checker.py), [report](https://github.com/lambdamikel/alcircc5/blob/master/verification/reports/certificate_checker.txt) |
| WP3 | Small-model SAT/UNSAT oracle | **PASS** | [`small_model_oracle.py`](https://github.com/lambdamikel/alcircc5/blob/master/verification/python/small_model_oracle.py), [report](https://github.com/lambdamikel/alcircc5/blob/master/verification/reports/small_model_oracle.txt) |
| WP4 | Multiple-superpart C_AB stress | **PASS** (folded into WP2/WP3) | see `cert_C_AB` in WP2, two-mate model in WP3 |
| WP5 | Request-closed blocking cycles | **PASS** (folded into WP2) | see `cert_WP5_cycle_*` in WP2 |
| WP6 | Mosaic closure search | **PASS** | [`mosaic_closure_search.py`](https://github.com/lambdamikel/alcircc5/blob/master/verification/python/mosaic_closure_search.py), [report](https://github.com/lambdamikel/alcircc5/blob/master/verification/reports/mosaic_closure_search.txt) |

**WP1 result.** Exhaustive enumeration over non-empty subsets of |U|=5 derives the 5-relation RCC5 base by set-theoretic comparison, then composes via triples to compute comp(R, S) for all 25 cells. The computed table matches GPT-5.5's stated table (repaired proof, lines 99–114) **exactly**. The signature stabilises at |U| = 4 (no new compositions at |U| = 5), confirming the table is universe-size-independent for |U| ≥ 4. The in-repo quasimodel reasoner's `COMP` table ([`src/alcircc5_reasoner.py`](https://github.com/lambdamikel/alcircc5/blob/master/src/alcircc5_reasoner.py)) differs only in four cells — (DR,DR), (PO,PO), (PP,PPI), (PPI,PP) — by exactly EQ, which the reasoner intentionally omits because it models edges between distinct nodes only (the `EQ_ADMITTING_PAIRS` convention). No genuine mismatches.

**WP2 result.** Implements (V1) type legality, (V3) vertical safety, (V4)/(V5) equality-aware vertical existential/universal discharge, (V9) typed-equality congruence on ports, and (V10) exact summaries — the vertical fragment of the validity-condition checker. 10-test corpus: C_up accepted with parent self-loop (G1 test under occurrence-level equality), C_AB accepted with two mate occurrences carrying different selected parents (G3 witness), C_AB rejected when forced into a single-parent mate (v2.1-style failure mode), UNSAT concepts rejected on the soundness side, and request-closed cycles accepted/rejected correctly (WP5 folded in). All 10 verdicts match expected.

**WP3 result.** Brute-force enumeration of complete RCC5 labelings on n ≤ 4 confirms WP2 on a 5-test corpus. C_AB realised at n = 3 with model A = {0, 2}, B = {1, 2}, ρ(2, 0) = PP, ρ(2, 1) = PP, ρ(0, 1) = PO — exactly the two-incomparable-PP-superparts pattern G3 was about. C_up returns "no finite model up to n = 4", consistent with WP2 accepting it via parent self-loop unfolding to an infinite chain (semantics: infinite-model-only SAT). The two genuine UNSAT entries return "no finite model" matching WP2's rejection.

**WP6 result.** Tests (M1)–(M5) and the support-closure axioms (SC1)–(SC4) on small mosaics. (A) Of all 4³ = 64 triangle labelings, 41 satisfy (M3) and 23 are rejected; every rejected triangle is also unrealizable by finite subsets of |U| ≤ 5, confirming (M3) is exact. (B) Every (M3)-consistent triangle is realizable for n ≤ 5 — Renz–Nebel patchwork property on triangles. (C) DR/PO side-witness insertion succeeds without breaking (M4) in both directions. (D) Universal propagation through a PP-chain forces A at the deep position via (M3)+(M4) jointly; the legal chain is accepted and a broken chain is caught. (E) Sibling-branching: with p PPI s₁, p PPI s₂, s₁ PO s₂, s₁ PPI c, the legal L(c, s₂) candidates are exactly {DR, PO, PP} = comp(PP, PO). No counterexample to the patchwork lemma was found.

### Implementation: ALCI\_RCC5 Concept Satisfiability Reasoner (quasimodel reasoner, full description)

[**`alcircc5_reasoner.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/alcircc5_reasoner.py) is a working implementation of a concept satisfiability checker for ALCI\_RCC5. It implements a **constructive quasimodel search** that builds candidate quasimodels bottom-up and verifies them using disjunctive path-consistency of RCC5 constraint networks. It is retained as a cross-validation oracle for the cover-tree tableau, **not** as a step of any decidability proof.

#### Algorithm

1. Parse input concept in negation normal form (NNF)
2. Compute Fischer-Ladner closure
3. Enumerate all Hintikka types over the closure
4. Compute SAFE relations between all type pairs (relations R such that all ∀R.C constraints in both types are satisfied)
5. **Bottom-up quasimodel construction:**
   - Start from each root type (containing the input concept)
   - Add witness types for unsatisfied existential demands (∃R.C)
   - After each addition, verify that the SAFE constraint network over the current type set is **disjunctive path-consistent**: for each pair of types, the domain is the SAFE set; arc-consistency propagation removes relations that have no support through intermediate types
   - By the **RCC5 patchwork property** (Renz & Nebel 1999), path-consistent disjunctive networks are globally satisfiable, making this check both **sound** (rejects only genuinely unsatisfiable configurations) and **complete** (accepts all satisfiable ones)
   - Backtrack if path-consistency fails; try alternative witness types
   - **Sibling compatibility check**: for each type with multiple demands (R₁,D₁),...,(Rₖ,Dₖ), verify that witnesses j₁,...,jₖ can be chosen jointly such that comp(INV[Rₘ], Rₘ') ∩ SAFE(jₘ, jₘ') ≠ ∅ for all pairs. When Rₘ ≠ Rₘ', the witnesses must be distinct elements even if they share the same type — the pairwise check is required. Same-type bypass is valid only when Rₘ = Rₘ' (one element serves both demands). Uses CSP with arc-consistency + backtracking.
6. Accept iff some root type leads to a valid quasimodel

#### Key design decisions

- **Three necessary conditions replace Q3/Q4.** The original conditions Q3/Q4 universally quantify over all safe relations, which is too strict. The replacement is three necessary conditions: (1) **disjunctive path-consistency** of the SAFE network; (2) **sibling compatibility** — joint witness assignment for co-demanded roles via CSP; (3) **role-path compatibility** — grandchild-grandparent connectivity through composition chains with iterative witness pruning. (1) and (2) are extractable from any model. **(3) is extractable only from tree models** — the check wrongly assumes that grandchild w is a fresh node, and fails to close the cycle when w may equal g via strong-EQ identification through a symmetric role. Consequently **UNSAT answers from this reasoner are sound only for concepts whose SAT-status is witnessed by a tree model**; for cyclic-via-symmetric-role SAT concepts the reasoner wrongly reports UNSAT. See the warning box in README for scope and fix status.

- **Deterministic type enumeration.** Closure concepts are sorted by string representation before building atoms. All frozenset iterations in the search use `sorted()`. This ensures the reasoner always produces the same type set regardless of Python's hash randomization.

- **Bottom-up construction avoids GFP non-monotonicity.** The original greatest-fixpoint type elimination is non-monotone: removing one type can make another supportable. This caused the algorithm to reject satisfiable concepts (e.g., C₁ from the paper). The constructive approach only checks consistency of types actually in the candidate quasimodel.

#### Test results

```
cd src
python3 alcircc5_reasoner.py
```

18 basic test cases plus a comprehensive stress test of **713 concepts** across seven categories (known SAT, known UNSAT, adversarial cross-role universals, systematic role-atom combinations, and random concepts of depths 2-4). **Zero correctness errors on this test set.** The sibling check correctly catches cross-role universal contradictions like ∃PP.(∀PPI.A) ⊓ ∃PPI.¬A (UNSAT: comp(PPI,PPI) = {PPI} forces the universal to fire on the sibling). *Known blind spot:* the test set does not include cyclic-via-symmetric-role SAT concepts such as the PO-loop pattern; on those the reasoner is known to wrongly report UNSAT.

#### Henkin tree extension test

[**`henkin_extension_test.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/henkin_extension_test.py) validates the Henkin construction by building actual tree models from quasimodel type sets. For each SAT concept, it:

1. Gets the quasimodel type set T from the reasoner
2. Builds a depth-4 Henkin tree, adding witnesses level by level
3. At each extension, computes the star network D(new, x) = comp(INV[R], ρ(parent, x)) ∩ SAFE(new_type, x_type) for all existing nodes x
4. Runs star arc-consistency and finds a consistent atomic assignment
5. Uses a **precomputed witness plan** (sibling-compatible assignment per type) with limited backtracking over alternative witnesses

**Result: zero failures for all basic tests across 12 hash seeds.** The future-flexibility ordering (PO > DR > PP > PPI) ensures cross-relations keep compositions wide at deeper tree levels. In the stress test, 8 Henkin failures occur at depths 2-3 for concepts that are satisfiable in cyclic models but whose tree unfoldings have cross-level composition conflicts — these are tree-model limitations, not reasoner bugs.

#### Limitations

- Exponential in closure size (enumerates all Hintikka types)
- Not optimized for large concepts; designed as a proof-of-concept
- The constructive search uses backtracking with depth bound, so may not find all satisfying quasimodels
- **Known incompleteness** on cyclic-via-symmetric-role SAT concepts (PO-loop pattern): the role-path compatibility check cannot close a chain g→R→j→S→g through a symmetric role, so witnesses that require such cycles are rejected. The decidability proof is unaffected.

### Pointers to other superseded papers and verification scripts

These pointers were in the README's file lists; the underlying papers/scripts remain in the repo but are not part of the current proof machinery.

#### GPT-5.4 Pro papers (profile-cached blocking series, superseded)

- [**`gpt/alcircc5_blocking_draft.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt/alcircc5_blocking_draft.pdf) -- Paper 1: Profile-cached global blocking, conditional on classwise normalization lemma ([source](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt/alcircc5_blocking_draft.tex))
- [**`gpt/alcircc5_blocking_revised.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt/alcircc5_blocking_revised.pdf) -- Paper 2: Self-correction — flat normalization false, introduces coherent predecessor blocks ([source](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt/alcircc5_blocking_revised.tex))
- [**`gpt/alcircc5_blocking_explicit_signatures.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt/alcircc5_blocking_explicit_signatures.pdf) -- Paper 3: Explicit depth-indexed signature construction, proves finite-index lemma (PDF only)
- [**`gpt/alcircc5_blocking_replay_final.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt/alcircc5_blocking_replay_final.pdf) -- Paper 4: Meet-semilattice approach, robust colorwise normalization — gap in blocked unraveling theorem ([source](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt/alcircc5_blocking_replay_final.tex))

#### GPT-5.4 Pro review correspondence (two-tier quotient)

- [**`review/review_closing_extension_gap_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/papers/review/review_closing_extension_gap_ALCIRCC5.pdf) -- GPT's review of Claude's companion paper: identifies algebraic error in Lemma 3.2 and counterexample to Theorem 5.5 ([source](https://github.com/lambdamikel/alcircc5/blob/master/papers/review/review_closing_extension_gap_ALCIRCC5.tex))
- [**`review2/response_to_two_tier_quotient_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/papers/review2/response_to_two_tier_quotient_ALCIRCC5.pdf) -- GPT's review of Claude's two-tier quotient paper: five objections against the decidability claim ([source](https://github.com/lambdamikel/alcircc5/blob/master/papers/review2/response_to_two_tier_quotient_ALCIRCC5.tex))
- [**`review2/response_to_gpt_review.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/papers/review2/response_to_gpt_review.pdf) -- Claude's response to GPT's first review (8 pages) ([source](https://github.com/lambdamikel/alcircc5/blob/master/papers/review2/response_to_gpt_review.tex))
- [**`review3/response_to_revised_two_tier_quotient_ALCIRCC5.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/papers/review3/response_to_revised_two_tier_quotient_ALCIRCC5.pdf) -- GPT's second review of two-tier quotient ([source](https://github.com/lambdamikel/alcircc5/blob/master/papers/review3/response_to_revised_two_tier_quotient_ALCIRCC5.tex))
- [**`review3/response_to_gpt_second_review.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/papers/review3/response_to_gpt_second_review.pdf) -- Claude's response to GPT's second review ([source](https://github.com/lambdamikel/alcircc5/blob/master/papers/review3/response_to_gpt_second_review.tex))
- [**`review4/response_to_latest_two_tier_revision.tex`**](https://github.com/lambdamikel/alcircc5/blob/master/papers/review4/response_to_latest_two_tier_revision.tex) -- GPT's third review of two-tier quotient
- [**`review4/response_to_gpt_third_review.pdf`**](https://github.com/lambdamikel/alcircc5/blob/master/papers/review4/response_to_gpt_third_review.pdf) -- Claude's response to GPT's third review (7 pages) ([source](https://github.com/lambdamikel/alcircc5/blob/master/papers/review4/response_to_gpt_third_review.tex))

#### Older computational verification scripts (quasimodel-era)

- [**`extension_gap_checker.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/extension_gap_checker.py) -- Exhaustive extension gap checker. Confirmed Q3-compatible configurations can fail (1,575 at m=3, 806,094 at m=4).
- [**`extension_gap_checker_v2.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/extension_gap_checker_v2.py) -- Tests existential Q3 vs universal Q3. Universal Q3 eliminates all failures through m=4.
- [**`q3_implies_q3s_check.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/q3_implies_q3s_check.py) -- Does Q3 imply Q3s? No (1,803 counterexamples at 3 types).
- [**`model_derived_q3s_fast.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/model_derived_q3s_fast.py) -- Result: 7,560/68,276 models produce DN networks violating Q3s. Confirms Q3s not extractable from models.

#### PP-kernel quotient investigation

- [**`pp_kernel_analysis.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/pp_kernel_analysis.py) -- Reflexive PP composition-consistency, PP-chain monotonicity and stabilization.
- [**`pp_kernel_quotient.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/pp_kernel_quotient.py) -- Tests disjunctive {PP,PPI} quotient: 6/15 two-type demand patterns are satisfiable; bidirectional demands fail.
- [**`pp_kernel_cycle_analysis.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/pp_kernel_cycle_analysis.py) -- Generates and validates 56 toy 2-type period descriptors.
- [**`gap_closing_verification.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/gap_closing_verification.py) -- Verifies algebraic facts: 0 failures across 164 two-element and 128 three-element configurations.

#### Extension gap root cause investigation scripts

- [**`self_absorption_analysis.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/self_absorption_analysis.py) -- Identifies comp(DR,PPI)={DR} as the unique asymmetric failure.
- [**`cross_subtree_investigation.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/cross_subtree_investigation.py) -- Ancestor projection strategy, self-safety theorem (S ∈ comp(S,S) for all S).
- [**`drpp_deep_analysis.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/drpp_deep_analysis.py) -- Modified profile-copy approach for DR+PP problematic case.
- [**`drpp_extension_investigation.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/drpp_extension_investigation.py) -- One-step extension solvability (45,528/45,528 pass).
- [**`profile_blocking_drpp.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/profile_blocking_drpp.py) -- Initial DR+PP profile-blocking investigation.

#### Triangle-type blocking investigation

- [**`triangle_closure_check.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/triangle_closure_check.py) -- Tests triangle-type blocking on 68,276 models. Zero genuine failures.
- [**`triangle_type_saturation_check.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/triangle_type_saturation_check.py) -- All three node types stabilize at k=2 (τ_A: 68 types, τ_B: 56 types, σ: 57 types).
- [**`profile_blocking_check.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/profile_blocking_check.py) -- Confirms node-identity-based profile blocking does NOT terminate.
- [**`tri_neighborhood_check.py`**](https://github.com/lambdamikel/alcircc5/blob/master/src/tri_neighborhood_check.py) -- Strengthened blocking condition also stabilizes, at k=3.

## Round-2 through round-6 review prose (moved from README on 2026-05-28)

The README's Latest News block grew to 17 detailed entries covering the
round-2 through round-6 review cycle (5-6 through 5-26).  After GPT-5.5's
round-7 review (2026-05-28) adopted occurrence-sensitive pair shapes as
the canonical labelling, all of the round-2 through round-6 material was
superseded.  The detailed prose is preserved here for the audit trail.

### Latest News entries 5-6-2026 through 5-26-2026 (archived)

- 5-28-2026: **GPT-5.5 round-7: pair-shape / incidence-tag architecture adopted as canonical.** GPT-5.5 published a [seventh formal review](papers/gpt5.5_final/formal_response_round6_review.pdf) ([LaTeX](papers/gpt5.5_final/formal_response_round6_review.tex)) of Claude's round-6 consolidated v2. Verdict: *"Round 6 is an important improvement, but the proof still does not stand as written."* Central architectural defect: in round-6, `lab(u,v) := L_Q(q(u), q(v))` with `L_Q(π, π) = EQ` collapses distinct laps of a blocking cycle into semantic equality, breaking the canonical certificate for `∃PP.⊤ ⊓ ∀PP.∃PP.⊤`. Five additional defects (D1–D5) and eight recommended repairs (R1–R8) listed. The defect is intrinsic to indexing labels by abstract position-symbol pairs and cannot be locally patched. **Adopted as canonical**: GPT-5.5's [round-7 no-automata proof sketch](papers/gpt5.5_final/repaired_split_forest_all_in_one_round7.pdf) ([LaTeX](papers/gpt5.5_final/repaired_split_forest_all_in_one_round7.tex), 14 pages), in which labels live on *pair shapes* `α(u,v) = (s_u, p_u, s_v, p_v, ι(u,v))` with incidence tags `ι ∈ {self, eq, up, down, side_R, front_R}`. Repeated blocked laps satisfy `ι ≠ self` and `ι ≠ eq`, so `ℓ_Q(α(u_i, u_j)) ≠ EQ`. Triple composition is verified on a finite triple-shape set Tri_Q. Twelve validity clauses (V1)–(V12) replace round-5/round-6's fifteen. Detailed companion: [`expanded_split_forest_full_details_proof.pdf`](papers/gpt5.5_final/expanded_split_forest_full_details_proof.pdf) ([LaTeX](papers/gpt5.5_final/expanded_split_forest_full_details_proof.tex), 28 pages). Independent witness: [`split_forest_automata_decidability_proof_detailed.pdf`](papers/gpt5.5_final/split_forest_automata_decidability_proof_detailed.pdf) ([LaTeX](papers/gpt5.5_final/split_forest_automata_decidability_proof_detailed.tex), 21 pages, parity-tree-automata route). Claude's [round-7 audit/response](papers/gpt5.5_final/claude_round7_audit_response.pdf) ([LaTeX](papers/gpt5.5_final/claude_round7_audit_response.tex), 9 pages) maps round-6 (G1)–(G6) and round-7 (D1)–(D5) to their resolutions, and three self-contained pure-stdlib verification scripts ([`wp7_selfcontained_side_witness.py`](verification/python/wp7_selfcontained_side_witness.py), [`wp8_round7_blocking_chain.py`](verification/python/wp8_round7_blocking_chain.py), [`wp9_round7_split_copies.py`](verification/python/wp9_round7_split_copies.py)) corroborate the three central stress concepts: comparable side witnesses, blocking-not-equality, and split copies for incomparable proper superparts. Claude's round-5 and round-6 manuscripts are marked superseded but retained as the historical audit trail.
- 5-26-2026: **Round-6 internal-coherence pass on the consolidated v2: 39-page paper closes G1--G6.** *(Superseded 5-28-2026 by GPT-5.5's round-7. Retained as audit trail.)* GPT-5.5 published a [sixth formal review](papers/gpt5.5_round2/formal_review_consolidated_v2_latest.pdf) ([LaTeX](papers/gpt5.5_round2/formal_review_consolidated_v2_latest.tex)) of the 36-page consolidated v2. Verdict: *"Substantial progress, but the decidability proof remains open as a formal manuscript."* Six internal-coherence gaps identified, not merely stylistic. Closed in [`papers/gpt5.5_round2/repaired_split_forest_no_automata_proof_v2_consolidated_round6.pdf`](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof_v2_consolidated_round6.pdf) ([LaTeX](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof_v2_consolidated_round6.tex)), 39 pages: **G1** Side-interface legality lemma rewritten as a stratified construction with a stratum forest, nested strata V_w for PP/PPI-comparable side witnesses, and an explicit "round-4 flat-frontier proof was invalid" remark; **G2** committed to the per-position (SC4') route — `Quotient lifting` rewritten to use L_Q directly and renamed to *"Concrete triple labels satisfy (F3), via L_Q"*; the patchwork theorem proof reworked to derive (F3) on each concrete triple from (V11) without any per-triple mosaic; **G3** new validity clause (V15) (Cross-pair universal safety) added: for every declared overlap cross-pair (p,q) with label R, if ∀ R.D ∈ τ(p) then D ∈ τ(q); `Universal-propagation preservation` lemma reproved via (V15); **G4** lasso construction restated on the *extended* profile Π (not the complete profile Π); pumping step uses the half-open [u_i, u_j) cycle word throughout; **G5** cubic m(n) = O(n³) replaced everywhere by the modal-depth recurrence m_*(C₀) = m(md(C₀)), enumeration proof updated to check (V1)--(V15), grammar updated to track the full stratum-forest object V_M = (Strat_M, Subsrc_M) instead of Vrt_M ⊆ P; **G6** new self-contained verification script [`verification/python/wp7_selfcontained_side_witness.py`](verification/python/wp7_selfcontained_side_witness.py) uses only the Python standard library to build the three-element abstract RCC5 frame, verify JEPD/inverse/strong-EQ/composition table, and confirm C_side is SAT at x. Certificate validity check now has 15 clauses (V1)--(V15) plus (M6'). B(C₀) ≤ 2^(2^(p(n))) preserved as an effectively computable bound.
- 5-23-2026: **Consolidated v2 paper: all round-5 repairs inlined into a single 36-page document.** *(Superseded 5-28-2026 by GPT-5.5's round-7. Retained as audit trail.)* [`papers/gpt5.5_round2/repaired_split_forest_no_automata_proof_v2_consolidated.pdf`](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof_v2_consolidated.pdf) ([LaTeX](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof_v2_consolidated.tex)), 36 pages, is the consolidation of the 31-page round-4 paper with the two Claude-drafted round-5 deltas (the (M6') v2 paper and the items-4-to-8 paper). All eight round-5 repairs are inlined as one self-contained statement: the recursive verticalization (M6') in §5; the explicit abstract pair-label function L_Q and validity clause (V11) for the composition table on T_Q in §5; the strong overlap-compatibility (O3') and validity clause (V12); the joint equality validity clause (V13) replacing assumption (A4); the half-open [i,j) cycle convention; the uniform-representative validity clause (V14) with the global regularization lemma; the side-width recurrence over modal depth replacing the polynomial m(n) = O(n³) bound; and the prover-alignment note. The three earlier documents (round-4 paper, v2 (M6') delta, items-4-to-8 delta) remain in the repository as the historical audit trail. Compiles cleanly to 36 pages with no warnings or undefined references.
- 5-23-2026: **Items 4--8 delta paper closes the remaining round-5 items.** *(Superseded 5-28-2026 by GPT-5.5's round-7. Retained as audit trail.)* [`papers/gpt5.5_round2/repaired_split_forest_no_automata_proof_items4to8.pdf`](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof_items4to8.pdf) ([LaTeX](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof_items4to8.tex)), 12 pages, addresses the remaining five mathematical items from round 5. **Item 4 (non-circular patchwork):** explicit abstract pair-label function L_Q: Pos_Q² → Base declared as certificate data, plus a new validity clause (V11) requiring the RCC5 composition table to hold on every triple in T_Q. (SC4) is replaced by a per-position version (SC4') that no longer requires per-triple mosaic coverage; the patchwork theorem becomes a direct consequence of (V11). **Item 5 (overlap amalgamation):** strong overlap compatibility (O3') requires a single declared cross-label function L₁₂^cross: (P₁ P₀) × (P₂ P₀) → Base compatible with all overlap nodes and all mixed triples simultaneously. New validity clause (V12) declares this function. **Item 6 (joint equality validity clause):** (A4) from the round-4 typed-EQ quotient theorem is promoted to an explicit (V13) requiring a declared joint witness w_E^(R,D) per equality class E per ∃ R.D. Lemma proves (V13) implies (A4). **Item 7 (half-open cycle convention):** the request-fulfilled repetition lemma is restated with the half-open [i,j) cycle convention; u_j is identified with the next lap's u_i^(ℓ+1) at the profile level only. The endpoint case (witness at u_j in the original path) is handled by the next-lap occurrence u_i^(ℓ+1), since profiles include closure types. **Item 8 (global finite regularization):** uniform representative selection lemma (V14) declares one (C_σ, cyc_σ) per extended profile σ ∈ Σ once, then uniformly substitutes across every infinite vertical ray. The finite extended-profile alphabet bounds the substitution data to |Σ| ≤ |Σ| · 2ⁿ. Combined with the v2 (M6') paper, all eight round-5 items are now addressed. The certificate validity check has 14 clauses (V1)--(V14) plus (M6') instead of round-4's (V1)--(V10); B(C₀) ≤ 2^(2^(p(n))) for a computable polynomial p is preserved.
- 5-23-2026: **v2 delta paper drafts the (M6') recursive-verticalization repair from the round-5 review.** *(Superseded 5-28-2026 by GPT-5.5's round-7. Retained as audit trail.)* [`papers/gpt5.5_round2/repaired_split_forest_no_automata_proof_v2.pdf`](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof_v2.pdf) ([LaTeX](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof_v2.tex)), 14 pages, is a focused delta to the 31-page round-4 paper. It replaces the flat verticalization Vrt⊆ P with a finite *stratum forest* in which each selected DR/PO side-witness may itself open a local vertical stratum carrying its own selected PP/PPI ancestors. The four sub-clauses of (M6) become (M6'.a)--(M6'.d), with the key change in (M6'.b) (containment labels are co-vertical: justified by *some* stratum, not necessarily the root) and (M6'.d) (only the *residual* sibling frontier is restricted to DR/PO). Lemma~7.1 (Vertical realisation of PP/PPI pairs) is restated as Lemma~4.1 with the recursive case analysis inside a single stratum; the Subcase (ii.e) argument carries over verbatim once "common stratum" replaces "root stratum". Validity clauses (V3')/(V4')/(V5')/(V9.Eb') are universally quantified over strata. The polynomial side-width m(n) = O(n³) is replaced by a recurrence m(d{+}1) = 1 + n³(1+k_Mate+k_bd) + n³ m(d) over modal depth, giving m(md(C₀)) ≤ (n³{+}1)^(md(C₀)+1)(1+k_Mate+k_bd) — effectively computable, no longer polynomial, which matches round-5 item~9. The double-exponential bound B(C₀) ≤ 2^(2^(p(n))) is preserved. The v2 paper closes round-5 items 2, 3, and 9 (side-interface verticalization, stress test added, polynomial claim dropped); items 4--8 are orthogonal editorial passes that the v2 architecture is the natural setting for. A worked v2 certificate for the round-5 stress concept ∃DR.(A ⊓ ∃PP.B) ⊓ ∃DR.B is constructed in §6 of the v2 paper and verified against all four (M6') sub-clauses.
- 5-22-2026: **GPT-5.5 fifth review of the 31-page repaired proof — "major progress, but not yet a watertight decidability proof".** GPT-5.5 published a fifth formal review ([PDF](papers/gpt5.5_round2/formal_review_progress_paper.pdf), [LaTeX](papers/gpt5.5_round2/formal_review_progress_paper.tex)) of the 31-page all-in-one repaired proof. Verdict: *"credible architecture with several remaining formal proof obligations."* The improvements are acknowledged (witness thinning, generated covers, occurrence-level equality cleanly separated from blocking, port-indexed mate clusters, request-fulfilled cycles strengthened). Eight repairs recommended; the most urgent is mathematical: **(M6) verticalization discipline is too strong** — it forbids non-vertical PP/PPI relations among side-witness positions, but such relations occur in satisfiable witness-generated models. Concrete stress concept: `∃DR.(A ⊓ ∃PP.B) ⊓ ∃DR.B`. All three of our reasoners (cover-tree tableau, baseline and cycle-aware quasimodel) report **SAT** on this concept (see [`verification/python/wp7_side_witness_stress.py`](verification/python/wp7_side_witness_stress.py)), corroborating the review. Other remaining items: (i) non-circular order in the mosaic patchwork proof (define abstract triples and a finite composition-table check *before* invoking patchwork); (ii) strengthen overlap amalgamation to a single cross-label assignment compatible with all overlap nodes and mixed triples; (iii) quote Renz–Nebel exactly; (iv) promote joint equality-witness compatibility from assumption (A4) to an explicit validity clause; (v) rewrite the request-fulfilled cycle lemma with a half-open `[i,j)` convention and explicit endpoint case; (vi) add a global finite regularization lemma covering all infinite vertical rays uniformly; (vii) drop the `m(n) = O(n³)` polynomial claim until side-context saturation is specified — an effectively computable bound is enough. The TeX/PDF mismatch the reviewer flagged is *not* present in our repo — `papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.tex` does compile to the 31-page PDF; the reviewer's bundle had stale source. **Status:** filed; waiting for GPT-5.5 to issue a corresponding repair pass (or human-expert input).
- 5-21-2026: **GPT-5.5 fourth review — all six gaps (G1–G6) and all five smaller issues (S1–S5) addressed; main proof now 31 pages.** GPT-5.5 published a fourth formal review ([PDF](papers/gpt5.5_round2/formal_review_latest_paper.pdf), [LaTeX](papers/gpt5.5_round2/formal_review_latest_paper.tex)) of the self-contained 23-page proof from the 5-21-2026 inlining (entry below). Verdict: *"promising repaired architecture, but not yet a complete formal decidability proof"* — six load-bearing gaps in the certificate semantics, the occurrence-level equality-port construction, the request-closed blocking lemma, and the support-closed mosaic/patchwork argument. Each gap was repaired in a dedicated commit: **G1** (commit `a5857a3`) adds the verticalization discipline (M6) to Definition 5.1, stratifying mosaic positions into vertical (source + EQ mates + selected PP/PPI witnesses) and sibling-frontier (DR/PO witnesses + boundary nodes), with a new Lemma 7.1 (*Vertical realisation of PP/PPI pairs*) lifting (M6) from mosaics to U(Q); **G2** (commit `f171456`) replaces state-level `Mate_Q(s)` with explicit port- and context-indexed mate clusters `Mate_Q(C, s, p)` attached to context schemes, so every occurrence comes with its synchronised companion occurrences by construction; **G3** (commit `bd3c2e4`, applied earlier in the day) renames Lemma 7.2 to *Request-fulfilled repetition lemma* with explicit (F1) + (F2a/F2b) structure proving strict cyclic fulfillment with lookahead ≤ 2(j-i); **G4** (commit `e8f046d`) formally constructs the abstract triple graph `T_Q` with explicit cardinality bounds (`|Pos_Q| ≤ 2|S|·(n+1)·|Ctx_Q|`, `|Trip_Q| ≤ |Pos_Q|³·125`) and a quotient-lifting lemma; **G5** (commit `4800385`) gives the concrete five-component construction of side interfaces `Side(u)` together with the polynomial-width bound `1 + n³ + 3n² + 3n` and an (M1)–(M6) legality lemma; **G6** (commit `0e8ba02`) makes `B(C_0) = 2^(2^(p(n)))` grammar-first by replacing the informal context-width prose with the explicit cubic `m(n) = O(n³)` from Lemma 4.4. The smaller issues **S1** (identity in mate reachability), **S2** (port-level strict-reachability exclusion in V9.Eb), **S3** (stratification reflection in support closure), **S4** (PP/PPI semantic-successor coverage in soundness), and **S5** (split completeness Lemma into four independent lemmas) are addressed in commit `411fbe0`. The [main proof](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.pdf) ([LaTeX](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.tex)) now stands at **31 pages**, fully self-contained, with every gap closed by explicit construction and verifiable lemma.
- 5-21-2026: **Addendum content inlined into the main repaired proof — single self-contained 23-page paper.** The four obligations closed in the 5-14-2026 addendum (closure and witness thinning, support-closed mosaic patchwork, standalone typed-≡_EQ quotient theorem, finite certificate grammar + enumeration bound) have been lifted directly into the [main repaired proof](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.pdf) ([LaTeX](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.tex)), which now stands at 23 pages: **§3.2** carries an explicit frame-inheritance lemma and a full structural induction over Cl(C₀) in NNF (atomic, Boolean, existential, and universal-via-NNF-complement cases), closing the (C2) closure / witness-thinning obligation in the main text; **§4.4–§4.6** carry the Renz–Nebel base case, overlap amalgamation, universal-propagation and typed-≡_EQ compatibility (Lemmas 4.3–4.5), and the support-closed mosaic patchwork theorem (Thm 4.6), discharging item (4) in the body of the proof; **§6.2** carries the standalone typed-≡_EQ quotient theorem with its six load-bearing assumptions (A1)–(A6) and four preservation properties (JEPD, strong equality, RCC5 composition, closure-formula truth), discharging item (5); **§8.1–§8.3** carry the explicit grammar of certificate components, component-wise polynomial bounds, and derivation of B(C₀) = 2^(2^(p(n))), discharging item (6). **§7.2** additionally expands the request-closed lasso lemma from the original 16-page proof with an explicit checkpoint structure — pending set, extended profile Π, infinite checkpoint sequence by pigeonhole, and a 5-step structured proof of the request-cycle pumping lemma (request-closure, pumping, universal preservation, existential preservation). The separate [technical addendum](papers/gpt5.5_round2/claude_verification_addendum.pdf) is retained as a more leisurely 14-page exposition of the same material but is no longer required for the main proof to be self-contained.
- 5-20-2026: **DL 2026 rejection — submission, three reviews, and analysis now public.** The DL 2026 Extended Abstract on this work was rejected (verdicts 33A Reject, 33B Accept, 33C Reject), with decision escalated to the DL Steering Committee. The full rejected submission (with post-submission typo corrections, substantive content unchanged), the three reviews, and a detailed point-by-point response are now in [`dl2026-rejected/`](dl2026-rejected/). See also the [**open letter to the DL 2026 Committee**](dl2026-rejected/open_letter.md) and the [**DL 2026 submission and rejection section**](#dl-2026-submission-and-rejection) below, which lays out why I (Wessel) believe the paper was rejected on the wrong basis — guidelines-violating weighting of optional-appendix defects, strawman framing, echoed epistemic disclaimers used as ammunition, and no engagement with the actual thesis.
- 5-14-2026: **Technical addendum closes items 2 + 4–6 at paper level — every obligation is now PASS or CLOSED at paper level.** Following the v2 response (items 1–3), the [**technical addendum**](papers/gpt5.5_round2/claude_verification_addendum.pdf) (14 pages, [LaTeX](papers/gpt5.5_round2/claude_verification_addendum.tex)) discharges the remaining items at the paper level: **(4) support-closed mosaic patchwork theorem** — Theorem 3.6 cites Renz–Nebel 1999 and verifies its hypotheses (M1)–(M3) for the manuscript's mosaic family, with overlap amalgamation (Lemma 3.3), universal-propagation preservation (Lemma 3.4), and typed-≡_EQ compatibility (Lemma 3.5) covering the two non-relational obligations beyond the classical patchwork; **(5) standalone typed-≡_EQ quotient lemma** — Theorem 4.7 lists all six load-bearing assumptions in one place (equivalence, vertical separation, type rigidity, joint witness obligations, quotient-compatible pair labels, sibling-mosaic agreement on ≡_EQ-endpoints) and proves the four preservation properties (JEPD, strong equality, RCC5 composition, closure-formula truth); **(6) finite certificate grammar and enumeration bound** — §5 gives an explicit grammar with coarse polynomial bounds on every component (closure types, ports, parent/child slots, request summaries, mosaics, blocked graph size), deriving B(C₀) = 2^(2^(p(n))) as a mathematical consequence (Lemma 5.2); **(2) closure and witness thinning** — supplementary §6 expands the compressed Lem. 3.3 of the repaired proof with an explicit frame-inheritance lemma (Lemma 6.1: (F1)–(F3) and strong-EQ all carry over to the induced sub-frame) and a full induction over Cl(C₀) in NNF (Theorem 6.2) covering atomic, Boolean, existential, and universal cases — the universal case explicitly using NNF-complement closure to extract a selected ∃R.¬D witness from W. After the addendum, the paper-level obligation table reads: C1 PASS, **C2 CLOSED (paper)**, C3 PARTIAL→PASS, **C4/C7/C8 CLOSED (paper)**, C5/C6 PASS. The Lean stack L1–L7 remains the only open verification work, in priority order L1, L3, L4, L6, then L2/L5/L7. *(Update 5-21-2026: addendum content has since been inlined directly into the main repaired proof — see the 5-21-2026 entry above.)*
- 5-14-2026: **GPT-5.5 third review — verdict moderated; v2 response addresses items 1–3.** GPT-5.5 published a third formal review ([PDF](papers/gpt5.5_round2/formal_review_claude_latest_response.pdf), [LaTeX](papers/gpt5.5_round2/formal_review_claude_latest_response.tex)) of Claude's updated verification response, with revised verdict: *"promising and substantially strengthened verification evidence; no reported bounded counterexample; several proof-critical obligations remain open."* The review identifies six items: (1) reproducibility — the 10-test bundle accompanying v1 did not match v1's text claiming 24 tests, blocking independent verification; (2) the strengthened C_AB^inc formula was not specified in v1; (3) the pure request-closure test was claimed but not isolated from V1/mate-route rejections; (4) the support-closed mosaic patchwork theorem remains a test, not a theorem; (5) the standalone typed-≡_EQ quotient lemma is manuscript-only; (6) the finite certificate grammar and enumeration bound need explicit derivation. The [**v2 response**](papers/gpt5.5_round2/claude_verification_response_v2.pdf) (14 pages, [LaTeX](papers/gpt5.5_round2/claude_verification_response_v2.tex)) closes items 1–3: it points to commit `1f9b3b4` for the reproducible bundle, gives the NNF formula C_AB^inc := ∃PP.A ⊓ ∃PP.B ⊓ ∀PP((¬ A ⊔ (¬ B ⊓ ∀PP.¬ B ⊓ ∀PPI.¬ B)) ⊓ (¬ B ⊔ (¬ A ⊓ ∀PP.¬ A ⊓ ∀PPI.¬ A))) with a written incomparability lemma and a single-parent infeasibility proof, and isolates the pure request-closure test (V1 clean, V4 sole rejection) from the earlier WP5 cycle test. The obligation table is downgraded accordingly: C5/C6 remain PASS (computational) with explicit lemmas; C2/C4/C7/C8 are reclassified as PARTIAL or OPEN pending a deferred technical addendum addressing items 4–6.
- 5-13-2026: **GPT-5.5 verification.zip review — non-LEAN gaps closed.** GPT-5.5 published a third formal review ([PDF](papers/gpt5.5_round2/formal_response_verification_zip_review.pdf), [LaTeX](papers/gpt5.5_round2/formal_response_verification_zip_review.tex)) of the WP1–WP6 verification campaign, identifying five substantive gaps: §3.2 vertical-only checker (no DR/PO mosaic V2/V6/V7/V8), §3.4 weak multiple-superpart stress, §3.5 request-cycle local type-clash only, §3.6 bounded mosaic tests only at arity 3, §3.7 oracle scope framing. Two cheap wins (strengthened C_AB^inc and pure request-closure) were closed in an earlier pass (commit `176143f`). This pass closes the four remaining non-LEAN items: **§3.2** — `certificate_checker.py` extended with a `mosaics` field and six DR/PO certs covering V2 (typed relation-safety), V6 (existential discharge), V7 (universal propagation), V8 (M3 triple consistency); **§3.5** — four occurrence-level distinction certs (two-state PP cycles with/without cross-cycle eq-ports; PP-chain sharing λ; eq across distinct λ) confirm V9.Ea and V9.Eb; **§3.6** — `mosaic_closure_search.py` extended with arity-4 tests F (atomic enumeration: 916/4096 (M3)-consistent 4-networks, 7 need n=6, all realize at n ≤ 6) and G (overlap amalgamation: 427/427 overlap-compatible triangle pairs amalgamate); **§3.7** — WP3 reframed in [`claude_verification_response.tex`](papers/gpt5.5_round2/claude_verification_response.tex) as *bounded counterexample search*, not as evidence for the infinite-unfolding theorem of Section 5 of the repaired proof. Final: cert checker 24/24 PASS (was 14/14), mosaic search PASS with arity-4 patchwork confirmed. The Lean stack (L1–L7, §3.1/§3.3/§3.4) remains the only open verification work.
- 5-12-2026: **GPT-5.5 round-2 review supersedes v2.1; repaired proof adopted as current best statement; Claude-side verification complete.** GPT-5.5 published a second formal review ([PDF](papers/gpt5.5_round2/formal_review_latest_v21.pdf), [LaTeX](papers/gpt5.5_round2/formal_review_latest_v21.tex)) of [completeness extraction v2.1](papers/completeness_extraction_ALCIRCC5_v2.pdf) that identifies **eight critical structural gaps (G1–G8)**, of which three are genuinely load-bearing: (G1) profile-level equality ports contradict vertical separation on self-loops via the M1+M7 reflexivity chain; (G3) the mate construction forces all mates to share a single semantic parent, refuted by a two-mate stress formula C_AB requiring different parents; (G4) the rootless orientation is incompatible with the depth-from-u_* projection used in the proof. Alongside the review, GPT-5.5 produced a [repaired proof](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.pdf) (16 pages, [LaTeX](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.tex)) that fixes all three load-bearing gaps via **occurrence-level equality** (u ≡_EQ v ⇔ orig(u) = orig(v), not port-equality on profiles), **mates with different parents**, and **request-closed cycles** in place of ω-acceptance; the result is a self-contained no-automata decidability proof with 10 finite-checkable validity conditions (V1)–(V10) and a coarse bound B(C₀) = 2^(2^(p(n))). **Decision (Wessel + Claude):** v2.1 is **marked superseded**; the GPT-5.5 repaired proof is adopted as the **current best statement** of the decidability argument. Claude's contribution shifts to **verification**, per GPT-5.5's [verification-recommendations document](papers/gpt5.5_round2/verification_recommendations_for_claude.pdf): six Python work packages (WP1–WP6) and seven Lean targets (L1–L7) cross-checking the repaired proof's combinatorial claims. **WP1–WP6 all complete; all PASS, no counterexample found** — four Python scripts under [`verification/python/`](verification/python/) cover all six work packages (WP4 multiple-superpart C_AB stress is folded into WP2; WP5 request-closed blocking-cycle tests are folded into WP2/WP3): WP1 confirms GPT-5.5's RCC5 composition table (repaired proof, lines 99–114) matches brute-force enumeration exactly, all 25 cells; WP2's certificate-soundness fuzzer accepts the G1/G3/G4 fixes (C_AB accepted with two different parents, C_up accepted under occurrence-level equality); WP3's small-model oracle realises C_AB at n=3 and correctly reports no finite model for infinite-only SAT concepts; WP6's (M1)–(M5) + (SC1)–(SC4) mosaic closure search finds no counterexample to the patchwork lemma. Output logs under [`verification/reports/`](verification/reports/). The Lean targets L1–L7 are not yet attempted. See the [Verification implementation section](#implementation-verification-of-the-repaired-proof-wp1-wp6) and [`verification/README.md`](verification/README.md) for the per-script summary. See [Round-2 review and repaired-proof adoption section](#round-2-review-and-repaired-proof-adoption-may-2026) below.
- 5-6-2026: **Completeness extraction v2.1** *(superseded by 5-12-2026 round-2 review)* ([PDF](papers/completeness_extraction_ALCIRCC5_v2.pdf), [LaTeX](papers/completeness_extraction_ALCIRCC5_v2.tex)) discharges *all six* remaining proof obligations from GPT-5.5's [v2 review](papers/gpt5.5/formal_response_v2_review.pdf): (O1) blocking-vs-EQ separation — typed-EQ colour replaced by an *explicit finite equality relation* `≡_{EQ,Q}` on declared *equality ports*, with a vertical-separation axiom forbidding `≡_{EQ,Q}` along strict PP/PPI-paths and a new lemma proving blocking ⇏ semantic EQ; (O2) EQ-aware reachability discharge — both existential and universal PP/PPI propagation now quantify over `Mate(σ)` instead of a single occurrence, handling the multiple-incomparable-upward-witness stress formula `C_{AB}`; (O3) EQ-modality normalization — a preprocessing lemma eliminates `∃EQ.D` and `∀EQ.D` (sound under strong EQ semantics); (O4) finite mosaic arity bound — a locality theorem establishes the effective constant `N(C₀) = 5`: every mosaic axiom (M1)–(M7) is ≤ 3-local, every support-closure operation (SC1)–(SC4) is ≤ 5-local, and by patchwork [Renz–Nebel 1999] a labelled complete graph of any arity is in a support-closed descriptor iff every sub-network of arity ≤ 5 is, with certificate enumeration bounded by `|E_d|⁵ · |Base|^{C(5,2)}`; (O5) DR/PO side-context witness lemma — every DR/PO witness placed by the witness policy lives in a bounded side context `Side(u,v)` of size ≤ 5, and the realized mosaic on that context satisfies all (M1)–(M7), all relation-safety, all universal-firing, and all RCC5 composition constraints at the interface; (O6) simultaneous eventuality realization — a canonical-unfolding theorem shows the split tree `T` from the witness-generated submodel is itself a concrete realization of `U(Q)` in which all PP/PPI eventualities at all occurrences are realized simultaneously (SR1: PP via the ultimately periodic parent walk, SR2: PPI via child multiplicity, SR3: universal propagation via mate-aware reachability), with patchwork ensuring a coherent atomic RCC5 refinement. With all six obligations discharged, the revised proof closes the completeness extraction without remaining acknowledged gaps. v2.1 is 31 pages.
- 5-6-2026: **Sibling-interface paper v2** ([PDF](papers/trees/sibling_interface_descriptors_ALCIRCC5_v2.pdf), [LaTeX](papers/trees/sibling_interface_descriptors_ALCIRCC5_v2.tex)) brings the second of the two argument-bearing papers up to v2. GPT-5.5's review also touched the sibling-interface paper itself (its Def 1.5 ambient-root assumption, its Def 1.7 witness-menu treatment of PP/PPI, and its Thm 1.20 proof sketch). The v2 sibling paper preserves Thms 1.17–1.19 (soundness) verbatim, reinterprets Def 1.5 to allow parent self-loops (no ambient root, generated witness-cover edges), discharges PP/PPI eventualities by reachability over the parent graph instead of via the witness menu, and replaces the defective Thm 1.20 sketch with a citation to v2 completeness extraction. The decidability argument now stands on two v2 papers: sibling v2 (soundness, by Claude, 10 pages) + completeness extraction v2 (completeness, by Claude, 31 pages, v2.1). Both v1 papers are retained as superseded.
- 5-6-2026: **Completeness extraction v2** ([PDF](papers/completeness_extraction_ALCIRCC5_v2.pdf), [LaTeX](papers/completeness_extraction_ALCIRCC5_v2.tex)) responds to the GPT-5.5 review. The review found two structural defects in v1: (1) the Hasse construction for the cover-tree breaks on infinite PP-chains (e.g. `C↑ ≡ ∃PP.⊤ ⊓ ∀PP.∃PP.⊤`), and (2) the C5 triple-coherence proof conflates witnesses across the three pairs. v2 repairs both with seven concrete fixes: witness-generated submodel reduction, generated cover edges (relative to the chosen witness set, not Hasse covers), containment orientation, parent self-loops to absorb infinite PP-chains, support-closed mosaics in place of raw pair tables, an explicit typed-EQ congruence axiom, and reachability discharge for PP/PPI eventualities (no Büchi machinery). The README, [overview paper](papers/overview_ALCIRCC5.pdf), and DL 2026 abstract appendix all updated to point at v2 (v1 marked superseded). GPT-5.5's own automata-route repaired proof and review materials are archived under [`papers/gpt5.5/`](papers/gpt5.5/). See the [dedicated section below](#gpt-55-review-and-v2-completeness-extraction-may-2026).
- 5-5-2026: Copilot created [another decidability

### Round-2 review and repaired-proof adoption section (archived from README)

### Round-2 review and repaired-proof adoption (May 2026)

A week after v2.1, GPT-5.5 produced a [second formal review](papers/gpt5.5_round2/formal_review_latest_v21.pdf) identifying **eight structural gaps (G1)–(G8)** in v2.1; three are load-bearing:

- **G1 — profile-level equality ports vs. vertical separation.** v2.1 defines ≡_EQ,Q at the profile level; M1 + M7 force reflexivity, vertical separation forbids ≡_EQ,Q along strict PP/PPI paths, and the two clash on PP self-loops (which v2.1 allows to absorb infinite PP-chains). No consistent reading.
- **G3 — multiple upward PP witnesses with different parents.** v2.1's mate class Mate_Q(σ) forces a single semantic parent; the stress formula C_AB ≡ A ⊓ B ⊓ ∃ PP.A ⊓ ∃ PP.B ⊓ ∀ PP.(A → ¬ B) ⊓ ∀ PP.(B → ¬ A) requires two mate occurrences with different parents.
- **G4 — rootless orientation vs. depth-from-u_* projection.** The simultaneous-realization lemma silently assumes u_* is a root, but the rootless orientation allows proper-superpart occurrences for which depth is undefined.

GPT-5.5's [repaired proof](papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.pdf) (16 pages at round 2) fixes all three: (i) **occurrence-level equality** (u ≡_EQ v ⇔ orig(u) = orig(v), killing the M1/vertical-separation clash); (ii) **mates with different parents** via a port-equivalence redefinition of Mate_Q(σ); (iii) **request-closed cycles** in the rank-d quotient in place of ω-acceptance. The proof formulates **ten finite-checkable validity conditions (V1)–(V10)** on rank-d split-forest certificates and gives the coarse bound B(C₀) = 2^(2^(p(n))).

**All-in-one fourth-review proof (31 pages, May 2026).** After two further rounds of adversarial review by GPT-5.5, the repaired proof has grown into a single self-contained document that bundles soundness, completeness, and the finite enumeration argument. Rounds 3 and 4 added four structural layers absent from the round-2 version: (i) a **verticalization discipline** (axiom (M6) on mosaics) that separates each context into a *vertical stratum* (source + EQ mates + selected PP/PPI witnesses) and a *sibling frontier* (DR/PO witnesses + boundary nodes), preventing the strata from interfering when validity is checked; (ii) **port-indexed mate clusters** Mate_Q(C, s, p) ⊆ S × Port(s') that attach mate equivalences to contexts and ports rather than to bare positions, with validity conditions (V3), (V4), (V5), and (V9.Eb) restated in this port-indexed form; (iii) an **explicit abstract triple graph** T_Q with cardinality bounds |Pos_Q| ≤ 2|S|·(n{+}1)·|Ctx_Q| and |Trip_Q| ≤ |Pos_Q|³ · 125, replacing the round-2 informal triple bookkeeping; and (iv) a **side interface** Side(u) with an explicit five-item composition and polynomial width bound m(n) = O(n³). The certificate-space bound B(C₀) = 2^(2^(p(n))) is now derived *grammar-first* from these component bounds rather than asserted top-down, and validity is finite-graph checkable, so ALCI\_RCC5 concept satisfiability reduces to a finite enumeration. All six Python work packages WP1–WP6 (below) cross-check the finite combinatorial content of this all-in-one version.

**Decision (Wessel + Claude):** v2.1 is marked superseded; the repaired proof is adopted as the current best statement; Claude's contribution shifts to **verification**.

**Verification status.** All six Python work packages WP1–WP6 under [`verification/`](verification/) **PASS** (WP4 and WP5 folded into WP2/WP3): WP1 (RCC5 composition table — exhaustive subset enumeration matches GPT-5.5's table exactly, 25/25 cells); WP2 ((V1)/(V3)/(V4)/(V5)/(V9)/(V10) certificate fuzzer — C_AB accepted with two different parents, rejected when forced into a single parent); WP3 (small-model SAT/UNSAT oracle — C_AB realised at n=3); WP6 ((M1)–(M5) + (SC1)–(SC4) mosaic closure search — Renz–Nebel patchwork holds on triangles, no counterexample to the patchwork lemma). The full prose of the Round-2 review and verification work is preserved in [OUTDATED.md](OUTDATED.md); the Lean targets L1–L7 are not yet attempted.

A self-contained [verification response paper](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt5.5_round2/claude_verification_response.pdf) (9 pages, [LaTeX](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt5.5_round2/claude_verification_response.tex)) follows GPT-5.5's prescribed final-report structure (summary verdict, proof-obligation table over the nine Section-3 audits, executable artifacts WP1–WP6 with the WP4/WP5 folding rationale, Lean artifacts (none yet), counterexamples (none), gaps mapped against criteria C1–C8, recommended manuscript edits) and is intended to be fed back to GPT-5.5 without repo access.

### Twelfth approach: GPT-5.5 automata-flavored split-forest proof — ALTERNATIVE ROUTE (archived from README)

**This proof independently establishes the decidability of ALCI\_RCC5** — a second, self-contained proof produced by GPT-5.5 about a week before the no-automata round-2 proof. Same target theorem as the eleventh approach, same overall split-forest architecture, but a different discipline for vertical PP/PPI eventualities.

**Paper.** [`papers/gpt5.5/ALCIRCC5_coherent_generated_split_forest_decidability.pdf`](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt5.5/ALCIRCC5_coherent_generated_split_forest_decidability.pdf) (May 2026, [LaTeX](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt5.5/ALCIRCC5_coherent_generated_split_forest_decidability.tex)) — *A Coherent Generated Split-Forest Decidability Proof for ALCI\_RCC5*. Proves Soundness (Thm 7.x), Completeness (Thm 8.x), and Decidability (Thm 9.x) in their entirety over strong abstract RCC5 frames.

**Shared structure with the eleventh approach.** Witness-generated submodel reduction, containment-oriented split forest with weak-EQ split copies, generated PP/PPI cover edges (not Hasse covers of an arbitrary order), sibling interfaces recorded by finite support-closed mosaics with {DR, PO}-only open cross-relations, finite-prefix patchwork via König's lemma, typed-EQ congruence quotient to recover strong-EQ semantics.

**Key difference: vertical eventuality discipline.** The two routes diverge on how PP/PPI eventualities along infinite vertical branches are checked in a finite quotient:

- **Eleventh approach (no-automata, [round-2 repaired proof](https://github.com/lambdamikel/alcircc5/blob/master/papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.pdf), *primary through round-10, superseded 2026-05-29*):** request-closed cycles in the rank-d quotient. Validity is the local property that the request-closure of the cycle realizes every ∃ PP.D / ∃ PPI.D requirement.
- **Twelfth approach (automata-flavored, this section):** ultimately periodic branches u₀,…,u_m,(v₀,…,v_(k-1))^ω with an explicit *cycle-realization condition* (Defn 6.x): every transitive eventuality occurring on the stem is met later on the stem or on the cycle, and every transitive eventuality on the cycle is met somewhere on the cycle. The regular-branch lemma (Lem 6.x) shows that every infinite satisfying branch over the finite profile alphabet can be regularized to such an ultimately periodic form.

Both formulations aim at the same decidability theorem. The no-automata route was *originally* preferred because it removes the residual ω-word notation and treats cycles as combinatorial blocking devices without semantic identification. **That preference was reversed on 2026-05-29** (see the next section): the no-automata route's finite-checkability half repeatedly failed cold review and kept reducing to automaton-shaped lemmas it could not prove, so the automata-flavored proof was promoted from "independent witness" to **primary statement**.

**Status.** Archived under [`papers/gpt5.5/`](https://github.com/lambdamikel/alcircc5/tree/master/papers/gpt5.5) alongside GPT-5.5's other materials. As of 2026-05-29 the automata route is the **primary** statement and the no-automata route is the superseded thread (next section).

---

## The no-automata split-forest thread (rounds 2–10) — superseded as primary, 2026-05-29

For eight review rounds the project's primary decidability statement was the **no-automata** split-forest proof: a finite combinatorial *certificate* whose validity was meant to be a finite syntactic check, with regularity and eventuality fulfilment encoded by request-closed blocking cycles instead of an automaton. On **2026-05-29** the primary statement was switched to the **split-forest + parity-tree-automata** proof (`papers/gpt5.5_final/split_forest_automata_decidability_proof_detailed.tex`). This section records why, and preserves the thread.

**Not retracted as wrong.** The split-forest *semantic normal form* — witness thinning → generated containment covers → split copies for incomparable superparts → side-interface mosaics → typed-EQ quotient — was found sound by every cold review and is shared *verbatim* with the automata proof. What was never discharged is the **finite-checkability / eventuality** half: the parts a hand certificate had to encode by ad-hoc finite catalogues and request-closed cycles. The automata proof keeps the sound normal form and replaces only that brittle half with a parity tree automaton (decided by non-emptiness), which handles those parts by construction. In other words, the no-automata route kept *converging onto an automaton* (request-closed cycles ≈ Büchi/parity acceptance; round-10's "finite product-state exhaustion" ≈ product-automaton reachability) without being able to prove the automaton-shaped lemmas; promoting the actual automaton is the convergent move.

**The round progression** (manuscripts retained as the audit trail):

| Round | What it added | Defect found by the next (cold) review |
|---|---|---|
| 4–6 (`papers/gpt5.5_round2/`) | request-closed cycles in a rank-d quotient; `(M6)` verticalization; `(V11)`–`(V15)` | round-6 `lab(u,v):=L_Q(q(u),q(v))` with `L_Q(π,π)=EQ` collapses distinct blocking laps into semantic equality (intrinsic to position-symbol indexing) |
| 7 (`papers/gpt5.5_final/repaired_split_forest_all_in_one_round7.*`, `expanded_split_forest_full_details_proof.*`) | occurrence-sensitive **pair shapes** with incidence tags `ι∈{self,eq,up,down,side_R,front_R}`; 12 validity clauses | cold Claude review: missing side/tree pair exhaustion; residual DR/PO frontier imposed before saturation; pair/triple catalogues bounded but not constructed |
| 8 (`papers/claude_latest_review_gpt5.5_fix/`) | saturated side context `S_k(u)`; cross side/tree exhaustion lemma; constructed `Pair_Q`/`Tri_Q` | cold Opus 4.8 review: **D-1** — the side/tree gap closes only on the finite boundary; a DR/PO witness can be composition-forced into an infinite *ancestor* PPI-tower (`C0' = (∃PP.G) ⊓ (∃PO.¬X)`, `G = (∀PO.X) ⊓ (∃PP.G)`) |
| 9 (`papers/gpt5.5_round3/`) | **composition-forced verticalization** closing D-1 (splice the ancestor PPI-tail into the vertical backbone); monotone-trace, bounded-threshold, global-residual-frontier lemmas | cold fresh-GPT-5.5 review (`papers/gpt5.5_round4/referee_response_alci_rcc5.*`): **Critical 1** the verticalization was one-sided (missed the dual *descendant* PP-tower); **Critical 2** V6/V7 finite-checkability was asserted, never proved; **Critical 3** boundary descriptors don't determine mixed labels; + a *false* simple-cycle bound |
| 10 (`papers/gpt5.5_round4/`) | dual splice; occurrence-local requests; ranked side-width; global-quotient-first extraction; `(M+1)N` closed-walk bound; **finite product-state exhaustion** + **complete interface descriptors** | (not cold-reviewed) — a deep read found the decidability burden funnels into two named-but-asserted lemmas (Finite Product Exhaustion, Complete-Interface Replacement), both automaton-shaped |

`expanded_split_forest_full_details_round10_merged.*` is the full round-10 expanded proof (the `_corrected` files are a lossy delta). The composition table itself was independently re-verified correct in every review (e.g. `papers/opus4.8_review/rcc5_compose.py`, `verification/python/rcc5_composition_check.py`).

**Computational corroboration retained.** `verification/python/wp10`–`wp12` machine-check the certificate/forced-verticalization machinery (ancestor case, the general parameterized family, and the round-10 dual descendant case). They remain valid corroboration of the split-forest semantic content; they do not exercise the automaton, and they do not touch round-10's two unproven keystones.

**Honest caveat on the promotion.** Switching to the automata route is a *strategic* clarity move, **not** a proof upgrade: the automata proof has not itself been cold-reviewed (its automaton construction, soundness/completeness-of-the-automaton lemmas, and finite-alphabet bound are unscrutinized). The decidability theorem's status remains *strongly supported, not certified*. The natural next step is to cold-review the automata proof (`papers/cold_review_round9/` packet repurposes).
