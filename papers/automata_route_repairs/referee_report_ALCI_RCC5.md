# Referee Report

**Manuscripts.** (1) *A Split-Forest Automata Proof of Decidability for $\mathcal{ALCI}_{\mathrm{RCC5}}$* (the detailed proof); (2) *Split-Forest Normal Forms and Finite Abstractions for $\mathcal{ALCI}_{\mathrm{RCC5}}$* (the A/B/C companion). Both dated May 30 2026.

**Claim under review.** Concept satisfiability for $\mathcal{ALCI}$ with the five RCC5 atomic roles $\{$EQ, PP, PPI, PO, DR$\}$, over abstract complete atomic RCC5 frames with strong equality (EQ $\Leftrightarrow$ identity), is decidable, via: split-forest normal form (Thm A) $\to$ finite frontier/pair/triple/equality-port abstraction (Thm B) $\to$ emptiness of a finite alternating parity tree automaton (Thm C).

---

## (a) Verdict

**Genuine gap (the result is most likely true; the manuscript does not prove it).**
Confidence: *very high* that the proof is incomplete as written; *moderate* that the theorem itself is true (plausible, by standard techniques, but — see below — **not** a corollary of any published result I can point to); *moderate* that the construction is repairable along the lines suggested.

A word on the **theorem** independent of this proof, since it is easy to overclaim (I did, in an earlier draft). It is *not* a corollary of Lutz & Miličić's $\mathcal{ALC}(\mathfrak D)$ decidability: that result concerns a *concrete domain* attached to $\mathcal{ALC}$ via functional *features*, where only feature-linked concrete values carry RCC constraints and the abstract domain is otherwise RCC-free. The present logic instead makes the five relations into ordinary *roles* and forces the **entire** domain to be one complete RCC5 network (every pair labelled, closed under composition) — a different, much more tightly coupled formalism. That relations-as-roles setting is in fact the one Lutz & Wolter (*Modal Logics of Topological Relations*, 2006) study, where the modal logic of RCC8 — and RCC5 — operators is *usually undecidable, often not even r.e.*, even over finite substructures. Their undecidability, however, is over **topological** semantics; the manuscript deliberately restricts to **abstract** composition-table frames (and §2 of the detailed PDF explicitly disclaims topological representability), precisely to escape it. So the result sits between a decidable concrete-domain version and an undecidable topological-roles version. Over the abstract semantics I think it is most likely true and provable by standard mosaic/automaton-plus-amalgamation methods — RCC5 *does* have the patchwork property, the key reusable ingredient — but I cannot hand you a published theorem that settles it, and assembling patchwork into a full proof for this logic is real work (roughly the work the manuscript attempts). So the manuscript is most likely trying to prove something true, by a bespoke route, and the question is whether the route is valid.

It is not, as written. The **soundness keystone — Theorem B / Lemma 6.9 ("finite pair/triple representation")** — derives a *globally consistent RCC5 labelling of an infinite tree* from purely *local* checks via "interface transformers," and the required global coherence is **asserted, not proved**. The same applies to the equality-port congruence (a genuinely global "for all $\zeta$" condition reduced to a finite frontier check with no separation argument), to the finite size bounds (counting heuristics that establish "a bound exists," not the stated bound), and to the multi-parent / cross-subtree case — which is the manuscript's own headline robustness example ($C_{\mathrm{split}}$, §14.2) and is dispatched there by a hand-wave. I was **unable to construct an accepted-but-unsatisfiable witness**, so I do not certify the construction *unsound*; but every gap sits exactly where unsoundness would hide, and the companion paper itself states that the prior version's gap was at this precise spot ("used 'represented target / represented triple' without proving that every semantic target or triple has a finite representative checked by the automaton"). The repair replaces the *words* with a *construction* whose correctness rests on the same unproved local-⇒-global step.

---

## (b) Findings (severity-graded)

Throughout, $\rho$ is the RCC5 labelling; "automata PDF" = manuscript (1), "normal-forms PDF" = manuscript (2). The composition table is **correct** (verified by enumeration — see (c) S1), so none of the findings is a table error; they are all about the abstraction-adequacy layer.

### CRITICAL

**C1 — Transformer coherence / well-definedness of $\rho_T$ is asserted, not proved.**
*Location:* automata PDF Def 6.5–6.8, Lemma 6.9 (esp. (F1),(F4)), §11.2; normal-forms PDF Def 4.4–4.7, Lemma C.2–C.3.
*Claim:* $\rho_T(\xi,\eta)$ is defined as the relation component of `rep2`$(\xi,\eta)$, computed by initialising a pair state at `lca`$(\xi,\eta)$ and applying the stored pair transformers down to the two endpoints; and (Lemma 6.9(F4)) for every triple $\rho_T(\xi,\zeta)\in\mathrm{Comp}(\rho_T(\xi,\eta),\rho_T(\eta,\zeta))$.
*Why it does not follow:* `rep3`$(\xi,\eta,\zeta)$ initialises at the **triple branch point**, which is in general *higher* in the tree than some pairwise LCA. For "$\rho_T$ satisfies composition on every triple" — the soundness keystone — the three pair-projections of `rep3` must equal the three independently-computed `rep2` values. That requires the coherence law

> *initialise-at-an-ancestor-then-push-both-endpoints-down = initialise-at-the-LCA*,

i.e. the transformer action must be well-defined on the quotient by interface-equivalence (a confluence/associativity property). **Nothing in the local legality conditions (Def 5.5; transitions Q1–Q7) checks this.** Q2/Q3 only verify that a declared (pair/triple) state is *composition-legal* and *converse-consistent* and that a triple's three projections match the pair transformers *one step at a time*; they never verify route-independence across multiple interface boundaries. Two consequences: (i) $\rho_T$ may not even be well-defined (route-dependent); (ii) even granting every stored triple state is composition-legal, the labelling actually *read off by* `rep2` need not satisfy composition. The proof of 6.9 papers over this with the single phrase "overlap compatibility says…," which is the missing lemma, stated as if it were a definition.
*Repair:* either (a) prove a confluence lemma — that the monoid of interface transformers acts well-definedly on pair/triple-state classes, and add the corresponding finite local check to the transition function; **or, far cleaner,** (b) delete Section 6 and invoke the **patchwork property of complete RCC5 networks**: finitely many local mosaics that agree on shared frontiers amalgamate into one globally consistent network. RCC5 has the patchwork property, so the amalgamation lemma itself is citable — it is precisely the property the bespoke machinery is trying (and failing) to re-derive. Wrapping that lemma into a model construction still has to be done, but it is a standard mosaic argument rather than the open-ended coherence bookkeeping of Section 6.

**C2 — Local checks do not pin down forced relations; the abstraction's freedom is globally unconstrained.**
*Location:* automata PDF transitions Q2,Q3; the multivaluedness of `Comp`.
*Claim (implicit):* satisfying the local legality clauses everywhere yields a genuine (and for unsat inputs, non-existent) model.
*Why it does not follow:* composition is **multivalued** on the entries that matter — e.g. (verified, see (c))
$$\mathrm{Comp}(\mathrm{PPI},\mathrm{PP})=\{\mathrm{EQ,PP,PPI,PO}\},\quad \mathrm{Comp}(\mathrm{PP},\mathrm{PO})=\{\mathrm{PP,PO,DR}\},\quad \mathrm{Comp}(\mathrm{DR},\mathrm{PP})=\{\mathrm{PP,PO,DR}\}.$$
A profile may therefore legally *declare* a relation that is composition-legal yet not the one *forced* by the rest of the structure. This freedom is *necessary* for completeness (a real model declares the true relation) but is exactly what an **unsatisfiable** concept needs in order to slip through — unless a global consistency argument forbids the bad declaration. The manuscript supplies none beyond C1's asserted coherence.
*Concrete pressure point — the manuscript's own $C_{\mathrm{split}}$ (§14.2):*
$$C_{\mathrm{split}}=\exists\mathrm{PP}.(A\sqcap\neg B\sqcap\forall\mathrm{PP}.\neg B\sqcap\forall\mathrm{PPI}.\neg B\sqcap\forall\mathrm{PO}.\neg B)\ \sqcap\ \exists\mathrm{PP}.B.$$
With $x\,\mathrm{PP}\,y$ (so $\rho(y,x)=\mathrm{PPI}$) and $x\,\mathrm{PP}\,z$, we get $\rho(y,z)\in\mathrm{Comp}(\mathrm{PPI},\mathrm{PP})=\{\mathrm{EQ,PP,PPI,PO}\}$ — crucially **DR $\notin$** this set. The four legal options each clash with one of $y$'s universals plus $z:B$, so $C_{\mathrm{split}}$ is genuinely **UNSAT**. The construction must reject it. But "reject" depends on the relation $(y,z)$ actually being evaluated *through their shared split-child $x$* so that $\mathrm{Comp}(\mathrm{PPI},\mathrm{PP})$ bites and forbids DR. Whether it is so evaluated is exactly C1/C3, which are unproved. The manuscript's stated reason — "equality synchronization still requires the two copies to have identical relation summaries to $y$ and $z$, so the same triple representative is checked" — does **not** establish that $y$ and $z$ ever appear in a common interface where $\mathrm{Comp}(\mathrm{PPI},\mathrm{PP})$ is enforced. (In the generated forest $y$ and $z$ are typically *roots of different trees*, linked only by the deep equality port $x_1\equiv_{\mathrm{EQ}}x_2$; see C3.)
*Repair:* as C1(b); the patchwork route makes DR impossible automatically because the complete network is consistent.

**C3 — Equality-port congruence: a global condition silently reduced to a finite check.**
*Location:* automata PDF Def 8.1 (E2), Lemma 8.2; normal-forms PDF Def B.1 (E2), Lemma B.2; transition Q5.
*Claim:* (E2) "$\rho(\xi,\zeta)=\rho(\eta,\zeta)$ for **every** occurrence $\zeta$," enforced "finitely by pair representatives: equality-port pairs have identical relation vectors to every live/shadow boundary position."
*Why it does not follow:*
1. **Frontier-agreement need not imply agreement-against-all-$\zeta$.** Two occurrences can have identical relation vectors to a finite frontier and still relate *differently* to a third occurrence $\zeta$ reached only by composition. The reduction is valid only if the frontier is *relationally separating* (a homogeneity / quantifier-elimination property of the RCC5 representation). That property is real for RCC5 — it follows from the homogeneous ω-categorical representation (Bodirsky & Wölfl) — but the manuscript neither states nor uses it; it asserts the reduction "by overlap compatibility."
2. **The check may never fire on the relevant pair.** Q5 spawns $q_{\mathrm{eq}}(a,b)$ only for two positions $a,b$ **in a single profile**. For the multi-parent split ($x_1$ under $y$, $x_2$ under $z$, with $y,z$ in different trees of the generated forest), $x_1$ and $x_2$ **never co-occur** in any profile, so the congruence between them is not obviously checked at all.
3. **The forest $\to$ single-input-tree encoding is unspecified.** The automaton consumes one ranked tree (Lemma 11.1: "root has a live position $p_0$ with $C_0\in\tau(p_0)$"), but the generated structure is a *forest* (maximal regions are distinct roots), and the satisfaction root $x$ sits *below* its PP-superparts. How the forest, the upward growth into superparts, and cross-subtree equality ports are folded into one input tree is never given. This is not a detail: it is where the relation between far-apart occurrences (and hence C2's DR-exclusion) lives.
*Repair:* (i) state and use the separating-frontier / homogeneity property of RCC5 explicitly (this is genuine work, and the cleanest source is the homogeneous representation of RCC5); or (ii) take the patchwork route, where EQ is just identity in the complete network and amalgamation handles split copies; **and** (iii) specify the forest-to-tree encoding and prove that every equality port is threaded through some common interface, or move to a two-way automaton (M3) that can read both endpoints' contexts.

### MAJOR

**M1 — The finite width bound $B(C_0)$ / saturation size is a counting heuristic.**
*Location:* automata PDF Def 5.1, Lemma 5.3 (recurrence $B_{r+1}=1+4e+4eB_r+4B_r^2+4B_r^3$); normal-forms PDF Def 3.5, §7 ($K(C_0)\le c\cdot n\cdot t\cdot h$), App A Lemma A.2.
*Claim:* a rank-$r$ saturated side context has a representative of size $\le B_r$.
*Why it does not follow:* Lemma 5.3's proof shows *finiteness at each fixed rank given that rank strictly decreases on recursive calls* — i.e. it proves "**some** finite bound exists," not the **displayed** bound. It does not account the positions actually forced by saturation (forced verticalization inserts a threshold node per inherited PP/PPI pair; equality/vertical strata are added per pair and per triple), nor prove the closure operator's *fixpoint* has size $\le B_r$ rather than merely being finite. "The recurrence deliberately overestimates these contributions" is an assertion, not a count. The companion's $K(C_0)\le c\cdot n\cdot t\cdot h$ is stated with no derivation of $c$ or $h$.
*Repair:* give an explicit per-rank accounting — positions added at a rank-$r$ source $\le$ (direct DR/PO witnesses $\le e$) $+$ (one threshold per inherited PP/PPI pair $\le |B(u)|\cdot|K|$) $+$ (recursive subcontexts $\le e\cdot B_{r-1}$) — and prove the fixpoint closes within it; or, simpler, replace the width bound entirely by a **type/mosaic** bound ($2^{\mathrm{poly}(|\mathrm{Cl}(C_0)|)}$ types), which is standard and avoids the recurrence.

**M2 — Shadow-class finiteness is asserted.**
*Location:* automata PDF Def 5.5 (P2) "$|H|\le B(C_0)$," Lemma 5.7.
*Claim:* only $B(C_0)$-many distinct "shadow" summaries of forgotten sources arise.
*Why it does not follow:* along an infinite PP/PPI chain there are infinitely many ancestors, each with its own relation vector to the live frontier and its own pending obligations; the claim that these collapse to $\le B(C_0)$ classes, with merge criterion "impose the same future obligations," is plausible but **unproved**, and the merge criterion is not shown to be a congruence for the relation-vector update (two shadows with the same obligations may update differently into a child).
*Repair:* prove shadow summaries range over the finite set $\mathrm{Type}(C_0)\times\mathrm{Rel}^{\le B}\times 2^{\mathrm{Rel}\times\mathrm{Cl}(C_0)}$ and that the relation-vector update factors through this quotient; the bound then follows.

**M3 — One-way sufficiency rests on the same unproved bookkeeping.**
*Location:* automata PDF §10 preamble ("Parent moves are not needed because all parent and ancestor information required by a child is included in the child-interface descriptor"); normal-forms PDF §5.1 (branching rank $B(C_0)$, "dummy padding children"), never resolved.
*Why it matters:* this is C1–C3 in disguise. A one-way device suffices **iff** shadows + inherited obligations *losslessly* summarise every ancestor constraint relevant to any descendant, including composition-forced and equality-mediated ones. If the summary is incomplete (C1–C3 unresolved), one-way is genuinely insufficient and one must invoke the **two-way alternating parity tree automaton emptiness theorem** (Vardi 1998) — still decidable, so the *theorem* survives, but the *stated automaton* is not justified. The two PDFs are also inconsistent here (normal-forms never commits to one-way vs two-way).
*Repair:* prove the lossless-summary lemma, or state the device as two-way and cite Vardi's emptiness result (decidable, ExpTime in the alternation/index).

**M4 — Universal propagation uses a may-analysis that can drop obligations.**
*Location:* automata PDF Def 7.2, Lemma 7.3; normal-forms PDF Def 4.2 (P5), Lemma C.4.
*Claim:* if $\forall R.D\in\mathrm{tp}(\xi)$ and $\rho_T(\xi,\eta)=R$ then $D\in\mathrm{tp}(\eta)$, by pushing $(R,D,\xi)$ through child interfaces "if a pair transformer can map the source to a future child occurrence with relation $R$."
*Why it does not follow:* the intermediate relation can leave and re-enter the $R$-class. E.g. a DR-obligation: $\mathrm{Comp}(\mathrm{DR},\mathrm{PPI})=\{\mathrm{DR}\}$ keeps it, but $\mathrm{Comp}(\mathrm{DR},\mathrm{PP})=\{\mathrm{PP,PO,DR}\}$ — does the DR-obligation persist to a *later* DR-target reached by a further step after a PP-step "maybe" took it out of DR? The proof says "since the final relation is $R$ the obligation survives along the unique product-state path," but never shows the may-tracking does not prune a branch that *later* realises $R$. For transitive $\forall\mathrm{PP}.D$ the obligation must be **re-emitted at every PP-ancestor**, which is not clearly in the construction.
*Repair:* track each obligation by the full *reachable relation-set* and discharge $D$ at any target whose recorded relation lies in that set; prove monotonicity (the set only shrinks correctly).

### MINOR

**m1 — Inconsistent objects across the two PDFs.** Width bound is $K(C_0)=c\cdot n\cdot t\cdot h$ (normal-forms §7) vs the $B(C_0)$ recurrence (automata §5.1); state families differ slightly; the "two-way would also work" aside (automata §10) is not reconciled with the normal-forms automaton. Unify before submission.

**m2 — Editorial.** Normal-forms PDF contents/appendix titles are truncated/garbled ("Suggested division between main paper and …", appendix headers ending mid-phrase).

**m3 — Eventuality bookkeeping under equality transfer.** The parity construction (automata §9, Lemma 9.4) is fine in outline, but Def 9.2's handling of a vertical request that "passes through an equality mate" — "the automaton tracks the request along the support branch chosen by the witness declaration" — is informal; pin it down so a request cannot be deferred forever by bouncing between equality mates. The "generalized Büchi-to-parity, ordered arbitrarily" line needs the explicit index.

---

## (c) Steps checked and found sound

**S1 — RCC5 composition table: CORRECT.** Recomputed by exhaustive enumeration of regions-as-point-sets over a 5-cell universe (every nonempty subset; $\rho$ defined by $=,\ \cap=\varnothing,\ \subsetneq,\ \supsetneq,$ else PO). The computed table matches **both PDFs in every one of the 25 cells**, including all four `Rel` (= all-five) entries and every singleton:

```
Comp | EQ        PP             PPI            PO            DR
-----+-------------------------------------------------------------
EQ   | {EQ}      {PP}           {PPI}          {PO}          {DR}
PP   | {PP}      {PP}           Rel            {PP,PO,DR}    {DR}
PPI  | {PPI}     {EQ,PP,PPI,PO} {PPI}          {PPI,PO}      {PPI,PO,DR}
PO   | {PO}      {PP,PO}        {PPI,PO,DR}    Rel           {PPI,PO,DR}
DR   | {DR}      {PP,PO,DR}     {DR}           {PP,PO,DR}    Rel
```
Forcing (singleton) compositions — the ones the unsat proofs rely on — are exactly: all `EQ;·` and `·;EQ`; `PP;PP={PP}`, `PP;DR={DR}`; `PPI;PPI={PPI}`; `DR;PPI={DR}`. Converse-consistency holds throughout. No error here.

**S2 — Witness thinning (Lemma 3.3, both PDFs): CORRECT and standard.** The only nontrivial direction (reverse, $D=\forall R.E$) correctly uses closure of $\mathrm{Cl}(C_0)$ under NNF complement: from $a\not\models_I\forall R.E$ one gets $a\models_I\exists R.\overline E$, and since $\exists R.\overline E=\overline{\forall R.E}\in\mathrm{Cl}(C_0)$, the chosen witness lies in $W$ and witnesses $\overline E$; induction finishes. Atomic/Boolean/$\exists$ cases are immediate. (This is the formal replacement for any "semantic Hasse" assumption, and it does that job.)

**S3 — Type machinery, NNF, strong-EQ normalisation (Def 2.1–2.2): CORRECT.** $\exists\mathrm{EQ}.C\equiv C$ and $\forall\mathrm{EQ}.C\equiv C$ are valid because EQ is identity (R1), and (T4),(T5) impose them on types correctly. $\mathrm{Cl}(C_0)$ is finite, closed under subformula and complement.

**S4 — Composition arithmetic of all diagnostic concepts: independently verified; the manuscript's target verdicts are the correct answers.**

| Concept | Forced step | Result |
|---|---|---|
| $\exists\mathrm{PP}.(\exists\mathrm{DR}.A)\sqcap\forall\mathrm{DR}.\neg A$ | $x\,\mathrm{PP}\,y,\ y\,\mathrm{DR}\,z$; $\mathrm{Comp}(\mathrm{PP,DR})=\{\mathrm{DR}\}\Rightarrow x\,\mathrm{DR}\,z$ | **UNSAT** (forces $\neg A$ at $z:A$) |
| $C_{\mathrm{split}}$ (above) | $\mathrm{Comp}(\mathrm{PPI,PP})=\{\mathrm{EQ,PP,PPI,PO}\}$; DR excluded; all 4 options blocked | **UNSAT** |
| $\exists\mathrm{DR}.(A\sqcap\exists\mathrm{DR}.B)$ | $\mathrm{Comp}(\mathrm{DR,DR})=\mathrm{Rel}$ (unconstrained) | **SAT** |
| $\exists\mathrm{PP}.\top\sqcap\forall\mathrm{PP}.\exists\mathrm{PP}.\top$ | $\mathrm{Comp}(\mathrm{PP,PP})=\{\mathrm{PP}\}$; eventuality discharged immediately | **SAT** |
| *extra:* $\exists\mathrm{DR}.(\exists\mathrm{PPI}.A)\sqcap\forall\mathrm{DR}.\neg A$ | $x\,\mathrm{DR}\,y,\ y\,\mathrm{PPI}\,z$; $\mathrm{Comp}(\mathrm{DR,PPI})=\{\mathrm{DR}\}\Rightarrow x\,\mathrm{DR}\,z$ | **UNSAT** |

So the *desired* automaton behaviour (reject the three unsat concepts, accept the two sat concepts) is the correct specification. What is **not** established is that the construction *realises* it: for concept 1 (the motivating example, where the forced target $z$ sits one interface hop away in the parent's side context) the rejection is plausible; for $C_{\mathrm{split}}$ the manuscript's justification is inadequate (see C2/C3); the *extra* concept stresses a forced target **two interface hops out** (a vertical child of a side-context witness) and shows the propagation/representation burden the construction must — but is not proven to — discharge.

**S5 — Quotient soundness *given* a genuine typed congruence (Lemma B.2 / 8.3): CORRECT.** Defining $\rho([x],[y])=\rho(x,y)$ is well-defined under (E1)–(E4); EQ becomes identity by exactness; converse and composition transfer to classes. The step is valid. Its **hypothesis** — that the finite checks actually yield a typed RCC5 congruence — is precisely what C3 disputes; the soundness of the quotient *operation* is not in question.

**S6 — Overall architecture: sound blueprint.** The A/B/C decomposition (semantic normal form $\to$ finite abstraction $\to$ automaton emptiness), and within A the pipeline witness-thinning $\to$ generated containment forest $\to$ side contexts for DR/PO $\to$ vertical eventualities by parity, is the right shape and matches how such results are normally proved. The defects are confined to the **abstraction-adequacy layer (Theorem B / §§5–8)**, not to the blueprint or to Theorem A's model-theoretic core.

---

## Summary for the authors

The cleanest path to a correct proof is to stop hand-building global consistency. RCC5 is ω-admissible and complete RCC5 networks have the patchwork property; that single fact is the amalgamation engine the pair/triple-product-state apparatus is laboriously and incompletely re-deriving. Concretely:

1. Keep Theorem A (it is essentially sound).
2. Replace Section 6 (and the transformer-coherence claims C1) by an explicit appeal to the **patchwork property** of complete RCC5 networks, or — if a self-contained automaton is wanted — by a **type/mosaic** construction with a **two-way alternating parity tree automaton** (M3) and a proved separating-frontier lemma for the equality quotient (C3).
3. Prove, don't assert, the finite bounds (M1, M2) — or sidestep them with the $2^{\mathrm{poly}}$ type bound.
4. Fix the universal-propagation may-analysis (M4) by tracking reachable relation-sets.

With those changes the result is reachable by standard techniques. As it stands, the manuscript states a (most likely true) theorem and the right overall strategy but does not prove the central adequacy theorem.
