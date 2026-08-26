# Cold attack request: the cut-leaf residue in ALCI_RCC5's ∀PO-free fragment

This is **not a review request**. It is a request for ideas on one narrow,
well-characterised open question. Two proposed answers have been refuted by
machine-checked probes in the last two days; both refutations are included so
you do not repeat them.

## 0. Standing honesty note

This project's ledger is **seventeen reviews, with a defect or overclaim found
in all but two**. In the session that produced this packet the author refuted
four of its own claims, retired three measurement instruments that could not
represent what they measured, and reported one result confidently that did not
survive its own follow-up test. Treat every claim below as needing your check,
including the ones marked certified — though those are Lean-checked, 0 sorries,
0 `sorryAx`, axioms `propext`/`Classical.choice`/`Quot.sound`.

## 1. Setting

`ALCI_RCC5` = ALCI with the five RCC5 relations `{DR, PO, EQ, PP, PPI}` as
roles, strong-EQ semantics (EQ = identity), concepts in NNF, inverse roles
absorbed. Concept satisfiability is the open problem.

The **∀PO-free fragment** forbids `∀PO.C` (but allows `∃PO.C`). Three of its
four quadrants have certified general decidability. The fourth — **mixed**,
where a concept carries both `∃PO` and `∃PP` demands — is the subject here, and
specifically its **vertical half** (the `∃PP` / `∃PPI` demands).

Certificates are `MultiTier β κ`: externals `β`, kernels `κ` (each an infinite
periodic tower with `p` phases), a relation `E : β → β → Atom` among externals,
`K : κ → β → Atom` from kernels to externals. `MultiTierOk` is the obligation
list — see `lean/EXCERPTS.lean`.

## 2. What is certified (all in Lean, no hypotheses)

| | |
|---|---|
| `odOfModel` | the model's own `PP`/`DR`, read off, IS an `ODStruct` (strict order + downward-closed disjointness). **Axiom-free.** |
| `odNet_frame` | any `ODStruct` induces a composition-closed RCC5 net |
| `cutNodes_stable_typeEnum` | the blocking closure stabilises at fuel `\|typeEnum C₀\|`, **for every witness selector, no hypothesis** |
| `cutNodes_up_mem` / `_dn_mem` | every demand's witness is in the closure — for EXPANDED nodes |
| `readoff_ee_all_pp/_ppi/_dr` | under read-off, `ee_all` is a consequence of the frame |
| `readoff_e_ex_pp/_ppi` | under read-off, vertical `e_ex` reduces to MEMBERSHIP |
| `chain_or_kernel` | along `∃PP` steps: either some reachable node has no `∃PP` demand, or a KERNEL exists |
| `rr_covers` | a kernel with the persistence guard serves all its demands (round-robin) |

`∀PO` obligations are absent by `mty_no_all_po` — the fragment's defining
property.

**Consequence:** every `ee_all` case and both vertical `e_ex` cases are
consequences of the frame. The certificate has ONE open question.

## 3. THE OPEN QUESTION

The blocking closure `cutNodes` stops expanding at a node whose model type
already appeared on the current path — this is what makes it terminate, and the
bound `|typeEnum C₀|` is certified. Call such a node a **cut leaf**.

A cut leaf is still a node of the certificate, so it owes its own demands. Its
witnesses were never added, because it was not expanded.

> **Which nodes are in the set?** Concretely: how is a cut leaf's `∃PP.D`
> served, given that adding its witness restarts the problem one level down?

Measured facts (probes included, all self-contained, RCC5 table re-derived from
finite set semantics in each):

* cut leaves with unserved demands arise in **3–13%** of cut leaves;
* **87–97%** of cut leaves are already served by an existing set member;
* a kernel's PHASES cover **87–97%** of the unserved ones (`wp117`, legitimate —
  no self-witnessing possible there);
* whether the blocked lap CONTINUES (which would give the leaf its own kernel via
  `chain_or_kernel`): tail leaves 94–99%, prefix leaves 33–56%, side leaves
  **0%, structurally** — a side node is not on the chain.

## 4. TWO REFUTED ANSWERS — do not re-propose these

### 4a. Expand the cut leaf (`wp116`)

Add and expand the blocker's witness at each cut leaf. Each target is itself
expanded and produces cut leaves of its own, generating ROUNDS.

Measured over an eventually periodic tower, period fixed at 3, aperiodic prefix
`L` growing:

| `L` | 4 | 8 | 12 | 18 | 26 | 40 |
|---|---|---|---|---|---|---|
| max rounds | 3 | 5 | 6 | 9 | 12 | 15+ |

**The round count grows ~linearly in the prefix length and does not saturate.**
It is a property of the MODEL, not of `C₀`. Not a type-count effect: prefix types
are drawn from three atoms and repeat many times over at `L = 40`.

### 4b. Serve by kernel phase or "declared edge" (`wp117` → refuted by `wp118`)

The frame is DECLARED and `ee_all` reads only LABELS, so since `mty(leaf) =
mty(blocker)` the leaf can borrow the blocker's witness under a declared edge.
Measured coverage: **100%**, five tower shapes, 3,218 demands.

**This was wrong.** The full `MultiTierOk` check (`wp118`) reported `frame_q`
converse failures at pairs `(x, x)`: the "witness" was **the leaf itself** — a
leaf is an `r`-successor of its own blocker. That is the project's round-6 lap
collapse (a node identified with itself) in miniature.

With `w ≠ v` forbidden, the same 305 demands go from "witness already in the set"
= 305 to **= 0**, and "witness is a NEW node" from 0 to **305**. So 4b collapses
into 4a.

## 5. What we would like from you

Any of:

1. **A third mechanism** for serving a cut leaf that neither expands nor
   identifies. We have not found one.
2. **An argument that the round count IS `C₀`-computable** despite §4a — i.e.
   that our tower class generates models a real extraction need not accept.
   Note completeness only requires SOME certificate for a satisfiable `C₀`, not
   one for every model of `C₀`; **we have never used that freedom**, and a
   model-normalisation theorem (pass to a sub-model with bounded prefix) would
   be the shape of it.
3. **A reason the question is the wrong one** — e.g. that cut leaves should not
   be certificate nodes at all, with a construction that keeps them out while
   preserving `e_ex` at their parents.
4. **A counterexample**: a satisfiable ∀PO-free `C₀` whose every certificate of
   this architecture must be infinite. That would kill the route and be worth as
   much as a repair.

## 6. Reproducing

```
cd probes
python3 wp112_lap_continuation_closed_form.py   # the closed-form tower class
python3 wp115_declared_edge_acceptance.py       # full check, FINITE set models
python3 wp116_target_rounds.py                  # 4a's refutation
python3 wp117_kernel_phase_coverage.py          # coverage (retired: see 4b)
python3 wp118_multitier_acceptance.py           # full MultiTierOk, kernel-bearing
```

`wp116`/`wp117`/`wp118` import the tower from `wp112`, so run them from that
directory.

**Probe discipline used here, offered as a warning:** three instruments in this
sequence failed because the model class could not represent the phenomenon
measured (finite models have no infinite tower; an indexed-residue quotient
cannot let a residue recur above itself). State a control's expected value BEFORE
the run and withhold the treatment when the control misses — that is what caught
4b.

## 7. Files

* `lean/EXCERPTS.lean` — the certified statements above, with proofs, excerpted
  from a 31,783-line file. Does not compile standalone.
* `probes/` — five self-contained Python probes, stdlib only.
