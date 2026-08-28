# Attack request, round 2 — the mixed quadrant of the ∀PO-free ALCI_RCC5 fragment

You (or a predecessor) answered round 1. **That report was good**: it solved one
of the three targets, refuted the one we recommended, and found two real defects
in our probes. `RESPONSE_TO_ROUND1.md` records exactly what we did with it,
including the one claim we could not reproduce.

This round asks about **one sharp question** plus a revisit that your own report
suggested. `STATUS.md` lists what is now machine-certified, so you do not
re-derive it. §3 lists routes already refuted — including two refuted *since*
round 1.

---

## 0. What changed since round 1

* **Target B is formalized end to end.** Your finite-rectangle argument is now
  Lean-certified (`atom_seq_stabilizes` → `two_tower_rectangle_gen` →
  `finite_fusion_recurrent` → `fused_kq_all`), direction-generic, with equal-type
  endpoints preserved. `kq_all` — open since 2026-07 — is discharged.
* **Your Target A refutation was accepted and its lesson certified.** The
  eight-point counterexample was rebuilt independently from your prose. It also
  kills a variant we had derived and were about to formalize (take the witness of
  a *maximal* group member) — the argument only uses that the top is above both.
* **The down-spectrum key is built and its payoff proved.** `dkey`,
  `keyEnum = typeEnum × sublists typeEnum`, the gate, and — the point —
  `dkey_union_serves`: under that key one member's `DR`-witness carries its `∀DR`
  bodies across *every* member's cone, so your §256 configuration cannot recur
  inside a key class. The whole phase-1 chain is ported to it.
* **Every `e_ex` case now has its edge**, horizontal included (the `∃DR` edge
  carries obligations on the *cones*, because disjointness is a downward closure;
  those transfer by the same spectrum argument).

So the extraction is blocked on one thing.

---

## 1. TARGET D — the borrowed edge's SELECTION, and global acyclicity

### The setting, concretely

The node set is a finite set `V` of points of one RCC5 model `ρ`. The gate keeps
the first node of each key `q(v) = (mty v, {mty x : x PP v})`. A node `v` whose
key already occurred is *blocked*; its gate-mate `a` satisfies `q(a) = q(v)`.

For a demand `∃PP.D ∈ mty v`, `a` has a witness `z` (`ρ(a,z) = PP`, `D` at `z`),
and the certificate DECLARES `v < z`. The declared order is

    L  :=  { (x,y) ∈ V² : ρ(x,y) = PP }  ∪  { (v,z) : borrowed }

and the certificate's frame is an **ordered-disjoint structure**: `lt` a strict
partial order, `disj` symmetric, irreflexive, DOWNWARD CLOSED, and — this is the
clause that bites — **`lt x y → ¬ disj x y`**.

### What is already certified

1. *Dichotomy* (axiom-free). If `ρ(z,v) = PP` then `ρ(a,v) = PP`. So the bad case
   is a type repeat on an ascending chain, not an arbitrary configuration.
2. *Agreement exists where it is needed.* If `ρ(a,v) = PP` then `v`'s own witness
   `w` satisfies `ρ(a,w) = PP` and `ρ(v,w) = PP` (by `comp(PP,PP) = {PP}`), so an
   AGREEING witness exists exactly in the configuration where the greedy one fails.
3. *Per-edge safety.* Hence for each single blocked node a witness can always be
   chosen with `ρ(w,v) ≠ PP`; and `w = v` is impossible in either branch.
4. *When the witness agrees* (`ρ(v,w) = PP`), the declared edge lies inside the
   model's own `PP`, so `L ⊆ ρ|PP`, and irreflexivity of the transitive closure is
   free (`ρ(x,x) = EQ`, never `PP`; transitivity by `comp(PP,PP) = {PP}`).

### The question

In the remaining case — `ρ(a,v) ≠ PP`, so item 2 does not apply — the chosen
witness `z` is merely **incomparable** to `v`: `ρ(v,z) ∈ {DR, PO}`. Two things are
then unproved:

> **D1.** Is the transitive closure of `L` irreflexive? Per-edge safety (item 3)
> is not enough: a cycle could pass through several borrowed edges and model `PP`
> edges. Either prove it, or exhibit a configuration where it fails.
>
> **D2.** If `ρ(v,z) = DR`, the declared `v < z` sits on a pair the frame also
> wants disjoint, violating `lt x y → ¬ disj x y` — and disjointness is a
> downward closure, so it is not enough to drop `(v,z)` from the seed. **Does a
> witness always exist that is neither below `v` nor `DR` from `v`?** If not,
> what bounded repair restores the frame?

D2 is the sharper half and it has history: an earlier round of this project hit
exactly this clause ("the blocker's witness can be `DR` from the leaf, which
labels cannot see") and repaired it by *strengthening the selection* to "neither
an ancestor nor disjoint". We do not know that such a witness always exists.

### What would count as progress

* A proof that a witness avoiding both conditions always exists (⟹ `L ⊆ ρ|PP ∪
  ρ|PO`-safe and D1 likely follows).
* A counterexample: a satisfiable ∀PO-free `C₀`, a model, and a blocked node all
  of whose gate-mate's witnesses are either below it or `DR` from it.
* A different discipline: e.g. route the demand to a kernel instead of an edge, or
  refine the key again (we know the cost: the key enumeration is already `N·2^N`).
* A proof of D1 that tolerates non-agreeing edges.

**Measurement we have.** `wp131` part G: on 1,040 instances, 132 genuinely needed
the fallback and none produced a cycle. That is evidence, not a theorem, and it
does not test D2 at all.

---

## 2. TARGET E — Target C revisited, with the refinement in hand

Your round-1 report isolated C's residue as *row-conservative finite demand
closure* and observed it "aligns naturally with the down-spectrum refinement
suggested by Target A". **That refinement now exists and is certified** (§0), which
is a genuinely new input rather than a re-ask.

Recall C: a kernel's existential demands need witnesses placed in the EXTERNAL
node set, but the external list must be fixed BEFORE the kernel's segment is
chosen (otherwise `externals_stabilize` does not apply). Your counterexample to
the naive tail-stabilize/add-witness iteration reproduces here.

> **E.** Does anchored PO-completion, with the external set closed under demands
> at the down-spectrum key, reach a finite fixed point? The key's enumeration is
> finite (`N·2^N`), which was not available to the argument before.

---

## 3. Routes already refuted — do not re-propose

Round 1's list stands (identify blocked node with blocker; budget-truncated
read-off; PO-default frame; poset frame without DR; algebra-only width
compression; off-the-shelf guarded covers). **Added since:**

7. **A shared class top keyed on the model TYPE alone** — your own eight-point
   counterexample, verified independently here.
8. **Taking the witness of a MAXIMAL group member** — dies to the same argument;
   the declared edge makes that witness a common top *in the declared frame*.
9. **Repeat-free chain selection for acyclicity** — refuted by `wp131`: survivors
   remain, and in every survivor there were ZERO repeat-free candidates, so the
   discipline could not even be applied.
10. **Tail-by-tail cross-kernel stabilization** — false, as you showed; the finite
    version is what the certificate consumes and is now certified.

---

## 4. What is in this packet

```
ATTACK_PROMPT_2.md       this file
STATUS.md                what is machine-certified now, obligation by obligation
RESPONSE_TO_ROUND1.md    what we did with round 1, incl. one non-reproduction
probes/wp131_*.py        the borrowed-edge probe, WITH your audit's fixes applied
probes/wp132_*.py        the down-spectrum probe (regression + control + treatment)
run_probes.sh
```

Both probes are self-contained Python 3 and re-derive the RCC5 table from finite
set semantics. `wp132` packages the eight-point counterexample as a regression, so
it will tell you immediately if we have mis-transcribed your model.

**Scope honesty, unchanged.** The Lean development is ~42,700 lines, 0 sorries,
0 warnings, axioms `propext`/`Quot.sound`/`Classical.choice`, and **unreviewed**.
Probe numbers are finite randomized sweeps over finite set models; kernels are not
exercised by them. Decidability of full ALCI_RCC5 is a separate, older open
problem and is not what this packet is about.
