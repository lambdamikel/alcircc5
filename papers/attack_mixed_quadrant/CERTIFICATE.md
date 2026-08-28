# The certificate, exactly — self-contained

A **`MultiTier`** certificate over finite index types `β` (externals) and
`κ` (kernels) consists of

| component | meaning |
|---|---|
| `tauE : β → List Concept` | the label of each external node |
| `p : κ → Nat` | the period (number of phases) of each kernel |
| `phase : κ → Nat → List Concept` | the label of phase `a < p k` of kernel `k` |
| `up : κ → Bool` | the kernel's direction (`true` = ascending, `PP`) |
| `E : β → β → Atom` | the declared relation between two externals |
| `K : κ → β → Atom` | the declared relation from a kernel to an external |
| `Q : κ → κ → Atom` | the declared relation between two kernels |

Its intended unfolding: each external is one element; each kernel `k` is an
infinite chain whose `n`-th element has label `phase k (n mod p k)` and whose
consecutive elements are related by `PP` (if `up k`) or `PPI`. All elements of a
kernel bear the SAME declared relation to any given external — that is what
makes `K` a function of `(k, e)` and not of the position in the chain, and it is
the source of Target B's difficulty.

`cdir true = PP`, `cdir false = PPI`. `conv` swaps `PP`/`PPI` and fixes the rest.

## The 19 obligations (`MultiTierOk`)

**Frame (2).**
1. `hp` — every period is positive.
2. `frame_q` — the declared relations form a composition-closed, converse-closed
   atomic RCC5 network. Discharged by reading them off an **ordered-disjoint
   structure**: a strict partial order `lt` plus a symmetric irreflexive `disj`
   that is DOWNWARD CLOSED (`x ≤ x'`, `y ≤ y'`, `disj x' y'` ⟹ `disj x y`) and
   never holds between comparable elements. Then
   `odNet x y = EQ / PP / PPI / DR / PO` according to
   `x = y` / `lt x y` / `lt y x` / `disj x y` / otherwise.
   *This is certified: the RCC5 normal form.*

**Propositional coherence (8).** For externals and for each phase: no
atom/negated-atom clash, no `⊥`, `and` decomposes, `or` has a disjunct present.
*Free when labels are model types.*

**Universal propagation (7).**
3. `ee_all` — `∀r.c ∈ tauE e` and `E e f = r` ⟹ `c ∈ tauE f`.
4. `ek_all` — `∀r.c ∈ tauE e` and `conv (K k e) = r` ⟹ `c ∈ phase k a` for EVERY
   phase `a`.
5. `ke_all` — `∀r.c ∈ phase k a` and `K k f = r` ⟹ `c ∈ tauE f`.
6. `kk_pp` — `∀PP.c ∈ phase k a` ⟹ `c ∈ phase k b` for EVERY `b < p k`.
7. `kk_ppi` — likewise for `∀PPI`.
8. `kk_eq` — `∀EQ.c ∈ phase k a` ⟹ `c ∈ phase k a`.
9. `kq_all` — `∀r.c ∈ phase k a` and `Q k k' = r` ⟹ `c ∈ phase k' b` for EVERY
   `b < p k'`. **← Target B lives here.**

Note that 4, 6, 7 and 9 quantify over ALL phases from ONE phase's universal. That
is forced by the certificate's shape: one declared value per (kernel, target)
pair must serve the whole infinite chain.

**Existential fulfilment (2).**
10. `e_ex` — `∃r.c ∈ tauE e` is served either by an external `f` with `E e f = r`
    and `c ∈ tauE f`, or by a kernel phase.
11. `k_ex` — `∃r.c ∈ phase k a` is served by an external, or by another phase of
    the same kernel in the kernel's own direction, or by `r = EQ` at the same
    phase, or by a phase of a different kernel.

## Where each obligation currently stands

| obligation | status |
|---|---|
| `hp`, propositional (9) | free from model-type labels |
| `frame_q` | certified from the ordered-disjoint normal form |
| `kk_pp`, `kk_ppi`, `kk_eq` | **certified** — the chain order plus one use of the kernel's type-recurrence `mty(c i) = mty(c (i+p))`, in opposite directions for the two |
| `ke_all`, `ek_all` | **certified** given a constant row, which is **achievable**: a finite external list fixed in advance has a uniform index past which every row is constant |
| `ee_all` | certified on edges that agree with the model; the residue is the borrowed edges of Target A |
| `e_ex` | node set certified finite, bounded and covered; the residue is Target A |
| `k_ex` | reduced to placing the (certified, uniform) kernel witnesses in the external set — Target C |
| `kq_all` | **OPEN — Target B** |

## Two facts about the fragment used throughout

* **`∀PO` never occurs in the closure**, so a declared PO edge imposes nothing on
  either endpoint. `∃PO` demands are therefore served by a fresh external with a
  declared PO edge and no coordination cost.
* **EQ is never forced.** Every non-trivial composition cell containing EQ also
  contains PP, PPI and PO — so no configuration of constraints can force two
  distinct elements to be identified.
