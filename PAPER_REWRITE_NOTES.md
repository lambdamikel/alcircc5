# Paper-rewrite notes: proof-architecture details not to gloss over

Recorded 2026-08-20, from a discussion that surfaced a real calibration gap
between the manuscripts and the Lean development. The papers will be rewritten
later; this file exists so the details are not lost or smoothed over in the
rewrite. Nothing here is a new mathematical claim — it is a record of which
claim lives in which register.

## 1. The trigger

While scoping the ∀PO-free mixing assembly, I said "the Lean artifact never used
split-forest". That is literally true of `formal/POFreeLift.lean` (zero
occurrences) but **misleading as an account of the framework**, and Michael was
right to push back: `papers/po_free_fragment_ALCIRCC5.tex` states its main
theorem in exactly split-forest terms. The honest version is:

> The Lean route does not *produce* a split-forest presentation, but it is built
> on the split-forest decomposition and would not typecheck without it.

## 2. Three registers, currently conflatable

| register | content | status |
|---|---|---|
| (i) the split-forest **insight** | present a complete-graph model as a forest: vertical `PP`/`PPI` skeleton, horizontal `DR`/`PO` completion, join nodes split into occurrence copies, re-identified by a quotient | ALIVE and formalized *in structure* — `MultiTier` is this discipline as a data type (`κ` kernels with `up : κ → Bool` = the vertical skeleton; `β` externals with `E` = the horizontal completion; `K`/`Q` = the interface) |
| (ii) the split-forest **presentation + `K(C)` width bound** | `papers/po_free_fragment_ALCIRCC5.tex`, Thm "Bounded live width; decidability": every satisfiable ∀PO-free `C` has a split-forest presentation of live width ≤ `K(C) = (1+m)²·2^(2^m)` | **proof sketch**, unreviewed, NOT machine-checked. The Lean file contains **no width statement at all** |
| (iii) split-forest **+ patchwork bags + parity automaton** | the FULL-LOGIC argument, Theorems A/B/C | untouched by any Lean work; still gated on F6 — the open problem |

The overview's claim that the split-forest idea is *"the semantic foundation that
every subsequent proof route consumes"* **stands** — register (i) — and should not
be weakened in a rewrite. What must be stated is that (ii) is not certified.

## 3. Shared engine vs different final step

The fragment paper's proof sketch and the Lean development share their engine:

| paper's sketch | Lean lemma |
|---|---|
| external-relation stabilization | `external_stabilizes` |
| `DR`/`PP` demands by backward forcing | `backward_forcing_dr`, `backward_forcing_pp` |
| `PPI` demands by forward absorption | `forward_absorption_ppi` |
| `PO`-safety because there is no `∀PO` | `mty_no_all_po` (via `pofree_cl_all`) |
| two-tier quotient | the `MultiTier` certificates |

They diverge at the end: the paper concludes with a **presentation + width
bound** and derives decidability from it; the Lean builds a **finite certificate**
and derives `Decidable (Satisfiable C0)` from `multiTier_sound` plus finite code
enumeration. So they are two arguments for the same decidability claim, sharing
their engine but not their final step.

**Do not** cite the Lean as certifying the paper's theorem as stated.

## 4. A second architecture fork, internal to the Lean (ASSEMBLY_DESIGN §40)

The Lean file itself contains two mixed-certificate architectures, and the
campaign pinned its summit to the more expensive one without recording the
comparison:

- **read-off** (`mixKernels`): `E`/`K`/`Q` are the model's own relations. Needs
  `hstab` and `hrectQ` (the whole §39 apparatus); `∃PO` at a phase needs the
  pool. Supports BOTH tower directions.
- **PO-default** (`mtkKernelsDR`, and the new `po_dr_multi_kernel_frame'`):
  `E`/`K`/`Q` DECLARED, `Q ≡ po`. No `hstab`, no `hrectQ`, `∃PO` free. Ascending
  only as built; being generalized with `up := dir`.

A rewrite should present the certificate route in whichever architecture the
development lands on, and should NOT describe the §39 stabilization apparatus as
essential if the PO-default route supersedes it. Both are certified; only one may
end up on the critical path.

## 5. Corrections already applied, to carry into the rewrite

- **§33's one-shot `∃PP` gap is narrower than recorded.** Its argument that a
  one-shot `∃PP` "cannot be a `PP` edge in the β-frame" silently assumes the
  `PP`-child itself has a `PP`-successor. `wp92` parts D/E: `PP` *siblings* are
  free, only `PP` *chains* violate closure, and a one-shot non-nested `∃PP` at a
  phase IS servable. The open item is specifically **nested** `∃PP`.
- **`∃PO` does not universally require the pool.** It requires it in the read-off
  architecture only (`wp91` part W); PO-default serves it by a declared edge.
- **`hstab` is on the phase WINDOW**, not the whole chain — the unrestricted form
  was unsatisfiable by the extraction's own witnesses.

## 6. What a rewrite should say about the fragment's status

Certified, machine-checked: the horizontal ∀PO-free fragment both directions;
the persistent vertical multi-tower certificate, unconditional; the selection
machinery. Not certified: the `K(C)` width bound, the split-forest presentation,
the mixed assembly (in progress), nested `∃PP`, and F6 for the full logic.

The standing label for the fragment theorem is unchanged: **strongly supported,
soundness core machine-certified — not certified end-to-end, and unreviewed.**
