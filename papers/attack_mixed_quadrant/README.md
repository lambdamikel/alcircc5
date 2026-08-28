# Attack packet — the mixed quadrant of the ∀PO-free fragment (2026-08-27)

**A request for ideas, not a review.** Three open problems have been isolated
from a decidability argument for the ∀PO-free fragment of ALCI_RCC5. Progress on
any one is the goal.

## Read in this order

1. **`ATTACK_PROMPT.md`** — the primer (§0: assumptions you must not misread),
   where the development stands (§1), the three targets (§§2–3), and — important
   — **§4, routes already refuted with machine-checked witnesses.**
2. **`CERTIFICATE.md`** — the certificate's exact 19 obligations, self-contained,
   and where each one currently stands.
3. **`./run_probes.sh`** — pure Python 3, no dependencies.

## The three targets, in one line each

* **A — the GROUP problem** *(recommended)*. Blocking gives one expanded node per
  model type, which spawns one child per demand; but several blocked nodes of
  that type may need different witnesses. Measured: one witness serves the whole
  group **91.8%** of the time, and in **0 of 140** failures does the model contain
  any common upper at all. Lead: declare a fresh "class top" and ask whether its
  label is always realizable.
* **B — the CROSS-KERNEL RECTANGLE**. Kernel-to-external rows can be stabilized
  because the externals are fixed points; kernel-to-kernel rows cannot, because
  both sides move. Is there a simultaneous stabilization theorem for finitely
  many interacting periodic towers?
* **C — the SELECTION-ORDER CIRCULARITY**. A kernel's witnesses must go into the
  external set, but the external set must be fixed before the kernel's segment is
  chosen. Probably the same obstruction as B.

## Honest scope

The Lean development is ~41,400 lines, 0 sorries, 0 warnings, axioms
`propext` / `Quot.sound` / `Classical.choice`. It is **unreviewed**: this project
has a ledger of seventeen reviews and found a defect or overclaim in all but two,
so assume something here is wrong and say so if you find it.

All probe numbers are finite randomized sweeps over **finite set models**, so
kernels are not exercised by them. Kernel claims are Lean-certified, not
probe-measured. The 91.8% and the 0/140 are measurements, not theorems.

Decidability of the FULL logic ALCI_RCC5 is a separate, older open problem (F6)
and is **not** what this packet is about.
