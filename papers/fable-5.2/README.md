# The 2026-11-11 handoff: received, checked, applied

This folder is the handoff package of a cloud session (Claude Fable 5.2) that
could read the repository but not write to it. Michael placed it here on
2026-11-11; a local session of the same model, with push access, applied it the
same day. This file records what the receiving session did and what it checked.

## What is here

| file | what it is |
|---|---|
| `HANDOFF.md` | the producing session's instructions, as received |
| `midelora_calculus_note.md` | as received; byte-identical to [`papers/midelora_calculus/README.md`](../midelora_calculus/README.md) |
| `handoff_alcircc5_2026-11-11.zip` | **not tracked** (git-ignored). It holds a git bundle whose eight commits are now `b85b614..085aaa2` on `master`, so the repository already contains its content. SHA-256 of the zip as received: `4eaca43e773d31a50d4bfedb90c2c45fad83eae6f3f0f3e07b7c5a5a1704002a` |

The copy of `HANDOFF.md` inside the zip differs from the one here in three lines
of §2 (the wording of what a revert of commit 7 would conflict with). Nothing
else differs.

## What was applied

The bundle, as a fast-forward of `master` from `52d392e` to
`085aaa2dc109dd71e990e4ac38fbbaf630867b9b`, pushed unchanged. The tag
`release-2026-09-14` was **not** moved; it still points at `52d392e`.

## Checks run before the push

On a clean worktree at `085aaa2`, on this machine:

| check | result |
|---|---|
| `SHA256SUMS` of the package; `git bundle verify` | all OK; the bundle requires exactly `52d392e` |
| `POFreeLift.lean` on Lean 4.33.1 | exit 0, 66 s; no error, no warning, no `sorryAx` |
| `PosetBridge.lean` against it | exit 0; 16 `#print axioms` lines, as the handoff lists them |
| `PosetBridge.lean` scanned for `sorry`, `axiom`, `native_decide`, `unsafe`, `opaque`, `partial`, `set_option` | none |
| `src/cover_tree_tableau.py` | 35 passed, 0 failed; matches the oracle |
| `src/midelora_tableau.py` | `K2` SAT; `K2x` UNSAT strong, SAT weak; the `PP`-tower `UNKNOWN` |
| `wp137` | 26/26, with the one `[SKIP]` the handoff allows (`python-sat` is not installed here, so the spiral's finite non-models were searched to 6 points, not 9) |
| `wp138` | 14/14 (98 s) |
| `wp139` | 33/33 (280 s) — the full run the producing session had to interrupt |
| the five PDFs | 57, 20, 43, 13, 19 pages; no bitmap fonts |

The scripts were read for imports and side effects before they were run: they
compute and print, and do nothing else.

## Checks beyond the handoff's list

* **E1, against primary sources.** The arXiv record of 1804.09447 (three
  versions, April 2018 to April 2019) states that the 2013 claim does not stand
  and that the status of the full problem "remains open". The introduction of
  Marzec & Tendera's CILC 2024 paper says the same of the 2013 proof, defines
  the spiral with five predicates exactly as `spiralSys` does, and closes by
  naming the unary fragment with entanglements and incomparable witnesses as the
  critical one and saying "we believe that the fragment is decidable". The
  journal version exists as cited (J. Logic Comput. 36(2), exaf068, online
  26 January 2026); its abstract was read, not its body. Pratt-Hartmann's
  abstract (Math. Log. Quart. 64(3)) gives the two finite-satisfiability bounds
  as cited.
* **E2, on the shipped code.** At `52d392e`, before the bundle was applied,
  `cover_tree_tableau.check_satisfiability(K2)` returns
  `(False, 'all branches closed')` and the quasimodel oracle returns SAT. The
  three-region model `r = {1,3}`, `a = {1,4}`, `b = {1,4,5}` was checked by hand:
  `r PO a`, `r PO b`, `a PP b`; `a` has no `PO`- or `DR`-neighbour in `B`.
* **The Lean statements, read.** `SPO` is irreflexive and transitive; `inc` is
  "distinct and unrelated"; `psat` is the usual recursion; `emb` is the table of
  the note. `k2_shape` fixes `K2` by `rfl`, so `k2_sat` is about the concept the
  text prints. `spiralConcept_infinite` quantifies over every `RCC5Interp` and
  yields an injective sequence inside the domain. `Satisfiable` is the
  artifact's, by import.
* **The two paper proofs, read.** The bridge (note §2) and the calculus
  (`midelora_calculus`, Lemmas 1 and 2 and the theorem) were read through and no
  error was found.
* **The diffs to the live documents, read**: the four `.tex` files, the README,
  `CLAUDE.md`. The corrections say what `ERRATA.md` says they say.

## What this does not amount to

It is not a review. The receiving session is the same model as the producing
one and worked with the project's context loaded, which is the kind of reading
this project's record says finds least. The proofs of the imported theorems
were not checked. `PosetBridge.lean` was read at the level of definitions and
statements, not proof by proof — the kernel checks those. The step from an
arbitrary two-variable sentence to a pattern system remains unformalized. The
work is still **unreviewed**, as every document it added says.

## Left for Michael

The five decisions of `HANDOFF.md` §6 are untouched: the tag; whether to keep
the tableau's experimental flag; whether to re-sync the papers' status tables;
whether to write to the authors of the two-variable papers; and the next step
on the calculus.
