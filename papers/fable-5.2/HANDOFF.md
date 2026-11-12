# Handoff: `lambdamikel/alcircc5`, work of 2026-11-11

For the Claude Code session that has push access, and for Michael. Self-contained:
everything needed to apply, verify and push is in this folder.

The producing session (Claude Fable 5.2, cloud) could read the repository but not
write to it. **Nothing has been pushed.**

**Instruction to the receiving session, in one line:** apply the bundle as a
fast-forward of `master` (§3), run the checks of §4, push (§5), and do not move the
release tag.

---

## 1. What is in the package

| file | what it is |
|---|---|
| `HANDOFF.md` | this file |
| `alcircc5-2026-11-11.bundle` | **the change**: 8 commits on top of `52d392e` (the current `origin/master`), branch `alcircc5-2026-11-11`, head `085aaa2dc109dd71e990e4ac38fbbaf630867b9b` |
| `changes-text-only.diff` | the same change as a readable diff, PDFs excluded. For reading, not for applying. |
| `read/ERRATA.md`, `read/poset_bridge_note.md`, `read/midelora_calculus_note.md` | reading copies of three files that are inside the bundle |
| `SHA256SUMS` | checksums of the files above |

## 2. What the change is

Full-logic decidability is **still open**. Eight commits, 31 files, +4,764 / −39:

```
b85b614  PosetBridge.lean: two-variable logic over strict partial orders embeds into ALCI_RCC5
3c2c737  wp137: brute-force companion to the poset bridge
92c8137  papers/poset_bridge: the note
fc4ceff  Errata: the withdrawn Szwast-Tendera theorem; the tableau's record
e450e43  Status: the poset bridge (README, CLAUDE.md, CONVERSATION.md)
1b76ef9  Audit of published claims: ERRATA.md and the corrections it lists
b4e6136  cover_tree_tableau: experimental nested-witness sibling check (off by default); wp138
085aaa2  The MiDeLoRa calculus as a reference reasoner: sound, complete, not terminating
```

Three pieces of work:

1. **The poset bridge and the errata** (commits 1–6). A Lean-checked embedding of
   two-variable logic over strict partial orders into ALCI_RCC5
   (`formal/PosetBridge.lean`, imports the certified artifact), so the full logic
   contains the unary case of an open problem; and the correction of two
   published statements, recorded in `ERRATA.md`. Five papers corrected (`.tex` and
   rebuilt `.pdf`): overview, fragment paper, slides, tableau paper, ∀PO-free
   explainer.
2. **An experimental repair of the cover-tree tableau** (commit 7), behind
   `check_satisfiability(C, nested_witnesses=True)`. **Off by default**; the shipped
   behaviour is unchanged. If Michael does not want it, `git revert b4e6136`
   removes it cleanly before pushing — commit 8 does not depend on it in code,
   though it would then leave conflicts in the three doc files commit 8 also
   touches (`CLAUDE.md`, `CONVERSATION.md`, `verification/README.md`,
   `approaches/Tableaux/Overview.md`); resolve by keeping commit 8's additions.
3. **The MiDeLoRa calculus** (commit 8): the complete-graph tableau of Michael's
   dissertation, proved sound and complete (not terminating) for strong EQ on
   paper (`papers/midelora_calculus/README.md`) and implemented as a reference
   reasoner (`src/midelora_tableau.py`).

`formal/POFreeLift.lean` is **not** touched. Commits 7 and 8 touch no Lean file.

Where to read: `ERRATA.md`; `papers/poset_bridge/README.md` §0;
`papers/midelora_calculus/README.md` §0 and §3; the first status paragraph of
`CLAUDE.md`, which summarizes all of it for an agent.

## 3. Apply

```bash
cd alcircc5
git status --short            # expect: clean
git fetch origin && git rev-parse origin/master
#   expect: 52d392eca358c7c0a3e0ddfdb51142dfe12fdeb2

git fetch /path/to/alcircc5-2026-11-11.bundle \
    alcircc5-2026-11-11:alcircc5-2026-11-11
git checkout master
git merge --ff-only alcircc5-2026-11-11
git rev-parse HEAD
#   expect: 085aaa2dc109dd71e990e4ac38fbbaf630867b9b
```

**If `origin/master` is no longer `52d392e`:** the fast-forward will refuse. Rebase
(`git rebase origin/master alcircc5-2026-11-11`). Expect conflicts only in
`README.md`, `CLAUDE.md`, `CONVERSATION.md` (each gets new entries at a fixed
place) and in the five PDFs. For a PDF conflict take either side and rebuild from
the merged `.tex`. Do not hand-merge the Lean file.

## 4. Verify before pushing

**What the producing session verified, and how.** Commits 1–6: on a pristine clone
with the bundle applied — both Lean builds, `wp137`, the tableau's tests, the
PDFs. Commit 7: on that clone — tableau tests, `wp137`, `wp138`, the Lean build of
`PosetBridge`. Commit 8: all three probes and both reasoners' tests in the working
tree at the committed content; on a pristine clone the fast-forward, the head
hash, the tableau's 35 tests and the reference reasoner's examples. The full
clean-clone run of `wp139` for commit 8 was started and interrupted, so **run it
here**. No Lean file changed after the last clean-clone Lean build.

**Lean** (pinned 4.33.1; the elan default has moved on):

```bash
cd formal
elan run leanprover/lean4:v4.33.1 lean -o POFreeLift.olean POFreeLift.lean
LEAN_PATH=. elan run leanprover/lean4:v4.33.1 lean PosetBridge.lean
```

Expect: both exit 0, no `error`, no `warning`; 16 `#print axioms` lines, each
`[propext, Classical.choice, Quot.sound]`, `[propext, Quot.sound]` (`walk_inj`) or
"does not depend on any axioms" (`spiralConcept_noExVert`,
`k2_witnesses_nested`). About a minute for the first command. `PosetBridge.lean`
imports the artifact, which is why the first command writes an `.olean`
(git-ignored).

**Reasoners and probes:**

```bash
(cd src && python3 cover_tree_tableau.py | tail -4)    # 35 passed, 0 failed
(cd src && python3 midelora_tableau.py)                 # K2 SAT; K2x strong UNSAT, weak SAT; UNKNOWN
python3 verification/python/wp137_poset_bridge_probe.py           # 27/27, ~25 s
python3 verification/python/wp138_tableau_nested_witnesses.py     # 14/14, 1-4 min
python3 verification/python/wp139_midelora_reference.py           # 33/33, ~3 min
```

`wp137` reports `26/26` with one `[SKIP]` line if the optional `python-sat`
package is missing; that is fine.

**PDFs.** They are in the bundle; nothing needs rebuilding. Sanity check:

```bash
for f in overview_arxiv pofree_fragment_arxiv talk_ALCIRCC5 \
         cover_tree_tableau_ALCIRCC5 why_po_free_decidable; do
  echo "$f $(pdfinfo papers/$f.pdf | awk '/Pages/{print $2}') pages," \
       "$(pdffonts papers/$f.pdf | grep -c 'Type 3') bitmap fonts"
done
```

Expect 57, 20, 43, 13, 19 pages and `0 bitmap fonts` each. **If you rebuild any
PDF, the TeX installation must have `cm-super`.** Without it pdfTeX silently
substitutes bitmap fonts and nothing else changes.

## 5. Push

```bash
git push origin master
```

The repository's convention is direct pushes to `master`. Do **not** move the tag
`release-2026-09-14`.

## 6. Decisions that are Michael's

1. **The tag.** `release-2026-09-14` still points at papers that contain both
   errata. Move it (as on 2026-10-08) or cut a new tag.
2. **Commit 7**, the tableau flag: keep (default unchanged) or revert (§2).
3. **The papers' status tables.** The papers were corrected, not re-synced: their
   tables do not list the two decided slices that come by import, the new infinity
   axiom, or the reference reasoner.
4. **Whether to write to the authors** of the two-variable papers (Tendera,
   Marzec, Pratt-Hartmann). The bridge is a statement about their open problem.
5. **Next step on the calculus**, if wanted: formalize refutation soundness in
   Lean, which would turn closed tableaux into kernel-checkable UNSAT
   certificates; or port the strong-EQ rule into MiDeLoRa itself (wire
   `join-nodes` into the JEPD prover).

## 7. What is not done, and what the work rests on

* **Unreviewed.** One session, no cold review. The project's ledger says a defect
  or overclaim was found in 19 of 22 reviews; presume this has one.
* The bridge's Lean theorem is about pattern systems (a normal form). The step
  from an arbitrary two-variable sentence to that normal form is textbook and
  **not** formalized.
* The two decided slices come **by import** from published theorems. Only the
  bridge is Lean-checked.
* "Open" is the literature's status as of Marzec & Tendera (J. Logic Comput.,
  online January 2026); of that paper the abstract, the introduction and the 2024
  workshop version were read in full.
* **The MiDeLoRa theorem is a paper proof.** Only its last step (a Hintikka
  labelling of an RCC5 frame is a model) is Lean-checked. The reasoner is tested
  — exact ground truth on 1,000 concepts, the 911 suite, named concepts — not
  verified, and emits no proof objects.
* MiDeLoRa itself was read, not run (LispWorks/Allegro). The dissertation was
  read in three sections, as extracted text.
* The tableau repair of commit 7 is evidence-backed only, and its test class has
  no nested existentials.
* **Not tested, and the natural next test of F6:** whether the certificate format
  of `formal/Round19Transport.lean` admits a certificate for `spiralConcept`.
* F6, bare `∀PO` in the certificate route, and the interaction of `DR`'s downward
  closure with `∀PO` are untouched.

## 8. Do not

* cite Szwast & Tendera 2013 as a decidability theorem;
* say that no verdict of the cover-tree tableau has been shown wrong, or call it
  a decision procedure;
* call the imported slices, or the MiDeLoRa theorem, Lean-certified;
* say the reference reasoner decides the logic — it does not terminate on
  concepts with only infinite models;
* claim a reduction **from** ALCI_RCC5 into a two-variable logic — none is known;
* describe full-logic decidability as anything but open.

## 9. Provenance

Commits are authored `Claude Fable 5.2 <noreply@anthropic.com>` and carry
`Co-Authored-By` and `Claude-Session` trailers. Base: `52d392e` ("Sync the
articles with the Astra 6 harvest; fix the tag-delta sentence").
