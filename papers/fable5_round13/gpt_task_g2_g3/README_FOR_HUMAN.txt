G2/G3 TASK PACKET (round-13)  --  notes for the human, NOT for the model
=========================================================================

Purpose: a single drag-and-drop bundle for handing GPT-5.5 the designated
next targets of the round-13 repair: G2 (extraction within the
D-discipline / verticalization-vs-width) and G3 (the Coverage walk).
These are the two places round-13 itself says a defect would most likely
hide (its Section "What would invalidate this repair").

WHAT THIS IS AND IS NOT
  - It is a TARGETED adversarial + repair task: the model is told exactly
    where to attack, gets the full context (including the 7th review and
    all machine evidence), and is asked to either break G2/G3 with a
    concrete witness or discharge them with round-14-grade proofs.
  - It is NOT a cold review. A genuinely cold review of round-13 remains
    an open obligation regardless of how this task turns out. Coldness
    and targeting are complementary signals: targeted review has the best
    chance of finding the flagged defects fast; cold review is the only
    trustworthy "found nothing" signal.
  - Reviewer/author hygiene: round-13 was authored by Claude (the 7th
    reviewer), so GPT-5.5 -- the round-12 author, a different lineage --
    is the natural adversary for it. This restores the cross-model
    review pattern the project has used throughout.

CONTENTS
  TASK_PROMPT.txt                       the prompt to paste (verbatim)
  OPTIONAL_COLD_PASS.txt                a short unguided prompt; see below
  manuscripts/
    split_forest_shadow_amalgamation_round13.pdf   round-13 delta (10pp)
    split_forest_shadow_amalgamation_round13.tex
    split_forest_automata_with_appendices.pdf      round-12 base (29pp)
    split_forest_automata_with_appendices.tex
    referee_report_round12_fable5.pdf              7th review (9pp)
  verification/
    wp14_patchwork_property_check.py  + wp14_output.txt
    wp15_shadow_row_realizability.py  + wp15_output.txt
    wp16_round12_bag_acceptance.py    + wp16_output.txt
    wp17_round13_discipline_check.py  + wp17_output.txt
  support/
    alcircc5_reasoner.py, cover_tree_tableau.py    ground-truth oracle
    (wp16 needs: PYTHONPATH=../support python3 -u wp16_...py)

HOW TO RUN
  Recommended two-pass protocol:
  1. OPTIONAL COLD-ISH FIRST PASS: open a fresh GPT-5.5 session, paste
     OPTIONAL_COLD_PASS.txt, attach ONLY the two manuscript PDFs
     (round-13 + round-12), nothing else. This preserves an unbiased
     signal: if the fresh session independently converges on G2/G3, that
     confirms the target designation; if it finds something ELSE, you
     have learned more than the targeted pass alone could tell you.
  2. TARGETED PASS: in the same session afterwards (or a new one), paste
     TASK_PROMPT.txt and attach everything.
  Running only the targeted pass is fine too -- it is the primary task.

INTERPRETING THE RESULT
  - A concrete G2/G3 witness (a concept, or a tree-of-bags configuration
    passing round-13's listed tests) -> triage; expect a round-14 repair;
    the 7-reviews-7-defects series continues.
  - Proofs of Coverage + Extraction at round-12-appendix rigor -> fold
    into a consolidated round-14 edition; the next step is then a
    genuinely COLD review of the consolidated manuscript (a fresh
    session, neutralized packet, in the style of papers/cold_review_*),
    and/or mechanization: the Shadow Amalgamation Lemma is now a small,
    Lean-friendly target (four decide-able facts + patchwork).
  - Either way: status language stays "strongly supported, not
    certified"; update README / CLAUDE.md / CONVERSATION.md per house
    convention.

WITHHOLD LIST (for the optional cold-ish first pass ONLY)
  Attach only the two manuscript PDFs. Withhold: the 7th-review report,
  all wp* scripts and logs, this README, TASK_PROMPT.txt, and anything
  naming G2/G3, "Shadow Amalgamation gap", or prior findings. (For the
  targeted pass, nothing is withheld -- targeting is the point.)
