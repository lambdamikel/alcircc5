COLD-REVIEW PACKET (round-16)  --  notes for the human, NOT for the reviewer
============================================================================

Purpose: a single drag-and-drop bundle for running a COLD review of the
current candidate stack -- round-12 base (model theory) + round-15
(cluster-quasimodel decision layer) + round-16 (certified joint
steering delta) -- in a FRESH GPT-5.5 session with no prior context.

This is the ELEVENTH review of the project if run. Ledger going in:
10 reviews, 10 defects.

CONTENTS
  split_forest_automata_with_appendices.pdf        base (29pp)
  cluster_quasimodels_round15.pdf                  decision layer (10pp)
  cluster_quasimodels_round16_joint_steering.pdf   delta (6pp)
  COLD_REVIEW_PROMPT.txt                           the prompt to paste
  README_FOR_HUMAN.txt                             this file

HOW TO RUN
  1. Open a FRESH GPT-5.5 session (no project files, no prior thread).
  2. Paste the PRIMARY PROMPT from COLD_REVIEW_PROMPT.txt.
  3. Attach ONLY the three PDFs above.

WHAT TO WITHHOLD (the answer key -- do NOT attach or paste)
  - all referee reports (papers/fable5_review/, papers/gpt5.5_round14/,
    papers/cold_review_round14/*packet*, papers/gpt5.5_round15_review/)
    and all response memos;
  - README.md, CLAUDE.md, CONVERSATION.md, OUTDATED.md;
  - all verification/ scripts and reports (WP1-WP28) -- note WP28's
    uniformization measurements are ALREADY quoted inside the round-16
    manuscript, which is fine (it is part of the candidate's own
    self-description); the scripts themselves stay withheld;
  - anything characterizing the prior findings beyond what the three
    manuscripts themselves say.

WHAT THE REVIEWER WILL UNAVOIDABLY KNOW (honest caveats)
  a. The stack self-describes its revision history: round 16 names the
     tenth review's witness and repairs it; round 15 names the ninth
     review's findings; both designate their own weak points in
     "what would invalidate" sections. This is by design -- the
     project's manuscripts carry their own audit trail -- and matches
     the round-14 packet precedent. What is withheld is the analysis
     depth: the full reports, severity arguments, probe logs, and
     scripts.
  b. The prompt tells the reviewer what the stack claims (soundness
     fully proved; completeness modulo one open lemma). Without this
     the review would be ill-posed: the stack is explicitly partial,
     and a reviewer must know which verdicts are being requested.
  c. Lineage: the base manuscript was authored by GPT-5.5 (a fresh
     session reviews its own lineage's document there), and the W1a
     witness quoted in round 16 was found by a GPT-5.5 session. The
     decision layer and delta are Claude-authored, so the cross-model
     property holds where it matters most (the new mathematics). For
     maximum independence a third lineage would be preferable; this
     packet follows the project owner's choice of GPT-5.5.

WHERE THE VALUE IS (for interpreting the result)
  The single most valuable outcome is a verdict on the SOUNDNESS claim:
  round 16 is the first round in the project's history whose
  model-construction half claims to contain no free choices and no
  unproved steps. If that claim survives a cold adversarial pass, the
  remaining work (uniformization, width details, core fixed point) is
  all on the completeness side, where failure means over-rejection,
  not wrong answers -- a qualitatively safer place for a decision
  procedure to be incomplete. If it does not survive, expect the
  defect in: the triangle taxonomy's "checked when the youngest was
  fresh" step, the reachability fixed point under core sharing, or the
  sufficiency of the state definition.

INTERPRETING THE RESULT
  - Concrete defect with witness -> defect #11; triage; round 17.
  - "Could not break the soundness claim" with a substantive checklist
    -> the first clean verdict on any load-bearing half in ten reviews.
    Do not upgrade the status label; the sanctioned next steps would be
    (i) mechanization of the soundness half (the deterministic
    construction and finite fixed point are unusually Lean-amenable)
    and (ii) the uniformization lemma as the remaining mathematics.
  - Either way the status label stays: strongly supported, not
    certified.
