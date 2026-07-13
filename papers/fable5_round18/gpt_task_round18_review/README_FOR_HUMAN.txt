ROUND-18 REVIEW PACKET (13th review)  --  notes for the human, NOT the model
============================================================================

Purpose: hand GPT-5.5 the round-18 delta for the thirteenth review:
acceptance test against its own lineage's M1-M6 (twelfth review), with
the audit of round-18's DEPARTURE from the work order called out as a
first-class task -- round-18 claims M1's two-case update was incomplete
and adds a third "birth-flip" clause. Whether that claim is right, and
whether the clause is correct, is exactly what an adversarial reviewer
should decide.

CONTENTS
  TASK_PROMPT.txt          the prompt (verbatim)
  OPTIONAL_COLD_PASS.txt   unguided first pass (five manuscript PDFs only)
  workorder/               the 12th review (Findings 17.1-17.5, M1-M6)
  manuscripts/             round-18 (target) + rounds 17/16/15 + base
  verification/            wp28/30/31/32 + outputs
  support/                 tableau oracle (PYTHONPATH=support)

HOW TO RUN: the usual two-pass protocol (optional cold pass with only
the five manuscript PDFs first; then the targeted pass with everything).

INTERPRETING THE RESULT
  - "Not discharged" / a Part-II witness -> the next defect; round 19.
  - Acceptance on M1-M6 incl. the birth-flip audit, nothing in Part II
    -> the transition system has survived its author-swap acceptance
    test; next steps are the Lean transcription (the U-clauses are the
    function definitions) and the completeness campaign (F6, W2'),
    possibly delivered as Part III by the same session. No status
    upgrade regardless.
  - Either way: strongly supported, NOT certified.

WITHHOLD (optional cold pass only): everything except the five
manuscript PDFs.
