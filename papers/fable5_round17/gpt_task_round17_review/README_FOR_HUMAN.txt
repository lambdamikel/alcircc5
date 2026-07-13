ROUND-17 REVIEW PACKET (12th review)  --  notes for the human, NOT the model
============================================================================

Purpose: hand GPT-5.5 the round-17 delta for the twelfth review, framed
as an ACCEPTANCE TEST against the eleventh review's own work order
(R1-R6) plus the new attack surface (Y1-Y4) and, optionally, the two
standing open items (F6 width budgets, W2' uniformization) as round-18
material.

WHY THIS FRAMING. The 11th review (cold, GPT lineage) ended with: "With
these changes, I would regard the intended soundness argument as very
likely correct." Round-17 claims to implement exactly those changes.
The highest-value question is therefore not "find any defect" but "does
the implementation discharge the work order as intended, and does the
NEW text introduce new defects?" -- with the ledger presumption (11
reviews: 10 defects-with-witness, 1 no-counterexample-with-repairs)
applied to the new material in full.

CONTENTS
  TASK_PROMPT.txt            the prompt to paste (verbatim)
  OPTIONAL_COLD_PASS.txt     unguided first pass (manuscripts only)
  workorder/                 the 11th review (R1-R6; App B transport rule)
  manuscripts/               round-17 (target), round-16, round-15,
                             round-12 base (only Theorem A + patchwork live)
  verification/              wp26/28/29/30 + outputs
                             (wp30 = executable transition system)
  support/                   tableau oracle (PYTHONPATH=support)

HOW TO RUN
  Two-pass protocol as usual:
  1. OPTIONAL: fresh session, OPTIONAL_COLD_PASS.txt, attach ONLY the
     four manuscript PDFs -- an unbiased signal on the new text.
  2. TARGETED: paste TASK_PROMPT.txt, attach everything.

INTERPRETING THE RESULT
  - "Not discharged" on any R-item, or a Y1/Y2 witness -> defect #11
    (or a formalization re-do); round 18.
  - Acceptance on R1-R6 + nothing on Y1-Y4 -> the soundness half of the
    decision layer has survived both its cold review's work order and
    an adversarial acceptance test. Do NOT upgrade the status label.
    The sanctioned next steps: (i) Lean transcription of the transition
    system + Theorem 3.1 + the canonical completion (now transcription,
    not research); (ii) the completeness campaign (F6, W2') -- possibly
    delivered by this same session as Part III.
  - Either way: strongly supported, NOT certified.

WITHHOLD (for the optional cold pass ONLY): everything except the four
manuscript PDFs. For the targeted pass, nothing is withheld -- the work
order is the point.
