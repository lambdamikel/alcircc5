W1/W2/W3 TASK PACKET (round-15)  --  notes for the human, NOT for the model
============================================================================

Purpose: drag-and-drop bundle handing GPT-5.5 the round-15 manuscript's
self-designated weak points: W1 (the steering induction, Lemma 4.3 --
the keystone), W2 (horizontal normal form / extraction, Lemma 5.2 and
Theorem 5.1), W3 (width recurrence and the core, Section 6 / (Q5)).
This continues the author/adversary alternation: Claude authored rounds
13 and 15; GPT-5.5 authored rounds 12 and 14 and broke round 13; a fresh
Fable 5 cold review broke round 14. The ledger is 9 reviews, 9 defects.

WHAT THIS IS AND IS NOT
  - A TARGETED adversarial + repair task, full context included (the 9th
    review, the harnesses, the oracle). NOT a cold review; if round 15
    survives this pass, the next step is a genuinely cold review by a
    third lineage (or a fresh session), per protocol.

CONTENTS
  TASK_PROMPT.txt          the prompt to paste (verbatim)
  OPTIONAL_COLD_PASS.txt   short unguided prompt (manuscripts only)
  manuscripts/             round-15 (target), round-12 base (Theorem A +
                           patchwork, inherited), round-14 (certified
                           semantic pattern, cited)
  context/                 the 9th review, packets 1-3
  verification/            wp26 (+ output), wp14/wp17 (+ outputs)
  support/                 tableau oracle + concept classes
                           (PYTHONPATH=support for wp26)

HOW TO RUN
  Recommended two-pass protocol, as before:
  1. OPTIONAL: fresh session, paste OPTIONAL_COLD_PASS.txt, attach ONLY
     the three manuscript PDFs. Unbiased first signal: does it land on
     W1-W3 independently, or find something else?
  2. TARGETED: paste TASK_PROMPT.txt, attach everything.

INTERPRETING THE RESULT
  - Concrete witness against W1/W2/W3 or the general targets -> defect
    #10; triage; round 16.
  - Full expanded proofs of Lemma 4.3 / Lemma 5.2 / the width extraction
    -> fold into a consolidated round-16 edition; then a COLD review by
    a fresh session (note: both lineages have now authored parts of the
    stack; a third lineage would give the cleanest independence), and/or
    mechanization -- W1 is a finite case analysis over a 10-element
    lattice plus the patchwork theorem: the most Lean-amenable keystone
    the project has had.
  - Either way the status label stays: strongly supported, not
    certified.

WITHHOLD LIST (for the optional cold-ish first pass ONLY)
  Attach only the three manuscript PDFs. Withhold: context/ (the 9th
  review), all wp* scripts and outputs, this README, TASK_PROMPT.txt,
  and anything naming W1-W3 or prior findings.
