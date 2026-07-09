COLD-REVIEW PACKET (round-14)  --  notes for the human, NOT for the reviewer
============================================================================

Purpose: a single drag-and-drop bundle for running a COLD review of the
current candidate decidability statement -- round-12 (base) + round-13
(delta; partially superseded) + round-14 (active-virtual-bag repair) -- in
a FRESH Fable 5 session with no prior context on this project.

CONTENTS
  split_forest_automata_with_appendices.pdf        round-12 base (29pp)
  split_forest_shadow_amalgamation_round13.pdf     round-13 delta (10pp)
  split_forest_round14_repaired_proof.pdf          round-14 repair (12pp)
  COLD_REVIEW_PROMPT.txt                           the prompt to paste
  README_FOR_HUMAN.txt                             this file

HOW TO RUN
  1. Open a FRESH Fable 5 session (no project context; do not run it in
     this repository or with this repo's CLAUDE.md in scope).
  2. Paste the PRIMARY PROMPT from COLD_REVIEW_PROMPT.txt.
  3. Attach ONLY the three PDFs above.

WHAT TO WITHHOLD (these are the answer key -- do NOT attach or paste)
  - all referee reports: papers/fable5_review/ (7th review),
    papers/gpt5.5_round14/round13_g2_g3_referee_report.* (8th review),
    papers/gpt5.5_round14/round14_delta_after_g2a.* (emergency delta),
    and every earlier report;
  - README.md, CLAUDE.md, CONVERSATION.md, OUTDATED.md;
  - all verification/ scripts and reports (WP1-WP25), especially the
    attack harnesses wp15/wp18/wp19;
  - anything naming "Shadow Amalgamation gap", "G2a", "F1", review counts,
    or what any prior review found.

COLDNESS -- honest caveats
  a. The three manuscripts are attached AS-IS (no neutralization pass).
     They are explicitly a revision stack: round-14's own text names the
     defect it repairs (the G2a tower and the withdrawn round-13 clauses).
     So the reviewer WILL know the revision history of the two most recent
     defects. That is acceptable and unavoidable here: real referees
     review revisions, and every prior cold review on this project found a
     NEW defect anyway. What is withheld is the analysis: the reports, the
     severity grades, the named residual targets, and the machine attack
     scripts.
  b. Lineage: round-13 was authored by a Fable 5 session (a different,
     context-loaded session). A fresh Fable 5 is context-cold but shares
     the lineage of the round-13 author; round-14 -- the main review
     target -- is GPT-5.5's, so the cross-model property holds where it
     matters most. If maximum independence is wanted, run the same packet
     additionally past a third lineage.
  c. The reviewer is told the stack structure (base + two deltas) because
     hiding it would make the task incoherent; it is NOT told where the
     current designated weak points are (the automaton monitor
     bookkeeping, the single-shadow closure explicitness, the inherited
     width accounting). Whether a cold reviewer independently lands on
     those -- or on something new -- is exactly the signal.

INTERPRETING THE RESULT
  - A concrete defect (with a witness concept, configuration, or a broken
    lemma) -> triage; round-15; the series continues (currently 8 reviews,
    8 defects).
  - "Could not break it" with a substantive checklist -> the FIRST clean
    review in the project's history. Do not upgrade the status label on
    one clean review; the sanctioned next steps would be a second cold
    review by a third lineage and/or mechanization (the finite core +
    active amalgamation lemma are Lean-friendly).
  - Either way, the status label stays: strongly supported, not certified.
