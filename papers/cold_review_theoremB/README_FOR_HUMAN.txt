COLD-REVIEW PACKET (automata route / Theorem B)  --  notes for the human
==========================================================================

Purpose: a drag-and-drop bundle for running a COLD review of the repaired
split-forest automata decidability proof, aimed at its load-bearing keystone --
the finite-abstraction theorem (Theorem B), the point both proof routes
converged on.

CONTENTS
  split_forest_automata_proof.pdf                 the proof (~18 pp)
  split_forest_normal_forms_and_abstractions.pdf  companion: Theorems A / B / C
  COLD_REVIEW_PROMPT.txt                           the prompt (+ optional focused pass)
  README_FOR_HUMAN.txt                             this file

HOW TO RUN
  1. Open a FRESH session of a frontier model with no prior context on this
     project (a fresh GPT-5.5, or any other frontier model, gives the most
     independence -- GPT-5.5 authored and self-reviewed the previous round, so a
     different model is preferable here).
  2. Paste the PRIMARY PROMPT; attach ONLY the two PDFs above.
  3. Run the primary (unguided) pass first; run the OPTIONAL FOCUSED PASS (on
     Theorem B) only if the primary returns no defect.

WHY THIS REVIEW MATTERS
  The previous two cold reviews (round-9 no-automata, and the original automata
  proof) BOTH reduced to the same keystone: a finite representation of all
  global pairs/triples + compositional universal propagation + exact equality
  congruence.  The repaired proof + companion isolate that as Theorem B.  So
  Theorem B is exactly where a defect, if one remains, will be -- this packet
  points the review there.

WHAT TO WITHHOLD (these would un-cold the reviewer -- do NOT attach or paste)
  - papers/automata_route_repairs/rcc5_split_forest_referee_report.*  (the prior
    review -- the answer key: the exact defects and the four acceptance tests)
  - papers/automata_route_repairs/formal_response_automata_referee_repair.*
  - the ORIGINAL automata proof
    (papers/gpt5.5_final/split_forest_automata_decidability_proof_detailed.*) and
    the whole no-automata thread (gpt5.5_round2/3/4, claude_latest_review...)
  - README.md, CLAUDE.md, CONVERSATION.md, OUTDATED.md
  - the verification/ scripts (WP1-WP13, including wp13's acceptance tests)
  - anything that says "referee", "repair", "round N", "Theorem B keystone",
    "Patch invariant gap", "strongly supported", or describes a prior finding.
  The load-bearing property of a useful cold review is that the reviewer has the
  PROOF but not the ANSWER KEY.

COLDNESS MEASURES ALREADY TAKEN (vs. the originals in automata_route_repairs/)
  These two PDFs were recompiled from copies with the history/version framing
  neutralised on the first-read surfaces:
    - the proof's title no longer says "Repaired"; its abstract no longer says
      "the repair addresses the main defects identified in referee feedback ..."
      (which would hand the reviewer the prior findings); the "Motivation and
      repair summary" and "How the repaired proof addresses the referee
      findings" sections are removed/neutralised;
    - the companion's "Companion Paper" subtitle and "this companion paper"
      phrasing are neutralised.
  The MATHEMATICS is the originals' content; the originals in
  papers/automata_route_repairs/ are untouched.

RESIDUAL (honest caveat)
  A few mid-body words still say "repair"/"referee" (~4 in the proof, ~3 in the
  companion).  This is a minor leak: a careful reader of all 18 pages may infer
  this is a revision.  That is acceptable -- real referees review revisions and
  still find new defects.  If you want maximum coldness, ask Claude to scrub the
  mid-body mentions and recompile.

INTERPRETING THE RESULT
  - A concrete defect (with a witness concept) on Theorem B -> triage, repair.
  - "I tried hard to break Theorem B and could not", with a substantive
    checklist -> this would be the FIRST cold review on this project to find
    nothing, and the first real signal to consider mechanisation (Lean/Coq of
    Theorem B) rather than another prose round.
