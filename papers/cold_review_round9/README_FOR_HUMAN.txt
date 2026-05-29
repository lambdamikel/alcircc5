COLD-REVIEW PACKET (round-9)  --  notes for the human, NOT for the reviewer
===========================================================================

Purpose: a single drag-and-drop bundle for running a COLD review of the round-9
ALCI_RCC5 split-forest decidability proof in a fresh model session.

CONTENTS
  split_forest_decidability_proof_sketch.pdf     16-page proof sketch
  split_forest_decidability_proof_expanded.pdf   32-page companion
  COLD_REVIEW_PROMPT.txt                          the prompt to paste (+ optional
                                                  focused follow-up)
  README_FOR_HUMAN.txt                            this file

HOW TO RUN
  1. Open a FRESH session of a frontier model with no prior context on this
     project (see "WHICH MODEL" below).
  2. Paste the PRIMARY PROMPT from COLD_REVIEW_PROMPT.txt.
  3. Attach ONLY the two PDFs above.
  4. Run the primary (unguided) pass first. Run the OPTIONAL FOCUSED PASS only
     if the primary pass returns no defect -- so the first pass stays unbiased.

WHAT TO WITHHOLD (these would un-cold the reviewer -- do NOT attach or paste)
  - papers/gpt5.5_round3/formal_response_opus48_round9_repair.*  (response memo)
  - the entire papers/opus4.8_review/ folder (the prior review + the answer key:
    the C0' counterexample, the severity grade, the proposed fix)
  - papers/gpt5.5_round3/round9_repair_README.txt
  - README.md, CLAUDE.md, CONVERSATION.md, OUTDATED.md
  - the verification/ scripts (WP1-WP11)
  - anything that says "D-1", "the gap", "round-8 defect", "strongly supported",
    or describes what a prior review found.
  The load-bearing property of a useful cold review is that the reviewer has the
  PROOF but not the ANSWER KEY.

COLDNESS MEASURES ALREADY TAKEN (vs. the originals in papers/gpt5.5_round3/)
  These two PDFs were recompiled from copies with the version/history framing
  neutralised on the first-read surfaces:
    - titles no longer say "Round-9 Repaired ... Forced Verticalization";
    - the abstracts no longer say "the repaired proof" / "the new round-9 repair
      addresses the unbounded side/tree defect" (which would have handed the
      reviewer the prior finding);
    - the one section heading that named the repair was neutralised.
  The MATHEMATICS is byte-for-byte the originals' content -- only framing words
  were changed. GPT-5.5's original files in papers/gpt5.5_round3/ are untouched.

RESIDUAL (honest caveat)
  A handful of mid-body words still say "repair" (~5 sketch, ~2 expanded) and
  "round-8" (x2, sketch), in passages that motivate the construction. This is a
  minor leak: a careful reviewer reading all 32 pages will infer this is a
  revision. That is acceptable -- real referees review revisions and still find
  new defects (every prior cold review on this project did). If you want MAXIMUM
  coldness, ask Claude to scrub those mid-body markers too and recompile; it is a
  bounded edit but risks lightly rephrasing the author's prose, so it was left
  out by default.

WHICH MODEL
  The load-bearing property is FRESHNESS (no project context), not the model
  identity. Note:
    - a fresh Opus 4.8 session is context-cold, but Opus 4.8 proposed the
      original repair, so it has latent familiarity with this exact area;
    - GPT-5.5 authored the proof;
    - => a fresh GPT-5.5 OR any other frontier model gives the most genuine
      independence. Any fresh session is still useful.

INTERPRETING THE RESULT
  - A concrete defect (with a witness concept) -> triage, then repair (round-10).
  - "I tried hard and could not break it" with a substantive checklist -> this
    would be the FIRST cold review on this project to find nothing, and the
    first real signal to consider the Lean formalisation step.
