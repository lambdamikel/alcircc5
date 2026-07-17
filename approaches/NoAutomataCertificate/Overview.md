# Approach: The no-automata hand certificate (rounds 2–10)

**Idea.** A finite syntactic *certificate* whose validity is checked by
local conditions (converse, composition, universal safety, request
discharge), so that "satisfiable" ⇔ "admits a valid finite certificate."

**Why it converged away.** Across ten rounds it kept reducing to
automaton-shaped machinery it could not fully discharge: request-closed
cycles behave like Büchi/parity acceptance, and "finite product-state
exhaustion" is product-automaton reachability. A sequence of cold reviews
found real gaps — the forced ancestor PPI-tower, its dual descendant
PP-tower, finite-checkability never proved, boundary non-determinacy — each
repaired, but the repairs were automaton-shaped. This motivated using an
automaton directly (see [`../Automata_Parity/`](../Automata_Parity/Overview.md)).

Full treatment: overview paper, §"The no-automata certificate, and the
automata route"; the full round-by-round history is in
[`../../OUTDATED.md`](../../OUTDATED.md).

**Manuscripts**
- [`papers/gpt5.5_round2/`](../../papers/gpt5.5_round2/), [`round3/`](../../papers/gpt5.5_round3/), [`round4/`](../../papers/gpt5.5_round4/), [`gpt5.5_final/`](../../papers/gpt5.5_final/)

**Probes:** WP7–WP12 in [`verification/python/`](../../verification/python/).

**Result.** A historical thread, retained as the audit trail — not wrong,
but superseded by the automata packaging of the *same* keystone. Its
repeatedly-rediscovered hard steps (finite checkability, simultaneous
eventuality fulfilment) are exactly what an automaton discharges by
construction.
