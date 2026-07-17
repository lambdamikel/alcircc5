# Approach: The parity tree-automaton route

**Idea.** Keep the split-forest normal form (Theorem A) and decide the
finite search problem by **non-emptiness of a two-way alternating parity
tree automaton** over the finite split-forest profile alphabet — so
finite-checkability and simultaneous eventuality fulfilment come for free.
Global relational consistency rests on the citable **RCC5 patchwork
property** (Renz & Nebel). The load-bearing keystone is **Theorem B**
(finite-abstraction adequacy: finite patchwork bags capture saturated split
forests up to satisfiability).

**Why it is not closed.** A cold review showed the decision layer must
decide an *existential-projection* language — a valid abstraction is a pair
(tree, enrichment), only part of which is on the automaton's tape — and the
local monitors can accept a tree with no globally consistent labelling. The
missing coherence-forcing step is exactly the open keystone **F6**.

Full treatment: overview paper, §"The no-automata certificate, and the
automata route".

**Manuscripts**
- [Split-forest + patchwork automata + appendices (self-contained)](../../papers/automata_route_repairs/split_forest_automata_with_appendices.pdf)
- [A/B/C companion paper (Theorem A / B / C)](../../papers/automata_route_repairs/split_forest_companion_ABC_paper.pdf)
- [All round-12/14 repairs and referee reports](../../papers/automata_route_repairs/)

**Probes:** WP13–WP16 in [`verification/python/`](../../verification/python/).

**Result.** Cleanly reduces the whole problem to Theorem B / F6 using
standard external tools (patchwork property; Vardi parity-automaton
emptiness), but the adequacy keystone is unproved.
