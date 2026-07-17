# Approach: The split-forest normal form

**Idea (the human author's, on a whiteboard).** A complete-graph RCC5 model
can be *presented* as a forest of trees by splitting join nodes into
EQ-mates and completing the missing horizontal edges by **patchwork**. This
is the sound semantic normal form (**Theorem A**) that every downstream
route consumes — and the one component no cold review ever broke.

Full treatment: overview paper, §"The split-forest idea" (and the whiteboard
photograph).

**Manuscripts**
- [Sibling-interface descriptors (v2)](../../papers/trees/sibling_interface_descriptors_ALCIRCC5_v2.pdf)
- [Split-forest + patchwork automata, self-contained edition (Theorem A spine)](../../papers/automata_route_repairs/split_forest_automata_with_appendices.pdf)

**Result.** Sound and repeatedly re-verified. It is a *normal form*, not by
itself a decision procedure: it does not bound the width of the presentation
— bounding that width is exactly the open keystone F6 (see
[`../Lean_F6/`](../Lean_F6/Overview.md)).
