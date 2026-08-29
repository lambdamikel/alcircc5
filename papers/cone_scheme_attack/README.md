# Cold attack packet — a claimed decision procedure for the ∀PO-free fragment
### 2026-08-28

**Read `ATTACK_PROMPT_3.md` first**, then `VERIFY.md`.

## The one-line claim

```lean
def decidableSat_cone (C0 : Concept) (hpo : POFree C0) : Decidable (Satisfiable C0)
```

No unproved premise. Carrier-polymorphic `Satisfiable`. Covers the whole
fragment, mixed quadrant included — the case your two previous reports attacked
and that has been open since 2026-08-06.

## Why we are sending it

Not for confirmation. This arrived in one working session, right after four
successive extraction disciplines were refuted (two of them by you) and a paper
that had survived four adversarial rounds was found to contain a genuine gap.
Seventeen reviews of this project have produced a defect or overclaim in all but
two. We would rather you break it.

`ATTACK_PROMPT_3.md` §2 lists where WE think it is most likely wrong, ranked.
The top entry is adequacy — whether the Lean statements mean ALCI_RCC5 at all —
because that is the class we can least check ourselves, and the class your
predecessor found against the previous artifact.

**This time the Lean source is included.** Round 2 noted its absence prevented
you from rebuilding our claims; `lean/POFreeLift.lean` is the artifact,
`VERIFY.md` says how to build it and what to audit.

## Honest label

Machine-checked, **not certified**. Zero sorries and a `propext` /
`Quot.sound` / `Classical.choice` footprint is exactly the guarantee that does
not protect against a statement meaning the wrong thing.

Decidability of full ALCI_RCC5 is a separate, older open problem and is not
claimed here.
