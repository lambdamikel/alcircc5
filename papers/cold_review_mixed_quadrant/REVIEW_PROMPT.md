# Cold review request — the ALCI_RCC5 ∀PO-free fragment, mixed quadrant

You are asked to review a Lean 4 development. It is unreviewed: **§§43–60 of
this campaign have never been looked at by anyone other than their author.**

The project's ledger stands at **a defect or overclaim found in 15 of 17
reviews**. Please assume this one contains one too, and find it.

## Two ways to run this

**(a) COLD FIRST PASS (preferred).** Read only `lean/POFreeLift.lean` (or the
`lean/sections_49_60_excerpt.lean` extract) and `CLAIMS.md`. Attack the
statements directly, without the author's narrative. Then read
`ASSEMBLY_DESIGN_43_60.md` and say whether it claims more than the Lean supports.

**(b) FULL PASS.** Read everything, including the design record.

Either way, the questions below are the ones worth your time.

## What is claimed

See `CLAIMS.md` for the precise table. In one sentence: *the ∀PO-free fragment's
decision pipeline is machine-checked end to end, with completeness reduced to one
named premise* (`MixedCompleteness`). Three of the fragment's four quadrants have
general decidability theorems; the fourth (mixed) is the open one.

The build is clean: 27,030 lines, 0 errors, 0 warnings, 0 sorries, no `sorryAx`.
Axioms are `propext` / `Quot.sound` / `Classical.choice`; `decidableSat_pofree`
itself uses only the first two.

## Targets, in descending order of value

**T1 — Is `MixedCompleteness` the right premise, and is it honest?**
`decidableSat_pofree` claims decidability modulo it. Check: (i) is
`mtAcceptB_sound` really unconditional; (ii) is the premise inhabitable by a
classical oracle rather than by a genuine certificate (this exact failure was
found in this project's round 26 — see `mixedCompleteness_of_code`); (iii) is
`codesM C0 (mixKT C0)³` actually a *fixed* enumeration computed from `C₀`, or
does something in it depend on the model?

**T2 — The §49 trichotomy.** `above_cofinal_is_above_all`,
`finite_pool_gives_cofinal_witness`, `finite_pool_all_or_nothing`. The claim is
that "above cofinally many *is* above all" and that a finite witness pool always
contains one member serving a whole kernel. Are the statements what the prose
says? Any hidden hypothesis doing the work?

**T3 — The cap construction (§§50–53).** `odAmalg`, `odSeedCap`, and especially
the transfer theorem **`odSeedCap_old`** ("adding a cap changes nothing below
it"). If that is wrong, everything downstream is. Also: is `capSeed`'s choice —
the cap disjoint from nothing — actually forced, as §51.1 argues, or convenient?

**T4 — The cap's obligations (§§56–57).** `cap_ee_all_pp`, `cap_stab_exists`,
`cap_ee_all_ppi`, `cap_reaches`, `cap_stab_up`. §57 claims *both* `∀` directions
are discharged. Is any `MultiTierOk` row missed? §58 found two gaps in `e_ex` by
writing the consumer — **are there more than two?**

**T5 — The probes.** `wp96`–`wp103` under `probes/`. The author caught FOUR of
his own measurement artifacts in one session (see §49.4 and §51.4 in the design
record). Assume there are more. In particular check whether `wp101`'s in-kernel
rate (~90%, the one number claimed stable across model classes) is an artifact of
the finite/cofinite representation.

**T6 — Anything the design record claims that the Lean does not.** The record has
been corrected mid-flight several times (§46.27→§46.28, §47.5, §55, §58). Check
whether any withdrawn claim is still asserted somewhere.

## What would be most useful

A counterexample, a false lemma, or a demonstration that a stated theorem does
not mean what its docstring says. Failing that: the strongest statement you are
willing to make about what IS established, and where you would attack next.

Machine-checkable witnesses are preferred over prose. Self-contained Python is
the project convention (re-derive the RCC5 composition table from finite set
semantics rather than assuming it).

## Building

Lean 4 core only, no mathlib. `cd lean && lean POFreeLift.lean` (elan-installed
Lean 4.32.0; takes about 20s).
