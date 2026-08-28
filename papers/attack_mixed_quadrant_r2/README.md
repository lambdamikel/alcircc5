# Attack packet, round 2 — the mixed quadrant (2026-08-28)

A follow-up, not a re-ask. Round 1 solved Target B, refuted Target A's proposed
lead, and found two real defects in our probes. All of that was reproduced
independently and acted on; the extraction is now blocked on **one question**.

## Read in this order

1. **`RESPONSE_TO_ROUND1.md`** — what we did with your findings, including the
   one claim we could not reproduce and a probe defect we found in our own work
   afterwards.
2. **`ATTACK_PROMPT_2.md`** — §0 what changed, §1 **Target D** (the question),
   §2 **Target E** (Target C revisited, now with the down-spectrum refinement
   certified), §3 routes already refuted — four of them added since round 1.
3. **`STATUS.md`** — what is machine-certified now, obligation by obligation, so
   you do not re-derive it.
4. **`./run_probes.sh`** — pure Python 3, no dependencies.

## The question, in one paragraph

The gate keys on `(mty v, {mty x : x PP v})` — your proposal, now built. A blocked
node borrows its gate-mate's witness `z` and the certificate declares `v < z`. We
have certified: the bad case forces `a < v` (dichotomy); an *agreeing* witness
exists exactly there; hence per-edge a witness with `ρ(z,v) ≠ PP` always exists;
and when the witness agrees, the declared order embeds in the model's `PP` so
irreflexivity is free. **Unproved:** in the non-agreeing case `z` is merely
incomparable to `v`, so (D1) is the transitive closure of all declared edges still
irreflexive, and (D2) if `ρ(v,z) = DR` the declared `v < z` violates the frame's
`lt x y → ¬ disj x y` — does a witness always exist that is neither below `v` nor
`DR` from `v`?

D2 has history in this project: an earlier round hit exactly that clause and
repaired it by strengthening the selection to "neither an ancestor nor disjoint".
Whether such a witness always exists is what we do not know.

## Honest scope

The Lean development is ~42,700 lines, 0 sorries, 0 warnings, axioms
`propext`/`Quot.sound`/`Classical.choice`, and **unreviewed** — this project's
ledger runs seventeen reviews with a defect or overclaim in all but two, so assume
something here is wrong and say so if you find it.

Probe numbers are finite randomized sweeps over finite set models; kernels are not
exercised by them. `wp131` part G's "132 instances used the fallback, none cycled"
is evidence for D1 and says nothing at all about D2.

Decidability of the full logic ALCI_RCC5 is a separate, older open problem and is
not what this packet is about.
