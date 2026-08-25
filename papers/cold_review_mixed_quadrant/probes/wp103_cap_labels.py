#!/usr/bin/env python3
"""WP103 -- can the CAP's labels be copied from the model, or must the model be
extended?

ASSEMBLY_DESIGN sec. 51.3.  The cap's STRUCTURE is certified (`odAmalg`,
`odTower`, `odAmalg_frame` -- ordered-disjoint, composition closure free).  What
is unproved is the LABELS.

Two routes:

  (a) EXTEND THE MODEL and read the cap's labels there.  Then every obligation
      is automatic (`top_all_ppi_automatic`), but the extension must be shown to
      exist.
  (b) COPY a label from an existing model node -- the demand's own witness `w`,
      which realizes exactly the required type (`witness_realizes_requirement`).
      Cheap, but the copied label carries `w`'s universals, and the cap sits
      above the WHOLE closure while `w` guarantees only what is below ITSELF.

Route (b) is worth measuring before route (a) is attempted, because (b) needs no
extension lemma at all.  sec. 50.4 already pinned the ONLY dangerous universal:
every edge out of the cap is PPI (into the closure) or PO (outside, and forall-PO
is absent).  So the whole question is:

    for Y with  forall-PPI.Y in mty(w),  does Y hold at EVERY node of the
    downward closure of the chain?

OUTCOME (2026-08-24), read this before the numbers.  Part A reports 100%, but
only **2 of 44** cap labels carried a forall-PPI AT ALL, so the rate rests on two
tests and is worth nothing on its own.  Asking what an adversarial instance would
need produced a PROOF instead, now certified as `cap_all_ppi_sound` /
`cap_all_ppi_sound_chain` (both axiom-free):

    the demand is present at EVERY chain node, so every c j has its own witness
    w j carrying forall-PPI.Y; a closure node u lies below SOME c j, hence below
    w j by transitivity, hence receives Y.

The witnesses' universals BLANKET the closure.  So the probe's role here was to
force the question, not to answer it -- and its headline number is exactly the
kind this project has learned to distrust (compare wp100, and wp102 Q1).

PARTS
  A  the rate at which a copied label is already sound
  B  does choosing `w` HIGHER help?  (sat_all_ppi_down makes forall-PPI content
     monotone DOWNWARD, so a higher witness should carry less of it)
  C  when it fails, is the failure on the CHAIN (where periodicity might rescue
     it) or off-chain?

Model class and exact-satisfaction machinery inherited from wp101.
"""

import random

from wp101_periodic_oneshot_vertical import (
    DR, PO, EQ, PP, PPI, Reg, rel, closure, rand_concept, build_model,
)


def chain_closure_sides(m, lo, hi_idx):
    """Side indices lying in the downward closure of the chain window."""
    return [j for j in range(len(m.sides))
            if any(rel(m.sides[j], m.a(i)) == PP for i in range(lo, hi_idx))]


def cap_label_sound(m, c0, hi, D, wj, lo, span):
    """Is side `wj`'s forall-PPI content satisfied everywhere in the closure?

    Returns (sound, n_bad_chain, n_bad_side).
    """
    ppis = [d[2] for d in closure(c0)
            if d[0] == "all" and d[1] == PPI and m.sat_side(wj, d, hi)]
    if not ppis:
        return True, 0, 0
    bad_chain = bad_side = 0
    for Y in ppis:
        for i in range(lo, lo + span):
            if not m.sat_chain(i, Y, hi):
                bad_chain += 1
        for j in chain_closure_sides(m, lo, lo + span):
            if not m.sat_side(j, Y, hi):
                bad_side += 1
    return (bad_chain + bad_side) == 0, bad_chain, bad_side


def demands_and_witnesses(m, c0, hi):
    """Cofinal one-shot exists-PP demands, with the available side witnesses,
    ordered by how high up the chain each witness reaches."""
    out = []
    WIN = 32 * m.p
    for d in closure(c0):
        if d[0] != "ex" or d[1] != PP:
            continue
        occ = [i for i in range(m._stab, m._stab + WIN)
               if m.sat_chain(i, d, hi)
               and not m.sat_chain(i, ("all", PP, d), hi)]
        if not occ or len([i for i in occ
                           if i > m._stab + 3 * WIN // 4]) < m.p:
            continue
        X = d[2]
        if len([k for k in range(m._stab, m._stab + 8 * m.p)
                if m.sat_chain(k, X, hi)]) >= 3:
            continue                                    # case 1, in-kernel
        ws = []
        for j in range(len(m.sides)):
            if not m.sat_side(j, X, hi):
                continue
            reach = [i for i in range(m._stab, m._stab + WIN)
                     if rel(m.a(i), m.sides[j]) == PP]
            if reach:
                ws.append((len(reach), j))
        if ws:
            out.append((X, sorted(ws)))
    return out


def part_a(trials=3000, seed=909909):
    print("PART A -- is a COPIED label already sound?")
    rng = random.Random(seed)
    hi = 60
    sound = unsound = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build_model(rng)
        for X, ws in demands_and_witnesses(m, c0, hi):
            _, wj = ws[-1]                              # the highest-reaching
            ok, _, _ = cap_label_sound(m, c0, hi, X, wj, m._stab, 4 * m.p)
            if ok:
                sound += 1
            else:
                unsound += 1
    tot = sound + unsound
    print(f"  cap labels examined (highest-reaching witness) : {tot}")
    if tot:
        print(f"    copied label SOUND as-is  : {sound:5d}  ({100*sound/tot:5.1f}%)")
        print(f"    copied label UNSOUND      : {unsound:5d}"
              f"  ({100*unsound/tot:5.1f}%)")
    print("  UNSOUND means the witness carries a forall-PPI whose consequent")
    print("  fails somewhere in the closure -- route (b) then needs route (a)'s")
    print("  model extension, or a better choice of witness (part B).")
    return tot > 0


def part_b(trials=3000, seed=111222):
    print("\nPART B -- does choosing a HIGHER witness help?")
    print("  sat_all_ppi_down (certified) makes forall-PPI content monotone")
    print("  DOWNWARD, so a higher witness should carry strictly less of it.")
    rng = random.Random(seed)
    hi = 60
    low_ok = high_ok = both = neither = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build_model(rng)
        for X, ws in demands_and_witnesses(m, c0, hi):
            if len(ws) < 2:
                continue
            lo_ok = cap_label_sound(m, c0, hi, X, ws[0][1], m._stab, 4 * m.p)[0]
            hi_ok = cap_label_sound(m, c0, hi, X, ws[-1][1], m._stab, 4 * m.p)[0]
            if lo_ok and hi_ok:
                both += 1
            elif hi_ok:
                high_ok += 1
            elif lo_ok:
                low_ok += 1
            else:
                neither += 1
    tot = both + high_ok + low_ok + neither
    print(f"  demands with >=2 candidate witnesses : {tot}")
    if tot:
        print(f"    both witnesses sound        : {both:5d}")
        print(f"    ONLY the higher is sound    : {high_ok:5d}   <- picking high helps")
        print(f"    ONLY the lower is sound     : {low_ok:5d}   <- picking high HURTS")
        print(f"    neither sound               : {neither:5d}")
    return tot > 0


def part_c(trials=3000, seed=333444):
    print("\nPART C -- when a copied label fails, WHERE does it fail?")
    print("  on the CHAIN (periodicity might rescue it) or OFF-CHAIN?")
    rng = random.Random(seed)
    hi = 60
    chain_only = side_only = mixed = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        m = build_model(rng)
        for X, ws in demands_and_witnesses(m, c0, hi):
            _, wj = ws[-1]
            ok, bc, bs = cap_label_sound(m, c0, hi, X, wj, m._stab, 4 * m.p)
            if ok:
                continue
            if bc and not bs:
                chain_only += 1
            elif bs and not bc:
                side_only += 1
            else:
                mixed += 1
    tot = chain_only + side_only + mixed
    print(f"  unsound labels : {tot}")
    if tot:
        print(f"    fails only ON the chain   : {chain_only:5d}"
              f"  ({100*chain_only/tot:5.1f}%)")
        print(f"    fails only OFF the chain  : {side_only:5d}"
              f"  ({100*side_only/tot:5.1f}%)")
        print(f"    both                      : {mixed:5d}")
    return True


def main():
    print("=" * 74)
    print("WP103 -- cap labels: copy from the model, or extend it?")
    print("=" * 74)
    for k, f in (("A copied-label soundness", part_a),
                 ("B higher witness", part_b),
                 ("C failure location", part_c)):
        f()
    print("\n" + "=" * 74)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
