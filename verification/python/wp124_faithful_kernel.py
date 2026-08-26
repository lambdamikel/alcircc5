#!/usr/bin/env python3
"""WP124 -- a FAITHFUL kernel instrument (ASSEMBLY_DESIGN sec.138.4).

wp123 could not measure the kernel's internal PPI obligations: it routed
phase-to-phase relations through `erel`, a FUNCTION, while the tail is a
quotient where a residue is both above and below every residue.  Section 117's
failure, third occurrence.

The fix is not to patch `erel`.  `MultiTier` never asks for a phase-to-phase
ATOM: it states the obligations directly, and they are exactly what a
non-functional relation needs --

    kk_pp   forall-PP.c  in phase a  =>  c in phase b for EVERY b
    kk_ppi  forall-PPI.c in phase a  =>  c in phase b for EVERY b
    kk_eq   forall-EQ.c  in phase a  =>  c in phase a
    ek_all  forall-r.c at external e, conv(K e) = r  =>  c in EVERY phase
    ke_all  forall-r.c in a phase, K f = r           =>  c in tauE f
    k_ex    exists-r.D in phase a  =>  an external f with K f = r carrying D,
                                       or r = cdir(up) and some phase carries D,
                                       or r = eq and phase a carries D

So phases are propagated to as a BLOCK, never by a computed relation.  That is
the faithful model, and it is what this probe implements.

CONTROL, stated before the run: with FULL-TYPE labels the checker must show
failures growing with the tower prefix.  If it does not, the harness is not
exercising what support labels change.
"""

import random

from wp112_lap_continuation_closed_form import (
    DR, EQ, PP, PPI, build, mdepth, po_free, rand_c)
from wp118_multitier_acceptance import CONV, CT, erel, krel
from wp122_support_extremal import build_cert, carriers, pick, support


def close_labels(T, c0, lab, phases, full_types, rounds=60):
    """Run the propagation rules to a fixpoint.  Phases are a BLOCK."""
    def add_ext(y, cs):
        cs = [c for c in cs if T.sat(y, c)]
        if not cs:
            return False
        new = support(T, y, list(lab.get(y, frozenset())) + cs) if not full_types \
            else lab.get(y, frozenset())
        if new != lab.get(y, frozenset()):
            lab[y] = new
            return True
        return False

    def add_phase(a, cs, R):
        cs = [c for c in cs if T.sat(R, c)]
        if not cs:
            return False
        new = support(T, R, list(phases[a]) + cs) if not full_types else phases[a]
        if new != phases[a]:
            phases[a] = new
            return True
        return False

    for _ in range(rounds):
        grew = False
        # ee_all, externals to externals
        for x in list(lab):
            for d in list(lab[x]):
                if d[0] != "all":
                    continue
                for y in list(lab):
                    if erel(T, x, y) == d[1]:
                        grew |= add_ext(y, [d[2]])
        # ek_all, external to EVERY phase
        for x in list(lab):
            K = krel(T, x)
            for d in list(lab[x]):
                if d[0] == "all" and CONV[K] == d[1]:
                    for a, R in enumerate(T.tail):
                        grew |= add_phase(a, [d[2]], R)
        # kk_pp / kk_ppi, phase block; kk_eq, in place
        for a, R in enumerate(T.tail):
            for d in list(phases[a]):
                if d[0] != "all":
                    continue
                if d[1] in (PP, PPI):
                    for b, Rb in enumerate(T.tail):
                        grew |= add_phase(b, [d[2]], Rb)
                elif d[1] == EQ:
                    grew |= add_phase(a, [d[2]], R)
        # ke_all, phase to externals
        for a in range(len(T.tail)):
            for d in list(phases[a]):
                if d[0] != "all":
                    continue
                for f in list(lab):
                    if krel(T, f) == d[1]:
                        grew |= add_ext(f, [d[2]])
        if not grew:
            return False
    return True


def serve(T, c0, lab, phases, extremal, rounds=40):
    """Witness generation for demands the closure introduced."""
    for _ in range(rounds):
        added = False
        for x in list(lab):
            for d in list(lab[x]):
                if d[0] != "ex" or d[1] not in (PP, PPI):
                    continue
                r, D = d[1], d[2]
                if any(erel(T, x, y) == r and D in lab[y] for y in lab):
                    continue
                if CONV[krel(T, x)] == r and any(D in ph for ph in phases):
                    continue
                y = pick(T, x, r, D, extremal)
                if y is None:
                    continue
                if y[0] == "R":
                    # The carrier is a KERNEL PHASE.  e_ex's second branch wants
                    # some phase to carry D, so extend that phase's label rather
                    # than trying to make a residue into an external.
                    a = T.tail.index(y)
                    new = support(T, y, list(phases[a]) + [D])
                    if new != phases[a]:
                        phases[a] = new
                        added = True
                    continue
                seeds = [D] + [e[2] for e in lab[x] if e[0] == "all" and e[1] == r]
                new = support(T, y, list(lab.get(y, frozenset())) + seeds)
                if new != lab.get(y, frozenset()):
                    lab[y] = new
                    added = True
        # A KERNEL GENERATES EXTERNAL WITNESSES TOO.  k_ex's first branch is an
        # external f with K k f = r: for an ascending kernel a descending demand
        # can ONLY be served that way, and the construction never produced one.
        for a, R in enumerate(T.tail):
            for d in list(phases[a]):
                if d[0] != "ex" or d[1] not in (PP, PPI):
                    continue
                r, D = d[1], d[2]
                if any(krel(T, f) == r and D in lab[f] for f in lab):
                    continue
                if r == PP and any(D in ph for ph in phases):
                    continue
                if r == PP:
                    # cdir(up) branch: some phase must carry D.  Put it in a
                    # residue that satisfies it.
                    hit = False
                    for b, Rb in enumerate(T.tail):
                        if T.sat(Rb, D):
                            new = support(T, Rb, list(phases[b]) + [D])
                            if new != phases[b]:
                                phases[b] = new
                                added = hit = True
                            else:
                                hit = True
                            break
                    if hit:
                        continue
                cand = [y for y in T.succs(R, r)
                        if y[0] != "R" and T.sat(y, D)]
                if not cand:
                    continue
                y = cand[0]
                seeds = [D] + [e[2] for e in phases[a]
                               if e[0] == "all" and e[1] == r]
                new = support(T, y, list(lab.get(y, frozenset())) + seeds)
                if new != lab.get(y, frozenset()):
                    lab[y] = new
                    added = True
        if not added:
            return False
        if close_labels(T, c0, lab, phases, False):
            return True
    return True


def check(T, lab, phases):
    bad = {}
    def note(k): bad[k] = bad.get(k, 0) + 1
    ext = sorted(lab, key=str)
    p = len(phases)
    K = {e: krel(T, e) for e in ext}

    def rel_q(x, y):
        if x == "K" and y == "K": return EQ
        if x == "K": return K[y]
        if y == "K": return CONV[K[x]]
        return erel(T, x, y)
    univ = list(ext) + ["K"]
    for x in univ:
        for y in univ:
            if CONV[rel_q(x, y)] != rel_q(y, x):
                note("frame_q_conv")
            for z in univ:
                if rel_q(x, z) not in CT[(rel_q(x, y), rel_q(y, z))]:
                    note("frame_q_comp")
    for e in ext:
        for d in lab[e]:
            if d[0] == "and" and not (d[1] in lab[e] and d[2] in lab[e]):
                note("e_and")
            if d[0] == "or" and not (d[1] in lab[e] or d[2] in lab[e]):
                note("e_or")
            if d[0] == "all":
                for f in ext:
                    if erel(T, e, f) == d[1] and d[2] not in lab[f]:
                        note("ee_all")
                if CONV[K[e]] == d[1]:
                    for a in range(p):
                        if d[2] not in phases[a]:
                            note("ek_all")
            if d[0] == "ex" and d[1] in (PP, PPI):
                if not (any(erel(T, e, f) == d[1] and d[2] in lab[f] for f in ext)
                        or (CONV[K[e]] == d[1]
                            and any(d[2] in phases[a] for a in range(p)))):
                    note("e_ex_" + d[1])
    for a in range(p):
        for d in phases[a]:
            if d[0] == "and" and not (d[1] in phases[a] and d[2] in phases[a]):
                note("k_and")
            if d[0] == "or" and not (d[1] in phases[a] or d[2] in phases[a]):
                note("k_or")
            if d[0] == "all":
                if d[1] in (PP, PPI):
                    for b in range(p):
                        if d[2] not in phases[b]:
                            note("kk_" + d[1])
                if d[1] == EQ and d[2] not in phases[a]:
                    note("kk_eq")
                for f in ext:
                    if K[f] == d[1] and d[2] not in lab[f]:
                        note("ke_all")
            if d[0] == "ex" and d[1] in (PP, PPI):
                if not (any(K[f] == d[1] and d[2] in lab[f] for f in ext)
                        or (d[1] == PP and any(d[2] in ph for ph in phases))
                        or (d[1] == EQ and d[2] in phases[a])):
                    note("k_ex_" + d[1])
    return bad


def sweep(seed, trials, L, p, full_types):
    rng = random.Random(seed)
    models = maxe = capped = 0
    fails = {}
    for _ in range(trials):
        c0 = rand_c(rng, rng.randint(2, 4))
        if not po_free(c0):
            continue
        T = build(rng, L=L, p=p)
        root = next((n for n in T.nodes if T.sat(n, c0)), None)
        if root is None or root[0] == "R":
            continue
        models += 1
        b = mdepth(c0) + 1
        if full_types:
            nodes, _ = build_cert(T, c0, root, True, True)
            lab = {x: lx for (x, lx) in nodes if x[0] != "R"}
            phases = [frozenset(d for d in T.mty(c0, R) if mdepth(d) <= b)
                      for R in T.tail]
        else:
            lab = {root: support(T, root, [c0])}
            phases = [frozenset() for _ in T.tail]
            c1 = close_labels(T, c0, lab, phases, False)
            c2 = serve(T, c0, lab, phases, True)
            capped += 1 if (c1 or c2) else 0
        maxe = max(maxe, len(lab))
        for k, v in check(T, lab, phases).items():
            fails[k] = fails.get(k, 0) + v
    return models, maxe, capped, fails


def main():
    print("WP124 -- faithful kernel: phases propagated as a BLOCK\n")
    for tag, ft in (("CONTROL: full-type labels", True),
                    ("support + extremal + joint fixpoint", False)):
        print(f"  --- {tag} ---")
        for L, p in ((4, 3), (8, 3), (18, 3), (40, 3)):
            m, me, cp, f = sweep(20260826 + L, 300, L, p, ft)
            fs = ", ".join(f"{k}:{v}" for k, v in sorted(f.items())) or "none"
            print(f"    L={L:<3d} p={p}  models {m:4d}  max externals {me:3d}  "
                  f"capped {cp:3d}  failures: {fs}")
        print()
    print("=" * 76)
    print("  Phase-to-phase is never a computed relation here: kk_pp / kk_ppi")
    print("  propagate to the phase BLOCK, which is what MultiTier states and")
    print("  what a non-functional quotient relation requires.")
    print("=" * 76)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
