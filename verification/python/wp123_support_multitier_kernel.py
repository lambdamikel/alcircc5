#!/usr/bin/env python3
"""WP123 -- support labels under the FULL MultiTierOk field list, WITH kernels.

ASSEMBLY_DESIGN sec.137.4 step 1.  wp122 showed support labels + extremal
selection + the joint fixpoint close every obligation an EXTERNALS-ONLY checker
can express, with node count constant across a tenfold prefix increase.  Its
stated gap: kernel-phase demands were excluded, because a tail residue is a
KERNEL PHASE whose obligations are `k_ex` / `ke_all` / `kk_*`, not `e_ex`.

wp118 models the kernel properly.  This probe is wp118's checker fed wp122's
construction.

  externals beta  = the closure's PREFIX and SIDE nodes, with SUPPORT labels
  kernel kappa    = the TAIL, phases = residues, with SUPPORT labels
  E, K            = read off
  labels          = support closure + witness generation, run to a JOINT fixpoint

CONTROL, stated before the run: with FULL-TYPE labels the same checker must show
failures and growing externals -- otherwise the harness is not exercising the
difference support labels make.
"""

import random

from wp112_lap_continuation_closed_form import (
    DR, EQ, PP, PPI, build, mdepth, po_free, rand_c)
from wp118_multitier_acceptance import CONV, CT, erel, krel
from wp122_support_extremal import build_cert, support


def check(T, c0, lab, ext, phases):
    """wp118's field list, over support labels."""
    bad = {}
    def note(k): bad[k] = bad.get(k, 0) + 1
    p = len(phases)
    if p == 0:
        note("hp"); return bad
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
            if d[0] == "atom" and ("nat", d[1]) in lab[e]:
                note("e_clash")
    for a in range(p):
        for d in phases[a]:
            if d[0] == "and" and not (d[1] in phases[a] and d[2] in phases[a]):
                note("k_and")
            if d[0] == "or" and not (d[1] in phases[a] or d[2] in phases[a]):
                note("k_or")
    for e in ext:                                              # ee_all
        for d in lab[e]:
            if d[0] != "all":
                continue
            for f in ext:
                if erel(T, e, f) == d[1] and d[2] not in lab[f]:
                    note("ee_all")
    for e in ext:                                              # ek_all
        for d in lab[e]:
            if d[0] == "all" and CONV[K[e]] == d[1]:
                for a in range(p):
                    if d[2] not in phases[a]:
                        note("ek_all")
    for a in range(p):                                         # ke_all
        for d in phases[a]:
            if d[0] != "all":
                continue
            for f in ext:
                if K[f] == d[1] and d[2] not in lab[f]:
                    note("ke_all")
    for a in range(p):                                         # kk_*
        for d in phases[a]:
            if d[0] != "all":
                continue
            if d[1] in (PP, PPI):
                for b in range(p):
                    if d[2] not in phases[b]:
                        note("kk_" + d[1])
            if d[1] == EQ and d[2] not in phases[a]:
                note("kk_eq")
    for e in ext:                                              # e_ex
        for d in lab[e]:
            if d[0] != "ex" or d[1] not in (PP, PPI):
                continue
            if not (any(erel(T, e, f) == d[1] and d[2] in lab[f] for f in ext)
                    or (CONV[K[e]] == d[1]
                        and any(d[2] in phases[a] for a in range(p)))):
                note("e_ex_" + d[1])
    for a in range(p):                                         # k_ex
        for d in phases[a]:
            if d[0] != "ex" or d[1] not in (PP, PPI):
                continue
            if not (any(K[f] == d[1] and d[2] in lab[f] for f in ext)
                    or (d[1] == PP and any(d[2] in phases[b] for b in range(p)))
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
        nodes, hit = build_cert(T, c0, root, full_types, True)
        capped += 1 if hit else 0
        lab = {}
        for (x, lx) in nodes:
            lab[x] = lab.get(x, frozenset()) | lx
        # EVERY kernel phase is part of the certificate and owes a label.
        # build_cert only labels residues that happened to be witnesses, so an
        # unvisited phase came out EMPTY and ek_all failed on it.  Seed them all,
        # then re-close support -- the universals do the rest.
        for R in T.tail:
            lab.setdefault(R, frozenset())
        for _ in range(60):
            grew = False
            for x in list(lab):
                for d in list(lab[x]):
                    if d[0] != "all":
                        continue
                    for y in list(lab):
                        if erel(T, x, y) != d[1] or d[2] in lab[y]:
                            continue
                        if not T.sat(y, d[2]):
                            continue
                        lab[y] = support(T, y, list(lab[y]) + [d[2]])
                        grew = True
            if not grew:
                break
        else:
            capped += 1
        ext = sorted([x for x in lab if x[0] != "R"], key=str)
        phases = [lab.get(R, frozenset()) for R in T.tail]
        maxe = max(maxe, len(ext))
        for k, v in check(T, c0, lab, ext, phases).items():
            fails[k] = fails.get(k, 0) + v
    return models, maxe, capped, fails


def main():
    print("WP123 -- support labels, full MultiTierOk field list, WITH kernels\n")
    for tag, ft in (("CONTROL: full-type labels", True),
                    ("support + extremal + joint fixpoint", False)):
        print(f"  --- {tag} ---")
        for L, p in ((4, 3), (8, 3), (18, 3), (40, 3)):
            m, me, cp, f = sweep(20260826 + L, 400, L, p, ft)
            fs = ", ".join(f"{k}:{v}" for k, v in sorted(f.items())) or "none"
            print(f"    L={L:<3d} p={p}  models {m:4d}  max externals {me:3d}  "
                  f"capped {cp:3d}  failures: {fs}")
        print()
    print("=" * 76)
    print("  The CONTROL must fail and grow; otherwise the harness is not")
    print("  exercising what support labels change.")
    print("=" * 76)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
