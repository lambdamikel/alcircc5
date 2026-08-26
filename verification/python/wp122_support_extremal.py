#!/usr/bin/env python3
"""WP122 -- SUPPORT LABELS + EXTREMAL SELECTION, under the FULL obligation set.

ASSEMBLY_DESIGN sec.136.  The cold response (sec.135) supplied two assets:

  support labels    -- MultiTierOk never requires tauE = mty, only the Hintikka
                       closure conditions, and wp120 showed the growth wp116
                       measured is full-type OVERLABELLING, not C0;
  extremal carriers -- choosing a D-MAXIMAL witness makes the demand DISAPPEAR
                       at the target (extremal_drops, certified axiom-free), so
                       the ascending spectrum strictly decreases.

Neither has been tested TOGETHER, and neither has been tested under the full
MultiTierOk field list on a kernel-bearing class.  Per sec.134.1 -- adopted after
two coverage probes produced two false positives -- this probe uses the full
checker, not a coverage measurement.

THE RISK, named before running.  Support labels make `ee_all` non-trivial.  With
read-off relations, `E(n,m) = r` fires on MANY pairs, and a universal at n must
land in m's label -- but m's label was seeded from ITS OWN parent, which may
never have carried that universal.  Complete types get this free because they
contain everything true; support labels do not.

CONTROLS, stated before the run:
  (1) with FULL-TYPE labels the node count must GROW with the tower prefix,
      reproducing wp116.  If it does not, the harness is not exercising the
      phenomenon.
  (2) with ARBITRARY (non-extremal) selection the ascending spectrum must fail
      to descend.  If extremal and arbitrary behave identically, extremality is
      doing no work here.
"""

import random

from wp112_lap_continuation_closed_form import (
    DR, EQ, PP, PPI, build, closure, mdepth, po_free, rand_c)

CONV = {DR: DR, "PO": "PO", EQ: EQ, PP: PPI, PPI: PP}


def sub(c):
    return closure(c)


def support(T, n, seeds):
    """Hintikka closure of `seeds` at n: decompose conjunctions, CHOOSE a true
    disjunct, keep universals and existentials as obligations.  Never adds a
    formula merely because it is true at n -- that is the overlabelling."""
    lab, work = set(), list(seeds)
    while work:
        c = work.pop()
        if c in lab:
            continue
        if not T.sat(n, c):
            continue                      # seeds must be true; guard anyway
        lab.add(c)
        if c[0] == "and":
            work += [c[1], c[2]]
        elif c[0] == "or":
            work.append(c[1] if T.sat(n, c[1]) else c[2])
        elif c[0] == "all" and c[1] == EQ:
            work.append(c[2])         # EQ is identity: forall-EQ.E forces E HERE
                                      # (MultiTierOk's kk_eq / the ee_all EQ case)
    return frozenset(lab)


def carriers(T, x, r, D):
    return [y for y in T.succs(x, r) if y != x and T.sat(y, D)]


def pick(T, x, r, D, extremal):
    """A witness.  Extremal = maximal in the carrier set, so the demand dies
    there (extremal_drops)."""
    cs = carriers(T, x, r, D)
    if not cs:
        return None
    if not extremal:
        return cs[0]
    for y in cs:
        if not any(z != y and z in T.succs(y, r) and T.sat(z, D) for z in cs):
            return y
    return cs[0]                           # no maximal member: chain case


def build_cert(T, c0, root, full_types=False, extremal=True, cap=250):
    """Node set + labels.  Nodes are (element, label) pairs: two occurrences of
    one element with different support are DISTINCT certificate nodes."""
    b = mdepth(c0) + 1
    if full_types:
        lab0 = frozenset(d for d in T.mty(c0, root) if mdepth(d) <= b)
    else:
        lab0 = support(T, root, [c0])
    nodes = {(root, lab0)}
    work = [(root, lab0)]
    steps = 0
    while work and steps < cap:
        steps += 1
        x, lab = work.pop()
        for d in sorted(lab):
            if d[0] != "ex" or d[1] not in (PP, PPI):
                continue
            r, D = d[1], d[2]
            y = pick(T, x, r, D, extremal)
            if y is None:
                continue
            if full_types:
                ylab = frozenset(e for e in T.mty(c0, y) if mdepth(e) <= b)
            else:
                seeds = [D] + [e[2] for e in lab
                               if e[0] == "all" and e[1] == r]
                ylab = support(T, y, seeds)
            if (y, ylab) not in nodes:
                nodes.add((y, ylab))
                work.append((y, ylab))
    if full_types:
        return nodes, (steps >= cap)
    # SUPPORT CLOSURE FIXPOINT, INTERLEAVED WITH WITNESS GENERATION.
    # The closure adds universal BODIES to labels, and a body can itself be an
    # EXISTENTIAL -- a demand that arrives after the worklist has drained and so
    # never gets a witness.  The two must be run to a JOINT fixpoint; whether
    # that terminates is the cold note's stated open item.
    # (The uninterleaved version is kept below for the control.)
    # SUPPORT CLOSURE FIXPOINT.  A universal at x must land in the label of every
    # r-related node -- and a support label seeded from ITS OWN parent need not
    # carry it.  Close under that, re-running the Hintikka closure each time, and
    # report whether it terminates.
    lab = {}
    for (x, lx) in nodes:
        lab[x] = lab.get(x, frozenset()) | lx
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
                        continue          # unsatisfiable demand: model is wrong
                    lab[y] = support(T, y, list(lab[y]) + [d[2]])
                    grew = True
        if not grew:
            break
    else:
        return {(x, lab[x]) for x in lab}, True     # fixpoint did not settle
        # witness regeneration for demands the closure introduced
    for _ in range(40):
        added = False
        for x in list(lab):
            for d in list(lab[x]):
                if d[0] != "ex" or d[1] not in (PP, PPI):
                    continue
                r, D = d[1], d[2]
                if any(erel(T, x, y) == r and D in lab[y] for y in lab):
                    continue
                y = pick(T, x, r, D, extremal)
                if y is None:
                    continue
                seeds = [D] + [e[2] for e in lab[x]
                               if e[0] == "all" and e[1] == r]
                ny = support(T, y, list(lab.get(y, frozenset())) + seeds)
                if y not in lab or ny != lab[y]:
                    lab[y] = ny
                    added = True
        if not added:
            break
        for _ in range(60):                       # re-close support
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
            return {(x, lab[x]) for x in lab}, True
    else:
        return {(x, lab[x]) for x in lab}, True   # joint fixpoint did not settle
    return {(x, lab[x]) for x in lab}, (steps >= cap)


def erel(T, x, y):
    if x == y:
        return EQ
    for r in (PP, PPI, DR):
        if y in T.succs(x, r):
            return r
    return "PO"


EXDIAG = []


def check(T, c0, nodes):
    """Every MultiTierOk field this externals-only model can express."""
    bad = {}
    def note(k): bad[k] = bad.get(k, 0) + 1
    ns = sorted(nodes, key=str)
    for (x, lx) in ns:
        for d in lx:
            if d[0] == "and" and not (d[1] in lx and d[2] in lx):
                note("e_and")
            if d[0] == "or" and not (d[1] in lx or d[2] in lx):
                note("e_or")
            if d[0] == "atom" and ("nat", d[1]) in lx:
                note("e_clash")
            if d[0] == "all":
                for (y, ly) in ns:
                    if erel(T, x, y) == d[1] and d[2] not in ly:
                        note("ee_all_" + d[1])
            if d[0] == "ex" and d[1] in (PP, PPI):
                if x[0] == "R":
                    continue      # a tail residue is a KERNEL PHASE, not an
                                  # external: its demands are MultiTierOk's
                                  # k_ex (served from within the kernel, or by
                                  # K k f), which this externals-only checker
                                  # does not model.  wp118 models it properly.
                if not any(erel(T, x, y) == d[1] and d[2] in ly
                           for (y, ly) in ns):
                    note("e_ex_" + d[1])
                    if len(EXDIAG) < 12:
                        inset = [(y, d[2] in ly) for (y, ly) in ns
                                 if erel(T, x, y) == d[1]]
                        model_w = [y for y in T.succs(x, d[1])
                                   if y != x and T.sat(y, d[2])]
                        EXDIAG.append({
                            "kind": x[0],
                            "r": d[1],
                            "carriers_in_model": len(model_w),
                            "carrier_kinds": sorted({w[0] for w in model_w}),
                            "r_related_in_cert": len(inset),
                            "any_r_related_has_D": any(v for _, v in inset),
                            "demand_in_support_only": True,
                        })
    return bad


def sweep(seed, trials, L, p, full_types, extremal):
    rng = random.Random(seed)
    models = maxn = capped = 0
    fails = {}
    for _ in range(trials):
        c0 = rand_c(rng, rng.randint(2, 4))
        if not po_free(c0):
            continue
        T = build(rng, L=L, p=p)
        root = next((n for n in T.nodes if T.sat(n, c0)), None)
        if root is None:
            continue
        models += 1
        nodes, hit = build_cert(T, c0, root, full_types, extremal)
        capped += 1 if hit else 0
        maxn = max(maxn, len(nodes))
        for k, v in check(T, c0, nodes).items():
            fails[k] = fails.get(k, 0) + v
    return models, maxn, capped, fails


def line(tag, res):
    models, maxn, capped, fails = res
    f = ", ".join(f"{k}:{v}" for k, v in sorted(fails.items())) or "none"
    print(f"    {tag:26s} models {models:5d}  max nodes {maxn:4d}  "
          f"capped {capped:4d}  failures: {f}")
    return maxn, capped, fails


def main():
    shapes = ((4, 3), (8, 3), (18, 3), (40, 3))
    print("WP122 -- support labels + extremal selection, full obligation set\n")
    for tag, ft, ex in (("CONTROL full-type", True, True),
                        ("CONTROL non-extremal", False, False),
                        ("support + extremal", False, True)):
        print(f"  --- {tag} ---")
        for (L, p) in shapes:
            line(f"L={L:<3d} p={p}", sweep(20260826 + L, 500, L, p, ft, ex))
        print()
    if EXDIAG:
        print("  e_ex failure diagnosis:")
        agg = {}
        for e in EXDIAG:
            k = (e["kind"], e["r"], e["carriers_in_model"] > 0,
                 tuple(e["carrier_kinds"]), e["r_related_in_cert"],
                 e["any_r_related_has_D"])
            agg[k] = agg.get(k, 0) + 1
        for k, n in sorted(agg.items(), key=lambda kv: -kv[1]):
            print(f"    {n:3d}  node kind {k[0]}, demand {k[1]}, "
                  f"model carriers exist {k[2]} (kinds {list(k[3])}), "
                  f"r-related cert nodes {k[4]}, one carries D {k[5]}")
        print()
    print("=" * 76)
    print("  CONTROL 1 (full-type) must show node counts GROWING with L,")
    print("  reproducing wp116; otherwise the harness misses the phenomenon.")
    print("  CONTROL 2 (non-extremal) shows what extremality is worth.")
    print("  'capped' now also counts runs where the SUPPORT CLOSURE FIXPOINT")
    print("  failed to settle in 60 sweeps -- that would be the open item biting.")
    print("=" * 76)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
