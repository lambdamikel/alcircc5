#!/usr/bin/env python3
"""WP119 candidate -- extremal carrier or demand-carrying kernel.

This is a deliberately NARROW probe.  It tests whether wp116's unbounded
TARGET ROUNDS are a consequence of choosing the first/nearest witness rather
than a necessity of the formula.

For a vertical demand exists-r.D at x, inspect the r-successors carrying D.

  * If one is r-extremal (it has no further r-successor carrying D), select an
    extremal carrier directly.
  * If none is extremal, dependent choice gives an infinite r-chain all of
    whose nodes carry D.  Such a chain is the intended source of a kernel with
    Ds=[D], rather than KernelData's current Ds=[].

The fixed-family treatment keeps C0 = exists-PP.A constant while the model's
aperiodic prefix grows.  The first-witness closure takes linearly many rounds;
the extremal selector jumps to the last A-carrier.

CONTROLS, stated before the run:
  1. Every labelled vertical existential has a real carrier in the tower.
  2. Every "kernel" classification (no extremal carrier) has a recurrent tail
     carrier of D in the requested direction in the closed-form tower.
  3. Every selected external is genuinely extremal for D.
  4. The worklist never hits its cap.

LIMIT: this does NOT build or check a complete MultiTierOk certificate.  In
particular, it does not discharge obligations of the newly proposed kernels.
It isolates only the source of wp116's model-prefix-dependent rounds.
"""

from collections import deque
import random

from wp112_lap_continuation_closed_form import (
    PP, PPI, Tower, build, mdepth, po_free, rand_c)
from wp116_target_rounds import close_from, rounds_to_close, unserved
from wp117_kernel_phase_coverage import served_by_phase


def label(T, c0, n):
    budget = mdepth(c0) + 1
    return [f for f in T.mty(c0, n) if mdepth(f) <= budget]


def demands(T, c0, n):
    return sorted([(f[1], f[2]) for f in label(T, c0, n)
                   if f[0] == "ex" and f[1] in (PP, PPI)], key=str)


def carriers(T, x, r, D):
    return [y for y in T.succs(x, r) if T.sat(y, D)]


def extremal_carriers(T, x, r, D):
    return [y for y in carriers(T, x, r, D)
            if not any(T.sat(z, D) for z in T.succs(y, r))]


def has_recurrent_tail_carrier(T, x, r, D):
    """Closed-form control: a tail residue represents infinitely many laps and
    is its own r-successor at a different lap."""
    return any(R in T.succs(x, r) and T.sat(R, D)
               and R in T.succs(R, r) for R in T.tail)


def extremal_closure(T, c0, root, cap=10000):
    """Resolve each full-type vertical defect by an extremal external or by a
    demand-carrying kernel marker.  Returns metrics and control failures."""
    nodes = {root}
    queue = deque([(root, 0)])
    expanded = set()
    kernels = []
    max_depth = 0
    failures = {"no_carrier": 0, "bad_kernel": 0, "bad_extremal": 0}

    while queue and len(expanded) < cap:
        x, depth = queue.popleft()
        max_depth = max(max_depth, depth)
        if x in expanded:
            continue
        expanded.add(x)

        for r, D in demands(T, c0, x):
            # Re-use a selected real node whenever read-off already serves it.
            if any(y in T.succs(x, r) and T.sat(y, D) for y in nodes):
                continue

            cs = carriers(T, x, r, D)
            if not cs:
                failures["no_carrier"] += 1
                continue

            xs = extremal_carriers(T, x, r, D)
            if xs:
                y = next((z for z in xs if z in nodes),
                         sorted(xs, key=str)[0])
                if any(T.sat(z, D) for z in T.succs(y, r)):
                    failures["bad_extremal"] += 1
                if y not in nodes:
                    nodes.add(y)
                    queue.append((y, depth + 1))
            else:
                if not has_recurrent_tail_carrier(T, x, r, D):
                    failures["bad_kernel"] += 1
                kernels.append((x, r, D))

    return {
        "nodes": len(nodes),
        "kernels": len(kernels),
        "depth": max_depth,
        "cap_hit": bool(queue),
        "failures": failures,
    }


def fixed_family():
    """C0 is fixed; only the irrelevant model prefix length changes."""
    A = ("at", 0)
    c0 = ("ex", PP, A)
    rows = []
    for L in (4, 8, 12, 18, 26, 40):
        # P0 is the root.  P1..P(L-1) carry A; the periodic tail does not.
        # Thus the first-witness selector walks the prefix, while P(L-1) is an
        # immediately available PP-maximal A-carrier.
        pref = {(0, i): i > 0 for i in range(L)}
        tail = {(0, t): False for t in range(3)}
        T = Tower(L, 3, pref, tail, [], {})
        nearest, _r0, hit = rounds_to_close(T, c0, ("P", 0), maxround=100)
        ext = extremal_closure(T, c0, ("P", 0))
        rows.append((L, nearest, hit, ext))
    return rows



def wp117_residue_check():
    """Revisit exactly wp117's phase-uncovered residue.  The candidate says
    those demands should have an r-extremal carrier, and that carrier cannot
    carry the same existential defect again."""
    out = {
        "residue": 0, "has_extremal": 0, "new": 0, "in_set": 0,
        "same_trigger_at_target": 0, "no_extremal": 0,
    }
    for seed, L, p in ((20260826, 4, 3), (777, 8, 3),
                       (31337, 18, 3), (5150, 8, 6),
                       (8675309, 26, 2)):
        rng = random.Random(seed)
        for _ in range(1200):
            c0 = rand_c(rng, rng.randint(2, 4))
            if not po_free(c0):
                continue
            T = build(rng, L=L, p=p)
            root = next((n for n in T.nodes if T.sat(n, c0)), None)
            if root is None:
                continue
            nodes, cuts = close_from(T, c0, root)
            for v in cuts:
                for r, D in unserved(T, c0, nodes, v):
                    if served_by_phase(T, c0, v, r, D):
                        continue
                    out["residue"] += 1
                    xs = extremal_carriers(T, v, r, D)
                    if not xs:
                        out["no_extremal"] += 1
                        continue
                    out["has_extremal"] += 1
                    y = xs[0]
                    out["in_set" if y in nodes else "new"] += 1
                    if ("ex", r, D) in T.mty(c0, y):
                        out["same_trigger_at_target"] += 1
    return out

def random_sweep(seed, trials, L, p):
    rng = random.Random(seed)
    out = {
        "models": 0, "max_nodes": 0, "max_kernels": 0,
        "max_depth": 0, "cap_hits": 0,
        "no_carrier": 0, "bad_kernel": 0, "bad_extremal": 0,
    }
    for _ in range(trials):
        c0 = rand_c(rng, rng.randint(2, 4))
        if not po_free(c0):
            continue
        T = build(rng, L=L, p=p)
        root = next((n for n in T.nodes if T.sat(n, c0)), None)
        if root is None:
            continue
        out["models"] += 1
        r = extremal_closure(T, c0, root)
        out["max_nodes"] = max(out["max_nodes"], r["nodes"])
        out["max_kernels"] = max(out["max_kernels"], r["kernels"])
        out["max_depth"] = max(out["max_depth"], r["depth"])
        out["cap_hits"] += int(r["cap_hit"])
        for k, v in r["failures"].items():
            out[k] += v
    return out


def main():
    print("WP119 candidate -- extremal carrier or D-carrying kernel\n")
    print("  FIXED C0 FAMILY: C0 = exists-PP.A")
    print("    L    nearest rounds    extremal nodes    extremal depth    kernels")
    for L, nearest, hit, ext in fixed_family():
        suffix = " (ceiling hit)" if hit else ""
        print(f"   {L:2d}         {nearest:2d}{suffix:14s}"
              f" {ext['nodes']:8d} {ext['depth']:17d} {ext['kernels']:10d}")
    print()

    residue = wp117_residue_check()
    print("  WP117 PHASE-UNCOVERED RESIDUE:")
    print(f"    residual demands                         : {residue['residue']}")
    print(f"    with an r-extremal D-carrier             : {residue['has_extremal']}")
    print(f"    extremal carrier already in node set     : {residue['in_set']}")
    print(f"    extremal carrier is new                  : {residue['new']}")
    print(f"    target still carries the SAME defect     : {residue['same_trigger_at_target']}")
    print(f"    no extremal carrier                      : {residue['no_extremal']}")
    print()

    print("  RANDOM TOWER SWEEP (same shapes/seeds as wp116):")
    total_control_fail = 0
    for label_, seed, L, p in (
            ("L=4   p=3", 20260826, 4, 3),
            ("L=8   p=3", 777, 8, 3),
            ("L=12  p=3", 31337, 12, 3),
            ("L=18  p=3", 5150, 18, 3),
            ("L=26  p=3", 8675309, 26, 3),
            ("L=40  p=3", 112358, 40, 3)):
        r = random_sweep(seed, 1200, L, p)
        ctl = r["no_carrier"] + r["bad_kernel"] + r["bad_extremal"] + r["cap_hits"]
        total_control_fail += ctl
        print(f"    {label_:10s}: models {r['models']:4d}, max nodes"
              f" {r['max_nodes']:2d}, max depth {r['max_depth']:2d},"
              f" max kernels {r['max_kernels']:2d}, control failures {ctl}")

    print("\n" + "=" * 76)
    if total_control_fail:
        print("  CONTROL MISSED -- treatment numbers WITHHELD.")
        return 1
    print("  CONTROLS HELD.  This rejects only the inference")
    print("      'wp116's growing first-witness rounds imply every extraction grows'.")
    print("  It is not yet a MultiTierOk acceptance result; kernel obligations and")
    print("  mixed PP/PPI alternation still require a proof or a stronger probe.")
    print("=" * 76)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
