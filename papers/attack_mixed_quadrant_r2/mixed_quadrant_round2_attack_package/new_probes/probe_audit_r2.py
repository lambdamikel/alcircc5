#!/usr/bin/env python3
"""Independent diagnostics for the round-2 probes.

This file lives only in the audit workspace.  It does not alter the supplied
packet and deliberately checks predicates that the supplied verdicts omit.
"""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import random


HERE = Path(__file__).resolve().parent
PROBES = (HERE.parent / "original_packet" / "attack_mixed_quadrant_r2"
          / "probes")


def load(name, filename):
    spec = spec_from_file_location(name, PROBES / filename)
    mod = module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


w131 = load("w131", "wp131_borrowed_edge_acyclicity.py")
w132 = load("w132", "wp132_down_spectrum_blocking.py")


def load_path(name, path):
    spec = spec_from_file_location(name, path)
    mod = module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


w131_dkey_fixed = load_path(
    "w131_dkey_fixed",
    HERE / "wp131_refined_key_audit.py",
)


def wp131_omitted_checks():
    rng = random.Random(20260827)
    samples = []
    for name, maker, kw, vert in w131.CLASSES:
        data, _seen = w131.sample(rng, maker, kw, vert, 260)
        samples.append((name, data))

    borrowed = invalid_target = fallback_instances_reported = 0
    invalid_instances = 0
    invalid_rel = {}
    invalid_body = 0
    true_group_fallback_instances = 0
    agree_only_cycles = agree_plus_repeat_free_cycles = 0
    divergent_fallback_instances = 0

    for _name, data in samples:
        for c0, (model, val, root) in data:
            nodes, edges, _ = w131.extract(model, val, c0, root)
            borrowed += len(edges)
            bad_here = False
            for v, z, D, a in edges:
                rr = w131.rel(a, z)
                body_ok = w131.sat(model, val, z, D)
                if rr != w131.PP or not body_ok:
                    invalid_target += 1
                    bad_here = True
                    invalid_rel[rr] = invalid_rel.get(rr, 0) + 1
                    invalid_body += not body_ok
            invalid_instances += bad_here

            # Supplied Part G tests individual agreement on each edge.
            individual_missing = any(
                not any(
                    w131.rel(a, y) == w131.PP
                    and w131.rel(v, y) == w131.PP
                    and w131.sat(model, val, y, D)
                    for y in model
                )
                for v, _z, D, a in edges
            )
            fallback_instances_reported += individual_missing

            # The actual group-aware rule needs one target for the whole group.
            groups = {}
            for v, _z, D, a in edges:
                groups.setdefault((a, D), []).append(v)
            group_missing = any(
                not any(
                    w131.rel(a, y) == w131.PP
                    and w131.sat(model, val, y, D)
                    and all(w131.rel(v, y) == w131.PP for v in vs)
                    for y in model
                )
                for (a, D), vs in groups.items()
            )
            true_group_fallback_instances += group_missing
            divergent_fallback_instances += individual_missing != group_missing

            n_ag, b_ag, _ = w131.extract(
                model, val, c0, root, repeat_free=False, mode="agree"
            )
            agree_only_cycles += bool(w131.declared_cycle(n_ag, b_ag))
            n_both, b_both, _ = w131.extract(
                model, val, c0, root, repeat_free=True, mode="agree"
            )
            agree_plus_repeat_free_cycles += bool(w131.declared_cycle(n_both, b_both))

    print("WP131 omitted predicates")
    print(" borrowed edges:", borrowed)
    print(" invalid borrowed targets (not a PP/D witness of blocker):", invalid_target)
    print(" affected instances:", invalid_instances)
    print(" invalid blocker-target relation histogram:", invalid_rel)
    print(" invalid target-body evaluations:", invalid_body)
    print(" Part-G individual-missing instances:", fallback_instances_reported)
    print(" actual group-fallback instances:", true_group_fallback_instances)
    print(" instances on which those fallback predicates differ:", divergent_fallback_instances)
    print(" cycles, group-aware agree only:", agree_only_cycles)
    print(" cycles, group-aware agree + repeat-free:", agree_plus_repeat_free_cycles)


def d2_counterexample():
    # Two disjoint, modally indistinguishable components.  The root reaches their
    # lower points by different roles, making both occur in the extraction stage.
    root = frozenset({4, 5})
    a = frozenset({1})
    v = frozenset({3, 4})
    za = frozenset({1, 2})
    zv = frozenset({3, 4, 6})
    model = [root, a, v, za, zv]

    P = ("at", 0)
    demand = ("ex", w131.PP, P)
    c0 = ("and", ("ex", w131.DR, demand), ("ex", w131.PO, demand))
    val = {(0, x): x in (za, zv) for x in model}
    cl = w131.closure(c0)

    def T(x):
        return w131.mty(model, val, x, cl)

    def dkey(x):
        return (T(x), frozenset(T(y) for y in model if w131.rel(y, x) == w131.PP))

    root_dr = [y for y in model if w131.rel(root, y) == w131.DR and w131.sat(model, val, y, demand)]
    root_po = [y for y in model if w131.rel(root, y) == w131.PO and w131.sat(model, val, y, demand)]
    a_witnesses = [y for y in model if w131.rel(a, y) == w131.PP and w131.sat(model, val, y, P)]
    safe = [y for y in a_witnesses if w131.rel(y, v) != w131.PP and w131.rel(v, y) != w131.DR]
    nodes, borrowed, _parent = w131.extract(model, val, c0, root)

    print("D2 finite-set counterexample")
    print(" C0 satisfiable at root:", w131.sat(model, val, root, c0))
    print(" forall-PO-free:", w131.po_free(c0))
    print(" root DR-demand candidates include a:", a in root_dr)
    print(" root PO-demand candidates include v:", v in root_po)
    print(" mty(a) == mty(v):", T(a) == T(v))
    print(" dkey(a) == dkey(v):", dkey(a) == dkey(v))
    print(" a PP-witnesses for P:", a_witnesses)
    print(" all such witnesses DR from v:", all(w131.rel(v, y) == w131.DR for y in a_witnesses))
    print(" witnesses satisfying D2 selection:", safe)
    print(" corrected-dkey extraction nodes:", nodes)
    print(" corrected-dkey borrowed edges:", borrowed)
    print(" declared order cyclic:", bool(w131.declared_cycle(nodes, borrowed)))
    print(" borrowed edge violates ltNotDj:", any(w131.rel(vv, z) == w131.DR for vv, z, _D, _a in borrowed))


def wp132_unsound_fresh_sat():
    m, _c0, _group, _D = w132.counterexample()
    P = ("at", "P")
    impossible = ("all", w132.EQ, ("and", P, ("nat", "P")))
    satisfiable = ("ex", w132.EQ, P)
    print("WP132 fresh_sat semantic checks")
    print(" impossible forall-EQ contradiction reported:", w132.fresh_sat(m, impossible, [], {}))
    print(" satisfiable exists-EQ(P) reported with P=true:", w132.fresh_sat(m, satisfiable, [], {"P": True}))


def wp132_treatment_routes(seed=20260828, trials=1500):
    counts = {"existing": 0, "fresh": 0, "failure": 0}
    models = groups = 0
    for _name, mk in w132.CLASSES:
        rng = random.Random(seed)
        for _ in range(trials):
            m, c0 = w132.family_instance(rng, **mk)
            if not w132.po_free(c0) or not m.closed() or not any(m.sat(x, c0) for x in m.pts):
                continue
            models += 1
            cl = w132.closure(c0)
            for vs, D in w132.groups_of(m, c0, "key1"):
                if not all(w132.cone(m, v) for v in vs):
                    continue
                if D[0] != "ex" or D[1] != w132.DR:
                    continue
                groups += 1
                ok, why = w132.serviceable(m, vs, D, cl)
                if not ok:
                    counts["failure"] += 1
                elif why == "fresh witness":
                    counts["fresh"] += 1
                else:
                    counts["existing"] += 1
    print("WP132 key1 route audit")
    print(" accepted generated models:", models)
    print(" non-vacuous group-demand evaluations:", groups)
    print(" route counts:", counts)


if __name__ == "__main__":
    print("=== supplied type-only gate ===")
    wp131_omitted_checks()
    print()
    print("=== actual dkey gate, with role included in child key ===")
    w131 = w131_dkey_fixed
    wp131_omitted_checks()
    print()
    d2_counterexample()
    print()
    wp132_unsound_fresh_sat()
    print()
    wp132_treatment_routes()
    wrapper = (PROBES.parent / "run_probes.sh").read_text(encoding="utf-8")
    masks_failures = 'python3 "$f" || echo' in wrapper
    print()
    print("Wrapper masks nonzero probe exits:", masks_failures)
    assert masks_failures
