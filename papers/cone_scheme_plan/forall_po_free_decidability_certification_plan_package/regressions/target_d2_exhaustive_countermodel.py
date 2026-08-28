#!/usr/bin/env python3
"""Independent finite-set search and exact check for Target D2.

This probe does not import either packaged probe.  RCC5 atoms are interpreted
directly on nonempty finite sets.  It does two things:

1. Exhaustively searches all point sets of size at most four over universes of
   size at most three, and all one-atom valuations, for the small D2 core with
   formula A = exists PP.P.
2. Checks a slightly larger, singleton-root-realized example and simulates the
   relevant down-spectrum gate and borrowing step.

The distinction matters: (1) is a network-level countermodel once a and v are
both in the finite node list; (2) shows that the configuration can actually be
generated from a satisfiable forall-PO-free input by ordinary existential
expansion, rather than merely postulated as a node list.
"""

from itertools import combinations


DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
ATOMS = (DR, PO, EQ, PP, PPI)


def rel(x, y):
    if x == y:
        return EQ
    if x < y:
        return PP
    if y < x:
        return PPI
    if x.isdisjoint(y):
        return DR
    return PO


def regions(n):
    u = range(n)
    return tuple(frozenset(c) for k in range(1, n + 1)
                 for c in combinations(u, k))


# Formula syntax: ("p", name), ("and", f, g), ("ex", role, f),
# ("all", role, f).  No universal PO is used in either example.
def closure(f, out=None):
    if out is None:
        out = []
    if f not in out:
        out.append(f)
    if f[0] == "and":
        closure(f[1], out)
        closure(f[2], out)
    elif f[0] in ("ex", "all"):
        closure(f[2], out)
    return tuple(out)


def po_free(f):
    if f[0] == "p":
        return True
    if f[0] == "and":
        return po_free(f[1]) and po_free(f[2])
    if f[0] == "all" and f[1] == PO:
        return False
    return po_free(f[2])


def sat(model, valuation, x, f):
    k = f[0]
    if k == "p":
        return x in valuation.get(f[1], frozenset())
    if k == "and":
        return sat(model, valuation, x, f[1]) and sat(model, valuation, x, f[2])
    if k == "ex":
        return any(rel(x, y) == f[1] and sat(model, valuation, y, f[2])
                   for y in model)
    if k == "all":
        return all(rel(x, y) != f[1] or sat(model, valuation, y, f[2])
                   for y in model)
    raise ValueError(f"unknown formula {f!r}")


def mtype(model, valuation, x, cl):
    """Positive closure signature, matching the packet's probe convention."""
    return tuple(f for f in cl if sat(model, valuation, x, f))


def dkey(model, valuation, x, cl):
    lower_spectrum = frozenset(
        mtype(model, valuation, y, cl)
        for y in model if rel(y, x) == PP
    )
    return mtype(model, valuation, x, cl), lower_spectrum


def pp_witnesses(model, valuation, x, body):
    return tuple(y for y in model
                 if rel(x, y) == PP and sat(model, valuation, y, body))


def demand_persistent(model, valuation, x, body):
    """Packet's PP-kernel guard: forall PP.(exists PP.body)."""
    guard = ("all", PP, ("ex", PP, body))
    return sat(model, valuation, x, guard)


def composition_table(n=4):
    """Re-derive the RCC5 composition table from full finite-set semantics."""
    pts = regions(n)
    table = {(r, s): set() for r in ATOMS for s in ATOMS}
    for x in pts:
        for y in pts:
            for z in pts:
                table[(rel(x, y), rel(y, z))].add(rel(x, z))
    return table


def composition_closed(model, table):
    return all(rel(x, z) in table[(rel(x, y), rel(y, z))]
               for x in model for y in model for z in model)


P = ("p", "P")
A = ("ex", PP, P)


def core_conditions(model, valuation, a, v):
    """The exact D2 core for demand exists PP.P at same dkey."""
    cl = closure(A)
    wa = pp_witnesses(model, valuation, a, P)
    return {
        "distinct": a != v,
        "same_dkey": dkey(model, valuation, a, cl) == dkey(model, valuation, v, cl),
        "remaining_branch": rel(a, v) != PP,
        "actual_demand_a": sat(model, valuation, a, A) and bool(wa),
        "actual_demand_v": sat(model, valuation, v, A),
        "edge_served_not_kernel": not demand_persistent(model, valuation, a, P),
        "all_witnesses_below_or_dr": bool(wa) and all(
            rel(z, v) in (PP, DR) for z in wa
        ),
        "per_edge_safe_exists": any(rel(z, v) != PP and z != v for z in wa),
        "no_d2_safe_witness": not any(
            rel(z, v) != PP and rel(z, v) != DR and z != v for z in wa
        ),
    }


def exhaustive_core_search():
    """Search in increasing universe/domain size; return first countermodel."""
    checked = 0
    no_hit_by_size = []
    for n in range(1, 4):
        regs = regions(n)
        for size in range(2, min(4, len(regs)) + 1):
            before = checked
            for model in combinations(regs, size):
                for bits in range(1 << size):
                    ptrue = frozenset(model[i] for i in range(size)
                                      if (bits >> i) & 1)
                    val = {"P": ptrue}
                    for a in model:
                        for v in model:
                            if a == v:
                                continue
                            checked += 1
                            cond = core_conditions(model, val, a, v)
                            if all(cond.values()):
                                return {
                                    "universe_size": n,
                                    "domain_size": size,
                                    "checked": checked,
                                    "no_hit_by_size": no_hit_by_size,
                                    "model": model,
                                    "valuation": val,
                                    "a": a,
                                    "v": v,
                                    "conditions": cond,
                                }
            no_hit_by_size.append((n, size, checked - before))
    return None


def tc(edges, nodes):
    reach = set(edges)
    changed = True
    while changed:
        changed = False
        for x, y in tuple(reach):
            for y2, z in tuple(reach):
                if y == y2 and (x, z) not in reach:
                    reach.add((x, z))
                    changed = True
    return reach


def od_checks(model, extra_edge=None):
    lt = {(x, y) for x in model for y in model if rel(x, y) == PP}
    if extra_edge is not None:
        lt.add(extra_edge)
    lt = tc(lt, model)
    dj = {(x, y) for x in model for y in model if rel(x, y) == DR}
    strict = all(x != y for x, y in lt)
    symmetric_irreflexive = (all(x != y for x, y in dj)
                             and all((y, x) in dj for x, y in dj))
    downward = all((u, y) in dj
                   for x, y in dj for u in model
                   if u == x or (u, x) in lt)
    compatible = all((x, y) not in dj for x, y in lt)
    return {
        "strict_order": strict,
        "disj_symmetric_irreflexive": symmetric_irreflexive,
        "disj_downward_closed": downward,
        "lt_implies_not_disj": compatible,
    }, lt, dj


def simulate_gate(model, valuation, c0, root):
    """Minimal independent simulation of gate, expansion, and child records."""
    cl = closure(c0)
    nodes = [root]
    child = {}
    trace = []
    for stage in range(8):
        first = {}
        kept = []
        for x in nodes:
            k = dkey(model, valuation, x, cl)
            if k not in first:
                first[k] = x
                kept.append(x)
        new = []
        for x in kept:
            for f in mtype(model, valuation, x, cl):
                if f[0] != "ex":
                    continue
                # Only PP demands satisfying the guard are kernel-routed.
                if f[1] == PP and demand_persistent(model, valuation, x, f[2]):
                    continue
                cands = [y for y in model
                         if rel(x, y) == f[1]
                         and sat(model, valuation, y, f[2])]
                if not cands:
                    continue
                y = cands[0]
                child.setdefault((x, f[2]), y)
                if y not in nodes and y not in new:
                    new.append(y)
        trace.append((stage, tuple(nodes), tuple(kept), tuple(new)))
        if not new:
            break
        nodes.extend(new)

    first = {}
    for x in nodes:
        first.setdefault(dkey(model, valuation, x, cl), x)
    blocked = tuple(
        x for x in nodes if first[dkey(model, valuation, x, cl)] != x
    )
    return tuple(nodes), child, tuple(trace), blocked, first


def explicit_root_realized():
    """A five-point model whose singleton-root expansion reaches a and v."""
    # Underlying carrier {0,1,2,3}.
    r = frozenset({0, 3})
    a = frozenset({0})
    v = frozenset({2})
    z = frozenset({0, 1})
    w = frozenset({2, 3})
    model = (r, a, v, z, w)  # deterministic witness order
    valuation = {"P": frozenset({z, w})}

    # Root formula: (exists PPI.A) and (exists DR.A), A = exists PP.P.
    left = ("ex", PPI, A)
    right = ("ex", DR, A)
    c0 = ("and", left, right)
    cl = closure(c0)

    nodes, child, trace, blocked, first = simulate_gate(
        model, valuation, c0, r
    )
    assert v in blocked
    mate = first[dkey(model, valuation, v, cl)]
    target = child[(mate, P)]

    wa = pp_witnesses(model, valuation, mate, P)
    wv = pp_witnesses(model, valuation, v, P)
    before, _, _ = od_checks(tuple(nodes))
    after, lt_after, dj_after = od_checks(tuple(nodes), (v, target))
    return {
        "model": model,
        "valuation": valuation,
        "root": r,
        "a": a,
        "v": v,
        "z": z,
        "w": w,
        "c0": c0,
        "closure": cl,
        "trace": trace,
        "nodes": nodes,
        "blocked": blocked,
        "mate": mate,
        "target": target,
        "witnesses": wa,
        "same_type": mtype(model, valuation, a, cl) == mtype(model, valuation, v, cl),
        "same_lower_spectrum": dkey(model, valuation, a, cl)[1]
                               == dkey(model, valuation, v, cl)[1],
        "same_dkey": dkey(model, valuation, a, cl)
                     == dkey(model, valuation, v, cl),
        "root_satisfies_c0": sat(model, valuation, r, c0),
        "forall_po_free": po_free(c0),
        "demand_actual": sat(model, valuation, a, A),
        "demand_nonpersistent": not demand_persistent(model, valuation, a, P),
        "all_mate_witnesses_dr": bool(wa) and all(rel(y, v) == DR for y in wa),
        "reverse_order_also_fails": bool(wv) and all(rel(y, a) == DR for y in wv),
        "per_edge_safe": rel(target, v) != PP and target != v,
        "d2_safe": rel(target, v) not in (PP, DR) and target != v,
        "before_od": before,
        "after_od": after,
        "borrowed_edge": (v, target),
        "borrowed_edge_is_disj": (v, target) in dj_after,
        "borrowed_order_acyclic": all(x != y for x, y in lt_after),
    }


def explicit_nonempty_spectrum():
    """Mixed, direct-root strengthening with matching nonempty spectra."""
    a = frozenset({0, 1})
    a0 = frozenset({0})
    v = frozenset({3, 4})
    v0 = frozenset({3})
    z = frozenset({0, 1, 2})
    w = frozenset({3, 4, 5})
    p = frozenset({1, 4})
    model = (a, v, z, p, w, a0, v0)
    valuation = {
        "P": frozenset({z, w}),
        "Q": frozenset({a, v}),
        "R": frozenset({p}),
    }
    qatom = ("p", "Q")
    ratom = ("p", "R")
    c0 = ("and", ("and", ("ex", DR, qatom), A),
          ("ex", PO, ratom))
    cl = closure(c0)
    nodes, child, trace, blocked, first = simulate_gate(
        model, valuation, c0, a
    )
    assert v in blocked and first[dkey(model, valuation, v, cl)] == a
    target = child[(a, P)]
    spectrum_a = dkey(model, valuation, a, cl)[1]
    spectrum_v = dkey(model, valuation, v, cl)[1]
    before, _, _ = od_checks(model)
    after, lt_after, dj_after = od_checks(nodes, (v, target))
    return {
        "model": model,
        "c0": c0,
        "root": a,
        "a": a,
        "v": v,
        "z": z,
        "nodes": nodes,
        "trace": trace,
        "target": target,
        "root_satisfies_c0": sat(model, valuation, a, c0),
        "forall_po_free": po_free(c0),
        "same_type": mtype(model, valuation, a, cl)
                     == mtype(model, valuation, v, cl),
        "same_nonempty_spectrum": spectrum_a == spectrum_v and bool(spectrum_a),
        "spectrum_size": len(spectrum_a),
        "demand_actual": sat(model, valuation, a, A),
        "demand_nonpersistent": not demand_persistent(model, valuation, a, P),
        "unique_witness_dr": pp_witnesses(model, valuation, a, P) == (z,)
                             and rel(z, v) == DR,
        "blocked": v in blocked,
        "borrow_is_d2_bad": target == z and rel(target, v) == DR,
        "base_od": all(before.values()),
        "borrow_acyclic": all(x != y for x, y in lt_after),
        "borrow_pair_disj": (v, target) in dj_after,
        "borrow_breaks_lt_not_disj": not after["lt_implies_not_disj"],
    }


def fmt_set(x):
    return "{" + ",".join(map(str, sorted(x))) + "}"


def main():
    table = composition_table(4)
    print("TARGET D2: INDEPENDENT EXHAUSTIVE / SYMBOLIC CHECK")
    print("=" * 72)
    print("RCC5 composition cells re-derived from finite-set semantics:",
          len(table), "of 25")

    hit = exhaustive_core_search()
    assert hit is not None
    print("\nPART 1 - bounded exhaustive network-level search")
    for n, size, count in hit["no_hit_by_size"]:
        print(f"  no hit: universe={n}, domain={size}; candidate pairs={count}")
    print(f"  FIRST HIT: universe={hit['universe_size']}, "
          f"domain={hit['domain_size']}; cumulative candidate pairs={hit['checked']}")
    model = hit["model"]
    a, v = hit["a"], hit["v"]
    print("  domain:", [fmt_set(x) for x in model])
    print("  P true:", [fmt_set(x) for x in hit["valuation"]["P"]])
    print("  a =", fmt_set(a), "v =", fmt_set(v), "rho(a,v) =", rel(a, v))
    print("  a-witnesses:",
          [(fmt_set(z), rel(z, v)) for z in pp_witnesses(model, hit["valuation"], a, P)])
    print("  exact checks:")
    for k, value in hit["conditions"].items():
        print(f"    {k:31s}: {value}")
    assert composition_closed(model, table)

    ex = explicit_root_realized()
    print("\nPART 2 - formula-realized singleton-root extraction")
    print("  model points:")
    for name in ("root", "a", "v", "z", "w"):
        x = ex[name]
        print(f"    {name:4s} = {fmt_set(x):8s}   P={sat(ex['model'], ex['valuation'], x, P)}")
    print("  C0 = (exists PPI.A) and (exists DR.A), A = exists PP.P")
    for stage, nodes, kept, new in ex["trace"]:
        print(f"  stage {stage}: nodes={[fmt_set(x) for x in nodes]}, "
              f"kept={[fmt_set(x) for x in kept]}, "
              f"new={[fmt_set(x) for x in new]}")
    print("  borrowed edge:", fmt_set(ex["borrowed_edge"][0]), "<",
          fmt_set(ex["borrowed_edge"][1]))
    checks = {
        "C0 satisfiable at root": ex["root_satisfies_c0"],
        "forall-PO-free": ex["forall_po_free"],
        "mty(a) = mty(v)": ex["same_type"],
        "down-spectrum(a) = down-spectrum(v)": ex["same_lower_spectrum"],
        "dkey(a) = dkey(v)": ex["same_dkey"],
        "v is actually blocked": ex["v"] in ex["blocked"],
        "gate-mate is a": ex["mate"] == ex["a"],
        "actual exists-PP.P demand": ex["demand_actual"],
        "demand is edge-served (guard false)": ex["demand_nonpersistent"],
        "all a-witnesses are DR from v": ex["all_mate_witnesses_dr"],
        "opposite gate order fails symmetrically": ex["reverse_order_also_fails"],
        "per-edge safety holds": ex["per_edge_safe"],
        "D2-safe witness exists": ex["d2_safe"],
        "base frame passes ordered-disjoint checks": all(ex["before_od"].values()),
        "borrowed order remains acyclic": ex["borrowed_order_acyclic"],
        "borrowed pair is disjoint": ex["borrowed_edge_is_disj"],
        "lt implies not disj after borrow": ex["after_od"]["lt_implies_not_disj"],
    }
    for k, value in checks.items():
        print(f"    {k:43s}: {value}")

    expected = [value for k, value in checks.items()
                if k not in ("D2-safe witness exists",
                             "lt implies not disj after borrow")]
    assert all(expected)
    assert checks["D2-safe witness exists"] is False
    assert checks["lt implies not disj after borrow"] is False
    assert composition_closed(ex["model"], table)

    ne = explicit_nonempty_spectrum()
    print("\nPART 3 - nonempty down-spectrum strengthening")
    print("  C0 = (exists DR.Q) and (exists PP.P) and (exists PO.R)")
    print("  direct singleton root = a; mixed DR/PP/PO existential input")
    print("  matching lower-spectrum cardinality:", ne["spectrum_size"])
    ne_checks = {
        "C0 satisfiable at root": ne["root_satisfies_c0"],
        "forall-PO-free": ne["forall_po_free"],
        "mty(a) = mty(v)": ne["same_type"],
        "equal spectra are nonempty": ne["same_nonempty_spectrum"],
        "v is actually blocked": ne["blocked"],
        "actual exists-PP.P demand": ne["demand_actual"],
        "demand is edge-served (guard false)": ne["demand_nonpersistent"],
        "unique a-witness is DR from v": ne["unique_witness_dr"],
        "borrowed target violates D2": ne["borrow_is_d2_bad"],
        "base ordered-disjoint frame is valid": ne["base_od"],
        "borrowed order remains acyclic": ne["borrow_acyclic"],
        "borrowed pair is disjoint": ne["borrow_pair_disj"],
        "borrow breaks lt implies not disj": ne["borrow_breaks_lt_not_disj"],
    }
    for k, value in ne_checks.items():
        print(f"    {k:43s}: {value}")
    assert all(ne_checks.values())
    assert composition_closed(ne["model"], table)

    print("\nVERDICT: TARGET D2'S UNIVERSAL SELECTION CLAIM IS FALSE.")
    print("  The formula-realized example has one gate-mate witness, it is DR")
    print("  from the blocked node, and the borrowed edge is acyclic but violates")
    print("  lt(x,y) -> not disj(x,y).  Thus this isolates D2 from D1.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
