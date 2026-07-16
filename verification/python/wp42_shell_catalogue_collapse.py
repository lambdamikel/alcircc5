#!/usr/bin/env python3
"""
WP42: shell-staircase quotient collapse.

This checks the sharp question raised after WP41: does the shell half-graph
force unbounded non-uniform live data, or can it be represented by a finite
catalogue-style steering rule of the Lean Round19Transport shape?

Result: the shell staircase is finitely quotient-representable.  A two-template
catalogue (root + recursive shell step) and finite row-keyed steering tables
pass the catalogue-level S-condition checks for the involved templates.  Its
finite prefixes unfold to the intended half-graph pattern:

    p_i PP p_j       for i < j
    y_i DR p_j       for j <= i
    y_i PO p_j       for j > i
    y_i DR y_j       for i != j

Thus the shell is not an F6 counterexample in the Lean/certificate sense.  It
has unbounded raw non-singleton old-new domains, but they all collapse to a
finite number of row states.
"""

from itertools import product, permutations
from typing import Dict, Iterable, List, Tuple

Atom = str
Port = Tuple[str, int]  # ('slot',k), ('core',c), ('fresh',j)
Occ = Tuple[str, int, int]  # ('core',c,0) or ('born',step,j)

ATOMS: List[Atom] = ["eq", "pp", "ppi", "po", "dr"]
PROPER: List[Atom] = ["pp", "ppi", "po", "dr"]
CONV: Dict[Atom, Atom] = {"eq": "eq", "pp": "ppi", "ppi": "pp", "po": "po", "dr": "dr"}
COMP: Dict[Tuple[Atom, Atom], set[Atom]] = {}

def add(a: Atom, b: Atom, vals: Iterable[Atom]) -> None:
    COMP[(a, b)] = set(vals)

# RCC5 composition table, same as Round19Transport.lean.
add("eq", "eq", ["eq"])
for b in PROPER:
    add("eq", b, [b])
for a in PROPER:
    add(a, "eq", [a])
add("pp", "pp", ["pp"])
add("pp", "ppi", ["eq", "pp", "ppi", "po", "dr"])
add("pp", "po", ["pp", "po", "dr"])
add("pp", "dr", ["dr"])
add("ppi", "pp", ["eq", "pp", "ppi", "po"])
add("ppi", "ppi", ["ppi"])
add("ppi", "po", ["ppi", "po"])
add("ppi", "dr", ["ppi", "po", "dr"])
add("po", "pp", ["pp", "po"])
add("po", "ppi", ["ppi", "po", "dr"])
add("po", "po", ["eq", "pp", "ppi", "po", "dr"])
add("po", "dr", ["ppi", "po", "dr"])
add("dr", "pp", ["pp", "po", "dr"])
add("dr", "ppi", ["dr"])
add("dr", "po", ["pp", "po", "dr"])
add("dr", "dr", ["eq", "pp", "ppi", "po", "dr"])

class Template:
    def __init__(self, name: str, nslots: int, nfresh: int, net: Dict[Tuple[Port, Port], Atom]):
        self.name = name
        self.nslots = nslots
        self.nfresh = nfresh
        self.net = net

    def ports(self) -> List[Port]:
        return [("slot", k) for k in range(self.nslots)] + [("core", 0)] + [("fresh", j) for j in range(self.nfresh)]

    def old_ports(self) -> List[Port]:
        return [("slot", k) for k in range(self.nslots)] + [("core", 0)]

    def val(self, p: Port, q: Port) -> Atom:
        if p == q:
            return "eq"
        return self.net[(p, q)]


def converse_complete(net: Dict[Tuple[Port, Port], Atom]) -> Dict[Tuple[Port, Port], Atom]:
    out = dict(net)
    for (p, q), a in list(net.items()):
        out[(q, p)] = CONV[a]
    return out

C = ("core", 0)
S = ("slot", 0)
P = ("fresh", 0)  # next P point
Y = ("fresh", 1)  # shell point

# Root template T0: core p0, fresh p1 and y0.
T0 = Template("root", 0, 2, converse_complete({
    (C, P): "pp",   # p0 PP p1
    (C, Y): "dr",   # p0 DR y0
    (Y, P): "po",   # y0 PO p1
}))

# Recursive template T1: inherited slot s=p_n, core p0, fresh p_{n+1}, y_n.
T1 = Template("recursive", 1, 2, converse_complete({
    (C, S): "pp",   # p0 PP p_n
    (S, P): "pp",   # p_n PP p_{n+1}
    (S, Y): "dr",   # p_n DR y_n
    (Y, P): "po",   # y_n PO p_{n+1}
    (C, P): "pp",   # p0 PP p_{n+1}
    (C, Y): "dr",   # p0 DR y_n
}))

# Steering tables keyed by rows to old ports: root row=(to core), recursive row=(to core,to slot).
# Values are pairs (value to fresh P, value to fresh Y).
F0: Dict[Tuple[Atom, ...], Tuple[Atom, Atom]] = {
    ("eq",): ("pp", "dr"),
    ("pp",): ("pp", "dr"),
    ("po",): ("pp", "po"),
    ("ppi",): ("pp", "po"),
    ("dr",): ("pp", "pp"),
}

F1: Dict[Tuple[Atom, ...], Tuple[Atom, Atom]] = {
    ("eq", "eq"): ("pp", "dr"),
    ("eq", "pp"): ("pp", "dr"),
    ("eq", "ppi"): ("pp", "dr"),
    ("eq", "po"): ("pp", "dr"),
    ("eq", "dr"): ("pp", "dr"),
    ("pp", "eq"): ("pp", "dr"),
    ("pp", "pp"): ("pp", "dr"),
    ("pp", "ppi"): ("pp", "dr"),
    ("pp", "po"): ("pp", "dr"),
    ("pp", "dr"): ("pp", "dr"),
    ("ppi", "eq"): ("pp", "dr"),
    ("ppi", "pp"): ("pp", "dr"),
    ("po", "eq"): ("pp", "dr"),
    ("po", "pp"): ("pp", "dr"),
    ("dr", "eq"): ("pp", "dr"),
    ("dr", "pp"): ("pp", "dr"),
    ("ppi", "po"): ("po", "ppi"),
    ("ppi", "dr"): ("pp", "po"),
    ("po", "ppi"): ("po", "po"),
    ("po", "po"): ("po", "po"),
    ("po", "dr"): ("pp", "po"),
    ("dr", "ppi"): ("po", "po"),
    ("dr", "po"): ("po", "dr"),
    ("ppi", "ppi"): ("po", "ppi"),
    ("dr", "dr"): ("pp", "dr"),
}


def rowval(row: Tuple[Atom, ...], p: Port) -> Atom:
    if p[0] == "core":
        return row[0]
    if p[0] == "slot":
        return row[1 + p[1]]
    raise ValueError(p)


def atom_rows(n: int) -> List[Tuple[Atom, ...]]:
    return list(product(ATOMS, repeat=n))


def check_template_scat(T: Template, F: Dict[Tuple[Atom, ...], Tuple[Atom, Atom]]) -> List[str]:
    """Finite analogue of the template-relevant parts of SCat."""
    errors: List[str] = []
    ports = T.ports()
    old = T.old_ports()
    fresh = [("fresh", j) for j in range(T.nfresh)]
    rows = atom_rows(1 + T.nslots)

    # net converse, properness, and net_r3.
    for p in ports:
        for q in ports:
            if T.val(q, p) != CONV[T.val(p, q)]:
                errors.append(f"{T.name}: net_conv failed {p},{q}")
    for p in ports:
        for z in fresh:
            if p != z and T.val(p, z) == "eq":
                errors.append(f"{T.name}: net_proper failed {p}->{z}")
    for p in ports:
        for q in ports:
            for z in fresh:
                if p != q and p != z and q != z:
                    if T.val(p, q) not in COMP[(T.val(p, z), CONV[T.val(q, z)])]:
                        errors.append(f"{T.name}: net_r3 failed {p},{q} via {z}")

    # steering member/member2/fresh/fresh/proper.
    for r in rows:
        if r not in F:
            errors.append(f"{T.name}: missing F row {r}")
            continue
        fvals = {fresh[j]: F[r][j] for j in range(T.nfresh)}
        for z in fresh:
            if fvals[z] == "eq":
                errors.append(f"{T.name}: f_proper failed {r}->{z}")
        for p in old:
            for z in fresh:
                rv = rowval(r, p)
                if CONV[rv] not in COMP[(T.val(p, z), CONV[fvals[z]])]:
                    errors.append(f"{T.name}: steer_member failed row {r}, old {p}, fresh {z}")
                if rv not in COMP[(fvals[z], CONV[T.val(p, z)])]:
                    errors.append(f"{T.name}: steer_member2 failed row {r}, old {p}, fresh {z}")
        for zx in fresh:
            for zy in fresh:
                if zx == zy:
                    continue
                if CONV[fvals[zx]] not in COMP[(T.val(zx, zy), CONV[fvals[zy]])]:
                    errors.append(f"{T.name}: steer_two_fresh failed row {r}, {zx},{zy}")
                if fvals[zx] not in COMP[(fvals[zy], T.val(zy, zx))]:
                    errors.append(f"{T.name}: steer_two_fresh2 failed row {r}, {zx},{zy}")

    # steered-steered: old pair v constrained through all old ports remains legal through each fresh port.
    for r in rows:
        for rp in rows:
            for v in ATOMS:
                if all(v in COMP[(rowval(r, a), CONV[rowval(rp, a)])] for a in old):
                    for j, z in enumerate(fresh):
                        if v not in COMP[(F[r][j], CONV[F[rp][j]])]:
                            errors.append(f"{T.name}: steer_steer failed rows {r},{rp}, v={v}, fresh={z}")
    return errors


def occ_core() -> Occ:
    return ("core", 0, 0)


def occ_born(step: int, j: int) -> Occ:
    return ("born", step, j)


def p_occ(i: int) -> Occ:
    return occ_core() if i == 0 else occ_born(i - 1, 0)


def y_occ(i: int) -> Occ:
    return occ_born(i, 1)


def pair_get(frame: Dict[Tuple[Occ, Occ], Atom], x: Occ, y: Occ) -> Atom:
    if x == y:
        return "eq"
    return frame[(x, y)]


def add_pair(frame: Dict[Tuple[Occ, Occ], Atom], x: Occ, y: Occ, a: Atom) -> None:
    if x == y:
        assert a == "eq"
        return
    old = frame.get((x, y))
    if old is not None:
        assert old == a, f"overwrite conflict {x}->{y}: {old} vs {a}"
        return
    frame[(x, y)] = a
    frame[(y, x)] = CONV[a]


def unfold_prefix(num_steps: int) -> Dict[Tuple[Occ, Occ], Atom]:
    """Unfold root plus num_steps-1 recursive steps."""
    assert num_steps >= 1
    frame: Dict[Tuple[Occ, Occ], Atom] = {}
    existing: List[Occ] = [occ_core()]

    for step in range(num_steps):
        T = T0 if step == 0 else T1
        F = F0 if step == 0 else F1
        slots: List[Occ] = [] if step == 0 else [p_occ(step)]
        fresh_occs = [occ_born(step, j) for j in range(T.nfresh)]

        def port_occ(p: Port) -> Occ:
            if p[0] == "core":
                return occ_core()
            if p[0] == "slot":
                return slots[p[1]]
            if p[0] == "fresh":
                return fresh_occs[p[1]]
            raise ValueError(p)

        # Pattern values among members, no overwrites.
        for p in T.ports():
            for q in T.ports():
                x, y = port_occ(p), port_occ(q)
                if x != y and (x, y) not in frame:
                    add_pair(frame, x, y, T.val(p, q))

        # Steering values: existing non-members to each fresh port.
        members = set(slots + [occ_core()] + fresh_occs)
        for x in list(existing):
            if x in members:
                continue
            row = tuple([pair_get(frame, x, occ_core())] + [pair_get(frame, x, s) for s in slots])
            vals = F[row]
            for j, z in enumerate(fresh_occs):
                add_pair(frame, x, z, vals[j])

        existing.extend(fresh_occs)
    return frame


def check_frame_closed(frame: Dict[Tuple[Occ, Occ], Atom], occs: List[Occ]) -> List[str]:
    errors = []
    for x, y in permutations(occs, 2):
        a = pair_get(frame, x, y)
        if a == "eq":
            errors.append(f"properness failed {x}->{y}")
        if pair_get(frame, y, x) != CONV[a]:
            errors.append(f"converse failed {x},{y}")
    for x, z, y in product(occs, repeat=3):
        xy = pair_get(frame, x, y)
        xz = pair_get(frame, x, z)
        zy = pair_get(frame, z, y)
        if xy not in COMP[(xz, zy)]:
            errors.append(f"closure failed {x}->{y}={xy} via {z}: {xz};{zy}")
            break
    return errors


def check_shell_pattern(frame: Dict[Tuple[Occ, Occ], Atom], num_steps: int) -> List[str]:
    # num_steps gives p_0..p_num_steps and y_0..y_{num_steps-1}
    errors = []
    for i in range(num_steps + 1):
        for j in range(num_steps + 1):
            if i < j and pair_get(frame, p_occ(i), p_occ(j)) != "pp":
                errors.append(f"expected p_{i} PP p_{j}")
    for i in range(num_steps):
        for j in range(num_steps + 1):
            got = pair_get(frame, y_occ(i), p_occ(j))
            exp = "dr" if j <= i else "po"
            if got != exp:
                errors.append(f"expected y_{i} {exp.upper()} p_{j}, got {got}")
    for i in range(num_steps):
        for j in range(num_steps):
            if i != j and pair_get(frame, y_occ(i), y_occ(j)) != "dr":
                errors.append(f"expected y_{i} DR y_{j}")
    return errors


def main() -> None:
    for T, F in [(T0, F0), (T1, F1)]:
        errs = check_template_scat(T, F)
        print(f"{T.name}: template-level SCat check errors = {len(errs)}")
        if errs:
            print("first errors:")
            for e in errs[:20]:
                print("  ", e)
            raise SystemExit(1)

    print("\nReachable recursive rows and steering:")
    print("  old P ancestors: row (to core, to slot) = ('ppi','pp') ->", F1[("ppi", "pp")])
    print("  old shell y_i:    row (to core, to slot) = ('dr','po')  ->", F1[("dr", "po")])
    print("  fresh order is (next P, new shell Y)")

    for n in [1, 2, 3, 5, 8]:
        frame = unfold_prefix(n)
        occs = [p_occ(i) for i in range(n + 1)] + [y_occ(i) for i in range(n)]
        errs = check_frame_closed(frame, occs) + check_shell_pattern(frame, n)
        print(f"prefix with {n} shell steps: objects={len(occs)}, errors={len(errs)}")
        if errs:
            for e in errs[:20]:
                print("  ", e)
            raise SystemExit(1)

    print("\nConclusion: finite row-keyed steering represents the entire shell staircase.")
    print("The shell half-graph has unbounded raw horizontal witnesses, but only two reachable")
    print("old-row classes at recursive interfaces: old P ancestors and old shell witnesses.")

if __name__ == "__main__":
    main()
