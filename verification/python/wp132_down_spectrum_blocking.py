#!/usr/bin/env python3
"""WP132 -- does DOWN-SPECTRUM blocking make a shared top serviceable?

ASSEMBLY_DESIGN sec. 256-257.  The cold attack refuted type-only blocking with an
eight-point counterexample: give two same-TYPE occurrences a common top `t`, and
comp(DR,PPI)={DR} drags t's own DR-witness onto BOTH lower cones, which disagree
on a forall-DR body.  Its proposed replacement keys on

    q(v) = ( mty(v), { mty(x) : x PP v } )        -- type + strict lower spectrum

We certified that the SPECIFIC conflict cannot arise within such a key class
(`cone_agreement_of_spectrum`: a body's truth is fixed by the point's type, so
equal spectra make "holds across my cone" agree).  That is one obstruction
removed, not a construction.  THIS PROBE ASKS WHETHER ANY OBSTRUCTION OF THAT
SHAPE SURVIVES.

THE TEST.  For a group G of same-key blocked nodes owing `exists PP.D`:
  * U = union of the members' strict lower cones;
  * a shared top t must sit above every member, hence (by PP;PP) above all of U;
  * for each `exists DR.A` that t's label owes, a witness z must be DR from t and
    therefore -- by comp(DR,PPI)={DR} -- DR from every point of U;
  * so the group is SERVICEABLE iff some model point is DR from all of U and
    satisfies A.  Failure is exactly the sec. 256 shape, at whatever granularity
    the key provides.

PREDICTIONS, FIXED BEFORE THE RUN:
  R  regression: the packaged eight-point counterexample must FAIL at key0 and,
     if the refinement means anything, PASS at key1.
  C  control (key0, type-only): failures MUST occur.  A 0% reading means the
     harness does not reproduce a KNOWN counterexample -- treatment withheld.
  T  treatment (key1): the question.  0% is evidence for the pivot; anything
     above 0% is a counterexample to it AT THIS GRANULARITY.
  N  non-vacuity is reported FIRST and gates everything (wp130's rule); the
     count that matters is groups with >=2 members whose demand is modal and
     whose cones are non-empty.

Self-contained: the RCC5 table is re-derived from finite set semantics.
"""

import random
from itertools import combinations

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
ATOMS = [DR, PO, EQ, PP, PPI]


def rel_sets(a, b):
    if a == b:
        return EQ
    if a < b:
        return PP
    if b < a:
        return PPI
    return DR if not (a & b) else PO


def comp_table(n=4):
    regs = [frozenset(c) for k in range(1, n + 1)
            for c in combinations(range(n), k)]
    t = {}
    for a in regs:
        for b in regs:
            r = rel_sets(a, b)
            for c in regs:
                t.setdefault((r, rel_sets(b, c)), set()).add(rel_sets(a, c))
    return t


CT = comp_table(4)
CONV = {DR: DR, PO: PO, EQ: EQ, PP: PPI, PPI: PP}
assert sorted(CT[(PP, PP)]) == [PP] and sorted(CT[(DR, PPI)]) == [DR]

# ------------------------------------------------------------------ concepts


def closure(c, acc=None):
    acc = [] if acc is None else acc
    if c not in acc:
        acc.append(c)
    if c[0] in ("and", "or"):
        closure(c[1], acc)
        closure(c[2], acc)
    elif c[0] in ("ex", "all"):
        closure(c[2], acc)
    return acc


def po_free(c):
    if c[0] in ("at", "nat"):
        return True
    if c[0] in ("and", "or"):
        return po_free(c[1]) and po_free(c[2])
    if c[0] == "all" and c[1] == PO:
        return False
    return po_free(c[2])


class Model:
    def __init__(self, pts, R, val):
        self.pts, self.R, self.val = pts, R, val

    def sat(self, x, c):
        k = c[0]
        if k == "at":
            return c[1] in self.val[x]
        if k == "nat":
            return c[1] not in self.val[x]
        if k == "and":
            return self.sat(x, c[1]) and self.sat(x, c[2])
        if k == "or":
            return self.sat(x, c[1]) or self.sat(x, c[2])
        if k == "ex":
            return any(self.R(x, y) == c[1] and self.sat(y, c[2])
                       for y in self.pts)
        return all(self.R(x, y) != c[1] or self.sat(y, c[2])
                   for y in self.pts)

    def mty(self, x, cl):
        return tuple(d for d in cl if self.sat(x, d))

    def closed(self):
        for p in self.pts:
            for q in self.pts:
                if CONV[self.R(p, q)] != self.R(q, p):
                    return False
                for r in self.pts:
                    if self.R(p, r) not in CT[(self.R(p, q), self.R(q, r))]:
                        return False
        return True


def od_model(pts, lt, dj, val):
    def R(p, q):
        if p == q:
            return EQ
        if (p, q) in lt:
            return PP
        if (q, p) in lt:
            return PPI
        if (p, q) in dj:
            return DR
        return PO
    return Model(pts, R, val)


# ------------------------------------------- the packaged 8-point regression

def counterexample():
    pts = ["x1", "v1", "y1", "z1", "x2", "v2", "y2", "z2"]
    lt = set()
    for i in ("1", "2"):
        for a, b in [("x", "v"), ("v", "y"), ("x", "y")]:
            lt.add((a + i, b + i))
    dj = set()
    for i in ("1", "2"):
        for p in ("x", "v", "y"):
            dj.add((p + i, "z" + i))
            dj.add(("z" + i, p + i))
    val = {"x1": {"P"}, "v1": {"P", "Q", "R"}, "y1": {"P", "Q"}, "z1": {"S"},
           "x2": {"Q", "S"}, "v2": {"P", "Q", "R"}, "y2": {"P", "Q"},
           "z2": set()}
    UP = ("all", DR, ("at", "P"))
    UQ = ("all", DR, ("at", "Q"))
    A = ("or", UP, UQ)
    D = ("ex", DR, A)
    C0 = ("and", ("and", ("ex", PP, D), ("ex", PO, ("at", "R"))),
          ("ex", PO, ("at", "S")))
    return od_model(pts, lt, dj, val), C0, ["v1", "v2"], D


# ------------------------------------------------------------------- the test

def cone(m, v):
    return [x for x in m.pts if m.R(x, v) == PP]


def atoms_of(c, acc=None):
    acc = set() if acc is None else acc
    if c[0] in ("at", "nat"):
        acc.add(c[1])
    elif c[0] in ("and", "or"):
        atoms_of(c[1], acc)
        atoms_of(c[2], acc)
    elif c[0] in ("ex", "all"):
        atoms_of(c[2], acc)
    return acc


def fresh_sat(m, A, U, assign):
    """Truth of `A` at a FRESH point that is DR from exactly `U`.

    Its own atoms are free (given by `assign`); a `forall DR.E` there is
    determined by the MODEL, since E is evaluated at U's points.  Nested
    existentials would need their own witnesses and are treated as unavailable
    (conservative: it can only make the test report failure more often)."""
    k = A[0]
    if k == "at":
        return assign.get(A[1], False)
    if k == "nat":
        return not assign.get(A[1], False)
    if k == "and":
        return fresh_sat(m, A[1], U, assign) and fresh_sat(m, A[2], U, assign)
    if k == "or":
        return fresh_sat(m, A[1], U, assign) or fresh_sat(m, A[2], U, assign)
    if k == "all":
        if A[1] != DR:
            return True              # no forced neighbours in that direction
        return all(m.sat(x, A[2]) for x in U)
    return False                     # nested existential: conservatively unmet


def serviceable(m, group, D, cl):
    """Can a shared top above `group` serve its own demand D?

    The top sits above the UNION U of the members' cones, so any DR-witness it
    needs is forced DR from all of U (comp(DR,PPI)={DR}).  Two ways to serve it:

      (i)  an EXISTING model point that is DR from all of U and satisfies A;
      (ii) a FRESH point -- the pivot's copied gadget -- which is DR from U by
           fiat, so the question is whether A can hold there GIVEN that its
           forall-DR bodies must hold across the whole of U.

    Route (ii) is the one that matters: sec.256's counterexample is exactly the
    case where no forall-DR body of A holds across the union."""
    U = []
    for v in group:
        for x in cone(m, v):
            if x not in U:
                U.append(x)
    if D[0] != "ex" or D[1] != DR:
        return True, "demand is not exists-DR; sec.256's shape does not apply"
    A = D[2]
    for z in m.pts:
        if z in U or z in group:
            continue
        if m.sat(z, A) and all(m.R(z, x) == DR for x in U):
            return True, f"existing point {z}"
    ats = sorted(atoms_of(A))
    for bits in range(1 << len(ats)):
        assign = {a: bool(bits >> i & 1) for i, a in enumerate(ats)}
        if fresh_sat(m, A, U, assign):
            return True, "fresh witness"
    return False, "no existing NOR fresh witness can serve the union"


def keys(m, cl, mode):
    if mode == "key0":
        return lambda v: m.mty(v, cl)
    return lambda v: (m.mty(v, cl),
                      frozenset(m.mty(x, cl) for x in cone(m, v)))


def groups_of(m, C0, mode):
    """Same-key nodes that jointly owe some `exists PP.D`."""
    cl = closure(C0)
    K = keys(m, cl, mode)
    buckets = {}
    for v in m.pts:
        buckets.setdefault(K(v), []).append(v)
    out = []
    for _k, vs in buckets.items():
        if len(vs) < 2:
            continue
        for d in m.mty(vs[0], cl):
            if d[0] == "ex" and d[1] == PP:
                out.append((vs, d[2]))
    return out


def assess(m, C0, mode):
    cl = closure(C0)
    tot = nonvac = fail = 0
    for vs, D in groups_of(m, C0, mode):
        tot += 1
        cones_ok = all(cone(m, v) for v in vs)
        modal = D[0] == "ex" and D[1] == DR
        if cones_ok and modal:
            nonvac += 1
            ok, _why = serviceable(m, vs, D, cl)
            if not ok:
                fail += 1
    return tot, nonvac, fail


# ------------------------------------------------------------- the generator

def rand_body(rng, natoms):
    a = rng.randrange(natoms)
    return ("at", a) if rng.random() < 0.5 else ("nat", a)


def family_instance(rng, branches=3, depth=2, extra_sides=1):
    """A randomized FAMILY around the eight-point counterexample.

    Each branch is a chain  x_b < ... < v_b < y_b  with a side point z_b that is
    DR from exactly that branch.  Upper chain points carry every atom, so the
    `v_b` share a model type; the BOTTOM point x_b carries only the atom of its
    branch's CLASS, so cones may or may not agree.

    Branches are randomly partitioned into x-classes.  Branches in the same class
    have IDENTICAL bottom valuations, so `key1` groups exactly those -- which is
    what makes the treatment non-trivial: the question is whether a shared top
    works for a group whose cones DO agree.  Branches in different classes have
    disagreeing cones and are the sec.256 configuration, which `key0` lumps
    together and `key1` separates."""
    ncls = rng.randint(1, max(1, branches - 1))
    cls = [rng.randrange(ncls) for _ in range(branches)]
    natoms = max(2, ncls)
    pts, lt, dj, val = [], set(), set(), {}
    for b in range(branches):
        chain = [f"c{b}_{i}" for i in range(depth + 1)]
        pts += chain
        for i in range(len(chain)):
            for j in range(i + 1, len(chain)):
                lt.add((chain[i], chain[j]))
        # bottom carries only its CLASS atom; the rest carry everything
        val[chain[0]] = {cls[b]}
        for q in chain[1:]:
            val[q] = set(range(natoms))
        z = f"z{b}"
        pts.append(z)
        val[z] = set()
        for q in chain:
            dj.add((z, q))
            dj.add((q, z))
    for e in range(extra_sides):
        w = f"w{e}"
        pts.append(w)
        val[w] = {a for a in range(natoms) if rng.random() < 0.5}
        for b in range(branches):
            if rng.random() < 0.5:
                for q in [p for p in pts if p.startswith(f"c{b}_")]:
                    dj.add((w, q))
                    dj.add((q, w))
    m = od_model(pts, lt, dj, val)
    inner = ("all", DR, ("at", 0))
    for a in range(1, natoms):
        inner = ("or", inner, ("all", DR, ("at", a)))
    D = ("ex", DR, inner)
    C0 = ("and", ("ex", PP, D), ("ex", PPI, ("at", 0)))
    return m, C0


# --------------------------------------------------------------------- parts

def part_r():
    print("PART R -- regression on the packaged eight-point counterexample")
    m, C0, group, D = counterexample()
    cl = closure(C0)
    print(f"  model composition-closed        : {m.closed()}")
    print(f"  forall-PO-free                  : {po_free(C0)}")
    k0 = keys(m, cl, "key0")
    k1 = keys(m, cl, "key1")
    print(f"  key0 same for v1,v2 (must be T) : {k0('v1') == k0('v2')}")
    print(f"  key1 same for v1,v2 (must be F) : {k1('v1') == k1('v2')}")
    ok, why = serviceable(m, group, D, cl)
    print(f"  shared top serviceable at key0  : {ok}  ({why})")
    good = (m.closed() and po_free(C0) and k0('v1') == k0('v2')
            and k1('v1') != k1('v2') and not ok)
    print(f"  => regression {'PASS' if good else 'FAIL'}")
    return good


def sweep(rng, mode, trials, **mk):
    T = N = F = D = 0
    for _ in range(trials):
        m, C0 = family_instance(rng, **mk)
        if not po_free(C0):
            continue
        if not m.closed():
            D += 1                      # counted, never silently skipped
            continue
        if not any(m.sat(x, C0) for x in m.pts):
            continue
        t, n, f = assess(m, C0, mode)
        T += t
        N += n
        F += f
    return T, N, F, D


CLASSES = [
    ("2 branches, depth 2", {"branches": 2, "depth": 2, "extra_sides": 1}),
    ("3 branches, depth 2", {"branches": 3, "depth": 2, "extra_sides": 1}),
    ("3 branches, depth 3", {"branches": 3, "depth": 3, "extra_sides": 2}),
    ("4 branches, depth 2", {"branches": 4, "depth": 2, "extra_sides": 2}),
]


def main(seed=20260828, trials=1500):
    print(__doc__.split("Self-contained")[0].rstrip())
    print("=" * 70)
    reg = part_r()

    print("\nPART N/C/T -- non-vacuity gate, then control and treatment")
    print(f"  {'model class':22s} {'key':>6} {'groups':>8} {'non-vac':>8} "
          f"{'unserviceable':>14}")
    ctrl_fail = 0
    treat_fail = 0
    treat_nonvac = 0
    for name, mk in CLASSES:
        for mode in ("key0", "key1"):
            rng = random.Random(seed)
            T, N, F, Dr = sweep(rng, mode, trials, **mk)
            pct = (100.0 * F / N) if N else float("nan")
            print(f"  {name:22s} {mode:>6} {T:8d} {N:8d} "
                  f"{F:8d} = {pct:5.1f}%   (non-closed dropped: {Dr})")
            if mode == "key0":
                ctrl_fail += F
            else:
                treat_fail += F
                treat_nonvac += N
    print(f"  control failures (must be > 0)      : {ctrl_fail}")
    print(f"  treatment failures                  : {treat_fail}"
          f"  on {treat_nonvac} non-vacuous groups")

    print("\n" + "=" * 70)
    if not reg:
        print("VERDICT: REGRESSION FAILED -- the harness does not reproduce the")
        print("  known counterexample.  Nothing below is trustworthy.")
        return 1
    if ctrl_fail == 0:
        print("VERDICT: CONTROL MISSED its stated expectation (failures at the")
        print("  type-only key).  Treatment WITHHELD -- the generator does not")
        print("  reach the phenomenon, exactly as wp131's first run did not.")
        return 1
    if treat_nonvac < 30:
        print(f"VERDICT: VACUOUS -- only {treat_nonvac} non-vacuous groups at the")
        print("  refined key.  No reading is reportable.  Reweight and rerun.")
        return 1
    if treat_fail == 0:
        print("VERDICT: the refined key removed every failure the type-only key")
        print("  exhibited, on a non-vacuous sample.  EVIDENCE for the pivot,")
        print("  not proof: finite randomized sweep, finite set models, and the")
        print("  copied-gadget and cycling-context parts are untested here.")
        return 0
    print("VERDICT: failures SURVIVE the refined key.  The down-spectrum pivot")
    print("  is refuted at this granularity; a strictly finer key or a")
    print("  different construction is needed.")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
