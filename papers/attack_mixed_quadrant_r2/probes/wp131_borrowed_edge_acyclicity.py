#!/usr/bin/env python3
"""WP131 -- does the BORROWED EDGE keep the declared order acyclic?

ASSEMBLY_DESIGN sec. 254.  The extraction blocks by model type: a node `v` whose
type already occurs earlier in the stage is not expanded; instead the certificate
DECLARES a PP-edge from `v` to the witness `z` of its gate-mate `a`
(`mty a = mty v`).  Propagation is certified (`borrowed_ee_all`).  What is NOT
certified is ACYCLICITY -- that `z` does not already lie below `v`.

`borrowed_edge_dichotomy` (certified, axiom-free) says the bad case forces
`a < v` in the model, i.e. a TYPE REPEAT on an ascending PP-chain, and
`borrowed_cycle_cuts` (= `path_cut`) says such a repeat is removable.  The open
step is whether choosing repeat-free chains makes the bad case never arise.

PREDICTIONS, STATED BEFORE THE RUN (per the project's probe discipline):

  B  dichotomy transcription ......... 100%   (it is a certified theorem; any
                                               miss means THIS SCRIPT is wrong)
  D0 control, no gating .............. 0 cycles (declared order = model order)
  D1 treatment, gating + borrowing ... NONZERO expected.  A 0% reading is to be
                                       treated as VACUITY until part N shows the
                                       sample actually contains blocked nodes
                                       with PP demands.
  C  repeat-free selection ........... strictly fewer cycles than D1; whether it
                                       reaches 0 is the question.

Part N counts the non-vacuous instances FIRST (wp130's lesson: a rate measured
on a sample that barely exercises the property is indistinguishable from a
finding).

Self-contained: RCC5 relations and the composition table are re-derived from
finite set semantics.
"""

import random
from itertools import combinations

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
ATOMS = [DR, PO, EQ, PP, PPI]


def rel(a, b):
    if a == b:
        return EQ
    if a < b:
        return PP
    if b < a:
        return PPI
    if not (a & b):
        return DR
    return PO


def subsets(univ):
    out = []
    for k in range(1, len(univ) + 1):
        for c in combinations(sorted(univ), k):
            out.append(frozenset(c))
    return out


def comp_table(n=4):
    regs = subsets(set(range(n)))
    t = {}
    for a in regs:
        for b in regs:
            r = rel(a, b)
            for c in regs:
                t.setdefault((r, rel(b, c)), set()).add(rel(a, c))
    return t


CT = comp_table(4)

# ------------------------------------------------------------ concept syntax


def closure(c, acc=None):
    if acc is None:
        acc = []
    if c not in acc:
        acc.append(c)
    k = c[0]
    if k in ("and", "or"):
        closure(c[1], acc)
        closure(c[2], acc)
    elif k in ("ex", "all"):
        closure(c[2], acc)
    return acc


def po_free(c):
    k = c[0]
    if k in ("at", "nat"):
        return True
    if k in ("and", "or"):
        return po_free(c[1]) and po_free(c[2])
    if k == "all" and c[1] == PO:
        return False
    return po_free(c[2])


def sat(model, val, x, c):
    k = c[0]
    if k == "at":
        return val.get((c[1], x), False)
    if k == "nat":
        return not val.get((c[1], x), False)
    if k == "and":
        return sat(model, val, x, c[1]) and sat(model, val, x, c[2])
    if k == "or":
        return sat(model, val, x, c[1]) or sat(model, val, x, c[2])
    if k == "ex":
        return any(rel(x, y) == c[1] and sat(model, val, y, c[2]) for y in model)
    return all(rel(x, y) != c[1] or sat(model, val, y, c[2]) for y in model)


def mty(model, val, x, cl):
    return tuple(d for d in cl if sat(model, val, x, d))


def persist_ds(model, val, x, cl):
    """The Lean `persistDs`: PP-demands whose GUARD holds -- these go to a
    kernel, not to an edge."""
    out = set()
    for d in cl:
        if d[0] == "ex" and d[1] == PP:
            guard = ("all", PP, ("ex", PP, d[2]))
            if sat(model, val, x, d) and sat(model, val, x, guard):
                out.add(d[2])
    return out


# ------------------------------------------------- concept / model generators

def rand_concept(rng, depth, natoms=2, vertical=0.0):
    if depth == 0 or rng.random() < 0.22:
        i = rng.randrange(natoms)
        return ("at", i) if rng.random() < 0.6 else ("nat", i)
    r = rng.random()
    if r < 0.18:
        return ("and", rand_concept(rng, depth - 1, natoms, vertical),
                rand_concept(rng, depth - 1, natoms, vertical))
    if r < 0.28:
        return ("or", rand_concept(rng, depth - 1, natoms, vertical),
                rand_concept(rng, depth - 1, natoms, vertical))
    if r < 0.72:
        # weight PP up when `vertical` is high: repeats live on PP-chains
        rr = PP if rng.random() < vertical else rng.choice(ATOMS)
        return ("ex", rr, rand_concept(rng, depth - 1, natoms, vertical))
    rr = PP if rng.random() < vertical else rng.choice([DR, PP, PPI, EQ])
    return ("all", rr, rand_concept(rng, depth - 1, natoms, vertical))


def model_random(rng, usize=4, natoms=2):
    regs = subsets(set(range(usize)))
    m = rng.sample(regs, min(len(regs), rng.randint(2, 6)))
    val = {(a, x): rng.random() < 0.5 for a in range(natoms) for x in m}
    return m, val


def model_chain(rng, usize=6, natoms=2):
    """A long nested PP-chain plus a little side structure -- the class where
    type repeats on an ascending chain actually occur."""
    chain = [frozenset(range(k + 1)) for k in range(usize)]
    m = list(chain)
    for _ in range(rng.randint(0, 2)):
        m.append(frozenset(rng.sample(range(usize), rng.randint(1, usize))))
    m = list(dict.fromkeys(m))
    # PERIODIC valuation: makes types recur up the chain (the hard case)
    period = rng.randint(2, 3)
    val = {}
    for a in range(natoms):
        bits = [rng.random() < 0.5 for _ in range(period)]
        for idx, x in enumerate(m):
            val[(a, x)] = bits[idx % period]
    return m, val


def find_model(rng, c, maker, tries=120, **kw):
    for _ in range(tries):
        m, val = maker(rng, **kw)
        for x in m:
            if sat(m, val, x, c):
                return m, val, x
    return None


# -------------------------------------------------------------- the extraction

def extract(model, val, c0, root, repeat_free=False, gate=True,
            mode=None, above=None):
    """Runs the ASSEMBLY_DESIGN sec.250 recipe.

    Returns (nodes, borrowed, path) where
      nodes    -- list of model points, in creation order (the stage);
      borrowed -- list of (v, z, D): blocked node v borrows gate-mate's witness z;
      path     -- parent map, for the repeat-free test.
    """
    cl = closure(c0)
    ty = {}

    def T(x):
        if x not in ty:
            ty[x] = mty(model, val, x, cl)
        return ty[x]

    nodes = [root]
    parent = {root: None}
    borrowed = []
    child = {}

    def anc_types(x):
        out, cur = [], parent.get(x)
        while cur is not None:
            out.append(T(cur))
            cur = parent.get(cur)
        return out

    def gated():
        if not gate:
            return list(nodes)
        seen, out = set(), []
        for n in nodes:
            if T(n) not in seen:
                seen.add(T(n))
                out.append(n)
        return out

    def witness(a, r, D, avoid, above=None):
        """Pick a witness for ex(r,D) at a.

        repeat_free  -- prefer one whose type is not already on the path.
        `above`      -- (borrowed edges only) prefer one the model ALREADY puts
                        PP-above the borrowing node, so the declared edge agrees
                        with the model and cannot create a cycle."""
        cands = [y for y in model
                 if rel(a, y) == r and sat(model, val, y, D)]
        if above is not None:
            agree = [y for y in cands if all(rel(u, y) == PP for u in above)]
            if agree:
                return agree[0]
        if repeat_free:
            fresh = [y for y in cands if T(y) not in avoid]
            if fresh:
                return fresh[0]
        return cands[0] if cands else None

    for _ in range(40):
        g = gated()
        new = []
        for a in g:
            pd = persist_ds(model, val, a, cl)
            for d in T(a):
                if d[0] != "ex":
                    continue
                if d[1] == PP and d[2] in pd:
                    continue                      # kernel-served, no edge
                w = witness(a, d[1], d[2], set(anc_types(a) + [T(a)]))
                if w is None:
                    continue
                child.setdefault((a, d[2]), w)
                if w not in nodes and w not in new:
                    new.append(w)
                    parent[w] = a
        if not new:
            break
        nodes.extend(new)

    # The borrowed edges.  AUDIT FIX (2026-08-28, from the cold attack report):
    # the gate-mate spawns ONE child per demand, so all borrowers of a group
    # must be redirected to THAT target.  The earlier version reselected per
    # borrower, which both invented targets outside `nodes` (silently dropped by
    # `declared_cycle`) and gave a single group several children -- so its cycle
    # counts were an UNDERCOUNT.  In `agree` mode the one child is chosen
    # GROUP-AWARE, which is the freedom the construction actually has.
    g = set(gated())
    first_of_type = {}
    for n in nodes:
        first_of_type.setdefault(T(n), n)
    groups = {}
    for v in nodes:
        if v in g:
            continue
        a = first_of_type[T(v)]
        pd = persist_ds(model, val, a, cl)
        for d in T(v):
            if d[0] != "ex" or d[1] != PP:
                continue
            if d[2] in pd:
                continue
            groups.setdefault((a, d[2]), []).append(v)
    for (a, D), vs in groups.items():
        if mode == "agree":
            z = witness(a, PP, D, set(), above=vs)
        else:
            z = child.get((a, D))
            if z is None:
                z = witness(a, PP, D, set(anc_types(a) + [T(a)]))
        if z is None:
            continue
        if z not in nodes:
            nodes.append(z)                      # counted, never dropped
        for v in vs:
            borrowed.append((v, z, D, a))
    return nodes, borrowed, parent


def declared_cycle(nodes, borrowed):
    """Declared order = model PP among nodes, PLUS borrowed edges.  Returns the
    number of nodes lying on a cycle of the transitive closure."""
    idx = {n: i for i, n in enumerate(nodes)}
    N = len(nodes)
    adj = [[False] * N for _ in range(N)]
    for x in nodes:
        for y in nodes:
            if x is not y and rel(x, y) == PP:
                adj[idx[x]][idx[y]] = True
    for (v, z, _D, _a) in borrowed:
        if v in idx and z in idx:
            adj[idx[v]][idx[z]] = True
    for k in range(N):
        for i in range(N):
            if adj[i][k]:
                for j in range(N):
                    if adj[k][j]:
                        adj[i][j] = True
    return sum(1 for i in range(N) if adj[i][i])


# --------------------------------------------------------------------- parts

CLASSES = [
    ("random |U|=4", model_random, {"usize": 4}, 0.0),
    ("random |U|=5", model_random, {"usize": 5}, 0.30),
    ("nested chain |U|=6, periodic val", model_chain, {"usize": 6}, 0.55),
    ("nested chain |U|=8, periodic val", model_chain, {"usize": 8}, 0.65),
]


def n_ex(c):
    return sum(1 for d in closure(c) if d[0] == "ex")


def sample(rng, maker, kw, vert, want, cap=60000):
    """Conditioned sampling: keep only instances that actually EXERCISE the
    borrowed edge.  wp130's rule -- a rate on a sample that barely contains the
    property under test is indistinguishable from a finding.  `seen` records how
    many raw instances were needed, so the retention rate is reportable."""
    out, seen = [], 0
    for _ in range(cap):
        if len(out) >= want:
            break
        c0 = rand_concept(rng, rng.randint(3, 4), vertical=vert)
        if not po_free(c0) or n_ex(c0) < 2:
            continue
        got = find_model(rng, c0, maker, **kw)
        if got is None:
            continue
        seen += 1
        m, val, root = got
        _n, b, _p = extract(m, val, c0, root)
        if not b:
            continue
        out.append((c0, got))
    return out, seen


def part_n(samples):
    print("PART N -- is the sample NON-VACUOUS?  (wp130's rule: count the thing")
    print("          being tested before believing any rate about it)")
    print(f"  {'model class':34s} {'inst':>5} {'mean nodes':>11} "
          f"{'mean blocked':>13} {'mean borrowed':>14}")
    ok = False
    for name, data in samples:
        if not data:
            print(f"  {name:34s} {'0':>5}   (no satisfiable instances)")
            continue
        tn = tb = tw = 0
        for c0, (m, val, root) in data:
            nodes, borrowed, _ = extract(m, val, c0, root)
            cl = closure(c0)
            seen, ng = set(), 0
            for n in nodes:
                t = mty(m, val, n, cl)
                if t in seen:
                    ng += 1
                else:
                    seen.add(t)
            tn += len(nodes)
            tb += ng
            tw += len(borrowed)
        k = len(data)
        print(f"  {name:34s} {k:5d} {tn / k:11.2f} {tb / k:13.2f} "
              f"{tw / k:14.2f}")
        if tw / k >= 0.5:
            ok = True
    print("  => at least one class must average >= 0.5 borrowed edges per")
    print("     instance, else every rate below is measuring emptiness.")
    return ok


def part_b(samples):
    print("\nPART B -- the DICHOTOMY as a transcription regression")
    print("          (certified: bad case => a < v in the model).  EXPECT 100%.")
    tot = bad = miss = 0
    for _name, data in samples:
        for c0, (m, val, root) in data:
            _nodes, borrowed, _ = extract(m, val, c0, root)
            for (v, z, _D, a) in borrowed:
                tot += 1
                if rel(z, v) == PP:
                    bad += 1
                    if rel(a, v) != PP:
                        miss += 1
    print(f"  borrowed edges examined            : {tot}")
    print(f"  of those, target already below v   : {bad}")
    print(f"  dichotomy violations (must be 0)   : {miss}")
    print(f"  agreement                          : "
          f"{100.0 if bad == 0 else 100.0 * (bad - miss) / bad:.1f}%")
    return miss == 0


def part_d(samples):
    print("\nPART D -- does the declared order stay ACYCLIC?")
    print("  D0 = control, NO gating (declared order = model order): expect 0")
    print("  D1 = treatment, gating + borrowed edges")
    print(f"  {'model class':34s} {'inst':>5} {'D0 cyc':>7} {'D1 cyc':>7} "
          f"{'D1 rate':>9}")
    ctrl_ok = True
    any_cycle = False
    rows = []
    for name, data in samples:
        if not data:
            continue
        c0cyc = c1cyc = 0
        for c0, (m, val, root) in data:
            n0, b0, _ = extract(m, val, c0, root, gate=False)
            if declared_cycle(n0, b0):
                c0cyc += 1
            n1, b1, _ = extract(m, val, c0, root, gate=True)
            if declared_cycle(n1, b1):
                c1cyc += 1
        k = len(data)
        rows.append((name, k, c0cyc, c1cyc))
        print(f"  {name:34s} {k:5d} {c0cyc:7d} {c1cyc:7d} "
              f"{100.0 * c1cyc / k:8.1f}%")
        if c0cyc:
            ctrl_ok = False
        if c1cyc:
            any_cycle = True
    if not ctrl_ok:
        print("  !! CONTROL FAILED -- the harness is wrong, treatment withheld")
    return ctrl_ok, any_cycle, rows


def part_c(samples, any_cycle):
    print("\nPART C -- does REPEAT-FREE witness selection remove the cycles?")
    if not any_cycle:
        print("  (part D found no cycles to remove -- nothing to measure)")
        return True
    print(f"  {'model class':34s} {'inst':>5} {'greedy':>7} {'rep-free':>9} "
          f"{'removed':>9}")
    allgone = True
    for name, data in samples:
        if not data:
            continue
        g = rf = 0
        for c0, (m, val, root) in data:
            n1, b1, _ = extract(m, val, c0, root, repeat_free=False)
            if declared_cycle(n1, b1):
                g += 1
            n2, b2, _ = extract(m, val, c0, root, repeat_free=True)
            if declared_cycle(n2, b2):
                rf += 1
        pct = 100.0 * (g - rf) / g if g else 100.0
        print(f"  {name:34s} {len(data):5d} {g:7d} {rf:9d} {pct:8.1f}%")
        if rf:
            allgone = False
    return allgone


def part_e(samples):
    print("\nPART E -- how often is a MODEL-AGREEING witness available?")
    print("  i.e. among the gate-mate's witnesses for the demand, is there one")
    print("  the model already places PP-ABOVE the blocked node?  If so the")
    print("  declared edge agrees with the model and CANNOT create a cycle.")
    print(f"  {'model class':34s} {'edges':>7} {'agreeing':>9} {'rate':>8}")
    for name, data in samples:
        if not data:
            continue
        tot = ag = 0
        for c0, (m, val, root) in data:
            nodes, borrowed, _ = extract(m, val, c0, root)
            cl = closure(c0)
            for (v, z, D, a) in borrowed:
                tot += 1
                if any(rel(a, y) == PP and rel(v, y) == PP
                       and sat(m, val, y, D) for y in m):
                    ag += 1
        pct = 100.0 * ag / tot if tot else 0.0
        print(f"  {name:34s} {tot:7d} {ag:9d} {pct:7.1f}%")
    return True


def part_f(samples):
    print("\nPART F -- cycles under the THREE selection rules")
    print(f"  {'model class':34s} {'inst':>5} {'greedy':>7} {'rep-free':>9} "
          f"{'agree':>7}")
    gone = True
    for name, data in samples:
        if not data:
            continue
        g = rf = ag = 0
        for c0, (m, val, root) in data:
            n1, b1, _ = extract(m, val, c0, root, repeat_free=False)
            if declared_cycle(n1, b1):
                g += 1
            n2, b2, _ = extract(m, val, c0, root, repeat_free=True)
            if declared_cycle(n2, b2):
                rf += 1
            n3, b3, _ = extract(m, val, c0, root, repeat_free=True,
                                mode="agree")
            if declared_cycle(n3, b3):
                ag += 1
        print(f"  {name:34s} {len(data):5d} {g:7d} {rf:9d} {ag:7d}")
        if ag:
            gone = False
    return gone


def part_q(samples):
    """Q1/Q2/Q3 -- the questions that located the residue.

    Q1  when greedy would cycle, is an AGREEING witness available?  (This is now
        the certified `agreeing_witness_exists`, so 100% is forced; it is kept as
        a transcription regression.)
    Q2  can ONE witness of the gate-mate serve ALL blocked nodes sharing it?
        (`a` spawns one child per demand, so this is what the construction needs.)
    Q3  when Q2 fails, WHY?  Are the group members pairwise comparable (then
        `common_upper_on_tower` applies), and does the MODEL contain a common
        ORDER-upper (ignoring the demand)?  The D-carrying version of that
        question IS Q2, so asking it again here would be tautological.
    """
    print("\nPART Q -- locating the residue")
    print(f"  {'model class':34s} {'Q1 avail':>9} {'Q2 grp ok':>10} "
          f"{'Q3 comparable':>14} {'Q3 has upper':>13}")
    T = [0, 0, 0, 0, 0, 0]
    for name, data in samples:
        if not data:
            continue
        bad = av = grp = ok = fcmp = fup = 0
        for c0, (m, val, root) in data:
            _nodes, borrowed, _ = extract(m, val, c0, root)
            for (v, z, D, a) in borrowed:
                if rel(z, v) == PP or z == v:
                    bad += 1
                    if any(rel(a, y) == PP and rel(v, y) == PP
                           and sat(m, val, y, D) for y in m):
                        av += 1
            groups = {}
            for (v, _z, D, a) in borrowed:
                groups.setdefault((a, D), []).append(v)
            for (a, D), vs in groups.items():
                grp += 1
                cands = [y for y in m
                         if rel(a, y) == PP and sat(m, val, y, D)]
                if any(all(rel(vv, y) == PP for vv in vs) for y in cands):
                    ok += 1
                    continue
                g = list(dict.fromkeys(vs + [a]))
                if all(rel(p, q) in (PP, PPI, EQ) for p in g for q in g):
                    fcmp += 1
                # AUDIT FIX (2026-08-28): this previously repeated Q2's own
                # predicate (upper AND carrying D) after Q2 had failed, so its
                # 0/140 was forced by program structure.  The D-test is dropped:
                # the question is now whether a common ORDER-upper exists at all.
                if any(all(rel(p, y) == PP for p in g) for y in m):
                    fup += 1
        f = len(g) if False else (grp - ok)
        pc = lambda x, n: (100.0 * x / n) if n else float("nan")
        print(f"  {name:34s} {pc(av, bad):8.1f}% {pc(ok, grp):9.1f}% "
              f"{pc(fcmp, f):13.1f}% {pc(fup, f):12.1f}%")
        T = [T[0] + bad, T[1] + av, T[2] + grp, T[3] + ok, T[4] + fcmp,
             T[5] + fup]
    print(f"  TOTALS: Q1 {T[1]}/{T[0]}   Q2 {T[3]}/{T[2]}   "
          f"Q3 comparable {T[4]}/{T[2] - T[3]}   has-upper {T[5]}/{T[2] - T[3]}")
    print("  => Q1 = 100% is FORCED (certified).  Q2 < 100% is THE RESIDUE.")
    print("     Q3 'has upper' now asks about a common ORDER-upper only (no D):")
    print("     a nonzero reading means such groups DO have an upper, but none")
    print("     of their uppers carries the demand -- which is what Q2 failing")
    print("     already says.  The obstruction is model-level either way.")
    return T


def part_g(samples):
    """The honest residue: `agree` cannot always apply.  Count the instances
    where it FAILS on at least one edge, and check those specifically."""
    print("\nPART G -- the residue: instances where AGREEMENT IS UNAVAILABLE")
    print(f"  {'model class':34s} {'inst':>5} {'fallback':>9} {'cycled':>8}")
    tot_fb = tot_cy = 0
    for name, data in samples:
        if not data:
            continue
        fb = cy = 0
        for c0, (m, val, root) in data:
            nodes, borrowed, _ = extract(m, val, c0, root)
            used = False
            for (v, z, D, a) in borrowed:
                if not any(rel(a, y) == PP and rel(v, y) == PP
                           and sat(m, val, y, D) for y in m):
                    used = True
                    break
            if not used:
                continue
            fb += 1
            n3, b3, _ = extract(m, val, c0, root, repeat_free=True,
                                mode="agree")
            if declared_cycle(n3, b3):
                cy += 1
        tot_fb += fb
        tot_cy += cy
        print(f"  {name:34s} {len(data):5d} {fb:9d} {cy:8d}")
    print(f"  => {tot_fb} instances genuinely needed the fallback; "
          f"{tot_cy} cycled.")
    print("     A 0 here is EVIDENCE, not a theorem: the fallback is still")
    print("     unanalysed, and this is a finite randomized sweep.")
    return tot_fb, tot_cy


def main(seed=20260827):
    rng = random.Random(seed)
    samples, retention = [], {}
    for (name, mk, kw, v) in CLASSES:
        data, seen = sample(rng, mk, kw, v, 260)
        samples.append((name, data))
        retention[name] = (len(data), seen)
    print("SAMPLING -- conditioned on producing at least one borrowed edge")
    for name, (k, seen) in retention.items():
        pct = 100.0 * k / seen if seen else 0.0
        print(f"  {name:34s} kept {k:4d} of {seen:6d} satisfiable "
              f"({pct:4.1f}%)")
    print()
    nonvac = part_n(samples)
    b = part_b(samples)
    ctrl_ok, any_cycle, _rows = part_d(samples)
    c = part_c(samples, any_cycle) if ctrl_ok else None
    part_e(samples)
    f = part_f(samples) if ctrl_ok else None
    fb, fcy = part_g(samples) if ctrl_ok else (0, 0)
    if ctrl_ok:
        part_q(samples)

    print("\n" + "=" * 72)
    print(f"  N non-vacuous sample     : {'YES' if nonvac else 'NO'}")
    print(f"  B dichotomy (expect 100%): {'PASS' if b else 'FAIL'}")
    print(f"  D control (expect 0 cyc) : {'PASS' if ctrl_ok else 'FAIL'}")
    print(f"  D treatment has cycles   : {'YES' if any_cycle else 'NO'}")
    if ctrl_ok:
        print(f"  C repeat-free removes all: "
              f"{'YES' if c else 'NO'}")
        print(f"  F agree-rule removes all : {'YES' if f else 'NO'}")
        print(f"  G fallback used / cycled : {fb} / {fcy}")
    print("=" * 72)
    if not nonvac:
        print("VERDICT: VACUOUS -- reweight the generator before reading rates.")
        return 1
    if not b or not ctrl_ok:
        print("VERDICT: HARNESS FAULT -- fix before drawing conclusions.")
        return 1
    if not any_cycle:
        print("VERDICT: no cycle found in this sweep.  Evidence FOR the")
        print("  acyclicity claim, NOT a proof -- and see part N for how hard")
        print("  the sample actually pushed on it.")
        return 0
    if f:
        print("VERDICT: cycles DO arise under greedy witness selection, and")
        print("  repeat-freeness does NOT remove them all -- but preferring a")
        print("  MODEL-AGREEING witness does, in this sweep.  That points the")
        print("  sec.254 discipline at agreement rather than repeat-freeness.")
        return 0
    if c:
        print("VERDICT: cycles DO arise under greedy witness selection, and")
        print("  repeat-free selection removes them ALL in this sweep.  That is")
        print("  evidence the sec.254 route is the right one -- the residue is")
        print("  exactly the step graph needed to enforce repeat-freeness.")
        return 0
    print("VERDICT: cycles arise AND survive repeat-free selection.  The")
    print("  sec.254 route as stated is NOT sufficient; the borrowed-edge")
    print("  discipline needs more than repeat-free chains.")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
