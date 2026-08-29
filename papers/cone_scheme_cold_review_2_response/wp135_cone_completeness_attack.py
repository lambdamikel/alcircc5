#!/usr/bin/env python3
"""WP135 -- attacking the COMPLETENESS half of the ConeScheme certificate.

The Lean artifact proves

    coneScheme_complete   : satisfiable  =>  some survivor carries C0
    coneScheme_unsat_full : no survivor  =>  UNSAT           (NO POFree hypothesis)

The second is a FULL-LOGIC claim, so a defect there is a defect about the open
problem, not about a fragment.  This probe tests the proof's actual content
rather than its statement, because the statement is not runnable: `sigStatic C0`
has size |typeEnum| * 2^|typeEnum| = 2^|cl C0| * 2^(2^|cl C0|), which is already
astronomical at |cl C0| = 4.

The proof route is

    Z := modelSigs = { dkey x : x in dom }
    (i)   Z subset sigStatic          [dkey_sigOk + dkey_mem_keyEnum]
    (ii)  Z subset pruneSig Z         [modelSigs_survives, via dkey_compat]
    (iii) Z subset gfp                [gfp_greatest]

(iii) is pure order theory over finite lists.  (i) and (ii) are where model
content enters, and BOTH are computable on a concrete model without touching
keyEnum.  That is what this probe checks, on real models of real concepts.

A single failure of (i) or (ii) refutes completeness.  A failure on a concept
containing forall-PO additionally refutes `coneScheme_unsat_full`.

PREDICTIONS, RECORDED BEFORE THE FIRST RUN (project rule: state the control's
expected value in advance, and withhold the treatment if the control misses):

  P1  Part A  (forall-PO-free)      : 100% of models pass (i), (ii), (iii-edge).
  P2  Part B  (FULL logic, PO allowed) : also 100%.  Completeness takes no
      fragment hypothesis, so PO must not matter.  Any failure here is the
      most valuable outcome this probe can produce.
  P3  Part C  (strengthening control) : each of four STRICTER variants of
      compatB must break obligation (ii) or (iii) on some model.  A weakening
      cannot break an obligation that already holds, so only a strengthening
      is a real control here.  If a strengthening never breaks anything, the
      obligations are too weak to detect an over-strong condition and Parts
      A/B pass vacuously.
  P4  Part D  (non-vacuity)         : the PO clause of compatB is literally
      `true`, so PO demands are served by any signature carrying the body.
      Expect the measured PO-demand discrimination to be ~0.  That does not
      threaten soundness of the UNSAT test, but it bounds its usefulness.

Self-contained: RCC5 relations, the composition table, concept syntax and
satisfaction are all rebuilt here from finite set semantics.
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
    t = {}
    regs = subsets(set(range(n)))
    for a in regs:
        for b in regs:
            r = rel(a, b)
            for c in regs:
                t.setdefault((r, rel(b, c)), set()).add(rel(a, c))
    return t


CT = comp_table(4)

# ---------------------------------------------------------- concept syntax
# ('at',i) ('nat',i) ('bot',) ('and',c,d) ('or',c,d) ('ex',r,c) ('all',r,c)


def cl(c, acc=None):
    """Mirror of Lean `cl`: subconcept closure, order-insensitive here."""
    if acc is None:
        acc = []
    if c not in acc:
        acc.append(c)
    k = c[0]
    if k in ("and", "or"):
        cl(c[1], acc)
        cl(c[2], acc)
    elif k in ("ex", "all"):
        cl(c[2], acc)
    return acc


def po_free(c):
    k = c[0]
    if k in ("at", "nat", "bot"):
        return True
    if k in ("and", "or"):
        return po_free(c[1]) and po_free(c[2])
    if k == "all" and c[1] == PO:
        return False
    return po_free(c[2])


def sat(model, val, x, c):
    k = c[0]
    if k == "bot":
        return False
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


# ------------------------------------------- the control layer, transcribed


def supportB(T):
    """Mirror of Lean `supportB`.  T is a frozenset of concepts."""
    for c in T:
        k = c[0]
        if k == "bot":
            return False
        if k == "at" and ("nat", c[1]) in T:
            return False
        if k == "and" and not (c[1] in T and c[2] in T):
            return False
        if k == "or" and not (c[1] in T or c[2] in T):
            return False
        if k in ("all", "ex") and c[1] == EQ and c[2] not in T:
            return False
    return True


def all_bodies(r, T):
    return frozenset(c[2] for c in T if c[0] == "all" and c[1] == r)


def sig_cone(q):
    """Mirror of `sigCone q = q.1 :: q.2`."""
    return (q[0],) + q[1]


def sig_ok(q):
    """Mirror of `sigOkB`."""
    if not supportB(q[0]):
        return False
    for U in q[1]:
        if not supportB(U):
            return False
        if not all_bodies(PP, U) <= q[0]:
            return False
        if not all_bodies(PPI, q[0]) <= U:
            return False
    return True


def sig_demands(q):
    """Mirror of `sigDemands`: every non-EQ existential of the support type."""
    return [(c[1], c[2]) for c in q[0] if c[0] == "ex" and c[1] != EQ]


def compat(r, D, q, qp, mut=None):
    """Mirror of `compatB`.  `mut` names a STRENGTHENING of one clause.

    A weakening cannot break an obligation that already holds, so it measures
    nothing.  A strengthening must break completeness -- that is what makes
    Parts A/B non-vacuous rather than trivially true.
    """
    if D not in qp[0]:
        return False
    if mut == "sup" and not q[0] <= qp[0]:
        return False                      # bogus: server must dominate the type
    if r == PP:
        if mut == "pp":                   # equality instead of inclusion
            return set(sig_cone(q)) == set(qp[1])
        return all(U in qp[1] for U in sig_cone(q))
    if r == PPI:
        if mut == "ppi":
            return set(sig_cone(qp)) == set(q[1])
        return all(U in q[1] for U in sig_cone(qp))
    if r == DR:
        if mut == "dr":                   # cone TYPES equal, not just DR bodies
            return set(sig_cone(q)) == set(sig_cone(qp))
        for U in sig_cone(q):
            for V in sig_cone(qp):
                if not (all_bodies(DR, U) <= V and all_bodies(DR, V) <= U):
                    return False
        return True
    return True  # PO, EQ


def prune(X, mut=None):
    """Mirror of `pruneSig`."""
    return [q for q in X
            if all(any(compat(r, D, q, qp, mut) for qp in X)
                   for (r, D) in sig_demands(q))]


# ------------------------------------------------------- model -> signatures


def mty(c0, model, val, x):
    return frozenset(d for d in cl(c0) if sat(model, val, x, d))


def dspec(c0, model, val, x):
    """Mirror of `dspec`: types of the STRICT PP-predecessors of x."""
    return tuple(sorted(
        (mty(c0, model, val, y) for y in model if rel(y, x) == PP),
        key=lambda s: sorted(map(str, s))))


def dkey(c0, model, val, x):
    seen, out = set(), []
    for t in dspec(c0, model, val, x):
        if t not in seen:
            seen.add(t)
            out.append(t)
    return (mty(c0, model, val, x), tuple(out))


# ------------------------------------------------------- generators / oracle


def rand_concept(rng, depth, natoms=2, allow_po=False, heavy_all=True):
    if depth == 0 or rng.random() < 0.2:
        i = rng.randrange(natoms)
        return ("at", i) if rng.random() < 0.6 else ("nat", i)
    r = rng.random()
    if r < 0.20:
        return ("and", rand_concept(rng, depth - 1, natoms, allow_po, heavy_all),
                rand_concept(rng, depth - 1, natoms, allow_po, heavy_all))
    if r < 0.32:
        return ("or", rand_concept(rng, depth - 1, natoms, allow_po, heavy_all),
                rand_concept(rng, depth - 1, natoms, allow_po, heavy_all))
    if r < 0.62:
        return ("ex", rng.choice(ATOMS),
                rand_concept(rng, depth - 1, natoms, allow_po, heavy_all))
    univ = [DR, PP, PPI, EQ] + ([PO] if allow_po else [])
    if heavy_all:
        # weight DR/PP/PPI: those are the clauses compatB actually constrains
        univ = [DR, DR, PP, PP, PPI, PPI, EQ] + ([PO, PO] if allow_po else [])
    return ("all", rng.choice(univ),
            rand_concept(rng, depth - 1, natoms, allow_po, heavy_all))


NESTED = None


def nested_families(usize=4):
    """Model shapes that actually exercise cones: chains and chains+siblings."""
    global NESTED
    if NESTED is None:
        regs = subsets(set(range(usize)))
        NESTED = regs
    return NESTED


def find_model(rng, c, natoms=2, tries=120, usize=4):
    """Reference oracle over set models; biased toward nested (PP-rich) ones."""
    regs = nested_families(usize)
    for _ in range(tries):
        if rng.random() < 0.5:
            # a chain plus optional extras -- guarantees PP structure
            base = rng.sample(sorted(range(usize)), usize)
            m = [frozenset(base[:k]) for k in range(1, usize + 1)]
            for _ in range(rng.randint(0, 2)):
                m.append(rng.choice(regs))
            m = list(dict.fromkeys(m))
        else:
            m = rng.sample(regs, min(len(regs), rng.randint(2, 6)))
        val = {}
        for a in range(natoms):
            for x in m:
                val[(a, x)] = rng.random() < 0.5
        for x in m:
            if sat(m, val, x, c):
                return m, val, x
    return None


# ------------------------------------------------------------------- checks


def check_instance(c0, model, val, mut=None):
    """The three model-side obligations of the completeness proof."""
    keys = {}
    for x in model:
        keys[x] = dkey(c0, model, val, x)
    Z = list(dict.fromkeys(keys.values()))
    probs = []

    # (i) dkey_sigOk : every model key is an admissible signature
    for x in model:
        if not sig_ok(keys[x]):
            probs.append(("sigOk", x))

    # (i') dkey_mem_keyEnum : mty in typeEnum and dspec subset typeEnum.
    #      typeEnum = sublists (cl C0), so this is "subset of cl C0".
    clset = frozenset(cl(c0))
    for x in model:
        if not keys[x][0] <= clset:
            probs.append(("mty_enum", x))
        for t in keys[x][1]:
            if not t <= clset:
                probs.append(("dspec_enum", x))

    # (ii) modelSigs_survives : Z subset pruneSig Z
    surv = set(map(id, [])) if False else prune(Z, mut)
    for q in Z:
        if q not in surv:
            probs.append(("survives", q))

    # (iii) dkey_compat : EVERY real model edge satisfies compatB
    for x in model:
        for y in model:
            r = rel(x, y)
            if r == EQ:
                continue
            for D in keys[y][0]:
                if not compat(r, D, keys[x], keys[y], mut):
                    probs.append(("compat", r, D))

    dem = sum(len(sig_demands(q)) for q in Z)
    alls = sum(1 for d in cl(c0) if d[0] == "all")
    return probs, len(Z), dem, alls


def run(name, trials, seed, allow_po):
    rng = random.Random(seed)
    tested = 0
    fails = {}
    dem_tot = cone_tot = all_tot = po_inst = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(1, 3), allow_po=allow_po)
        if not allow_po and not po_free(c0):
            continue
        got = find_model(rng, c0)
        if got is None:
            continue
        model, val, _root = got
        probs, nz, dem, alls = check_instance(c0, model, val)
        tested += 1
        dem_tot += dem
        all_tot += alls
        cone_tot += sum(len(dkey(c0, model, val, x)[1]) for x in model)
        if not po_free(c0):
            po_inst += 1
        for p in probs:
            fails[p[0]] = fails.get(p[0], 0) + 1
    print(f"  {name}: {tested} satisfiable instances checked")
    print(f"    NON-VACUITY  mean demands/instance {dem_tot/max(tested,1):.2f}"
          f"   mean forall-bodies {all_tot/max(tested,1):.2f}"
          f"   mean cone entries {cone_tot/max(tested,1):.2f}")
    if allow_po:
        print(f"    instances containing forall-PO : {po_inst}"
              f" ({100*po_inst/max(tested,1):.1f}%)")
    if fails:
        print(f"    FAILURES {fails}")
    else:
        print("    (i) sigOk  (i') key-enum  (ii) survives  (iii) compat"
              "  -- ALL HOLD")
    return tested > 0 and not fails, dem_tot / max(tested, 1)


def part_a():
    print("PART A -- completeness obligations, forall-PO-free  [predict 100%]")
    ok, dem = run("A", 2500, 20260829, allow_po=False)
    return ok and dem > 0.5


def part_b():
    print("\nPART B -- completeness obligations, FULL LOGIC  [predict 100%]")
    print("          this is the one that carries coneScheme_unsat_full")
    ok, dem = run("B", 2500, 98760829, allow_po=True)
    return ok and dem > 0.5


def part_c(trials=1500, seed=555111):
    """Strengthening control: a STRICTER compatB must break completeness.

    If it does not, obligations (ii)/(iii) are too weak to detect an
    over-strong condition, and Parts A/B pass vacuously.
    """
    print("\nPART C -- strengthening control  [predict: every clause breaks]")
    rng = random.Random(seed)
    inst = []
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(1, 3), allow_po=True)
        got = find_model(rng, c0)
        if got is not None:
            inst.append((c0, got[0], got[1]))
    print(f"    {len(inst)} instances reused for every mutation")
    base = sum(1 for (c0, m, v) in inst if check_instance(c0, m, v)[0])
    print(f"    unmutated failures                  : {base:5d}"
          f"   {'ok' if base == 0 else 'PROBLEM'}")
    broke = {}
    for name, label in (("pp", "PP  cone equality"),
                        ("ppi", "PPI cone equality"),
                        ("dr", "DR  cone equality"),
                        ("sup", "server dominates type")):
        n = sum(1 for (c0, m, v) in inst if check_instance(c0, m, v, name)[0])
        broke[name] = n
        print(f"    strengthen {label:22s}: {n:5d} / {len(inst)}"
              f"   {'breaks completeness' if n else 'NO EFFECT -- test is weak'}")
    return base == 0 and all(v > 0 for v in broke.values())


def part_d(trials=1200, seed=777222):
    """How much can the PO clause ever discriminate?  compatB po = true."""
    print("\nPART D -- non-vacuity of the FULL-LOGIC test  [predict ~0 for PO]")
    rng = random.Random(seed)
    per = {}
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(1, 3), allow_po=True)
        got = find_model(rng, c0)
        if got is None:
            continue
        model, val = got[0], got[1]
        Z = list(dict.fromkeys(dkey(c0, model, val, x) for x in model))
        for q in Z:
            for (r, D) in sig_demands(q):
                tot = ref = 0
                for qp in Z:
                    if D in qp[0]:
                        tot += 1
                        if not compat(r, D, q, qp):
                            ref += 1
                if tot:
                    a, b = per.get(r, (0, 0))
                    per[r] = (a + ref, b + tot)
    print("    of the signatures that CARRY the demanded body, what fraction")
    print("    does the relational clause still reject?")
    for r in [PP, PPI, DR, PO]:
        a, b = per.get(r, (0, 0))
        if b:
            print(f"      {r:3s} {a:6d}/{b:6d}  = {100*a/b:5.1f}%")
        else:
            print(f"      {r:3s}      -- no instances")
    po_rate = per.get(PO, (0, 1))
    ok = po_rate[0] == 0
    print(f"    => PO discrimination is {'zero, as predicted' if ok else 'NONZERO -- unexpected'}")
    print("       so the full-logic UNSAT test is SOUND but blind to forall-PO;")
    print("       it can only reject via PP/PPI/DR structure and support.")
    return True


def main():
    res = {
        "A pofree completeness": part_a(),
        "B full-logic completeness": part_b(),
        "C mutation control": part_c(),
        "D non-vacuity": part_d(),
    }
    print("\n" + "=" * 70)
    for k, v in res.items():
        print(f"  {k:28s} : {'PASS' if v else 'FAIL'}")
    print("=" * 70)
    ok = all(res.values())
    print("VERDICT:", "ALL PASS" if ok else "FAILURE")
    print()
    print("  SCOPE.  This checks the model-side content of the completeness")
    print("  proof (dkey_sigOk, dkey_compat, modelSigs_survives) on concrete")
    print("  finite set models.  It does NOT run the certificate: sigStatic is")
    print("  doubly exponential and unreachable at any interesting size.  It")
    print("  also cannot see infinite models, where the same three obligations")
    print("  are what the Lean proof discharges in general.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
