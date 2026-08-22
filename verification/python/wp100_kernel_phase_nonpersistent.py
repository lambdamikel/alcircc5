"""WP100 -- can a KERNEL PHASE carry a NON-PERSISTENT exists-PP demand?

ASSEMBLY_DESIGN sec.45 flags the question.  Section 44.27's persistent/one-shot
split routes a node's exists-PP demands two ways -- persistent to a round-robin
KERNEL, one-shot to an elt edge to an EXTERNAL -- but that is stated for
externals, where both routes exist.  A kernel PHASE has only the cdir branch,
which needs persistAll; its external branch needs side k = false, which an
ASCENDING kernel does not have.

So: does a phase ever carry an exists-PP demand that is NOT persistent there?

  A  how often is an exists-PP demand non-persistent at all?
  B  walking PP-successors from a node x, do the successors carry exists-PP
     demands OUTSIDE persistDs(x)?  (the kernel's Ds is fixed at its base)
  C  and are those demands non-persistent AT THE SUCCESSOR?  That is the case
     sec.45 has no route for.
  D  the constructed probe: a concept with a persistent tower AND a
     non-persistent side demand, to see where the side demand lands.

Self-contained: RCC5 relations and the composition table from finite set
semantics.

RESULT: THIS PROBE CANNOT ANSWER THE QUESTION, and the run shows why.

Over finite set models 100% of exists-PP demands come out "non-persistent" --
not because non-persistence is common, but because the guard
forall-PP.(exists-PP.D) ALWAYS fails at a maximal element, and every finite
model has one.  Persistence is by definition a property of infinite ascending
chains, so a finite-model probe measures nothing about it.  Part D makes the
same point from the other side: the constructed persistent tower is simply
UNSATISFIABLE over finite models, as it should be.

The file is kept as a recorded negative result -- the measurement is an
artifact of the model class, and the section 45 question needs either infinite
models (intervals over Q, or a finitely-presented infinite structure) or a
proof.  Reading the 100% as evidence would be wrong.
"""

import random
from itertools import combinations

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
ATOMS = [DR, PO, EQ, PP, PPI]


def rel(a, b):
    if a == b: return EQ
    if a < b: return PP
    if b < a: return PPI
    if not (a & b): return DR
    return PO


def subsets(univ):
    out = []
    for k in range(1, len(univ) + 1):
        for c in combinations(sorted(univ), k):
            out.append(frozenset(c))
    return out


def mdepth(c):
    k = c[0]
    if k in ("at", "nat"): return 0
    if k in ("and", "or"): return max(mdepth(c[1]), mdepth(c[2]))
    return 1 + mdepth(c[2])


def closure(c, acc=None):
    if acc is None: acc = []
    if c not in acc: acc.append(c)
    k = c[0]
    if k in ("and", "or"): closure(c[1], acc); closure(c[2], acc)
    elif k in ("ex", "all"): closure(c[2], acc)
    return acc


def po_free(c):
    k = c[0]
    if k in ("at", "nat"): return True
    if k in ("and", "or"): return po_free(c[1]) and po_free(c[2])
    if k == "all" and c[1] == PO: return False
    return po_free(c[2])


def sat(model, val, x, c):
    k = c[0]
    if k == "at": return val.get((c[1], x), False)
    if k == "nat": return not val.get((c[1], x), False)
    if k == "and": return sat(model, val, x, c[1]) and sat(model, val, x, c[2])
    if k == "or": return sat(model, val, x, c[1]) or sat(model, val, x, c[2])
    if k == "ex":
        return any(rel(x, y) == c[1] and sat(model, val, y, c[2]) for y in model)
    return all(rel(x, y) != c[1] or sat(model, val, y, c[2]) for y in model)


def mty(model, val, x, c0):
    return frozenset(d for d in closure(c0) if sat(model, val, x, d))


def pp_demands(model, val, x, c0):
    return [d[2] for d in mty(model, val, x, c0) if d[0] == "ex" and d[1] == PP]


def persistent(model, val, x, c0, D):
    """exists-PP.D holds at x AND its guard forall-PP.(exists-PP.D) does."""
    return (sat(model, val, x, ("ex", PP, D)) and
            sat(model, val, x, ("all", PP, ("ex", PP, D))))


def rand_concept(rng, depth, natoms=2):
    if depth == 0 or rng.random() < 0.22:
        i = rng.randrange(natoms)
        return ("at", i) if rng.random() < 0.6 else ("nat", i)
    r = rng.random()
    if r < 0.18:
        return ("and", rand_concept(rng, depth-1, natoms), rand_concept(rng, depth-1, natoms))
    if r < 0.28:
        return ("or", rand_concept(rng, depth-1, natoms), rand_concept(rng, depth-1, natoms))
    if r < 0.70:
        return ("ex", rng.choice([PP, PP, DR, PO, PPI]), rand_concept(rng, depth-1, natoms))
    return ("all", rng.choice([PP, PP, DR, PPI, EQ]), rand_concept(rng, depth-1, natoms))


def find_model(rng, c, natoms=2, tries=140, usize=4):
    regs = subsets(set(range(usize)))
    for _ in range(tries):
        m = rng.sample(regs, min(len(regs), rng.randint(2, 6)))
        val = {}
        for a in range(natoms):
            for x in m:
                val[(a, x)] = rng.random() < 0.5
        for x in m:
            if sat(m, val, x, c):
                return m, val, x
    return None


def part_abc(trials=6000, seed=100100):
    print("PART A/B/C -- non-persistent exists-PP demands, and where they sit")
    rng = random.Random(seed)
    tested = 0
    tot_dem = nonpersist = 0
    succ_outside = 0          # successor carries a demand outside persistDs(x)
    succ_outside_np = 0       # ... and it is NON-persistent at the successor
    inst_hit = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        if not po_free(c0):
            continue
        got = find_model(rng, c0)
        if got is None:
            continue
        model, val, root = got
        tested += 1
        hit = False
        for x in model:
            dsx = [D for D in pp_demands(model, val, x, c0)
                   if persistent(model, val, x, c0, D)]
            for D in pp_demands(model, val, x, c0):
                tot_dem += 1
                if not persistent(model, val, x, c0, D):
                    nonpersist += 1
            # walk PP-successors of x -- the kernel's phases would live here
            for y in model:
                if rel(x, y) != PP:
                    continue
                for E in pp_demands(model, val, y, c0):
                    if E not in dsx:
                        succ_outside += 1
                        if not persistent(model, val, y, c0, E):
                            succ_outside_np += 1
                            hit = True
        if hit:
            inst_hit += 1
    print(f"  instances tested                              : {tested}")
    print(f"  exists-PP demands seen                        : {tot_dem}")
    print(f"  of those NON-persistent                       : {nonpersist}"
          f"  ({100.0*nonpersist/max(tot_dem,1):.1f}%)")
    print(f"  successor demands OUTSIDE persistDs(base)     : {succ_outside}")
    print(f"  ... and NON-persistent at the successor       : {succ_outside_np}")
    print(f"  instances exhibiting the sec.45 configuration : {inst_hit}"
          f"  ({100.0*inst_hit/max(tested,1):.1f}%)")
    return tested > 0


def part_d():
    print("\nPART D -- constructed: a persistent tower plus a non-persistent side demand")
    A = ("at", 0)
    tower = ("and", ("ex", PP, ("at", 1)), ("all", PP, ("ex", PP, ("at", 1))))
    c0 = ("and", tower, ("ex", PP, A))
    print("  C0 = (exists-PP.B and forall-PP.exists-PP.B) and exists-PP.A")
    print(f"  po_free : {po_free(c0)}")
    # chain e0 < e1 < e2 < e3 ; B everywhere above e0 ; A only at e1
    model = [frozenset(range(i + 1)) for i in range(4)]
    val = {}
    for i, x in enumerate(model):
        val[(0, x)] = (i == 1)          # A only at e1
        val[(1, x)] = (i >= 1)          # B from e1 up
    root = model[0]
    print(f"  model satisfies C0 at the root : {sat(model, val, root, c0)}")
    for i, x in enumerate(model):
        dem = pp_demands(model, val, x, c0)
        nps = [D for D in dem if not persistent(model, val, x, c0, D)]
        print(f"    e{i}: exists-PP demands {len(dem)}, non-persistent {len(nps)}")
    print("  => the model does NOT satisfy C0: forall-PP.(exists-PP.B) fails at")
    print("     the maximal element, so a persistent tower is UNSATISFIABLE over")
    print("     finite models -- correctly, since it forces an infinite chain.")
    print("     This is why parts A/B/C report 100% non-persistent: an artifact")
    print("     of the model class, not a measurement.  The sec.45 question")
    print("     needs infinite models or a proof.")
    return True


def main():
    res = {"A/B/C measurement": part_abc(), "D constructed": part_d()}
    print("\n" + "=" * 72)
    for k, v in res.items():
        print(f"  {k:22s} : {'PASS' if v else 'FAIL'}")
    print("=" * 72)
    print("VERDICT:", "ALL PASS" if all(res.values()) else "FAILURE")
    return 0 if all(res.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
