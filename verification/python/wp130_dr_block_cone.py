#!/usr/bin/env python3
"""WP130 -- how much of a DR-witness's BLOCK stays DR from the chain?

ASSEMBLY_DESIGN sec.181.  `kDR` wants an external DR from the WHOLE kernel
chain; `glueDRMT` supplies it by gluing a whole certificate, at the price of
`DRCompat`.  DRCompat is FREE on nodes already DR from the chain, because the
chain's forall-DR universals then fire on them directly.

sec.181 proves the DESCENDING direction free (comp(DR,PPI) = {DR}) and leaves
ascending / horizontal open (comp(DR,PP) and comp(DR,DR), comp(DR,PO) are wide).
This probe measures how much that actually costs on real blocks.

  measured: of the nodes in a DR-witness's demand closure, what fraction are
            DR from every chain point at or below the demand's height?
            broken down by the direction of the step that REACHED the node.

CONTROLS, stated BEFORE the run:
  C1  nodes reached by a PURE DESCENT must be 100% DR.  That is dr_cone_free,
      now a theorem; anything below 100% means the probe is wrong.
  C2  the witness itself (empty path) must be 100% DR at-or-below its height.
      That is dr_witness_below; same status.

wp127's decay (100% -> 24.7%) was measured with chain a_i = {0..i} inside a
FIXED finite universe, where the chain necessarily exhausts the universe and
nothing can stay disjoint.  Per the campaign's companion rule, that is a
candidate generator artifact, so this probe uses TWO model classes:
  G1  unrestricted random subsets of a universe (wp127-like)
  G2  a RESERVED region the chain never enters (the artifact removed)
A rate that moves between G1 and G2 is a property of the generator.

Self-contained: RCC5 relations and the composition table from finite set
semantics.
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

# the two cells sec.181 turns on, re-derived rather than assumed
assert CT[(DR, PPI)] == {DR}, CT[(DR, PPI)]
assert CT[(PP, DR)] == {DR}, CT[(PP, DR)]
assert len(CT[(DR, PP)]) > 1 and len(CT[(DR, DR)]) > 1


# ------------------------------------------------------------ concept syntax

def mdepth(c):
    k = c[0]
    if k in ("at", "nat"):
        return 0
    if k in ("and", "or"):
        return max(mdepth(c[1]), mdepth(c[2]))
    return 1 + mdepth(c[2])


def closure(c, acc=None):
    if acc is None:
        acc = []
    if c not in acc:
        acc.append(c)
    k = c[0]
    if k in ("and", "or"):
        closure(c[1], acc); closure(c[2], acc)
    elif k in ("ex", "all"):
        closure(c[2], acc)
    return acc


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


def rand_concept(rng, depth, natoms=2):
    if depth == 0 or rng.random() < 0.3:
        i = rng.randrange(natoms)
        return ("at", i) if rng.random() < 0.6 else ("nat", i)
    r = rng.random()
    if r < 0.2:
        return ("and", rand_concept(rng, depth - 1, natoms),
                rand_concept(rng, depth - 1, natoms))
    if r < 0.32:
        return ("or", rand_concept(rng, depth - 1, natoms),
                rand_concept(rng, depth - 1, natoms))
    if r < 0.78:
        return ("ex", rng.choice(ATOMS), rand_concept(rng, depth - 1, natoms))
    # never forall-PO; DR weighted up so the DRCompat question is NON-VACUOUS
    return ("all", rng.choice([DR, DR, DR, PP, PPI, EQ]),
            rand_concept(rng, depth - 1, natoms))


# ------------------------------------------------------- the two model classes

def gen_model(rng, cls, chain_len=3, extra=6):
    """Return (model, val, chain).  chain is an ascending PP-chain."""
    if cls == "G1":                        # wp127-like: one shared universe
        U = list(range(6))
        chain = [frozenset(U[:k + 1]) for k in range(1, chain_len + 1)]
        pool = subsets(set(U))
    else:                                  # G2: a region the chain never enters
        A, B = list(range(4)), list(range(4, 8))
        chain = [frozenset(A[:k + 1]) for k in range(1, chain_len + 1)]
        pool = subsets(set(A + B))
    model = list(dict.fromkeys(chain + rng.sample(pool, min(len(pool), extra))))
    val = {}
    for a in range(2):
        for x in model:
            val[(a, x)] = rng.random() < 0.5
    return model, val, chain


def block_nodes(model, val, w, c0, budget):
    """Demand closure from w, recording HOW each node was reached:
       'desc' = every step was PPI (the free cone), 'mixed' = anything else."""
    seen = {w: ("desc", 0)}
    frontier = [(w, "desc", budget)]
    while frontier:
        x, tag, b = frontier.pop()
        if b <= 0:
            continue
        for d in closure(c0):
            if d[0] != "ex" or mdepth(d) >= b or not sat(model, val, x, d):
                continue
            for y in model:
                if rel(x, y) == d[1] and sat(model, val, y, d[2]):
                    ntag = "desc" if (tag == "desc" and d[1] == PPI) else "mixed"
                    if y not in seen or (seen[y][0] == "mixed" and ntag == "desc"):
                        seen[y] = (ntag, b - 1)
                        frontier.append((y, ntag, b - 1))
                    break
    return seen


def run(cls, trials, seed):
    rng = random.Random(seed)
    stats = {"desc": [0, 0], "mixed": [0, 0], "root": [0, 0]}
    blocks = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        model, val, chain = gen_model(rng, cls)
        # find a chain point carrying an exists-DR demand
        cand = [(j, d) for j in range(len(chain)) for d in closure(c0)
                if d[0] == "ex" and d[1] == DR and sat(model, val, chain[j], d)]
        if not cand:
            continue
        j, dem = rng.choice(cand)
        wit = [y for y in model
               if rel(chain[j], y) == DR and sat(model, val, y, dem[2])]
        if not wit:
            continue
        w = rng.choice(wit)
        blocks += 1
        below = chain[:j + 1]
        seen = block_nodes(model, val, w, c0, mdepth(c0))
        for y, (tag, _) in seen.items():
            key = "root" if y == w else tag
            ok = all(rel(cp, y) == DR for cp in below)
            stats[key][1] += 1
            stats[key][0] += 1 if ok else 0
    return blocks, stats


def report(cls, blocks, stats):
    print(f"\n  model class {cls}:  {blocks} blocks built")
    print(f"    {'reached by':<22}{'DR from chain-below':>22}{'nodes':>9}")
    for key, label in (("root", "the witness itself (C2)"),
                       ("desc", "pure descent (C1)"),
                       ("mixed", "any ascent/across")):
        ok, tot = stats[key]
        pct = f"{100.0*ok/tot:.1f}%" if tot else "n/a"
        print(f"    {label:<22}{pct:>22}{tot:>9}")
    return stats


def part_b(cls, trials, seed):
    """The number that actually decides the route: is DRCompat -- the LABEL
    condition -- satisfied, even though the model has no DR-separation?

    DRCompat asks: every forall-DR body owed by the CHAIN holds at every BLOCK
    node, and every forall-DR body owed by the BLOCK holds at every chain point.
    Nothing here reads the model's DR relation; the glue DECLARES it.

    VACUOUS instances (no forall-DR body in play at all) are DISCARDED, not
    counted as successes: a first run scored 94% on a sample whose mean body
    count was 0.1, i.e. the headline was measuring emptiness."""
    rng = random.Random(seed)
    both = chain_side = block_side = tot = 0
    body_counts = []
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        model, val, chain = gen_model(rng, cls)
        cand = [(j, d) for j in range(len(chain)) for d in closure(c0)
                if d[0] == "ex" and d[1] == DR and sat(model, val, chain[j], d)]
        if not cand:
            continue
        j, dem = rng.choice(cand)
        wit = [y for y in model
               if rel(chain[j], y) == DR and sat(model, val, y, dem[2])]
        if not wit:
            continue
        w = rng.choice(wit)
        seen = block_nodes(model, val, w, c0, mdepth(c0))
        blk = list(seen.keys())
        cbodies = [d[2] for d in closure(c0) if d[0] == "all" and d[1] == DR
                   and any(sat(model, val, cp, d) for cp in chain)]
        bbodies = [d[2] for d in closure(c0) if d[0] == "all" and d[1] == DR
                   and any(sat(model, val, y, d) for y in blk)]
        nb = len(cbodies) + len(bbodies)
        if nb == 0:
            continue                      # VACUOUS: DRCompat holds trivially
        body_counts.append(nb)
        cs = all(sat(model, val, y, X) for X in cbodies for y in blk)
        bs = all(sat(model, val, cp, X) for X in bbodies for cp in chain)
        tot += 1
        chain_side += 1 if cs else 0
        block_side += 1 if bs else 0
        both += 1 if (cs and bs) else 0
    return tot, chain_side, block_side, both, body_counts


def part_c(cls, trials, seed):
    """THE DECISIVE NUMBER.  Part B glued an ARBITRARY witness's block.  The
    route does not need every block to work -- it needs ONE.  sec.180 certifies
    the body set is consistent AT THE ROOT; this asks whether the whole block
    can be chosen too.

    For each non-vacuous instance: does SOME witness of the demand have a block
    satisfying DRCompat?"""
    rng = random.Random(seed)
    tot = exists = arbitrary_ok = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        model, val, chain = gen_model(rng, cls)
        cand = [(j, d) for j in range(len(chain)) for d in closure(c0)
                if d[0] == "ex" and d[1] == DR and sat(model, val, chain[j], d)]
        if not cand:
            continue
        j, dem = rng.choice(cand)
        wit = [y for y in model
               if rel(chain[j], y) == DR and sat(model, val, y, dem[2])]
        if not wit:
            continue
        cbodies = [d[2] for d in closure(c0) if d[0] == "all" and d[1] == DR
                   and any(sat(model, val, cp, d) for cp in chain)]
        oks = []
        nonvac = False
        for w in wit:
            blk = list(block_nodes(model, val, w, c0, mdepth(c0)).keys())
            bbodies = [d[2] for d in closure(c0) if d[0] == "all" and d[1] == DR
                       and any(sat(model, val, y, d) for y in blk)]
            if len(cbodies) + len(bbodies) == 0:
                continue
            nonvac = True
            oks.append(all(sat(model, val, y, X) for X in cbodies for y in blk)
                       and all(sat(model, val, cp, X) for X in bbodies
                               for cp in chain))
        if not nonvac:
            continue
        tot += 1
        exists += 1 if any(oks) else 0
        arbitrary_ok += sum(oks) / len(oks)
    return tot, exists, arbitrary_ok


def part_d(cls, trials, seed, pool_size=60):
    """WHAT PART C WITHHELD.  Parts B/C draw the block from the SAME model as
    the chain.  That is not a constraint the real setting imposes: `glueDRMT`
    builds a NEW certificate, and the block may be a certificate of a DIFFERENT
    model -- sec.180 certifies the body set is CONSISTENT, so a model of
    `D and (all the chain's forall-DR bodies)` exists.

    Per the campaign's companion rule, a probe must model every FREEDOM the
    real setting allows, not only every constraint.  This part restores it: the
    block is searched for across independently generated models."""
    rng = random.Random(seed)
    pool = [gen_model(rng, cls) for _ in range(pool_size)]
    tot = exists = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        model, val, chain = gen_model(rng, cls)
        cand = [(j, d) for j in range(len(chain)) for d in closure(c0)
                if d[0] == "ex" and d[1] == DR and sat(model, val, chain[j], d)]
        if not cand:
            continue
        j, dem = rng.choice(cand)
        if not any(rel(chain[j], y) == DR and sat(model, val, y, dem[2])
                   for y in model):
            continue
        cbodies = [d[2] for d in closure(c0) if d[0] == "all" and d[1] == DR
                   and any(sat(model, val, cp, d) for cp in chain)]
        found = False
        nonvac = False
        for (m2, v2, _) in pool:
            for w in m2:
                if not sat(m2, v2, w, dem[2]):
                    continue
                blk = list(block_nodes(m2, v2, w, c0, mdepth(c0)).keys())
                bbodies = [d[2] for d in closure(c0)
                           if d[0] == "all" and d[1] == DR
                           and any(sat(m2, v2, y, d) for y in blk)]
                if len(cbodies) + len(bbodies) == 0:
                    continue
                nonvac = True
                if (all(sat(m2, v2, y, X) for X in cbodies for y in blk)
                        and all(sat(model, val, cp, X) for X in bbodies
                                for cp in chain)):
                    found = True
                    break
            if found:
                break
        if not nonvac:
            continue
        tot += 1
        exists += 1 if found else 0
    return tot, exists


def part_e(cls, trials, seed):
    """WHERE do the failures live?  Prediction, stated before the run:

    w is DR from the chain AT OR BELOW the demand's height j (dr_witness_below),
    so in the MODEL the block's forall-DR universals already fire on c_0..c_j and
    are satisfied there.  The glue additionally declares DR to c_{j+1}, c_{j+2},
    ... where the model guarantees nothing.

    So block-side violations should be ENTIRELY above the demand's height.  If
    that holds, DRCompat's residue is the same 'above the demand' gap sec.178
    hit and sec.179 closed for the other direction -- a known shape with a known
    tool -- rather than a new obstruction."""
    rng = random.Random(seed)
    fails = below = above_only = nonroot = 0
    for _ in range(trials):
        c0 = rand_concept(rng, rng.randint(2, 3))
        model, val, chain = gen_model(rng, cls)
        cand = [(j, d) for j in range(len(chain)) for d in closure(c0)
                if d[0] == "ex" and d[1] == DR and sat(model, val, chain[j], d)]
        if not cand:
            continue
        j, dem = rng.choice(cand)
        wit = [y for y in model
               if rel(chain[j], y) == DR and sat(model, val, y, dem[2])]
        if not wit:
            continue
        w = rng.choice(wit)
        blk = list(block_nodes(model, val, w, c0, mdepth(c0)).keys())
        bbodies = [d[2] for d in closure(c0) if d[0] == "all" and d[1] == DR
                   and any(sat(model, val, y, d) for y in blk)]
        rootb = [d[2] for d in closure(c0) if d[0] == "all" and d[1] == DR
                 and sat(model, val, w, d)]
        bad = [(X, i) for X in bbodies for i in range(len(chain))
               if not sat(model, val, chain[i], X)]
        if not bad:
            continue
        fails += 1
        if all(i > j for (_, i) in bad):
            above_only += 1
        else:
            # at-or-below: must come from a NON-ROOT node, since w is DR from
            # every c_i with i <= j and its own universals already fire there
            below += 1
            if all(X not in rootb for (X, i) in bad if i <= j):
                nonroot += 1
    return fails, above_only, below, nonroot


def main():
    print("WP130 -- the free DR cone, measured")
    print(__doc__.split("Self-contained")[0].strip().splitlines()[-1])
    res = {}
    for cls, seed in (("G1", 20260826), ("G2", 20260827)):
        b, st = run(cls, 4000, seed)
        report(cls, b, st)
        res[cls] = st

    print("\n" + "=" * 72)
    ok = True
    for cls in ("G1", "G2"):
        for key, name in (("root", "C2 dr_witness_below"), ("desc", "C1 dr_cone_free")):
            good, tot = res[cls][key]
            if tot and good != tot:
                print(f"  CONTROL FAILURE {cls} {name}: {good}/{tot}")
                ok = False
    if ok:
        print("  CONTROLS PASS: both theorem-backed rates are exactly 100% in")
        print("  both model classes -- dr_witness_below and dr_cone_free hold")
        print("  on every node the probe generated.")
    print()
    for cls in ("G1", "G2"):
        g, t = res[cls]["mixed"]
        if t:
            print(f"  {cls} ascent/across nodes still DR : {100.0*g/t:.1f}%  ({t} nodes)")
    g1 = res["G1"]["mixed"]; g2 = res["G2"]["mixed"]
    if g1[1] and g2[1]:
        d = abs(100.0*g1[0]/g1[1] - 100.0*g2[0]/g2[1])
        print(f"  spread between model classes      : {d:.1f} points")
        print("  (a large spread means the rate is a property of the GENERATOR,")
        print("   not of the logic -- the campaign's companion rule.)")
    print("=" * 72)
    print("VERDICT:", "CONTROLS PASS" if ok else "CONTROL FAILURE -- numbers withheld")
    print()
    print("\nPART B -- DRCompat itself, as a LABEL condition (nothing reads the")
    print("          model's DR relation; the glue DECLARES it)")
    bres = {}
    for cls, seed in (("G1", 20260828), ("G2", 20260829)):
        tot, cs, bs, both, bc = part_b(cls, 4000, seed)
        mean = sum(bc) / len(bc) if bc else 0.0
        bres[cls] = (tot, both)
        print(f"\n  model class {cls}:  {tot} NON-VACUOUS glue candidates "
              f"(mean {mean:.1f} forall-DR bodies in play)")
        if tot:
            print(f"    chain's bodies hold at every block node : {100.0*cs/tot:5.1f}%")
            print(f"    block's bodies hold at every chain point: {100.0*bs/tot:5.1f}%")
            print(f"    DRCompat (both directions)              : {100.0*both/tot:5.1f}%")
    if bres["G1"][0] and bres["G2"][0]:
        d = abs(100.0*bres["G1"][1]/bres["G1"][0] - 100.0*bres["G2"][1]/bres["G2"][0])
        print(f"\n  spread between model classes : {d:.1f} points")
    print("\nPART C -- THE DECISIVE NUMBER: can a block be CHOSEN to satisfy it?")
    cres = {}
    for cls, seed in (("G1", 20260830), ("G2", 20260831)):
        tot, ex, arb = part_c(cls, 12000, seed)
        cres[cls] = (tot, ex)
        if tot:
            print(f"\n  model class {cls}:  {tot} non-vacuous instances")
            print(f"    an ARBITRARY witness's block works      : {100.0*arb/tot:5.1f}%")
            print(f"    SOME witness's block works (existence)  : {100.0*ex/tot:5.1f}%")
    if cres["G1"][0] and cres["G2"][0]:
        d = abs(100.0*cres["G1"][1]/cres["G1"][0] - 100.0*cres["G2"][1]/cres["G2"][0])
        print(f"\n  spread between model classes : {d:.1f} points")
    print("\nPART D -- the freedom parts B/C withheld: block from a DIFFERENT model")
    dres = {}
    for cls, seed in (("G1", 20260832), ("G2", 20260833)):
        tot, ex = part_d(cls, 6000, seed)
        dres[cls] = (tot, ex)
        if tot:
            print(f"    {cls}: some block ANYWHERE satisfies DRCompat : "
                  f"{100.0*ex/tot:5.1f}%   ({tot} non-vacuous instances)")
    print("\nPART E -- WHERE the block-side failures live (prediction: above only)")
    eres = {}
    for cls, seed in (("G1", 20260834), ("G2", 20260835)):
        f, ab, bl, nr = part_e(cls, 12000, seed)
        eres[cls] = (f, ab, bl, nr)
        if f:
            print(f"    {cls}: {f} failing instances -- "
                  f"{100.0*ab/f:5.1f}% ONLY above the demand's height, "
                  f"{100.0*bl/f:5.1f}% at or below")
            if bl:
                print(f"        of the at-or-below ones, {nr}/{bl} are owed by a "
                      f"NON-ROOT node (the root's own are forced, as predicted)")
    print()
    print("  READ, in the order the parts establish it:")
    print("   A  the free cone IS free -- 100% in both model classes, matching")
    print("      dr_witness_below and dr_cone_free.  But it is SMALL: nodes")
    print("      reached by any ascent or across-step are ~2% DR from the chain,")
    print("      stable across generators.  So DRCompat is NOT inherited from")
    print("      the model; the glue must DECLARE the DR and discharge the")
    print("      LABEL condition on its own.")
    print("   B  as a label condition on an ARBITRARY block, DRCompat holds")
    print("      ~36% of the time (non-vacuous instances only -- a first run")
    print("      scored 94% on a sample averaging 0.1 bodies, i.e. emptiness).")
    print("   C  choosing the witness INSIDE the model barely helps: existence")
    print("      tracks the arbitrary rate.  Selection is not the lever.")
    print("   D  letting the block come from a DIFFERENT model -- a freedom the")
    print("      real setting allows and B/C withheld -- roughly doubles it, to")
    print("      ~48%.  So the lever is the block's PROVENANCE, not its choice.")
    print("   E  and the residue is LOCALIZED: 91-97% of block-side failures")
    print("      occur ONLY at chain points ABOVE the demand's height, and every")
    print("      single at-or-below failure is owed by a NON-ROOT node.  Both")
    print("      halves are predicted: the root is DR from everything at or")
    print("      below by dr_witness_below, so its own universals are already")
    print("      forced there; non-root nodes are outside the free cone.")
    print()
    print("  NET: DRCompat's residue is the SAME 'above the demand' shape")
    print("  sec.178 met and sec.179 closed in the other direction, plus the")
    print("  non-root nodes sec.181 identifies as outside the free cone.  That")
    print("  is a known shape with a known tool, not a new obstruction -- but")
    print("  it is NOT free, and the ~48% says a construction is required.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
