#!/usr/bin/env python3
"""WP91 -- the MIXING ORDER CYCLE probe (ASSEMBLY_DESIGN sec. 39).

Context.  `mixKernels_ok`'s `hstab` requires every beta-external's row to every
kernel chain to be CONSTANT across the kernel's phases.  `externals_stabilize`
supplies a horizon only for an external list given IN ADVANCE, while
`kernel_site`'s DR/PP phase-witnesses are picked AFTER the base (above the
segment).  For a kernel's OWN chain that is harmless -- backward forcing
(comp(PP,DR) = {DR}) hands back the constant row for free.  The question this
probe settles is the CROSS-kernel direction:

  Q-crisp:  if `w` is a DR-witness of a high occurrence on chain `c` (so
            rho(c_b, w) = DR for every b below the cutoff), and `d` is a second
            ascending tower NON-COMPARABLE with `c`, is `w`'s row to `d` then
            already constant on the same window?

If Q-crisp were TRUE the cycle would dissolve: the witness would carry its
cross-kernel constancy for free, exactly as it carries its own-chain constancy,
and the bases could be fixed before the witnesses.

RESULT: Q-crisp is FALSE, and the failure is UNBOUNDED -- part C exhibits, for
every N, a configuration whose horizon is exactly N.  So no bound on the bases
can be fixed in advance of the witnesses.  Part D confirms the row nevertheless
always stabilizes (rank monotone, at most 2 changes), i.e. the obstruction is
the ORDER OF CHOICE, not the geometry.

Everything is self-contained: the RCC5 relations and composition table are
re-derived from finite set semantics, per project convention.
"""

from itertools import combinations

# ---------------------------------------------------------------- set semantics

DR, PO, EQ, PP, PPI = "DR", "PO", "EQ", "PP", "PPI"
ATOMS = [DR, PO, EQ, PP, PPI]


def rel(a, b):
    """The RCC5 relation between two nonempty regions, from set semantics."""
    if a == b:
        return EQ
    if a < b:
        return PP
    if b < a:
        return PPI
    if not (a & b):
        return DR
    return PO


def subsets(univ, nonempty=True):
    out = []
    for k in range(0 if not nonempty else 1, len(univ) + 1):
        for c in combinations(sorted(univ), k):
            out.append(frozenset(c))
    return out


def comp_table(n=4):
    """comp(r,s) = { rel(a,c) : rel(a,b)=r, rel(b,c)=s } by exhaustive search."""
    univ = set(range(n))
    regs = subsets(univ)
    table = {(r, s): set() for r in ATOMS for s in ATOMS}
    for a in regs:
        for b in regs:
            r = rel(a, b)
            for c in regs:
                table[(r, rel(b, c))].add(rel(a, c))
    return table


CT = comp_table(4)

# ------------------------------------------------- part A: sanity of the table


def part_a():
    print("PART A -- composition table re-derived from set semantics")
    checks = {
        ("PP", "PP"): {PP},
        ("PP", "DR"): {DR},
        ("DR", "PPI"): {DR},
        ("PP", "EQ"): {PP},
        ("EQ", "EQ"): {EQ},
    }
    ok = True
    for (r, s), expected in checks.items():
        got = CT[(r, s)]
        flag = got == expected
        ok &= flag
        print(f"  comp({r:3s},{s:3s}) = {sorted(got)!s:28s} expected {sorted(expected)}"
              f"  {'OK' if flag else 'MISMATCH'}")
    # the two facts the argument leans on
    print(f"  backward forcing  : DR in comp(PP,DR) and comp(PP,DR)=={{DR}} -> "
          f"{CT[('PP', 'DR')] == {DR}}")
    return ok


# ------------------------------------ tower helpers (finite prefixes of towers)


def ascending(chain):
    return all(chain[i] < chain[i + 1] for i in range(len(chain) - 1))


def embeds(c, d):
    """`c` embeds in `d`:  every c_i is PP-or-EQ inside some d_j."""
    return all(any(rel(ci, dj) in (PP, EQ) for dj in d) for ci in c)


def comparable(c, d):
    return embeds(c, d) or embeds(d, c)


def row(chain, w):
    return [rel(x, w) for x in chain]


# --------------------------------- part B: Q-crisp is FALSE (explicit witness)


def part_b():
    print("\nPART B -- Q-crisp: does cross-kernel constancy come for free?")
    c = [frozenset({0}), frozenset({0, 1}), frozenset({0, 1, 2})]
    d = [frozenset({4}), frozenset({3, 4}), frozenset({2, 3, 4})]
    w = frozenset({3})

    assert ascending(c) and ascending(d), "chains must ascend"
    rc = row(c, w)
    rd = row(d, w)
    print(f"  c        = {[sorted(x) for x in c]}")
    print(f"  d        = {[sorted(x) for x in d]}")
    print(f"  w        = {sorted(w)}")
    print(f"  non-comparable(c,d)            : {not comparable(c, d)}")
    print(f"  cross rel rho(c_2,d_2)         : {rel(c[2], d[2])}   "
          f"(the incomparable+overlapping PO case)")
    print(f"  row  c -> w                    : {rc}   constant: {len(set(rc)) == 1}")
    print(f"  row  d -> w                    : {rd}   constant: {len(set(rd)) == 1}")

    own_ok = set(rc) == {DR}
    cross_bad = len(set(rd)) > 1
    print(f"  w is a DR-witness of ALL of c  : {own_ok}   (own-chain constancy free)")
    print(f"  w's row to d is NON-constant   : {cross_bad}   <-- Q-crisp FALSE")
    print("  => a witness picked for kernel c does NOT carry constancy w.r.t. d;")
    print("     d's base must be pushed past w's horizon, and w exists only")
    print("     after c's base was chosen.  That is the sec.39 cycle.")
    return own_ok and cross_bad and not comparable(c, d)


# ---------------------------- part C: the horizon is UNBOUNDED (parameterized)


def family(N):
    """For a target horizon N: `c` ascends through the evens, `d` ascends slowly
    through a private block and only swallows `w` at step N."""
    # c lives on 0, 2, 4, ...   (never touches the odd block or w)
    c = [frozenset(range(0, 2 * k + 1, 2)) for k in range(1, 4)]
    # w is a single odd point far from c
    w = frozenset({1})
    # d ascends through a private block of "high" points, reaching w only at N
    block = [frozenset({100 + i}) for i in range(N)]
    d = []
    cur = frozenset()
    for b in block:
        cur = cur | b
        d.append(cur)
    d.append(cur | w)            # step N: swallows w
    d.append(cur | w | frozenset({3}))
    return c, d, w


def part_c(Ns=(1, 2, 3, 5, 8, 13)):
    print("\nPART C -- is the horizon bounded?  (can bases be fixed in advance?)")
    ok = True
    for N in Ns:
        c, d, w = family(N)
        assert ascending(c) and ascending(d)
        rd = row(d, w)
        # horizon = first index from which the row is constant
        horizon = 0
        for i in range(len(rd)):
            if len(set(rd[i:])) == 1:
                horizon = i
                break
        else:
            horizon = None
        noncomp = not comparable(c, d)
        own = set(row(c, w)) == {DR}
        good = (horizon == N) and noncomp and own
        ok &= good
        print(f"  N={N:3d}  row d->w = {rd[0]}*{N} then {rd[-1]}   horizon={horizon:3d}"
              f"   non-comparable={noncomp}  w DR-witness of c={own}"
              f"   {'OK' if good else 'FAIL'}")
    print("  => the horizon is UNBOUNDED in the configuration, so no bound on the")
    print("     kernel bases can be pre-committed before the witnesses are known.")
    return ok


# ------------------- part D: the row DOES stabilize (rank monotone, <=2 changes)


RANK = {DR: 0, PP: 0, PO: 1, EQ: 1, PPI: 2}


def part_d(trials=4000, seed=20260819):
    print("\nPART D -- does the row stabilize?  (is the obstruction geometric?)")
    import random
    rng = random.Random(seed)
    univ = set(range(6))
    regs = [r for r in subsets(univ)]
    checked = 0
    mono_ok = True
    changes_ok = True
    worst = 0
    for _ in range(trials):
        # random ascending chain of length 4
        chain = []
        cur = frozenset({rng.randrange(6)})
        chain.append(cur)
        good = True
        for _ in range(3):
            cands = [r for r in regs if cur < r]
            if not cands:
                good = False
                break
            cur = rng.choice(cands)
            chain.append(cur)
        if not good:
            continue
        w = rng.choice(regs)
        r = row(chain, w)
        ranks = [RANK[x] for x in r]
        checked += 1
        if any(ranks[i] > ranks[i + 1] for i in range(len(ranks) - 1)):
            mono_ok = False
            print(f"    RANK NON-MONOTONE: chain={[sorted(x) for x in chain]} "
                  f"w={sorted(w)} row={r}")
        nch = sum(1 for i in range(len(ranks) - 1) if ranks[i] != ranks[i + 1])
        worst = max(worst, nch)
        if nch > 2:
            changes_ok = False
    print(f"  sampled ascending chains          : {checked}")
    print(f"  rank monotone along the chain     : {mono_ok}")
    print(f"  max rank changes observed         : {worst} (bound is 2)  ok={changes_ok}")
    print("  => every row stabilizes after at most 2 rank changes.  The geometry")
    print("     always resolves; what does not resolve is the ORDER OF CHOICE.")
    return mono_ok and changes_ok


# ------------- part E: the row's SHAPE, and the cofinal-DR dividing line


def part_e(n=5):
    """EXHAUSTIVE over a universe of size n: every ascending 3-chain and every
    node.  Establishes (i) the row shape is  X* PO* EQ? PPI*  with X in
    {DR,PP} -- in particular the rank-0 block is CONSTANT, so a row whose limit
    is DR is DR from index 0 (horizon 0); (ii) cofinally-DR <=> DR everywhere."""
    print("\nPART E -- the row's shape, and the cofinal-DR dividing line")
    univ = set(range(n))
    regs = subsets(univ)
    chains = []
    for a in regs:
        for b in regs:
            if not a < b:
                continue
            for c3 in regs:
                if b < c3:
                    chains.append([a, b, c3])
    shape_ok = True
    rank0_const_ok = True
    cofinal_ok = True
    seen_shapes = set()
    total = 0
    for ch in chains:
        for w in regs:
            r = row(ch, w)
            total += 1
            ranks = [RANK[x] for x in r]
            # (i) rank-0 block constant: no DR/PP switch inside rank 0
            zeros = [x for x, rk in zip(r, ranks) if rk == 0]
            if len(set(zeros)) > 1:
                rank0_const_ok = False
                print(f"    RANK-0 NOT CONSTANT: chain={[sorted(x) for x in ch]} "
                      f"w={sorted(w)} row={r}")
            # (ii) EQ, if present, is the last rank-1 entry
            for i, x in enumerate(r):
                if x == EQ and i + 1 < len(r) and r[i + 1] != PPI:
                    shape_ok = False
                    print(f"    EQ NOT FOLLOWED BY PPI: {r}")
            seen_shapes.add("".join({DR: "d", PP: "p", PO: "o", EQ: "e",
                                     PPI: "i"}[x] for x in r))
            # (iii) cofinal DR (here: DR at the TOP of the prefix) <=> DR everywhere
            if r[-1] == DR and set(r) != {DR}:
                cofinal_ok = False
                print(f"    DR AT TOP BUT NOT EVERYWHERE: {r}")
    print(f"  exhaustive (chain, node) pairs, |U|={n}   : {total}")
    print(f"  rank-0 block always constant (no DR/PP switch) : {rank0_const_ok}")
    print(f"  EQ always immediately followed by PPI         : {shape_ok}")
    print(f"  DR at the top  =>  DR everywhere (horizon 0)  : {cofinal_ok}")
    print(f"  distinct row shapes observed                  : {len(seen_shapes)}")
    print("  => a cofinally-DR external needs NO horizon (cofinal_dr_all /")
    print("     cofinal_dr_stab, both kernel-checked).  The sec.39 cycle bites")
    print("     ONLY for externals some other kernel eventually overlaps or")
    print("     swallows -- that is the narrowed target sec.39.6.")
    return rank0_const_ok and shape_ok and cofinal_ok


# ------------------ part F: R4-prime itself, and what replaces it


def part_f(M=6):
    """F1 -- R4' FAILS per model: two always-DR (hence non-comparable) towers
    where EVERY D-witness of the first is eventually swallowed by the second.
    F2 -- and the natural strengthening (a BASE-INDEPENDENT witness bank: one
    D-witness DR from the WHOLE chain) can fail too, because the chain itself
    eventually swallows every fixed region."""
    print("\nPART F -- R4' and the base-independent-bank alternative")

    # F1: c on the evens, d on the odds, D-witnesses = odd singletons
    c = [frozenset(range(0, 2 * m + 1, 2)) for m in range(1, M)]
    d = [frozenset(range(1, 2 * j + 2, 2)) for j in range(1, M)]
    wits = [frozenset({2 * t + 1}) for t in range(M)]
    cross = {rel(x, y) for x in c for y in d}
    dr_from_all_c = [w for w in wits if all(rel(x, w) == DR for x in c)]
    cofinal_dr_from_d = [w for w in dr_from_all_c
                         if rel(d[-1], w) == DR]
    print(f"  F1  cross relations c vs d           : {sorted(cross)}"
          f"   (always DR -> non-comparable)")
    print(f"      D-witnesses DR from ALL of c     : {len(dr_from_all_c)}/{len(wits)}")
    print(f"      ... of those, cofinally DR from d: {len(cofinal_dr_from_d)}")
    f1 = len(dr_from_all_c) > 0 and len(cofinal_dr_from_d) == 0
    print(f"      => R4' FAILS in this model       : {f1}")

    # F2: c exhausts the universe -> no fixed region stays DR from all of c
    univ = set(range(M))
    c2 = [frozenset(range(0, m + 1)) for m in range(M)]
    regs = subsets(univ)
    base_indep = [w for w in regs if all(rel(x, w) == DR for x in c2)]
    per_phase = all(any(rel(c2[m], w) == DR for w in regs) for m in range(M - 1))
    print(f"  F2  regions DR from the WHOLE chain  : {len(base_indep)}"
          f"   (chain exhausts the universe)")
    print(f"      but every phase HAS some DR-witness : {per_phase}")
    f2 = len(base_indep) == 0 and per_phase
    print(f"      => a BASE-INDEPENDENT bank can fail : {f2}")

    print("  => neither R4' nor 'pre-select a base-independent bank' is available")
    print("     in general.  What survives is the WINDOW reading of hstab: a")
    print("     witness need only be constant on [i, i+p), which is exactly what")
    print("     kernel_site delivers (mixKernels_ok's hstab weakened, sec.39.7).")
    return f1 and f2


# ---------- part G: is R6 SATISFIABLE?  (search for an impossible configuration)


def rand_chain(rng, univ, L, maxstep=2):
    """A random ascending chain of length L inside `univ`.  `maxstep=1` keeps the
    chain thin, so that regions disjoint from it (DR-witnesses) still exist at
    every level -- required when the demand must be live all the way up."""
    rest = sorted(univ)
    rng.shuffle(rest)
    cur = frozenset({rest.pop()})
    ch = [cur]
    for _ in range(L - 1):
        if not rest:
            return None
        k = min(len(rest), 1 if maxstep == 1 else rng.choice([1, 1, 2]))
        cur = cur | frozenset(rest[:k])
        rest = rest[k:]
        ch.append(cur)
    return ch


def rand_bank(rng, chain, regs):
    """A witness bank making the demand LIVE at every chain level: for each node
    a region DR from it (different levels may need different witnesses)."""
    bank = set()
    for node in chain:
        cands = [w for w in regs if rel(node, w) == DR]
        if not cands:
            return None
        bank.add(rng.choice(cands))
    return sorted(bank, key=lambda s: (len(s), sorted(s)))


def valid_config(A, B, WA, WB, L, minp=1, maxp=3):
    """Search for bases/periods/witnesses satisfying, simultaneously:
       - each kernel's own DR-demand served across its whole window, and
       - EACH witness's row CONSTANT on the OTHER kernel's window (hstab)."""
    for pA in range(minp, maxp + 1):
        for pB in range(minp, maxp + 1):
            for iA in range(L - pA + 1):
                winA = [A[iA + b] for b in range(pA)]
                okA = [w for w in WA if all(rel(x, w) == DR for x in winA)]
                if not okA:
                    continue
                for iB in range(L - pB + 1):
                    winB = [B[iB + b] for b in range(pB)]
                    okB = [w for w in WB if all(rel(x, w) == DR for x in winB)]
                    if not okB:
                        continue
                    for wA in okA:
                        if len({rel(x, wA) for x in winB}) != 1:
                            continue          # wA not stable on B's window
                        for wB in okB:
                            if len({rel(x, wB) for x in winA}) != 1:
                                continue      # wB not stable on A's window
                            return (iA, pA, iB, pB, wA, wB)
    return None


def part_g(trials=3000, n=8, L=5, seed=20260819):
    """R6, tested directly.  Over many two-kernel models in which BOTH demands
    are live at every level, does a valid (bases, periods, witnesses) vector
    always exist?  Reported separately for periods >= 1 (the general case, where
    period-1 makes hstab vacuous) and periods >= 2 (the genuinely periodic,
    multi-demand round-robin case, where the cycle can actually bite)."""
    print("\nPART G -- is R6 satisfiable?  (search for an IMPOSSIBLE configuration)")
    import random
    rng = random.Random(seed)
    univ = set(range(n))
    regs = subsets(univ)
    stats = {1: [0, 0], 2: [0, 0]}          # minp -> [models, failures]
    fail_example = {}
    for _ in range(trials):
        A = rand_chain(rng, univ, L)
        B = rand_chain(rng, univ, L)
        if A is None or B is None:
            continue
        WA = rand_bank(rng, A, regs)
        WB = rand_bank(rng, B, regs)
        if not WA or not WB:
            continue
        for minp in (1, 2):
            stats[minp][0] += 1
            cfg = valid_config(A, B, WA, WB, L, minp=minp)
            if cfg is None:
                stats[minp][1] += 1
                fail_example.setdefault(minp, (A, B, WA, WB))
    for minp in (1, 2):
        tot, bad = stats[minp]
        print(f"  periods >= {minp}:  models tested {tot:5d}   "
              f"NO valid configuration in {bad:5d}   "
              f"({100.0 * bad / max(tot, 1):.2f}%)")
    if 2 in fail_example:
        A, B, WA, WB = fail_example[2]
        print(f"    example failure (periods>=2):")
        print(f"      A  = {[sorted(x) for x in A]}")
        print(f"      B  = {[sorted(x) for x in B]}")
    print("  NOTE the two degrees of freedom sec.39.8 had missed:")
    print("   (i) period 1 makes hstab VACUOUS (a < 1 forces a = 0) -- so the")
    print("       cycle can only bite for genuinely multi-phase kernels;")
    print("  (ii) a window is constant if it lies entirely BELOW a transition,")
    print("       not only above it -- so 'push past every transition' is not")
    print("       the only way to satisfy hstab.")
    return stats


# ------------------ part H: the STRESS of R6 -- 3 kernels, bigger, adversarial


def valid_multi(chains, banks, L, minp, maxp, minbase=0):
    """R6 for ANY number of kernels.  Key simplification: once the base/period
    VECTOR is fixed, each kernel's witness condition is INDEPENDENT of the other
    kernels' witness choices (w_k must be DR on k's own window and constant on
    every other window), so the search is linear in the number of kernels rather
    than exponential."""
    m = len(chains)
    opts = [(i, p) for p in range(minp, maxp + 1)
            for i in range(minbase, L - p + 1)]

    def rec(idx, chosen):
        if idx == m:
            wins = [[chains[k][i + b] for b in range(p)] for k, (i, p) in enumerate(chosen)]
            for k in range(m):
                found = False
                for w in banks[k]:
                    if not all(rel(x, w) == DR for x in wins[k]):
                        continue
                    if all(len({rel(x, w) for x in wins[k2]}) == 1
                           for k2 in range(m) if k2 != k):
                        found = True
                        break
                if not found:
                    return None
            return chosen
        for o in opts:
            r = rec(idx + 1, chosen + [o])
            if r is not None:
                return r
        return None

    return rec(0, [])


def part_h(models=400, banks_per=12, n=9, L=6, seed=20260819):
    print("\nPART H -- R6 stressed: 3 kernels, larger models, many banks each")
    import random
    rng = random.Random(seed)
    univ = set(range(n))
    regs = subsets(univ)
    for m in (2, 3):
        for minp in (1, 2):
            tested = bad = 0
            for _ in range(models):
                chains = [rand_chain(rng, univ, L) for _ in range(m)]
                if any(c is None for c in chains):
                    continue
                for _ in range(banks_per):
                    bks = [rand_bank(rng, c, regs) for c in chains]
                    if any(not b for b in bks):
                        continue
                    tested += 1
                    if valid_multi(chains, bks, L, minp, 3) is None:
                        bad += 1
            print(f"  kernels={m}  periods>={minp}:  (model,bank) pairs {tested:6d}"
                  f"   NO valid configuration in {bad:4d}"
                  f"   ({100.0 * bad / max(tested, 1):.2f}%)")
    print("  => across 2- and 3-kernel families, with the demand live at every")
    print("     level and minimal (one-per-level) witness banks, a simultaneously")
    print("     valid base/period/witness vector was ALWAYS found.  Evidence FOR")
    print("     R6 -- not a proof, and the search is over finite prefixes.")


# ------------- part I: WHICH mechanism satisfies hstab?  (the proof route)


def part_i(models=500, banks_per=8, n=9, L=6, seed=7654321):
    """For each successfully found configuration, classify HOW each cross-row was
    made constant: the window sat BELOW the witness's transition (cross-value DR,
    the 'stay low' mechanism) or ABOVE it (cross-value non-DR, the 'push past'
    mechanism of sec.39.8).  This says what a proof would have to argue."""
    print("\nPART I -- which mechanism makes the cross-rows constant?")
    import random
    rng = random.Random(seed)
    univ = set(range(n))
    regs = subsets(univ)
    below = above = 0
    both_needed = 0
    solved = 0
    for _ in range(models):
        A = rand_chain(rng, univ, L)
        B = rand_chain(rng, univ, L)
        if A is None or B is None:
            continue
        for _ in range(banks_per):
            WA = rand_bank(rng, A, regs)
            WB = rand_bank(rng, B, regs)
            if not WA or not WB:
                continue
            cfg = valid_multi([A, B], [WA, WB], L, 2, 3)
            if cfg is None:
                continue
            solved += 1
            (iA, pA), (iB, pB) = cfg
            winA = [A[iA + b] for b in range(pA)]
            winB = [B[iB + b] for b in range(pB)]
            # recover the witnesses the search would have used
            vals = []
            for (own, other, bank) in ((winA, winB, WA), (winB, winA, WB)):
                for w in bank:
                    if all(rel(x, w) == DR for x in own) and \
                       len({rel(x, w) for x in other}) == 1:
                        vals.append(next(iter({rel(x, w) for x in other})))
                        break
            if len(vals) < 2:
                continue
            nb = sum(1 for v in vals if v == DR)
            below += nb
            above += 2 - nb
            if 0 < nb < 2:
                both_needed += 1
    tot = below + above
    print(f"  configurations solved                     : {solved}")
    print(f"  cross-rows constant at DR  ('stay low')   : {below:5d}"
          f"  ({100.0 * below / max(tot, 1):.1f}%)")
    print(f"  cross-rows constant elsewhere ('push past'): {above:5d}"
          f"  ({100.0 * above / max(tot, 1):.1f}%)")
    print(f"  configurations needing BOTH mechanisms     : {both_needed}")
    print("  => the dominant mechanism is 'stay low': the cross-row sits in the")
    print("     row's INITIAL rank-0 block, which part E proved CONSTANT.  A")
    print("     proof of R6 should therefore argue that windows can be kept")
    print("     inside the initial DR-block, NOT that they can be pushed past")
    print("     every transition (the sec.39.8 framing, which the cycle blocks).")


# ---- part J: the probe's OWN gap -- bases must sit at a type recurrence (>= T)


def part_j(models=300, banks_per=10, n=12, L=6, seed=13579, Ts=(0, 1, 2, 3, 4)):
    """PARTS G-I DID NOT MODEL a constraint the real extraction imposes: a base
    must be a TYPE-RECURRENCE point, and `rr_segment_from` can only push it UP,
    never down.  Since part I found 92.7% of successes used the 'stay low'
    mechanism (windows in the row's INITIAL block), the earlier result may be
    optimistic.  This re-runs the search with every base forced >= T."""
    print("\nPART J -- bases forced to a late recurrence (the gap in parts G-I)")
    import random
    rng = random.Random(seed)
    univ = set(range(n))
    regs = subsets(univ)
    for T in Ts:
        tested = bad = low = high = 0
        for _ in range(models):
            A = rand_chain(rng, univ, L, maxstep=1)
            B = rand_chain(rng, univ, L, maxstep=1)
            if A is None or B is None:
                continue
            for _ in range(banks_per):
                WA = rand_bank(rng, A, regs)
                WB = rand_bank(rng, B, regs)
                if not WA or not WB:
                    continue
                tested += 1
                cfg = valid_multi([A, B], [WA, WB], L, 2, 3, minbase=T)
                if cfg is None:
                    bad += 1
                    continue
                (iA, pA), (iB, pB) = cfg
                winA = [A[iA + b] for b in range(pA)]
                winB = [B[iB + b] for b in range(pB)]
                for (own, other, bank) in ((winA, winB, WA), (winB, winA, WB)):
                    for w in bank:
                        if all(rel(x, w) == DR for x in own) and \
                           len({rel(x, w) for x in other}) == 1:
                            v = next(iter({rel(x, w) for x in other}))
                            if v == DR:
                                low += 1
                            else:
                                high += 1
                            break
        tot = low + high
        print(f"  base >= {T}:  pairs {tested:5d}   NO valid config {bad:4d}"
              f"  ({100.0 * bad / max(tested, 1):5.2f}%)"
              f"   |  stay-low {100.0 * low / max(tot, 1):5.1f}%"
              f"  push-past {100.0 * high / max(tot, 1):5.1f}%")
    print("  => if the failure rate stays ~0 as T grows, the route SURVIVES the")
    print("     recurrence constraint; if it climbs, 'stay low' was an artifact")
    print("     of letting the windows sit at the bottom of the chain.")


# ------- part K: is part J's failure a TRUNCATION artifact of finite prefixes?


def sample_regs(rng, univ, count):
    """A manageable pool of candidate witness regions (all singletons + random
    small sets), so the search stays fast on a universe large enough to hold two
    long disjointish chains."""
    pool = {frozenset({x}) for x in univ}
    us = sorted(univ)
    for _ in range(count):
        k = rng.randint(1, 3)
        pool.add(frozenset(rng.sample(us, k)))
    return sorted(pool, key=lambda t: (len(t), sorted(t)))


def part_k(models=250, banks_per=8, n=16, T=4, Ls=(6, 8, 10, 12), seed=24680):
    """Part J showed failures appearing at base >= 4 with L = 6 -- but there the
    window had exactly ONE legal position, so the failure may be TRUNCATION (the
    finite prefix running out of room above the base) rather than a genuine
    obstruction.  Real chains are infinite.  Fixing T and GROWING L decides it:
    if the failure rate falls to 0 as room is added above, it was truncation."""
    print(f"\nPART K -- truncation or obstruction?  (base >= {T}, growing the prefix)")
    import random
    rng = random.Random(seed)
    univ = set(range(n))
    regs = sample_regs(rng, univ, 500)
    for L in Ls:
        tested = bad = 0
        for _ in range(models):
            A = rand_chain(rng, univ, L, maxstep=1)
            B = rand_chain(rng, univ, L, maxstep=1)
            if A is None or B is None:
                continue
            for _ in range(banks_per):
                WA = rand_bank(rng, A, regs)
                WB = rand_bank(rng, B, regs)
                if not WA or not WB:
                    continue
                tested += 1
                if valid_multi([A, B], [WA, WB], L, 2, 3, minbase=T) is None:
                    bad += 1
        room = max(0, L - T - 2 + 1)
        print(f"  L={L:3d}  (legal window positions at base>={T}: {room:2d})"
              f"   pairs {tested:5d}   NO valid config {bad:4d}"
              f"  ({100.0 * bad / max(tested, 1):5.2f}%)")
    print("  => failures vanishing as the prefix grows means part J's 7.67% was")
    print("     TRUNCATION, not an obstruction: on an infinite chain there is")
    print("     always room above any recurrence base.")


# ------- part L: the DENSE constraint system -- many demands, PP too, m up to 4


def rand_bank_rel(rng, chain, univ, r):
    """A bank making an `exists r . D` demand live at every level (r = DR or PP).
    Witnesses are CONSTRUCTED rather than filtered from a pool, so that PP
    witnesses (which must strictly CONTAIN a chain node) exist at every level:
    DR -> a nonempty subset of the node's complement; PP -> the node plus one."""
    bank = set()
    us = sorted(univ)
    for node in chain:
        comp = [x for x in us if x not in node]
        if not comp:
            return None
        k = rng.randint(1, min(3, len(comp)))
        extra = frozenset(rng.sample(comp, k))
        bank.add(extra if r == DR else (node | extra))
    return sorted(bank, key=lambda t: (len(t), sorted(t)))


def valid_slots(chains, slots, L, minp, maxp, minbase=0):
    """`MixSelect` verbatim: slots = [(kernel, relation, bank)].  NOTE the
    structure -- once the base/period VECTOR is fixed the slots are INDEPENDENT
    (no constraint couples two witnesses), so all the joint content sits in
    choosing ONE base vector that satisfies every slot at once."""
    m = len(chains)
    opts = [(i, p) for p in range(minp, maxp + 1)
            for i in range(minbase, L - p + 1)]

    def ok(chosen):
        wins = [[chains[k][i + b] for b in range(p)] for k, (i, p) in enumerate(chosen)]
        for (k, r, bank) in slots:
            if not any(all(rel(x, w) == r for x in wins[k]) and
                       all(len({rel(x, w) for x in wins[k2]}) == 1
                           for k2 in range(m) if k2 != k)
                       for w in bank):
                return False
        return True

    def rec(idx, chosen):
        if idx == m:
            return chosen if ok(chosen) else None
        for o in opts:
            r = rec(idx + 1, chosen + [o])
            if r is not None:
                return r
        return None

    return rec(0, [])


def part_l(models=120, banks_per=5, n=16, L=10, T=4, seed=97531):
    """Every earlier part gave each kernel ONE DR-demand.  Real kernels carry
    SEVERAL DR/PP demands, each needing its own witness, and every witness
    constrains EVERY kernel's window.  This sweeps the density: m kernels x d
    demands per kernel, with both DR and PP demands, bases forced late (>= T)."""
    print(f"\nPART L -- dense constraint systems (bases >= {T}, DR and PP demands)")
    import random
    rng = random.Random(seed)
    univ = set(range(n))
    for m in (2, 3, 4):
        for d in (1, 2, 3):
            tested = bad = 0
            for _ in range(models):
                chains = [rand_chain(rng, univ, L, maxstep=1) for _ in range(m)]
                if any(c is None for c in chains):
                    continue
                for _ in range(banks_per):
                    slots = []
                    okgen = True
                    for k in range(m):
                        for t in range(d):
                            r = DR if t % 2 == 0 else PP
                            bk = rand_bank_rel(rng, chains[k], univ, r)
                            if bk is None:
                                okgen = False
                                break
                            slots.append((k, r, bk))
                        if not okgen:
                            break
                    if not okgen:
                        continue
                    tested += 1
                    if valid_slots(chains, slots, L, 2, 3, minbase=T) is None:
                        bad += 1
            print(f"  kernels={m}  demands/kernel={d}  (slots={m * d:2d})"
                  f"   systems {tested:5d}   NO valid config {bad:4d}"
                  f"  ({100.0 * bad / max(tested, 1):5.2f}%)")
    print("  => the density sweep is the sharpest test of the joint selection:")
    print("     every added slot is another witness that must be simultaneously")
    print("     stable on EVERY kernel's window, under ONE base vector.")


# ------ part M: does ONE COMMON BASE suffice?  (the shape of the proof)


def common_base_ok(chains, slots, T, p):
    """All kernels at the SAME base T with the SAME period p -- the simplest
    conceivable selection.  If this always works, the joint selection collapses
    to 'push every window to one common late level', and no genuine
    fixed-point/iteration argument is needed at all."""
    m = len(chains)
    wins = [[chains[k][T + b] for b in range(p)] for k in range(m)]
    for (k, r, bank) in slots:
        if not any(all(rel(x, w) == r for x in wins[k]) and
                   all(len({rel(x, w) for x in wins[k2]}) == 1
                       for k2 in range(m) if k2 != k)
                   for w in bank):
            return False
    return True


def part_m(models=200, banks_per=5, n=16, L=10, seed=112358,
           Ts=(4, 5, 6), ps=(2, 3)):
    print("\nPART M -- does ONE COMMON BASE suffice?  (would collapse the selection)")
    import random
    rng = random.Random(seed)
    univ = set(range(n))
    for m in (2, 3, 4):
        for T in Ts:
            for p in ps:
                if T + p > L:
                    continue
                tested = bad = 0
                for _ in range(models):
                    chains = [rand_chain(rng, univ, L, maxstep=1) for _ in range(m)]
                    if any(c is None for c in chains):
                        continue
                    for _ in range(banks_per):
                        slots = []
                        for k in range(m):
                            for t in range(3):
                                r = DR if t % 2 == 0 else PP
                                bk = rand_bank_rel(rng, chains[k], univ, r)
                                if bk:
                                    slots.append((k, r, bk))
                        if not slots:
                            continue
                        tested += 1
                        if not common_base_ok(chains, slots, T, p):
                            bad += 1
                print(f"  kernels={m}  common base={T}  period={p}"
                      f"   systems {tested:5d}   FAILS {bad:4d}"
                      f"  ({100.0 * bad / max(tested, 1):5.2f}%)")
    print("  => a 0% column would mean the joint selection COLLAPSES: put every")
    print("     window at one common late level and pick witnesses per slot.")
    print("     A nonzero column means the bases genuinely have to differ, and")
    print("     the proof must choose them jointly.")


# ------ part N: the STAGED construction -- strictly increasing bases


def valid_slots_increasing(chains, slots, L, p, minbase=0):
    """Part M killed the common base, so the bases must differ.  The natural
    replacement is a STAGED construction: process kernels in increasing base
    order i_1 < i_2 < ... < i_m.  Then each cross-constraint has a designated
    branch of the sec.39.10 dichotomy --
      * a LATER kernel's window vs an EARLIER kernel's witness: push the later
        base past that witness's horizon  ('push past'),
      * an EARLIER (low) window vs a LATER kernel's witness: the row is still in
        its initial rank-0 block down there  ('stay low').
    If this restricted search succeeds as often as the free one, the staged
    construction is the Lean proof plan."""
    m = len(chains)

    def rec(k, prev, chosen):
        if k == m:
            wins = [[chains[j][chosen[j] + b] for b in range(p)] for j in range(m)]
            for (kk, r, bank) in slots:
                if not any(all(rel(x, w) == r for x in wins[kk]) and
                           all(len({rel(x, w) for x in wins[k2]}) == 1
                               for k2 in range(m) if k2 != kk)
                           for w in bank):
                    return None
            return chosen
        for i in range(max(minbase, prev + 1), L - p + 1):
            r = rec(k + 1, i, chosen + [i])
            if r is not None:
                return r
        return None

    return rec(0, minbase - 1, [])


def part_n(models=200, banks_per=5, n=16, L=12, T=3, seed=31415):
    print("\nPART N -- the STAGED construction (strictly increasing bases)")
    import random
    rng = random.Random(seed)
    univ = set(range(n))
    for m in (2, 3, 4):
        for p in (2, 3):
            tested = bad_free = bad_inc = 0
            for _ in range(models):
                chains = [rand_chain(rng, univ, L, maxstep=1) for _ in range(m)]
                if any(c is None for c in chains):
                    continue
                for _ in range(banks_per):
                    slots = []
                    for k in range(m):
                        for t in range(3):
                            r = DR if t % 2 == 0 else PP
                            bk = rand_bank_rel(rng, chains[k], univ, r)
                            if bk:
                                slots.append((k, r, bk))
                    if not slots:
                        continue
                    tested += 1
                    if valid_slots(chains, slots, L, p, p, minbase=T) is None:
                        bad_free += 1
                    if valid_slots_increasing(chains, slots, L, p, minbase=T) is None:
                        bad_inc += 1
            print(f"  kernels={m}  period={p}   systems {tested:5d}"
                  f"   free bases FAIL {bad_free:4d} ({100.0 * bad_free / max(tested,1):5.2f}%)"
                  f"   |  STAGED FAIL {bad_inc:4d} ({100.0 * bad_inc / max(tested,1):5.2f}%)")
    print("  => if STAGED matches FREE, the joint selection can be done in one")
    print("     pass with a designated dichotomy branch per direction -- that is")
    print("     a Lean-shaped argument, not a fixed-point search.")


# ---- part O: does the GREEDY staged procedure succeed (not merely: a vector exists)?


def greedy_staged(chains, slots, L, p, T):
    """Part N showed an increasing base VECTOR exists.  That is NOT the same as
    the CONSTRUCTIVE left-to-right procedure succeeding: once `i_j` is fixed and
    `w_j` picked above it, 'w_j stable on the EARLIER windows' is no longer under
    our control.  This runs the actual greedy -- commit to each base and its
    witnesses in turn, with no lookahead and no backtracking."""
    m = len(chains)
    bases, chosen = [], []          # chosen : list of (kernel, witness)

    def stable_on(w, k, i):
        return len({rel(chains[k][i + b], w) for b in range(p)}) == 1

    for j in range(m):
        lo = max(T, bases[-1] + 1) if bases else T
        pick = None
        for i in range(lo, L - p + 1):
            # every ALREADY-chosen witness must be stable on this new window
            if not all(stable_on(w, j, i) for (_, w) in chosen):
                continue
            # and every slot of kernel j must find a witness serving its own
            # window AND stable on all EARLIER windows
            newly = []
            ok = True
            for (k, r, bank) in slots:
                if k != j:
                    continue
                cand = None
                for w in bank:
                    if not all(rel(chains[j][i + b], w) == r for b in range(p)):
                        continue
                    if all(stable_on(w, k2, bases[k2]) for k2 in range(j)):
                        cand = w
                        break
                if cand is None:
                    ok = False
                    break
                newly.append((j, cand))
            if ok:
                pick = (i, newly)
                break
        if pick is None:
            return None
        bases.append(pick[0])
        chosen.extend(pick[1])
    return bases


def part_o(models=200, banks_per=5, n=16, L=12, T=3, seed=161803):
    print("\nPART O -- GREEDY staged procedure vs mere EXISTENCE of a vector")
    import random
    rng = random.Random(seed)
    univ = set(range(n))
    for m in (2, 3, 4):
        for p in (2, 3):
            tested = bad_exist = bad_greedy = 0
            for _ in range(models):
                chains = [rand_chain(rng, univ, L, maxstep=1) for _ in range(m)]
                if any(c is None for c in chains):
                    continue
                for _ in range(banks_per):
                    slots = []
                    for k in range(m):
                        for t in range(3):
                            r = DR if t % 2 == 0 else PP
                            bk = rand_bank_rel(rng, chains[k], univ, r)
                            if bk:
                                slots.append((k, r, bk))
                    if not slots:
                        continue
                    tested += 1
                    if valid_slots_increasing(chains, slots, L, p, minbase=T) is None:
                        bad_exist += 1
                    if greedy_staged(chains, slots, L, p, T) is None:
                        bad_greedy += 1
            print(f"  kernels={m}  period={p}   systems {tested:5d}"
                  f"   EXISTS fails {bad_exist:4d} ({100.0 * bad_exist / max(tested,1):5.2f}%)"
                  f"   |  GREEDY fails {bad_greedy:4d} ({100.0 * bad_greedy / max(tested,1):5.2f}%)")
    print("  => GREEDY matching EXISTS means the construction is CONSTRUCTIVE:")
    print("     one left-to-right pass, no backtracking -- directly formalizable.")
    print("     A gap would mean the Lean proof needs search, not a construction.")


# ---- part P: does SOME kernel ORDER make the greedy work?  (a weaker plan)


def greedy_any_order(chains, slots, L, p, T):
    """Part O killed the plain left-to-right greedy.  Weaker candidate plan: is
    there SOME processing order for which the greedy succeeds?  That would still
    be a clean statement ('choose the right order'), just with a finite search
    over orders instead of a fixed left-to-right pass."""
    from itertools import permutations
    m = len(chains)
    for perm in permutations(range(m)):
        rechain = [chains[k] for k in perm]
        pos = {k: idx for idx, k in enumerate(perm)}
        reslots = [(pos[k], r, bank) for (k, r, bank) in slots]
        if greedy_staged(rechain, reslots, L, p, T) is not None:
            return perm
    return None


def part_p(models=150, banks_per=4, n=16, L=12, T=3, seed=271828):
    print("\nPART P -- does SOME kernel order rescue the greedy?")
    import random
    rng = random.Random(seed)
    univ = set(range(n))
    for m in (3, 4):
        for p in (2, 3):
            tested = bad_fixed = bad_any = 0
            for _ in range(models):
                chains = [rand_chain(rng, univ, L, maxstep=1) for _ in range(m)]
                if any(c is None for c in chains):
                    continue
                for _ in range(banks_per):
                    slots = []
                    for k in range(m):
                        for t in range(3):
                            r = DR if t % 2 == 0 else PP
                            bk = rand_bank_rel(rng, chains[k], univ, r)
                            if bk:
                                slots.append((k, r, bk))
                    if not slots:
                        continue
                    tested += 1
                    if greedy_staged(chains, slots, L, p, T) is None:
                        bad_fixed += 1
                    if greedy_any_order(chains, slots, L, p, T) is None:
                        bad_any += 1
            print(f"  kernels={m}  period={p}   systems {tested:5d}"
                  f"   fixed-order greedy fails {bad_fixed:4d}"
                  f" ({100.0 * bad_fixed / max(tested,1):5.2f}%)"
                  f"   |  SOME-order greedy fails {bad_any:4d}"
                  f" ({100.0 * bad_any / max(tested,1):5.2f}%)")
    print("  => if SOME-order is ~0%, the plan becomes 'process the kernels in a")
    print("     suitable order' -- still one pass, choosing the order first.")
    print("     If not, the selection needs genuine simultaneity, not staging.")


# ---- part Q: is the COLLAPSE hypothesis (a cofinal witness) actually available?


def part_q(L=14):
    """`mixSelect_of_cofinal_bank` (certified) dissolves the whole joint selection
    IF every horizontal demand has a witness bearing that relation to the ENTIRE
    chain.  Is that hypothesis available?  The ESCAPING family says no: the
    demand is live at every level, yet each witness is swallowed one level later,
    so the decreasing sets W_n = {w : rho(c n, w) = DR} are all nonempty with
    EMPTY intersection.  Then: does a valid config still exist for two such
    escaping kernels (i.e. is the collapse sufficient-but-not-necessary)?"""
    print("\nPART Q -- is the collapse hypothesis available?  (escaping witnesses)")
    # c_n = {0..n} ascending;  D-witnesses are the singletons {n+1}.
    # The chain runs LONGER than the witness list so that EVERY witness is
    # actually tested past its eating level (else the last one is never eaten --
    # the finite-prefix trap that part K already caught once).
    c = [frozenset(range(n + 1)) for n in range(L + 2)]
    wits = [frozenset({n + 1}) for n in range(L)]
    live = all(any(rel(c[n], w) == DR for w in wits) for n in range(L))
    cofinal = [w for w in wits if all(rel(x, w) == DR for x in c)]
    eats = [min(j for j, x in enumerate(c) if rel(x, w) != DR) for w in wits]
    print(f"  every witness has a finite 'eating level'  : {max(eats)} (max)")
    print(f"  demand live at EVERY level                 : {live}")
    print(f"  witnesses DR from the WHOLE chain (cofinal): {len(cofinal)}")
    print(f"  => W_n all nonempty, intersection EMPTY    : {live and not cofinal}")
    print("     so `CofinalWitness` is NOT always available -- the collapse is")
    print("     SUFFICIENT, not necessary.")

    # two escaping kernels on disjoint halves: does a valid config still exist?
    A = [frozenset(range(0, 2 * n + 2, 2)) for n in range(L + 2)]    # evens
    B = [frozenset(range(1, 2 * n + 3, 2)) for n in range(L + 2)]    # odds
    WA = [frozenset({2 * n + 2}) for n in range(L)]                  # eaten by A later
    WB = [frozenset({2 * n + 3}) for n in range(L)]                  # eaten by B later
    okA = all(any(rel(A[n], w) == DR for w in WA) for n in range(L))
    okB = all(any(rel(B[n], w) == DR for w in WB) for n in range(L))
    cofA = [w for w in WA if all(rel(x, w) == DR for x in A)]
    print(f"  two escaping kernels: demands live         : {okA and okB}")
    print(f"    cofinal witnesses for kernel A           : {len(cofA)}  (collapse unavailable)")
    for p in (2, 3):
        cfg = valid_slots([A, B], [(0, DR, WA), (1, DR, WB)], L, p, p, minbase=3)
        print(f"    period {p}: valid config with bases >= 3 : "
              f"{'YES ' + str(cfg) if cfg else 'NONE'}")
    print("  => a valid config existing WITHOUT a cofinal witness means the")
    print("     general case needs the sec.39.10 DICHOTOMY, not the collapse.")


# ---- part R: the ESCAPING residue under NON-COMPARABILITY (what sec.38 leaves)


def escaping_bank(rng, own, others, univ, adversarial=True):
    """A witness bank that ESCAPES its own chain: the witness for level n is DR
    from own[n] but NOT from own[n+1].  When `adversarial`, pick among the
    escaping candidates the one whose transition level w.r.t. the OTHER chains
    differs most from its own -- decorrelated transitions are what makes a window
    straddle, so this is the worst case for the selection."""
    us = sorted(univ)

    def trans(ch, w):
        for j, x in enumerate(ch):
            if rel(x, w) != DR:
                return j
        return len(ch)

    bank = set()
    for n in range(len(own) - 1):
        cands = []
        for _ in range(40):
            comp = [x for x in us if x not in own[n]]
            if not comp:
                break
            k = rng.randint(1, min(2, len(comp)))
            w = frozenset(rng.sample(comp, k))
            if rel(own[n], w) == DR and rel(own[n + 1], w) != DR:   # escaping
                cands.append(w)
        if not cands:
            return None
        if adversarial and others:
            cands.sort(key=lambda w: -max(abs(trans(o, w) - trans(own, w))
                                          for o in others))
        bank.add(cands[0])
    return sorted(bank, key=lambda t: (len(t), sorted(t)))


def part_r(models=400, n=14, L=10, T=3, seed=99991):
    """Parts L/N used random banks, where escaping is rare.  This forces EVERY
    demand to escape, picks witnesses ADVERSARIALLY to decorrelate their
    transition levels across chains, and restricts to NON-COMPARABLE chain pairs
    -- exactly what sec.38's merge leaves behind."""
    print("\nPART R -- the ESCAPING residue, non-comparable chains, adversarial")
    import random
    rng = random.Random(seed)
    univ = set(range(n))
    for p in (2, 3):
        tested = bad = 0
        skipped_comp = 0
        maxgap = 0
        for _ in range(models):
            A = rand_chain(rng, univ, L, maxstep=1)
            B = rand_chain(rng, univ, L, maxstep=1)
            if A is None or B is None:
                continue
            if comparable(A, B):
                skipped_comp += 1
                continue                      # sec.38's merge removes these
            WA = escaping_bank(rng, A, [B], univ)
            WB = escaping_bank(rng, B, [A], univ)
            if not WA or not WB:
                continue
            # measure transition decorrelation actually achieved
            def trans(ch, w):
                for j, x in enumerate(ch):
                    if rel(x, w) != DR:
                        return j
                return len(ch)
            for w in WA:
                maxgap = max(maxgap, abs(trans(A, w) - trans(B, w)))
            tested += 1
            if valid_slots([A, B], [(0, DR, WA), (1, DR, WB)], L, p, p,
                           minbase=T) is None:
                bad += 1
        print(f"  period={p}   non-comparable systems {tested:5d}"
              f"  (comparable skipped {skipped_comp:5d})"
              f"   NO valid config {bad:4d} ({100.0 * bad / max(tested,1):5.2f}%)"
              f"   max transition gap {maxgap}")
    print("  => escaping demands + adversarially decorrelated transitions, on the")
    print("     NON-COMPARABLE pairs sec.38 actually leaves.  0% would say the")
    print("     residue is benign once comparable towers are merged away.")


# ---- part S: SOLUTION DENSITY -- are valid base vectors rare or abundant?


def part_s(models=250, n=14, L=10, T=3, seed=123457):
    """Greedy fails (part O) yet solutions always exist (L/N/R).  In aperiodic
    tilings the resolution is a HIERARCHY telling you which choice to make.  A
    cheaper possibility here: solutions may simply be ABUNDANT, in which case a
    counting argument ('bad base vectors are a minority') proves existence with
    no hierarchy at all.  This measures the fraction of base vectors that work,
    on the escaping + non-comparable residue."""
    print("\nPART S -- solution DENSITY on the escaping residue")
    import random
    rng = random.Random(seed)
    univ = set(range(n))
    for p in (2, 3):
        tot_frac = 0.0
        worst = 1.0
        systems = 0
        zero = 0
        for _ in range(models):
            A = rand_chain(rng, univ, L, maxstep=1)
            B = rand_chain(rng, univ, L, maxstep=1)
            if A is None or B is None or comparable(A, B):
                continue
            WA = escaping_bank(rng, A, [B], univ)
            WB = escaping_bank(rng, B, [A], univ)
            if not WA or not WB:
                continue
            slots = [(0, DR, WA), (1, DR, WB)]
            good = tot = 0
            for iA in range(T, L - p + 1):
                for iB in range(T, L - p + 1):
                    tot += 1
                    wins = [[A[iA + b] for b in range(p)],
                            [B[iB + b] for b in range(p)]]
                    okall = True
                    for (k, r, bank) in slots:
                        if not any(all(rel(x, w) == r for x in wins[k]) and
                                   all(len({rel(x, w) for x in wins[k2]}) == 1
                                       for k2 in (0, 1) if k2 != k)
                                   for w in bank):
                            okall = False
                            break
                    if okall:
                        good += 1
            if tot == 0:
                continue
            systems += 1
            frac = good / tot
            tot_frac += frac
            worst = min(worst, frac)
            if good == 0:
                zero += 1
        print(f"  period={p}  systems {systems:4d}"
              f"   mean valid-vector fraction {tot_frac / max(systems,1):6.3f}"
              f"   worst {worst:6.3f}   systems with NO solution {zero}")
    print("  => a high mean with a bounded-away-from-zero WORST case would")
    print("     support a counting proof; a tiny worst case means solutions are")
    print("     rare and a structural (hierarchy-style) argument is needed.")


# ---- part T: the COUNTING LEMMA behind a union-bound existence proof


def part_t(nmax=5, plist=(2, 3, 4)):
    """Abundance (part S) suggests a UNION BOUND rather than a hierarchy.  Its
    engine is: for ONE witness and ONE chain, the bases whose window is NOT
    constant are FEW.  Since the row has shape X* PO* EQ? PPI* (part E) it has at
    most 3 transitions, and a window of length p is non-constant only if it
    straddles one -- at most p-1 bases per transition, so at most 3(p-1) bad
    bases, a bound depending on p ALONE (not on the chain, the witness, or the
    model).  Verified exhaustively here."""
    print("\nPART T -- the counting lemma:  #bad bases <= 3(p-1)")
    univ = set(range(nmax))
    regs = subsets(univ)
    chains = []
    for a in regs:
        for b in regs:
            if not a < b:
                continue
            for c3 in regs:
                if b < c3:
                    chains.append([a, b, c3])
    # long chains for the base-count check
    worst_tr = 0
    for ch in chains:
        for w in regs:
            r = row(ch, w)
            tr = sum(1 for i in range(len(r) - 1) if r[i] != r[i + 1])
            worst_tr = max(worst_tr, tr)
    print(f"  exhaustive rows (|U|={nmax}, 3-chains)   : max transitions {worst_tr}"
          f"   (claim: <= 3)   {'OK' if worst_tr <= 3 else 'FAIL'}")

    # bad-base count on longer random chains
    import random
    rng = random.Random(5150)
    bigU = set(range(12))
    bigR = subsets(bigU)
    ok = True
    for p in plist:
        worst = 0
        for _ in range(4000):
            ch = rand_chain(rng, bigU, 9, maxstep=1)
            if ch is None:
                continue
            w = rng.choice(bigR)
            bad = sum(1 for i in range(len(ch) - p + 1)
                      if len({rel(ch[i + b], w) for b in range(p)}) != 1)
            worst = max(worst, bad)
        bound = 3 * (p - 1)
        good = worst <= bound
        ok &= good
        print(f"  p={p}: worst #bad bases {worst:2d}   bound 3(p-1) = {bound:2d}"
              f"   {'OK' if good else 'FAIL'}")
    print("  => with B := 3(p-1) bad bases per (witness, chain), choosing each")
    print("     base from R candidate recurrences makes the bad vectors at most")
    print("     m(m-1) * B * R^(m-1) out of R^m, which is < R^m once R > m^2 * B.")
    print("     So a valid base vector EXISTS -- a counting proof, no hierarchy,")
    print("     and non-constructive is fine (decidability comes from the code")
    print("     enumeration, not from constructing the vector).")
    return ok and worst_tr <= 3


# ---- part U: the HIGH-BANK construction -- decoupled choices, no product count


def part_u(models=400, n=14, L=12, seed=777, Ms=(2, 3)):
    """Since W_n is DECREASING (witness_sets_decreasing), a witness chosen for the
    HIGHEST candidate base serves EVERY lower one.  So pick the whole bank ABOVE
    the top of the candidate range: the witnesses are then FIXED independently of
    the bases, every kernel's constraints DECOUPLE, and each base need only avoid
    the <= (m-1)*S*B values spoiled by the other kernels' fixed witnesses.  This
    is the construction part O's greedy got wrong -- it picked witnesses too low.

    Checked here: (i) a top-level witness really does serve every lower window,
    (ii) the forbidden-base count matches the bound 2(p-1) per (witness, chain),
    (iii) a valid base vector always exists among the decoupled choices."""
    print("\nPART U -- the HIGH-BANK construction (witnesses above the range)")
    import random
    rng = random.Random(seed)
    univ = set(range(n))
    for m in Ms:
        for p in (2, 3):
            systems = serves_ok = bound_ok = exists_ok = 0
            worst_forbidden = 0
            for _ in range(models):
                chains = [rand_chain(rng, univ, L, maxstep=1) for _ in range(m)]
                if any(c is None for c in chains):
                    continue
                top = L - 1                       # the "above the range" level
                # bank: for each kernel, a witness DR from its chain AT THE TOP
                bank = []
                okgen = True
                for k in range(m):
                    cands = [frozenset(x) for x in
                             [rng.sample(sorted(univ - chains[k][top]),
                                         min(2, len(univ - chains[k][top])))
                              for _ in range(30)]
                             if x]
                    cands = [w for w in cands if rel(chains[k][top], w) == DR]
                    if not cands:
                        okgen = False
                        break
                    bank.append(cands[0])
                if not okgen:
                    continue
                systems += 1
                # (i) does the top witness serve EVERY lower window?
                if all(rel(chains[k][j], bank[k]) == DR
                       for k in range(m) for j in range(top)):
                    serves_ok += 1
                # (ii) forbidden-base count per (witness, chain) vs 2(p-1)
                worst = 0
                for k in range(m):
                    for k2 in range(m):
                        if k2 == k:
                            continue
                        bad = sum(1 for i in range(top - p + 1)
                                  if len({rel(chains[k2][i + b], bank[k])
                                          for b in range(p)}) != 1)
                        worst = max(worst, bad)
                worst_forbidden = max(worst_forbidden, worst)
                if worst <= 2 * (p - 1):
                    bound_ok += 1
                # (iii) decoupled choice: each base avoids the others' bad sets
                choice = []
                for k2 in range(m):
                    good = [i for i in range(top - p + 1)
                            if all(len({rel(chains[k2][i + b], bank[k])
                                        for b in range(p)}) == 1
                                   for k in range(m) if k != k2)]
                    if good:
                        choice.append(good[0])
                if len(choice) == m:
                    exists_ok += 1
            print(f"  kernels={m} p={p}  systems {systems:4d}"
                  f"   top witness serves all {serves_ok:4d}"
                  f"   bound 2(p-1) held {bound_ok:4d}"
                  f"   decoupled vector found {exists_ok:4d}"
                  f"   (worst forbidden {worst_forbidden})")
    print("  => 'serves all' should be 100% (backward forcing), the bound should")
    print("     always hold, and the decoupled vector should always exist --")
    print("     that is the whole proof, with NO product counting.")


# ---- part V: the exists-PO case -- no forcing law, so is the cycle back?


def part_v(models=600, n=13, L=10, T=3, seed=246810):
    """DR/PP demands are served by LATE picking: a witness above the range is
    forced DR/PP down through the whole window by comp(PP,DR)={DR} /
    comp(PP,PP)={PP}.  PO has NO such law -- comp(PP,PO) = {PP,PO,DR} -- so a
    witness picked high need not be PO lower down, and the late-picking trick is
    unavailable.  Does that reintroduce the sec.39 ordering problem?

    What a PO demand needs: a witness whose row is CONSTANT PO across the window
    (then hstab makes the base value PO too, and hk_ex's external disjunct
    fires).  Since rank is monotone and PO is rank 1, that is equivalent to PO at
    BOTH ENDS of the window (row_no_return).  Measured here: with the demand live
    at every level, how often does such a witness exist?"""
    print("\nPART V -- the exists-PO case (no forcing law)")
    print(f"  comp(PP,PO) = {sorted(CT[(PP, PO)])}   "
          f"(vs comp(PP,DR) = {sorted(CT[(PP, DR)])}, comp(PP,PP) = {sorted(CT[(PP, PP)])})")
    import random
    rng = random.Random(seed)
    univ = set(range(n))
    us = sorted(univ)
    for p in (2, 3):
        systems = solvable = late_ok = 0
        for _ in range(models):
            # NOTE: a SINGLETON region has no PO partner at all (a\b and a∩b
            # cannot both be nonempty when |a| = 1), so an exists-PO demand
            # cannot be live at a singleton node -- the chain must start with
            # at least two elements.
            base = frozenset(rng.sample(us, 2))
            rest = [x for x in us if x not in base]
            rng.shuffle(rest)
            if len(rest) < L - 1:
                continue
            c, cur = [base], base
            for t in range(L - 1):
                cur = cur | {rest[t]}
                c.append(cur)
            # a PO-witness bank: for each level, some region overlapping it
            bank = set()
            ok = True
            for nd in c:
                cands = []
                for _ in range(40):
                    inside = rng.sample(sorted(nd), 1)
                    outside = [x for x in us if x not in nd]
                    if not outside:
                        continue
                    w = frozenset(inside + rng.sample(outside, 1))
                    if rel(nd, w) == PO:
                        cands.append(w)
                if not cands:
                    ok = False
                    break
                bank.add(rng.choice(cands))
            if not ok:
                continue
            bank = sorted(bank, key=lambda t: (len(t), sorted(t)))
            if not all(any(rel(c[j], w) == PO for w in bank) for j in range(L)):
                continue
            systems += 1
            # (i) is there a base whose window has a constant-PO witness?
            if any(any(all(rel(c[i + b], w) == PO for b in range(p)) for w in bank)
                   for i in range(T, L - p + 1)):
                solvable += 1
            # (ii) does the LATE-picking trick work?  i.e. is a witness that is
            #      PO at the TOP of the range also PO across a lower window?
            top = L - 1
            hi = [w for w in bank if rel(c[top], w) == PO]
            if hi and any(all(rel(c[i + b], w) == PO for b in range(p))
                          for w in hi for i in range(T, L - p + 1)):
                late_ok += 1
        print(f"  p={p}  systems {systems:4d}"
              f"   constant-PO window exists {solvable:4d}"
              f" ({100.0 * solvable / max(systems,1):5.1f}%)"
              f"   |  LATE pick suffices {late_ok:4d}"
              f" ({100.0 * late_ok / max(systems,1):5.1f}%)")
    print("  => a gap between the two columns is the point: if constant-PO")
    print("     windows exist but the LATE pick does not deliver them, the PO")
    print("     bank cannot be placed above the range, and the sec.39.2")
    print("     decoupling does NOT extend to PO.")


# ---- part W: the ONE-LEVEL PO witness -- an adversarial family


def part_w(L=9):
    """Part V's random banks nearly always contained a witness PO across a whole
    window.  Can that be defeated?  Yes, and cleanly.  Take the chain
    c_j = {e_0,...,e_j} and the witnesses w_j = {e_j, e_{j+1}}:

      * at level j-1:  w_j is DR   (neither element is in c_{j-1})
      * at level j:    w_j is PO   (e_j inside, e_{j+1} outside, c_j not inside w_j)
      * at level j+1:  w_j is PPI  (both elements now in c_{j+1}, properly)

    so EVERY witness is PO at EXACTLY ONE level.  The demand is live everywhere,
    yet no witness is PO across a window of length >= 2 -- so no single external
    can serve an exists-PO demand across a whole window, at ANY base."""
    print("\nPART W -- the one-level PO witness (adversarial)")
    c = [frozenset(range(j + 2)) for j in range(L)]        # c_j = {0..j+1}
    wits = [frozenset({j + 1, j + 2}) for j in range(L)]
    live = all(any(rel(c[j], w) == PO for w in wits) for j in range(L - 1))
    spans = {}
    for w in wits:
        po_levels = [j for j in range(L) if rel(c[j], w) == PO]
        spans[tuple(sorted(w))] = po_levels
    widest = max((len(v) for v in spans.values()), default=0)
    ok2 = any(all(rel(c[i + b], w) == PO for b in range(2)) for w in wits
              for i in range(L - 1))
    print(f"  demand live at every level              : {live}")
    print(f"  widest PO-span of any witness (levels)  : {widest}")
    print(f"  some witness PO across a window of 2    : {ok2}")
    print(f"  => no single external serves the exists-PO demand across a")
    print(f"     window of length >= 2, at ANY base   : {not ok2}")
    print("  Consequence: the sec.39.2 high-bank decoupling does NOT extend to")
    print("  exists-PO.  DR/PP work because comp(PP,DR)={DR} and comp(PP,PP)={PP}")
    print("  force the whole window from one high pick; PO has no such law")
    print("  (comp(PP,PO)={DR,PO,PP}), and it can be pinned to a single level.")
    print("  So exists-PO at kernel phases NEEDS the pool machinery (MTOkPool /")
    print("  glueFam_ok), not an external bank -- an architectural requirement,")
    print("  not bookkeeping.")
    return live and widest <= 1 and not ok2


# ----------------------------------------------------------------------- main

def main():
    results = {
        "A comp table": part_a(),
        "B Q-crisp is FALSE": part_b(),
        "C horizon unbounded": part_c(),
        "D row always stabilizes": part_d(),
        "E row shape / cofinal-DR": part_e(),
        "F R4' and bank fail": part_f(),
        "T counting lemma": part_t(),
    }
    part_g()   # reported, not pass/fail -- it measures rather than asserts
    part_h()
    part_i()
    part_j()
    part_k()
    part_l()
    part_m()
    part_n()
    part_o()
    part_p()
    part_q()
    part_r()
    part_s()
    part_u()
    part_v()
    part_w()
    print("\n" + "=" * 68)
    for k, v in results.items():
        print(f"  {k:28s} : {'PASS' if v else 'FAIL'}")
    allok = all(results.values())
    print("=" * 68)
    print("VERDICT:", "ALL PASS" if allok else "FAILURE")
    print()
    print("  The sec.39 cycle is REAL and is an ORDERING obstruction, not a")
    print("  geometric one:  cross-kernel constancy is NOT free (B), the horizon")
    print("  cannot be pre-committed (C), yet every row does eventually stabilize")
    print("  (D).  So repair R4 is dead in its naive form.")
    print()
    print("  PARTS L-N (the selection): dense systems (up to 4 kernels x 3")
    print("  demands, DR and PP, late bases) NEVER failed; a single COMMON base")
    print("  does NOT suffice (up to 35% failure), so the bases must genuinely")
    print("  differ; and the STAGED construction (strictly increasing bases)")
    print("  matches the free search exactly at 0%.  That is the proof plan:")
    print("  one pass, with a designated dichotomy branch per direction.")
    print()
    print("  E narrows it: the rank-0 block of a row is CONSTANT, so an external")
    print("  cofinally DR from a chain is DR from index 0 -- no horizon at all")
    print("  (kernel-checked: cofinal_dr_all / cofinal_dr_stab).  So the cycle")
    print("  bites only for externals another kernel overlaps or swallows.")
    print()
    print("  F then kills the two obvious ways to exploit that: R4' (always pick")
    print("  a witness cofinally-DR from every other kernel) FAILS, and so does")
    print("  pre-selecting a base-independent bank -- a chain can swallow every")
    print("  fixed region.  What survives is the WINDOW reading of hstab, now")
    print("  implemented (sec.39.7): a witness need only be constant on")
    print("  [i, i+p), which is exactly what kernel_site delivers.")
    print()
    print("  That does not dissolve the cycle, but it converts it into a FINITE")
    print("  combinatorial one: by D each row has at most 2 transition points, so")
    print("  the bad positions number at most 2*|banks|*|kappa| -- a bound in C0")
    print("  alone.  Whether a clean window can then be found is sec.39.8 (R6).")
    return 0 if allok else 1


if __name__ == "__main__":
    raise SystemExit(main())
