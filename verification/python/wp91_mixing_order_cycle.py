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


# ----------------------------------------------------------------------- main

def main():
    results = {
        "A comp table": part_a(),
        "B Q-crisp is FALSE": part_b(),
        "C horizon unbounded": part_c(),
        "D row always stabilizes": part_d(),
        "E row shape / cofinal-DR": part_e(),
        "F R4' and bank fail": part_f(),
    }
    part_g()   # reported, not pass/fail -- it measures rather than asserts
    part_h()
    part_i()
    part_j()
    part_k()
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
