#!/usr/bin/env python3
"""rev4 -- does the N artifact reach wp101's other parts too?"""
import random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp101_periodic_oneshot_vertical as W

PP = W.PP
TOP = W.Reg(True, ())
NATOMS = 2


def has_top(m):
    return any(s == TOP for s in m.sides)


def part_a_split(trials=600, seed=101101):
    rng = random.Random(seed)
    hi = 40
    st = {True: [0, 0], False: [0, 0]}     # has_top -> [persistent, oneshot]
    for _ in range(trials):
        c0 = W.rand_concept(rng, rng.randint(2, 3))
        m = W.build_model(rng)
        t = has_top(m)
        for i in range(m._stab, m._stab + 2 * m.p):
            for d in W.closure(c0):
                if d[0] != "ex" or d[1] != PP:
                    continue
                if not m.sat_chain(i, d, hi):
                    continue
                if m.sat_chain(i, ("all", PP, d), hi):
                    st[t][0] += 1
                else:
                    st[t][1] += 1
    print("PART A (validity: 'persistent demands appear at all'), split by N")
    for k in (True, False):
        p, o = st[k]
        tot = p + o
        if tot:
            print(f"   models {'WITH' if k else 'WITHOUT'} N: n={tot:6d}  "
                  f"persistent {p:6d} ({100*p/tot:5.1f}%)  "
                  f"one-shot {o:6d} ({100*o/tot:5.1f}%)")
    p, o = st[True]
    if p + o:
        print(f"   -> inside N-models the one-shot rate is "
              f"{100*o/(p+o):.1f}%; wp100 reported 100% and was retired for it.")


def occ_filter_split(trials, seed, name, window_mult, need_top_quarter):
    """Common shape of parts B/C/E: count qualifying demands, split by N."""
    rng = random.Random(seed)
    hi = 60
    st = {True: 0, False: 0}
    for _ in range(trials):
        c0 = W.rand_concept(rng, rng.randint(2, 3))
        m = W.build_model(rng)
        t = has_top(m)
        for d in W.closure(c0):
            if d[0] != "ex" or d[1] != PP:
                continue
            WIN = window_mult * m.p
            occ = [i for i in range(m._stab, m._stab + WIN)
                   if m.sat_chain(i, d, hi)
                   and not m.sat_chain(i, ("all", PP, d), hi)]
            if need_top_quarter:
                if not occ or len([i for i in occ
                                   if i > m._stab + 3 * WIN // 4]) < m.p:
                    continue
            else:
                if len(occ) < 2 * m.p:
                    continue
            st[t] += 1
    tot = st[True] + st[False]
    print(f"{name}: qualifying demands n={tot}   "
          f"from N-models {st[True]} ({100*st[True]/tot if tot else 0:.1f}%)   "
          f"from non-N models {st[False]}")


if __name__ == "__main__":
    print("=" * 74)
    part_a_split()
    print()
    occ_filter_split(600, 202202, "PART B population", 3, False)
    occ_filter_split(600, 303303, "PART C population", 3, False)
    occ_filter_split(1200, 505505, "PART E population (pre in-kernel cut)",
                     64, True)
    print("=" * 74)
