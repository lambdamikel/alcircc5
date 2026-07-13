#!/usr/bin/env python3
"""
WP28 -- Machine checks for the round-16 repair: JOINT steering via
certified steering functions (papers/fable5_round16/), replacing the
round-15 pairwise condition (Q4) that the tenth review broke at W1a.

THE REPAIR UNDER TEST.  Round 16 makes the steering data part of the
certificate: for each gluing edge, a STEERING FUNCTION f assigning to
every reachable interface STATE (type, row-over-separator) one fixed row
of values to the fresh members.  The canonical completion is then
DETERMINISTIC -- every cross value in the unfolding is f-generated -- and
all closure obligations become finitely checkable conditions on f over
the reachable singleton and pair states:

  (S1) through-separator: f(t,r)(b) in Comp(r(s), N(s,b)) for all s;
  (S2) safety:            f(t,r)(b) in Safe(t, tau(b));
  (S3) fresh edges:       f(t,r)(b') in Comp(f(t,r)(b), N(b,b'));
  (S4) pair condition:    for every reachable pair of states with
       realized mutual value W:  f(t,r)(b) in Comp(W, f(t',r')(b)).

The tenth review's W1a witness is rejected because NO f exists (the pair
condition with W = PP forces f(Y-state)(b) in Comp(PP, DR) = {DR},
excluded by Safe(Y,B) = {PO}).

Parts:

  A  THE W1a WITNESS UNDER (Q4').  A1: the tenth review's exact
     configuration admits NO steering function -- the round-16 condition
     REJECTS what the round-15 pairwise condition wrongly accepted
     (and rejection is correct: the configuration is semantically
     unrealizable -- y inside z and z disjoint from b force y DR b,
     which Safe(Y,B) forbids; machine-checked here).  A2: the repaired
     sibling (Safe(Y,B) = {DR}) admits f, and the resulting joint
     completion exists.

  B  SOUNDNESS AND UNIFORMIZATION RATES ON RANDOM GLUE STEPS.  Random
     realized cluster-tree frames + a fresh glued pattern + random
     per-pair safe domains (built WITHOUT hard-wiring any selector --
     the WP26 Part-B mistake is not repeated):
       B1 (soundness of (Q4')): whenever a steering function exists,
          the induced joint assignment is composition-closed and a full
          completion exists.  Expected: 100%.
       B2 (the residual keystone W2', measured): among instances where
          SOME joint (possibly non-uniform) assignment exists, how often
          does a UNIFORM steering function exist?  A gap here is the
          uniformization obligation that round-16's extraction
          designates as its open lemma; this part quantifies it
          empirically instead of hiding it.
       B3 (regression): the W1a family (selector-unsafe disjunction
          branches) is rejected by (Q4') exactly when no joint
          assignment exists -- no false accepts observed.

Run:  python3 verification/python/wp28_round16_joint_steering.py
"""

import itertools
import random
import sys

BASE = ('EQ', 'PP', 'PPI', 'PO', 'DR')
NONEQ = ('PP', 'PPI', 'PO', 'DR')
HOR = ('DR', 'PO')
CONV = {'EQ': 'EQ', 'PP': 'PPI', 'PPI': 'PP', 'PO': 'PO', 'DR': 'DR'}


def derive_comp(n=5):
    U = range(n)
    subs = [frozenset(c) for k in range(1, n + 1)
            for c in itertools.combinations(U, k)]

    def rel(a, b):
        if a == b:
            return 'EQ'
        if not a & b:
            return 'DR'
        if a < b:
            return 'PP'
        if b < a:
            return 'PPI'
        return 'PO'

    t = {(r, s): set() for r in BASE for s in BASE}
    for a in subs:
        for b in subs:
            r = rel(a, b)
            for c in subs:
                t[(r, rel(b, c))].add(rel(a, c))
    return {k: frozenset(v) for k, v in t.items()}


COMP = derive_comp(5)


def net_set(N, i, j, r):
    N[(i, j)] = r
    N[(j, i)] = CONV[r]


def is_closed(N, V):
    for i in V:
        for j in V:
            if i == j:
                continue
            for k in V:
                if k in (i, j):
                    continue
                if N[(i, k)] not in COMP[(N[(i, j)], N[(j, k)])]:
                    return False
    return True


def pc_complete(V, known, domains=None, rng=None):
    dom = {}
    for i in V:
        for j in V:
            if i == j:
                continue
            if (i, j) in known:
                dom[(i, j)] = frozenset([known[(i, j)]])
            elif domains and (i, j) in domains:
                dom[(i, j)] = frozenset(domains[(i, j)])
            else:
                dom[(i, j)] = frozenset(NONEQ)

    def pc(dom):
        changed = True
        while changed:
            changed = False
            for i in V:
                for j in V:
                    if i == j:
                        continue
                    dij = dom[(i, j)]
                    for k in V:
                        if k in (i, j):
                            continue
                        allowed = set()
                        for a in dom[(i, k)]:
                            for b in dom[(k, j)]:
                                allowed |= COMP[(a, b)]
                        new = dij & allowed
                        if new != dij:
                            dom[(i, j)] = frozenset(new)
                            dom[(j, i)] = frozenset(CONV[r] for r in new)
                            dij = dom[(i, j)]
                            changed = True
                        if not dij:
                            return False
        return True

    if not pc(dom):
        return None

    def rec(dom):
        und = [(p, d) for p, d in dom.items() if len(d) > 1 and p[0] < p[1]]
        if not und:
            N = {p: next(iter(d)) for p, d in dom.items()}
            return N if is_closed(N, V) else None
        und.sort(key=lambda t: len(t[1]))
        pair, d = und[0]
        vals = list(d)
        if rng is not None:
            rng.shuffle(vals)
        for r in vals:
            nd = dict(dom)
            nd[pair] = frozenset([r])
            nd[(pair[1], pair[0])] = frozenset([CONV[r]])
            if pc(nd):
                res = rec(nd)
                if res is not None:
                    return res
        return None

    return rec(dom)


# ------------------------------------------------------ steering search --

def glue_step_data(frame, elems, sep, fresh, patt, domains):
    """Package one gluing step: old elements (not in sep) with their
    rows over sep and pairwise realized values; fresh members with
    pattern network; per-pair domains."""
    old = [y for y in elems if y not in sep]
    rows = {y: tuple(frame[(y, s)] for s in sep) for y in old}
    mutual = {(y, z): frame[(y, z)] for y in old for z in old if y != z}
    return old, rows, mutual


def state_of(y, rows, domains, fresh):
    """Interface state of an old element: its row over the separator plus
    its safety signature toward the fresh members (the round-16 state)."""
    sig = tuple(tuple(sorted(domains[(y, b)])) for b in fresh)
    return (rows[y], sig)


def find_steering(old, rows, mutual, sep, fresh, patt, domains, frame):
    """Search for a steering function f: state -> (value per fresh member)
    satisfying (S1)-(S4).  Returns f (dict) or None."""
    states = {}
    for y in old:
        states.setdefault(state_of(y, rows, domains, fresh), []).append(y)
    state_list = list(states)

    # candidate rows per state: product of per-fresh domains, filtered by
    # (S1) through-separator and (S3) fresh-edge closure
    def candidates(st):
        row, sig = st
        per_fresh = []
        for i, b in enumerate(fresh):
            dom = set(sig[i])
            # (S1): v in Comp(row(s), N(s,b)) for every separator member
            for j, s in enumerate(sep):
                dom &= COMP[(row[j], patt[(s, b)])]
            if not dom:
                return []
            per_fresh.append(sorted(dom))
        out = []
        for combo in itertools.product(*per_fresh):
            ok = True
            for i, b in enumerate(fresh):
                for i2, b2 in enumerate(fresh):
                    if b2 == b:
                        continue
                    if combo[i2] not in COMP[(combo[i], patt[(b, b2)])]:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                out.append(combo)
        return out

    cand = {st: candidates(st) for st in state_list}
    if any(not c for c in cand.values()):
        return None

    # realized mutual values between instances of each state pair
    pairW = {}
    for y in old:
        for z in old:
            if y == z:
                continue
            key = (state_of(y, rows, domains, fresh),
                   state_of(z, rows, domains, fresh))
            pairW.setdefault(key, set()).add(mutual[(y, z)])

    def compatible(st1, c1, st2, c2):
        for W in pairW.get((st1, st2), ()):
            for i in range(len(fresh)):
                if c1[i] not in COMP[(W, c2[i])]:
                    return False
        return True

    # backtracking over states
    assign = {}

    def rec(idx):
        if idx == len(state_list):
            return True
        st = state_list[idx]
        for c in cand[st]:
            ok = True
            for st2, c2 in assign.items():
                if not (compatible(st, c, st2, c2) and
                        compatible(st2, c2, st, c)):
                    ok = False
                    break
            if ok and compatible(st, c, st, c):
                assign[st] = c
                if rec(idx + 1):
                    return True
                del assign[st]
        return False

    if rec(0):
        return {st: assign[st] for st in state_list}
    return None


def joint_assignment_exists(elems, frame, sep, fresh, patt, domains):
    """Ground truth: does ANY (possibly non-uniform) joint assignment
    within the domains complete to a closed frame?"""
    known = dict(frame)
    known.update(patt)
    allv = elems + fresh
    return pc_complete(allv, known, domains=domains) is not None


def apply_steering(elems, frame, sep, fresh, patt, domains, f, rows):
    """Assign cross values per f and check full closure."""
    known = dict(frame)
    known.update(patt)
    old = [y for y in elems if y not in sep]
    for y in old:
        st = state_of(y, rows, domains, fresh)
        for i, b in enumerate(fresh):
            net_set(known, y, b, f[st][i])
    allv = elems + fresh
    return pc_complete(allv, known) is not None


# ---------------------------------------------------------------- Part A --

def part_a():
    # The tenth review's witness: old y PP z PP s (y PP s); fresh s PPI b.
    frame = {}
    for (i, j, r) in [('y', 'z', 'PP'), ('z', 's', 'PP'), ('y', 's', 'PP')]:
        net_set(frame, i, j, r)
    elems = ['y', 'z', 's']
    sep = ['s']
    fresh = ['b']
    patt = {}
    net_set(patt, 's', 'b', 'PPI')
    doms_bad = {('y', 'b'): frozenset({'PO'}), ('b', 'y'): frozenset({'PO'}),
                ('z', 'b'): frozenset({'DR'}), ('b', 'z'): frozenset({'DR'})}
    old, rows, mutual = glue_step_data(frame, elems, sep, fresh, patt,
                                       doms_bad)
    f = find_steering(old, rows, mutual, sep, fresh, patt, doms_bad, frame)
    joint = joint_assignment_exists(elems, frame, sep, fresh, patt, doms_bad)
    # semantic unrealizability: y PP z and z DR b force y DR b
    forced = COMP[('PP', 'DR')]
    a1 = (f is None) and (not joint) and forced == frozenset({'DR'})
    print("A1 tenth-review W1a witness under (Q4'):")
    print(f"    steering function exists: {f is not None}; joint "
          f"assignment exists: {joint}; comp(PP,DR)={sorted(forced)}")
    print(f"    (Q4') REJECTS the witness -- and rejection is semantically"
          f" correct: {'PASS' if a1 else 'FAIL'}")

    doms_ok = {('y', 'b'): frozenset({'DR'}), ('b', 'y'): frozenset({'DR'}),
               ('z', 'b'): frozenset({'DR'}), ('b', 'z'): frozenset({'DR'})}
    f2 = find_steering(old, rows, mutual, sep, fresh, patt, doms_ok, frame)
    ok2 = f2 is not None and apply_steering(elems, frame, sep, fresh, patt,
                                            doms_ok, f2, rows)
    print(f"A2 repaired sibling (Safe(Y,B)={{DR}}): steering function found"
          f" and induced completion closed: {'PASS' if ok2 else 'FAIL'}")
    return a1 and ok2


# ---------------------------------------------------------------- Part B --

def rand_cluster_tree_frame(rng, n_clusters=4):
    fresh_ids = itertools.count()
    v0 = [f'e{next(fresh_ids)}' for _ in range(rng.randint(2, 3))]
    frame = pc_complete(v0, {}, rng=rng)
    elems = list(v0)
    for _ in range(n_clusters - 1):
        sep = rng.sample(elems, min(len(elems), rng.randint(1, 2)))
        new = [f'e{next(fresh_ids)}' for _ in range(rng.randint(1, 2))]
        known = dict(frame)
        allv = elems + new
        frame = pc_complete(allv, known, rng=rng)
        if frame is None:
            return None
        elems = allv
    return elems, frame


def part_b(trials=300, seed=201):
    rng = random.Random(seed)
    n = 0
    sound_fail = 0
    joint_yes = 0
    uniform_yes = 0
    q4p_accepts = 0
    false_accept = 0
    attempts = 0
    while n < trials and attempts < trials * 40:
        attempts += 1
        made = rand_cluster_tree_frame(rng, rng.randint(3, 5))
        if made is None:
            continue
        elems, frame = made
        sep = rng.sample(elems, min(len(elems), rng.randint(1, 2)))
        fresh = [f'b{i}' for i in range(rng.randint(1, 2))]
        sepn = {(i, j): frame[(i, j)] for i in sep for j in sep if i != j}
        patt = pc_complete(sep + fresh, dict(sepn), rng=rng)
        if patt is None:
            continue
        # random per-pair domains: nonempty random subsets of the pair's
        # feasible set -- NO selector hard-wiring
        known = dict(frame)
        known.update(patt)
        allv = elems + fresh
        cross = [(y, b) for y in elems if y not in sep for b in fresh]
        domains = {}
        ok = True
        for (y, b) in cross:
            feas = [v for v in NONEQ
                    if pc_complete(allv, {**known, (y, b): v,
                                          (b, y): CONV[v]}) is not None]
            if not feas:
                ok = False
                break
            k = rng.randint(1, len(feas))
            dom = frozenset(rng.sample(feas, k))
            domains[(y, b)] = dom
            domains[(b, y)] = frozenset(CONV[v] for v in dom)
        if not ok:
            continue
        n += 1
        old, rows, mutual = glue_step_data(frame, elems, sep, fresh, patt,
                                           domains)
        f = find_steering(old, rows, mutual, sep, fresh, patt, domains,
                          frame)
        joint = joint_assignment_exists(elems, frame, sep, fresh, patt,
                                        domains)
        if joint:
            joint_yes += 1
        if f is not None:
            q4p_accepts += 1
            if not apply_steering(elems, frame, sep, fresh, patt, domains,
                                  f, rows):
                sound_fail += 1
            if not joint:
                false_accept += 1
        if joint and f is not None:
            uniform_yes += 1
    print(f"Part B: {n} random glue steps with selector-free random safe "
          f"domains")
    print(f"    B1 soundness: (Q4')-accepted steps whose f-induced "
          f"completion is closed: {q4p_accepts - sound_fail}/{q4p_accepts} "
          f"({'PASS' if sound_fail == 0 else 'FAIL'})")
    print(f"    B3 no false accepts ((Q4') accepts but no joint assignment "
          f"exists): {false_accept} ({'PASS' if false_accept == 0 else 'FAIL'})")
    print(f"    B2 uniformization rate (the W2' keystone, measured): "
          f"{uniform_yes}/{joint_yes} jointly-realizable steps admit a "
          f"UNIFORM steering function "
          f"({100.0 * uniform_yes / max(joint_yes, 1):.1f}%)")
    if uniform_yes < joint_yes:
        print(f"    NOTE: {joint_yes - uniform_yes} instances are "
              f"joint-realizable but not state-uniform -- the honest "
              f"measure of the round-16 extraction obligation (W2').")
    return sound_fail == 0 and false_accept == 0


if __name__ == '__main__':
    print(__doc__.split('\n')[1])
    print('=' * 70)
    r = [part_a(), part_b()]
    print('=' * 70)
    print("WP28 OVERALL:", "PASS" if all(r) else "ATTENTION: see above")
    sys.exit(0 if all(r) else 1)
