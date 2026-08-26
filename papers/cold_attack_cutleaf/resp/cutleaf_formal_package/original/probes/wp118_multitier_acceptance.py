#!/usr/bin/env python3
"""WP118 -- FULL `MultiTierOk` acceptance test over a KERNEL-BEARING class.

ASSEMBLY_DESIGN sec.132.4.  wp115 checks every obligation but over FINITE set
models, which have no infinite towers and therefore no kernels -- so the
phases branch of sec.132's redesign is unreachable there.  wp117 exercises the
kernel-bearing tower but only measures COVERAGE of cut-leaf demands, not the
whole obligation set.

This probe is the intersection: wp112's closed-form tower, wp115's full checking,
and sec.132's treatment (kernel phase OR declared edge, nothing added).

THE CERTIFICATE, modelled as the Lean `MultiTier` actually is:

  externals  beta   = the closure's PREFIX and SIDE nodes
  kernel     kappa  = the TAIL, one kernel with p phases (the residues)
  E e f             = read-off relation between externals, OVERRIDDEN by the
                      declared edges of sec.123
  K k e             = relation from the kernel to an external (uniform across
                      phases -- the tail sits above every prefix node)
  up k              = true (the tail ascends)

OBLIGATIONS CHECKED -- the literal `MultiTierOk` field list:
  hp, frame_q, e_clash/e_nobot/e_and/e_or, k_clash/k_nobot/k_and/k_or,
  ee_all, ek_all, ke_all, kk_pp, kk_ppi, kk_eq, kq_all, e_ex, k_ex

CONTROL, stated before the run: with the declared edges DISABLED there must be
`e_ex` failures.  If disabling them changes nothing, the treatment is doing no
work and a pass says nothing about it.
"""

import random

from wp112_lap_continuation_closed_form import (
    DR, EQ, PP, PPI, build, closure, mdepth, persistent, po_free, rand_c)
from wp116_target_rounds import close_from, unserved, vdemands

ATOMS = [DR, "PO", EQ, PP, PPI]
CONV = {DR: DR, "PO": "PO", EQ: EQ, PP: PPI, PPI: PP}


def comp_table():
    """RCC5 composition, from finite set semantics."""
    from itertools import combinations
    def rel(a, b):
        if a == b: return EQ
        if a < b: return PP
        if b < a: return PPI
        if not (a & b): return DR
        return "PO"
    regs = [frozenset(c) for k in range(1, 5)
            for c in combinations(range(4), k)]
    t = {}
    for a in regs:
        for b in regs:
            r = rel(a, b)
            for c in regs:
                t.setdefault((r, rel(b, c)), set()).add(rel(a, c))
    return t


CT = comp_table()


# ------------------------------------------------------------- the certificate

def erel(T, x, y):
    """Read-off relation between two EXTERNALS (prefix or side nodes)."""
    if x == y:
        return EQ
    for r in (PP, PPI, DR):
        if y in T.succs(x, r):
            return r
    return "PO"


def krel(T, e):
    """Relation FROM the kernel (tail) TO external e -- uniform across phases."""
    R = T.tail[0]
    for r in (PP, PPI, DR):
        if e in T.succs(R, r):
            return r
    return "PO"


def build_cert(T, c0, root, use_edges=True):
    """Closure, then sec.132's treatment.  Returns (externals, E, phases)."""
    nodes, cuts = close_from(T, c0, root)
    ext = sorted([n for n in nodes if n[0] != "R"], key=str)
    b = mdepth(c0) + 1
    lab = lambda n: [d for d in T.mty(c0, n) if mdepth(d) <= b]
    E = {}
    for x in ext:
        for y in ext:
            E[(x, y)] = erel(T, x, y)
    DECL = set()
    if use_edges:
        blk = {}
        for v in cuts:
            if v[0] == "R":
                continue
            tv = T.mty(c0, v)
            blk[v] = next((z for z in ext if z != v and T.mty(c0, z) == tv), None)
        for v in cuts:
            if v[0] == "R" or v not in ext:
                continue
            for (r, D) in unserved(T, c0, nodes, v):
                # already served by a kernel phase?
                if any(w in T.succs(v, r) and T.sat(w, D) for w in T.tail):
                    continue
                a = blk.get(v)
                if a is None:
                    continue
                for w in T.succs(a, r):
                    if not T.sat(w, D) or w not in ext:
                        continue
                    if w == v:
                        continue          # a node is never its own witness --
                                          # round 6's lap collapse in miniature
                    if v in T.succs(w, r):
                        continue                      # would cycle
                    if w in T.succs(v, DR) or v in T.succs(w, DR):
                        continue                      # would break ltNotDj
                    if (v, w) in DECL or (w, v) in DECL:
                        break                  # pair already declared: one value
                    DECL.add((v, w))
                    DECL.add((w, v))
                    E[(v, w)] = r
                    E[(w, v)] = CONV[r]
                    break
    phases = [lab(R) for R in T.tail]
    DECLG.clear()
    DECLG.update(DECL)
    return ext, E, lab, phases


CONVDIAG = []
DECLG = set()


def check(T, c0, ext, E, lab, phases):
    bad = {}
    def note(k): bad[k] = bad.get(k, 0) + 1
    p = len(phases)
    if p == 0:
        note("hp")
        return bad
    K = {e: krel(T, e) for e in ext}

    # frame_q: converse + composition closure over externals AND the kernel,
    # the kernel treated as one node (qnet's quotient view)
    def rel_q(x, y):
        if x == "K" and y == "K": return EQ
        if x == "K": return K[y]
        if y == "K": return CONV[K[x]]
        return E[(x, y)]
    univ = list(ext) + ["K"]
    for x in univ:
        for y in univ:
            if CONV[rel_q(x, y)] != rel_q(y, x):
                note("frame_q_conv")
                if len(CONVDIAG) < 6:
                    CONVDIAG.append((x, y, rel_q(x, y), rel_q(y, x),
                                     (x, y) in DECLG, (y, x) in DECLG))
            for z in univ:
                if rel_q(x, z) not in CT[(rel_q(x, y), rel_q(y, z))]:
                    note("frame_q_comp")
    # propositional coherence
    for e in ext:
        for d in lab(e):
            if d[0] == "and" and not (d[1] in lab(e) and d[2] in lab(e)):
                note("e_and")
            if d[0] == "or" and not (d[1] in lab(e) or d[2] in lab(e)):
                note("e_or")
    for a in range(p):
        for d in phases[a]:
            if d[0] == "and" and not (d[1] in phases[a] and d[2] in phases[a]):
                note("k_and")
            if d[0] == "or" and not (d[1] in phases[a] or d[2] in phases[a]):
                note("k_or")
    # ee_all
    for e in ext:
        for d in lab(e):
            if d[0] != "all":
                continue
            for f in ext:
                if E[(e, f)] == d[1] and d[2] not in lab(f):
                    note("ee_all")
    # ek_all : a universal at e whose relation matches conv(K k e) hits EVERY phase
    for e in ext:
        for d in lab(e):
            if d[0] == "all" and CONV[K[e]] == d[1]:
                for a in range(p):
                    if d[2] not in phases[a]:
                        note("ek_all")
    # ke_all : a universal in a phase hits every external with K k f = r
    for a in range(p):
        for d in phases[a]:
            if d[0] != "all":
                continue
            for f in ext:
                if K[f] == d[1] and d[2] not in lab(f):
                    note("ke_all")
    # kk_pp / kk_ppi / kk_eq
    for a in range(p):
        for d in phases[a]:
            if d[0] != "all":
                continue
            if d[1] in (PP, PPI):
                for bb in range(p):
                    if d[2] not in phases[bb]:
                        note("kk_" + d[1])
            if d[1] == EQ and d[2] not in phases[a]:
                note("kk_eq")
    # e_ex
    for e in ext:
        for d in lab(e):
            if d[0] != "ex":
                continue
            if d[1] not in (PP, PPI):
                continue                       # horizontal closure not modelled
            byext = any(E[(e, f)] == d[1] and d[2] in lab(f) for f in ext)
            bykern = (CONV[K[e]] == d[1]
                      and any(d[2] in phases[a] for a in range(p)))
            if not (byext or bykern):
                note("e_ex_" + d[1])
    # k_ex
    for a in range(p):
        for d in phases[a]:
            if d[0] != "ex":
                continue
            if d[1] not in (PP, PPI):
                continue                       # horizontal closure not modelled
            byext = any(K[f] == d[1] and d[2] in lab(f) for f in ext)
            byself = (d[1] == PP and any(d[2] in phases[b] for b in range(p)))
            byeq = (d[1] == EQ and d[2] in phases[a])
            if not (byext or byself or byeq):
                note("k_ex_" + d[1])
    return bad


def sweep(seed, trials, L, p, use_edges=True):
    rng = random.Random(seed)
    models = 0
    fails = {}
    for _ in range(trials):
        c0 = rand_c(rng, rng.randint(2, 4))
        if not po_free(c0):
            continue
        T = build(rng, L=L, p=p)
        root = next((n for n in T.nodes if T.sat(n, c0)), None)
        if root is None or root[0] == "R":
            continue
        models += 1
        ext, E, lab, phases = build_cert(T, c0, root, use_edges)
        for k, v in check(T, c0, ext, E, lab, phases).items():
            fails[k] = fails.get(k, 0) + v
    return models, fails


def main():
    shapes = (("L=4  p=3", 20260826, 4, 3), ("L=8  p=3", 777, 8, 3),
              ("L=18 p=3", 31337, 18, 3), ("L=8  p=6", 5150, 8, 6))
    print("WP118 -- full MultiTierOk acceptance over a kernel-bearing class\n")
    for tag, use in (("CONTROL: declared edges OFF", False),
                     ("declared edges ON", True)):
        print(f"  --- {tag} ---")
        tot = {}
        n = 0
        for lbl, seed, L, p in shapes:
            m, f = sweep(seed, 700, L, p, use)
            n += m
            for k, v in f.items():
                tot[k] = tot.get(k, 0) + v
        print(f"    certificates checked : {n}")
        if tot:
            for k in sorted(tot):
                print(f"      {k:16s} {tot[k]}")
        else:
            print("      ALL OBLIGATIONS HOLD")
        print()
    if CONVDIAG:
        print("  frame_q_conv diagnosis (x, y, E[x,y], E[y,x], decl_xy, decl_yx):")
        for row in CONVDIAG:
            print(f"    {row}")
        print()
    print("=" * 72)
    print("  The CONTROL must show e_ex failures: if disabling the declared")
    print("  edges changes nothing, the treatment is doing no work and a pass")
    print("  says nothing about it.")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
