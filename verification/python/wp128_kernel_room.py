#!/usr/bin/env python3
"""WP128 -- must a kernel chain leave room for a disjoint external?

ASSEMBLY_DESIGN sec.168.3.  `mKdr` asks for a SINGLE external disjoint from a
kernel's ENTIRE chain.  If a kernel chain can exhaust its space, no such external
exists and each phase's exists-DR demand has its own witness with no common one --
which the certificate cannot express, since K k f is one relation per
(kernel, external) pair.

The concept under test, forall-PO-free by inspection (no forall-PO anywhere):

    C0 = exists-PP.TOP  AND  forall-PP.( exists-PP.TOP  AND  exists-DR.A )

It forces an infinite ascending chain (the exists-PP.TOP demand is guarded by
forall-PP, so it is PERSISTENT -- a kernel) and an exists-DR.A demand at every
chain point.

TWO MODELS, both over subsets of a universe:

  EXHAUSTING   chain a_i = {0..i}, A on singletons.  Union of the chain is
               everything, so NO region is disjoint from all of it.
  ROOMY        same chain inside column 0 of N x {0,1}; A on {(0,1)}, which is
               disjoint from the whole chain.

If C0 holds in both, then mKdr FAILS in one and HOLDS in the other, so the
answer to sec.168.3 is: not every model leaves room, but some does -- and the
gap is model CHOICE, not the logic.

CONTROL, stated before the run: C0 must be satisfied at the chain root in BOTH
models.  If it fails in either, the concept is not testing what is claimed.
"""

N = 60          # chain length used to approximate the infinite chain
TOP, A = ("top",), ("at", 0)


def rel(a, b):
    if a == b: return "EQ"
    if a < b: return "PP"
    if b < a: return "PPI"
    if not (a & b): return "DR"
    return "PO"


def sat(dom, val, x, c):
    k = c[0]
    if k == "top": return True
    if k == "at": return val.get((c[1], x), False)
    if k == "and": return sat(dom, val, x, c[1]) and sat(dom, val, x, c[2])
    if k == "ex":
        return any(rel(x, y) == c[1] and sat(dom, val, y, c[2]) for y in dom)
    if k == "all":
        return all(rel(x, y) != c[1] or sat(dom, val, y, c[2]) for y in dom)
    raise ValueError(k)


C0 = ("and", ("ex", "PP", TOP),
      ("all", "PP", ("and", ("ex", "PP", TOP), ("ex", "DR", A))))


def exhausting():
    """chain {0..i}; A on singletons {k}.  Chain union = everything."""
    chain = [frozenset(range(i + 1)) for i in range(N)]
    sides = [frozenset([k]) for k in range(N + 2)]
    dom = list(dict.fromkeys(chain + sides))
    val = {(0, s): (s in sides) for s in dom}
    return dom, val, chain


def roomy():
    """same chain in column 0 of N x {0,1}; A on {(0,1)}, off the chain."""
    chain = [frozenset((k, 0) for k in range(i + 1)) for i in range(N)]
    spare = frozenset([(0, 1)])
    sides = [spare] + [frozenset([(k, 0)]) for k in range(N + 2)]
    dom = list(dict.fromkeys(chain + sides))
    val = {(0, s): (s == spare) for s in dom}
    return dom, val, chain


def report(name, dom, val, chain):
    root = chain[0]
    holds = sat(dom, val, root, C0)
    # a region disjoint from EVERY chain point, from some base onward
    common = [w for w in dom
              if all(rel(chain[b], w) == "DR" for b in range(len(chain)))]
    # each phase separately has one
    per = all(any(rel(chain[b], w) == "DR" and sat(dom, val, w, A) for w in dom)
              for b in range(len(chain)))
    print(f"  {name}")
    print(f"    C0 holds at the chain root      : {holds}   <- CONTROL, must be True")
    print(f"    every phase has a DR A-witness  : {per}")
    print(f"    a COMMON disjoint external      : "
          f"{'YES (' + str(len(common)) + ')' if common else 'NONE'}")
    return holds, bool(common)


def main():
    print("WP128 -- must a kernel chain leave room for a disjoint external?\n")
    h1, c1 = report("EXHAUSTING model", *exhausting())
    print()
    h2, c2 = report("ROOMY model", *roomy())
    print()
    print("=" * 72)
    if not (h1 and h2):
        print("  CONTROL MISSED -- C0 fails in a model, conclusion WITHHELD.")
        return 1
    print("  CONTROL HELD: C0 is satisfied at the root of BOTH models.")
    print()
    if (not c1) and c2:
        print("  ANSWER: NO -- a kernel chain need NOT leave room.  The same")
        print("  satisfiable forall-PO-free concept has one model where mKdr is")
        print("  UNSATISFIABLE and another where it holds.")
        print()
        print("  So the gap is MODEL CHOICE, not the logic: completeness needs")
        print("  SOME certificate for a satisfiable C0, and the extraction is")
        print("  free to build it from a roomy model -- but only if one always")
        print("  exists, which is the next question and is NOT settled here.")
    else:
        print(f"  Unexpected: common-external present = {c1} / {c2}.")
        print("  Read the two rows above before concluding anything.")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
