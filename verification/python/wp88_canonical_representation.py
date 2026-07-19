#!/usr/bin/env python3
"""
wp88_canonical_representation.py  (2026-07-18)

Independent verification of GPT-5.6 Pro's canonical set representation
(`papers/final_paper_gpt_5.6_review/ALCI_RCC5_F6_technical_note.tex`,
Theorem 4.1) -- the CONVERSE of the RCC5 normal form, for arbitrary domains.
Our forward direction (RCC5 network -> ordered-disjoint structure) is certified
in `formal/RCC5NormalForm.lean`; the converse was previously only exhaustively
checked to size four (wp47). GPT-5.6's construction proves it in general; here
we check it far past n=4, and independently of GPT's own sanity script.

The construction: for an ordered-disjoint structure read off a strong-EQ
composition-closed RCC5 network (<= = reflexive closure of PP, D = DR),
   Omega   = { (u,v) : NOT u D v }              (non-disjoint pairs)
   eta(x)  = { (u,v) in Omega : u <= x or v <= x }
Then eta is injective and the ordinary set-RCC5 relation between eta(x), eta(y)
equals the network's relation N(x,y) -- so every ordered-disjoint structure IS
a family of sets under set-RCC5 (which is composition-closed).

This is the exact statement now certified in Lean (OrderedDisjoint.sub_iff_le
[0 axioms], eta_injective [0 axioms], disj_iff_eta_disjoint [+Classical]).

Self-contained (derives the table from set semantics). Exit 0 + PASS iff eta
reproduces every relation on many genuine strong-EQ networks, and the §7
identity-selector network checks out.
"""
import random
import itertools

random.seed(88)


def rel(a, b):
    a, b = frozenset(a), frozenset(b)
    if a == b: return "EQ"
    if a < b: return "PP"
    if b < a: return "PPI"
    if a.isdisjoint(b): return "DR"
    return "PO"


def eta_reproduces(N, pts):
    """Build GPT-5.6's eta from the ABSTRACT (<=, D) of the network N and check
    the set-RCC5 relation among eta-images equals N. Returns None or an error."""
    le = lambda x, y: x == y or N[(x, y)] == "PP"      # reflexive closure of PP
    D  = lambda x, y: N[(x, y)] == "DR"
    Omega = [(u, v) for u in pts for v in pts if not D(u, v)]
    eta = {x: frozenset((u, v) for (u, v) in Omega if le(u, x) or le(v, x))
           for x in pts}
    if any(len(eta[x]) == 0 for x in pts):
        return "eta empty"
    if len({eta[x] for x in pts}) != len(pts):
        return "eta not injective"
    for x in pts:
        for y in pts:
            if rel(eta[x], eta[y]) != N[(x, y)]:
                return f"mismatch {x},{y}: eta={rel(eta[x], eta[y])} N={N[(x, y)]}"
    return None


def random_strongEQ_network(n, univ):
    """n DISTINCT nonempty subsets of range(univ) -> strong-EQ composition-closed
    network (distinctness is essential: equal regions would give off-diagonal EQ,
    violating strong-EQ)."""
    seen, regs, tries = set(), [], 0
    while len(regs) < n and tries < 20000:
        tries += 1
        s = frozenset(i for i in range(univ) if random.random() < 0.5)
        if s and s not in seen:
            seen.add(s); regs.append(s)
    if len(regs) < n:
        return None
    pts = list(range(n))
    return {(i, j): rel(regs[i], regs[j]) for i in pts for j in pts}, pts


def part_representation():
    tested = fails = 0
    for n in range(1, 10):
        for _ in range(4000):
            r = random_strongEQ_network(n, max(n + 2, 8))
            if r is None:
                continue
            N, pts = r
            e = eta_reproduces(N, pts)
            tested += 1
            if e:
                fails += 1
                if fails <= 3:
                    print(f"   n={n}: {e}")
    assert fails == 0, f"{fails}/{tested} representation failures"
    print(f"A. canonical representation: {tested} strong-EQ composition-closed "
          f"networks (n up to 9), eta reproduces every relation, 0 failures -- PASS")


def part_selector(nI=8):
    """§7: the infinite identity-selector network is ordered-disjoint and the
    selector A_j separates (L_i, U_i) exactly when i = j."""
    pts = ["b"] + [f"L{i}" for i in range(nI)] + [f"U{i}" for i in range(nI)] \
        + [f"A{i}" for i in range(nI)]
    lt = {("b", f"U{i}") for i in range(nI)}                # strict order b < U_i
    D0 = set()
    for i in range(nI):
        D0 |= {("b", f"L{i}"), (f"L{i}", "b"),
               (f"L{i}", f"A{i}"), (f"A{i}", f"L{i}")}      # symmetric D seeds
    le = lambda x, y: x == y or (x, y) in lt
    D  = lambda x, y: (x, y) in D0
    def NN(x, y):
        if x == y: return "EQ"
        if le(x, y): return "PP"
        if le(y, x): return "PPI"
        if D(x, y): return "DR"
        return "PO"
    N = {(x, y): NN(x, y) for x in pts for y in pts}
    # validity: eta must reproduce it (i.e. it is a genuine ordered-disjoint RCC5 net)
    e = eta_reproduces(N, pts)
    assert e is None, f"selector network not eta-representable: {e}"
    # selector equations
    for i in range(nI):
        assert N[(f"L{i}", "b")] == "DR" and N[(f"U{i}", "b")] == "PPI"
        for j in range(nI):
            want = "DR" if i == j else "PO"
            assert N[(f"L{i}", f"A{j}")] == want
            assert N[(f"U{i}", f"A{j}")] == "PO"
    print(f"B. identity-selector network (I={nI}): ordered-disjoint, "
          f"eta-represented, A_j separates (L_i,U_i) iff i=j -- PASS")


if __name__ == "__main__":
    part_representation()
    part_selector()
    print()
    print("ALL PASS -- GPT-5.6's canonical set representation (converse normal")
    print("form) reproduces every relation far past n=4, and identity selectors")
    print("form a valid (word-automatic) RCC5 network. Matches the Lean")
    print("certification in formal/RCC5NormalForm.lean.")
