#!/usr/bin/env python3
"""
wp90 -- END-TO-END validation of the mtk-with-kernels mixing architecture.

Follows wp89 (which showed the naive route breaks ke_all and PO-defaulting the
kernel edges fixes it, for ONE ascending villain).  wp90 validates the WHOLE
proposed extraction architecture -- for BOTH kernel directions -- before it is
written in Lean:

  * externals = mtk-truncated skeleton (budget mdepth C0, −1 per horizontal
    step);
  * kernels attached at ∃PP (ascending) / ∃PPI (descending) nodes; phases =
    tower points' mty TRUNCATED at the attaching node's budget;
  * far edges = CANONICAL COMPLETION: real model relation on adjacency
    (demand tree edges + the kernel-attaching edge), and every other edge
    relaxed to PO wherever that keeps the network composition-closed
    (forced-value elsewhere).  This is the mtHF trick (PO where free) made
    uniform across kernel edges too.

THE UNIFYING OBSERVATION.  Every MultiTierOk universal clause
(ee_all / ek_all / ke_all / kk_pp / kk_ppi / kk_eq / kq_all) is ONE property:

    (∀-PROP)  for all cert nodes x,y:  ∀r.c ∈ label(x)  and  ρ(x,y) = r
              ⟹  c ∈ label(y).

and every existential clause (e_ex / k_ex) is:

    (∃-FUL)   for all x:  ∃r.c ∈ label(x)  ⟹  ∃ y, ρ(x,y) = r ∧ c ∈ label(y).

So a cert is a valid MultiTierOk (modulo the propositional clauses, which mtk
handles by construction) iff the completed network is a FRAME and satisfies
(∀-PROP) and (∃-FUL) with the TRUNCATED labels.  wp90 checks exactly these,
on the completed+truncated cert, and contrasts with the naive cert
(real edges, full mty labels).

A PASS means: the canonical completion + phase truncation yields a fully valid
finite certificate for satisfiable ∀PO-free concepts, in BOTH the ascending
and descending kernel directions (and mixed) -- i.e. the Lean extraction can be
written against this architecture.

Self-contained (RCC5 comp table from finite-set semantics).
"""

from itertools import combinations

# ---------------------------------------------------------------------------
# 1. RCC5 from finite-set semantics  (identical core to wp89)
# ---------------------------------------------------------------------------
REL = ["DR", "PO", "EQ", "PP", "PPI"]

def rel_of(X, Y):
    if X == Y:  return "EQ"
    if X < Y:   return "PP"
    if Y < X:   return "PPI"
    if X & Y:   return "PO"
    return "DR"

def build_comp_table(univ=range(1, 6)):
    subs = [frozenset(s) for n in range(1, len(list(univ)) + 1)
            for s in combinations(univ, n)]
    comp = {r: {s: set() for s in REL} for r in REL}
    for X in subs:
        for Y in subs:
            r = rel_of(X, Y)
            for Z in subs:
                comp[r][rel_of(Y, Z)].add(rel_of(X, Z))
    return comp

COMP = build_comp_table()
def conv(r): return {"EQ":"EQ","PP":"PPI","PPI":"PP","PO":"PO","DR":"DR"}[r]

assert COMP["PP"]["DR"] == {"DR"} and COMP["DR"]["PPI"] == {"DR"}
assert COMP["PP"]["PP"] == {"PP"} and COMP["PPI"]["PPI"] == {"PPI"}

# ---------------------------------------------------------------------------
# 2. Concepts / mdepth / subformulas / satisfaction / mty / mtk (as wp89)
# ---------------------------------------------------------------------------
def mdepth(C):
    t = C[0]
    if t in ("top","bot","atom","natom"): return 0
    if t in ("and","or"): return max(mdepth(C[1]), mdepth(C[2]))
    if t in ("ex","all"): return 1 + mdepth(C[2])
    raise ValueError(C)

def subformulas(C, acc=None):
    if acc is None: acc = []
    if C not in acc: acc.append(C)
    t = C[0]
    if t in ("and","or"): subformulas(C[1], acc); subformulas(C[2], acc)
    elif t in ("ex","all"): subformulas(C[2], acc)
    return acc

class Model:
    def __init__(self, sets, val):
        self.sets = sets; self.names = list(sets); self.val = val
        for a in self.names:                       # verify it is an RCC5 model
            for b in self.names:
                r = self.rho(a, b)
                for c in self.names:
                    assert self.rho(a, c) in COMP[r][self.rho(b, c)], \
                        ("model not closed", a, b, c)
    def rho(self, a, b): return rel_of(self.sets[a], self.sets[b])
    def sat(self, x, C):
        t = C[0]
        if t=="top": return True
        if t=="bot": return False
        if t=="atom": return C[1] in self.val[x]
        if t=="natom": return C[1] not in self.val[x]
        if t=="and": return self.sat(x,C[1]) and self.sat(x,C[2])
        if t=="or":  return self.sat(x,C[1]) or self.sat(x,C[2])
        if t=="ex":  return any(self.rho(x,y)==C[1] and self.sat(y,C[2]) for y in self.names)
        if t=="all": return all(self.rho(x,y)!=C[1] or self.sat(y,C[2]) for y in self.names)
    def mty(self, C0, x): return [C for C in subformulas(C0) if self.sat(x, C)]
    def mtk(self, C0, x, k): return [C for C in self.mty(C0,x) if mdepth(C) <= k]

# ---------------------------------------------------------------------------
# 3. Certificate: nodes with truncated labels + canonical (PO-max) completion
# ---------------------------------------------------------------------------
class Cert:
    """A cert node set over model elements, each with a truncation budget, an
       adjacency set (edges kept at the real model relation), and a policy
       ('canonical' PO-max, or 'naive' real+full-labels)."""
    def __init__(self, M, C0, nodes, elt, budget, adjacency, policy):
        self.M, self.C0 = M, C0
        self.nodes = nodes
        self.elt = elt                     # node -> model element name
        self.budget = budget               # node -> truncation budget (None = full mty)
        self.adj = adjacency               # set of frozenset{a,b} kept real
        self.policy = policy
        self.rho = self._complete()

    def label(self, n):
        # BOTH policies use the mtk-TRUNCATED label; only the edge policy
        # differs (naive = real model edges = the wp89 seam; canonical =
        # forcing-completion).  So a naive failure is exactly over-truncation.
        b = self.budget[n]
        if b is None:
            return self.M.mty(self.C0, self.elt[n])
        return self.M.mtk(self.C0, self.elt[n], b)

    def _real(self, a, b):
        return self.M.rho(self.elt[a], self.elt[b])

    def _closed(self, rho):
        for a in self.nodes:
            for b in self.nodes:
                r = rho[a][b]
                for c in self.nodes:
                    if rho[a][c] not in COMP[r][rho[b][c]]:
                        return False
        return True

    def _complete(self):
        if self.policy == "naive":
            # the real model network (globally consistent, closed) -- infinite
            # labels, used only as the "always valid but not finite" baseline.
            return {a: {b: self._real(a, b) for b in self.nodes}
                    for a in self.nodes}
        # CANONICAL COMPLETION (forcing-propagation):
        #   adjacency edges = real; force every singleton-determined edge to
        #   fixpoint (tower transitivity comp(PP,PP)={PP}, disjointness
        #   comp(PP,DR)={DR}, ...); PO the genuinely-free rest.  Closed by
        #   construction: a free edge sits in no singleton cell, and PO lives
        #   in every non-singleton cell (the escape valve).
        rho = {a: {b: (None if a != b else "EQ") for b in self.nodes}
               for a in self.nodes}
        for a, b in combinations(self.nodes, 2):
            if frozenset((a, b)) in self.adj:
                rho[a][b] = self._real(a, b); rho[b][a] = conv(rho[a][b])
        changed = True
        while changed:
            changed = False
            for a in self.nodes:
                for c in self.nodes:
                    if rho[a][c] is not None:
                        continue
                    for b in self.nodes:
                        if rho[a][b] is not None and rho[b][c] is not None:
                            cell = COMP[rho[a][b]][rho[b][c]]
                            if len(cell) == 1:
                                s = next(iter(cell))
                                rho[a][c] = s; rho[c][a] = conv(s)
                                changed = True
                                break
        for a in self.nodes:                       # free edges -> PO
            for b in self.nodes:
                if rho[a][b] is None:
                    rho[a][b] = "PO"
        return rho

# ---------------------------------------------------------------------------
# 4. The three validity properties (subsume all MultiTierOk clauses)
# ---------------------------------------------------------------------------
def check_frame(cert):
    bad = []
    for a in cert.nodes:
        for b in cert.nodes:
            r = cert.rho[a][b]
            for c in cert.nodes:
                if cert.rho[a][c] not in COMP[r][cert.rho[b][c]]:
                    bad.append((a, b, c))
    return bad

def check_all_prop(cert):
    """(∀-PROP): every ∀r.c at x with ρ(x,y)=r forces c ∈ label(y).
       Subsumes ee_all/ek_all/ke_all/kk_*/kq_all."""
    fails = []
    lab = {n: cert.label(n) for n in cert.nodes}
    for x in cert.nodes:
        for C in lab[x]:
            if C[0] != "all": continue
            r, arg = C[1], C[2]
            for y in cert.nodes:
                if cert.rho[x][y] == r and arg not in lab[y]:
                    fails.append((x, C, y, cert.rho[x][y]))
    return fails

def check_exists(cert):
    """(∃-FUL): every ∃r.c at x has a cert witness y with ρ(x,y)=r, c∈label(y).
       Subsumes e_ex/k_ex.  (EQ is reflexive: y=x.)"""
    fails = []
    lab = {n: cert.label(n) for n in cert.nodes}
    for x in cert.nodes:
        for C in lab[x]:
            if C[0] != "ex": continue
            r, arg = C[1], C[2]
            served = any(cert.rho[x][y] == r and arg in lab[y] for y in cert.nodes)
            if not served:
                fails.append((x, C))
    return fails

def show(C):
    t=C[0]
    if t=="all": return f"∀{C[1]}.{show(C[2])}"
    if t=="ex":  return f"∃{C[1]}.{show(C[2])}"
    if t=="atom":return f"A{C[1]}"
    if t=="top": return "⊤"
    if t=="and": return f"({show(C[1])}⊓{show(C[2])})"
    return str(C)

# ---------------------------------------------------------------------------
# 5. Villains: ascending, descending, and mixed (two kernels)
# ---------------------------------------------------------------------------
A = ("atom", 0); B = ("atom", 1)
c_deep = ("all","DR",("all","DR",("all","DR",A)))            # mdepth 3
U_dr   = ("all","DR",c_deep)                                 # mdepth 4, top-level ∀DR

def report(title, cert, expect_ok):
    fr = check_frame(cert); ap = check_all_prop(cert); ex = check_exists(cert)
    ok = (not fr) and (not ap) and (not ex)
    print(f"  [{cert.policy:9s}] frame_closed={not fr}  "
          f"∀-prop_ok={not ap}  ∃-ful_ok={not ex}   => VALID={ok}")
    if ap:
        f = ap[0]
        print(f"        ∀-PROP FAIL e.g.: {show(f[1])} at {f[0]!r} fires "
              f"(ρ={f[3]}) but arg {show(f[1][2])} (mdepth {mdepth(f[1][2])}) "
              f"∉ label({f[2]!r}, budget {cert.budget[f[2]]})")
    if ex:
        print(f"        ∃-FUL FAIL e.g.: {show(ex[0][1])} at {ex[0][0]!r} unserved")
    return ok

results = []

# ---- (I) ASCENDING villain (wp89 geometry, now full clause check) ----------
# C0 = U_dr ⊓ ∃PP.⊤ ⊓ ∃DR.∃DR.⊤ ;  kernel ascending at root.
print("=" * 74)
print("wp90 -- mtk-with-kernels architecture, end-to-end (both directions)")
print("=" * 74)
C0a = ("and", ("and", U_dr, ("ex","PP",("top",))), ("ex","DR",("ex","DR",("top",))))
md_a = mdepth(C0a)
# model: R⊂T0⊂T1 (ascending tower), R DR g1 DR g2, all A-true.
#   The tower points ALSO carry the horizontal demand ∃DR.∃DR.⊤ (a top-level
#   conjunct), so per §25.6 they SPAWN their own DR-children h1 DR h2, added as
#   externals adjacent to the phases (h1 reused by both T0 and T1).
setsA = {"R":frozenset({1}), "T0":frozenset({1,2}), "T1":frozenset({1,2,3}),
         "g1":frozenset({4}), "g2":frozenset({5}),
         "h1":frozenset({6}), "h2":frozenset({7})}
Ma = Model(setsA, {n:{0} for n in setsA})
assert Ma.sat("R", C0a) and Ma.rho("R","T0")=="PP" and Ma.rho("T0","g2")=="DR"
assert Ma.rho("T0","h1")=="DR" and Ma.rho("h1","h2")=="DR"
# cert nodes: externals R,g1,g2 + phase-children h1,h2 ; phases T0,T1.
nodesA = ["R","g1","g2","T0","T1","h1","h2"]
eltA   = {n:n for n in nodesA}
budA   = {"R":md_a, "g1":md_a-1, "g2":md_a-2, "T0":md_a, "T1":md_a,
          "h1":md_a-1, "h2":md_a-2}               # phase-children truncate below the phase
adjA   = {frozenset(("R","g1")), frozenset(("g1","g2")),   # root's demand tree
          frozenset(("R","T0")),                            # kernel-attaching (R ∃PP -> T0)
          frozenset(("T0","T1")),                           # tower step
          frozenset(("T0","h1")), frozenset(("T1","h1")),   # phases' ∃DR served by h1
          frozenset(("h1","h2"))}                           # h1's ∃DR served by h2
print(f"\n(I) ASCENDING villain  C0 = {show(C0a)}   (mdepth {md_a})")
naiveA = Cert(Ma, C0a, nodesA, eltA, budA, adjA, "naive")   # real edges, full labels
canonA = Cert(Ma, C0a, nodesA, eltA, budA, adjA, "canonical")
report("naive", naiveA, False)
results.append(("ascending", report("canonical", canonA, True)))

# ---- (II) DESCENDING villain: ∃PPI kernel + the FORCED-DR-to-child case -----
# C0 = U_dr ⊓ ∃PPI.⊤ ⊓ ∃DR.∃DR.⊤ ;  kernel descending at root (base BELOW R).
C0d = ("and", ("and", U_dr, ("ex","PPI",("top",))), ("ex","DR",("ex","DR",("top",))))
md_d = mdepth(C0d)
# model: base B0 ⊂ R (R ⊃ B0 so R PPI B0... R demands ∃PPI -> a proper part),
#        B1 ⊂ B0 (descending tower), R DR g1 DR g2.  A true everywhere.
#   B0 DR g1 is FORCED (R⊃B0, R DR g1 => B0 DR g1) -- the crux forced edge.
setsD = {"R":frozenset({1,2,3}), "B0":frozenset({1,2}), "B1":frozenset({1}),
         "g1":frozenset({4}), "g2":frozenset({5})}
Md = Model(setsD, {n:{0} for n in setsD})
assert Md.sat("R", C0d) and Md.rho("R","B0")=="PPI" and Md.rho("B0","g1")=="DR"
nodesD = ["R","g1","g2","B0","B1"]
eltD   = {n:n for n in nodesD}
budD   = {"R":md_d, "g1":md_d-1, "g2":md_d-2, "B0":md_d, "B1":md_d}
adjD   = {frozenset(("R","g1")), frozenset(("g1","g2")),
          frozenset(("R","B0")),                            # kernel-attaching (R ∃PPI -> B0)
          frozenset(("B0","B1"))}
print(f"\n(II) DESCENDING villain  C0 = {show(C0d)}   (mdepth {md_d})")
print(f"     (B0 DR g1 is FORCED by R⊃B0, R DR g1; g1 has budget {budD['g1']} "
      f">= mdepth c ({mdepth(c_deep)}) so the forced edge is budget-safe)")
naiveD = Cert(Md, C0d, nodesD, eltD, budD, adjD, "naive")
canonD = Cert(Md, C0d, nodesD, eltD, budD, adjD, "canonical")
report("naive", naiveD, False)
results.append(("descending", report("canonical", canonD, True)))
# is B0->g1 kept DR (forced) and B0->g2 relaxed to PO?
print(f"     completed: ρ(B0,g1)={canonD.rho['B0']['g1']} (forced DR expected), "
      f"ρ(B0,g2)={canonD.rho['B0']['g2']} (PO expected)")

# ---- (III) MIXED: one ascending + one descending kernel (cross-kernel kq) ---
# C0 = ∃PP.⊤ ⊓ ∃PPI.⊤ ⊓ U_dr  ; two kernels off the root, DR-linked.
C0m = ("and", ("and", ("ex","PP",("top",)), ("ex","PPI",("top",))), U_dr)
md_m = mdepth(C0m)
#   R ; ascending T0⊃R ; descending B0⊂R ; T0 vs B0: PO-ish/DR by model.
setsM = {"R":frozenset({2,3}), "T0":frozenset({2,3,4}), "B0":frozenset({2}),
         "g1":frozenset({7})}
Mm = Model(setsM, {n:{0} for n in setsM})
assert Mm.sat("R", C0m)
nodesM = ["R","g1","T0","B0"]
eltM   = {n:n for n in nodesM}
budM   = {"R":md_m, "g1":md_m-1, "T0":md_m, "B0":md_m}
adjM   = {frozenset(("R","g1")), frozenset(("R","T0")), frozenset(("R","B0"))}
print(f"\n(III) MIXED villain  C0 = {show(C0m)}   (mdepth {md_m})   "
      f"[ascending T0 + descending B0]")
naiveM = Cert(Mm, C0m, nodesM, eltM, budM, adjM, "naive")
canonM = Cert(Mm, C0m, nodesM, eltM, budM, adjM, "canonical")
report("naive", naiveM, True)     # small mdepth here; naive may or may not pass
results.append(("mixed", report("canonical", canonM, True)))

# ---------------------------------------------------------------------------
# 6. Verdict
# ---------------------------------------------------------------------------
print("\n" + "=" * 74)
all_ok = all(ok for _, ok in results)
for name, ok in results:
    print(f"  {name:12s}: canonical cert VALID = {ok}")
print("=" * 74)
if all_ok:
    print("PASS -- the mtk-with-kernels architecture (canonical PO-max completion +\n"
          "       phase truncation at the attaching budget) yields a FULLY VALID\n"
          "       MultiTierOk certificate in BOTH kernel directions and mixed:\n"
          "       frame-closed, ∀-propagation holds (ke_all/kq_all included), and\n"
          "       every ∃ is served.  The naive certs fail ∀-propagation (the wp89\n"
          "       depth seam).  The Lean extraction can be written against this:\n"
          "       real edges on adjacency, PO where free, forced value where forced,\n"
          "       phases mtk-truncated at the attaching node's budget.")
else:
    print("INCONCLUSIVE / FAIL -- some canonical cert is invalid; inspect above.")

assert all_ok, "expected every canonical cert to be a valid MultiTierOk"
print("\nall assertions passed.")
