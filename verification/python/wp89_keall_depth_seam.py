#!/usr/bin/env python3
"""
wp89 -- the ke_all DEPTH SEAM of the mtk/mty multi-kernel merge.

CONTEXT (formal/POFreeLift.lean, the ∀PO-free mixing quadrant, §25.7).
`mixKernels_ok` proves the externals+kernels MultiTierOk coordination in the
UNIFORM full-`mty` setting (β arbitrary, not finite). For DECIDABILITY the
extraction needs a FINITE external node set, which comes from `mtk`-truncation:

    mtk C0 I x k  =  (mty C0 I x).filter (fun F => mdepth F <= k)

i.e. drop from x's label every concept deeper than the node's budget k.
Root budget = mdepth C0, and each horizontal step drops the budget by 1
(mtk_all_fwd: `∀r.c` at budget k lands `c` at budget k-1, since
mdepth(∀r.c) = 1 + mdepth c <= k).

THE QUESTION (the design's flagged "one genuine open question", §25.6):
porting the merge to `mtk`-truncated externals, is the `ke_all` clause
   (kernel phase `∀r.c` fires at external f whenever K k f = r  =>  c ∈ tauE f)
still satisfied?  `mty_all` gives `c ∈ mty(g f)`, but the TRUNCATED external
needs `c ∈ mtk(g f) kᶠ`, i.e. ALSO `mdepth c <= kᶠ`.  Analysis (see the
session notes) says this can FAIL for a grandchild-or-deeper external that is
DR to a kernel base carrying a top-level `∀dr.c`.

THIS PROBE settles it concretely and tests the candidate fix:

  (A) build a ∀PO-free concept C0 + a genuine RCC5 (finite-set) model;
  (B) NAIVE cert (K read off the model, like `mixKernels`): show `ke_all`
      FAILS under mtk-truncation -- a needed universal-argument is dropped;
  (C) PO-DEFAULT cert (the kernel's K to non-kernel-adjacent externals set to
      PO, exactly the trick `mtHF` already uses for its horizontal E edges):
      show `ke_all` becomes vacuous AND the frame stays composition-closed.

Self-contained: the RCC5 composition table is derived from finite-set
semantics by brute force (no reliance on the Lean artifact).

A PASS means: the naive route is genuinely broken (over-truncation), and
PO-defaulting the kernel edges is a sound, promising fix -- i.e. the
extraction should PO-default K/Q for non-adjacent nodes, not read them off
the model.
"""

from itertools import combinations, product

# ---------------------------------------------------------------------------
# 1. RCC5 from finite-set semantics (strong EQ = set equality)
# ---------------------------------------------------------------------------

REL = ["DR", "PO", "EQ", "PP", "PPI"]

def rel_of(X, Y):
    """The RCC5 relation of two nonempty finite sets (frozensets)."""
    if X == Y:
        return "EQ"
    if X < Y:          # proper subset
        return "PP"
    if Y < X:
        return "PPI"
    if X & Y:          # overlap, neither subset, not equal
        return "PO"
    return "DR"        # disjoint

def build_comp_table(univ=range(1, 6)):
    """comp[r][s] = set of possible rel(X,Z) given rel(X,Y)=r, rel(Y,Z)=s,
       computed exhaustively over nonempty subsets of a small universe."""
    subsets = [frozenset(s) for n in range(1, len(list(univ)) + 1)
               for s in combinations(univ, n)]
    comp = {r: {s: set() for s in REL} for r in REL}
    for X in subsets:
        for Y in subsets:
            r = rel_of(X, Y)
            for Z in subsets:
                comp[r][rel_of(Y, Z)].add(rel_of(X, Z))
    return comp

COMP = build_comp_table()

def conv(r):
    return {"EQ": "EQ", "PP": "PPI", "PPI": "PP", "PO": "PO", "DR": "DR"}[r]

# sanity: converse involution + a few known singleton cells
assert all(conv(conv(r)) == r for r in REL)
assert COMP["PP"]["PP"] == {"PP"}, COMP["PP"]["PP"]
assert COMP["PP"]["DR"] == {"DR"}, COMP["PP"]["DR"]
assert COMP["DR"]["PPI"] == {"DR"}, COMP["DR"]["PPI"]
# the two non-singleton cells that make PO "unforced" / vertical motion loose
assert "PO" in COMP["PP"]["PO"] and "PO" in COMP["PPI"]["PO"]

# ---------------------------------------------------------------------------
# 2. Concepts (NNF), modal depth, subformula closure, satisfaction
# ---------------------------------------------------------------------------
# concept encoding:
#   ('top',) ('bot',) ('atom',n) ('natom',n)
#   ('and',c,d) ('or',c,d) ('ex',r,c) ('all',r,c)

def mdepth(C):
    t = C[0]
    if t in ("top", "bot", "atom", "natom"):
        return 0
    if t in ("and", "or"):
        return max(mdepth(C[1]), mdepth(C[2]))
    if t in ("ex", "all"):
        return 1 + mdepth(C[2])
    raise ValueError(C)

def subformulas(C, acc=None):
    if acc is None:
        acc = []
    if C not in acc:
        acc.append(C)
    t = C[0]
    if t in ("and", "or"):
        subformulas(C[1], acc); subformulas(C[2], acc)
    elif t in ("ex", "all"):
        subformulas(C[2], acc)
    return acc

class Model:
    """A finite RCC5 interpretation given by a name->frozenset assignment
       plus an atomic valuation val[name] = set of true atom indices."""
    def __init__(self, sets, val):
        self.sets = sets                      # name -> frozenset
        self.names = list(sets)
        self.val = val                        # name -> set(int)
        # verify it is a genuine RCC5 model: every triangle composition-closed
        for a in self.names:
            for b in self.names:
                r = self.rho(a, b)
                for c in self.names:
                    assert self.rho(a, c) in COMP[r][self.rho(b, c)], \
                        ("model not composition-closed", a, b, c)

    def rho(self, a, b):
        return rel_of(self.sets[a], self.sets[b])

    def sat(self, x, C):
        t = C[0]
        if t == "top":  return True
        if t == "bot":  return False
        if t == "atom": return C[1] in self.val[x]
        if t == "natom":return C[1] not in self.val[x]
        if t == "and":  return self.sat(x, C[1]) and self.sat(x, C[2])
        if t == "or":   return self.sat(x, C[1]) or self.sat(x, C[2])
        if t == "ex":
            return any(self.rho(x, y) == C[1] and self.sat(y, C[2])
                       for y in self.names)
        if t == "all":
            return all((self.rho(x, y) != C[1]) or self.sat(y, C[2])
                       for y in self.names)
        raise ValueError(C)

    def mty(self, C0, x):
        return [C for C in subformulas(C0) if self.sat(x, C)]

    def mtk(self, C0, x, k):
        return [C for C in self.mty(C0, x) if mdepth(C) <= k]

# ---------------------------------------------------------------------------
# 3. The villain concept + a model realizing the bad geometry
# ---------------------------------------------------------------------------
# c   = ∀DR.∀DR.∀DR.A          (mdepth 3)   -- the deep universal argument
# U   = ∀DR.c                  (mdepth 4)   -- a TOP-LEVEL universal, lives on
#                                              the tower (kernel phase)
# C0  = U ⊓ ∃PP.⊤ ⊓ ∃DR.∃DR.⊤  (mdepth 4)
#   - ∃PP.⊤    forces a tower  -> a KERNEL is attached here
#   - ∃DR.∃DR.⊤ forces a horizontal DR grandchild (depth 2)
A   = ("atom", 0)
c   = ("all", "DR", ("all", "DR", ("all", "DR", A)))     # mdepth 3
U   = ("all", "DR", c)                                   # mdepth 4
C0  = ("and", ("and", U, ("ex", "PP", ("top",))),
              ("ex", "DR", ("ex", "DR", ("top",))))       # mdepth 4

assert mdepth(c) == 3 and mdepth(U) == 4 and mdepth(C0) == 4

# Model (sets chosen so A holds EVERYWHERE, so c/U hold everywhere trivially):
#   R = {1}       root
#   T = {1,2}     tower base/phase       (R ⊂ T  => R PP T,  kernel here)
#   g1 = {3}      R's DR-child           (R DR g1)
#   g2 = {4}      g1's DR-child (depth 2)(g1 DR g2;  T DR g2)
sets = {"R": frozenset({1}), "T": frozenset({1, 2}),
        "g1": frozenset({3}), "g2": frozenset({4})}
val  = {n: {0} for n in sets}          # atom 0 (=A) true everywhere
M = Model(sets, val)

# geometry we rely on
assert M.rho("R", "T")  == "PP"        # tower step (served by the kernel)
assert M.rho("R", "g1") == "DR"        # horizontal child
assert M.rho("g1", "g2")== "DR"        # horizontal grandchild
assert M.rho("T", "g2") == "DR"        # kernel base DR the deep external  <-- crux
assert M.sat("R", C0)                  # C0 holds at the root
assert U in M.mty(C0, "T")             # the tower phase carries ∀DR.c

# naive budgets: root = mdepth C0, minus 1 per horizontal step
BUDGET = {"R": mdepth(C0), "g1": mdepth(C0) - 1, "g2": mdepth(C0) - 2}
assert BUDGET == {"R": 4, "g1": 3, "g2": 2}

EXTERNALS = ["R", "g1", "g2"]          # the horizontal skeleton
KERNEL_BASE = "T"
KERNEL_ADJ  = {"R"}                    # the kernel is attached at R (serves R's ∃PP)

# ---------------------------------------------------------------------------
# 4. (B) NAIVE cert: K read off the model  ->  does ke_all hold under mtk?
# ---------------------------------------------------------------------------
# ke_all: for the kernel phase (label = mty T), every  ∀r.cc  in the phase,
# every external f with  K f = r,  requires  cc ∈ mtk(g f, budget f).
# NAIVE:  K f = rho(T, f)   (the real model relation).

def ke_all_failures(K):
    """Return list of (f, universal, arg, needed_budget, have_budget) where
       the kernel universal fires at external f but its argument is dropped
       from f's truncated label."""
    fails = []
    phase = M.mty(C0, KERNEL_BASE)                 # kernel phase = full mty(T)
    for uni in phase:
        if uni[0] != "all":
            continue
        r, arg = uni[1], uni[2]
        for f in EXTERNALS:
            if K(f) != r:
                continue
            # fires: model guarantees arg ∈ mty(g f); truncation may drop it
            assert M.sat(f, arg), ("model unsound?", f, arg)   # real model OK
            if arg not in M.mtk(C0, f, BUDGET[f]):
                fails.append((f, uni, arg, mdepth(arg), BUDGET[f]))
    return fails

K_naive = lambda f: M.rho(KERNEL_BASE, f)          # real relations
naive_fails = ke_all_failures(K_naive)

# ---------------------------------------------------------------------------
# 5. (C) PO-DEFAULT cert: K = PO to non-kernel-adjacent externals
# ---------------------------------------------------------------------------
# Exactly mtHF's trick for E: only "adjacent" edges carry the real relation;
# everything else defaults to PO, which is vacuous under ∀PO-freeness.
def K_podefault(f):
    return M.rho(KERNEL_BASE, f) if f in KERNEL_ADJ else "PO"

podefault_fails = ke_all_failures(K_podefault)

# does any ∀PO live in the closure?  (∀PO-free => none => PO edges vacuous)
has_all_po = any(C[0] == "all" and C[1] == "PO" for C in subformulas(C0))

# frame check for the PO-default combined network over {R,g1,g2,T}:
#   E among externals = mtHF-style (tree edges real DR/EQ; non-tree = PO),
#   K (base<->external) = K_podefault,  and its converse,
#   diagonal = EQ.
TREE_EDGES = {("R", "g1"), ("g1", "g2")}           # the demand tree
def E_ext(a, b):
    if a == b:
        return "EQ"
    if (a, b) in TREE_EDGES or (b, a) in TREE_EDGES:
        return M.rho(a, b)                          # real (DR here)
    return "PO"                                     # non-tree default

NODES = EXTERNALS + [KERNEL_BASE]
def cert_rho(a, b):
    if a == b:
        return "EQ"
    if a in EXTERNALS and b in EXTERNALS:
        return E_ext(a, b)
    if a == KERNEL_BASE and b in EXTERNALS:
        return K_podefault(b)
    if b == KERNEL_BASE and a in EXTERNALS:
        return conv(K_podefault(a))
    return "EQ"

def frame_closed(rho):
    bad = []
    for a in NODES:
        for b in NODES:
            r = rho(a, b)
            for cc in NODES:
                if rho(a, cc) not in COMP[r][rho(b, cc)]:
                    bad.append((a, b, cc, rho(a, b), rho(b, cc), rho(a, cc)))
    return bad

podefault_frame_bad = frame_closed(cert_rho)

# For reference: the NAIVE combined network (everything real) is exactly the
# model restricted to these 4 points, hence trivially frame-closed.
def naive_rho(a, b):
    return M.rho(a, b)
naive_frame_bad = frame_closed(naive_rho)

# ---------------------------------------------------------------------------
# 6. Report
# ---------------------------------------------------------------------------
def show_uni(u):
    def s(C):
        return {"all": lambda: f"∀{C[1]}.{s(C[2])}",
                "ex": lambda: f"∃{C[1]}.{s(C[2])}",
                "atom": lambda: f"A{C[1]}", "top": lambda: "⊤",
                "and": lambda: f"({s(C[1])}⊓{s(C[2])})"}[C[0]]()
    return s(u)

print("=" * 74)
print("wp89 -- the ke_all depth seam (mtk-truncated externals + kernels)")
print("=" * 74)
print(f"comp table: derived from finite-set semantics, "
      f"{sum(len(COMP[r][s]) for r in REL for s in REL)} cell-entries; "
      f"converse involution + singleton cells verified.")
print(f"villain C0 = {show_uni(('and',('and',U,('ex','PP',('top',))),('ex','DR',('ex','DR',('top',)))))}")
print(f"   mdepth C0 = {mdepth(C0)};  tower universal U = ∀DR.c "
      f"(mdepth {mdepth(U)});  its arg c has mdepth {mdepth(c)}")
print(f"   ∀PO in closure? {has_all_po}  (∀PO-free fragment => PO edges vacuous)")
print(f"model: R⊂T (R PP T, kernel here), R DR g1 DR g2, and T DR g2;  "
      f"A true everywhere.")
print(f"naive budgets (−1/horizontal step): {BUDGET}")
print("-" * 74)

print("(B) NAIVE cert  (K read off the model, as in `mixKernels`):")
if naive_fails:
    for f, uni, arg, need, have in naive_fails:
        print(f"    ke_all FAILS at external {f!r}: kernel {show_uni(uni)} fires "
              f"(K {f} = {K_naive(f)}),")
        print(f"        needs arg {show_uni(arg)} (mdepth {need}) in mtk({f},{have}) "
              f"-- DROPPED ({need} > {have}).")
    print(f"    => over-truncation: {len(naive_fails)} needed conclusion(s) "
          f"dropped.  naive frame-closed? {not naive_frame_bad} (real model).")
else:
    print("    ke_all holds -- analysis WRONG, naive route survives.")
print("-" * 74)

print("(C) PO-DEFAULT cert  (K = PO to non-kernel-adjacent externals, the "
      "mtHF trick):")
print(f"    ke_all failures now: {len(podefault_fails)} "
      f"({'VACUOUS/holds' if not podefault_fails else 'STILL FAILS'})")
print(f"    PO-default combined frame composition-closed? "
      f"{not podefault_frame_bad}")
if podefault_frame_bad:
    for t in podefault_frame_bad[:4]:
        print(f"        bad triangle {t}")
print("-" * 74)

naive_broken   = len(naive_fails) > 0 and not naive_frame_bad
fix_works      = (len(podefault_fails) == 0) and (not podefault_frame_bad) \
                 and (not has_all_po)

print("VERDICT:")
print(f"  naive mtk-truncation route BROKEN by over-truncation: {naive_broken}")
print(f"  PO-defaulting the kernel edges fixes ke_all + stays frame-sound: "
      f"{fix_works}")
print()
if naive_broken and fix_works:
    print("PASS -- the depth seam is REAL (naive route produces an invalid cert "
          "for a\n       satisfiable ∀PO-free concept), and the fix is to "
          "PO-DEFAULT the kernel's\n       K/Q for non-adjacent nodes (as mtHF "
          "already does for E), NOT read them\n       off the model.  The "
          "extraction should build PO-defaulted kernel edges;\n       the "
          "`mixKernels_ok` hypotheses (real K, hstab, hrectQ) then apply only "
          "to the\n       bounded adjacent set.")
else:
    print("INCONCLUSIVE -- revisit the construction.")

assert naive_broken, "expected the naive route to break"
assert fix_works, "expected PO-defaulting to fix it"
print("\nall assertions passed.")
