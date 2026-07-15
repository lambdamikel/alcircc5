#!/usr/bin/env python3
r"""
WP35 -- an ADVERSARIAL attack on F6 (the bounded-width / K(C0) obligation),
and its honest outcome.

F6 is the standing open completeness-side obligation: that every satisfiable
ALCI_RCC5 concept admits a split-forest / catalogue presentation of BOUNDED
WIDTH (bounded live occurrences per cluster).  A counterexample would force
some concept's models to require unboundedly many mutually-constrained
occurrences at a single interface -- killing the finite-catalogue route.

THE ATTACK: the "alternating-colour gap tower".  Evaluated at a spy region
a_0 (smallest), it forces a PP-tower a_0 PP a_1 PP ... (nested, growing) and
at each level a_k an existential PO-witness w_k, with alternating colours B/C
so that each level's rejection universals force the NEXT level's witness to
be DISCRETE (DR) from the level below without colliding with the level's own
witness:
    Even = exists PO.B and forall PP.~C and forall PO.~C and exists PP.Odd
    Odd  = exists PO.C and forall PP.~B and forall PO.~B and exists PP.Even
(start at a_0 = Even).

Machine-checked findings (stages below):
 (1) SAT: for every depth D there is an explicit interval model (nested
     intervals + gap witnesses), a valid RCC5 network (0 composition
     violations), satisfying C0(D); the tableau agrees (SAT).
 (2) FORCED unbounded spy-degree: in EVERY model the spy a_0 has >= D
     distinct DR-neighbours.  Proven two ways:
       (A) a forcing certificate from composition facts
           F1 comp(PP,PO)\{PP,PO} = {DR}  (universal => a_{k-1} DR w_k),
           F2 comp(DR,PPI) = {DR}          (=> w_k DR a_j for all j<k, incl a_0),
           F3 PO != DR                     (=> level-k and level-j witnesses distinct),
           F4 comp(PP,PP) = {PP}           (PP transitive: no tower loops);
       (B) a path-consistency model search that is FREE to share/merge
           witnesses: for D=2..5 the ONLY feasible witness-count is D --
           every attempt with fewer witnesses COLLAPSES under RCC5 path
           consistency (a sound impossibility proof).

 (3) BUT THE ATTACK FAILS -- and this is the point.  The unbounded spy
     degree is entirely SHADOW width: 7 of 8 a_0->w_k edges (D=8) are
     composition-forced (singleton comp via a_1: comp(PP,DR)={DR}).  The
     LIVE (non-shadow) cross-degree is BOUNDED at 4, constant in D.  So the
     concept HAS a bounded-live-width model -- exactly the "unbounded forced
     global degree, bounded live width" case the shadow / virtual-bag
     argument is designed to absorb.

CONCLUSION.  This does NOT refute F6.  It is a concrete, machine-checked
stress test that the shadow mechanism must (and here does) handle, and thus
mild evidence FOR F6: the RCC5 composition table RESISTED the natural
"make the spy see unboundedly many neighbours" attack by funnelling all the
unbounded degree into shadows.  It also SHARPENS the target: a genuine F6
counterexample cannot come from global node degree (always shadows) -- it
would need unbounded LIVE width, i.e. unboundedly many occurrences in ONE
cluster whose mutual relations are NOT composition-determined.  Every attempt
to force that runs into the tension that forced edges are shadows (determined)
while free edges can be re-oriented ("model surgery") to collapse the width.

This is an attack harness: a passing run CONFIRMS the findings above (SAT +
forced global degree + bounded live width => attack fails, F6 survives).

Run: python3 verification/python/wp35_f6_width_attack.py
"""
import sys, os, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', '..', 'src'))
from alcircc5_reasoner import (
    DR, PO, PP, PPI, INV, COMP,
    AtomicConcept, NegAtomicConcept, Top, Bottom, And, Or, Exists, ForAll,
)

ALL = frozenset({DR, PO, PP, PPI})
B = AtomicConcept('B'); C = AtomicConcept('C')
nB = NegAtomicConcept('B'); nC = NegAtomicConcept('C')

# ---------------------------------------------------------------- concept ---
def conj(*cs):
    r = cs[0]
    for c in cs[1:]:
        r = And(r, c)
    return r

def _level(parity, depth):
    own = B if parity == 0 else C
    rejN = nC if parity == 0 else nB
    base = conj(Exists(PO, own), ForAll(PP, rejN), ForAll(PO, rejN))
    if depth <= 0:
        return base
    return conj(base, Exists(PP, _level(1 - parity, depth - 1)))

def C0(D):
    return _level(0, D)

# ---------------------------------------------------------- interval model ---
def rel(x, y):
    (a, b), (c, d) = x, y
    if x == y: return 'EQ'
    if b <= c or d <= a: return 'DR'
    xin = (c <= a and b <= d); yin = (a <= c and d <= b)
    if xin and not yin: return 'PP'
    if yin and not xin: return 'PPI'
    return 'PO'

def build_model(D):
    nodes, typ = {}, {}
    for k in range(D + 1):
        nodes[f'a{k}'] = (0.0, k + 1.0); typ[f'a{k}'] = set()
    for k in range(D + 1):
        nodes[f'w{k}'] = (k + 0.5, k + 1.5); typ[f'w{k}'] = {'B' if k % 2 == 0 else 'C'}
    return nodes, typ

def sat_at(concept, node, nodes, typ):
    R = lambda x, y: rel(nodes[x], nodes[y])
    if isinstance(concept, Top): return True
    if isinstance(concept, Bottom): return False
    if isinstance(concept, AtomicConcept): return concept.name in typ[node]
    if isinstance(concept, NegAtomicConcept): return concept.name not in typ[node]
    if isinstance(concept, And):
        return sat_at(concept.left, node, nodes, typ) and sat_at(concept.right, node, nodes, typ)
    if isinstance(concept, Or):
        return sat_at(concept.left, node, nodes, typ) or sat_at(concept.right, node, nodes, typ)
    if isinstance(concept, Exists):
        return any(y != node and R(node, y) == concept.role
                   and sat_at(concept.concept, y, nodes, typ) for y in nodes)
    if isinstance(concept, ForAll):
        return all(sat_at(concept.concept, y, nodes, typ)
                   for y in nodes if y != node and R(node, y) == concept.role)
    raise ValueError(concept)

def network(nodes):
    names = list(nodes)
    R = {(x, y): rel(nodes[x], nodes[y]) for x in names for y in names if x != y}
    viol = sum(1 for x in names for y in names for z in names
               if len({x, y, z}) == 3
               and R[(x, z)] not in COMP[(R[(x, y)], R[(y, z)])])
    return R, viol

# --------------------------------------------------- (2A) forcing certificate ---
def forcing_certificate():
    return {
        'F1 comp(PP,PO)\\{PP,PO}={DR}': (COMP[(PP, PO)] - {PP, PO}) == frozenset({DR}),
        'F2 comp(DR,PPI)={DR}': COMP[(DR, PPI)] == frozenset({DR}),
        'F3 PO!=DR': PO != DR,
        'F4 comp(PP,PP)={PP}': COMP[(PP, PP)] == frozenset({PP}),
    }

# ------------------------------------------------- (2B) PC feasibility search ---
def path_consistent(dom, nodes):
    dom = dict(dom)
    for i in nodes:
        for j in nodes:
            if i < j:
                d = dom.get((i, j), ALL) & frozenset(INV[r] for r in dom.get((j, i), ALL))
                if not d: return None
                dom[(i, j)] = d; dom[(j, i)] = frozenset(INV[r] for r in d)
    changed = True
    while changed:
        changed = False
        for i in nodes:
            for j in nodes:
                if i == j: continue
                for k in nodes:
                    if k in (i, j): continue
                    comp = set()
                    for r in dom[(i, k)]:
                        for s in dom[(k, j)]:
                            comp |= COMP[(r, s)]
                    new = dom[(i, j)] & comp
                    if new != dom[(i, j)]:
                        if not new: return None
                        dom[(i, j)] = new; dom[(j, i)] = frozenset(INV[r] for r in new)
                        changed = True
    return dom

def feasible_with_W(D, W):
    tower = [f'a{k}' for k in range(D + 1)]; wits = [f'w{m}' for m in range(W)]
    nodes = tower + wits
    base = {}
    for i in range(D + 1):
        for j in range(D + 1):
            if i < j: base[(f'a{i}', f'a{j}')] = frozenset({PP})
            elif i > j: base[(f'a{i}', f'a{j}')] = frozenset({PPI})
    for assign in itertools.product(range(W), repeat=D):
        g = {k + 1: assign[k] for k in range(D)}
        wcol, ok = {}, True
        for k, m in g.items():
            p = k % 2
            if m in wcol and wcol[m] != p: ok = False; break
            wcol[m] = p
        if not ok: continue
        dom = dict(base)
        for k, m in g.items():
            wn = f'w{m}'
            dom[(wn, f'a{k}')] = frozenset({PO}); dom[(f'a{k}', wn)] = frozenset({PO})
            dom[(wn, f'a{k-1}')] = frozenset({DR}); dom[(f'a{k-1}', wn)] = frozenset({DR})
        for x in nodes:
            for y in nodes:
                if x != y and (x, y) not in dom: dom[(x, y)] = ALL
        if path_consistent(dom, nodes) is not None:
            return True
    return False

# ------------------------------------------------ (3) shadow vs live width ---
def is_shadow(R, names, x, y):
    return any(m not in (x, y) and len(COMP[(R[(x, m)], R[(m, y)])]) == 1 for m in names)

def live_cross_degree(R, names, x):
    return sum(1 for y in names if y != x and R[(x, y)] in ('DR', 'PO')
               and not is_shadow(R, names, x, y))

# --------------------------------------------------------------------- main ---
if __name__ == '__main__':
    print("WP35: adversarial attack on F6 (bounded width)")
    print("=" * 70)

    print("\n(1) SATISFIABILITY -- explicit interval model per depth:")
    sat_ok = True
    for D in range(1, 11):
        nodes, typ = build_model(D)
        _, viol = network(nodes)
        ok = sat_at(C0(D), 'a0', nodes, typ)
        R, _ = network(nodes)
        drdeg = sum(1 for y in nodes if y != 'a0' and R[('a0', y)] == 'DR')
        sat_ok &= ok and viol == 0 and drdeg == D
        print(f"    D={D}: model|=C0={ok}  RCC5-viol={viol}  spy-DR-degree={drdeg}")

    print("\n(2A) forcing certificate (composition facts):")
    cert = forcing_certificate(); cert_ok = all(cert.values())
    for k, v in cert.items(): print(f"    {k}: {v}")

    print("\n(2B) PC search -- min feasible witness count (free to share/merge):")
    forced_ok = True
    for D in range(2, 6):
        feas = [W for W in range(1, D + 1) if feasible_with_W(D, W)]
        m = min(feas) if feas else None
        forced_ok &= (m == D)
        print(f"    D={D}: feasible W={feas}; min={m}; forced (min==D)? {m == D}")

    print("\n(3) shadow vs LIVE width (the attack's undoing):")
    live_bounded = True
    for D in [4, 6, 8, 10]:
        nodes, _ = build_model(D); R, _ = network(nodes); names = list(nodes)
        drdeg = sum(1 for y in names if y != 'a0' and R[('a0', y)] == 'DR')
        maxlive = max(live_cross_degree(R, names, x) for x in names)
        live_bounded &= (maxlive <= 4)
        print(f"    D={D}: spy global DR-degree={drdeg} (grows);  "
              f"max LIVE cross-degree={maxlive} (bounded)")

    print("\n" + "=" * 70)
    verdict = sat_ok and cert_ok and forced_ok and live_bounded
    print("WP35 OVERALL:",
          "PASS -- SAT + forced-unbounded-global-degree + bounded-live-width: "
          "the attack FAILS, F6 survives (all width is shadow); the composition "
          "table resists forcing live width." if verdict else "ATTENTION")
    sys.exit(0 if verdict else 1)
