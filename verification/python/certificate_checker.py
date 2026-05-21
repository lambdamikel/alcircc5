"""
WP2 certificate validity checker, extended to DR/PO mosaics (per GPT-5.5
round-2 verification.zip review section 3.2).

Implements the validity-condition checker for finite generated split-forest
certificates per Definition 4.1 (def:certificate) and Definition 4.5 (def:valid)
of papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.tex.

Scope
-----
This version covers both the vertical fragment AND the DR/PO mosaic
fragment.  Conditions checked:

  - V1  type legality (Hintikka types over the closure of C_0)
  - V2  context legality (mosaic Hintikka types, RCC5 composition on
        triples, EQ-reflexivity, INV-converse, typed relation-safety)
  - V3  vertical safety (forall PP/PPI propagation on the strict graph)
  - V4  equality-aware vertical existential discharge
  - V5  equality-aware vertical universal discharge
  - V6  DR/PO existential support (each state-level exists R.D for R in
        {DR,PO} has a declared mosaic witness)
  - V7  DR/PO universal safety (state-level forall R.D propagates to
        every mosaic neighbor at relation R from any source position)
  - V8  support closure (basic: every source position is in a declared
        mosaic with matching tau).  Full triple-support is exercised by
        the patchwork fuzzer (mosaic_closure_search.py).
  - V9  typed equality congruence on ports (Ea, Eb)
  - V10 exact summaries (vacuous in this representation)

The hand-crafted corpus exercises the three load-bearing fixes from the
GPT-5.5 round-2 review:

  G1 (profile-port equality contradicts vertical separation on self-loops)
     -> tested by C_up = exists PP.top  &  forall PP.exists PP.top, which
        admits a one-state cycle on par_Q.  Under occurrence-level equality
        (s ~ s only trivially), this is consistent.  Under profile-port
        equality, reflexivity + vertical separation contradict.
  G3 (multiple upward PP witnesses with different parents)
     -> tested by C_AB which forces two equality-mate occurrences with
        different selected parents.
  G4 (rootless orientation)
     -> tested implicitly by allowing par_Q(s) = s (no ambient root).

The test corpus also includes two known-UNSAT concepts that exercise the
soundness side: the checker must reject every candidate certificate.

Run:  python3 verification/python/certificate_checker.py
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from typing import Optional


# -----------------------------------------------------------------------------
# Concept syntax in NNF.  We do not need full ALC; just what the corpus needs.
# -----------------------------------------------------------------------------

BASE_RELS = ('EQ', 'DR', 'PO', 'PP', 'PPI')
VERTICAL = ('PP', 'PPI')
MOSAIC = ('DR', 'PO')

INV = {'EQ': 'EQ', 'DR': 'DR', 'PO': 'PO', 'PP': 'PPI', 'PPI': 'PP'}

# RCC5 composition table (brute-force verified in WP1).
# Used by V2 (mosaic legality) and V8 (support closure on triples).
COMP = {
    ('EQ', 'EQ'): frozenset({'EQ'}),
    ('EQ', 'DR'): frozenset({'DR'}),
    ('EQ', 'PO'): frozenset({'PO'}),
    ('EQ', 'PP'): frozenset({'PP'}),
    ('EQ', 'PPI'): frozenset({'PPI'}),
    ('DR', 'EQ'): frozenset({'DR'}),
    ('DR', 'DR'): frozenset({'EQ', 'DR', 'PO', 'PP', 'PPI'}),
    ('DR', 'PO'): frozenset({'DR', 'PO', 'PP'}),
    ('DR', 'PP'): frozenset({'DR', 'PO', 'PP'}),
    ('DR', 'PPI'): frozenset({'DR'}),
    ('PO', 'EQ'): frozenset({'PO'}),
    ('PO', 'DR'): frozenset({'DR', 'PO', 'PPI'}),
    ('PO', 'PO'): frozenset({'EQ', 'DR', 'PO', 'PP', 'PPI'}),
    ('PO', 'PP'): frozenset({'PO', 'PP'}),
    ('PO', 'PPI'): frozenset({'DR', 'PO', 'PPI'}),
    ('PP', 'EQ'): frozenset({'PP'}),
    ('PP', 'DR'): frozenset({'DR'}),
    ('PP', 'PO'): frozenset({'DR', 'PO', 'PP'}),
    ('PP', 'PP'): frozenset({'PP'}),
    ('PP', 'PPI'): frozenset({'EQ', 'DR', 'PO', 'PP', 'PPI'}),
    ('PPI', 'EQ'): frozenset({'PPI'}),
    ('PPI', 'DR'): frozenset({'DR', 'PO', 'PPI'}),
    ('PPI', 'PO'): frozenset({'PO', 'PPI'}),
    ('PPI', 'PP'): frozenset({'EQ', 'PO', 'PP', 'PPI'}),
    ('PPI', 'PPI'): frozenset({'PPI'}),
}


@dataclass(frozen=True)
class Concept:
    """A concept formula in negation normal form.

    kind in {'top', 'bot', 'atom', 'neg', 'and', 'or', 'exists', 'forall'}.
      atom: name = atom name (string)
      neg : sub is an atomic concept ('atom') only (NNF invariant)
      and/or: subs = tuple of concepts
      exists/forall: role = relation in BASE_RELS, sub = concept
    """
    kind: str
    name: Optional[str] = None
    role: Optional[str] = None
    sub: Optional['Concept'] = None
    subs: tuple = ()

    def __repr__(self) -> str:
        if self.kind == 'top':
            return 'T'
        if self.kind == 'bot':
            return '_|_'
        if self.kind == 'atom':
            return self.name
        if self.kind == 'neg':
            return f'~{self.sub}'
        if self.kind == 'and':
            return '(' + ' & '.join(str(s) for s in self.subs) + ')'
        if self.kind == 'or':
            return '(' + ' | '.join(str(s) for s in self.subs) + ')'
        if self.kind == 'exists':
            return f'E{self.role}.{self.sub}'
        if self.kind == 'forall':
            return f'A{self.role}.{self.sub}'
        return f'?{self.kind}?'


def TOP() -> Concept:
    return Concept('top')


def BOT() -> Concept:
    return Concept('bot')


def Atom(n: str) -> Concept:
    return Concept('atom', name=n)


def Neg(c: Concept) -> Concept:
    """NNF negation: pushes the negation inward."""
    if c.kind == 'top':
        return BOT()
    if c.kind == 'bot':
        return TOP()
    if c.kind == 'atom':
        return Concept('neg', sub=c)
    if c.kind == 'neg':
        return c.sub
    if c.kind == 'and':
        return Concept('or', subs=tuple(Neg(s) for s in c.subs))
    if c.kind == 'or':
        return Concept('and', subs=tuple(Neg(s) for s in c.subs))
    if c.kind == 'exists':
        return Concept('forall', role=c.role, sub=Neg(c.sub))
    if c.kind == 'forall':
        return Concept('exists', role=c.role, sub=Neg(c.sub))
    raise ValueError(f'cannot negate {c.kind}')


def And(*cs: Concept) -> Concept:
    return Concept('and', subs=tuple(cs))


def Or(*cs: Concept) -> Concept:
    return Concept('or', subs=tuple(cs))


def E(r: str, c: Concept) -> Concept:
    return Concept('exists', role=r, sub=c)


def A(r: str, c: Concept) -> Concept:
    return Concept('forall', role=r, sub=c)


def closure(c0: Concept) -> frozenset:
    """Smallest set closed under subformula and NNF complement."""
    out = set()

    def visit(c: Concept) -> None:
        if c in out:
            return
        out.add(c)
        out.add(Neg(c))
        if c.kind == 'neg':
            visit(c.sub)
        elif c.kind in ('and', 'or'):
            for s in c.subs:
                visit(s)
        elif c.kind in ('exists', 'forall'):
            visit(c.sub)

    visit(c0)
    visit(TOP())
    visit(BOT())
    return frozenset(out)


# -----------------------------------------------------------------------------
# Hintikka types over the closure.
# -----------------------------------------------------------------------------

def is_hintikka_type(tau: frozenset, cl: frozenset) -> bool:
    """Check that tau is a closure type per the repaired proof's local conditions.

    - top in tau, bot not in tau
    - exactly one of {C, neg C} for every C in cl
    - C & D in tau iff C, D in tau
    - C | D in tau iff (C in tau or D in tau)
    - EQ modalities locally normalized:
        exists EQ.D in tau iff D in tau
        forall EQ.D in tau iff D in tau
    """
    if TOP() not in tau or BOT() in tau:
        return False
    for c in cl:
        nc = Neg(c)
        if (c in tau) == (nc in tau):
            return False
    for c in tau:
        if c.kind == 'and':
            if not all(s in tau for s in c.subs):
                return False
        elif c.kind == 'or':
            if not any(s in tau for s in c.subs):
                return False
        elif c.kind == 'exists' and c.role == 'EQ':
            if (c.sub in tau) != (c in tau):
                return False
        elif c.kind == 'forall' and c.role == 'EQ':
            if (c.sub in tau) != (c in tau):
                return False
    for c in cl:
        if c.kind == 'and' and c in tau:
            if not all(s in tau for s in c.subs):
                return False
        if c.kind == 'or' and c in tau:
            if not any(s in tau for s in c.subs):
                return False
    return True


# -----------------------------------------------------------------------------
# Certificate data structure (vertical fragment).
#
# We use the bare minimum needed for V1, V3, V4, V5, V9, V10:
#
#   S    = profile state names (set of strings)
#   s0   = distinguished start state
#   lam  = map state -> Hintikka type (frozenset of concepts)
#   par  = partial parent map state -> state (None means no selected parent;
#          self-loop par[s] = s is allowed and corresponds to ultimately
#          periodic ancestor walks)
#   ports = state -> set of (port_id, color)
#   eq_ports = set of (state, port_id) pairs declared equal
# -----------------------------------------------------------------------------

@dataclass
class Mosaic:
    """Finite RCC5 network used to back DR/PO existentials and contain
    typed witnesses for them.

    Per Def 1.2 of repaired_split_forest_no_automata_proof.tex: a mosaic
    over a finite position set P is a triple (P, tau, L) with
      - tau : P -> closure type
      - L   : P x P -> base relation (with L(p,p) = EQ and L(p,q) = INV(L(q,p)))
      - L respects the RCC5 composition table on triples
      - any existential declared to be witnessed inside the mosaic has a
        position q with L(p,q) = R and D in tau(q).

    Type completeness (each tau(p) being a Hintikka type over cl(C_0)) is
    enforced by V2 in conjunction with the Hintikka check.
    """
    name: str
    positions: tuple
    tau: dict   # {position: frozenset of concepts}
    L: dict     # {(p, q): relation}, must include all ordered pairs


@dataclass
class Certificate:
    S: tuple
    s0: str
    lam: dict
    par: dict = field(default_factory=dict)
    ports: dict = field(default_factory=dict)
    eq_ports: set = field(default_factory=set)
    # DR/PO mosaic infrastructure (optional; empty means vertical-only cert).
    mosaics: list = field(default_factory=list)               # list[Mosaic]
    source_pos: dict = field(default_factory=dict)            # {state: list[(mosaic_name, pos)]}
    dr_po_wit: dict = field(default_factory=dict)             # {(state, concept): (mosaic_name, pos)}
    name: str = '?'

    def parents_of(self, s: str):
        out = []
        if s in self.par:
            out.append(self.par[s])
        return out

    def mosaic_by_name(self, mname: str):
        for m in self.mosaics:
            if m.name == mname:
                return m
        return None


# -----------------------------------------------------------------------------
# Equality-aware reachability.
#
# Per Definition 4.3 (repaired proof, lines 411-431):
#
#   reach_PP : transitive closure of par_Q (cycles count as strict reachability)
#   Mate_Q(s) = states whose ports are eq^Q-equivalent to a port of s
#   Reach_R(s, t) iff exists s_hat in Mate_Q(s) with s_hat reach_R t
#
# Note: a cycle counts as STRICT reachability because each lap unfolds to a
# fresh occurrence.  This means s reach_PP s holds whenever s is on a parent
# cycle.
# -----------------------------------------------------------------------------

def eq_classes(cert: Certificate):
    """Union-find on declared equality ports."""
    parent = {}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[rx] = ry

    nodes = []
    for s, pset in cert.ports.items():
        for (pid, _color) in pset:
            n = (s, pid)
            nodes.append(n)
            parent[n] = n
    for (a, b) in cert.eq_ports:
        if a in parent and b in parent:
            union(a, b)

    classes = {}
    for n in nodes:
        r = find(n)
        classes.setdefault(r, set()).add(n)
    return classes


def mate(cert: Certificate, s: str) -> frozenset:
    """States with a port eq-equivalent to some port of s.

    For the vertical fragment, when a state has no declared ports, Mate(s) = {s}.
    This matches the repaired proof's intent: equality is opt-in, never inferred.
    """
    classes = eq_classes(cert)
    if not cert.ports.get(s):
        return frozenset({s})
    out = {s}
    my_ports = {(s, pid) for (pid, _color) in cert.ports[s]}
    for cls in classes.values():
        if cls & my_ports:
            for (t, _pid) in cls:
                out.add(t)
    return frozenset(out)


def reach_PP(cert: Certificate, src: str) -> frozenset:
    """States reachable from src via 1+ par_Q steps (cycles count strict)."""
    out = set()
    s = cert.par.get(src)
    visited = set()
    while s is not None and s not in visited:
        visited.add(s)
        out.add(s)
        s = cert.par.get(s)
    # Re-visiting once more on a cycle keeps producing fresh occurrences in the
    # unfolding; on the finite quotient, reachability is just the set of states
    # encountered above.  Self-loops produce reach_PP(s) = {s, ...}.
    return frozenset(out)


def reach_PPI(cert: Certificate, src: str) -> frozenset:
    """Inverse-parent reachability: states from which src is PP-reachable."""
    out = set()
    for t in cert.S:
        if src in reach_PP(cert, t):
            out.add(t)
    return frozenset(out)


def Reach(cert: Certificate, src: str, R: str) -> frozenset:
    """Equality-aware reachability over Mate(src)."""
    out = set()
    for sh in mate(cert, src):
        if R == 'PP':
            out |= reach_PP(cert, sh)
        elif R == 'PPI':
            out |= reach_PPI(cert, sh)
    return frozenset(out)


# -----------------------------------------------------------------------------
# Validity checks (vertical fragment).
# -----------------------------------------------------------------------------

class ValidityReport:
    def __init__(self, cert_name: str):
        self.cert_name = cert_name
        self.failures = []
        self.passes = []

    def fail(self, code: str, msg: str) -> None:
        self.failures.append((code, msg))

    def ok(self, code: str, msg: str = '') -> None:
        self.passes.append((code, msg))

    def is_valid(self) -> bool:
        return not self.failures


def check_V1_type_legality(cert: Certificate, c0: Concept, cl: frozenset,
                           rep: ValidityReport) -> None:
    """V1: every lam(s) is a closure type; C_0 in lam(s_0); EQ-modal normalized."""
    if c0 not in cert.lam[cert.s0]:
        rep.fail('V1', f'C0 not in lambda(s_0={cert.s0})')
    for s in cert.S:
        tau = cert.lam[s]
        if not is_hintikka_type(tau, cl):
            rep.fail('V1', f'lambda({s}) is not a Hintikka type')
            return
    rep.ok('V1', f'all {len(cert.S)} states carry Hintikka types and C0 in lambda(s_0)')


def check_V3_vertical_safety(cert: Certificate, rep: ValidityReport) -> None:
    """V3: forall PP.D in lam(s) and s reach_PP t  ==>  D in lam(t).  (Same for PPI.)"""
    for s in cert.S:
        for c in cert.lam[s]:
            if c.kind == 'forall' and c.role in VERTICAL:
                R = c.role
                targets = reach_PP(cert, s) if R == 'PP' else reach_PPI(cert, s)
                for t in targets:
                    if c.sub not in cert.lam[t]:
                        rep.fail('V3',
                                 f'{s}: forall {R}.{c.sub} but {c.sub} not in lambda({t})')
                        return
    rep.ok('V3', 'all PP/PPI universals propagate along reach_R')


def check_V4_existential_discharge(cert: Certificate, rep: ValidityReport) -> None:
    """V4: exists R.D in lam(s) with R in {PP,PPI}  ==>  some t with s Reach_R t and D in lam(t)."""
    for s in cert.S:
        for c in cert.lam[s]:
            if c.kind == 'exists' and c.role in VERTICAL:
                R = c.role
                targets = Reach(cert, s, R)
                if not any(c.sub in cert.lam[t] for t in targets):
                    rep.fail('V4',
                             f'{s}: exists {R}.{c.sub} not discharged '
                             f'(Reach_{R}={sorted(targets)}, '
                             f'no t carries {c.sub})')
                    return
    rep.ok('V4', 'all PP/PPI existentials are eq-aware reach-discharged')


def check_V5_universal_via_mate(cert: Certificate, rep: ValidityReport) -> None:
    """V5: forall R.D in lam(s) with R in {PP,PPI}  ==>  for all t with s Reach_R t, D in lam(t).

    Strictly stronger than V3: V5 quantifies over mates, V3 only over the
    occurrence itself.  Both must hold.
    """
    for s in cert.S:
        for c in cert.lam[s]:
            if c.kind == 'forall' and c.role in VERTICAL:
                R = c.role
                for t in Reach(cert, s, R):
                    if c.sub not in cert.lam[t]:
                        rep.fail('V5',
                                 f'{s}: forall {R}.{c.sub} but '
                                 f'mate-path reach {t} lacks {c.sub}')
                        return
    rep.ok('V5', 'all PP/PPI universals propagate along Reach_R (mate-aware)')


def check_V9_typed_equality_congruence(cert: Certificate, rep: ValidityReport) -> None:
    """V9 Ea-Ed: typed equality congruence.

    Ea: if ports of s, t are eq^Q-equivalent, then lambda(s) = lambda(t).
    Eb: no two states connected by strict reach_PP/PPI are eq^Q-equivalent
        through any ports.
    Ed (partial): equality of profile names alone does not generate eq^Q.
        This is guaranteed by construction (we only record explicit ports).
    """
    classes = eq_classes(cert)
    state_partners = {s: {s} for s in cert.S}
    for cls in classes.values():
        states_in_cls = {n[0] for n in cls}
        for s in states_in_cls:
            state_partners[s] |= states_in_cls

    for s in cert.S:
        for t in state_partners[s]:
            if cert.lam[s] != cert.lam[t]:
                rep.fail('V9.Ea',
                         f'{s} and {t} share eq-ports but lambda differs')
                return

    for s in cert.S:
        pp_targets = reach_PP(cert, s)
        for t in pp_targets:
            if t == s:
                continue
            if t in state_partners[s]:
                rep.fail('V9.Eb',
                         f'{s} reach_PP {t} but they share eq-ports')
                return
        ppi_targets = reach_PPI(cert, s)
        for t in ppi_targets:
            if t == s:
                continue
            if t in state_partners[s]:
                rep.fail('V9.Eb',
                         f'{s} reach_PPI {t} but they share eq-ports')
                return
    rep.ok('V9', 'typed-EQ congruence consistent (Ea, Eb)')


def _typed_relation_safety_ok(L: dict, tau: dict, positions: tuple) -> Optional[str]:
    """For every pair (p, q) with L(p,q) = R, every forall R.D in tau(p)
    must put D in tau(q).  Returns an error message or None if clean.
    """
    for p in positions:
        for c in tau[p]:
            if c.kind == 'forall':
                R = c.role
                for q in positions:
                    if L[(p, q)] == R and c.sub not in tau[q]:
                        return (f'pos {p}: forall {R}.{c.sub} but {c.sub} '
                                f'not in tau({q}) [L({p},{q})={R}]')
    return None


def check_V2_context_legality(cert: Certificate, cl: frozenset,
                              rep: ValidityReport) -> None:
    """V2: every mosaic is a legal RCC5 network with typed relation-safety.

    Checks:
      - tau(p) is a Hintikka type over cl for every position p,
      - L(p,p) = EQ,
      - L(p,q) = INV(L(q,p)),
      - L respects RCC5 composition on every triple,
      - typed relation-safety: forall R.D in tau(p) and L(p,q) = R implies D in tau(q).
    """
    if not cert.mosaics:
        rep.ok('V2', 'no mosaics declared; vacuously legal')
        return
    for m in cert.mosaics:
        # Hintikka types
        for p in m.positions:
            if p not in m.tau:
                rep.fail('V2', f'mosaic {m.name}: no tau for position {p}')
                return
            if not is_hintikka_type(m.tau[p], cl):
                rep.fail('V2', f'mosaic {m.name}: tau({p}) is not a Hintikka type')
                return
        # Reflexivity and converse
        for p in m.positions:
            if m.L.get((p, p)) != 'EQ':
                rep.fail('V2', f'mosaic {m.name}: L({p},{p}) = {m.L.get((p,p))} != EQ')
                return
        for p in m.positions:
            for q in m.positions:
                if (p, q) not in m.L:
                    rep.fail('V2', f'mosaic {m.name}: L({p},{q}) missing')
                    return
                if m.L[(p, q)] != INV[m.L[(q, p)]]:
                    rep.fail('V2',
                             f'mosaic {m.name}: L({p},{q})={m.L[(p,q)]} but '
                             f'INV(L({q},{p}))=INV({m.L[(q,p)]})={INV[m.L[(q,p)]]}')
                    return
        # Composition on triples
        for p in m.positions:
            for q in m.positions:
                for r in m.positions:
                    rpr = m.L[(p, r)]
                    rpq = m.L[(p, q)]
                    rqr = m.L[(q, r)]
                    if rpr not in COMP[(rpq, rqr)]:
                        rep.fail('V2',
                                 f'mosaic {m.name}: L({p},{r})={rpr} not in '
                                 f'comp(L({p},{q}),L({q},{r}))=comp({rpq},{rqr})'
                                 f'={sorted(COMP[(rpq, rqr)])}')
                        return
        # Typed relation-safety
        err = _typed_relation_safety_ok(m.L, m.tau, m.positions)
        if err is not None:
            rep.fail('V2', f'mosaic {m.name}: {err}')
            return
    rep.ok('V2', f'{len(cert.mosaics)} mosaics are legal RCC5 networks with typed safety')


def check_V6_dr_po_existential_support(cert: Certificate,
                                       rep: ValidityReport) -> None:
    """V6: every exists R.D in lam(s) with R in {DR, PO} has a declared
    witness (mosaic, q) where the source position p of s in that mosaic
    satisfies L(p, q) = R and D in tau(q).

    Note: a certificate with no mosaics is NOT vacuously V6-legal -- if
    any state carries a DR/PO existential, the absence of a witness must
    cause rejection. (Fix per GPT-5.5 May 2026 review.)
    """
    for s in cert.S:
        for c in cert.lam[s]:
            if c.kind != 'exists' or c.role not in MOSAIC:
                continue
            key = (s, c)
            if key not in cert.dr_po_wit:
                rep.fail('V6',
                         f'{s}: exists {c.role}.{c.sub} has no declared '
                         f'mosaic witness')
                return
            mname, q = cert.dr_po_wit[key]
            m = cert.mosaic_by_name(mname)
            if m is None:
                rep.fail('V6',
                         f'{s}: witness mosaic {mname!r} for {c} not in cert.mosaics')
                return
            sources = [pos for (mn, pos) in cert.source_pos.get(s, [])
                       if mn == mname]
            if not sources:
                rep.fail('V6',
                         f'{s}: witness claims mosaic {mname} but s has no '
                         f'source position there')
                return
            ok = False
            for p in sources:
                if m.L.get((p, q)) == c.role and c.sub in m.tau.get(q, frozenset()):
                    ok = True
                    break
            if not ok:
                rep.fail('V6',
                         f'{s}: witness ({mname},{q}) for exists {c.role}.{c.sub} '
                         f'fails: no source p with L(p,{q})={c.role} and '
                         f'{c.sub} in tau({q})')
                return
    rep.ok('V6', 'all DR/PO existentials are mosaic-witnessed')


def check_V7_dr_po_universal_safety(cert: Certificate,
                                    rep: ValidityReport) -> None:
    """V7: every forall R.D in lam(s) with R in {DR, PO} must propagate
    D to every q at relation R from any source position of s in any mosaic.
    """
    if not cert.mosaics:
        rep.ok('V7', 'no mosaics declared; no DR/PO universals checked here')
        return
    for s in cert.S:
        for c in cert.lam[s]:
            if c.kind != 'forall' or c.role not in MOSAIC:
                continue
            for (mname, p) in cert.source_pos.get(s, []):
                m = cert.mosaic_by_name(mname)
                if m is None:
                    continue
                for q in m.positions:
                    if m.L[(p, q)] == c.role and c.sub not in m.tau[q]:
                        rep.fail('V7',
                                 f'{s}: forall {c.role}.{c.sub} but {c.sub} '
                                 f'not in tau({q}) of mosaic {mname} '
                                 f'(source {p}, L({p},{q})={c.role})')
                        return
    rep.ok('V7', 'all DR/PO universals propagate to mosaic neighbors')


def check_V8_support_closure(cert: Certificate, rep: ValidityReport) -> None:
    """V8 (basic): support closure on the declared mosaic family.

    Minimum check: every state-existential pair backed by V6 names a
    mosaic that is in the family, and every source position of every
    state lies in a declared mosaic.  Full triple-support closure (every
    abstract triple shape generated by the certificate appears in some
    mosaic) is handled by the patchwork fuzzer (mosaic_closure_search.py)
    and is not implemented here.
    """
    if not cert.mosaics:
        rep.ok('V8', 'no mosaics declared; vacuously support-closed')
        return
    mnames = {m.name for m in cert.mosaics}
    for s in cert.S:
        for (mname, p) in cert.source_pos.get(s, []):
            if mname not in mnames:
                rep.fail('V8', f'{s}: source mosaic {mname!r} not in cert.mosaics')
                return
            m = cert.mosaic_by_name(mname)
            if p not in m.positions:
                rep.fail('V8',
                         f'{s}: source position {p} not in mosaic {mname}.positions')
                return
            if cert.lam[s] != m.tau[p]:
                rep.fail('V8',
                         f'{s}: lambda({s}) != mosaic {mname}.tau({p}); '
                         f'source-position typing must agree with state label')
                return
    rep.ok('V8', f'{len(cert.mosaics)} mosaics: basic support closure holds')


def check_V10_exact_summaries(cert: Certificate, rep: ValidityReport) -> None:
    """V10: reachability summaries stored in profiles match the finite graph.

    In this vertical-fragment encoding, we have no separately-stored summaries
    beyond what reach_PP / reach_PPI compute on demand; V10 is therefore
    trivially satisfied modulo our representation.  This check exists to be
    upgraded once the full mosaic store is added.
    """
    rep.ok('V10', 'no separately-stored summaries; vacuously consistent')


def check_certificate(cert: Certificate, c0: Concept,
                      cl: Optional[frozenset] = None) -> ValidityReport:
    if cl is None:
        cl = closure(c0)
    rep = ValidityReport(cert.name)
    check_V1_type_legality(cert, c0, cl, rep)
    if not rep.is_valid():
        return rep
    check_V2_context_legality(cert, cl, rep)
    if not rep.is_valid():
        return rep
    check_V3_vertical_safety(cert, rep)
    check_V4_existential_discharge(cert, rep)
    check_V5_universal_via_mate(cert, rep)
    check_V6_dr_po_existential_support(cert, rep)
    check_V7_dr_po_universal_safety(cert, rep)
    check_V8_support_closure(cert, rep)
    check_V9_typed_equality_congruence(cert, rep)
    check_V10_exact_summaries(cert, rep)
    return rep


# -----------------------------------------------------------------------------
# Helpers for building Hintikka types over closures.
# -----------------------------------------------------------------------------

def saturate_for(cl: frozenset, must: list) -> frozenset:
    """Build the smallest Hintikka type over `cl` containing the given concepts.

    Decisions on undetermined elements are made by leaving them out and then
    accepting their negation.  When 'must' fixes a contradictory pair, raises.
    Backtracking is unnecessary for the small hand-crafted corpora here.
    """
    forced = set(must) | {TOP()}
    changed = True
    while changed:
        changed = False
        for c in list(forced):
            if c.kind == 'and':
                for s in c.subs:
                    if s not in forced:
                        forced.add(s)
                        changed = True
            elif c.kind == 'or':
                if not any(s in forced for s in c.subs):
                    forced.add(c.subs[0])
                    changed = True
            elif c.kind == 'exists' and c.role == 'EQ':
                if c.sub not in forced:
                    forced.add(c.sub)
                    changed = True
            elif c.kind == 'forall' and c.role == 'EQ':
                if c.sub not in forced:
                    forced.add(c.sub)
                    changed = True
        for c in cl:
            if c.kind == 'and' and c not in forced:
                if all(s in forced for s in c.subs):
                    forced.add(c)
                    changed = True
            if c.kind == 'or' and c not in forced:
                if any(s in forced for s in c.subs):
                    forced.add(c)
                    changed = True
    # Consistency: forced cannot contain a concept and its NNF complement.
    for c in list(forced):
        if Neg(c) in forced:
            raise ValueError(f'forced concepts {must} inconsistent at {c} / {Neg(c)}')
    if BOT() in forced:
        raise ValueError(f'forced concepts {must} inconsistent (BOT forced)')
    tau = set()
    # Pair up each c in cl with its NNF complement and pick exactly one.
    seen = set()
    for c in cl:
        if c in seen:
            continue
        nc = Neg(c)
        seen.add(c)
        seen.add(nc)
        if c in forced:
            tau.add(c)
        elif nc in forced:
            tau.add(nc)
        else:
            # Default: prefer the more "negative" option (the one whose
            # presence does not introduce further constraints).  For
            # existentials, prefer the universal complement.
            if c.kind == 'exists' and c.role in VERTICAL:
                tau.add(nc)
            elif nc.kind == 'exists' and nc.role in VERTICAL:
                tau.add(c)
            else:
                tau.add(nc if c.kind in ('and', 'exists') else c)
    tau.add(TOP())
    return frozenset(tau)


# -----------------------------------------------------------------------------
# Test corpus.
# -----------------------------------------------------------------------------

def cert_C_up() -> tuple:
    """C_up = exists PP.top  &  forall PP.exists PP.top.

    One-state certificate with a parent self-loop.  Exercises G1 (no
    profile-port equality is asserted, so self-loop does not contradict
    vertical separation).
    """
    e_pp_top = E('PP', TOP())
    a_pp_e_pp_top = A('PP', e_pp_top)
    C_up = And(e_pp_top, a_pp_e_pp_top)
    cl = closure(C_up)
    tau = saturate_for(cl, [C_up])
    cert = Certificate(
        S=('s0',),
        s0='s0',
        lam={'s0': tau},
        par={'s0': 's0'},
        ports={},
        eq_ports=set(),
        name='C_up (PP self-loop, no eq ports)',
    )
    return cert, C_up


def cert_C_up_with_eq_port() -> tuple:
    """C_up with an equality port declared on the self-loop state.

    This is the G1 stress: profile-port reflexivity (M1 of v2.1) plus
    vertical separation (Eb of repaired proof) on a PP self-loop.

    Under the repaired proof's *occurrence-level* equality, equality is
    explicit and is *not* generated by profile reflexivity, so the
    certificate cannot declare its single port equal to itself by an
    "identity port-map" - there is no port-map at all.  The certificate
    we test here declares NO eq_ports, so V9.Eb is satisfied.  This shows
    the repaired proof's discipline: equality is opt-in, never auto-generated.
    """
    cert, c0 = cert_C_up()
    cert.ports = {'s0': frozenset({('p0', 'red')})}
    cert.eq_ports = set()
    cert.name = 'C_up with ports, no eq edges'
    return cert, c0


def cert_C_up_with_bad_eq() -> tuple:
    """G1 reproducer (should FAIL V9.Eb).

    Two states linked by PP and explicitly declared eq-equivalent on a port.
    The repaired proof's Eb forbids this.
    """
    e_pp_top = E('PP', TOP())
    a_pp_e_pp_top = A('PP', e_pp_top)
    C_up = And(e_pp_top, a_pp_e_pp_top)
    cl = closure(C_up)
    tau = saturate_for(cl, [C_up])
    cert = Certificate(
        S=('s0', 's1'),
        s0='s0',
        lam={'s0': tau, 's1': tau},
        par={'s0': 's1', 's1': 's1'},
        ports={
            's0': frozenset({('p0', 'red')}),
            's1': frozenset({('p1', 'red')}),
        },
        eq_ports={(('s0', 'p0'), ('s1', 'p1'))},
        name='G1 reproducer: PP plus eq across vertical (should fail V9.Eb)',
    )
    return cert, C_up


def cert_C_AB() -> tuple:
    """C_AB = A & B & exists PP.A & exists PP.B
                & forall PP.(A -> ~B) & forall PP.(B -> ~A).

    The G3 stress: two equality-mate occurrences of the root, one with
    parent sA (an A-type superpart) and one with parent sB (a B-type
    superpart).  Eq-aware reach must visit both.
    """
    a = Atom('A')
    b = Atom('B')
    not_a = Neg(a)
    not_b = Neg(b)
    e_pp_a = E('PP', a)
    e_pp_b = E('PP', b)
    a_pp_a_imp_nb = A('PP', Or(not_a, not_b))  # A -> ~B equivalent to ~A | ~B
    a_pp_b_imp_na = A('PP', Or(not_b, not_a))  # B -> ~A
    C_AB = And(a, b, e_pp_a, e_pp_b, a_pp_a_imp_nb, a_pp_b_imp_na)
    cl = closure(C_AB)
    tau_root = saturate_for(cl, [C_AB])
    tau_A = saturate_for(cl, [a, not_b, a_pp_a_imp_nb, a_pp_b_imp_na])
    tau_B = saturate_for(cl, [not_a, b, a_pp_a_imp_nb, a_pp_b_imp_na])
    cert = Certificate(
        S=('s_root', 's_root_prime', 's_A', 's_B'),
        s0='s_root',
        lam={
            's_root': tau_root,
            's_root_prime': tau_root,
            's_A': tau_A,
            's_B': tau_B,
        },
        par={
            's_root': 's_A',
            's_root_prime': 's_B',
        },
        ports={
            's_root': frozenset({('p_root', 'g')}),
            's_root_prime': frozenset({('p_root_prime', 'g')}),
        },
        eq_ports={(('s_root', 'p_root'), ('s_root_prime', 'p_root_prime'))},
        name='C_AB (G3): two mates with different selected parents',
    )
    return cert, C_AB


def cert_C_AB_wrong_singleparent() -> tuple:
    """v2.1 style attempt: single occurrence with only one parent.

    Should FAIL V4: only one of exists PP.A, exists PP.B is discharged.
    """
    a = Atom('A')
    b = Atom('B')
    not_a = Neg(a)
    not_b = Neg(b)
    e_pp_a = E('PP', a)
    e_pp_b = E('PP', b)
    a_pp_a_imp_nb = A('PP', Or(not_a, not_b))
    a_pp_b_imp_na = A('PP', Or(not_b, not_a))
    C_AB = And(a, b, e_pp_a, e_pp_b, a_pp_a_imp_nb, a_pp_b_imp_na)
    cl = closure(C_AB)
    tau_root = saturate_for(cl, [C_AB])
    tau_A = saturate_for(cl, [a, not_b, a_pp_a_imp_nb, a_pp_b_imp_na])
    cert = Certificate(
        S=('s_root', 's_A'),
        s0='s_root',
        lam={'s_root': tau_root, 's_A': tau_A},
        par={'s_root': 's_A'},
        ports={},
        eq_ports=set(),
        name='C_AB v2.1-style single-parent (should fail V4)',
    )
    return cert, C_AB


def _build_C_AB_inc():
    """Build the strengthened C_AB^inc formula and its key subterms.

    C_AB^inc = exists PP.A
             & exists PP.B
             & forall PP. ( (~A | (~B & forall PP.~B & forall PPI.~B))
                          & (~B | (~A & forall PP.~A & forall PPI.~A)) )

    Unlike C_AB, this formula forbids the A-superpart and B-superpart from
    being PP-comparable, since any A-witness must have no B in its PP/PPI
    cone (and symmetrically).  This forces two PP-incomparable mate
    occurrences with different selected parents.
    """
    a = Atom('A')
    b = Atom('B')
    not_a = Neg(a)
    not_b = Neg(b)
    no_b_cone = And(not_b, A('PP', not_b), A('PPI', not_b))
    no_a_cone = And(not_a, A('PP', not_a), A('PPI', not_a))
    or1 = Or(not_a, no_b_cone)
    or2 = Or(not_b, no_a_cone)
    body = And(or1, or2)
    fa_pp_body = A('PP', body)
    e_pp_a = E('PP', a)
    e_pp_b = E('PP', b)
    C = And(e_pp_a, e_pp_b, fa_pp_body)
    return C, a, b, not_a, not_b, no_a_cone, no_b_cone, body, fa_pp_body


def cert_C_AB_inc() -> tuple:
    """C_AB^inc (strengthened G3 stress, per GPT-5.5 verification.zip review).

    Valid certificate: two equality-mate occurrences of the root with
    different selected parents, one carrying A (with the full no-B-cone)
    and one carrying B (with the full no-A-cone).  This is the canonical
    incomparability-forcing positive test.
    """
    C, a, b, not_a, not_b, no_a_cone, no_b_cone, body, fa_pp_body = _build_C_AB_inc()
    cl = closure(C)
    tau_root = saturate_for(cl, [C, not_a, not_b])
    tau_A = saturate_for(cl, [a, no_b_cone, body, fa_pp_body])
    tau_B = saturate_for(cl, [b, no_a_cone, body, fa_pp_body])
    cert = Certificate(
        S=('s_root', 's_root_prime', 's_A', 's_B'),
        s0='s_root',
        lam={
            's_root': tau_root,
            's_root_prime': tau_root,
            's_A': tau_A,
            's_B': tau_B,
        },
        par={
            's_root': 's_A',
            's_root_prime': 's_B',
        },
        ports={
            's_root': frozenset({('p_root', 'g')}),
            's_root_prime': frozenset({('p_root_prime', 'g')}),
        },
        eq_ports={(('s_root', 'p_root'), ('s_root_prime', 'p_root_prime'))},
        name='C_AB^inc (G3 strengthened): two mates with different parents',
    )
    return cert, C


def cert_C_AB_inc_singleparent() -> tuple:
    """C_AB^inc single-parent attempt.  Should FAIL V4.

    Only one mate, parented in an A-superpart, so exists PP.B never finds
    a witness in Reach_PP.
    """
    C, a, b, not_a, not_b, no_a_cone, no_b_cone, body, fa_pp_body = _build_C_AB_inc()
    cl = closure(C)
    tau_root = saturate_for(cl, [C, not_a, not_b])
    tau_A = saturate_for(cl, [a, no_b_cone, body, fa_pp_body])
    cert = Certificate(
        S=('s_root', 's_A'),
        s0='s_root',
        lam={'s_root': tau_root, 's_A': tau_A},
        par={'s_root': 's_A'},
        ports={},
        eq_ports=set(),
        name='C_AB^inc single-parent attempt (should fail V4)',
    )
    return cert, C


def cert_C_AB_inc_singlechain() -> tuple:
    """C_AB^inc single-PP-chain attempt.  Should FAIL V3.

    Both A-witness and B-witness placed on one comparable chain
    s_root -> s_A -> s_B.  The inner forall PP.~B at s_A then forces ~B
    at s_B, contradicting B in tau_B.
    """
    C, a, b, not_a, not_b, no_a_cone, no_b_cone, body, fa_pp_body = _build_C_AB_inc()
    cl = closure(C)
    tau_root = saturate_for(cl, [C, not_a, not_b])
    tau_A = saturate_for(cl, [a, no_b_cone, body, fa_pp_body])
    tau_B = saturate_for(cl, [b, no_a_cone, body, fa_pp_body])
    cert = Certificate(
        S=('s_root', 's_A', 's_B'),
        s0='s_root',
        lam={'s_root': tau_root, 's_A': tau_A, 's_B': tau_B},
        par={'s_root': 's_A', 's_A': 's_B'},
        ports={},
        eq_ports=set(),
        name='C_AB^inc single-chain attempt (should fail V3)',
    )
    return cert, C


def cert_C_clash_pp_universal() -> tuple:
    """A bogus certificate for exists PP.A & forall PP.~A (UNSAT).

    The repaired-proof root would need both `exists PP.A` and `forall PP.~A`
    in its type, which is an NNF-complementary pair: no Hintikka type
    satisfies V1.  We hand-craft an explicitly broken type to exercise V1.
    """
    a = Atom('A')
    not_a = Neg(a)
    e_pp_a = E('PP', a)
    a_pp_na = A('PP', not_a)
    C_clash = And(e_pp_a, a_pp_na)
    cl = closure(C_clash)
    # Hand-build a broken type containing both e_pp_a and forall PP.~A.
    broken_root = set()
    seen = set()
    for c in cl:
        if c in seen:
            continue
        nc = Neg(c)
        seen.add(c)
        seen.add(nc)
        if c == e_pp_a:
            broken_root.add(c)
            broken_root.add(nc)  # both: deliberately broken
        elif c == a_pp_na:
            broken_root.add(c)
        elif c == C_clash:
            broken_root.add(c)
        else:
            broken_root.add(nc if c.kind in ('and', 'exists') else c)
    broken_root.add(TOP())
    cert = Certificate(
        S=('s0',),
        s0='s0',
        lam={'s0': frozenset(broken_root)},
        par={},
        ports={},
        eq_ports=set(),
        name='UNSAT: exists PP.A & forall PP.~A (broken type should fail V1)',
    )
    return cert, C_clash


def cert_C_pp_transitive_unsat() -> tuple:
    """forall PP.~C & exists PP.exists PP.C  (UNSAT under PP transitivity).

    PP is transitive: par chain s0 -> s1 -> s2 means s0 reach_PP s2.  So
    forall PP.~C at s0 must propagate ~C to s2, which must also satisfy C.
    Should FAIL V3 (vertical safety).
    """
    cc = Atom('C')
    not_c = Neg(cc)
    a_pp_nc = A('PP', not_c)
    e_pp_e_pp_c = E('PP', E('PP', cc))
    C_concept = And(a_pp_nc, e_pp_e_pp_c)
    cl = closure(C_concept)
    tau_root = saturate_for(cl, [C_concept])
    tau_mid = saturate_for(cl, [not_c, E('PP', cc)])
    tau_leaf = saturate_for(cl, [cc])  # Will lack a_pp_nc / not_c propagation
    # Place forall PP.~C only at the root, so V3 is what catches the chain.
    cert = Certificate(
        S=('s0', 's1', 's2'),
        s0='s0',
        lam={'s0': tau_root, 's1': tau_mid, 's2': tau_leaf},
        par={'s0': 's1', 's1': 's2'},
        ports={},
        eq_ports=set(),
        name='UNSAT: PP-transitive (should fail V3)',
    )
    return cert, C_concept


def cert_WP5_cycle_carries_existential_sat() -> tuple:
    """WP5 positive variant: cycle profile carries exists PP.A and the cycle
    contains a state with A.  Each lap unfolds to fresh occurrences, so the
    request is discharged within one lap.
    """
    a = Atom('A')
    e_pp_a = E('PP', a)
    a_pp_e_pp_a = A('PP', e_pp_a)
    C = And(a, e_pp_a, a_pp_e_pp_a)
    cl = closure(C)
    tau = saturate_for(cl, [a, e_pp_a, a_pp_e_pp_a])
    cert = Certificate(
        S=('s0',),
        s0='s0',
        lam={'s0': tau},
        par={'s0': 's0'},
        ports={},
        eq_ports=set(),
        name='WP5 SAT: cycle with exists PP.A discharged by self-loop',
    )
    return cert, C


def cert_WP5_cycle_unfulfilled_request_unsat() -> tuple:
    """WP5 negative test (from verification_recommendations Section 3.5):
    a cycle that carries exists PP.A but no state on the cycle has A.

    Should FAIL V4: the existential reaches only the cycle's states.
    """
    a = Atom('A')
    not_a = Neg(a)
    e_pp_a = E('PP', a)
    a_pp_na = A('PP', not_a)
    C = And(not_a, e_pp_a, a_pp_na)
    cl = closure(C)
    # Bypass saturate (which would refuse: e_pp_a + a_pp_na is the V1 clash).
    # Instead force tau by hand without the negation pairing.
    seen = set()
    tau_set = set()
    for c in cl:
        if c in seen:
            continue
        nc = Neg(c)
        seen.add(c)
        seen.add(nc)
        if c == a:
            tau_set.add(nc)  # ~A
        elif c == e_pp_a:
            tau_set.add(c)
        elif c == a_pp_na:
            tau_set.add(c)
        elif c == C:
            tau_set.add(c)
        else:
            tau_set.add(nc if c.kind in ('and', 'exists') else c)
    tau_set.add(TOP())
    cert = Certificate(
        S=('s0',),
        s0='s0',
        lam={'s0': frozenset(tau_set)},
        par={'s0': 's0'},
        ports={},
        eq_ports=set(),
        name='WP5 UNSAT: cycle carries exists PP.A but no state has A',
    )
    return cert, C


def cert_dr_witness_sat() -> tuple:
    """exists DR.A backed by a 2-position mosaic with L(p1,p2)=DR.

    Single state s0, source position p1; mosaic m0 has positions {p1,p2}
    with L(p1,p2)=DR, tau(p2) contains A.  V6 must accept the named witness.

    Note: tau_a is forced to contain `exists DR.A` (not `forall DR.~A`) so
    the witness position carries an existential, not a universal complement.
    This matches the model semantics: p2 is DR from p1 which has A, so p2
    itself satisfies `exists DR.A` (via the inverse edge back to p1).
    """
    a = Atom('A')
    e_dr_a = E('DR', a)
    C = e_dr_a
    cl = closure(C)
    tau_root = saturate_for(cl, [C])
    tau_a = saturate_for(cl, [a, e_dr_a])
    L = {
        ('p1', 'p1'): 'EQ', ('p2', 'p2'): 'EQ',
        ('p1', 'p2'): 'DR', ('p2', 'p1'): 'DR',
    }
    m = Mosaic(name='m0', positions=('p1', 'p2'),
               tau={'p1': tau_root, 'p2': tau_a}, L=L)
    cert = Certificate(
        S=('s0',),
        s0='s0',
        lam={'s0': tau_root},
        par={},
        ports={},
        eq_ports=set(),
        mosaics=[m],
        source_pos={'s0': [('m0', 'p1')]},
        dr_po_wit={('s0', e_dr_a): ('m0', 'p2')},
        name='DR witness: exists DR.A discharged by 2-position mosaic (V6 SAT)',
    )
    return cert, C


def cert_po_witness_sat() -> tuple:
    """exists PO.A backed by a 2-position mosaic with L(p1,p2)=PO.

    Same construction as the DR variant: tau_a contains `exists PO.A` so
    the typed relation-safety check sees no `forall PO.~A` at p2.
    """
    a = Atom('A')
    e_po_a = E('PO', a)
    C = e_po_a
    cl = closure(C)
    tau_root = saturate_for(cl, [C])
    tau_a = saturate_for(cl, [a, e_po_a])
    L = {
        ('p1', 'p1'): 'EQ', ('p2', 'p2'): 'EQ',
        ('p1', 'p2'): 'PO', ('p2', 'p1'): 'PO',
    }
    m = Mosaic(name='m0', positions=('p1', 'p2'),
               tau={'p1': tau_root, 'p2': tau_a}, L=L)
    cert = Certificate(
        S=('s0',),
        s0='s0',
        lam={'s0': tau_root},
        par={},
        ports={},
        eq_ports=set(),
        mosaics=[m],
        source_pos={'s0': [('m0', 'p1')]},
        dr_po_wit={('s0', e_po_a): ('m0', 'p2')},
        name='PO witness: exists PO.A discharged by 2-position mosaic (V6 SAT)',
    )
    return cert, C


def cert_dr_witness_undeclared() -> tuple:
    """exists DR.A with mosaics present but no witness entry.  Should FAIL V6.

    Mosaic itself is V2-clean (same construction as cert_dr_witness_sat);
    the failure mode we exercise here is purely the missing dr_po_wit entry.
    """
    a = Atom('A')
    e_dr_a = E('DR', a)
    C = e_dr_a
    cl = closure(C)
    tau_root = saturate_for(cl, [C])
    tau_a = saturate_for(cl, [a, e_dr_a])
    L = {
        ('p1', 'p1'): 'EQ', ('p2', 'p2'): 'EQ',
        ('p1', 'p2'): 'DR', ('p2', 'p1'): 'DR',
    }
    m = Mosaic(name='m0', positions=('p1', 'p2'),
               tau={'p1': tau_root, 'p2': tau_a}, L=L)
    cert = Certificate(
        S=('s0',),
        s0='s0',
        lam={'s0': tau_root},
        par={},
        ports={},
        eq_ports=set(),
        mosaics=[m],
        source_pos={'s0': [('m0', 'p1')]},
        dr_po_wit={},  # no witness declared
        name='DR witness undeclared: exists DR.A has no mosaic entry (V6 FAIL)',
    )
    return cert, C


def cert_dr_witness_wrong_relation() -> tuple:
    """exists DR.A witnessed by a PO-labeled mosaic edge.  Should FAIL V6.

    Mosaic is V2-clean (PO edges are RCC5-legal); V6 catches the relation
    mismatch between the requested role (DR) and the actual L(p1,p2)=PO.
    """
    a = Atom('A')
    e_dr_a = E('DR', a)
    C = e_dr_a
    cl = closure(C)
    tau_root = saturate_for(cl, [C])
    tau_a = saturate_for(cl, [a, e_dr_a])
    L = {
        ('p1', 'p1'): 'EQ', ('p2', 'p2'): 'EQ',
        ('p1', 'p2'): 'PO', ('p2', 'p1'): 'PO',
    }
    m = Mosaic(name='m0', positions=('p1', 'p2'),
               tau={'p1': tau_root, 'p2': tau_a}, L=L)
    cert = Certificate(
        S=('s0',),
        s0='s0',
        lam={'s0': tau_root},
        par={},
        ports={},
        eq_ports=set(),
        mosaics=[m],
        source_pos={'s0': [('m0', 'p1')]},
        dr_po_wit={('s0', e_dr_a): ('m0', 'p2')},
        name='DR witness wrong-relation: L(p1,p2)=PO not DR (V6 FAIL)',
    )
    return cert, C


def cert_dr_universal_violated() -> tuple:
    """forall DR.A in lam(s), but a DR-neighbor in the mosaic lacks A.

    Should FAIL V7.  The state's source has a mosaic neighbor at DR
    whose type does not contain A.
    """
    a = Atom('A')
    not_a = Neg(a)
    a_dr_a = A('DR', a)
    e_dr_top = E('DR', TOP())
    # forall DR.A & exists DR.top -- but the mosaic witness places a
    # DR-neighbor with ~A, violating V7.
    C = And(a_dr_a, e_dr_top)
    cl = closure(C)
    tau_root = saturate_for(cl, [C])
    tau_bad = saturate_for(cl, [not_a, a_dr_a])  # ~A neighbor, still carries the universal
    L = {
        ('p1', 'p1'): 'EQ', ('p2', 'p2'): 'EQ',
        ('p1', 'p2'): 'DR', ('p2', 'p1'): 'DR',
    }
    m = Mosaic(name='m0', positions=('p1', 'p2'),
               tau={'p1': tau_root, 'p2': tau_bad}, L=L)
    cert = Certificate(
        S=('s0',),
        s0='s0',
        lam={'s0': tau_root},
        par={},
        ports={},
        eq_ports=set(),
        mosaics=[m],
        source_pos={'s0': [('m0', 'p1')]},
        dr_po_wit={('s0', e_dr_top): ('m0', 'p2')},
        name='DR universal violated: forall DR.A but neighbor has ~A (V2/V7 FAIL)',
    )
    return cert, C


def cert_mosaic_illegal_composition() -> tuple:
    """Mosaic with PP-PP-DR triangle.  Should FAIL V2 (composition).

    PP o PP = {PP}, so L(p1,p3)=DR is not allowed.  The cert otherwise
    discharges exists PP.A vertically (via par) but the mosaic is intrinsically
    illegal.
    """
    a = Atom('A')
    e_pp_a = E('PP', a)
    C = e_pp_a
    cl = closure(C)
    tau_root = saturate_for(cl, [C])
    tau_a = saturate_for(cl, [a])
    L = {
        ('p1', 'p1'): 'EQ', ('p2', 'p2'): 'EQ', ('p3', 'p3'): 'EQ',
        ('p1', 'p2'): 'PP', ('p2', 'p1'): 'PPI',
        ('p2', 'p3'): 'PP', ('p3', 'p2'): 'PPI',
        ('p1', 'p3'): 'DR', ('p3', 'p1'): 'DR',  # illegal: PP o PP = {PP}
    }
    m = Mosaic(name='m_bad', positions=('p1', 'p2', 'p3'),
               tau={'p1': tau_root, 'p2': tau_a, 'p3': tau_a}, L=L)
    # Vertical par discharges exists PP.A via s1.
    cert = Certificate(
        S=('s0', 's1'),
        s0='s0',
        lam={'s0': tau_root, 's1': tau_a},
        par={'s0': 's1'},
        ports={},
        eq_ports=set(),
        mosaics=[m],
        source_pos={'s0': [('m_bad', 'p1')]},
        dr_po_wit={},
        name='mosaic illegal composition: PP-PP-DR triangle (V2 FAIL)',
    )
    return cert, C


def cert_dr_existential_no_mosaics() -> tuple:
    """exists DR.A with no mosaics declared at all.  Should FAIL V6.

    GPT-5.5 May-2026 regression test: prior to the fix, V6 returned
    vacuously on cert.mosaics==[], so this cert was incorrectly accepted.
    With the fix, V6 scans all states/existentials unconditionally and
    rejects the missing witness.
    """
    a = Atom('A')
    e_dr_a = E('DR', a)
    C = e_dr_a
    cl = closure(C)
    tau_root = saturate_for(cl, [C])
    cert = Certificate(
        S=('s0',),
        s0='s0',
        lam={'s0': tau_root},
        par={},
        ports={},
        eq_ports=set(),
        mosaics=[],
        source_pos={},
        dr_po_wit={},
        name='exists DR.A with no mosaics: V6 must reject (regression)',
    )
    return cert, C


def cert_po_existential_no_mosaics() -> tuple:
    """exists PO.A with no mosaics declared at all.  Should FAIL V6.

    Symmetric to cert_dr_existential_no_mosaics; covers the PO leg of the
    V6 no-mosaics loophole flagged by GPT-5.5.
    """
    a = Atom('A')
    e_po_a = E('PO', a)
    C = e_po_a
    cl = closure(C)
    tau_root = saturate_for(cl, [C])
    cert = Certificate(
        S=('s0',),
        s0='s0',
        lam={'s0': tau_root},
        par={},
        ports={},
        eq_ports=set(),
        mosaics=[],
        source_pos={},
        dr_po_wit={},
        name='exists PO.A with no mosaics: V6 must reject (regression)',
    )
    return cert, C


def cert_WP5_pure_request_unfulfilled() -> tuple:
    """Pure request-closure negative test (GPT-5.5 verification.zip review section 3.5).

    One-state self-loop carrying ~A & exists PP.A, with no forall PP.~A
    (so V1 is locally satisfied -- no NNF-complement clash inside the
    Hintikka type).  Should FAIL V4: reach_PP(s0) = {s0} (self-loop),
    but lam(s0) carries ~A, so the existential is never discharged.

    Distinct from cert_WP5_cycle_unfulfilled_request_unsat which combines
    ~A & exists PP.A & forall PP.~A and is rejected at V1 (Hintikka clash
    between exists PP.A and forall PP.~A as NNF complements), short-
    circuiting before V4 is genuinely exercised.
    """
    a = Atom('A')
    not_a = Neg(a)
    e_pp_a = E('PP', a)
    C = And(not_a, e_pp_a)
    cl = closure(C)
    tau = saturate_for(cl, [C])
    cert = Certificate(
        S=('s0',),
        s0='s0',
        lam={'s0': tau},
        par={'s0': 's0'},
        ports={},
        eq_ports=set(),
        name='WP5 pure request-closure: self-loop carries ~A & exists PP.A (V4 fails, V1 clean)',
    )
    return cert, C


def cert_C_pp_simple_sat() -> tuple:
    """forall PP.A & exists PP.A.  SAT via one parent state with A and forall PP.A.

    The parent's lam must also contain forall PP.A so the safety condition is
    closed (in case the parent itself has further PP ancestors via par).  In
    this 2-state certificate, par(s0) = s1 and s1 has no parent set, so
    reach_PP(s1) = {} and V3 is vacuously true at s1.
    """
    a = Atom('A')
    a_pp_a = A('PP', a)
    e_pp_a = E('PP', a)
    C = And(a_pp_a, e_pp_a)
    cl = closure(C)
    tau_root = saturate_for(cl, [C])
    tau_parent = saturate_for(cl, [a, a_pp_a])
    cert = Certificate(
        S=('s0', 's1'),
        s0='s0',
        lam={'s0': tau_root, 's1': tau_parent},
        par={'s0': 's1'},
        ports={},
        eq_ports=set(),
        name='SAT: forall PP.A & exists PP.A',
    )
    return cert, C


# -----------------------------------------------------------------------------
# Occurrence-level vs profile-name distinction tests.
#
# Per GPT-5.5 verification.zip review section 4.5: the script's encoding
# uses *profiles* (string names) as certificate states.  Different profile
# names always represent distinct semantic occurrences; identical profile
# names across cycle laps represent FRESH occurrences (the t == s skip in
# V9.Eb encodes this).  The only way to declare two occurrences as eq^Q-
# equal is via explicit eq_ports edges.
#
# The certs below pin down four boundary behaviors of this convention:
#   - multi-state cycles with profile reuse but no eq_ports stay SAT
#     (each lap is fresh; transitive PP-reachability does not generate eq)
#   - cycles where eq_ports explicitly identify reach_PP-related states
#     are rejected by V9.Eb
#   - PP chains with identical Hintikka types across distinct profiles
#     are SAT (profile equality does not imply semantic EQ)
#   - eq_ports across states with distinct lambdas are rejected by V9.Ea
# -----------------------------------------------------------------------------

def cert_two_state_pp_cycle_no_eq() -> tuple:
    """Multi-state PP cycle: par[s0]=s1, par[s1]=s0.  Both states share
    the same Hintikka type.  No eq_ports declared.

    Semantically the cycle unfolds to s0_1 PP s1_1 PP s0_2 PP s1_2 PP ...
    where every lap produces fresh occurrences.  Profile reuse alone must
    NOT generate semantic eq^Q -- this is the multi-state analogue of
    cert_C_up's one-state self-loop.  Should be VALID.
    """
    e_pp_top = E('PP', TOP())
    a_pp_e_pp_top = A('PP', e_pp_top)
    C_up = And(e_pp_top, a_pp_e_pp_top)
    cl = closure(C_up)
    tau = saturate_for(cl, [C_up])
    cert = Certificate(
        S=('s0', 's1'),
        s0='s0',
        lam={'s0': tau, 's1': tau},
        par={'s0': 's1', 's1': 's0'},
        ports={},
        eq_ports=set(),
        name='Two-state PP cycle, no eq_ports (occurrence freshness)',
    )
    return cert, C_up


def cert_two_state_pp_cycle_with_cross_eq() -> tuple:
    """Same two-state PP cycle, but eq_ports declares (s0,p) eq^Q (s1,p).

    s0 reach_PP s1 (one cycle step) and s1 reach_PP s0 (another step).
    V9.Eb forbids declaring eq^Q across reach_PP-related occurrences:
    distinct laps cannot be semantic mates.  Should FAIL V9.Eb.
    """
    e_pp_top = E('PP', TOP())
    a_pp_e_pp_top = A('PP', e_pp_top)
    C_up = And(e_pp_top, a_pp_e_pp_top)
    cl = closure(C_up)
    tau = saturate_for(cl, [C_up])
    cert = Certificate(
        S=('s0', 's1'),
        s0='s0',
        lam={'s0': tau, 's1': tau},
        par={'s0': 's1', 's1': 's0'},
        ports={
            's0': frozenset({('p0', 'g')}),
            's1': frozenset({('p1', 'g')}),
        },
        eq_ports={(('s0', 'p0'), ('s1', 'p1'))},
        name='Two-state PP cycle with eq across cycle (should fail V9.Eb)',
    )
    return cert, C_up


def cert_pp_chain_same_lambda_no_eq() -> tuple:
    """PP chain s0 -> s1 -> s2 (s2 self-loop) with identical lambdas
    across all three states; no eq_ports.

    Three distinct profile names carrying the SAME Hintikka type must
    stay SAT under the occurrence-level convention: profile equality
    (same string content of lambda) never implies semantic eq^Q.
    """
    e_pp_top = E('PP', TOP())
    a_pp_e_pp_top = A('PP', e_pp_top)
    C_up = And(e_pp_top, a_pp_e_pp_top)
    cl = closure(C_up)
    tau = saturate_for(cl, [C_up])
    cert = Certificate(
        S=('s0', 's1', 's2'),
        s0='s0',
        lam={'s0': tau, 's1': tau, 's2': tau},
        par={'s0': 's1', 's1': 's2', 's2': 's2'},
        ports={},
        eq_ports=set(),
        name='PP chain (3 states) sharing lambda, no eq_ports (SAT)',
    )
    return cert, C_up


def cert_eq_across_distinct_lambdas() -> tuple:
    """eq_ports declares s0 eq^Q s1 but lambda(s0) != lambda(s1).

    C_0 = A.  s0 carries A; s1 carries ~A.  Both Hintikka types are
    individually legal, but V9.Ea (typed-EQ congruence) forbids declaring
    eq across distinct lambdas: an eq^Q-class must share Hintikka type.

    Should FAIL V9.Ea before any vertical-fragment condition fires
    (there are no PP/PPI roles in C_0).
    """
    a = Atom('A')
    not_a = Neg(a)
    C = a
    cl = closure(C)
    tau_a = saturate_for(cl, [a])
    tau_not_a = saturate_for(cl, [not_a])
    cert = Certificate(
        S=('s0', 's1'),
        s0='s0',
        lam={'s0': tau_a, 's1': tau_not_a},
        par={},
        ports={
            's0': frozenset({('p0', 'g')}),
            's1': frozenset({('p1', 'g')}),
        },
        eq_ports={(('s0', 'p0'), ('s1', 'p1'))},
        name='eq across distinct lambdas (should fail V9.Ea)',
    )
    return cert, C


# -----------------------------------------------------------------------------
# Driver.
# -----------------------------------------------------------------------------

# Each test: (builder, expected_valid)
CORPUS = [
    (cert_C_up, True),
    (cert_C_up_with_eq_port, True),
    (cert_C_up_with_bad_eq, False),
    (cert_C_AB, True),
    (cert_C_AB_wrong_singleparent, False),
    (cert_C_AB_inc, True),
    (cert_C_AB_inc_singleparent, False),
    (cert_C_AB_inc_singlechain, False),
    (cert_C_clash_pp_universal, False),
    (cert_C_pp_transitive_unsat, False),
    (cert_WP5_cycle_carries_existential_sat, True),
    (cert_WP5_cycle_unfulfilled_request_unsat, False),
    (cert_WP5_pure_request_unfulfilled, False),
    (cert_C_pp_simple_sat, True),
    # DR/PO mosaic tests (V2/V6/V7/V8).
    (cert_dr_witness_sat, True),
    (cert_po_witness_sat, True),
    (cert_dr_witness_undeclared, False),
    (cert_dr_witness_wrong_relation, False),
    (cert_dr_universal_violated, False),
    (cert_mosaic_illegal_composition, False),
    (cert_dr_existential_no_mosaics, False),
    (cert_po_existential_no_mosaics, False),
    # Occurrence-level distinction (V9.Ea/Eb, per review section 4.5).
    (cert_two_state_pp_cycle_no_eq, True),
    (cert_two_state_pp_cycle_with_cross_eq, False),
    (cert_pp_chain_same_lambda_no_eq, True),
    (cert_eq_across_distinct_lambdas, False),
]


def main() -> int:
    print('=' * 79)
    print('WP2 (vertical fragment): bounded certificate validity checker')
    print('per repaired_split_forest_no_automata_proof.tex Def 4.1/4.5')
    print('=' * 79)
    print()
    print('Conditions checked: V1, V2, V3, V4, V5, V6, V7, V8 (basic),')
    print('                    V9 (Ea, Eb), V10.')
    print('Full V8 triple-support closure: see mosaic_closure_search.py.')
    print()
    overall_ok = True
    summaries = []
    for i, (builder, expected) in enumerate(CORPUS, 1):
        cert, c0 = builder()
        rep = check_certificate(cert, c0)
        is_valid = rep.is_valid()
        outcome = 'PASS' if is_valid == expected else 'FAIL'
        if outcome == 'FAIL':
            overall_ok = False
        print(f'[{i}] {cert.name}')
        print(f'    C0 = {c0}')
        print(f'    states = {sorted(cert.S)}')
        if is_valid:
            print('    verdict: VALID')
        else:
            print('    verdict: INVALID')
            for code, msg in rep.failures:
                print(f'      - {code}: {msg}')
        print(f'    expected: {"VALID" if expected else "INVALID"}     outcome: {outcome}')
        print()
        summaries.append((cert.name, expected, is_valid, outcome))

    print('-' * 79)
    print('Summary')
    print('-' * 79)
    for name, exp, got, outcome in summaries:
        flag = '*' if outcome == 'FAIL' else ' '
        print(f' {flag} expected={"V" if exp else "I"}  got={"V" if got else "I"}  {name}')
    print()
    if overall_ok:
        print('VERDICT: PASS.  All certificates match expected validity.')
        return 0
    print('VERDICT: FAIL.  At least one certificate disagrees with expected.')
    return 1


if __name__ == '__main__':
    sys.exit(main())
