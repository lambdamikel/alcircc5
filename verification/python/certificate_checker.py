"""
WP2 (initial vertical-fragment version) from
gpt5.5_round2/verification_recommendations_for_claude.tex.

Implements the validity-condition checker for finite generated split-forest
certificates per Definition 4.1 (def:certificate) and Definition 4.5 (def:valid)
of papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.tex.

Scope of this initial version
-----------------------------
This script covers the *vertical fragment*: certificates whose witness
mechanisms use only PP/PPI vertical reachability (no DR/PO mosaic positions).
That means we check (V1) type legality, (V3) vertical safety, (V4)/(V5)
equality-aware vertical existential/universal discharge, (V9) typed-equality
congruence on ports, and (V10) exact summaries.  (V2), (V6), (V7), (V8) involve
DR/PO mosaics and are deferred to WP6/full version.

This subset is sufficient to exercise the three load-bearing fixes from the
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

INV = {'EQ': 'EQ', 'DR': 'DR', 'PO': 'PO', 'PP': 'PPI', 'PPI': 'PP'}


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
class Certificate:
    S: tuple
    s0: str
    lam: dict
    par: dict = field(default_factory=dict)
    ports: dict = field(default_factory=dict)
    eq_ports: set = field(default_factory=set)
    name: str = '?'

    def parents_of(self, s: str):
        out = []
        if s in self.par:
            out.append(self.par[s])
        return out


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
    check_V3_vertical_safety(cert, rep)
    check_V4_existential_discharge(cert, rep)
    check_V5_universal_via_mate(cert, rep)
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
# Driver.
# -----------------------------------------------------------------------------

# Each test: (builder, expected_valid)
CORPUS = [
    (cert_C_up, True),
    (cert_C_up_with_eq_port, True),
    (cert_C_up_with_bad_eq, False),
    (cert_C_AB, True),
    (cert_C_AB_wrong_singleparent, False),
    (cert_C_clash_pp_universal, False),
    (cert_C_pp_transitive_unsat, False),
    (cert_WP5_cycle_carries_existential_sat, True),
    (cert_WP5_cycle_unfulfilled_request_unsat, False),
    (cert_C_pp_simple_sat, True),
]


def main() -> int:
    print('=' * 79)
    print('WP2 (vertical fragment): bounded certificate validity checker')
    print('per repaired_split_forest_no_automata_proof.tex Def 4.1/4.5')
    print('=' * 79)
    print()
    print('Conditions checked: V1, V3, V4, V5, V9 (Ea, Eb), V10.')
    print('Out of scope (this version): V2, V6, V7, V8 (DR/PO mosaics).')
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
