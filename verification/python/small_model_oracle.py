"""
WP3 from gpt5.5_round2/verification_recommendations_for_claude.tex.

Brute-force finite abstract RCC5/Kripke model search.  For domain sizes
n in {2, 3, 4} we enumerate all complete RCC5 labelings (a relation
rho : dom x dom -> {EQ, DR, PO, PP, PPI}) that satisfy:

  (J1) rho(x, x) = EQ for all x
  (J2) rho(y, x) = INV[rho(x, y)] for all x != y
  (J3) for all triples (x, y, z),
         rho(x, z) in comp(rho(x, y), rho(y, z))

We then enumerate atomic assignments and check concept satisfaction at the
declared root.  The oracle reports SAT (with a concrete model) or
"no finite model found up to size N" -- which is *not* the same as UNSAT for
concepts whose only models are infinite (e.g. exists PP.top).

This is the WP3 cross-check for the WP2 certificate checker.  Limitations:

  * C_up = exists PP.top & forall PP.exists PP.top forces an infinite
    ascending PP-chain, so the oracle will not produce a model.  WP2
    correctly accepts the certificate (a parent self-loop on the rank-d
    quotient unfolds to fresh occurrences).  WP3 confirms "no finite model
    up to size 4" -- consistent with SAT in an infinite frame.

  * Genuine UNSAT (e.g. exists PP.A & forall PP.~A) yields "no model up
    to size 4" *and* WP2 rejects the certificate -- mutually corroborating.

Run:  python3 verification/python/small_model_oracle.py
"""

from __future__ import annotations

import sys
from itertools import product
from typing import Optional

sys.path.insert(0, __file__.rsplit('/', 1)[0])

from certificate_checker import (  # noqa: E402
    Concept, Atom, Neg, And, Or, E, A, TOP, BOT, closure,
    INV, BASE_RELS,
)


# RCC5 composition table (brute-force verified by WP1).
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


def all_atoms_in(c: Concept) -> set:
    out = set()

    def visit(x: Concept) -> None:
        if x.kind == 'atom':
            out.add(x.name)
        elif x.kind == 'neg':
            visit(x.sub)
        elif x.kind in ('and', 'or'):
            for s in x.subs:
                visit(s)
        elif x.kind in ('exists', 'forall'):
            visit(x.sub)

    visit(c)
    return out


# -----------------------------------------------------------------------------
# Concept evaluation.
# -----------------------------------------------------------------------------

def eval_concept(c: Concept, x: int, rho: dict, val: dict) -> bool:
    """val: {atom_name: frozenset of domain elements satisfying it}."""
    k = c.kind
    if k == 'top':
        return True
    if k == 'bot':
        return False
    if k == 'atom':
        return x in val[c.name]
    if k == 'neg':
        return not eval_concept(c.sub, x, rho, val)
    if k == 'and':
        return all(eval_concept(s, x, rho, val) for s in c.subs)
    if k == 'or':
        return any(eval_concept(s, x, rho, val) for s in c.subs)
    if k == 'exists':
        R = c.role
        dom = val.get('__dom__')
        if dom is None:
            raise RuntimeError('val must include __dom__')
        return any(rho[(x, y)] == R and eval_concept(c.sub, y, rho, val)
                   for y in dom)
    if k == 'forall':
        R = c.role
        dom = val['__dom__']
        return all((rho[(x, y)] != R) or eval_concept(c.sub, y, rho, val)
                   for y in dom)
    raise ValueError(f'unknown concept kind {k}')


# -----------------------------------------------------------------------------
# Brute-force enumeration of RCC5 labelings on a fixed domain.
# -----------------------------------------------------------------------------

def enumerate_labelings(n: int):
    """Yield all complete RCC5 labelings rho: pairs -> BASE_RELS for domain {0..n-1}.

    Returns ((x,y)->rel) dicts satisfying (J1), (J2), (J3).
    Constructed by choosing labels for ordered pairs (x, y) with x < y; the
    reverse labels are derived by INV; the diagonal is EQ.  Composition is
    enforced as a pruning step.
    """
    dom = list(range(n))
    pairs = [(x, y) for x in dom for y in dom if x < y]
    # Off-diagonal choices: 4 non-EQ relations between distinct elements.
    OFF = ('DR', 'PO', 'PP', 'PPI')
    for choice in product(OFF, repeat=len(pairs)):
        rho = {}
        for x in dom:
            rho[(x, x)] = 'EQ'
        for (x, y), r in zip(pairs, choice):
            rho[(x, y)] = r
            rho[(y, x)] = INV[r]
        # Check composition on all triples.
        ok = True
        for x in dom:
            if not ok:
                break
            for y in dom:
                if not ok:
                    break
                for z in dom:
                    rxz = rho[(x, z)]
                    rxy = rho[(x, y)]
                    ryz = rho[(y, z)]
                    if rxz not in COMP[(rxy, ryz)]:
                        ok = False
                        break
        if ok:
            yield rho


def enumerate_valuations(atoms: list, n: int):
    """Yield all subsets-of-domain assignments for each atom."""
    dom = list(range(n))
    subsets = []
    for mask in range(1 << n):
        subsets.append(frozenset(i for i in dom if (mask >> i) & 1))
    for combo in product(subsets, repeat=len(atoms)):
        val = {a: combo[i] for i, a in enumerate(atoms)}
        val['__dom__'] = dom
        yield val


def find_finite_model(c0: Concept, max_n: int = 4) -> Optional[tuple]:
    atoms = sorted(all_atoms_in(c0))
    for n in range(1, max_n + 1):
        for rho in enumerate_labelings(n):
            for val in enumerate_valuations(atoms, n):
                for root in range(n):
                    if eval_concept(c0, root, rho, val):
                        return (n, rho, val, root)
    return None


# -----------------------------------------------------------------------------
# Test corpus -- a subset of the WP2 tests whose answer can be cross-checked.
# -----------------------------------------------------------------------------

def get_corpus():
    a, b, cc = Atom('A'), Atom('B'), Atom('C')

    cases = []

    # WP2 SAT (finite-model-friendly).
    cases.append(('forall PP.A & exists PP.A',
                  And(A('PP', a), E('PP', a)),
                  True))

    cases.append(('A & B & exists PP.A & exists PP.B '
                  '& forall PP.(~A | ~B) & forall PP.(~B | ~A)  [C_AB]',
                  And(a, b, E('PP', a), E('PP', b),
                      A('PP', Or(Neg(a), Neg(b))),
                      A('PP', Or(Neg(b), Neg(a)))),
                  True))

    # C_AB^inc: strengthened incomparability-forcing concept
    # (GPT-5.5 verification.zip review section 3.3).  Forces any A-superpart
    # and any B-superpart to be PP/PPI-incomparable, so single chains are
    # ruled out.  Expected SAT in a 3-element model where the root has two
    # PP-successors related by PO (or DR), one carrying A and one B.
    cases.append((
        'exists PP.A & exists PP.B & forall PP.('
        '(~A | (~B & forall PP.~B & forall PPI.~B)) & '
        '(~B | (~A & forall PP.~A & forall PPI.~A)))  [C_AB^inc]',
        And(E('PP', a), E('PP', b),
            A('PP', And(
                Or(Neg(a), And(Neg(b), A('PP', Neg(b)), A('PPI', Neg(b)))),
                Or(Neg(b), And(Neg(a), A('PP', Neg(a)), A('PPI', Neg(a)))),
            ))),
        True))

    # UNSAT cases.
    cases.append(('exists PP.A & forall PP.~A',
                  And(E('PP', a), A('PP', Neg(a))),
                  False))

    cases.append(('forall PP.~C & exists PP.exists PP.C  [PP-transitive UNSAT]',
                  And(A('PP', Neg(cc)), E('PP', E('PP', cc))),
                  False))

    # Infinite-model SAT: WP2 says VALID, but WP3 finds no finite model.
    cases.append(('exists PP.top & forall PP.exists PP.top  [C_up, infinite SAT]',
                  And(E('PP', TOP()), A('PP', E('PP', TOP()))),
                  None))  # None = "infinite-model SAT; WP3 will not find a model"

    return cases


def fmt_rho(rho: dict, n: int) -> str:
    rows = []
    for x in range(n):
        row = []
        for y in range(n):
            row.append(rho[(x, y)].rjust(3))
        rows.append('  ' + ' '.join(row))
    return '\n'.join(rows)


def fmt_val(val: dict) -> str:
    parts = []
    for k, v in val.items():
        if k == '__dom__':
            continue
        parts.append(f'{k}={sorted(v)}')
    return ' '.join(parts) if parts else '(no atoms)'


def main() -> int:
    print('=' * 79)
    print('WP3: small-model oracle')
    print('=' * 79)
    print()
    print('Domains searched: n = 1, 2, 3, 4.  For each concept C0 we either:')
    print('  - find a model and report SAT, or')
    print('  - exhaust the search and report "no finite model up to size 4".')
    print()
    print('Cross-check with WP2 certificate checker:')
    print('  - WP2 VALID + WP3 SAT             -> consistent (finite model)')
    print('  - WP2 VALID + WP3 no model        -> consistent IF C0 needs infinite')
    print('  - WP2 INVALID + WP3 no model      -> consistent (UNSAT)')
    print('  - WP2 INVALID + WP3 SAT           -> oracle conflict (BUG)')
    print()
    cases = get_corpus()
    all_ok = True
    for label, c0, expect in cases:
        print(f'>>> {label}')
        print(f'    C0 = {c0}')
        result = find_finite_model(c0, max_n=4)
        if result is None:
            outcome = 'no finite model up to n=4'
            if expect is True:
                verdict = 'FAIL (expected SAT)'
                all_ok = False
            elif expect is False:
                verdict = 'PASS (UNSAT)'
            else:
                verdict = 'PASS (expected infinite-model-only SAT)'
            print(f'    {outcome}')
            print(f'    expected={expect}    {verdict}')
        else:
            n, rho, val, root = result
            outcome = f'SAT at n={n} root={root}'
            if expect is False:
                verdict = 'FAIL (expected UNSAT)'
                all_ok = False
            elif expect is True:
                verdict = 'PASS (SAT)'
            else:
                verdict = 'FAIL (expected no finite model)'
                all_ok = False
            print(f'    {outcome}')
            print(f'    valuation: {fmt_val(val)}')
            print('    rho =')
            print(fmt_rho(rho, n))
            print(f'    expected={expect}    {verdict}')
        print()

    if all_ok:
        print('VERDICT: PASS.  WP3 oracle agrees with WP2 on all corpus entries.')
        return 0
    print('VERDICT: FAIL.  See * above.')
    return 1


if __name__ == '__main__':
    sys.exit(main())
