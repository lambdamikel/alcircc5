#!/usr/bin/env python3
"""
WP24 -- finite RCC5 checks used by the round-14 G2/G3 review.

The script checks the small composition-table claims needed for the repaired
Coverage walk and extraction-width arguments:

  W1. A nonempty word over {PP,PPI} composes to a vertical-only relation set
      only when it is uniformly oriented.  Mixed vertical walks always admit a
      horizontal result (PO, and sometimes DR), so they cannot be the untracked
      case handled solely by D3.
  W2. A horizontal row prefix/suffix survives any vertical segment: composing
      a horizontal atom with a vertical word, on either side, always leaves at
      least one horizontal atom available.  Hence a walk that has already made
      a horizontal row manifestation cannot later be forced into an undeclared
      vertical-only value; it can be row-covered or deliberately verticalized.
  W3. The two vertical transitivity cells used by D3 are singleton cells.
  W4. The finite G_m approximants of the prompt's C0' stress family are SAT
      according to the supplied cover-tree oracle.  This is not a proof of the
      recursive schematic case; it is a regression check that the repaired
      discipline does not reject the finite forced-tail patterns.
"""
import itertools
import os
import sys

BASE = ('EQ', 'PP', 'PPI', 'PO', 'DR')
HOR = {'DR', 'PO'}
VERT = {'PP', 'PPI'}
CONV = {'EQ': 'EQ', 'PP': 'PPI', 'PPI': 'PP', 'PO': 'PO', 'DR': 'DR'}


def derive_comp(n=5):
    universe = range(n)
    subsets = []
    for k in range(1, n + 1):
        subsets += [frozenset(c) for c in itertools.combinations(universe, k)]

    def rel(a, b):
        if a == b:
            return 'EQ'
        if not (a & b):
            return 'DR'
        if a < b:
            return 'PP'
        if b < a:
            return 'PPI'
        return 'PO'

    t = {(r, s): set() for r in BASE for s in BASE}
    for a in subsets:
        for b in subsets:
            r = rel(a, b)
            for c in subsets:
                t[(r, rel(b, c))].add(rel(a, c))
    return {k: frozenset(v) for k, v in t.items()}

COMP = derive_comp()


def compose_sets(left, right):
    out = set()
    for r in left:
        for s in right:
            out |= COMP[(r, s)]
    return frozenset(out)


def compose_word(word):
    cur = frozenset([word[0]])
    for a in word[1:]:
        cur = compose_sets(cur, frozenset([a]))
    return cur


def check_w1(max_len=8):
    bad = []
    examples = []
    for L in range(1, max_len + 1):
        for w in itertools.product(('PP', 'PPI'), repeat=L):
            val = compose_word(w)
            uniform = all(a == w[0] for a in w)
            vertical_only = bool(val) and set(val) <= VERT
            if vertical_only and not uniform:
                bad.append((w, val))
            if not uniform and (set(val) & HOR) and len(examples) < 5:
                examples.append((w, val))
    return bad, examples


def check_w2(max_len=8):
    bad = []
    for L in range(1, max_len + 1):
        for vw in itertools.product(('PP', 'PPI'), repeat=L):
            vval = compose_word(vw)
            for h in HOR:
                if not (compose_sets(frozenset([h]), vval) & HOR):
                    bad.append(((h,) + vw, 'left-prefix', compose_sets(frozenset([h]), vval)))
                if not (compose_sets(vval, frozenset([h])) & HOR):
                    bad.append((vw + (h,), 'right-suffix', compose_sets(vval, frozenset([h]))))
    return bad


def _add_support_path():
    here = os.path.dirname(__file__)
    candidates = [
        os.path.join(here, 'support'),
        os.path.join(here, '..', 'support'),
        os.path.join(here, '..', 'g2g3', 'gpt_task_g2_g3', 'support'),
        '/mnt/data/g2g3/gpt_task_g2_g3/support',
    ]
    for cand in candidates:
        if os.path.exists(os.path.join(cand, 'cover_tree_tableau.py')):
            if cand not in sys.path:
                sys.path.insert(0, cand)
            return cand
    raise RuntimeError('support directory not found; set up support/ next to this script')


def make_prompt_family(depth):
    # Finite approximants of C0-prime = ExPP.G n ExPO.~X, G = AllPO.X n ExPP.G.
    _add_support_path()
    from alcircc5_reasoner import AtomicConcept, NegAtomicConcept, Top, And, Exists, ForAll, PP, PO
    X = AtomicConcept('X')
    notX = NegAtomicConcept('X')
    G = Top()
    for _ in range(depth):
        G = And(ForAll(PO, X), Exists(PP, G))
    return And(Exists(PP, G), Exists(PO, notX))


def check_w4(max_depth=None):
    if max_depth is None:
        max_depth = int(os.environ.get('WP24_MAX_DEPTH', '4'))
    _add_support_path()
    from cover_tree_tableau import check_satisfiability
    out = []
    for d in range(1, max_depth + 1):
        C = make_prompt_family(d)
        sat, info = check_satisfiability(C, verbose=False)
        out.append((d, sat, info.get('closure_size'), info.get('time')))
    return out


def main():
    print('WP24 -- vertical walk facts retained by round-14')
    print('=' * 72)
    bad1, ex1 = check_w1()
    print('W1 mixed vertical walks have a horizontal composition option:', 'PASS' if not bad1 else 'FAIL')
    if ex1:
        print('   sample mixed words:', '; '.join('%s -> %s' % (''.join(w), sorted(v)) for w, v in ex1[:3]))
    bad2 = check_w2()
    print('W2 horizontal prefix/suffix survives vertical segments:', 'PASS' if not bad2 else 'FAIL')
    print('W3 singleton vertical transitivity cells:', 'PASS' if COMP[('PP','PP')] == frozenset(['PP']) and COMP[('PPI','PPI')] == frozenset(['PPI']) else 'FAIL')
    w4 = check_w4()
    ok4 = all(sat for _, sat, _, _ in w4)
    print('W4 finite C0-prime approximants SAT by cover-tree oracle:', 'PASS' if ok4 else 'FAIL')
    for d, sat, cl, tm in w4:
        print(f'   depth {d}: {"SAT" if sat else "UNSAT"}, closure={cl}, time={tm:.4f}s')
    print('=' * 72)
    overall = (not bad1) and (not bad2) and ok4
    print('WP24 OVERALL:', 'PASS' if overall else 'ATTENTION')
    return 0 if overall else 1

if __name__ == '__main__':
    raise SystemExit(main())
