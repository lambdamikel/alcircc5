"""
WP1 from gpt5.5_round2/verification_recommendations_for_claude.tex.

Computes the RCC5 composition table by exhaustive enumeration over nonempty
subsets of a finite universe, then compares it against:

  (a) the table in GPT-5.5's repaired proof
      (papers/gpt5.5_round2/repaired_split_forest_no_automata_proof.tex,
       lines 99-114);
  (b) the COMP table in the quasimodel reasoner
      (src/alcircc5_reasoner.py, lines 41-58).

Convention. For nonempty subsets A, B of a finite universe U:
    A EQ B  <=>  A == B
    A PP B  <=>  A is a proper subset of B
    A PPI B <=>  B is a proper subset of A
    A DR B  <=>  A intersect B = empty
    A PO B  <=>  A intersect B != empty and A not subset of B and B not subset of A

For each (R, S) in Base x Base, the computed entry is

    comp(R, S) = { T in Base : exists nonempty A, B, C in 2^U
                               with A R B, B S C, A T C }.

Output. A side-by-side report listing for each (R, S):
  - the computed set,
  - GPT-5.5's claimed set,
  - the reasoner's set (or n/a when EQ is involved, since the reasoner
    excludes EQ as a non-trivial edge label),
  - PASS / FAIL.

Run:  python3 verification/python/rcc5_composition_check.py
"""

from itertools import combinations
import sys

BASE = ('EQ', 'DR', 'PO', 'PP', 'PPI')


def relation(A: frozenset, B: frozenset) -> str:
    if A == B:
        return 'EQ'
    if not (A & B):
        return 'DR'
    if A < B:
        return 'PP'
    if B < A:
        return 'PPI'
    return 'PO'


def all_nonempty_subsets(n: int):
    elements = tuple(range(n))
    out = []
    for k in range(1, n + 1):
        for combo in combinations(elements, k):
            out.append(frozenset(combo))
    return out


def compute_composition(n: int):
    """Enumerate triples and tabulate which targets are realized for each (R, S)."""
    subsets = all_nonempty_subsets(n)
    table = {(r, s): set() for r in BASE for s in BASE}
    for A in subsets:
        for B in subsets:
            r = relation(A, B)
            for C in subsets:
                s = relation(B, C)
                t = relation(A, C)
                table[(r, s)].add(t)
    return {k: frozenset(v) for k, v in table.items()}


GPT55_TABLE = {
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


REASONER_TABLE = {
    ('DR', 'DR'): frozenset({'DR', 'PO', 'PP', 'PPI'}),
    ('DR', 'PO'): frozenset({'DR', 'PO', 'PP'}),
    ('DR', 'PP'): frozenset({'DR', 'PO', 'PP'}),
    ('DR', 'PPI'): frozenset({'DR'}),
    ('PO', 'DR'): frozenset({'DR', 'PO', 'PPI'}),
    ('PO', 'PO'): frozenset({'DR', 'PO', 'PP', 'PPI'}),
    ('PO', 'PP'): frozenset({'PO', 'PP'}),
    ('PO', 'PPI'): frozenset({'DR', 'PO', 'PPI'}),
    ('PP', 'DR'): frozenset({'DR'}),
    ('PP', 'PO'): frozenset({'DR', 'PO', 'PP'}),
    ('PP', 'PP'): frozenset({'PP'}),
    ('PP', 'PPI'): frozenset({'DR', 'PO', 'PP', 'PPI'}),
    ('PPI', 'DR'): frozenset({'DR', 'PO', 'PPI'}),
    ('PPI', 'PO'): frozenset({'PO', 'PPI'}),
    ('PPI', 'PP'): frozenset({'PO', 'PP', 'PPI'}),
    ('PPI', 'PPI'): frozenset({'PPI'}),
}


def fmt(s):
    return '{' + ','.join(b for b in BASE if b in s) + '}'


def stability_check():
    """Confirm the computed table stabilizes by size 5."""
    print('Stability check across |U| = 2, 3, 4, 5:')
    print()
    prev = None
    for n in range(2, 6):
        table = compute_composition(n)
        sig = tuple(sorted((k, tuple(sorted(v))) for k, v in table.items()))
        delta = '' if prev is None else ('SAME' if sig == prev else 'DIFFERENT')
        print(f'  |U| = {n}: signature {hash(sig) % 10**8:08d}  {delta}')
        prev = sig
    print()


# The reasoner intentionally omits EQ from comp(R, inv(R)) cells because it
# models edges between distinct nodes only. The "missing" EQ in these four
# cells is a convention, not a bug; see EQ_ADMITTING_PAIRS in the reasoner.
REASONER_CONVENTIONAL_EQ_OMISSIONS = frozenset({
    ('DR', 'DR'), ('PO', 'PO'), ('PP', 'PPI'), ('PPI', 'PP'),
})


def compare_tables():
    """Compare the |U| = 5 computed table against both manuscript tables."""
    computed = compute_composition(5)
    issues_gpt = 0
    issues_reasoner = 0
    lines_full = []
    print('Per-cell comparison at |U| = 5:')
    print()
    header = f'  {"(R, S)":<14} {"computed":<28} {"GPT-5.5":<28} {"reasoner":<24} status'
    print(header)
    print('  ' + '-' * (len(header) - 2))
    for r in BASE:
        for s in BASE:
            comp_cell = computed[(r, s)]
            gpt_cell = GPT55_TABLE[(r, s)]
            reasoner_cell = REASONER_TABLE.get((r, s))
            gpt_ok = comp_cell == gpt_cell
            if not gpt_ok:
                issues_gpt += 1
            if reasoner_cell is not None:
                differs = comp_cell != reasoner_cell
                if differs:
                    # Convention-only difference: reasoner drops EQ from the
                    # four cells where the composition admits EQ.
                    diff_set = comp_cell - reasoner_cell
                    if (diff_set == frozenset({'EQ'})
                            and (r, s) in REASONER_CONVENTIONAL_EQ_OMISSIONS):
                        reas_status = 'conv.'
                    else:
                        reas_status = 'FAIL'
                        issues_reasoner += 1
                else:
                    reas_status = 'PASS'
                reas_str = fmt(reasoner_cell)
            else:
                reas_status = 'n/a'
                reas_str = 'n/a (EQ)'
            row_ok = gpt_ok and reas_status in ('PASS', 'conv.', 'n/a')
            mark_gpt = ' ' if gpt_ok else '*'
            mark_reas = ' ' if reas_status in ('PASS', 'conv.', 'n/a') else '*'
            line = (f'  {f"({r}, {s})":<14}'
                    f'{fmt(comp_cell):<28}'
                    f'{mark_gpt}{fmt(gpt_cell):<27}'
                    f'{mark_reas}{reas_str:<23}'
                    f'{reas_status}')
            print(line)
            lines_full.append(line)
    print()
    print(f'Summary: {issues_gpt} GPT-5.5 mismatches, {issues_reasoner} reasoner mismatches')
    print('         (convention-only EQ omissions in 4 reasoner cells do not count).')
    return issues_gpt, issues_reasoner, lines_full


def main():
    print('=' * 79)
    print('WP1: RCC5 composition-table verification by exhaustive subset enumeration')
    print('=' * 79)
    print()
    stability_check()
    issues_gpt, issues_reasoner, _ = compare_tables()
    print()
    if issues_gpt == 0 and issues_reasoner == 0:
        print('VERDICT: PASS. GPT-5.5 table matches brute-force enumeration exactly.')
        print('         Reasoner table differs only by the conventional EQ omission')
        print('         in 4 cells (DR/DR, PO/PO, PP/PPI, PPI/PP), as documented in')
        print('         the reasoner source by EQ_ADMITTING_PAIRS.')
        return 0
    print('VERDICT: FAIL. See * marks above for the mismatching cells.')
    return 1


if __name__ == '__main__':
    sys.exit(main())
