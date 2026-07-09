#!/usr/bin/env python3
"""
WP19 -- G3b mixed-orientation probe.

This is not a valid round-13 D-abstraction under literal D2: D2 would
verticalize x across the first boundary because the separator relation x-z is
PP, so x would become co-bagged with y. The point of the probe is narrower:
it mechanically checks the RCC5 fact that a vertical endpoint relation can be
supported by a mixed PP/PPI bag path. Therefore Coverage case (c)'s uniform-
orientation conclusion is not a consequence of the composition table alone;
it needs the extra D2 fallback invariant.

Network: bag B0={x,z}, bag B1={z,y}, overlap {z}, with
    x PP z, z PPI y, and completion x PP y.
The complete network is closed. For a source type containing AllPP.D, D3
propagates from x to z along x PP z, but does not propagate from z to y along
z PPI y. Thus y may lack D even though the completed relation x PP y holds,
unless D2 has already forced co-bagging/row coverage.
"""

BASE = ('EQ', 'PP', 'PPI', 'PO', 'DR')
CONV = {'EQ': 'EQ', 'PP': 'PPI', 'PPI': 'PP', 'PO': 'PO', 'DR': 'DR'}
COMP = {
    ('EQ', 'EQ'): {'EQ'}, ('EQ', 'PP'): {'PP'}, ('EQ', 'PPI'): {'PPI'},
    ('EQ', 'PO'): {'PO'}, ('EQ', 'DR'): {'DR'},
    ('PP', 'EQ'): {'PP'}, ('PP', 'PP'): {'PP'},
    ('PP', 'PPI'): set(BASE), ('PP', 'PO'): {'PP', 'PO', 'DR'},
    ('PP', 'DR'): {'DR'},
    ('PPI', 'EQ'): {'PPI'}, ('PPI', 'PP'): {'EQ', 'PP', 'PPI', 'PO'},
    ('PPI', 'PPI'): {'PPI'}, ('PPI', 'PO'): {'PPI', 'PO'},
    ('PPI', 'DR'): {'PPI', 'PO', 'DR'},
    ('PO', 'EQ'): {'PO'}, ('PO', 'PP'): {'PP', 'PO'},
    ('PO', 'PPI'): {'PPI', 'PO', 'DR'}, ('PO', 'PO'): set(BASE),
    ('PO', 'DR'): {'PPI', 'PO', 'DR'},
    ('DR', 'EQ'): {'DR'}, ('DR', 'PP'): {'PP', 'PO', 'DR'},
    ('DR', 'PPI'): {'DR'}, ('DR', 'PO'): {'PP', 'PO', 'DR'},
    ('DR', 'DR'): set(BASE),
}


def setrel(N, a, b, r):
    N[(a, b)] = r
    N[(b, a)] = CONV[r]


def is_closed(V, N):
    for i in V:
        for j in V:
            if i == j:
                continue
            for k in V:
                if k == i or k == j:
                    continue
                if N[(i, k)] not in COMP[(N[(i, j)], N[(j, k)])]:
                    return False, (i, j, k, N[(i, j)], N[(j, k)], N[(i, k)], COMP[(N[(i, j)], N[(j, k)])])
    return True, None


def d3_pp_closure(edges, source='x'):
    # Minimal symbolic D3 propagation for a single universal AllPP.D.
    has_D = {source: False, 'z': False, 'y': False}
    has_AllPP_D = {source: True, 'z': False, 'y': False}
    changed = True
    while changed:
        changed = False
        for a, b, r in edges:
            if r == 'PP' and has_AllPP_D.get(a, False):
                if not has_D[b]:
                    has_D[b] = True
                    changed = True
                if not has_AllPP_D[b]:
                    has_AllPP_D[b] = True
                    changed = True
            # Dually, AllPPI would propagate over PPI; not used here.
    return has_D, has_AllPP_D


def main():
    N = {}
    setrel(N, 'x', 'z', 'PP')
    setrel(N, 'z', 'y', 'PPI')
    setrel(N, 'x', 'y', 'PP')
    closed, witness = is_closed(['x', 'z', 'y'], N)
    edges = [('x', 'z', 'PP'), ('z', 'y', 'PPI')]
    has_D, has_All = d3_pp_closure(edges)
    print('B0={x,z}, B1={z,y}, overlap={z}')
    print('relations: x PP z, z PPI y, completion x PP y')
    print('composition_closed =', closed)
    if not closed:
        print('closure_witness =', witness)
    print('D3_from_AllPP_D_at_x gives D flags:', has_D)
    print('D3_from_AllPP_D_at_x gives AllPP.D flags:', has_All)
    print('endpoint_relation_x_y =', N[('x', 'y')])
    print('conclusion = PASS: mixed PP/PPI path can have vertical endpoint; uniformity needs an extra invariant')
    return 0 if closed and N[('x', 'y')] == 'PP' and not has_D['y'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
