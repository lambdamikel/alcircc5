#!/usr/bin/env python3
"""
WP40: PO-incoherent period descriptor does not by itself force live width.

Builds finite prefixes of the standard PO-gap construction:
  d_0 PP d_1 PP d_2 PP ...
  types alternate A/B; at A-position d_{2k} a side witness w_k is PO,
  below it DR, above it PPI.  Pairwise w_j DR w_k.

Checks RCC5 composition closure and measures which chain-witness edges are
locally shadowed by a singleton composition through a third node.  The only
unshadowed event edges lie in a bounded-width window around each PO event.
"""
from itertools import product

REL = ["DR", "PO", "PP", "PPI"]
ALL = set(REL)
CONV = {"DR":"DR", "PO":"PO", "PP":"PPI", "PPI":"PP", "EQ":"EQ"}
COMP = {
    ("DR","DR"): set(["DR","PO","PP","PPI"]),  # EQ omitted for distinct endpoints
    ("DR","PO"): set(["DR","PO","PP"]),
    ("DR","PP"): set(["DR","PO","PP"]),
    ("DR","PPI"): set(["DR"]),
    ("PO","DR"): set(["DR","PO","PPI"]),
    ("PO","PO"): set(["DR","PO","PP","PPI"]),
    ("PO","PP"): set(["PO","PP"]),
    ("PO","PPI"): set(["DR","PO","PPI"]),
    ("PP","DR"): set(["DR"]),
    ("PP","PO"): set(["DR","PO","PP"]),
    ("PP","PP"): set(["PP"]),
    ("PP","PPI"): set(["DR","PO","PP","PPI"]),
    ("PPI","DR"): set(["DR","PO","PPI"]),
    ("PPI","PO"): set(["PO","PPI"]),
    ("PPI","PP"): set(["PO","PP","PPI"]), # EQ omitted
    ("PPI","PPI"): set(["PPI"]),
}

def build(n_chain: int):
    assert n_chain >= 3
    # include witnesses w_k for A events d_{2k} with room on both sides where possible
    n_w = (n_chain + 1) // 2
    nodes = [f"d{i}" for i in range(n_chain)] + [f"w{k}" for k in range(n_w)]
    idx_d = {f"d{i}": i for i in range(n_chain)}
    idx_w = {f"w{k}": k for k in range(n_w)}
    rho = {}
    for x in nodes:
        rho[(x,x)] = "EQ"
    def setrel(x,y,r):
        if x == y:
            assert r == "EQ"
            return
        rho[(x,y)] = r
        rho[(y,x)] = CONV[r]
    # chain: d_i PP d_j for i < j
    for i in range(n_chain):
        for j in range(i+1, n_chain):
            setrel(f"d{i}", f"d{j}", "PP")
    # witnesses: sequence DR ... PO ... PPI relative to chain
    for k in range(n_w):
        for i in range(n_chain):
            if i <= 2*k - 1:
                r = "DR"
            elif i == 2*k:
                r = "PO"
            else:
                r = "PPI"
            setrel(f"d{i}", f"w{k}", r)
    # pairwise witnesses discrete
    for j in range(n_w):
        for k in range(j+1, n_w):
            setrel(f"w{j}", f"w{k}", "DR")
    return nodes, rho

def check_closed(nodes, rho):
    bad = []
    for x,y,z in product(nodes, repeat=3):
        if len({x,y,z}) < 3:
            continue
        rxy, ryz, rxz = rho[(x,y)], rho[(y,z)], rho[(x,z)]
        if rxz not in COMP[(rxy, ryz)]:
            bad.append((x,y,z,rxy,ryz,rxz,COMP[(rxy,ryz)]))
    return bad

def is_singleton_shadow(x,y,nodes,rho):
    if x == y:
        return False, None
    r = rho[(x,y)]
    for z in nodes:
        if z == x or z == y:
            continue
        cell = COMP[(rho[(x,z)], rho[(z,y)])]
        if cell == {r}:
            return True, z
    return False, None

def summarize(n):
    nodes, rho = build(n)
    bad = check_closed(nodes, rho)
    if bad:
        print(f"n={n}: NOT CLOSED, first violation: {bad[0]}")
        return
    chain_w_edges = []
    live = []
    shadow = []
    for x in nodes:
        for y in nodes:
            if x >= y:
                continue
            if (x.startswith('d') and y.startswith('w')) or (x.startswith('w') and y.startswith('d')):
                s,z = is_singleton_shadow(x,y,nodes,rho)
                chain_w_edges.append((x,y,rho[(x,y)],s,z))
                (shadow if s else live).append((x,y,rho[(x,y)],z))
    # group live edges by witness and by chain point
    by_w = {}
    by_d = {}
    for x,y,r,_ in live:
        w = x if x.startswith('w') else y
        d = x if x.startswith('d') else y
        by_w.setdefault(w, []).append((x,y,r))
        by_d.setdefault(d, []).append((x,y,r))
    max_per_w = max((len(v) for v in by_w.values()), default=0)
    max_per_d = max((len(v) for v in by_d.values()), default=0)
    print(f"n_chain={n:2d} nodes={len(nodes):2d} witnesses={(n+1)//2:2d} CLOSED=True")
    print(f"  chain-witness edges: total={len(chain_w_edges):3d}, singleton-shadow={len(shadow):3d}, local-live={len(live):3d}, max live per witness={max_per_w}")
    print(f"  max live incident per chain point={max_per_d}")
    for w in sorted(by_w, key=lambda s:int(s[1:]))[:4]:
        print(f"    {w}: {by_w[w]}")
    if len(by_w) > 4:
        print("    ...")

if __name__ == "__main__":
    for n in [5, 7, 9, 13, 21]:
        summarize(n)
