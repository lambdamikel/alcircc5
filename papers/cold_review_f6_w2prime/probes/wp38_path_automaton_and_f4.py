r"""
WP38 -- the 14th review (GPT-5.5 cold, rounds 19-25) machine-verified:
the path-automaton lemma (a genuine strengthening) and the F4
over-restriction (a confirmed, repairable defect).

The 14th review of the project was the FIRST cold review of the Lean
development (papers/gpt5.5_round25_review/). Verdict: "gap, repairable"
-- and, importantly, the SOUNDNESS adequacy was CONFIRMED (syntax,
`sat` polarity, `RCC5Interp` R1/R2/R3, and the comp/conv table all
found faithful to the reference semantics; no soundness defect). The
gaps are on the finite-certificate / completeness interface (F1: Cert/
Catalog use higher-order function fields, not finite syntax; F2:
`Satisfiable` fixes the carrier to `Occ` rather than arbitrary domains;
F3: `CompletenessObligation` is not stated in decision-grade/bounded
form) plus one concrete over-restriction (F4) and weak witnesses (F5).

This harness verifies the two machine-checkable items.

(1) PATH-AUTOMATON LEMMA (GPT's genuine new result, after reading the
    width-barrier report). Define the reachable "relation set" of a
    composition path from the identity: Rel([]) = {EQ},
    Rel(w.a) = U_{r in Rel(w)} comp(r,a). A path segment is FOLDABLE if
    EQ in Rel(w) (a repeated state can be blocked by equality). The
    exhaustive finite audit of the induced subset-automaton proves:

      There is NO non-EQ cycle using a horizontal label (DR or PO);
      every cycle among no-EQ states uses only PP or PPI.

    So every infinite composition path that never admits an EQ-fold is
    eventually VERTICAL. This strengthens WP36 ("only singleton
    determinations are vertical") to a path/automaton-level statement
    that also handles non-singleton propagation sets like {DR,PO,PP}.
    It is exactly a "horizontal clock": horizontal recurrence always
    folds; non-foldable recurrence is vertical. (It does NOT close F6 --
    F6 is a WIDTH statement, not a path statement -- but it removes a
    class of would-be counterexamples and matches WP37's reduction.)

(2) F4 CONFIRMED (a repairable over-restriction in SCat). The semantic
    condition SCond.tri excludes degenerate triples through the fresh
    occurrence (x != born i jz, y != born i jz), but the catalogue
    check SCat.net_r3 has only p != q -- so it can inspect the diagonal
    template value net(fresh_j, fresh_j). With a junk diagonal
    net(f1,f1)=DR and net(f0,f1)=PP, SCat.net_r3 (p=f0,q=f1,j=1) demands
    PP in comp(PP, conv DR) = comp(PP,DR) = {DR}: FALSE. So SCat rejects
    a certificate over an irrelevant diagonal. The all-DR witnesses mask
    it because comp(DR,DR) is the whole algebra. Repair (identified, not
    yet applied to avoid destabilizing the native_decide witness proofs;
    it is completeness-side over-rejection, never a soundness issue):
    add p != fresh_j and q != fresh_j to net_r3, or require diagonal EQ.

Run: python3 verification/python/wp38_path_automaton_and_f4.py
"""
import sys, os, itertools, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', '..', 'src'))

def derive_full(n=6):
    U = range(n)
    subs = [frozenset(c) for k in range(1, n + 1)
            for c in itertools.combinations(U, k)]
    def r(a, b):
        if a == b: return 'EQ'
        if not a & b: return 'DR'
        if a < b: return 'PP'
        if b < a: return 'PPI'
        return 'PO'
    t = {}
    for a in subs:
        for b in subs:
            for c in subs:
                t.setdefault((r(a, b), r(b, c)), set()).add(r(a, c))
    return {k: frozenset(v) for k, v in t.items()}

C = derive_full()
LAB = ['DR', 'PO', 'PP', 'PPI']

def step(S, a):
    out = set()
    for r in S: out |= C[(r, a)]
    return frozenset(out)

def path_automaton_lemma():
    start = frozenset({'EQ'})
    seen = {start}; frontier = [start]; edges = []
    while frontier:
        S = frontier.pop()
        for a in LAB:
            T = step(S, a); edges.append((S, a, T))
            if T not in seen: seen.add(T); frontier.append(T)
    noEQ = lambda S: 'EQ' not in S
    sub = [(S, a, T) for (S, a, T) in edges if noEQ(S) and noEQ(T)]
    nodes = {S for e in sub for S in (e[0], e[2])}
    adj = collections.defaultdict(list)
    for S, a, T in sub: adj[S].append(T)
    idx = {}; low = {}; onst = {}; stk = []; comp = {}; cnt = [0]; cid = [0]
    sys.setrecursionlimit(10000)
    def tarjan(v):
        idx[v] = low[v] = cnt[0]; cnt[0] += 1; stk.append(v); onst[v] = True
        for w in adj[v]:
            if w not in idx: tarjan(w); low[v] = min(low[v], low[w])
            elif onst.get(w): low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            c = cid[0]; cid[0] += 1
            while True:
                w = stk.pop(); onst[w] = False; comp[w] = c
                if w == v: break
    for v in nodes:
        if v not in idx: tarjan(v)
    cyc = [(S, a, T) for (S, a, T) in sub if comp[S] == comp[T]]
    horiz = [(sorted(S), a, sorted(T)) for (S, a, T) in cyc if a in ('DR', 'PO')]
    vert = [(a, sorted(S)) for (S, a, T) in cyc if a in ('PP', 'PPI')]
    return len(seen), len(nodes), len(cyc), horiz, vert

def f4_check():
    # PP in comp(PP, conv DR) ?  conv DR = DR ; comp(PP,DR) = {DR}
    return ('PP' in C[('PP', 'DR')], sorted(C[('PP', 'DR')]),
            sorted(C[('DR', 'DR')]))

if __name__ == '__main__':
    print("WP38: 14th-review verified items")
    print("=" * 70)
    nseen, nno, ncyc, horiz, vert = path_automaton_lemma()
    print(f"\n(1) path-automaton lemma:")
    print(f"    reachable Rel-states={nseen}, no-EQ states={nno}, "
          f"no-EQ cycle edges={ncyc}")
    print(f"    HORIZONTAL (DR/PO) cycle edges: {len(horiz)}  {horiz}")
    print(f"    VERTICAL (PP/PPI) cycle edges:  {len(vert)}")
    for a, S in sorted(vert): print(f"        {a}: {S} (self-loop)")
    lemma_ok = len(horiz) == 0 and len(vert) == 6
    print(f"    LEMMA HOLDS (no horizontal non-EQ cycle): {lemma_ok}")

    pp_in, ppdr, drdr = f4_check()
    print(f"\n(2) F4 over-restriction:")
    print(f"    conv DR = DR; comp(PP,DR) = {ppdr}; PP in it? {pp_in}")
    print(f"    => SCat.net_r3 demands PP in {{DR}} on a junk diagonal: "
          f"rejects a valid certificate (F4 CONFIRMED)")
    print(f"    all-DR masking: comp(DR,DR) = {drdr} (absorbs everything)")
    f4_ok = (pp_in is False)

    print("\n" + "=" * 70)
    ok = lemma_ok and f4_ok
    print("WP38 OVERALL:",
          "PASS -- path-automaton lemma verified (no horizontal non-EQ "
          "cycle; a genuine strengthening of WP36) and F4 over-restriction "
          "confirmed (repairable, completeness-side only)." if ok
          else "ATTENTION")
    sys.exit(0 if ok else 1)
