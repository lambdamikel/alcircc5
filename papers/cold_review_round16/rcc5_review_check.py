REL = ("EQ", "PP", "PPI", "PO", "DR")
conv = {"EQ": "EQ", "PP": "PPI", "PPI": "PP", "PO": "PO", "DR": "DR"}

Comp = {
    "EQ":  {"EQ": {"EQ"}, "PP": {"PP"}, "PPI": {"PPI"}, "PO": {"PO"}, "DR": {"DR"}},
    "PP":  {"EQ": {"PP"}, "PP": {"PP"}, "PPI": set(REL), "PO": {"PP", "PO", "DR"}, "DR": {"DR"}},
    "PPI": {"EQ": {"PPI"}, "PP": {"EQ", "PP", "PPI", "PO"}, "PPI": {"PPI"}, "PO": {"PPI", "PO"}, "DR": {"PPI", "PO", "DR"}},
    "PO":  {"EQ": {"PO"}, "PP": {"PP", "PO"}, "PPI": {"PPI", "PO", "DR"}, "PO": set(REL), "DR": {"PPI", "PO", "DR"}},
    "DR":  {"EQ": {"DR"}, "PP": {"PP", "PO", "DR"}, "PPI": {"DR"}, "PO": {"PP", "PO", "DR"}, "DR": set(REL)},
}
Comp = {a: {b: frozenset(v) for b, v in row.items()} for a, row in Comp.items()}


def comp_set(A, B):
    out = set()
    for a in A:
        for b in B:
            out |= set(Comp[a][b])
    return frozenset(out)


for a in REL:
    for b in REL:
        lhs = {conv[c] for c in Comp[a][b]}
        rhs = set(Comp[conv[b]][conv[a]])
        assert lhs == rhs, (a, b, lhs, rhs)

for a in REL:
    for b in REL:
        for c in REL:
            ok = c in Comp[a][b]
            assert ok == (a in Comp[c][conv[b]])
            assert ok == (b in Comp[conv[a]][c])

atoms = ("PP", "PPI", "PO", "DR")
folds = {frozenset([a]) for a in atoms}
changed = True
while changed:
    changed = False
    for F in list(folds):
        for a in atoms:
            G = comp_set(F, frozenset([a]))
            if G not in folds:
                folds.add(G)
                changed = True

print("fold count:", len(folds))
for F in sorted(folds, key=lambda x: (len(x), sorted(x))):
    print("{" + ",".join(sorted(F)) + "}")

assert len(folds) == 10
assert all(len(F) == 1 or ("DR" in F or "PO" in F) for F in folds)
assert {frozenset(["PO", "PP"]),
        frozenset(["PO", "PPI"]),
        frozenset(["EQ", "PO", "PP", "PPI"])} == {
            F for F in folds if len(F) > 1 and "DR" not in F
        }

assert all("DR" in Comp[w]["DR"] for w in REL)
assert all({"DR", "PO"} <= set(Comp[a][b]) for a in ("DR", "PO") for b in ("DR", "PO"))
assert Comp["PP"]["PP"] == frozenset(["PP"])
assert Comp["PPI"]["PPI"] == frozenset(["PPI"])

for a in REL:
    for b in REL:
        if (a, b) != ("EQ", "EQ") and "EQ" in Comp[a][b]:
            assert {"PP", "PPI", "PO"} <= set(Comp[a][b])

print("PASS")
