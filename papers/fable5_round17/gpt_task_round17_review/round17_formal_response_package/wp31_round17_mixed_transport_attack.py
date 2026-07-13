#!/usr/bin/env python3
"""
WP31 -- targeted finite attack on round-17 Definition 3.3 / Theorem 3.1.

It isolates the edge case not exercised by WP30: crossing from a copy k
into a child gluing h where one old endpoint is outside k (updated by T)
and the other old endpoint is a member of k but not of h's separator
(a birth-adjacent/catalogue state, not in the domain of T as written).

Under the manuscript's P3 text, the pair is not transported. If the
missing current pair is omitted from S4, a standard RCC5 triangle accepted
by S1/S2/S3 becomes composition-inconsistent. Adding the evident mixed
transport rule makes S4 reject it.
"""

REL = ("EQ", "PP", "PPI", "PO", "DR")
CONV = {"EQ": "EQ", "PP": "PPI", "PPI": "PP", "PO": "PO", "DR": "DR"}
COMP = {
    "EQ":  {"EQ": {"EQ"}, "PP": {"PP"}, "PPI": {"PPI"},
             "PO": {"PO"}, "DR": {"DR"}},
    "PP":  {"EQ": {"PP"}, "PP": {"PP"}, "PPI": set(REL),
             "PO": {"PP", "PO", "DR"}, "DR": {"DR"}},
    "PPI": {"EQ": {"PPI"}, "PP": {"EQ", "PP", "PPI", "PO"},
             "PPI": {"PPI"}, "PO": {"PPI", "PO"},
             "DR": {"PPI", "PO", "DR"}},
    "PO":  {"EQ": {"PO"}, "PP": {"PP", "PO"},
             "PPI": {"PPI", "PO", "DR"}, "PO": set(REL),
             "DR": {"PPI", "PO", "DR"}},
    "DR":  {"EQ": {"DR"}, "PP": {"PP", "PO", "DR"},
             "PPI": {"DR"}, "PO": {"PP", "PO", "DR"},
             "DR": set(REL)},
}
COMP = {a: {b: frozenset(v) for b, v in row.items()} for a, row in COMP.items()}


def check(condition, msg):
    if not condition:
        raise AssertionError(msg)


# Intended geometry at child gluing h:
# y PP z PP s, separator s PPI b, but steering chooses y PO b and z DR b.
yz = "PP"
zs = "PP"
ys = "PP"      # forced by y PP z PP s, and used as y's row to separator s
sb = "PPI"     # pattern edge s -> b
zb = "DR"      # steering value for parent member z toward fresh b

yb_bad = "PO"  # steering value for ambient y toward fresh b

# S1 checks through separator s. Both bad choices pass S1 because Comp(PP,PPI)=Rel.
check(yb_bad in COMP[ys][sb], "S1 should allow y PO b through s")
check(zb in COMP[zs][sb], "S1 should allow z DR b through s")

# S3 is vacuous for one fresh member; S2 can be made true by setting safe domains accordingly.
# S4, if the current pair (St_h(y), St_h(z), PP) is present, rejects y PO b.
required_by_s4 = COMP[yz][zb]
check(required_by_s4 == frozenset({"DR"}), f"Expected Comp(PP,DR)={{DR}}, got {required_by_s4}")
check(yb_bad not in required_by_s4, "S4 should reject the bad y-b value")

# Direct composition-closure failure of triangle (y,z,b): rho(y,b) must be in Comp(rho(y,z),rho(z,b)).
closure_ok = yb_bad in COMP[yz][zb]
check(not closure_ok, "The bad triangle should fail RCC5 composition closure")

# Now model just the P-rules at the state-symbol level.
# At parent gluing g, z is fresh in copy k and y is ambient, so P2 creates (Yg,Zg,PP).
Yg = "state_y_at_g"          # ambient state before attaching k
Zg = "birth_state_z_in_k"    # z's birth state at g
Yh = "state_y_at_child_h"    # T(Yg)
Zh = "birth_adjacent_state_z_at_h"  # read from catalogue; not T(Zg) in Def. 3.3

reachable_pairs = {(Yg, Zg, yz), (Zg, Yg, CONV[yz])}
T = {Yg: Yh}  # T is defined only for occurrences ambient at g; z in V_k has no T-state clause.

# Manuscript P3: transport only if both singleton transitions are defined.
for a, b, w in list(reachable_pairs):
    if a in T and b in T:
        reachable_pairs.add((T[a], T[b], w))
        reachable_pairs.add((T[b], T[a], CONV[w]))

missing_current_pair = (Yh, Zh, yz) not in reachable_pairs
check(missing_current_pair, "As written P3 unexpectedly transported the mixed ambient/parent pair")

# Evident repair: mixed transport maps the parent-copy endpoint to its birth-adjacent child-gluing state.
reachable_repaired = set(reachable_pairs)
parent_adjacent = {Zg: Zh}
for a, b, w in [(Yg, Zg, yz), (Zg, Yg, CONV[yz])]:
    if a in T and b in parent_adjacent:
        reachable_repaired.add((T[a], parent_adjacent[b], w))
    if a in parent_adjacent and b in T:
        reachable_repaired.add((parent_adjacent[a], T[b], w))

check((Yh, Zh, yz) in reachable_repaired, "Mixed transport repair should add the current pair")

print("PASS: S1/S2/S3 can accept the bad y-z-b triangle when the mixed pair is omitted.")
print("PASS: The manuscript P3 text omits (state_y_at_child_h, birth_adjacent_state_z_at_h, PP).")
print("PASS: Adding a mixed ambient/parent transport rule restores the pair, so S4 rejects the bad row.")
