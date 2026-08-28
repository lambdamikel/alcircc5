# What we did with round 1

Everything was reproduced independently before being accepted: your probes were
run, and both load-bearing arguments were rebuilt from the report's prose rather
than from your code.

## Accepted in full

**Target A's counterexample.** Rebuilt from the prose: the frame is
composition-closed, `mty(v₁) = mty(v₂)`, and `T` contains no positive `∀PP`
formula — so the "is the class-top label satisfiable?" question we posed is
trivially YES and was too weak to be the question. Your diagnosis is the right
one: the obstruction is not the edge but what the shared top must then serve.

It also killed a variant we had derived and were one step from formalizing — take
the witness of a *maximal* group member, which keeps the order acyclic. It dies to
the same argument, because declaring the edge makes that witness a common top *in
the declared frame*. We would have spent a session on it.

**Target B.** Formalized end to end (see `STATUS.md`). Your framing insight was
the whole thing: we asked for tail × tail constancy, which is false; the
certificate reads finite segments, where it is true and available arbitrarily
late. Two facts we had to discover while formalizing, in case they are useful:
pairs must be handled in INDEX ORDER with the reverse direction from `conv`
(doing both directions from the rectangle demands pushing an already-placed tower
out), and the period cannot be an input (the rectangle's threshold depends on the
earlier segment's length, while equal-type endpoints determine that length).

**Two of your three probe findings.**
* `wp131`'s Q3 was **tautological** — its "has upper" predicate repeated Q2's own
  condition after Q2 had failed, so the `0/140` was forced by program structure.
  We had reported that as headline evidence. Corrected (D-test dropped):
  **44/140**, matching your 44 exactly.
* `wp131`'s cycle counts were an **undercount** — it reselected a target per
  borrower while the construction spawns one child per (gate-mate, demand), and
  off-node targets were silently dropped. Corrected: **17** repeat-free
  survivors, not 5. The probe now reports dropped edges explicitly.
* `wp93`/`wp94` are weak as you say (budget-exempted `ee_all`, off-diagonal `EQ`
  between distinct occurrences of one region, a `len(used) > 0` success test).
  Both predate this work and were shipped with an "ALL PASS" banner. Accepted;
  they are not in this packet.

**The `kq_all` guard.** You were right that our `CERTIFICATE.md` omitted `k ≠ k'`.
The guard IS present in the Lean; the packet document was wrong. Fixed.

## One claim we could not reproduce

You report that redirecting all borrowers to the actual gate child yields **eight**
cyclic instances under **both** repeat-free and "agree" selection. We reproduce
the repeat-free half (our corrected count is 17 in-probe, 8 in a standalone
reconstruction — either way, more than our original 5, so your finding stands).

We do not reproduce the "agree" half. The difference is what the agree rule is
allowed to choose: you fix the child by the rule GREEDY selection produced and
then redirect borrowers to it, whereas the rule as we stated it chooses the single
child per (gate-mate, demand) GROUP-AWARE — a freedom the construction has, since
which witness that child is, is ours to pick. Under that reading the corrected
probe reads 0 cycles in all four classes. If you think group-aware selection is
illegitimate for a reason we have missed, that would be worth knowing, because
`dkey_union_serves` is built on it.

## A probe defect we found ourselves, after yours

Testing your down-spectrum proposal, our first `wp132` failed its own stated
control (0 failures at the type-only key, on as few as 1 non-vacuous group) and
was withheld. The second reported failures SURVIVING the refined key — also
wrong, and ours: the serviceability test searched only EXISTING model points and
had a `pass` stub where the FRESH witness belonged, which is your construction's
entire mechanism. Fixed; the third run is the one in this packet.

Three probe defects in two days, two found by you. The lesson we recorded: a
diagnostic must ask a different question from the test it diagnoses, and a harness
that drops data it cannot place must count the drops.
