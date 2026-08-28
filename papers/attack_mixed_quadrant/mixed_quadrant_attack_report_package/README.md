# Mixed-quadrant attack report package

This package accompanies the report **Cold Attack on the Mixed Quadrant of the
forall-PO-Free Fragment of ALCI_RCC5** (2026-08-28).

## Main files

- `report/mixed_quadrant_attack_report.pdf` - rendered technical report.
- `report/mixed_quadrant_attack_report.tex` - complete LaTeX source.
- `new_probes/` - dependency-free executable checks added for this report.
- `original_packet/` - the supplied attack packet, copied without modification.
- `MANIFEST.sha256` - SHA-256 digest of every packaged file except the manifest itself.

## Principal findings

1. **Target B:** finite recurrence segments can be selected simultaneously so
   that every cross-kernel phase rectangle is constant. This is the property
   required by `kq_all`. The stronger infinite-tail rectangle statement is false.
2. **Target A:** the proposed local class-top label is always satisfiable, but a
   common fresh class top need not admit completion. An eight-point
   ordered-disjoint counterexample is included and checked.
3. **Target C:** selecting beyond all current external thresholds and then adding
   witnesses need not reach a finite fixed point. Uniform witnesses should instead
   be postselected and incorporated through an anchored PO-completion.

These are paper-level results, not additions to the supplied Lean development.
The Python checks validate finite RCC5 calculations and concrete counterexamples;
they are not substitutes for general Lean proofs.

## Run the new checks

From the package root:

```sh
./run_new_probes.sh
```

Expected result: each script prints a final `PASS` verdict and the wrapper exits
with status zero.

## Build the PDF

With a standard TeX Live installation:

```sh
cd report
latexmk -pdf -interaction=nonstopmode -halt-on-error mixed_quadrant_attack_report.tex
```

If `latexmk` is unavailable, run `pdflatex` twice with the same interaction and
error options.

## Formal-status cautions

- The finite simultaneous-rectangle theorem assumes the fixed finite family of
  source towers and the ability to choose arbitrarily late equal-type recurrence
  endpoints stated in the input packet.
- The displayed `kq_all` definition in `CERTIFICATE.md` should be checked for a
  `k != k'` guard before formal integration.
- Down-spectrum blocking gives a bounded local repair for Target A; finite SCC to
  kernel compilation remains unproved.
- The original packet is retained verbatim even where the report identifies probe
  defects or overclaims.

