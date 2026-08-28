# Mixed-quadrant cold attack, round 2

This package is an independent technical attack on
`attack_mixed_quadrant_r2.zip`. The supplied packet is preserved unchanged
under `original_packet/`; the report and all added probes are separate.

## Results

| Target | Cold-attack result |
|---|---|
| D1: global acyclicity | False for the stated local-agreement/fallback discipline. Two individually safe PO fallback groups form an alternating cycle. |
| D2: safe existing witness | False at the exact refined down-spectrum key. The only relevant gate-mate witness is DR from the blocked node. |
| E: finite closure | The pure finite key-demand closure terminates, with the stated product bound. |
| E: valid placement | The current gate-mate borrowing policy is not anchor-compatible. A general bounded repair remains open. |

These conclusions do not claim that every globally coordinated witness
assignment fails, or that no different bounded construction can repair the
mixed quadrant. The input packet reports Lean certification, but it does not
contain Lean source files, theorem statements, a build manifest, or compiler
output; those claims were therefore not independently rebuilt here.

## Contents

- `report/mixed_quadrant_round2_attack_report.pdf`: 14-page technical report.
- `report/mixed_quadrant_round2_attack_report.tex`: report source.
- `new_probes/`: exact countermodels, symbolic checks, and probe audits.
- `original_packet/attack_mixed_quadrant_r2/`: the supplied R2 packet,
  unchanged.
- `MANIFEST.sha256`: checksums for every other packaged file.

## Reproduce

From the package root:

```sh
./run_new_probes.sh
sha256sum -c MANIFEST.sha256
```

The exact finite models are deterministic. The audit reproduces the packet's
fixed-seed sweeps and takes roughly a minute on a typical workstation.

To rebuild the PDF with a standard TeX Live installation:

```sh
cd report
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  mixed_quadrant_round2_attack_report.tex
```

Input ZIP SHA-256:
`22777b9c3a132f6102e0207e07ee04135338e00580c8315ff92098d028e41d48`.

