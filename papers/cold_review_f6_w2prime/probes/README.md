# Probes

Four self-contained probes behind the width-barrier analysis. Python 3
stdlib only; they import the RCC5 composition table and the cover-tree
tableau from `../src/` (shipped in this packet).

Run all four from the packet root:

    ./run_probes.sh

Or individually:

    PYTHONPATH=src python3 probes/wp36_determination_vs_distinctness.py

(The probes contain a hard-coded `../../src` path from their in-repo
location; that entry is simply absent here and ignored -- `PYTHONPATH=src`
supplies the modules. The probe bytes are identical to the canonical
`verification/python/` versions.)

- `wp35_f6_width_attack` -- a concept with unbounded *total* DR-degree but
  bounded *live* width (all extra edges are shadows): the naive width
  attack fails.
- `wp36_determination_vs_distinctness` -- the four vertical singletons; PO
  never forced; horizontal distinctness stays live.
- `wp37_f6_reduces_to_forcing` -- substrate free + horizontal chains block
  => F6 reduces to horizontal forcing.
- `wp38_path_automaton_and_f4` -- the path-automaton lemma (no non-EQ
  horizontal recurrence). Ignore the F4 part (an unrelated
  completeness-side over-restriction).
