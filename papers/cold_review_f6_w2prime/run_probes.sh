#!/usr/bin/env bash
# Run the four F6/W2' probes. Dependency-free (Python 3 stdlib only).
# They import the RCC5 composition table + cover-tree tableau from src/
# (shipped in this packet); PYTHONPATH points there.
set -e
cd "$(dirname "$0")"
export PYTHONPATH="src"
for w in wp35_f6_width_attack wp36_determination_vs_distinctness \
         wp37_f6_reduces_to_forcing wp38_path_automaton_and_f4; do
  echo "======================================================================"
  echo "  probes/$w.py"
  echo "======================================================================"
  python3 "probes/$w.py"
  echo
done
