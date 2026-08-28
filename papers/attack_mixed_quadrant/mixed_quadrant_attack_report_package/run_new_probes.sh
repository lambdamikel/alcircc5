#!/bin/sh
set -eu

cd "$(dirname "$0")/new_probes"

for probe in \
  target_a_class_top_counterexample.py \
  target_b_finite_rectangle_lemma.py \
  target_c_selection_circularity.py
do
  echo "=================================================================="
  echo "== $probe"
  echo "=================================================================="
  python3 "$probe"
  echo
done

echo "ALL NEW PROBES PASS"

