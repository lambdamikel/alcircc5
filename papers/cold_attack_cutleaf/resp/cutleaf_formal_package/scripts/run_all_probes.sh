#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
OUT=${1:-"$ROOT/outputs/rerun"}
mkdir -p "$OUT"

run_original() {
  name=$1
  echo "Running $name"
  (cd "$ROOT/original/probes" && python3 "$name") > "$OUT/${name%.py}.txt" 2>&1
}

run_candidate() {
  name=$1
  echo "Running $name"
  PYTHONPATH="$ROOT/original/probes:$ROOT/candidates/probes${PYTHONPATH:+:$PYTHONPATH}" \
    python3 "$ROOT/candidates/probes/$name" > "$OUT/${name%.py}.txt" 2>&1
}

run_original wp112_lap_continuation_closed_form.py
run_original wp115_declared_edge_acceptance.py
run_original wp116_target_rounds.py
run_original wp117_kernel_phase_coverage.py
run_original wp118_multitier_acceptance.py
run_candidate wp119_extremal_carrier_probe.py
run_candidate wp120_support_label_fence.py
run_candidate wp121_support_multitier_acceptance.py

echo "Outputs written to $OUT"
