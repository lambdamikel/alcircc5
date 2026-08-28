#!/bin/sh
set -eu

ATTACK_ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PYTHON_BIN=${PYTHON_BIN:-python3}

run_probe() {
    script_name=$1
    printf '\n== %s ==\n' "$script_name"
    "$PYTHON_BIN" -B "$ATTACK_ROOT/new_probes/$script_name"
}

run_probe target_d1_multigroup_cycle.py
run_probe target_d2_mixed_counterexample.py
run_probe target_d2_exhaustive_countermodel.py
run_probe target_e_anchor_compatibility.py
run_probe target_e_finite_key_anchor_counterexample.py
run_probe probe_audit_r2.py

printf '\nAll cold-attack probes passed.\n'
