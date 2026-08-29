#!/bin/sh
set -eu

PLAN_ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PYTHON_BIN=${PYTHON_BIN:-python3}

printf '%s\n' "== blueprint dependency ledger =="
"$PYTHON_BIN" -B "$PLAN_ROOT/blueprint/check_blueprint.py"

for script_name in \
    target_d1_multigroup_cycle.py \
    target_d2_exhaustive_countermodel.py \
    target_e_anchor_compatibility.py
do
    printf '\n== regression: %s ==\n' "$script_name"
    "$PYTHON_BIN" -B "$PLAN_ROOT/regressions/$script_name"
done

printf '\nAll blueprint and cold-attack regressions passed.\n'
