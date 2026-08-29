#!/bin/sh
set -eu

package_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$package_dir"

echo "[1/7] Verify package checksums"
sha256sum -c MANIFEST.sha256

echo "[2/7] Verify original ZIP integrity"
unzip -t original_artifact/cone_scheme_attack.zip >/dev/null

echo "[3/7] Compile Python probes"
python3 -c 'from pathlib import Path; [compile(Path(p).read_text(), p, "exec") for p in ["probes/wp133_cone_scheme_unfolding.py", "probes/wp134_cone_scheme_prune.py", "probes/wp_full_logic_boundary.py"]]'

echo "[4/7] Run pruning probe"
python3 probes/wp134_cone_scheme_prune.py

echo "[5/7] Run full-logic boundary probe"
python3 probes/wp_full_logic_boundary.py

echo "[6/7] Check documented wp133 outcome"
wp133_log=$(mktemp)
trap 'rm -f "$wp133_log"' EXIT HUP INT TERM
if python3 probes/wp133_cone_scheme_unfolding.py >"$wp133_log" 2>&1; then
  echo "wp133 unexpectedly exited 0" >&2
  cat "$wp133_log" >&2
  exit 1
fi
cat "$wp133_log"
if grep -Eq 'Frame violations[^0-9]*0|frame violations[^0-9]*0' "$wp133_log"; then
  :
else
  echo "wp133 did not report the documented zero frame violations" >&2
  exit 1
fi

echo "[7/7] Lean source check"
if command -v lean >/dev/null 2>&1; then
  lean original_artifact/cone_scheme_attack/lean/POFreeLift.lean
else
  echo "SKIP: Lean executable not installed; claimed Lean 4.32.0 build not reproduced."
fi

echo "Audit checks completed with the documented scope."
