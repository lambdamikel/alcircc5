#!/bin/sh
# Self-contained: pure Python 3, no dependencies.  Each probe re-derives the
# RCC5 composition table from finite set semantics, so nothing is taken on trust.
set -e
cd "$(dirname "$0")/probes"
for f in wp47*.py wp93*.py wp94*.py wp131*.py; do
  [ -f "$f" ] || continue
  echo "=================================================================="
  echo "== $f"
  echo "=================================================================="
  python3 "$f" || echo "(non-zero exit -- see the probe's own verdict line)"
  echo
done
