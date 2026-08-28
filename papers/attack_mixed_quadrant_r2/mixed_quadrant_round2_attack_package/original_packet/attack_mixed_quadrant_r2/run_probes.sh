#!/bin/sh
# Self-contained: pure Python 3, no dependencies.  Both probes re-derive the RCC5
# composition table from finite set semantics.
#
# wp132 packages round 1's eight-point counterexample as a REGRESSION -- if we
# have mis-transcribed your model, its PART R will say so immediately.
set -e
cd "$(dirname "$0")/probes"
for f in wp131*.py wp132*.py; do
  [ -f "$f" ] || continue
  echo "=================================================================="
  echo "== $f"
  echo "=================================================================="
  python3 "$f" || echo "(non-zero exit -- read the probe's own verdict line)"
  echo
done
