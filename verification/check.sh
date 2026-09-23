#!/bin/sh
# Re-checks everything under verification/: the Lean proofs, that the
# conformance vectors are those the Lean mirrors generate, and the TLA+ models.
# The vectors themselves are replayed against lib/hpke.ml by `dune runtest`.
#
# Needs elan (Lean 4.34.0), a JDK, and tla2tools.jar. tla/check.sh reads JAVA
# and TLA2TOOLS to override its defaults.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
metadir=$(mktemp -d)
trap 'rm -rf "$metadir"' EXIT

echo "== Lean"
cd "$here/lean"
lake build
if grep -rn --include='*.lean' -E '\bsorry\b|\badmit\b|^axiom ' HpkeSpec HpkeSpec.lean; then
  echo "unproved statements found" >&2
  exit 1
fi

echo "== Conformance vectors"
lake env lean --run Conformance.lean > "$metadir/vectors.txt"
cmp "$metadir/vectors.txt" "$here/conformance/vectors.txt" || {
  echo "conformance/vectors.txt is stale: regenerate it with" >&2
  echo "  (cd verification/lean && lake env lean --run Conformance.lean > ../conformance/vectors.txt)" >&2
  exit 1
}

echo "== TLA+"
TLC_METADIR="$metadir" "$here/tla/check.sh"
