#!/usr/bin/env bash
#
# Check that veir-opt and mlir-opt reach the same accept/reject verdict on a
# single test file. Used by the `VEIR_MLIR_SAME_VERDICT` lit substitution (see Test/lit.cfg).
#
# Usage: veir_mlir_same_verdict.sh <veir-opt> <mlir-opt> <test-file>
#
# Exits 0 iff both tools verify the input (both accept) or both reject it (parse
# or verification failure). Only the verdict is compared, not the diagnostic
# text, which is not stable across mlir-opt versions.
#
# veir-opt natively accepts unregistered ops such as `test.test`; mlir-opt needs
# `--allow-unregistered-dialect` to do the same, so the two invocations differ
# only by that flag.

set -u

if [ "$#" -ne 3 ]; then
  echo "veir_mlir_same_verdict.sh: expected 3 arguments, got $#" >&2
  exit 2
fi

veir="$1"
mlir="$2"
file="$3"

"$veir" "$file" >/dev/null 2>&1
[ $? -eq 0 ] && veir_verdict=accept || veir_verdict=reject

"$mlir" --allow-unregistered-dialect "$file" >/dev/null 2>&1
[ $? -eq 0 ] && mlir_verdict=accept || mlir_verdict=reject

if [ "$veir_verdict" = "$mlir_verdict" ]; then
  echo "VEIR_MLIR_SAME_VERDICT: veir-opt and mlir-opt agree ($veir_verdict) on $file"
  exit 0
fi

echo "VEIR_MLIR_SAME_VERDICT: DISAGREEMENT on $file: veir-opt=$veir_verdict mlir-opt=$mlir_verdict" >&2
exit 1
