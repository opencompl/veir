#!/usr/bin/env bash
# Compatibility wrapper for the Phase 1 harness gates.
#
# The pre-Phase-0 version of this script read deleted harness files and could
# emit misleading status. The canonical gate inventory now lives in
# docs/harness/GATES.md.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

scripts/harness/doctor.sh
scripts/harness/verify-llzk-source.sh --llzk-lib ../llzk-lib
scripts/harness/check-doc-freshness.sh
scripts/harness/validate-skills.sh

if [[ "${VEIR_HARNESS_LOCAL_ONLY:-0}" == "1" ]]; then
  echo "WARN: companion llzk-lean dependency gate explicitly skipped via VEIR_HARNESS_LOCAL_ONLY=1."
  echo "WARN: this is a local layout check, not Phase 1 acceptance evidence."
elif [[ -n "${LLZK_LEAN_ROOT:-}" ]]; then
  scripts/harness/doctor.sh --companion-llzk-lean "$LLZK_LEAN_ROOT"
elif [[ -d "${ROOT}/../llzk-lean" ]]; then
  scripts/harness/doctor.sh --companion-llzk-lean "${ROOT}/../llzk-lean"
else
  echo "FAIL: companion llzk-lean dependency gate was not run." >&2
  echo "Set LLZK_LEAN_ROOT, place llzk-lean at ../llzk-lean, or set" >&2
  echo "VEIR_HARNESS_LOCAL_ONLY=1 for a non-acceptance local layout check." >&2
  exit 1
fi

echo
echo "Phase 2 harness gates completed."
