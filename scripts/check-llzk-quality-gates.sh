#!/usr/bin/env bash
# Compatibility wrapper for the current harness gates.
#
# The pre-Phase-0 version of this script read deleted harness files and could
# emit misleading status. The canonical gate inventory now lives in
# docs/harness/GATES.md.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

DOCTOR_ARGS=()
if [[ "${VEIR_HARNESS_LOCAL_ONLY:-0}" == "1" ]]; then
  :
elif [[ -n "${LLZK_LEAN_ROOT:-}" ]]; then
  DOCTOR_ARGS=(--companion-llzk-lean "$LLZK_LEAN_ROOT")
elif [[ -d "${ROOT}/../llzk-lean" ]]; then
  DOCTOR_ARGS=(--companion-llzk-lean "${ROOT}/../llzk-lean")
else
  echo "FAIL: companion llzk-lean dependency gate was not run." >&2
  echo "Set LLZK_LEAN_ROOT, place llzk-lean at ../llzk-lean, or set" >&2
  echo "VEIR_HARNESS_LOCAL_ONLY=1 for a non-acceptance local layout check." >&2
  exit 1
fi

scripts/harness/doctor.sh "${DOCTOR_ARGS[@]}"
scripts/harness/verify-llzk-source.sh --llzk-lib ../llzk-lib
VEIR_QUALITY_GATES_RUNNING=1 scripts/harness/check-doc-freshness.sh
scripts/harness/validate-skills.sh

if [[ "${VEIR_HARNESS_LOCAL_ONLY:-0}" == "1" ]]; then
  echo "WARN: companion llzk-lean dependency gate explicitly skipped via VEIR_HARNESS_LOCAL_ONLY=1."
  echo "WARN: this is a local layout check, not Phase 6 acceptance evidence."
fi

echo
echo "Phase 6 harness gates completed."
