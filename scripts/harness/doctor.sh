#!/usr/bin/env bash

set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
MODE="strict"
COMPANION_LLZK_LEAN=""

EXPECTED_VEIR_HEAD="4b0978bddec0"
EXPECTED_LLZK_LEAN_HEAD="ea2363f87bcc"
EXPECTED_VEIR_DEP="09d5f00f0d2b4a8710afbe53dfdd7cf468578a04"
EXPECTED_VEIR_DEP_SHORT="09d5f00f0d2b"

FAIL=0
WARN=0

usage() {
  cat <<'USAGE'
usage: scripts/harness/doctor.sh [--mode strict|exploratory] [--companion-llzk-lean PATH]

Validates the Phase 0 VeIR harness. Strict companion checks fail on dirty or
mismatched llzk-lean .lake/packages/VeIR state. Exploratory mode reports the
same state but allows the command to complete successfully.
USAGE
}

ok() {
  echo "PASS: $*"
}

warn() {
  echo "WARN: $*" >&2
  WARN=$((WARN + 1))
}

fail() {
  echo "FAIL: $*" >&2
  FAIL=$((FAIL + 1))
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --mode)
      MODE="${2:-}"
      shift 2
      ;;
    --companion-llzk-lean)
      COMPANION_LLZK_LEAN="${2:-}"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      fail "unknown argument: $1"
      usage
      exit 2
      ;;
  esac
done

case "$MODE" in
  strict|exploratory) ;;
  *)
    fail "invalid mode: ${MODE}"
    exit 2
    ;;
esac

require_file() {
  local path="$1"
  if [[ -f "${ROOT}/${path}" ]]; then
    ok "found ${path}"
  else
    fail "missing ${path}"
  fi
}

require_executable() {
  local path="$1"
  if [[ -x "${ROOT}/${path}" ]]; then
    ok "executable ${path}"
  else
    fail "missing executable ${path}"
  fi
}

require_tool() {
  local tool="$1"
  if command -v "$tool" >/dev/null 2>&1; then
    ok "tool ${tool} is available"
  else
    fail "required tool ${tool} is not available"
  fi
}

optional_tool() {
  local tool="$1"
  if command -v "$tool" >/dev/null 2>&1; then
    ok "optional tool ${tool} is available"
  else
    warn "optional tool ${tool} is not available"
  fi
}

require_tool git
require_tool lake
optional_tool uv

git_root="$(git -C "$ROOT" rev-parse --show-toplevel 2>/dev/null || true)"
if [[ "$git_root" == "$ROOT" ]]; then
  ok "git root is ${ROOT}"
else
  fail "expected git root ${ROOT}, got ${git_root:-<none>}"
fi

head_short="$(git -C "$ROOT" rev-parse --short=12 HEAD 2>/dev/null || true)"
if [[ "$head_short" == "$EXPECTED_VEIR_HEAD" ]]; then
  ok "VeIR HEAD matches ${EXPECTED_VEIR_HEAD}"
else
  fail "VeIR HEAD ${head_short:-<none>} does not match bootstrap ${EXPECTED_VEIR_HEAD}"
fi

require_file AGENTS.md
require_file docs/phases/PHASE-00-harness-reset.md
require_file docs/phases/PHASE_TEMPLATE.md
require_file docs/harness/CURRENT.md
require_file docs/harness/SOURCES.md
require_file docs/harness/GATES.md
require_file docs/harness/REVIEWS.md
require_file reviews/PHASE-00/request.md
require_file reviews/PHASE-00/findings.md
require_file reviews/PHASE-00/disposition.md
require_file reviews/PHASE-00/adversarial-review.md
require_executable scripts/harness/check-doc-freshness.sh
require_executable scripts/harness/validate-skills.sh

if [[ -d "${ROOT}/reviews/PHASE-00/evidence" ]]; then
  ok "found reviews/PHASE-00/evidence"
else
  fail "missing reviews/PHASE-00/evidence"
fi

if [[ -n "$COMPANION_LLZK_LEAN" ]]; then
  companion="$(cd "$ROOT" && cd "$COMPANION_LLZK_LEAN" 2>/dev/null && pwd || true)"
  if [[ -z "$companion" ]]; then
    fail "companion llzk-lean path is not readable: ${COMPANION_LLZK_LEAN}"
  else
    ok "companion llzk-lean path is ${companion}"
    companion_head="$(git -C "$companion" rev-parse --short=12 HEAD 2>/dev/null || true)"
    if [[ "$companion_head" == "$EXPECTED_LLZK_LEAN_HEAD" ]]; then
      ok "llzk-lean HEAD matches ${EXPECTED_LLZK_LEAN_HEAD}"
    else
      fail "llzk-lean HEAD ${companion_head:-<none>} does not match bootstrap ${EXPECTED_LLZK_LEAN_HEAD}"
    fi

    if grep -q "$EXPECTED_VEIR_DEP" "${companion}/lakefile.toml" &&
       grep -q "$EXPECTED_VEIR_DEP" "${companion}/lake-manifest.json"; then
      ok "llzk-lean Lake files pin VeIR ${EXPECTED_VEIR_DEP_SHORT}"
    else
      fail "llzk-lean Lake files do not both pin VeIR ${EXPECTED_VEIR_DEP}"
    fi

    dep="${companion}/.lake/packages/VeIR"
    if [[ -d "$dep/.git" ]]; then
      dep_head="$(git -C "$dep" rev-parse --short=12 HEAD 2>/dev/null || true)"
      if [[ "$dep_head" == "$EXPECTED_VEIR_DEP_SHORT" ]]; then
        ok "llzk-lean dependency checkout is at ${EXPECTED_VEIR_DEP_SHORT}"
      else
        fail "llzk-lean dependency checkout ${dep_head:-<none>} does not match ${EXPECTED_VEIR_DEP_SHORT}"
      fi

      dep_status="$(git -C "$dep" status --short 2>/dev/null || true)"
      if [[ -z "$dep_status" ]]; then
        ok "llzk-lean dependency checkout is clean"
      elif [[ "$MODE" == "exploratory" ]]; then
        warn "llzk-lean dependency checkout is dirty in exploratory mode:"
        printf '%s\n' "$dep_status" >&2
      else
        fail "llzk-lean dependency checkout is dirty:"
        printf '%s\n' "$dep_status" >&2
      fi
    else
      fail "llzk-lean dependency checkout missing at ${dep}"
    fi
  fi
else
  warn "companion llzk-lean dependency was not checked; pass --companion-llzk-lean PATH"
fi

echo
echo "doctor summary: ${FAIL} fail, ${WARN} warn, mode=${MODE}"
if [[ "$FAIL" -ne 0 ]]; then
  exit 1
fi
exit 0
