#!/usr/bin/env bash

set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
MODE="strict"
COMPANION_LLZK_LEAN=""

EXPECTED_VEIR_HEAD="a0bb2fc8e6d38ab068247dfc6506ba63f5feb953"
EXPECTED_VEIR_SHORT="${EXPECTED_VEIR_HEAD:0:12}"
EXPECTED_LLZK_LEAN_HEAD="617702beadfbad6be784945e2bd98e8a788d357c"
EXPECTED_LLZK_LEAN_SHORT="${EXPECTED_LLZK_LEAN_HEAD:0:12}"

FAIL=0
WARN=0

usage() {
  cat <<'USAGE'
usage: scripts/harness/doctor.sh [--mode strict|exploratory] [--companion-llzk-lean PATH]

Validates the current VeIR harness. Strict companion checks require llzk-lean
to pin the accepted VeIR commit in Lake metadata and a clean dependency
checkout.
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
if [[ "$head_short" == "$EXPECTED_VEIR_SHORT" ]]; then
  ok "VeIR HEAD matches bootstrap input ${EXPECTED_VEIR_SHORT}"
elif git -C "$ROOT" merge-base --is-ancestor "$EXPECTED_VEIR_HEAD" HEAD 2>/dev/null; then
  ok "VeIR HEAD ${head_short:-<none>} descends from bootstrap input ${EXPECTED_VEIR_SHORT}"
else
  warn "VeIR HEAD ${head_short:-<none>} differs from bootstrap input ${EXPECTED_VEIR_SHORT}"
fi

require_file AGENTS.md
require_file docs/phases/PHASE-00-harness-reset.md
require_file docs/phases/PHASE-01-pins-and-repro.md
require_file docs/phases/PHASE-02-llzk-source-truth.md
require_file docs/phases/PHASE-03-felt-op-gap-ledger.md
require_file docs/phases/PHASE-04-strategy-a-differential.md
require_file docs/phases/PHASE-05-strategy-a-pin-and-corpus.md
require_file docs/phases/PHASE-06-strategy-a-divergence-burndown.md
require_file docs/phases/PHASE_TEMPLATE.md
require_file docs/harness/CURRENT.md
require_file docs/harness/SOURCES.md
require_file docs/harness/GATES.md
require_file docs/harness/FELT_OP_GAPS.md
require_file docs/harness/LLZK_SOURCE.md
require_file docs/harness/PINS.md
require_file docs/harness/REVIEWS.md
require_file reviews/PHASE-00/request.md
require_file reviews/PHASE-00/findings.md
require_file reviews/PHASE-00/disposition.md
require_file reviews/PHASE-00/adversarial-review.md
require_file reviews/PHASE-01/request.md
require_file reviews/PHASE-01/findings.md
require_file reviews/PHASE-01/disposition.md
require_file reviews/PHASE-01/adversarial-review.md
require_file reviews/PHASE-02/request.md
require_file reviews/PHASE-02/findings.md
require_file reviews/PHASE-02/disposition.md
require_file reviews/PHASE-02/adversarial-review.md
require_file reviews/PHASE-03/request.md
require_file reviews/PHASE-03/findings.md
require_file reviews/PHASE-03/disposition.md
require_file reviews/PHASE-03/adversarial-review.md
require_file reviews/PHASE-04/request.md
require_file reviews/PHASE-04/findings.md
require_file reviews/PHASE-04/disposition.md
require_file reviews/PHASE-04/adversarial-review.md
require_file reviews/PHASE-05/request.md
require_file reviews/PHASE-05/findings.md
require_file reviews/PHASE-05/disposition.md
require_file reviews/PHASE-05/adversarial-review.md
require_file reviews/PHASE-06/request.md
require_file reviews/PHASE-06/findings.md
require_file reviews/PHASE-06/disposition.md
require_file reviews/PHASE-06/adversarial-review.md
require_executable scripts/harness/check-doc-freshness.sh
require_executable scripts/harness/verify-companion-pin.sh
require_executable scripts/harness/verify-llzk-source.sh
require_executable scripts/harness/validate-skills.sh

if [[ -d "${ROOT}/reviews/PHASE-00/evidence" ]]; then
  ok "found reviews/PHASE-00/evidence"
else
  fail "missing reviews/PHASE-00/evidence"
fi

if [[ -d "${ROOT}/reviews/PHASE-01/evidence" ]]; then
  ok "found reviews/PHASE-01/evidence"
else
  fail "missing reviews/PHASE-01/evidence"
fi

if [[ -d "${ROOT}/reviews/PHASE-02/evidence" ]]; then
  ok "found reviews/PHASE-02/evidence"
else
  fail "missing reviews/PHASE-02/evidence"
fi

if [[ -d "${ROOT}/reviews/PHASE-03/evidence" ]]; then
  ok "found reviews/PHASE-03/evidence"
else
  fail "missing reviews/PHASE-03/evidence"
fi

if [[ -d "${ROOT}/reviews/PHASE-04/evidence" ]]; then
  ok "found reviews/PHASE-04/evidence"
else
  fail "missing reviews/PHASE-04/evidence"
fi

if [[ -d "${ROOT}/reviews/PHASE-05/evidence" ]]; then
  ok "found reviews/PHASE-05/evidence"
else
  fail "missing reviews/PHASE-05/evidence"
fi

if [[ -d "${ROOT}/reviews/PHASE-06/evidence" ]]; then
  ok "found reviews/PHASE-06/evidence"
else
  fail "missing reviews/PHASE-06/evidence"
fi

if [[ -n "$COMPANION_LLZK_LEAN" ]]; then
  companion="$(cd "$ROOT" && cd "$COMPANION_LLZK_LEAN" 2>/dev/null && pwd || true)"
  if [[ -z "$companion" ]]; then
    fail "companion llzk-lean path is not readable: ${COMPANION_LLZK_LEAN}"
  else
    ok "companion llzk-lean path is ${companion}"
    companion_head="$(git -C "$companion" rev-parse --short=12 HEAD 2>/dev/null || true)"
    if [[ "$companion_head" == "$EXPECTED_LLZK_LEAN_SHORT" ]]; then
      ok "llzk-lean HEAD matches bootstrap input ${EXPECTED_LLZK_LEAN_SHORT}"
    elif git -C "$companion" merge-base --is-ancestor "$EXPECTED_LLZK_LEAN_HEAD" HEAD 2>/dev/null; then
      ok "llzk-lean HEAD ${companion_head:-<none>} descends from bootstrap input ${EXPECTED_LLZK_LEAN_SHORT}"
    else
      warn "llzk-lean HEAD ${companion_head:-<none>} differs from bootstrap input ${EXPECTED_LLZK_LEAN_SHORT}"
    fi
    if "${ROOT}/scripts/harness/verify-companion-pin.sh" --mode "$MODE" --companion-llzk-lean "$companion"; then
      ok "companion pin verification passed"
    else
      fail "companion pin verification failed"
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
