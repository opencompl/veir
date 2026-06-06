#!/usr/bin/env bash

set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
FAIL=0
ACCEPTED_VEIR_COMMIT="d4cc1bf2d31beeca17eb2e8c9c7181d04af013a3"

fail() {
  echo "FAIL: $*" >&2
  FAIL=$((FAIL + 1))
}

ok() {
  echo "PASS: $*"
}

require_file() {
  local path="$1"
  if [[ -f "${ROOT}/${path}" ]]; then
    ok "found ${path}"
  else
    fail "missing ${path}"
  fi
}

require_nonempty() {
  local path="$1"
  if [[ -s "${ROOT}/${path}" ]]; then
    ok "evidence present ${path}"
  else
    fail "missing or empty evidence ${path}"
  fi
}

require_file docs/phases/PHASE-00-harness-reset.md
require_file docs/phases/PHASE-01-pins-and-repro.md
require_file docs/phases/PHASE-02-llzk-source-truth.md
require_file docs/phases/PHASE_TEMPLATE.md
require_file docs/harness/CURRENT.md
require_file docs/harness/SOURCES.md
require_file docs/harness/GATES.md
require_file docs/harness/LLZK_SOURCE.md
require_file docs/harness/PINS.md
require_file docs/harness/REVIEWS.md
require_file reviews/PHASE-01/disposition.md
require_file reviews/PHASE-01/findings.md
require_file reviews/PHASE-01/request.md
require_file reviews/PHASE-01/adversarial-review.md
require_file reviews/PHASE-02/disposition.md
require_file reviews/PHASE-02/findings.md
require_file reviews/PHASE-02/request.md
require_file reviews/PHASE-02/adversarial-review.md

phase_date="$(sed -n 's/^Last reviewed: //p' "${ROOT}/docs/phases/PHASE-02-llzk-source-truth.md" | head -1)"
if [[ "$phase_date" =~ ^[0-9]{4}-[0-9]{2}-[0-9]{2}$ ]]; then
  ok "phase review date has ISO format"
else
  fail "phase review date is missing or not ISO formatted"
fi

for doc in docs/harness/CURRENT.md docs/harness/SOURCES.md docs/harness/GATES.md docs/harness/LLZK_SOURCE.md docs/harness/PINS.md docs/harness/REVIEWS.md; do
  doc_date="$(sed -n 's/^Last reviewed: //p' "${ROOT}/${doc}" | head -1)"
  if [[ "$doc_date" == "$phase_date" ]]; then
    ok "${doc} review date agrees with phase"
  else
    fail "${doc} review date (${doc_date:-<none>}) does not match phase (${phase_date:-<none>})"
  fi
done

if grep -q "Active phase: Phase 2" "${ROOT}/docs/harness/CURRENT.md"; then
  ok "CURRENT names active phase"
else
  fail "CURRENT does not name Phase 2 as active"
fi

if grep -q "Accepted VeIR pin" "${ROOT}/docs/harness/SOURCES.md"; then
  ok "SOURCES records accepted VeIR pin"
else
  fail "SOURCES does not record accepted VeIR pin"
fi

if grep -q "Accepted LLZK source commit" "${ROOT}/docs/harness/SOURCES.md"; then
  ok "SOURCES records accepted LLZK source commit"
else
  fail "SOURCES does not record accepted LLZK source commit"
fi

if grep -q "$ACCEPTED_VEIR_COMMIT" "${ROOT}/docs/harness/PINS.md"; then
  ok "PINS records accepted VeIR commit"
else
  fail "PINS does not record accepted VeIR commit"
fi

if grep -q "Disposition" "${ROOT}/reviews/PHASE-02/disposition.md"; then
  ok "Phase 2 disposition exists"
else
  fail "Phase 2 disposition is not populated"
fi

for evidence in \
  reviews/PHASE-02/evidence/llzk-lib-refs.txt \
  reviews/PHASE-02/evidence/llzk-field-registry.txt \
  reviews/PHASE-02/evidence/llzk-felt-ops.txt \
  reviews/PHASE-02/evidence/verify-llzk-source-after.txt \
  reviews/PHASE-02/evidence/verify-companion-pin-after.txt \
  reviews/PHASE-02/evidence/lake-build-veir-after.txt \
  reviews/PHASE-02/evidence/adversarial-review.txt; do
  require_nonempty "$evidence"
done

echo
echo "doc freshness summary: ${FAIL} fail"
if [[ "$FAIL" -ne 0 ]]; then
  exit 1
fi
exit 0
