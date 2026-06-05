#!/usr/bin/env bash

set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
FAIL=0

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

require_file docs/phases/PHASE-00-harness-reset.md
require_file docs/phases/PHASE_TEMPLATE.md
require_file docs/harness/CURRENT.md
require_file docs/harness/SOURCES.md
require_file docs/harness/GATES.md
require_file docs/harness/REVIEWS.md
require_file reviews/PHASE-00/disposition.md
require_file reviews/PHASE-00/findings.md
require_file reviews/PHASE-00/request.md
require_file reviews/PHASE-00/adversarial-review.md

phase_date="$(sed -n 's/^Last reviewed: //p' "${ROOT}/docs/phases/PHASE-00-harness-reset.md" | head -1)"
if [[ "$phase_date" =~ ^[0-9]{4}-[0-9]{2}-[0-9]{2}$ ]]; then
  ok "phase review date has ISO format"
else
  fail "phase review date is missing or not ISO formatted"
fi

for doc in docs/harness/CURRENT.md docs/harness/SOURCES.md docs/harness/GATES.md docs/harness/REVIEWS.md; do
  doc_date="$(sed -n 's/^Last reviewed: //p' "${ROOT}/${doc}" | head -1)"
  if [[ "$doc_date" == "$phase_date" ]]; then
    ok "${doc} review date agrees with phase"
  else
    fail "${doc} review date (${doc_date:-<none>}) does not match phase (${phase_date:-<none>})"
  fi
done

if grep -q "Active phase: Phase 0" "${ROOT}/docs/harness/CURRENT.md"; then
  ok "CURRENT names active phase"
else
  fail "CURRENT does not name Phase 0 as active"
fi

if grep -q "Stale Historical Material" "${ROOT}/docs/harness/SOURCES.md"; then
  ok "SOURCES marks stale historical material"
else
  fail "SOURCES does not mark stale historical material"
fi

if grep -q "Disposition" "${ROOT}/reviews/PHASE-00/disposition.md"; then
  ok "Phase 0 disposition exists"
else
  fail "Phase 0 disposition is not populated"
fi

for evidence in \
  reviews/PHASE-00/evidence/doctor-local.txt \
  reviews/PHASE-00/evidence/doctor-companion-strict.txt \
  reviews/PHASE-00/evidence/doctor-companion-exploratory.txt \
  reviews/PHASE-00/evidence/validate-skills.txt \
  reviews/PHASE-00/evidence/adversarial-review.txt; do
  if [[ -s "${ROOT}/${evidence}" ]]; then
    ok "evidence present ${evidence}"
  else
    fail "missing or empty evidence ${evidence}"
  fi
done

echo
echo "doc freshness summary: ${FAIL} fail"
if [[ "$FAIL" -ne 0 ]]; then
  exit 1
fi
exit 0
