#!/usr/bin/env bash

set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
FAIL=0
COUNT=0

fail() {
  echo "FAIL: $*" >&2
  FAIL=$((FAIL + 1))
}

ok() {
  echo "PASS: $*"
}

if [[ ! -d "${ROOT}/skills" ]]; then
  fail "missing skills directory"
else
  while IFS= read -r skill; do
    COUNT=$((COUNT + 1))
    rel="${skill#${ROOT}/}"
    if grep -q '^# ' "$skill"; then
      ok "${rel} has title"
    else
      fail "${rel} is missing title"
    fi
    if grep -q '^## When to use' "$skill"; then
      ok "${rel} has usage trigger"
    else
      fail "${rel} is missing 'When to use'"
    fi
    if grep -q '^## Validation' "$skill"; then
      ok "${rel} has validation path"
    else
      fail "${rel} is missing 'Validation'"
    fi
    if grep -q 'scripts/harness/' "$skill"; then
      ok "${rel} points at harness scripts"
    else
      fail "${rel} does not point at a harness script"
    fi
  done < <(find "${ROOT}/skills" -mindepth 2 -maxdepth 2 -name SKILL.md | sort)
fi

if [[ "$COUNT" -eq 0 ]]; then
  fail "no repo-local skills found"
fi

echo
echo "skill validation summary: ${FAIL} fail over ${COUNT} skills"
if [[ "$FAIL" -ne 0 ]]; then
  exit 1
fi
exit 0
