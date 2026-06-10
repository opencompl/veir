#!/usr/bin/env bash

set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
FAIL=0
ACCEPTED_VEIR_COMMIT="220cd215579b435c3c22ce86b34a3f4ce2ca276e"
ACCEPTED_LLZK_REMOTE="git@github.com:project-llzk/llzk-lib.git"

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

require_contains() {
  local path="$1"
  local needle="$2"
  local description="$3"
  if grep -Fq -- "$needle" "${ROOT}/${path}"; then
    ok "$description"
  else
    fail "${description}: ${path} does not contain ${needle}"
  fi
}

require_not_contains() {
  local path="$1"
  local needle="$2"
  local description="$3"
  if grep -Fq -- "$needle" "${ROOT}/${path}"; then
    fail "${description}: ${path} still contains ${needle}"
  else
    ok "$description"
  fi
}

require_op_once() {
  local mnemonic="$1"
  local count
  count="$(grep -Fc -- "| \`${mnemonic}\` |" "${ROOT}/docs/harness/FELT_OP_GAPS.md")"
  if [[ "$count" == "1" ]]; then
    ok "FELT_OP_GAPS records ${mnemonic} exactly once"
  else
    fail "FELT_OP_GAPS records ${mnemonic} ${count} times"
  fi
}

require_op_row_contains() {
  local mnemonic="$1"
  local needle="$2"
  local description="$3"
  local row
  row="$(grep -F -- "| \`${mnemonic}\` |" "${ROOT}/docs/harness/FELT_OP_GAPS.md")"
  if [[ "$row" == *"$needle"* ]]; then
    ok "$description"
  else
    fail "${description}: ${mnemonic} row does not contain ${needle}"
  fi
}

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
require_file reviews/PHASE-01/disposition.md
require_file reviews/PHASE-01/findings.md
require_file reviews/PHASE-01/request.md
require_file reviews/PHASE-01/adversarial-review.md
require_file reviews/PHASE-02/disposition.md
require_file reviews/PHASE-02/findings.md
require_file reviews/PHASE-02/request.md
require_file reviews/PHASE-02/adversarial-review.md
require_file reviews/PHASE-03/disposition.md
require_file reviews/PHASE-03/findings.md
require_file reviews/PHASE-03/request.md
require_file reviews/PHASE-03/adversarial-review.md
require_file reviews/PHASE-03/evidence/README.md
require_file reviews/PHASE-04/disposition.md
require_file reviews/PHASE-04/findings.md
require_file reviews/PHASE-04/request.md
require_file reviews/PHASE-04/adversarial-review.md
require_file reviews/PHASE-04/evidence/README.md
require_file reviews/PHASE-05/disposition.md
require_file reviews/PHASE-05/findings.md
require_file reviews/PHASE-05/request.md
require_file reviews/PHASE-05/adversarial-review.md
require_file reviews/PHASE-05/evidence/README.md
require_file reviews/PHASE-06/disposition.md
require_file reviews/PHASE-06/findings.md
require_file reviews/PHASE-06/request.md
require_file reviews/PHASE-06/adversarial-review.md
require_file reviews/PHASE-06/evidence/README.md

phase_date="$(sed -n 's/^Last reviewed: //p' "${ROOT}/docs/phases/PHASE-06-strategy-a-divergence-burndown.md" | head -1)"
if [[ "$phase_date" =~ ^[0-9]{4}-[0-9]{2}-[0-9]{2}$ ]]; then
  ok "phase review date has ISO format"
else
  fail "phase review date is missing or not ISO formatted"
fi

for doc in docs/harness/CURRENT.md docs/harness/SOURCES.md docs/harness/GATES.md docs/harness/FELT_OP_GAPS.md docs/harness/LLZK_SOURCE.md docs/harness/PINS.md docs/harness/REVIEWS.md; do
  doc_date="$(sed -n 's/^Last reviewed: //p' "${ROOT}/${doc}" | head -1)"
  if [[ "$doc_date" == "$phase_date" ]]; then
    ok "${doc} review date agrees with phase"
  else
    fail "${doc} review date (${doc_date:-<none>}) does not match phase (${phase_date:-<none>})"
  fi
done

if grep -q "Active phase: Phase 6" "${ROOT}/docs/harness/CURRENT.md"; then
  ok "CURRENT names active phase"
else
  fail "CURRENT does not name Phase 6 as active"
fi

require_contains docs/phases/PHASE-05-strategy-a-pin-and-corpus.md "Status: completed; superseded by Phase 6" "Phase 5 phase file is marked completed"

require_not_contains docs/harness/CURRENT.md "corpus expansion beyond the seed set remains the next" "CURRENT no longer says corpus expansion is future work"
require_not_contains docs/harness/CURRENT.md "starts moving corpus evidence" "CURRENT no longer says clean-pin corpus migration is only starting"
require_not_contains docs/harness/CURRENT.md "seed canonical corpus must keep running" "CURRENT no longer describes the canonical corpus as seed-only"

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

if grep -q "docs/harness/FELT_OP_GAPS.md" "${ROOT}/docs/harness/SOURCES.md"; then
  ok "SOURCES records Felt operation gap ledger"
else
  fail "SOURCES does not record docs/harness/FELT_OP_GAPS.md"
fi

if grep -q "docs/phases/PHASE-04-strategy-a-differential.md" "${ROOT}/docs/harness/SOURCES.md"; then
  ok "SOURCES records Phase 4 phase file"
else
  fail "SOURCES does not record docs/phases/PHASE-04-strategy-a-differential.md"
fi

if grep -q "docs/phases/PHASE-05-strategy-a-pin-and-corpus.md" "${ROOT}/docs/harness/SOURCES.md"; then
  ok "SOURCES records Phase 5 phase file"
else
  fail "SOURCES does not record docs/phases/PHASE-05-strategy-a-pin-and-corpus.md"
fi

if grep -q "docs/phases/PHASE-06-strategy-a-divergence-burndown.md" "${ROOT}/docs/harness/SOURCES.md"; then
  ok "SOURCES records Phase 6 phase file"
else
  fail "SOURCES does not record docs/phases/PHASE-06-strategy-a-divergence-burndown.md"
fi

if grep -q "reviews/PHASE-04/evidence/differential-canonicalize.txt" "${ROOT}/docs/harness/SOURCES.md" &&
   grep -q "reviews/PHASE-04/evidence/adversarial-review-fresh.txt" "${ROOT}/docs/harness/SOURCES.md"; then
  ok "SOURCES records Phase 4 implementation and fresh review evidence"
else
  fail "SOURCES does not record Phase 4 implementation and fresh review evidence"
fi

if grep -q "scripts/llzk-diff.sh" "${ROOT}/docs/harness/SOURCES.md"; then
  ok "SOURCES records VeIR differential script"
else
  fail "SOURCES does not record scripts/llzk-diff.sh"
fi

if grep -Fq -- "/nix/store/awcw2wiypa02sl5vx4xm06qwji68xz3h-llzk-debug-2.0.0/bin/llzk-opt" "${ROOT}/docs/harness/SOURCES.md"; then
  ok "SOURCES records accepted local llzk-opt binary"
else
  fail "SOURCES does not record accepted local llzk-opt binary"
fi

if grep -Fq -- "/home/alh/llvm-project" "${ROOT}/docs/harness/SOURCES.md" &&
   grep -Fq -- "49f12af164138123589263fe75ea5f1d356e8780" "${ROOT}/docs/harness/SOURCES.md"; then
  ok "SOURCES records local llvm-project test infrastructure"
else
  fail "SOURCES does not record local llvm-project test infrastructure"
fi

if grep -Fq -- "$ACCEPTED_LLZK_REMOTE" "${ROOT}/docs/harness/SOURCES.md" &&
   grep -Fq -- "$ACCEPTED_LLZK_REMOTE" "${ROOT}/docs/harness/LLZK_SOURCE.md"; then
  ok "SOURCES and LLZK_SOURCE record accepted LLZK remote"
else
  fail "SOURCES or LLZK_SOURCE does not record accepted LLZK remote ${ACCEPTED_LLZK_REMOTE}"
fi

if grep -q "$ACCEPTED_VEIR_COMMIT" "${ROOT}/docs/harness/PINS.md"; then
  ok "PINS records accepted VeIR commit"
else
  fail "PINS does not record accepted VeIR commit"
fi

op_rows="$(grep -Ec '^\| `[^`]+` \|' "${ROOT}/docs/harness/FELT_OP_GAPS.md")"
if [[ "$op_rows" == "18" ]]; then
  ok "FELT_OP_GAPS has exactly 18 operation rows"
else
  fail "FELT_OP_GAPS has ${op_rows} operation rows, expected 18"
fi

for mnemonic in \
  const add sub mul pow div uintdiv sintdiv umod smod neg inv \
  bit_and bit_or bit_xor bit_not shl shr; do
  require_op_once "$mnemonic"
done

for mnemonic in pow div uintdiv sintdiv umod smod inv bit_and bit_or bit_xor bit_not shl shr; do
  require_op_row_contains "$mnemonic" 'Missing from `Data.Felt` and `InterpModel`' "FELT_OP_GAPS marks ${mnemonic} semantic model missing"
  require_op_row_contains "$mnemonic" "| Gap |" "FELT_OP_GAPS marks ${mnemonic} as a gap"
done

if grep -q "Disposition" "${ROOT}/reviews/PHASE-02/disposition.md"; then
  ok "Phase 2 disposition exists"
else
  fail "Phase 2 disposition is not populated"
fi

if grep -q "# Phase 3 Disposition" "${ROOT}/reviews/PHASE-03/disposition.md"; then
  ok "Phase 3 disposition exists"
else
  fail "Phase 3 disposition is not populated"
fi

if grep -q "# Phase 4 Disposition" "${ROOT}/reviews/PHASE-04/disposition.md"; then
  ok "Phase 4 disposition exists"
else
  fail "Phase 4 disposition is not populated"
fi

if grep -q "# Phase 5 Disposition" "${ROOT}/reviews/PHASE-05/disposition.md"; then
  ok "Phase 5 disposition exists"
else
  fail "Phase 5 disposition is not populated"
fi

if grep -q "# Phase 6 Disposition" "${ROOT}/reviews/PHASE-06/disposition.md"; then
  ok "Phase 6 disposition exists"
else
  fail "Phase 6 disposition is not populated"
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

for evidence in \
  reviews/PHASE-03/evidence/README.md \
  reviews/PHASE-03/evidence/check-doc-freshness.txt \
  reviews/PHASE-03/evidence/verify-llzk-source.txt \
  reviews/PHASE-03/evidence/verify-companion-pin.txt \
  reviews/PHASE-03/evidence/doctor-companion.txt \
  reviews/PHASE-03/evidence/quality-gates.txt \
  reviews/PHASE-03/evidence/validate-skills.txt \
  reviews/PHASE-03/evidence/lake-build.txt \
  reviews/PHASE-03/evidence/adversarial-review.txt; do
  require_nonempty "$evidence"
done

for evidence in \
  reviews/PHASE-04/evidence/README.md \
  reviews/PHASE-04/evidence/check-doc-freshness.txt \
  reviews/PHASE-04/evidence/verify-llzk-source.txt \
  reviews/PHASE-04/evidence/verify-companion-pin.txt \
  reviews/PHASE-04/evidence/doctor-companion.txt \
  reviews/PHASE-04/evidence/quality-gates.txt \
  reviews/PHASE-04/evidence/validate-skills.txt \
  reviews/PHASE-04/evidence/lake-build.txt \
  reviews/PHASE-04/evidence/adversarial-review.txt \
  reviews/PHASE-04/evidence/adversarial-review-fresh.txt \
  reviews/PHASE-04/evidence/differential-bootstrap.txt \
  reviews/PHASE-04/evidence/differential-canonicalize.txt \
  reviews/PHASE-04/evidence/corpus-classification.txt; do
  require_nonempty "$evidence"
done

for evidence in \
  reviews/PHASE-05/evidence/README.md \
  reviews/PHASE-05/evidence/check-doc-freshness.txt \
  reviews/PHASE-05/evidence/verify-llzk-source.txt \
  reviews/PHASE-05/evidence/verify-companion-pin.txt \
  reviews/PHASE-05/evidence/doctor-companion.txt \
  reviews/PHASE-05/evidence/quality-gates.txt \
  reviews/PHASE-05/evidence/validate-skills.txt \
  reviews/PHASE-05/evidence/lake-build.txt \
  reviews/PHASE-05/evidence/polarity-guard.txt \
  reviews/PHASE-05/evidence/differential-clean-pin-canonicalize.txt \
  reviews/PHASE-05/evidence/adversarial-review.txt; do
  require_nonempty "$evidence"
done

for evidence in \
  reviews/PHASE-06/evidence/README.md \
  reviews/PHASE-06/evidence/check-doc-freshness.txt \
  reviews/PHASE-06/evidence/verify-llzk-source.txt \
  reviews/PHASE-06/evidence/verify-companion-pin.txt \
  reviews/PHASE-06/evidence/doctor-companion.txt \
  reviews/PHASE-06/evidence/quality-gates.txt \
  reviews/PHASE-06/evidence/validate-skills.txt \
  reviews/PHASE-06/evidence/lake-build.txt \
  reviews/PHASE-06/evidence/differential-clean-pin-canonicalize.txt \
  reviews/PHASE-06/evidence/adversarial-review.txt; do
  require_nonempty "$evidence"
done

require_contains reviews/PHASE-03/evidence/verify-llzk-source.txt "LLZK source verification summary: 0 fail" "verify-llzk-source evidence reports no failures"
require_contains reviews/PHASE-03/evidence/verify-companion-pin.txt "companion pin verification summary: 0 fail" "companion pin evidence reports no failures"
require_contains reviews/PHASE-03/evidence/doctor-companion.txt "doctor summary: 0 fail" "companion doctor evidence reports no failures"
if [[ "${VEIR_QUALITY_GATES_RUNNING:-0}" == "1" ]]; then
  ok "quality-gates evidence marker validation deferred while wrapper is running"
else
  require_contains reviews/PHASE-03/evidence/quality-gates.txt "Phase 3 harness gates completed." "quality-gates evidence records wrapper completion"
  require_contains reviews/PHASE-03/evidence/quality-gates.txt "doctor summary: 0 fail, 0 warn, mode=strict" "quality-gates evidence includes strict companion doctor success"
fi
require_contains reviews/PHASE-03/evidence/validate-skills.txt "skill validation summary: 0 fail" "skill evidence reports no failures"
require_contains reviews/PHASE-03/evidence/lake-build.txt "Build completed successfully" "lake build evidence reports success"
require_contains reviews/PHASE-03/evidence/adversarial-review.txt "PASS: no missing-op semantic definitions found in VeIR Felt semantics" "adversarial evidence confirms missing-op semantics were not added"
require_contains reviews/PHASE-03/evidence/adversarial-review.txt "PASS: no modified, staged, or untracked files under Veir/" "adversarial evidence confirms no VeIR source changes"
require_contains reviews/PHASE-04/evidence/verify-llzk-source.txt "LLZK source verification summary: 0 fail" "Phase 4 source evidence reports no failures"
require_contains reviews/PHASE-04/evidence/verify-companion-pin.txt "companion pin verification summary: 0 fail" "Phase 4 companion pin evidence reports no failures"
require_contains reviews/PHASE-04/evidence/doctor-companion.txt "doctor summary: 0 fail" "Phase 4 companion doctor evidence reports no failures"
if [[ "${VEIR_QUALITY_GATES_RUNNING:-0}" == "1" ]]; then
  ok "Phase 4 quality-gates evidence marker validation deferred while wrapper is running"
else
  require_contains reviews/PHASE-04/evidence/quality-gates.txt "Phase 4 harness gates completed." "Phase 4 quality-gates evidence records wrapper completion"
  require_contains reviews/PHASE-04/evidence/quality-gates.txt "doctor summary: 0 fail, 0 warn, mode=strict" "Phase 4 quality-gates evidence includes strict companion doctor success"
fi
require_contains reviews/PHASE-04/evidence/validate-skills.txt "skill validation summary: 0 fail" "Phase 4 skill evidence reports no failures"
require_contains reviews/PHASE-04/evidence/lake-build.txt "Build completed successfully" "Phase 4 lake build evidence reports success"
require_contains reviews/PHASE-04/evidence/adversarial-review.txt "PASS: llzk-opt binary is executable" "Phase 4 adversarial evidence confirms llzk-opt is executable"
require_contains reviews/PHASE-04/evidence/adversarial-review.txt "PASS: canonicalization-aware diff-script implementation is dispositioned under reviews/PHASE-04" "Phase 4 adversarial evidence dispositions the diff-script implementation"
require_contains reviews/PHASE-04/evidence/differential-bootstrap.txt "VEIR_DIFF=/home/alh/LLZK/veir/scripts/llzk-diff.sh" "Phase 4 parse/print differential evidence records workspace VeIR script"
require_contains reviews/PHASE-04/evidence/differential-bootstrap.txt "Summary: 4 pass (incl. expected-diverge), 0 fail, 0 skip, 3 mode-skip" "Phase 4 parse/print differential evidence reports no failures"
require_contains reviews/PHASE-04/evidence/differential-canonicalize.txt "LLZK_OPT=/nix/store/awcw2wiypa02sl5vx4xm06qwji68xz3h-llzk-debug-2.0.0/bin/llzk-opt" "Phase 4 canonical differential evidence records accepted llzk-opt"
require_contains reviews/PHASE-04/evidence/differential-canonicalize.txt "--canonicalize differential/corpus" "Phase 4 canonical differential evidence records canonicalization command"
require_contains reviews/PHASE-04/evidence/differential-canonicalize.txt "Summary: 7 pass (incl. expected-diverge), 0 fail" "Phase 4 canonical differential evidence reports no failures"
require_contains reviews/PHASE-04/evidence/corpus-classification.txt "differential/corpus/expected-divergence/canonical/registered_add_wrap.llzk" "Phase 4 corpus evidence records canonical expected-divergence cases"
require_contains reviews/PHASE-04/evidence/adversarial-review-fresh.txt "PASS: companion llzk-lean canonical run without VEIR_DIFF now exits early with an actionable clean-pin/override message." "Phase 4 fresh adversarial evidence records clean-pin guard"
require_contains reviews/PHASE-05/evidence/verify-llzk-source.txt "LLZK source verification summary: 0 fail" "Phase 5 source evidence reports no failures"
require_contains reviews/PHASE-05/evidence/verify-llzk-source.txt "WARN: llzk-lib worktree HEAD" "Phase 5 source evidence captures known stale llzk-lib warning detail"
require_contains reviews/PHASE-05/evidence/verify-companion-pin.txt "companion pin verification summary: 0 fail" "Phase 5 companion pin evidence reports no failures"
require_contains reviews/PHASE-05/evidence/doctor-companion.txt "doctor summary: 0 fail" "Phase 5 companion doctor evidence reports no failures"
if [[ "${VEIR_QUALITY_GATES_RUNNING:-0}" == "1" ]]; then
  ok "Phase 5 quality-gates evidence marker validation deferred while wrapper is running"
else
  require_contains reviews/PHASE-05/evidence/quality-gates.txt "Phase 5 harness gates completed." "Phase 5 quality-gates evidence records wrapper completion"
fi
require_contains reviews/PHASE-05/evidence/validate-skills.txt "skill validation summary: 0 fail" "Phase 5 skill evidence reports no failures"
require_contains reviews/PHASE-05/evidence/lake-build.txt "Build completed successfully" "Phase 5 lake build evidence reports success"
require_contains reviews/PHASE-05/evidence/polarity-guard.txt "LLZK-FAIL: /home/alh/LLZK/llzk-lean/differential/corpus/expected-divergence/canonical/registered_add_fold.llzk" "Phase 5 polarity guard rejects wrong expected-divergence failure mode"
require_contains reviews/PHASE-05/evidence/polarity-guard.txt "exit code: 1" "Phase 5 polarity guard records nonzero exit"
require_contains reviews/PHASE-05/evidence/differential-clean-pin-canonicalize.txt "./differential/run-differential.sh --canonicalize differential/corpus" "Phase 5 clean-pin canonical evidence records default dependency command"
require_contains reviews/PHASE-05/evidence/differential-clean-pin-canonicalize.txt "differential/corpus/felt/add_const_swap.llzk" "Phase 5 clean-pin canonical evidence records expanded positive corpus"
require_contains reviews/PHASE-05/evidence/differential-clean-pin-canonicalize.txt "differential/corpus/expected-divergence/canonical/assoc_const_fold_mul.llzk" "Phase 5 clean-pin canonical evidence records expanded expected-divergence corpus"
require_contains reviews/PHASE-05/evidence/differential-clean-pin-canonicalize.txt "Summary: 21 pass (incl. expected-diverge), 0 fail" "Phase 5 clean-pin canonical evidence reports no failures"
require_contains reviews/PHASE-05/evidence/adversarial-review.txt "PASS: companion expected-divergence polarity is marker-specific" "Phase 5 adversarial evidence records exact polarity guard"
require_contains reviews/PHASE-05/evidence/adversarial-review.txt "PASS: companion differential wrapper rejects missing-tool SKIP runs as non-acceptance evidence." "Phase 5 adversarial evidence records companion skip guard"
require_contains reviews/PHASE-05/evidence/adversarial-review.txt "PASS: no Phase 5 findings remain open." "Phase 5 adversarial evidence reports no open findings"
require_contains reviews/PHASE-06/evidence/verify-llzk-source.txt "LLZK source verification summary: 0 fail" "Phase 6 source evidence reports no failures"
require_contains reviews/PHASE-06/evidence/verify-companion-pin.txt "companion pin verification summary: 0 fail" "Phase 6 companion pin evidence reports no failures"
require_contains reviews/PHASE-06/evidence/doctor-companion.txt "doctor summary: 0 fail" "Phase 6 companion doctor evidence reports no failures"
if [[ "${VEIR_QUALITY_GATES_RUNNING:-0}" == "1" ]]; then
  ok "Phase 6 quality-gates evidence marker validation deferred while wrapper is running"
else
  require_contains reviews/PHASE-06/evidence/quality-gates.txt "Phase 6 harness gates completed." "Phase 6 quality-gates evidence records wrapper completion"
fi
require_contains reviews/PHASE-06/evidence/validate-skills.txt "skill validation summary: 0 fail" "Phase 6 skill evidence reports no failures"
require_contains reviews/PHASE-06/evidence/lake-build.txt "Build completed successfully" "Phase 6 lake build evidence reports success"
require_contains reviews/PHASE-06/evidence/differential-clean-pin-canonicalize.txt "Summary: 21 pass (incl. expected-diverge), 0 fail" "Phase 6 clean-pin canonical baseline reports no failures"
require_contains reviews/PHASE-06/evidence/adversarial-review.txt "PASS: Phase 5 is marked completed before Phase 6 starts." "Phase 6 adversarial evidence records Phase 5 closeout"
require_contains reviews/PHASE-06/evidence/adversarial-review.txt "PASS: companion expected-divergence polarity remains exact and marker-driven." "Phase 6 adversarial evidence records exact polarity baseline"
require_contains ../llzk-lean/differential/README.md "clean-pin expanded corpus" "companion differential README records clean-pin expanded corpus status"
require_contains ../llzk-lean/differential/README.md "The directory is not a wildcard" "companion differential README documents exact expected-divergence markers"
require_not_contains ../llzk-lean/differential/README.md "still intentionally small" "companion differential README no longer calls the Phase 5 corpus intentionally small"
require_not_contains ../llzk-lean/differential/README.md "corpus is still a reviewed seed" "companion differential README no longer calls the Phase 5 corpus a seed"
require_not_contains ../llzk-lean/differential/README.md "Current seed bar" "companion differential README no longer carries the stale seed bar"
require_contains ../llzk-lean/differential/corpus/README.md 'EXPECTED-LLZK-FAIL' "companion corpus README documents expected LLZK failure polarity"
require_contains ../llzk-lean/differential/corpus/README.md 'EXPECTED-VEIR-FAIL' "companion corpus README documents expected VEIR failure polarity"
require_contains ../llzk-lean/differential/corpus/README.md 'with `EXPECTED-DIVERGE` marker' "companion corpus README documents exact output-divergence polarity"

if grep -q "Phase 5 implementation gate" "${ROOT}/docs/phases/PHASE-05-strategy-a-pin-and-corpus.md" &&
   grep -q "Clean-pin expanded corpus evidence covers the 15 VeIR Felt rewrite-pattern" "${ROOT}/docs/phases/PHASE-05-strategy-a-pin-and-corpus.md"; then
  ok "Phase 5 docs record clean-pin Strategy A corpus expansion"
else
  fail "Phase 5 docs do not record clean-pin Strategy A corpus expansion"
fi

if grep -q "Phase 6: Strategy A Divergence Burn-Down" "${ROOT}/docs/phases/PHASE-06-strategy-a-divergence-burndown.md" &&
   grep -q "21 pass (incl. expected-diverge), 0 fail" "${ROOT}/docs/phases/PHASE-06-strategy-a-divergence-burndown.md"; then
  ok "Phase 6 docs record divergence burn-down baseline"
else
  fail "Phase 6 docs do not record divergence burn-down baseline"
fi

if grep -Fq -- "$ACCEPTED_LLZK_REMOTE" "${ROOT}/reviews/PHASE-02/evidence/llzk-lib-refs.txt"; then
  ok "Phase 2 llzk-lib ref evidence records accepted remote"
else
  fail "Phase 2 llzk-lib ref evidence does not record accepted remote ${ACCEPTED_LLZK_REMOTE}"
fi

echo
echo "doc freshness summary: ${FAIL} fail"
if [[ "$FAIL" -ne 0 ]]; then
  exit 1
fi
exit 0
