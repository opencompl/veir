# Phase 0 Findings

Reviewed: 2026-06-05
Repository: veir

## Findings

### V-P0-001: Stale quality gate referenced deleted harness docs

Severity: High

`scripts/check-llzk-quality-gates.sh` read `harness/coverage.md` and `plan.md`,
which are absent in this checkout. That made the script unsuitable as an
acceptance gate because it could report status from missing or stale sources.

Evidence:

- `reviews/PHASE-00/evidence/stale-references.txt`
- `reviews/PHASE-00/evidence/local-refs.txt`

### V-P0-002: Companion dependency dirty state must stay explicit

Severity: Critical

The companion llzk-lean Lake dependency checkout is dirty at bootstrap. Any
harness that omits this fact can cause reviews to rely on hidden local proof
state.

Evidence:

- `reviews/PHASE-00/evidence/companion-veir-status.txt`

### V-P0-003: Phase 0 does not provide semantic Felt acceptance

Severity: Medium

The new harness verifies source-state visibility and executable gate behavior.
It does not run the full lit suite, differential corpus, or Lean theorem audit.

Evidence:

- `docs/harness/GATES.md`

### V-P0-004: Compatibility wrapper skipped companion state by default

Severity: High

The first Phase 0 wrapper implementation exited 0 when `LLZK_LEAN_ROOT` was not
set and only printed that the companion dependency gate had not run. That still
left room for the old quality-gate entrypoint to be mistaken for full Phase 0
acceptance.

Evidence:

- `reviews/PHASE-00/evidence/quality-wrapper-strict.txt`
- `reviews/PHASE-00/evidence/quality-wrapper-local-only.txt`

### V-P0-005: Doctor treated bootstrap commit refs as immutable current HEADs

Severity: High

After Phase 0 was committed, `scripts/harness/doctor.sh` failed before reaching
the companion dependency check because the current VeIR and llzk-lean HEADs no
longer matched the pre-Phase-0 bootstrap refs. A committed script cannot
reliably require its repository HEAD to equal a literal hash stored inside that
same commit. The harness should report HEAD drift, while keeping dependency pin
and dirty-state checks as hard failures.

Evidence:

- Direct rerun of `scripts/harness/doctor.sh` on 2026-06-05 after the Phase 0
  commit.
