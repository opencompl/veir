# Phase 0 Disposition

Reviewed: 2026-06-05
Repository: veir

## Disposition

- V-P0-001: fixed. `scripts/check-llzk-quality-gates.sh` now delegates to the
  Phase 0 harness scripts and no longer reads deleted `harness/*.md` files.
- V-P0-002: fixed. `scripts/harness/doctor.sh --companion-llzk-lean ../llzk-lean`
  fails in strict mode on the dirty dependency state and reports exact files.
- V-P0-003: accepted-risk. Phase 0 intentionally does not claim Felt semantic
  acceptance; future phases must add those gates with fresh evidence.
- V-P0-004: fixed. `scripts/check-llzk-quality-gates.sh` now auto-checks
  `../llzk-lean` or `LLZK_LEAN_ROOT` in strict mode and fails on the known dirty
  companion dependency. Local-only execution requires
  `VEIR_HARNESS_LOCAL_ONLY=1` and prints that it is not acceptance evidence.
- V-P0-005: fixed. `scripts/harness/doctor.sh` now reports repository HEAD
  drift from bootstrap inputs as a warning. Dependency pin mismatches and dirty
  companion dependency state remain hard failures.
