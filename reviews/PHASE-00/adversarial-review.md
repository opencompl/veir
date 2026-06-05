# Adversarial Review Refresh

Reviewed: 2026-06-05
Repository: veir

## Scope

This refresh reviewed every Phase 0 artifact added or changed in this session:

- `AGENTS.md`
- `docs/harness/*.md`
- `docs/phases/*.md`
- `scripts/harness/*.sh`
- `scripts/check-llzk-quality-gates.sh`
- `scripts/llzk-diff.sh`
- `skills/*/SKILL.md`
- `reviews/PHASE-00/*`

## Review Questions

- Can any executable gate still report acceptance while skipping companion
  llzk-lean dependency state?
- Do canonical docs distinguish strict, exploratory, and local-only modes?
- Do stale historical `harness/*.md` references remain marked as stale?
- Are review findings dispositioned and supported by evidence?
- Are doc freshness checks strong enough to catch missing canonical docs and
  missing review evidence?

## New Findings From Refresh

- V-P0-004 was added: the compatibility wrapper previously skipped the
  companion check by default and exited 0.
- The wrapper now auto-checks `../llzk-lean` or `LLZK_LEAN_ROOT` and fails in
  strict mode on the known dirty companion state.
- `VEIR_HARNESS_LOCAL_ONLY=1` is now required for a non-acceptance local-only
  wrapper run.
- `scripts/harness/check-doc-freshness.sh` now checks all canonical harness
  review dates and required review evidence without depending on wrapper
  evidence that the wrapper itself would need to create.

## Residual Risk

Phase 0 still does not claim Felt semantic parity, full lit-suite acceptance, or
Lean proof acceptance. Those remain future phase work.
