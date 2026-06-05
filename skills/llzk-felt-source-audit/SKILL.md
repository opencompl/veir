# LLZK Felt Source Audit

## When to use

Use this skill when a task cites LLZK Felt behavior, LLZK field arithmetic, or
LLZK/VeIR parity.

## Procedure

- Start from `docs/harness/SOURCES.md`; do not rely on historical review notes
  unless the claim is revalidated.
- Record exact local files, refs, and command outputs under
  `reviews/PHASE-00/evidence/` when the claim affects Phase 0.
- Keep semantic Felt changes out of Phase 0.

## Validation

Run `scripts/harness/validate-skills.sh` and `scripts/harness/doctor.sh`.
