# LLZK Felt Source Audit

## When to use

Use this skill when a task cites LLZK Felt behavior, LLZK field arithmetic, or
LLZK/VeIR parity.

## Procedure

- Start from `docs/harness/SOURCES.md`; do not rely on historical review notes
  unless the claim is revalidated.
- Record exact local files, refs, and command outputs under
  the active phase review directory, e.g. `reviews/PHASE-01/evidence/` for the
  current pin phase.
- Keep semantic Felt changes out of reproducible-pin phases unless the phase
  explicitly scopes them in.

## Validation

Run `scripts/harness/validate-skills.sh` and `scripts/harness/doctor.sh`.
