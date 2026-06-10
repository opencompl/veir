# Phase Bootstrap

## When to use

Use this skill when creating or closing a phase bootstrap file.

## Procedure

- Start from `docs/phases/PHASE_TEMPLATE.md`.
- Update `docs/harness/CURRENT.md`, `docs/harness/SOURCES.md`, and
  `docs/harness/GATES.md` with exact refs; update `docs/harness/PINS.md` when
  the phase changes companion dependency state.
- Create `reviews/<PHASE>/request.md`, `findings.md`, `disposition.md`, and
  `evidence/`.

## Validation

Run `scripts/harness/check-doc-freshness.sh`,
`scripts/harness/validate-skills.sh`, and `scripts/harness/doctor.sh`.
