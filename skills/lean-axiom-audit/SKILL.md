# Lean Axiom Audit

## When to use

Use this skill when reviewing Lean proof files, theorem claims, `axiom`, or
`sorry` usage.

## Procedure

- Check current source state before trusting historical proof summaries.
- Prefer exact file paths and command evidence over broad claims.
- Treat dirty dependency proof files as exploratory unless the dirty state is
  explicitly reviewed.

## Validation

Run `scripts/harness/validate-skills.sh` and `scripts/harness/doctor.sh`.
