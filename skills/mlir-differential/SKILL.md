# MLIR Differential

## When to use

Use this skill when comparing `veir-opt` and `llzk-opt` output or classifying a
differential failure.

## Procedure

- Read `docs/harness/GATES.md` before treating a differential result as
  acceptance evidence.
- Use `scripts/llzk-diff.sh` for local comparisons.
- Record missing tools, parse failures, pass failures, and semantic divergence
  as distinct outcomes.

## Validation

Run `scripts/harness/validate-skills.sh` and `scripts/harness/doctor.sh`.
