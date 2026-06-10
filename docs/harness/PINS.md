# Companion Dependency Pin

Last reviewed: 2026-06-10

## Accepted VeIR Pin

- Commit: `d899d95004d4bd988c8456d686c33b11a7a5eb4a`
- Short ref: `d899d95004d4`
- Remote: `https://github.com/project-llzk/veir.git`
- Branch at selection time: `felt-review-structural-close`
- Mode: remote commit consumed by llzk-lean through Lake metadata and a clean
  Lake package checkout

This commit is a descendant of the Phase 2 accepted pin
`d4cc1bf2d31beeca17eb2e8c9c7181d04af013a3`, which was itself a descendant of
the Phase 1 accepted pin `d52917ca4a57c4094b1aa61dd413aca4e1c2a56e`.

This pin preserves the Phase 2 field-registry update and source-truth gate,
preserves the Phase 5 canonicalization-aware `scripts/llzk-diff.sh` driver
consumed by the default llzk-lean dependency checkout, adds the Phase 6
DCE-enabled canonical differential path, adds Phase 7 registered-field
fold-result reduction, and adds Phase 8 bare/unknown-field fold-precondition
parity. The driver uses a built `.lake/build/bin/veir-opt` when present and
falls back to `lake exec`.

## Required Companion State

The following companion files and checkout must all identify the accepted
commit:

- `../llzk-lean/lakefile.toml` `git` and `rev`
- `../llzk-lean/lake-manifest.json` `url`, `type`, `rev`, and `inputRev`
- `../llzk-lean/.lake/packages/VeIR` HEAD

`git -C ../llzk-lean/.lake/packages/VeIR status --short` must be empty.

## Allowed Modes

- Strict acceptance: companion Lake files and dependency checkout all match the
  accepted commit, and the dependency checkout is clean.
- Local-only VeIR layout:
  `VEIR_HARNESS_LOCAL_ONLY=1 scripts/check-llzk-quality-gates.sh` may skip the
  companion gate and must print that the result is not acceptance evidence.
- Exploratory companion checks may report state, but dirty or mismatched
  dependency state must not close a phase.

## Forbidden Hidden State

Do not rely on:

- Modified, staged, deleted, or untracked files under
  `../llzk-lean/.lake/packages/VeIR`.
- Local commits in the dependency checkout that are not the accepted commit.
- A workspace checkout path as the source of truth.
- `lake update` output that changes the VeIR rev without a deliberate review
  evidence update.

## Update Procedure

1. Select a new VeIR commit and verify that it is available from the accepted
   remote.
2. Record the branch, remote, and exact commit under `docs/harness/SOURCES.md`
   and Phase review evidence.
3. Update companion `lakefile.toml` and `lake-manifest.json` to the exact
   commit.
4. Refresh companion `.lake/packages/VeIR` to that commit and ensure it is
   clean.
5. Run `scripts/harness/verify-companion-pin.sh --companion-llzk-lean
   ../llzk-lean`.
6. Run the companion llzk-lean strict doctor and `lake build`.
7. Record all command output under `reviews/PHASE-XX/evidence/`.

## Rollback Procedure

1. Restore companion `lakefile.toml` and `lake-manifest.json` to the previous
   accepted commit.
2. Refresh companion `.lake/packages/VeIR` to that commit.
3. Confirm the companion dependency checkout is clean.
4. Re-run `scripts/harness/verify-companion-pin.sh --companion-llzk-lean
   ../llzk-lean` and companion `lake build`.
5. Record rollback evidence and disposition the reason for rollback.
