# Current Harness State

Last reviewed: 2026-06-06

## Active Phase

- Active phase: Phase 2, LLZK source truth and field registry parity.
- Phase bootstrap file: `docs/phases/PHASE-02-llzk-source-truth.md`.
- Companion repository: `../llzk-lean`.
- Companion phase file:
  `../llzk-lean/docs/phases/PHASE-02-llzk-source-truth.md`.

## Accepted VeIR Pin

- Accepted VeIR commit:
  `d4cc1bf2d31beeca17eb2e8c9c7181d04af013a3`.
- Accepted source branch: `felt-review-structural-close`.
- Accepted source remote: `https://github.com/project-llzk/veir.git`.
- Pin mode: remote commit consumed by llzk-lean through Lake metadata and a
  clean `.lake/packages/VeIR` checkout.

## Accepted LLZK Source

- Accepted `llzk-lib` commit:
  `db922857bc5a88a9107627ef6b36a8b5e57bc5c2`.
- Accepted source ref: `origin/main`.
- Accepted source checkout: `../llzk-lib`.
- Source ledger: `docs/harness/LLZK_SOURCE.md`.

## Refs

- VeIR Phase 1 bootstrap HEAD:
  `039068b68552bb37f1a887ec509e9b9111d4d54a`.
- llzk-lean Phase 1 bootstrap HEAD:
  `336a5a221ae79d00e5d1346e09341232bdc4323d`.
- VeIR implementation HEAD when Phase 1 started locally:
  `d4cc1bf2d31beeca17eb2e8c9c7181d04af013a3`.
- llzk-lean implementation HEAD when Phase 1 started locally:
  `6b4a7ec3aa38e2da7e1de23fb347b5c2cbac6386`.

The bootstrap refs are historical inputs from the phase file. The accepted
VeIR pin above is the dependency state llzk-lean is allowed to consume as
acceptance evidence.

## Dirty-State Policy

Phase 1 forbids hidden dependency edits. The companion llzk-lean checkout must
pin the accepted commit in `lakefile.toml` and `lake-manifest.json`; its
`.lake/packages/VeIR` checkout must be clean and at the same commit.

Local-only VeIR paths are not a source of truth unless the run is explicitly
documented as exploratory and non-acceptance.

## Known Hazards

- The Phase 1 bootstrap state included a dirty llzk-lean dependency checkout.
  That state is preserved under `reviews/PHASE-01/evidence/` and must not be
  treated as proof state after the pin transition.
- `scripts/llzk-diff.sh` remains useful for differential investigation, but
  Phase 1 does not claim Strategy A acceptance coverage.
- The local `../llzk-lib` worktree is behind fetched `origin/main`. Current
  Phase 2 source claims use `git show origin/main:...` at
  `db922857bc5a88a9107627ef6b36a8b5e57bc5c2`, not stale worktree files.

## Acceptance Rule

Phase 2 is current only when:

- `scripts/harness/verify-llzk-source.sh --llzk-lib ../llzk-lib` passes from
  the VeIR root.
- `scripts/harness/doctor.sh` passes from the VeIR root.
- `scripts/harness/verify-companion-pin.sh --companion-llzk-lean ../llzk-lean`
  passes from the VeIR root.
- `scripts/harness/check-doc-freshness.sh` passes from the VeIR root.
- `scripts/harness/validate-skills.sh` passes from the VeIR root.
- `scripts/check-llzk-quality-gates.sh` runs the strict companion pin gate and
  reports success.
