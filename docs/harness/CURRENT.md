# Current Harness State

Last reviewed: 2026-06-10

## Active Phase

- Active phase: Phase 6, Strategy A divergence burn-down bootstrap.
- Phase bootstrap file: `docs/phases/PHASE-06-strategy-a-divergence-burndown.md`.
- Companion repository: `../llzk-lean`.
- Companion phase file:
  `../llzk-lean/docs/phases/PHASE-06-strategy-a-divergence-burndown.md`.

## Accepted VeIR Pin

- Accepted VeIR commit:
  `220cd215579b435c3c22ce86b34a3f4ce2ca276e`.
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
- Operation gap ledger: `docs/harness/FELT_OP_GAPS.md`.

## Strategy A Test Infrastructure

- Accepted local `llzk-opt` binary:
  `/nix/store/awcw2wiypa02sl5vx4xm06qwji68xz3h-llzk-debug-2.0.0/bin/llzk-opt`.
- Local LLVM/MLIR checkout: `/home/alh/llvm-project`.
- LLVM checkout commit:
  `49f12af164138123589263fe75ea5f1d356e8780`.
- LLVM tools available:
  `/home/alh/llvm-project/build/bin/mlir-opt` and
  `/home/alh/llvm-project/build/bin/llvm-config`, both reporting
  `23.0.0git`.

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

The pin policy forbids hidden dependency edits. The companion llzk-lean checkout must
pin the accepted commit in `lakefile.toml` and `lake-manifest.json`; its
`.lake/packages/VeIR` checkout must be clean and at the same commit.

Local-only VeIR paths are not a source of truth unless the run is explicitly
documented as exploratory and non-acceptance.

## Known Hazards

- The Phase 1 bootstrap state included a dirty llzk-lean dependency checkout.
  That state is preserved under `reviews/PHASE-01/evidence/` and must not be
  treated as proof state after the pin transition.
- `scripts/llzk-diff.sh` supports canonicalization mode. Phase 5 made
  llzk-lean consume that support through the clean dependency pin for
  pin-backed evidence. Phase 6 starts from that exact-polarity corpus baseline.
- The local `../llzk-lib` worktree is behind fetched `origin/main`. Current
  source claims use `git show origin/main:...` at
  `db922857bc5a88a9107627ef6b36a8b5e57bc5c2`, not stale worktree files.
- Phase 3 closed the operation-gap ledger. Phase 4 added seed canonical
  differential coverage through a workspace `VEIR_DIFF` override. Phase 5 pinned
  the canonicalization-aware VeIR driver, recorded companion llzk-lean's
  expanded 21-input canonical corpus on the clean dependency path, and fixed
  expected-divergence polarity to exact file-header markers. The corpus covers
  all 15 current VeIR Felt rewrite-pattern definitions as PASS or
  EXPECTED-DIVERGE, plus one EXPECTED-LLZK-FAIL parser/verifier gap, but this is
  not full Strategy A acceptance.

## Acceptance Rule

Phase 6 bootstrap is current only when:

- `docs/harness/FELT_OP_GAPS.md` records every accepted LLZK Felt mnemonic and
  explicitly marks unsupported operations as gaps.
- `docs/phases/PHASE-06-strategy-a-divergence-burndown.md` exists and
  `docs/harness/CURRENT.md` names Phase 6 as active.
- `docs/harness/SOURCES.md` records `scripts/llzk-diff.sh`, the accepted
  `llzk-opt` binary path, `/home/alh/llvm-project`, the Phase 6 phase file,
  and Phase 5 exact-polarity guard evidence.
- `scripts/harness/verify-llzk-source.sh --llzk-lib ../llzk-lib` passes from
  the VeIR root.
- `scripts/harness/doctor.sh` passes from the VeIR root.
- `scripts/harness/verify-companion-pin.sh --companion-llzk-lean ../llzk-lean`
  passes from the VeIR root.
- `scripts/harness/check-doc-freshness.sh` passes from the VeIR root.
- `scripts/harness/validate-skills.sh` passes from the VeIR root.
- `scripts/check-llzk-quality-gates.sh` runs the strict companion pin gate and
  reports success.

Phase 6 implementation evidence additionally requires reducing or reclassifying
expected divergences without weakening the clean-pin canonical baseline. Until a
Phase 6 implementation deliberately changes that matrix, the companion clean-pin
canonical run remains `21 pass (incl. expected-diverge), 0 fail`.
