# Phase 4: Strategy A Differential Harness Bootstrap

Status: completed; superseded by Phase 5
Last reviewed: 2026-06-09
Repository: veir
Companion phase file: ../../../llzk-lean/docs/phases/PHASE-04-strategy-a-differential.md

## Objective

Bootstrap Strategy A as the active phase: turn the existing LLZK/VeIR
differential scaffold into the canonical next workstream, record the available
test infrastructure, and set gates for the later pass-pipeline differential
implementation.

This phase starts from the Phase 3 operation-gap ledger. It does not claim new
semantic parity. Its job is to make the next acceptance target explicit:
`llzk-opt --canonicalize` and `veir-opt -p=felt-combine` over a source-grounded
Felt corpus, with divergences classified instead of hidden by skips.

## Starting State

- VeIR HEAD at Phase 4 bootstrap:
  `0c5280de5715dc0fa518e7e3782e784a5962d4d8`.
- llzk-lean HEAD at Phase 4 bootstrap:
  `617702beadfbad6be784945e2bd98e8a788d357c`.
- Accepted VeIR pin consumed by llzk-lean remains:
  `d4cc1bf2d31beeca17eb2e8c9c7181d04af013a3`.
- Accepted LLZK source commit remains:
  `db922857bc5a88a9107627ef6b36a8b5e57bc5c2`.
- Local `../llzk-lib` worktree remains stale at
  `30b0fa1eb77de154ff60c13fa88ef286d8b01c65`; source facts still use the
  accepted commit through `git show`.
- `llzk-opt` is not on `PATH`, but the accepted local binary is available at
  `/nix/store/awcw2wiypa02sl5vx4xm06qwji68xz3h-llzk-debug-2.0.0/bin/llzk-opt`.
- LLVM/MLIR test infrastructure is available at `~/llvm-project`, a clean
  checkout of `https://github.com/llvm/llvm-project.git` at
  `49f12af164138123589263fe75ea5f1d356e8780`, with
  `/home/alh/llvm-project/build/bin/mlir-opt` and
  `/home/alh/llvm-project/build/bin/llvm-config` reporting `23.0.0git`.
- Current `scripts/llzk-diff.sh` supports both normalized parse/print
  differential mode and Phase 4 canonicalization mode:
  `llzk-opt --canonicalize --mlir-print-op-generic` compared with
  `veir-opt -p=felt-combine`.
- The companion `llzk-lean/differential/` corpus has been reclassified into
  positives and expected divergences, including canonical-only gaps for DCE,
  modular reduction, and field-registry preconditions.
- Current worktrees are dirty from Phase 2/3 harness documentation and Phase 4
  bootstrap edits. These are not differential acceptance evidence.

## Non-Goals

- Do not port the 13 missing Felt operations in this phase bootstrap.
- Do not expand Strategy E certificates or implement the C++ certificate
  matcher.
- Do not change the accepted VeIR dependency pin.
- Do not claim Strategy A acceptance until the pass-pipeline differential runs
  with `llzk-opt`, `veir-opt`, a reviewed corpus, and classified divergences.
- Do not treat missing `llzk-opt`, skipped runs, or parse/print agreement as
  pass-pipeline acceptance.

## Artifacts To Create Or Update

- `docs/phases/PHASE-04-strategy-a-differential.md`: Phase 4 bootstrap.
- `docs/harness/CURRENT.md`: move the active phase to Phase 4.
- `docs/harness/SOURCES.md`: record the differential harness, `llzk-opt`, and
  `~/llvm-project` test infrastructure as local sources.
- `docs/harness/GATES.md`: document Phase 4 bootstrap and future Strategy A
  acceptance gates.
- `scripts/harness/check-doc-freshness.sh`: require Phase 4 to be active while
  preserving Phase 2 source-truth and Phase 3 gap-ledger evidence checks.
- `scripts/harness/doctor.sh`: require Phase 4 docs and review workspace.
- `scripts/check-llzk-quality-gates.sh`: report Phase 4 bootstrap gates.
- `reviews/PHASE-04/{request.md,findings.md,disposition.md,adversarial-review.md,evidence/}`:
  Phase 4 review workspace.

## Gates To Implement

- Bootstrap freshness:
  `scripts/harness/check-doc-freshness.sh` passes only when Phase 4 is active,
  the Phase 4 review workspace exists, the Phase 3 gap ledger remains intact,
  and the source ledger records the differential harness plus local test tools.
- Source truth:
  `scripts/harness/verify-llzk-source.sh --llzk-lib ../llzk-lib` continues to
  pass from the VeIR root.
- Companion pin:
  `scripts/harness/verify-companion-pin.sh --companion-llzk-lean ../llzk-lean`
  continues to pass from the VeIR root.
- Strict doctor:
  `scripts/harness/doctor.sh --companion-llzk-lean ../llzk-lean` continues to
  pass from the VeIR root.
- Build:
  `lake build` succeeds after bootstrap documentation changes.
- Implementation gate:
  Strategy A acceptance requires a reviewed command that sets `LLZK_OPT` to the
  accepted binary and runs canonicalization on both tools over the accepted
  corpus. The workspace command is:
  `LLZK_OPT=/nix/store/awcw2wiypa02sl5vx4xm06qwji68xz3h-llzk-debug-2.0.0/bin/llzk-opt VEIR_DIFF=../veir/scripts/llzk-diff.sh ./differential/run-differential.sh --canonicalize differential/corpus`.
  Bootstrap does not satisfy this gate; the workspace implementation is seed
  evidence until llzk-lean's clean VeIR pin consumes the updated script.

## Review Requirements

- The reviewer must verify that Phase 4 is clearly scoped to Strategy A.
- The reviewer must verify that the docs do not claim differential acceptance
  before canonicalization and corpus evidence exist.
- The reviewer must verify that `~/llvm-project` and the Nix `llzk-opt` path are
  recorded as test infrastructure, not as proof state.
- The reviewer must verify that Phase 2 source-truth gates and Phase 3 gap-ledger
  evidence still pass.
- Disposition every finding before closing the phase.

## Done Criteria

- Phase 4 bootstrap docs and review workspace exist in both VeIR and llzk-lean.
- `docs/harness/CURRENT.md` names Phase 4 as active.
- `docs/harness/SOURCES.md` records the differential harness, accepted
  `llzk-opt` path, and `~/llvm-project` build path.
- `check-doc-freshness.sh`, `verify-llzk-source.sh`, companion pin checks,
  `doctor.sh`, `validate-skills.sh`, `scripts/check-llzk-quality-gates.sh`, and
  `lake build` pass after the bootstrap.
- The canonicalization-aware workspace execution path exists and the seed corpus
  is reclassified. The next task is to bump/consume a clean VeIR pin for this
  script and broaden the corpus toward the full Strategy A v1 bar.
