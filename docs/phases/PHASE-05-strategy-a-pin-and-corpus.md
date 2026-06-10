# Phase 5: Strategy A Pin and Corpus

Status: completed; superseded by Phase 6
Last reviewed: 2026-06-10
Repository: veir
Companion phase file: ../../../llzk-lean/docs/phases/PHASE-05-strategy-a-pin-and-corpus.md

## Objective

Bootstrap the next Strategy A workstream after the Phase 4 workspace
differential: prepare the canonicalization-aware VeIR diff script to be
consumed through llzk-lean's clean dependency pin, then use that clean path to
broaden the reviewed corpus.

This phase starts from Phase 4's seed evidence. Bootstrap did not change the
accepted dependency pin or claim full Strategy A acceptance. Phase 5 execution
now selects a clean VeIR pin that contains the canonicalization-aware diff
driver; the clean-pin corpus now covers all 15 VeIR Felt rewrite-pattern
definitions as either positives or expected divergences.

## Starting State

- VeIR HEAD at Phase 5 bootstrap:
  `0c5280de5715dc0fa518e7e3782e784a5962d4d8`.
- llzk-lean HEAD at Phase 5 bootstrap:
  `617702beadfbad6be784945e2bd98e8a788d357c`.
- Accepted VeIR pin consumed by llzk-lean at bootstrap:
  `d4cc1bf2d31beeca17eb2e8c9c7181d04af013a3`.
- Phase 5 clean-pin target:
  `220cd215579b435c3c22ce86b34a3f4ce2ca276e`.
- Accepted LLZK source commit remains:
  `db922857bc5a88a9107627ef6b36a8b5e57bc5c2`.
- Local `../llzk-lib` worktree remains stale at
  `30b0fa1eb77de154ff60c13fa88ef286d8b01c65`; source facts still use the
  accepted commit through `git show`.
- Phase 4 produced reviewed workspace evidence for:
  `LLZK_OPT=/nix/store/awcw2wiypa02sl5vx4xm06qwji68xz3h-llzk-debug-2.0.0/bin/llzk-opt VEIR_DIFF=../veir/scripts/llzk-diff.sh ./differential/run-differential.sh --canonicalize differential/corpus`.
- Current `scripts/llzk-diff.sh` supports canonicalization mode and is consumed
  by llzk-lean through the clean dependency pin.
- Current worktrees are dirty from Phase 2/3 harness documentation, Phase 4
  differential implementation, and Phase 5 bootstrap docs. These are not pin
  acceptance evidence.

## Non-Goals

- Do not treat workspace `VEIR_DIFF=../veir/scripts/llzk-diff.sh` runs as clean
  pin acceptance.
- Do not broaden Strategy A claims beyond reviewed corpus evidence.
- Do not port missing Felt operations or Strategy E certificates in this phase
  bootstrap.
- Do not change accepted LLZK source facts or field registry facts.

## Artifacts To Create Or Update

- `docs/phases/PHASE-05-strategy-a-pin-and-corpus.md`: Phase 5 bootstrap.
- `docs/harness/CURRENT.md`: move the active phase to Phase 5.
- `docs/harness/SOURCES.md`: record Phase 5, Phase 4 evidence, and clean-pin
  consumption target.
- `docs/harness/GATES.md`: document Phase 5 bootstrap and clean-pin Strategy A
  implementation gates.
- `scripts/harness/check-doc-freshness.sh`: require Phase 5 to be active while
  preserving Phase 2, Phase 3, and Phase 4 evidence checks.
- `scripts/harness/doctor.sh`: require Phase 5 docs and review workspace.
- `scripts/check-llzk-quality-gates.sh`: report Phase 5 bootstrap gates.
- `reviews/PHASE-05/{request.md,findings.md,disposition.md,adversarial-review.md,evidence/}`:
  Phase 5 review workspace.

## Gates To Implement

- Bootstrap freshness:
  `scripts/harness/check-doc-freshness.sh` passes only when Phase 5 is active,
  the Phase 5 review workspace exists, Phase 4 evidence remains present, and
  source ledgers record the Phase 5 target.
- Source truth:
  `scripts/harness/verify-llzk-source.sh --llzk-lib ../llzk-lib` continues to
  pass from the VeIR root.
- Companion pin:
  `scripts/harness/verify-companion-pin.sh --companion-llzk-lean ../llzk-lean`
  passes with the clean dependency pin at
  `220cd215579b435c3c22ce86b34a3f4ce2ca276e`.
- Strict doctor:
  `scripts/harness/doctor.sh --companion-llzk-lean ../llzk-lean` continues to
  pass from the VeIR root.
- Build:
  `lake build` succeeds after bootstrap documentation changes.
- Phase 5 implementation gate:
  after the pin bump, llzk-lean canonicalization must run through the default
  clean dependency path with no workspace override:
  `LLZK_OPT=/nix/store/awcw2wiypa02sl5vx4xm06qwji68xz3h-llzk-debug-2.0.0/bin/llzk-opt ./differential/run-differential.sh --canonicalize differential/corpus`.
  Clean-pin expanded corpus evidence covers the 15 VeIR Felt rewrite-pattern
  definitions and still separates passing cases from expected divergences.
  Reducing expected divergences and any future reclassification remain open
  Phase 5 work.

## Review Requirements

- The reviewer must verify that Phase 5 is scoped to clean pin consumption and
  corpus expansion, not general Strategy A acceptance.
- The reviewer must verify that docs distinguish workspace evidence from clean
  dependency evidence.
- The reviewer must verify that Phase 4 adversarial findings are closed before
  Phase 5 implementation work starts.
- The reviewer must verify that existing source-truth, companion-pin, doctor,
  skill, wrapper, and build gates still pass.
- Disposition every finding before closing the phase.

## Done Criteria

- Phase 5 bootstrap docs and review workspace exist in both VeIR and llzk-lean.
- `docs/harness/CURRENT.md` names Phase 5 as active.
- `docs/harness/SOURCES.md` records the Phase 5 phase file and Phase 4
  canonical differential evidence.
- `check-doc-freshness.sh`, `verify-llzk-source.sh`, companion pin checks,
  `doctor.sh`, `validate-skills.sh`, `scripts/check-llzk-quality-gates.sh`, and
  `lake build` pass after the bootstrap.
- The clean VeIR pin consumes the canonicalization-aware diff script, and the
  clean-pin corpus matrix covers all 15 VeIR Felt rewrite-pattern definitions
  as either PASS or EXPECTED-DIVERGE under the canonicalized gate.
