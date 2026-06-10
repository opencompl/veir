# Phase 6: Strategy A Divergence Burn-Down

Status: completed; superseded by Phase 7
Last reviewed: 2026-06-10
Repository: veir
Companion phase file: ../../../llzk-lean/docs/phases/PHASE-06-strategy-a-divergence-burndown.md

## Objective

Bootstrap the next Strategy A workstream after the Phase 5 clean-pin corpus:
support companion llzk-lean's exact-polarity divergence burn-down by preserving
the clean VeIR diff driver, clean companion pin state, and Phase 5 corpus
baseline while the next implementation target is selected.

## Starting State

- VeIR HEAD at Phase 6 bootstrap:
  `220cd215579b435c3c22ce86b34a3f4ce2ca276e`.
- llzk-lean HEAD at Phase 6 bootstrap:
  `617702beadfbad6be784945e2bd98e8a788d357c`.
- Accepted VeIR pin consumed by llzk-lean at bootstrap:
  `220cd215579b435c3c22ce86b34a3f4ce2ca276e`.
- Accepted LLZK source commit remains:
  `db922857bc5a88a9107627ef6b36a8b5e57bc5c2`.
- Phase 5 companion corpus evidence records 21 clean-pin inputs with exact
  `EXPECTED-*` polarity and `0 fail`.

## Phase 6 Implementation Update

- First burn-down VeIR commit:
  `a0bb2fc8e6d38ab068247dfc6506ba63f5feb953`.
- Companion llzk-lean now consumes that clean VeIR pin through Lake metadata and
  a clean `.lake/packages/VeIR` checkout.
- VeIR canonical differential mode now compares `llzk-opt --canonicalize`
  against `veir-opt -p=felt-combine,dce`, aligning the diff path with LLZK's
  dead-input cleanup after constant folds.
- Companion llzk-lean's clean-pin corpus still has 21 inputs and `0 fail`, but
  the classification is now 7 PASS cases, 13 `EXPECTED-DIVERGE` canonical
  cases, and 1 `EXPECTED-LLZK-FAIL` named-field parser/verifier gap.
- Companion reclassified positives:
  `felt/registered_add_fold.llzk`, `felt/constant_fold_sub.llzk`, and
  `felt/constant_fold_mul.llzk`.

## Non-Goals

- Do not broaden Strategy A claims beyond reviewed corpus evidence.
- Do not change accepted LLZK source facts or field registry facts.
- Do not port missing Felt operations or Strategy E certificates in this phase
  bootstrap.
- Do not treat workspace overrides as clean-pin acceptance evidence.

## Artifacts To Create Or Update

- `docs/phases/PHASE-06-strategy-a-divergence-burndown.md`: Phase 6 bootstrap.
- `docs/phases/PHASE-05-strategy-a-pin-and-corpus.md`: mark Phase 5 completed.
- `docs/harness/CURRENT.md`: move the active phase to Phase 6.
- `docs/harness/SOURCES.md`: record Phase 6 and Phase 5 exact-polarity closeout
  evidence.
- `docs/harness/GATES.md`: document Phase 6 bootstrap and companion divergence
  burn-down gates.
- `scripts/llzk-diff.sh`: run `felt-combine,dce` in canonical differential
  mode.
- `scripts/harness/check-doc-freshness.sh`: require Phase 6 to be active while
  preserving Phase 2 through Phase 5 evidence checks.
- `scripts/harness/doctor.sh`: require Phase 6 docs and review workspace.
- `scripts/check-llzk-quality-gates.sh`: report Phase 6 bootstrap gates.
- `reviews/PHASE-06/{request.md,findings.md,disposition.md,adversarial-review.md,evidence/}`:
  Phase 6 review workspace.

## Gates To Implement

- Bootstrap freshness:
  `scripts/harness/check-doc-freshness.sh` passes only when Phase 6 is active,
  the Phase 6 review workspace exists, Phase 5 is marked complete, and Phase 5
  clean-pin plus exact-polarity evidence remains present.
- Source truth:
  `scripts/harness/verify-llzk-source.sh --llzk-lib ../llzk-lib` continues to
  pass from the VeIR root.
- Companion pin:
  `scripts/harness/verify-companion-pin.sh --companion-llzk-lean ../llzk-lean`
  continues to pass with the accepted clean dependency pin.
- Strict doctor:
  `scripts/harness/doctor.sh --companion-llzk-lean ../llzk-lean` continues to
  pass from the VeIR root.
- Build:
  `lake build` succeeds.
- Companion Strategy A baseline:
  companion llzk-lean's clean-pin canonical differential remains
  `21 pass (incl. expected-diverge), 0 fail` with the Phase 6
  reclassification above.

## Review Requirements

- The reviewer must verify that Phase 5 findings are closed before Phase 6
  implementation work starts.
- The reviewer must verify that companion expected-divergence polarity remains
  exact and marker-driven.
- The reviewer must verify that VeIR docs do not claim full Strategy A
  acceptance.
- Every Phase 6 finding must be dispositioned before the phase closes.

## Done Criteria

- Phase 6 bootstrap docs and review workspace exist in both VeIR and llzk-lean.
- `docs/harness/CURRENT.md` names Phase 6 as active.
- `docs/harness/SOURCES.md` records Phase 6 and Phase 5 exact-polarity closeout
  evidence.
- Freshness, source truth, companion pin checks, strict doctor, skill
  validation, wrapper gates, `lake build`, and the companion clean-pin
  canonical differential baseline pass.
