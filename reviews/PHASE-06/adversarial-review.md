# Phase 6 Adversarial Review

Repository: veir
Reviewed: 2026-06-10

## Scope

This review covers the Phase 6 bootstrap and first implementation target. It
verifies that VeIR and companion llzk-lean start from Phase 5's clean-pin
corpus and exact expected-divergence polarity, then reclassify only DCE-only
divergences without claiming full Strategy A acceptance.

## Bootstrap Checks

- Confirm Phase 5 is marked completed and all Phase 5 findings are closed.
- Confirm `docs/harness/CURRENT.md` names Phase 6 as active.
- Confirm `docs/harness/SOURCES.md` records the Phase 6 phase file and Phase 5
  exact-polarity guard evidence.
- Confirm freshness, source-truth, companion-pin, doctor, skill, wrapper, build,
  and companion clean-pin canonical differential baseline gates pass.

## Implementation Checks

- Confirm `scripts/llzk-diff.sh` canonical mode runs `felt-combine,dce`.
- Confirm companion llzk-lean consumes
  `a0bb2fc8e6d38ab068247dfc6506ba63f5feb953` as a clean pin.
- Confirm companion llzk-lean's clean dependency checkout is exactly
  `a0bb2fc8e6d38ab068247dfc6506ba63f5feb953` and invokes
  `-p=felt-combine,dce`.
- Confirm companion llzk-lean moved only the DCE-only registered add/sub/mul
  fold cases from expected divergence to `felt/`.
- Confirm those three moved companion inputs pass independently in canonical
  mode.
- Confirm remaining expected-divergence files keep exact `EXPECTED-*` polarity.
- Confirm the Phase 6 VeIR change did not edit VeIR Lean implementation files;
  it only changes the differential wrapper plus harness docs/evidence.

## Result

F6-VEIR-01 is resolved. Phase 6 implementation evidence under
`reviews/PHASE-06/evidence/` records the companion clean-pin corpus at
`21 pass (incl. expected-diverge), 0 fail`. A fresh post-implementation
adversarial pass found no new findings.
