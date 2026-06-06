# Phase 1 Adversarial Review

Repository: veir

## Checks

- Companion dirty dependency rejection:
  `scripts/harness/verify-companion-pin.sh --companion-llzk-lean ../llzk-lean`
  was run before cleanup and failed while llzk-lean still named the old pin and
  had a dirty dependency checkout.
- Compatibility wrapper rejection: `scripts/check-llzk-quality-gates.sh` was run
  before cleanup and failed instead of reporting acceptance.
- Companion clean dependency acceptance: the companion pin gate was run after
  cleanup and passed only after llzk-lean Lake files and dependency checkout all
  agreed on `d52917ca4a57c4094b1aa61dd413aca4e1c2a56e`.
- Companion source spoof rejection: a temp-copy companion Lakefile and manifest
  with the accepted commit but a non-canonical VeIR URL was rejected.
- Companion manifest inputRev rejection: a temp-copy companion manifest with
  accepted `rev` but stale `inputRev` was rejected.

## Result

VeIR now has a strict companion-side gate for the Phase 1 pin invariant. A
local checkout path is documented as exploratory only; the accepted source is
the recorded remote commit.
