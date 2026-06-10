# Phase 7 Review Request

Repository: veir
Requested: 2026-06-10

Review the Phase 7 Strategy A modular-reduction execution.

Scope:
- Phase 6 is completed and superseded by Phase 7.
- Phase 7 is active in harness docs and gates.
- The implementation target is limited to the companion registered-field
  modular-reduction cases `registered_add_wrap.llzk` and
  `constant_fold_neg.llzk`.
- The companion target cases are reclassified as positive corpus cases only
  after clean-pin evidence shows they match LLZK.
- The companion clean-pin canonical baseline remains
  `21 pass (incl. expected-diverge), 0 fail` after the reclassification.
- Exact `EXPECTED-*` polarity remains required for all expected-divergence
  inputs.

Out of scope:
- Full Strategy A acceptance.
- Strategy E certificates.
- Reclassification of nonconstant algebraic rewrite divergences before a
  reviewed implementation change lands.
