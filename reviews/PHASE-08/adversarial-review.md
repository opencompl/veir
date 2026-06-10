# Phase 8 Adversarial Review

Repository: veir
Reviewed: 2026-06-10

## Scope

This review closes the first Phase 8 field-precondition target and checks that
the new accepted VeIR pin preserves the companion corpus baseline without
claiming broad Strategy A acceptance. It also checks that the reclassified
Phase 8 target is the companion field-precondition gap recorded by
`unspecified_add_fold.llzk`, not the remaining nonconstant algebraic rewrite
divergences.

## Checks

- Confirm Phase 7 findings are resolved and Phase 7 is marked completed.
- Confirm the companion clean-pin canonical corpus still records
  `21 pass (incl. expected-diverge), 0 fail`.
- Confirm the consumed VeIR pin is
  `d899d95004d4bd988c8456d686c33b11a7a5eb4a`.
- Confirm companion expected-divergence polarity remains exact and
  marker-driven.
- Confirm `docs/harness/CURRENT.md` names Phase 8 as active.
- Confirm Phase 8 reclassifies only companion
  `differential/corpus/felt/unspecified_add_fold.llzk`.
- Confirm VeIR's own fold-positive pipeline lit fixture uses a registered field
  after the Phase 8 bare-field no-fold tightening.
- Confirm nonconstant algebraic rewrite divergences remain out of scope until a
  reviewed implementation change lands.

## Result

Accepted as Phase 8 implementation evidence for bare/unknown-field
fold-precondition parity. No Phase 7 closeout blocker or Phase 8 blocker
remains. The follow-up CI fixture drift in
`Test/LLZK/Felt/pipelines/combine_then_dce.mlir` is resolved by making that
fold-positive pipeline case registered-field explicit.
