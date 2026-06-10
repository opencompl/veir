# Phase 8 Findings

Repository: veir
Reviewed: 2026-06-10

No Phase 8 findings are open.

## F8-VEIR-01: Bare Felt Constant Fold Ignored LLZK Field Preconditions

- Severity: medium
- Status: resolved
- Area: Strategy A canonical differential, VeIR Felt folding

At Phase 8 bootstrap, companion `unspecified_add_fold.llzk` documented a
narrow field-precondition divergence: LLZK left a bare `!felt.type` add unfired
because no registered field name resolved, while VeIR folded the same constants
under canonicalization.

Resolution: VeIR commit
`d899d95004d4bd988c8456d686c33b11a7a5eb4a` makes constant-fold and associative
constant-fold helpers return no rewrite when the field name cannot resolve
through the accepted registry. The companion case moved to
`differential/corpus/felt/unspecified_add_fold.llzk` as a positive no-fold
case, and the clean-pin canonical corpus remains
`21 pass (incl. expected-diverge), 0 fail`.

## F8-VEIR-02: Pipeline FileCheck Fixture Expected Bare-Field Folding

- Severity: low
- Status: resolved
- Area: VeIR CI, Felt pipeline tests

The open PR's Lean Action CI ran the full lit suite and failed
`Test/LLZK/Felt/pipelines/combine_then_dce.mlir`: the fixture still expected
`felt-combine,dce` to fold bare `!felt.type` constants `1 + 2` into `3`.
That expectation contradicted the Phase 8 field-precondition fix, where
bare/unknown-field constant folds intentionally do not fire.

Resolution: the pipeline fixture now uses registered `!felt.type<"babybear">`
values for the fold-then-DCE path and explicitly leaves the bare-field no-fold
case to the companion Phase 8 `unspecified_add_fold.llzk` target. The targeted
lit reproduction passes locally, and the full VeIR lit suite reports
`350 passed, 10 unsupported, 0 failed`.
