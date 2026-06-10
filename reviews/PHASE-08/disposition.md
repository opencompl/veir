# Phase 8 Disposition

Repository: veir
Updated: 2026-06-10

No Phase 8 findings are open.

Phase 8 starts from the completed Phase 7 registered-field modular-reduction
closeout. The first target is the companion bare/unknown-field
fold-precondition divergence recorded by `unspecified_add_fold.llzk`.

F8-VEIR-01 is resolved by VeIR commit
`d899d95004d4bd988c8456d686c33b11a7a5eb4a`. The target moved to companion
`differential/corpus/felt/unspecified_add_fold.llzk` as a positive no-fold
case, and the companion clean-pin canonical baseline remains
`21 pass (incl. expected-diverge), 0 fail`.

F8-VEIR-02 is resolved by refreshing
`Test/LLZK/Felt/pipelines/combine_then_dce.mlir` to exercise registered-field
folding before DCE. The bare-field no-fold behavior remains covered by the
companion Phase 8 target instead of by this fold-positive pipeline test.
