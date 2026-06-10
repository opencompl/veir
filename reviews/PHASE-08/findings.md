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
