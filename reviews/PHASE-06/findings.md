# Phase 6 Findings

Repository: veir
Reviewed: 2026-06-10

## F6-VEIR-01: Canonical diff omitted DCE after Felt combines

Severity: medium
Status: resolved

At Phase 6 bootstrap, companion llzk-lean carried three DCE-only expected
divergences: registered add, registered sub, and registered mul constant
folds. VeIR's canonical diff path ran `felt-combine` alone, so it preserved
dead input constants that LLZK's canonicalizer removed.

Resolution: VeIR commit `a0bb2fc8e6d38ab068247dfc6506ba63f5feb953` updates
`scripts/llzk-diff.sh` canonical mode to run `felt-combine,dce`. Companion
llzk-lean consumes that clean pin and reclassifies the three DCE-only cases as
PASS while preserving the exact-polarity expected-divergence gate.

No Phase 6 findings remain open.
