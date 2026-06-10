# Phase 5 Disposition

Repository: veir
Created: 2026-06-09
Updated: 2026-06-10

- F5-VEIR-01 resolved by updating `scripts/llzk-diff.sh` in
  `220cd215579b435c3c22ce86b34a3f4ce2ca276e` to use the built `veir-opt`
  binary when available and preserve `lake exec` as a fallback.
- Companion llzk-lean finding F5-LLZK-01 was resolved in the companion
  repository by making SKIP a non-zero wrapper outcome.
- F5-VEIR-02 resolved by updating stale Phase 5 status docs and adding
  freshness checks that reject seed-only/future-expansion language.
- F5-VEIR-03 resolved by documenting companion `EXPECTED-LLZK-FAIL` and
  `EXPECTED-VEIR-FAIL` corpus polarity and gating those labels in VeIR doc
  freshness.
- F5-VEIR-04 resolved by refreshing `verify-llzk-source.txt` with stderr
  captured so the known stale `../llzk-lib` warning is present in the evidence.
- F5-VEIR-05 resolved by tightening companion expected-divergence polarity to
  exact `EXPECTED-*` headers and gating wrong-failure-mode evidence.

No Phase 5 findings remain open.
