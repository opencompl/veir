# Phase 5 Adversarial Review

Repository: veir
Reviewed: 2026-06-10

## Scope

This review covers Phase 5 bootstrap, clean VeIR pin consumption by companion
llzk-lean, and the expanded corpus run through the default
`.lake/packages/VeIR/scripts/llzk-diff.sh` path. It does not claim full
Strategy A corpus coverage.

## Required Checks

- Confirm `docs/harness/CURRENT.md` names Phase 5 as active.
- Confirm `docs/phases/PHASE-05-strategy-a-pin-and-corpus.md` records the clean
  pin consumption target.
- Confirm Phase 4 workspace evidence remains present and separated from clean
  dependency acceptance.
- Confirm clean-pin corpus evidence uses the default dependency path, not a
  workspace `VEIR_DIFF` override.
- Confirm the corpus matrix covers all 15 VeIR Felt rewrite patterns while
  keeping expected divergences separate from positives.

## Initial Result

Bootstrap documentation is ready for review once freshness, source, companion
pin, doctor, skill, wrapper, and build gates pass.

## Final Result

Accepted as Phase 5 clean-pin expanded corpus evidence.

- `reviews/PHASE-05/evidence/check-doc-freshness.txt`: doc freshness summary is
  `0 fail`; the gate now requires Phase 5 to be active, the Phase 5 review
  workspace to exist, and Phase 4 evidence to remain present.
- `reviews/PHASE-05/evidence/verify-llzk-source.txt`: LLZK source verification
  summary is `0 fail, 1 warn`; the warning is the known stale `../llzk-lib`
  worktree HEAD while the gate reads the accepted commit with `git show`.
- `reviews/PHASE-05/evidence/verify-companion-pin.txt`: companion pin
  verification summary is `0 fail, 0 warn`; local VeIR HEAD and companion
  llzk-lean's dependency checkout both equal the accepted clean pin.
- `reviews/PHASE-05/evidence/doctor-companion.txt`: strict companion doctor
  summary is `0 fail, 0 warn`.
- `reviews/PHASE-05/evidence/quality-gates.txt`: compatibility wrapper reports
  `Phase 5 harness gates completed.`
- `reviews/PHASE-05/evidence/validate-skills.txt`: skill validation summary is
  `0 fail over 4 skills`.
- `reviews/PHASE-05/evidence/lake-build.txt`: `lake build` completed
  successfully.
- `reviews/PHASE-05/evidence/differential-clean-pin-canonicalize.txt`: the
  companion llzk-lean clean dependency driver runs the expanded canonical corpus
  with no `VEIR_DIFF` override and reports `21 pass (incl. expected-diverge),
  0 fail`.
- `reviews/PHASE-05/evidence/adversarial-review.txt`: confirms the bootstrap
  state, clean-pin corpus evidence, and expected-divergence boundary.

The clean-pin consumption and initial 15-pattern corpus expansion parts of
Phase 5 are complete. Reducing expected divergences and reclassifying closed
gaps remain active work.

## Fresh Review Update

A subsequent fresh adversarial review found stale Phase 5 status language after
the companion 21-input corpus expansion, incomplete companion corpus polarity
documentation for expected LLZK/VEIR failures, and source evidence that omitted
stderr warning detail. These are resolved by updating the current status docs,
tightening doc freshness against stale seed-corpus language, documenting
expected tool-failure polarity in companion llzk-lean, and refreshing source
evidence with stderr captured.

The final fresh review found that companion expected-divergence polarity was
too broad: canonical output-divergence tests would accept an LLZK-side or
VEIR-side tool failure merely because they lived under `expected-divergence/`.
This is resolved by making each companion expected-divergence file's
`EXPECTED-*` header authoritative and by adding guard evidence proving a wrong
failure mode exits nonzero.
