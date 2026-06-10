# Phase 5 Findings

Repository: veir
Reviewed: 2026-06-10

## F5-VEIR-01: Clean-pinned differential driver could hang in `lake exec`

Severity: high
Status: resolved

The first clean-pin candidate, `3e936409c85a27b6d9695f5431d6ccb8a6d842fd`,
contained `--canonicalize` support but invoked `veir-opt` only through
`lake exec`. In the companion llzk-lean dependency checkout, the first
canonical corpus input did not finish within a 240-second bounded run, while
the already-built `.lake/packages/VeIR/.lake/build/bin/veir-opt` completed the
same lowered input immediately.

Resolution: VeIR commit `220cd215579b435c3c22ce86b34a3f4ce2ca276e` updates
`scripts/llzk-diff.sh` to prefer an existing `.lake/build/bin/veir-opt` and
fall back to `lake exec` only when the binary is absent. Companion llzk-lean now
pins that commit, and the clean-pin canonical corpus evidence runs through the
default dependency driver without `VEIR_DIFF`.

Companion llzk-lean finding F5-LLZK-01 was found and resolved in the companion
Phase 5 review workspace by making SKIP a non-zero wrapper outcome.

## F5-VEIR-02: Phase 5 status docs still described corpus evidence as only starting

Severity: medium
Status: resolved

After companion llzk-lean expanded the clean-pin corpus to 21 inputs,
`docs/harness/CURRENT.md` still said Phase 5 was starting to move corpus
evidence onto the clean dependency path and still described the canonical corpus
as seed-only. That contradicted the companion corpus evidence and could mislead
the next phase handoff even while freshness passed.

Resolution: `docs/harness/CURRENT.md` and `docs/harness/GATES.md` now describe
the companion clean-pin expanded corpus and the 15-pattern rewrite matrix without
claiming full Strategy A acceptance. `scripts/harness/check-doc-freshness.sh`
now rejects stale seed/future-work language and checks the companion llzk-lean
corpus docs.

## F5-VEIR-03: Companion corpus docs omitted expected tool-failure polarity

Severity: low
Status: resolved

The companion corpus README documented PASS/DIVERGE inversion under
`expected-divergence/`, but the wrapper and current corpus also support
`EXPECTED-LLZK-FAIL` and `EXPECTED-VEIR-FAIL`.

Resolution: companion llzk-lean now documents expected LLZK/VEIR failure
polarity, and VeIR doc freshness checks those companion labels.

## F5-VEIR-04: Source evidence omitted stderr warning detail

Severity: low
Status: resolved

`reviews/PHASE-05/evidence/verify-llzk-source.txt` reported
`LLZK source verification summary: 0 fail, 1 warn`, but the warning text itself
was emitted on stderr and was not captured in the evidence file.

Resolution: Phase 5 source evidence is refreshed with stderr captured so the
known stale `../llzk-lib` warning appears alongside the pass/fail summary.

## F5-VEIR-05: Companion expected-divergence polarity accepted wrong failure modes

Severity: high
Status: resolved

Companion `llzk-lean/differential/run-differential.sh` treated every file under
`expected-divergence/` as allowed to pass on `DIVERGE`, `VEIR-FAIL`, or
`LLZK-FAIL`. For canonical output-divergence tests, that could hide a regression
where one tool stopped producing comparable output.

Resolution: companion llzk-lean now requires each expected-divergence file to
declare its exact accepted `EXPECTED-*` outcome. VeIR doc freshness checks the
companion docs and local Phase 5 polarity-guard evidence showing a wrong failure
mode exits nonzero.
