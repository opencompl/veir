# Phase 3 Findings

Repository: veir
Reviewed: 2026-06-06

## P3-V1: Freshness gate accepted README-only Phase 3 evidence

- Severity: medium
- Evidence: `scripts/harness/check-doc-freshness.sh` required only
  `reviews/PHASE-03/evidence/README.md`, while the Phase 3 done criteria require
  fresh adversarial evidence.
- Status: fixed
- Disposition: `check-doc-freshness.sh` now requires nonempty Phase 3 evidence
  outputs for doc freshness, LLZK source truth, companion pin verification,
  companion doctor, quality gates, skill validation, lake build, and
  adversarial review.

## P3-V2: Evidence README omitted declared closeout gates

- Severity: low
- Evidence: `reviews/PHASE-03/evidence/README.md` did not list companion pin,
  quality-gates, or skill-validation evidence even though those gates are part
  of the Phase 3 acceptance path.
- Status: fixed
- Disposition: the README now lists every required bootstrap evidence file, and
  each file has been captured under `reviews/PHASE-03/evidence/`.

## P3-V3: Freshness checks allowed weak evidence and ledger false positives

- Severity: medium
- Evidence: the freshness gate required accepted operation mnemonics to appear,
  but did not require exactly 18 operation rows, did not reject duplicate rows,
  did not enforce that unsupported rows still ended as `Gap`, and treated
  arbitrary nonempty evidence files as sufficient.
- Status: fixed
- Disposition: `check-doc-freshness.sh` now requires exactly one row for each
  accepted Felt mnemonic, exactly 18 operation rows, explicit missing
  `Data.Felt`/`InterpModel` plus `Gap` status for unmodeled operations, and
  expected success markers in the captured Phase 3 evidence files.

## P3-V4: Quality-gates evidence validation was self-recursive

- Severity: medium
- Evidence: after P3-V3, `scripts/check-llzk-quality-gates.sh` failed while
  regenerating `reviews/PHASE-03/evidence/quality-gates.txt` because the
  wrapper runs `check-doc-freshness.sh` before it has printed its own final
  `Phase 3 harness gates completed.` marker.
- Status: fixed
- Disposition: the wrapper now sets `VEIR_QUALITY_GATES_RUNNING=1` for its
  internal freshness run. That run still validates all other evidence markers
  and defers only the still-being-written quality-gates completion markers.
  A standalone freshness run after the wrapper validates the completed
  `quality-gates.txt` file.
