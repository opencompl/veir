# Phase 1 Review Request

Requested: 2026-06-05
Repository: veir

Review the Phase 1 reproducible-pin transition:

- `docs/phases/PHASE-01-pins-and-repro.md`
- `docs/harness/CURRENT.md`
- `docs/harness/SOURCES.md`
- `docs/harness/GATES.md`
- `docs/harness/PINS.md`
- `scripts/harness/verify-companion-pin.sh`
- `scripts/harness/doctor.sh`
- `scripts/harness/check-doc-freshness.sh`
- `scripts/check-llzk-quality-gates.sh`
- `reviews/PHASE-01/evidence/`

The review should confirm that VeIR can prove which commit llzk-lean consumes,
that companion Lake metadata and dependency checkout agree, and that dirty
companion dependency state cannot pass the strict gates.
