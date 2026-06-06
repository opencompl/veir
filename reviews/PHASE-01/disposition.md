# Phase 1 Disposition

Repository: veir

## P1-V1

Disposition: fixed

`scripts/harness/verify-companion-pin.sh` now checks the companion llzk-lean
Lake files, `.lake/packages/VeIR` HEAD, and dependency cleanliness against the
accepted VeIR commit
`d52917ca4a57c4094b1aa61dd413aca4e1c2a56e`. `scripts/harness/doctor.sh` and
`scripts/check-llzk-quality-gates.sh` preserve strict companion checking.

## P1-V2

Disposition: fixed

The accepted commit, source branch, and remote are recorded in
`docs/harness/SOURCES.md` and `docs/harness/PINS.md`. Remote branch evidence is
captured under `reviews/PHASE-01/evidence/accepted-remote-branch.txt`.

## P1-V3

Disposition: fixed

`scripts/harness/verify-companion-pin.sh` now verifies the companion VeIR `git`
URL in `lakefile.toml` and VeIR `url` in `lake-manifest.json` against
`https://github.com/project-llzk/veir.git`. The URL spoof adversarial probe is
recorded in `evidence/adversarial-url-spoof-after.txt` and exits non-zero as
expected.

## P1-V4

Disposition: fixed

`scripts/harness/verify-companion-pin.sh` now verifies companion
`lake-manifest.json` `inputRev` against the accepted commit. The stale-`inputRev`
adversarial probe is recorded in `evidence/adversarial-inputrev-after.txt` and
exits non-zero as expected.

## P1-V5

Disposition: fixed

`docs/phases/PHASE-01-pins-and-repro.md` now records `Status: active`.

## Closure Rule

Phase 1 is closed only if the final evidence includes:

- `scripts/harness/verify-companion-pin.sh --companion-llzk-lean ../llzk-lean`
- `scripts/harness/doctor.sh --companion-llzk-lean ../llzk-lean`
- `scripts/check-llzk-quality-gates.sh`
- adversarial URL and `inputRev` spoof probes
- `scripts/harness/check-doc-freshness.sh`
- `scripts/harness/validate-skills.sh`
