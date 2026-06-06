# Phase 1 Findings

Repository: veir

## P1-V1 - Companion dirty dependency state needed a dedicated strict gate

Severity: Critical

At bootstrap, llzk-lean's `.lake/packages/VeIR` checkout was dirty while Lake
metadata still named `09d5f00f0d2b4a8710afbe53dfdd7cf468578a04`. VeIR needed a
companion-facing gate that checked the declared pin, manifest pin, dependency
HEAD, and dependency cleanliness together.

Evidence:

- `evidence/dependency-status-before.txt`
- `evidence/verify-companion-pin-before.txt`
- `evidence/check-llzk-quality-gates-before.txt`

Disposition: fixed in `reviews/PHASE-01/disposition.md`.

## P1-V2 - Accepted VeIR source needed remote evidence

Severity: High

A local VeIR checkout path cannot be the source of truth for Phase 1
acceptance. The accepted commit must be recorded with branch and remote
evidence.

Evidence:

- `evidence/accepted-remote-branch.txt`
- `evidence/accepted-commit.txt`
- `docs/harness/PINS.md`

Disposition: fixed in `reviews/PHASE-01/disposition.md`.

## P1-V3 - Companion source URL was documented but not enforced

Severity: High

The accepted companion pin mode records `https://github.com/project-llzk/veir.git`,
but the first companion gate only checked the commit rev. A companion checkout
could name another VeIR URL and still pass if `.lake/packages/VeIR` was locally
at the accepted commit.

Evidence:

- `evidence/adversarial-url-spoof-after.txt`

Disposition: fixed in `reviews/PHASE-01/disposition.md`.

## P1-V4 - Companion manifest inputRev was not checked

Severity: Medium

The first companion gate checked `lake-manifest.json` `rev` but not `inputRev`,
allowing internally inconsistent manifest state to pass strict verification.

Evidence:

- `evidence/adversarial-inputrev-after.txt`

Disposition: fixed in `reviews/PHASE-01/disposition.md`.

## P1-V5 - Phase file status lagged the active harness state

Severity: Low

`docs/phases/PHASE-01-pins-and-repro.md` still said `Status: bootstrap` after
the harness docs marked Phase 1 active.

Disposition: fixed in `reviews/PHASE-01/disposition.md`.

## Open Findings

No open Critical or High findings remain for Phase 1 pin reproducibility.
