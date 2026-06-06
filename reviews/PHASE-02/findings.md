# Phase 2 Preflight Findings

Repository: veir
Reviewed: 2026-06-06

## P2-V1 - Local llzk-lib checkout is stale relative to fetched origin/main

Severity: Critical

`../llzk-lib` local `main` is at
`30b0fa1eb77de154ff60c13fa88ef286d8b01c65`, while fetched `origin/main` is at
`db922857bc5a88a9107627ef6b36a8b5e57bc5c2`. Phase 2 must use an explicitly
selected source ref, not the stale local worktree by accident.

Disposition: fixed by `docs/harness/LLZK_SOURCE.md` and
`scripts/harness/verify-llzk-source.sh`, which read the accepted ref through
`git show` and warn when the worktree is stale.

## P2-V2 - VeIR feltPrime is stale against current LLZK Field.cpp

Severity: Critical

Fetched `llzk-lib origin/main:lib/Util/Field.cpp` maps `bn128` and `bn254` to
the BN scalar field, adds `grumpkin` as a distinct built-in field, and keeps
`koalabear`. Current VeIR `Veir/Passes/Felt/InterpModel.lean` mapped `bn128`
and `bn254` to the grumpkin scalar and had no `grumpkin` case before Phase 2
edits.

Disposition: fixed by updating `Veir/Passes/Felt/InterpModel.lean` and adding
the source gate.

## P2-V3 - Phase 1 pin reproducibility passes but does not prove source parity

Severity: High

The Phase 1 gates prove llzk-lean consumes a clean VeIR commit. They do not
prove that the VeIR commit's Felt registry or op ledger matches current LLZK
source.

Disposition: fixed by adding the Phase 2 source gate and gate documentation.

## P2-V4 - Phase 1 work is not committed in this workspace

Severity: Medium

Both `veir` and `llzk-lean` contain uncommitted Phase 1 implementation changes.
Phase 2 execution should either commit those changes first or explicitly carry
the dirty state as non-release local work.

Disposition: accepted-risk for this working session. The Phase 2 edits remain
uncommitted and llzk-lean still pins the Phase 1 VeIR commit until a deliberate
commit-and-pin update is requested.
