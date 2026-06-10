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

Disposition: fixed by selecting VeIR commit
`d4cc1bf2d31beeca17eb2e8c9c7181d04af013a3`, pushing it to
`project-llzk/veir`, and updating llzk-lean's Lake metadata plus clean
dependency checkout to that commit.

## P2-V5 - Accepted LLZK source remote is stale and ungated

Severity: High

`docs/harness/LLZK_SOURCE.md` recorded
`git@github.com:Veridise/llzk-lib.git`, but the checked and fetched source
repository uses `git@github.com:project-llzk/llzk-lib.git`. The source gate
checked only the commit and `origin/main`, so it could not catch a remote
provenance mismatch.

Disposition: fixed by recording
`git@github.com:project-llzk/llzk-lib.git` in the source ledger and requiring
that exact `origin` URL in `scripts/harness/verify-llzk-source.sh` and doc
freshness evidence.

## P2-V6 - Source ledger files were listed but not all gated

Severity: Medium

The source ledger listed `OpInterfaces.td`, Felt lit tests, and unit tests, but
the source gate only checked a subset of paths and parsed only ops/types/field
registry facts deeply. That made the ledger broader than the mechanical gate.

Disposition: fixed by checking every ledgered source path at the accepted
commit and adding representative checks for Felt attrs, op interfaces, folder
source, lit tests, and unit tests.
