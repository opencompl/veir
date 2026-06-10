# Phase 3: Felt Operation Semantics Gap Ledger

Status: completed; superseded by Phase 4
Last reviewed: 2026-06-06
Repository: veir
Companion phase file: ../../../llzk-lean/docs/phases/PHASE-03-felt-op-gap-ledger.md

## Objective

Create a source-grounded ledger that maps every accepted LLZK Felt operation to
VeIR's current syntax support, semantic model, rewrite/proof coverage, and known
gaps.

This phase is a documentation and gate phase. It sets the exact target for later
operation-porting, differential, and certificate work without changing Felt
semantics yet.

## Starting State

- VeIR HEAD at Phase 3 bootstrap:
  `0c5280de5715dc0fa518e7e3782e784a5962d4d8`.
- llzk-lean HEAD at Phase 3 bootstrap:
  `617702beadfbad6be784945e2bd98e8a788d357c`.
- Accepted VeIR pin consumed by llzk-lean:
  `d4cc1bf2d31beeca17eb2e8c9c7181d04af013a3`.
- Accepted LLZK source remote:
  `git@github.com:project-llzk/llzk-lib.git`.
- Accepted LLZK source commit:
  `db922857bc5a88a9107627ef6b36a8b5e57bc5c2`.
- Local `../llzk-lib` checkout remains stale at
  `30b0fa1eb77de154ff60c13fa88ef286d8b01c65`; Phase 3 source facts must use
  the accepted commit through `git show`.
- Phase 2 source gates pass and prove the accepted 18-op LLZK Felt source set
  plus field registry.
- Current VeIR semantic model covers `const`, `add`, `sub`, `mul`, and `neg`.
  The LLZK source also defines `pow`, `div`, `uintdiv`, `sintdiv`, `umod`,
  `smod`, `inv`, `bit_and`, `bit_or`, `bit_xor`, `bit_not`, `shl`, and `shr`.
- Current worktree is dirty from Phase 2 close-out documentation/harness fixes
  and separate pre-existing root/skill documentation edits. These are not Phase
  3 semantic implementation evidence.

## Non-Goals

- Do not implement missing Felt operation semantics in this phase.
- Do not add or change Felt rewrite proofs in this phase.
- Do not change the accepted llzk-lean VeIR dependency pin.
- Do not claim Strategy A differential acceptance.
- Do not implement the Strategy E runtime MLIR matcher.
- Do not treat stale `../llzk-lib` worktree files as source truth.

## Artifacts To Create Or Update

- `docs/harness/FELT_OP_GAPS.md`: canonical operation coverage and gap ledger.
- `docs/harness/CURRENT.md`: move the active phase to Phase 3.
- `docs/harness/SOURCES.md`: record the Phase 3 ledger as trusted local source.
- `docs/harness/GATES.md`: document the Phase 3 documentation gate.
- `scripts/harness/check-doc-freshness.sh`: require the Phase 3 phase file,
  review workspace, and operation-gap ledger.
- `reviews/PHASE-03/{request.md,findings.md,disposition.md,adversarial-review.md,evidence/}`:
  adversarial review workspace.

## Gates To Implement

- `scripts/harness/check-doc-freshness.sh` fails if Phase 3 docs or review
  workspace files are missing, if
  `docs/harness/FELT_OP_GAPS.md` is missing, or if the ledger omits any accepted
  LLZK Felt mnemonic.
- `scripts/harness/verify-llzk-source.sh --llzk-lib ../llzk-lib` continues to
  pass, proving the operation ledger is grounded in the accepted LLZK source.
- `scripts/harness/doctor.sh --companion-llzk-lean ../llzk-lean` continues to
  pass, proving llzk-lean still consumes the accepted VeIR pin.
- `scripts/check-llzk-quality-gates.sh` continues to pass.
- `lake build` succeeds after documentation changes.

## Review Requirements

- Every operation-coverage claim must cite an exact local source file or the
  accepted LLZK source ledger.
- The reviewer must verify that the 18 LLZK Felt op mnemonics are all present
  in `docs/harness/FELT_OP_GAPS.md`.
- The reviewer must verify that missing semantics are framed as gaps, not as
  parity.
- The reviewer must verify that Phase 3 does not smuggle in semantic
  implementation changes.
- Disposition every finding before closing the phase.

## Done Criteria

- `docs/harness/FELT_OP_GAPS.md` records all 18 accepted LLZK Felt operations.
- The ledger distinguishes supported VeIR semantic-model operations from
  missing or unclassified operations.
- The ledger records the current rewrite/proof surface without claiming parity
  for operations that are not modeled.
- `check-doc-freshness.sh`, `verify-llzk-source.sh`, companion pin checks, and
  `lake build` pass.
- Phase 3 review artifacts contain fresh adversarial evidence.
