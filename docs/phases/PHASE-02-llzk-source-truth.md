# Phase 2: LLZK Source Truth And Field Registry Parity

Status: active
Last reviewed: 2026-06-06
Repository: veir
Companion phase file: ../../../llzk-lean/docs/phases/PHASE-02-llzk-source-truth.md

## Objective

Establish a fresh, source-grounded LLZK Felt dialect ledger and bring VeIR's
field registry model into parity with the accepted LLZK source.

This phase is about source truth and registry parity. It is the prerequisite
for later verifier, differential, missing-op, and certificate work.

## Starting State

- VeIR HEAD at Phase 2 bootstrap:
  `d52917ca4a57c4094b1aa61dd413aca4e1c2a56e`.
- llzk-lean HEAD at Phase 2 bootstrap:
  `6b4a7ec3aa38e2da7e1de23fb347b5c2cbac6386`.
- Accepted VeIR pin consumed by llzk-lean:
  `d52917ca4a57c4094b1aa61dd413aca4e1c2a56e`.
- Local `llzk-lib` checkout after fetch:
  - local `main`: `30b0fa1eb77de154ff60c13fa88ef286d8b01c65`
  - fetched `origin/main`: `db922857bc5a88a9107627ef6b36a8b5e57bc5c2`
  - local checkout is behind `origin/main` and must not be treated as current
    source truth without an explicit checkout or `git show origin/main:...`.
- Fetched `llzk-lib origin/main` changes Felt source truth relative to local
  `main`:
  - `lib/Util/Field.cpp` separates `bn128`/`bn254` from `grumpkin`.
  - `include/llzk/Dialect/Felt/IR/Attrs.td` lists `grumpkin` as built-in.
  - `include/llzk/Dialect/Felt/IR/Ops.td` documents shift semantics.
- Current VeIR `Veir/Passes/Felt/InterpModel.lean` must map `bn128` and
  `bn254` to the BN scalar, include `grumpkin`, and include `koalabear`.

## Non-Goals

- Do not port additional Felt operations in this phase.
- Do not prove missing rewrite semantics.
- Do not claim Strategy A differential acceptance.
- Do not implement the Strategy E runtime MLIR matcher.
- Do not merge or reset `../llzk-lib` unless the action is deliberate and
  evidence is recorded.

## Artifacts To Create Or Update

- `docs/harness/LLZK_SOURCE.md`: source ledger for LLZK Felt files, exact
  commits, accepted branch, and retrieval commands.
- `docs/harness/SOURCES.md`: add Phase 2 LLZK source refs.
- `docs/harness/GATES.md`: add source-truth and registry-parity gates.
- `Veir/Passes/Felt/InterpModel.lean`: update `feltPrime` to match the accepted
  LLZK field registry.
- `scripts/harness/verify-llzk-source.sh`: verify the expected LLZK source ref,
  Felt op set, and built-in field registry facts.
- `reviews/PHASE-02/{request.md,findings.md,disposition.md,evidence/}`:
  adversarial review workspace for the source-truth transition.

## Source Files To Ledger

Use `../llzk-lib` as the local repository, but use fetched `origin/main` as the
initial source truth until a newer source ref is deliberately selected.

- `include/llzk/Dialect/Felt/IR/Ops.td`
- `include/llzk/Dialect/Felt/IR/Types.td`
- `include/llzk/Dialect/Felt/IR/Attrs.td`
- `lib/Dialect/Felt/IR/Ops.cpp`
- `lib/Util/Field.cpp`
- `test/Dialect/Felt/*`

## Field Registry Target

The initial accepted LLZK source ref defines these built-in fields:

- `bn128`:
  `21888242871839275222246405745257275088548364400416034343698204186575808495617`
- `bn254`:
  `21888242871839275222246405745257275088548364400416034343698204186575808495617`
- `grumpkin`:
  `21888242871839275222246405745257275088696311157297823662689037894645226208583`
- `babybear`: `2013265921`
- `goldilocks`: `18446744069414584321`
- `mersenne31`: `2147483647`
- `koalabear`: `2130706433`

## Gates To Implement

- `scripts/harness/verify-llzk-source.sh --llzk-lib ../llzk-lib` fails if
  `../llzk-lib origin/main` is unavailable or if the accepted source ref is not
  recorded.
- The source gate extracts or checks the 18 Felt op mnemonics:
  `const`, `add`, `sub`, `mul`, `pow`, `div`, `uintdiv`, `sintdiv`, `umod`,
  `smod`, `neg`, `inv`, `bit_and`, `bit_or`, `bit_xor`, `bit_not`, `shl`,
  `shr`.
- The source gate fails if `feltPrime` disagrees with the accepted built-in
  field registry.
- `lake build` succeeds in VeIR after the registry update.
- llzk-lean pin verification still passes after the VeIR change is selected
  and propagated through Phase 1 pin machinery.

## Review Requirements

- Every source-truth claim must cite an exact `llzk-lib` commit and file path.
- Review evidence must include `git -C ../llzk-lib rev-parse HEAD origin/main`
  and a diff or extraction showing relevant Felt source facts.
- The reviewer must explicitly check for stale local `llzk-lib` use.
- The reviewer must verify that `bn128`/`bn254` no longer use the grumpkin
  scalar in VeIR and that `grumpkin`/`koalabear` are present.
- Disposition every finding before closing the phase.

## Done Criteria

- `docs/harness/LLZK_SOURCE.md` records the accepted LLZK Felt source ref and
  files.
- VeIR `feltPrime` matches the accepted LLZK built-in field registry.
- A source-truth gate catches the old `bn128`/`bn254` value and missing
  `grumpkin` or `koalabear` entries.
- VeIR builds.
- llzk-lean still consumes a clean, deliberate VeIR pin after the registry
  update.
- Phase 2 review artifacts contain fresh adversarial evidence.
