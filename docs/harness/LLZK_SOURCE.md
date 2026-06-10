# LLZK Felt Source Ledger

Last reviewed: 2026-06-10

## Accepted Source

| Item | Value |
|---|---|
| Repository | `../llzk-lib` |
| Remote | `git@github.com:project-llzk/llzk-lib.git` |
| Accepted ref | `origin/main` |
| Accepted commit | `db922857bc5a88a9107627ef6b36a8b5e57bc5c2` |
| Retrieval form | `git -C ../llzk-lib show db922857bc5a88a9107627ef6b36a8b5e57bc5c2:<path>` |

The local `../llzk-lib` worktree is stale at
`30b0fa1eb77de154ff60c13fa88ef286d8b01c65`. Phase 2 source truth uses fetched
`origin/main` at the accepted commit above and reads files through `git show`,
not through the stale worktree checkout.

## Source Files

| Path at accepted commit | Use |
|---|---|
| `include/llzk/Dialect/Felt/IR/Ops.td` | Felt op mnemonic ledger |
| `include/llzk/Dialect/Felt/IR/Types.td` | Felt type syntax ledger |
| `include/llzk/Dialect/Felt/IR/Attrs.td` | Felt attribute syntax ledger |
| `include/llzk/Dialect/Felt/IR/OpInterfaces.td` | Felt op interface ledger |
| `lib/Dialect/Felt/IR/Ops.cpp` | Felt folder implementation ledger |
| `lib/Util/Field.cpp` | Built-in field registry and reduction source |
| `test/Dialect/Felt/felt_arith_pass.llzk` | Accepted Felt op syntax examples |
| `test/Dialect/Felt/felt_arith_fail.llzk` | Accepted Felt verifier failures |
| `test/Dialect/Felt/felt_const_fold.llzk` | Accepted Felt fold examples |
| `test/Dialect/Felt/felt_spec_pass.llzk` | Accepted field-spec syntax examples |
| `test/Dialect/Felt/types_pass.llzk` | Accepted Felt type syntax examples |
| `unittests/IR/FeltFoldTests.cpp` | Accepted unit-level fold behavior |

The stale local worktree must not be used for source evidence unless it is
explicitly checked out to the accepted commit.

## Felt Ops

`include/llzk/Dialect/Felt/IR/Ops.td` at the accepted commit defines these
Felt op mnemonics, in source order:

- `const`
- `add`
- `sub`
- `mul`
- `pow`
- `div`
- `uintdiv`
- `sintdiv`
- `umod`
- `smod`
- `neg`
- `inv`
- `bit_and`
- `bit_or`
- `bit_xor`
- `bit_not`
- `shl`
- `shr`

The accepted source does not define `nondet` or `mod` in the Felt dialect at
this ref.

## Field Registry

`lib/Util/Field.cpp::initKnownFields` at the accepted commit defines:

| Field | Prime |
|---|---:|
| `bn128` | `21888242871839275222246405745257275088548364400416034343698204186575808495617` |
| `bn254` | `21888242871839275222246405745257275088548364400416034343698204186575808495617` |
| `grumpkin` | `21888242871839275222246405745257275088696311157297823662689037894645226208583` |
| `babybear` | `2013265921` |
| `goldilocks` | `18446744069414584321` |
| `mersenne31` | `2147483647` |
| `koalabear` | `2130706433` |

## Verification

Run:

```bash
scripts/harness/verify-llzk-source.sh --llzk-lib ../llzk-lib
```

The gate reads source through `git show` at the accepted commit, checks the
`origin` remote URL and `origin/main`, verifies every ledgered source file is
present, checks representative syntax and fold facts from the ledgered files,
verifies the Felt op mnemonic list above, verifies the field registry, and
checks VeIR's local `feltPrime` mirror.
