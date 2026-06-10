# Felt Operation Gap Ledger

Last reviewed: 2026-06-10

## Source Basis

- Accepted LLZK source ledger: `docs/harness/LLZK_SOURCE.md`.
- Accepted LLZK source commit:
  `db922857bc5a88a9107627ef6b36a8b5e57bc5c2`.
- Accepted LLZK source remote:
  `git@github.com:project-llzk/llzk-lib.git`.
- Current VeIR source for algebraic Felt semantics:
  `Veir/Data/Felt/Basic.lean`.
- Current VeIR source for runtime-value Felt semantics proof of concept:
  `Veir/Passes/Felt/InterpModel.lean`.
- Current VeIR source for verified rewrite patterns:
  `Veir/Passes/Felt/Combine.lean`,
  `Veir/Passes/Felt/Proofs.lean`, and
  `Veir/Passes/Felt/RewriteLemmas.lean`.

## Phase 3 Rule

This ledger is not a semantic parity claim. It is the current gap map that a
future implementation phase must use before adding operations, differential
inputs, or certificates.

Any row that moves from `gap` to `covered` must have source evidence, a build,
and an adversarial review disposition.

## Current Operation Coverage

| LLZK mnemonic | Accepted LLZK source | VeIR semantic model | VeIR rewrite/proof status | Phase 3 status |
|---|---|---|---|---|
| `const` | `Ops.td`, `Attrs.td`, `Ops.cpp`, fold tests | `Data.Felt.const`, `InterpModel.interpretConst` | Used by rewrite patterns and proofs as constant input/result | Covered baseline |
| `add` | `Ops.td`, `Ops.cpp`, fold tests | `Data.Felt.add`, `InterpModel.interpretAdd` | Multiple verified patterns over add, including `right_identity_zero_add` and `constant_fold_add` | Covered with known LLZK modular-reduction caveat |
| `sub` | `Ops.td`, `Ops.cpp`, fold tests | `Data.Felt.sub`, `InterpModel.interpretSub` | Verified patterns include `self_subtraction_to_zero`, `constant_fold_sub`, and telescoping rewrites | Covered with known LLZK modular-reduction caveat |
| `mul` | `Ops.td`, `Ops.cpp`, fold tests | `Data.Felt.mul`, `InterpModel.interpretMul` | Verified patterns include `right_identity_one_mul`, `right_zero_mul`, `constant_fold_mul`, and `assoc_const_fold_mul` | Covered with known LLZK modular-reduction caveat |
| `neg` | `Ops.td`, `Ops.cpp`, fold tests | `Data.Felt.neg`, `InterpModel.interpretNeg` | Verified patterns include `constant_fold_neg`, `add_neg_to_zero`, and `neg_neg_to_self` | Covered with known LLZK modular-reduction caveat |
| `pow` | `Ops.td`, `Ops.cpp`, fold tests | Missing from `Data.Felt` and `InterpModel` | No verified VeIR rewrite/proof coverage | Gap |
| `div` | `Ops.td`, `Ops.cpp`, fold tests | Missing from `Data.Felt` and `InterpModel` | No verified VeIR rewrite/proof coverage | Gap |
| `uintdiv` | `Ops.td`, `Ops.cpp`, fold tests | Missing from `Data.Felt` and `InterpModel` | No verified VeIR rewrite/proof coverage | Gap |
| `sintdiv` | `Ops.td`, `Ops.cpp`, fold tests | Missing from `Data.Felt` and `InterpModel` | No verified VeIR rewrite/proof coverage | Gap |
| `umod` | `Ops.td`, `Ops.cpp`, fold tests | Missing from `Data.Felt` and `InterpModel` | No verified VeIR rewrite/proof coverage | Gap |
| `smod` | `Ops.td`, `Ops.cpp`, fold tests | Missing from `Data.Felt` and `InterpModel` | No verified VeIR rewrite/proof coverage | Gap |
| `inv` | `Ops.td`, `Ops.cpp`, fold tests | Missing from `Data.Felt` and `InterpModel` | No verified VeIR rewrite/proof coverage | Gap |
| `bit_and` | `Ops.td`, `Ops.cpp`, fold tests | Missing from `Data.Felt` and `InterpModel` | No verified VeIR rewrite/proof coverage | Gap |
| `bit_or` | `Ops.td`, `Ops.cpp`, fold tests | Missing from `Data.Felt` and `InterpModel` | No verified VeIR rewrite/proof coverage | Gap |
| `bit_xor` | `Ops.td`, `Ops.cpp`, fold tests | Missing from `Data.Felt` and `InterpModel` | No verified VeIR rewrite/proof coverage | Gap |
| `bit_not` | `Ops.td`, `Ops.cpp`, fold tests | Missing from `Data.Felt` and `InterpModel` | No verified VeIR rewrite/proof coverage | Gap |
| `shl` | `Ops.td`, `Ops.cpp`, fold tests | Missing from `Data.Felt` and `InterpModel` | No verified VeIR rewrite/proof coverage | Gap |
| `shr` | `Ops.td`, `Ops.cpp`, fold tests | Missing from `Data.Felt` and `InterpModel` | No verified VeIR rewrite/proof coverage | Gap |

## Known Constraints

- LLZK folds require matching registered field names and use
  `lib/Util/Field.cpp::reduce`; VeIR's current algebraic proofs are over
  `ZMod p` and its runtime proof-of-concept stores canonical `Nat` values only
  in `InterpModel`.
- The current verified rewrite set is not the same thing as complete operation
  semantics. Most accepted LLZK Felt operations have no VeIR semantic model.
- Phase 3 may refine this ledger and its gates, but must not mark a gap covered
  without source evidence and review disposition.
