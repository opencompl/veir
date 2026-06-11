# VeIR Felt Drop-In Roadmap Role

Last reviewed: 2026-06-11

This repo is the implementation side of the Felt drop-in replacement effort.
The project-wide roadmap lives in the companion repository at
`../llzk-lean/docs/drop-in-roadmap.md` in the shared workspace.

## Current Role

VEIR currently provides:

- LLZK Felt IR representation, parser/printer support, verifier shape checks,
  and the `felt-combine` pass.
- Fifteen Felt rewrite patterns over `const`, `add`, `sub`, `mul`, and `neg`.
- Lean arithmetic proofs and sorry-free structural rewrite precondition proofs
  for those 15 patterns.
- A standalone value-level Felt interpreter proof-of-concept in
  `Veir/Passes/Felt/InterpModel.lean`.
- The differential driver `scripts/llzk-diff.sh`, consumed by llzk-lean's
  clean-pin harness.

VEIR does not yet provide a complete drop-in Felt replacement:

- 13 accepted LLZK Felt operations still lack semantic models and interpreter
  cases in VEIR.
- The current `felt-combine` pass includes verified algebraic rewrites that the
  C++ LLZK canonicalizer does not perform. Those are useful verified
  optimizations, but they must be separated from the C++-parity adoption
  profile.
- There is no whole-program rewrite semantic theorem.
- There is no direct `llzk-opt` replacement integration point.

## Replacement Profiles

VEIR should expose two Felt profiles for the drop-in work:

- **C++-parity profile.** Adoption and regression baseline. This profile should
  match the accepted LLZK C++ folder/canonicalization behavior as closely as
  possible so users can opt in, compare, and fall back cleanly.
- **Enhanced VEIR profile.** Improvement path. This profile may run additional
  verified rewrites from `felt-combine`, but every intentional divergence from
  C++ LLZK must have differential evidence, executable side conditions,
  semantic justification, and downstream compatibility review.

The current nonconstant algebraic divergences are not automatically defects.
They are blockers only for the parity profile. They become compelling
enhanced-profile features only after their runtime semantics and replacement
toolchain behavior are tied down.

## VeIR Work Required For Drop-In

1. **Add profile separation.** Keep `felt-combine` as the stronger verified
   optimization pass, but add or configure a C++-parity profile that matches
   the C++ Felt folder behavior first.
2. **Port the missing folder semantics.** Implement the C++ fold behavior for
   `pow`, `div`, `uintdiv`, `sintdiv`, `umod`, `smod`, `inv`, `bit_and`,
   `bit_or`, `bit_xor`, `bit_not`, `shl`, and `shr`, including no-fold side
   conditions.
3. **Model runtime side conditions.** Field registry lookup, registered-field
   preconditions, signed representative conversion, bitwidth, division by zero,
   and `NotFieldNative` scope must be executable conditions, not prose.
4. **Attach auditable rewrite metadata.** If Strategy E continues, certificate
   shapes and side conditions should be derived from or colocated with the
   executable patterns so llzk-lean does not hand-maintain a parallel catalog.
5. **Strengthen semantic statements.** Arithmetic identities in
   `Veir/Passes/Felt/Proofs.lean` are supporting lemmas. Drop-in claims need
   value-level runtime lemmas tied to the operations, matchers, result
   constructors, and side conditions that actually run.

## Non-Claims

The current VeIR fork does not claim:

- full LLZK Felt semantic parity;
- complete coverage of all C++ Felt folders;
- runtime LLZK rewrite verification;
- replacement of all of `llzk-opt`;
- whole-program semantic preservation for `felt-combine`.

Those claims become available only through the roadmap gates in the companion
`llzk-lean` document.
