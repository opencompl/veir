# Phase 10: Toolchain Replacement Spike

Status: bootstrap; not harness-active
Last reviewed: 2026-06-11
Repository: veir
Companion phase file: ../../../llzk-lean/docs/phases/PHASE-10-toolchain-replacement-spike.md

## Objective

Support the first executable Felt replacement spike and define the VEIR pass
surface needed for both the C++-parity profile and the enhanced VEIR profile.

## Starting State

- The current external-driver smoke uses `scripts/llzk-diff.sh`.
- `.llzk` custom assembly is lowered through LLZK before VEIR runs.
- Canonical smoke currently exercises `veir-opt -p=felt-combine,dce`.
- `felt-combine` is stronger than the C++ LLZK canonicalizer for current
  nonconstant algebraic rewrites.

## Required Implementation Direction

- Add or configure a C++-parity Felt profile that omits enhanced algebraic
  rewrites not performed by C++ LLZK.
- Keep the enhanced `felt-combine` profile available as the improvement path.
- Make profile selection explicit in scripts/docs so differential evidence
  states which profile was exercised.
- Continue tying proof claims to executable rewrite conditions rather than to
  standalone arithmetic identities.

## Non-Goals

- Do not weaken the current enhanced `felt-combine` profile just to obtain
  parity.
- Do not make undocumented output differences part of the replacement claim.
- Do not claim parser/frontend replacement while LLZK still owns lowering.

## Gates To Implement

- llzk-lean Phase 10 smoke:
  `scripts/harness/phase10-toolchain-smoke.sh`.
- Targeted proof build after proof/doc edits:
  `lake build Veir.Passes.Felt.Proofs`.
- Later implementation gate: a profile-selectable `veir-opt` invocation whose
  parity mode avoids the current nonconstant algebraic expected divergences.

## Bootstrap Finding

The first llzk-lean Phase 10 smoke found that workspace VEIR, unlike the
accepted llzk-lean clean pin, no longer removed dead Felt constants after
`felt-combine` folded `registered_add_fold.llzk`. The cause was the newer DCE
side-effect API: Felt operations were not listed as pure and therefore defaulted
to side-effecting.

`Veir/GlobalOpInfo.lean` now marks `.felt _` as side-effect-free, which restores
the expected `felt-combine,dce` behavior for Felt constants and arithmetic in
the external-driver smoke.

## Done Criteria

- VEIR can be invoked in a documented Phase 10 smoke path.
- The parity/enhanced profile split is represented in VEIR implementation or
  command-line configuration.
- Any promoted enhanced-profile divergence has differential evidence,
  semantic justification, and downstream compatibility notes.
