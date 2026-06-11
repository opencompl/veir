# Phase 9: Drop-In Roadmap And Claim Reset

Status: completed; superseded by Phase 10 bootstrap
Last reviewed: 2026-06-11
Repository: veir
Companion phase file: ../../../llzk-lean/docs/phases/PHASE-09-drop-in-roadmap.md

## Objective

Align the VeIR implementation-side claims with the project-wide Felt drop-in
roadmap after Phase 8 landed in the `project-llzk/veir` fork.

## Starting State

- Workspace VeIR HEAD at bootstrap:
  `42db1ae3cbe76ca6c917501acc8e92a4f01cbc75`.
- `project-llzk/veir#1` is merged into `main` at merge commit
  `45d31a20b4ff10498f7caba3c8b635553cc93dea`.
- `opencompl/veir#829` is closed unmerged.
- VEIR has 15 Felt rewrite patterns over `const`, `add`, `sub`, `mul`, and
  `neg`.
- VEIR does not yet expose a separate C++-parity Felt profile.

## Claim Reset

- Current `felt-combine` is the enhanced VEIR profile seed.
- A separate C++-parity profile is needed for low-risk adoption and debugging.
- Current nonconstant algebraic divergences are parity blockers, but may become
  enhanced-profile features if semantic and downstream claims are established.
- Arithmetic identities in `Veir/Passes/Felt/Proofs.lean` are supporting
  lemmas, not whole-program semantic-preservation claims.

## Non-Goals

- Do not claim complete LLZK Felt semantic parity.
- Do not claim whole-program semantic preservation for `felt-combine`.
- Do not replace all of `llzk-opt`.

## Artifacts Created Or Updated

- `docs/drop-in-roadmap.md`: VeIR-side role in the project-wide roadmap.
- `README.md`: pointer to the roadmap.
- `Veir/Passes/Felt/Proofs.lean`: proof-boundary comment corrected.
- `docs/harness/SOURCES.md`: records the roadmap as planning context, not
  phase acceptance evidence.

## Done Criteria

- VEIR docs distinguish C++ parity from enhanced VEIR improvements.
- VEIR docs state current non-claims.
- Phase 10 has a concrete implementation-side target.
