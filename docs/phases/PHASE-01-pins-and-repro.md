# Phase 1: Reproducible Pins

Status: completed; superseded by Phase 2
Last reviewed: 2026-06-05
Repository: veir
Companion phase file: ../../../llzk-lean/docs/phases/PHASE-01-pins-and-repro.md

## Objective

Make the VeIR state consumed by llzk-lean explicit, clean, and reproducible.

At the end of this phase, llzk-lean must not depend on a dirty
`.lake/packages/VeIR` checkout, and reviewers must be able to prove which VeIR
commit is being used without inspecting hidden local state.

## Starting State

- veir HEAD at Phase 1 bootstrap: `039068b68552bb37f1a887ec509e9b9111d4d54a`.
- llzk-lean HEAD at Phase 1 bootstrap:
  `336a5a221ae79d00e5d1346e09341232bdc4323d`.
- llzk-lean Lake files currently pin VeIR to:
  `09d5f00f0d2b4a8710afbe53dfdd7cf468578a04`.
- llzk-lean dependency checkout is currently dirty:
  - modified `Veir/Passes/Felt/Combine.lean`
  - modified `Veir/Passes/Felt/Proofs.lean`
  - untracked `Veir/Passes/Felt/RewriteLemmas.lean`
- Phase 0 harness gates exist and must remain the active safety net while this
  phase is implemented.

## Non-Goals

- Do not port additional Felt operations.
- Do not change rewrite semantics.
- Do not repair Strategy A differential behavior except where needed to report
  pin state accurately.
- Do not treat a local checkout path as the source of truth unless the chosen
  mode explicitly documents that it is exploratory.

## Artifacts To Create Or Update

- `docs/harness/CURRENT.md`: record Phase 1 as active once implementation
  starts, and list the accepted VeIR pin mode.
- `docs/harness/SOURCES.md`: add the chosen VeIR source commit, branch, and
  remote URL as trusted Phase 1 inputs.
- `docs/harness/GATES.md`: add reproducible-pin gates.
- `docs/harness/PINS.md`: document the intended VeIR pin, allowed dependency
  modes, update procedure, and rollback procedure.
- `scripts/harness/verify-companion-pin.sh`: compare this repo's intended VeIR
  commit and remote URL against llzk-lean's `lakefile.toml`,
  `lake-manifest.json`, and `.lake/packages/VeIR` checkout.
- `reviews/PHASE-01/{request.md,findings.md,disposition.md,evidence/}`:
  adversarial review workspace for the pin transition.

## Gates To Implement

- `scripts/harness/doctor.sh` continues to pass locally.
- `scripts/harness/verify-companion-pin.sh --companion-llzk-lean ../llzk-lean`
  fails while llzk-lean pins `09d5f00f0d2b` or has a dirty dependency checkout.
- The same gate passes only when:
  - llzk-lean `lakefile.toml` and `lake-manifest.json` agree on the VeIR rev;
  - llzk-lean `lakefile.toml` and `lake-manifest.json` use the accepted VeIR
    remote URL;
  - `lake-manifest.json` has `type: "git"` and records the accepted commit in
    both `rev` and `inputRev`;
  - `.lake/packages/VeIR` is clean;
  - `.lake/packages/VeIR` HEAD equals the manifest rev/inputRev;
  - the rev is the explicitly accepted Phase 1 VeIR commit.
- `scripts/check-llzk-quality-gates.sh` preserves strict companion checking and
  cannot report acceptance when the dependency is dirty or mismatched.

## Review Requirements

- Capture exact command output under `reviews/PHASE-01/evidence/`.
- Cite the local VeIR commit, the llzk-lean Lake files including source
  URL/type/inputRev, and dependency checkout status in every review.
- Include one adversarial check from the veir side and one from the llzk-lean
  side.
- Disposition every finding before closing the phase.

## Done Criteria

- The accepted VeIR commit is recorded in both repositories.
- llzk-lean Lake files pin that exact commit.
- llzk-lean `.lake/packages/VeIR` is clean and at that exact commit.
- VeIR companion pin verification passes from the veir root.
- llzk-lean strict doctor passes without exploratory mode.
- Phase 1 review artifacts exist and contain fresh evidence.
