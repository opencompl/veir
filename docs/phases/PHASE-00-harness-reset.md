# Phase 0: Harness Reset

Status: bootstrap
Last reviewed: 2026-06-05
Repository: veir
Companion phase file: ../../../llzk-lean/docs/phases/PHASE-00-harness-reset.md

## Objective

Replace the current ad hoc agent documentation and quality-gate story with a small,
repo-local harness that is fresh, executable, and explicit about which VeIR,
LLZK, and llzk-lean state is being used.

Phase 0 is a prerequisite for further Felt dialect work. No semantic Felt work
should be treated as accepted until this phase gives agents and reviewers a
reliable source of truth.

## Starting State

- veir HEAD at bootstrap time: `4b0978bddec0`.
- llzk-lean HEAD at bootstrap time: `ea2363f87bcc`.
- llzk-lean Lake dependency `VeIR` at bootstrap time: `09d5f00f0d2b`.
- llzk-lean Lake dependency `VeIR` is dirty at bootstrap time:
  - modified `Veir/Passes/Felt/Combine.lean`
  - modified `Veir/Passes/Felt/Proofs.lean`
  - untracked `Veir/Passes/Felt/RewriteLemmas.lean`
- veir has no repo-local `AGENTS.md`, no skill directory, and no `docs/harness`
  source of truth.
- `scripts/check-llzk-quality-gates.sh` references missing harness files and
  must not be treated as a reliable acceptance gate until repaired.

## Non-Goals

- Do not port additional Felt operations in this phase.
- Do not change Lean proof content except as needed to make harness checks
  inspectable.
- Do not rely on the dirty `llzk-lean/.lake/packages/VeIR` checkout as an
  implicit source of truth.
- Do not turn historical review notes into canonical docs without revalidating
  every claim.

## Artifacts To Create

- `AGENTS.md`: concise entrypoint for agents working in this repository.
- `docs/harness/CURRENT.md`: current active phase, refs, dirty-state policy,
  toolchain assumptions, and known hazards.
- `docs/harness/SOURCES.md`: trusted source ledger with upstream LLZK/MLIR/Lean
  references, commit hashes or retrieval dates, and exact local files used.
- `docs/harness/GATES.md`: executable gate inventory and what each gate proves.
- `docs/harness/REVIEWS.md`: review protocol, severity definitions, and finding
  disposition rules.
- `docs/phases/PHASE_TEMPLATE.md`: template for future phase bootstrap files.
- `reviews/PHASE-00/{request.md,findings.md,disposition.md,evidence/}`:
  adversarial review workspace for this phase.
- `scripts/harness/doctor.sh`: validate refs, dirty state, dependency pins,
  tool availability, and expected repo layout.
- `scripts/harness/check-doc-freshness.sh`: reject stale phase metadata and
  unreviewed canonical-doc changes.
- `scripts/harness/validate-skills.sh`: validate any repo-local skills.

## Skill Infrastructure

Create repo-local skills only when they remove repeated work or encode a
project-specific review protocol. Initial candidates:

- `skills/llzk-felt-source-audit/SKILL.md`
- `skills/lean-axiom-audit/SKILL.md`
- `skills/mlir-differential/SKILL.md`
- `skills/phase-bootstrap/SKILL.md`

Each skill must be concise, include when to use it, point to exact scripts or
references, and have a validation path in `scripts/harness/validate-skills.sh`.

## Gates To Implement

- `scripts/harness/doctor.sh` passes from the veir root.
- `scripts/harness/doctor.sh` detects a dirty or mismatched
  `llzk-lean/.lake/packages/VeIR` dependency when run with the companion repo.
- Existing `scripts/check-llzk-quality-gates.sh` either becomes a truthful gate
  or is demoted/replaced so it cannot emit misleading PASS results.
- Canonical docs list exact refs and explicitly mark stale historical docs.
- A clean reviewer can reproduce the same harness status without relying on
  chat history or hidden local state.

## Review Requirements

- Every Phase 0 claim must cite either a local file, a command output captured
  under `reviews/PHASE-00/evidence/`, or an explicitly trusted external source.
- The reviewer must run the harness gates from a clean shell and record the
  commands used.
- Findings must be dispositioned as fixed, accepted-risk, deferred, or invalid.
- Phase 0 cannot close while known stale docs remain unmarked as stale.

## Done Criteria

- `AGENTS.md` exists and points to canonical harness docs.
- `docs/harness/CURRENT.md` is the single source of truth for active phase,
  refs, and dirty-state policy.
- Harness gates fail on the known dirty dependency state unless explicitly run
  in an exploratory mode.
- Phase 0 review artifacts exist and contain an independent findings pass.
- Future phase bootstrap files can be generated from `PHASE_TEMPLATE.md`.
