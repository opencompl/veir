# Current Harness State

Last reviewed: 2026-06-05

## Active Phase

- Active phase: Phase 0, harness reset.
- Phase bootstrap file: `docs/phases/PHASE-00-harness-reset.md`.
- Companion repository: `../llzk-lean`.
- Companion phase file:
  `../llzk-lean/docs/phases/PHASE-00-harness-reset.md`.

## Refs

- VeIR bootstrap HEAD: `4b0978bddec0`.
- llzk-lean bootstrap HEAD: `ea2363f87bcc`.
- llzk-lean Lake `VeIR` dependency pin: `09d5f00f0d2b4a8710afbe53dfdd7cf468578a04`.
- llzk-lean Lake `VeIR` dependency checkout observed at:
  `09d5f00f0d2b`.

These refs are Phase 0 acceptance inputs. If any ref changes, update this file,
`docs/harness/SOURCES.md`, and the review evidence before treating the harness
as current.

## Dirty-State Policy

The llzk-lean Lake dependency checkout is expected to be dirty at bootstrap:

- `Veir/Passes/Felt/Combine.lean`
- `Veir/Passes/Felt/Proofs.lean`
- `Veir/Passes/Felt/RewriteLemmas.lean`

Strict harness runs must fail when this dirty dependency is present. Exploratory
runs may acknowledge the dirtiness by passing `--mode exploratory`, but those
runs are not release or acceptance evidence.

## Toolchain Assumptions

- `git` is required for all harness checks.
- `lake` is required for Lean project checks.
- `uv` and FileCheck tooling are needed for the full lit suite, but Phase 0 does
  not claim lit-suite acceptance.
- `llzk-opt` is not required for the local VeIR harness doctor. It is required
  for differential checks that exercise LLZK output.

## Known Hazards

- Historical VeIR comments and review notes still reference deleted files such
  as `harness/coverage.md`, `harness/differential.md`,
  `harness/porting-notes.md`, `harness/regions-design.md`, and `plan.md`.
  Those references are stale unless `docs/harness/SOURCES.md` revalidates a
  specific claim.
- `scripts/check-llzk-quality-gates.sh` was stale at bootstrap because it read
  missing harness files. In Phase 0 it is a strict wrapper around the current
  harness scripts. It auto-checks `../llzk-lean` when present and fails while
  that companion dependency is dirty. `VEIR_HARNESS_LOCAL_ONLY=1` is an
  explicit non-acceptance layout check.
- `scripts/llzk-diff.sh` is useful for differential investigation, but Phase 0
  does not claim Strategy A acceptance coverage.

## Acceptance Rule

Phase 0 is current only when:

- `scripts/harness/doctor.sh` passes from the VeIR root.
- `scripts/harness/check-doc-freshness.sh` passes from the VeIR root.
- `scripts/harness/validate-skills.sh` passes from the VeIR root.
- A strict companion run,
  `scripts/harness/doctor.sh --companion-llzk-lean ../llzk-lean`, reports the
  dirty llzk-lean dependency instead of hiding it.
- `scripts/check-llzk-quality-gates.sh` fails in strict mode on the known dirty
  companion state and only exits 0 for local-only mode when
  `VEIR_HARNESS_LOCAL_ONLY=1` is set.
