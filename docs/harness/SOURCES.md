# Source Ledger

Last reviewed: 2026-06-05

## Trusted Local Sources

| Source | Ref or retrieval | Use |
|---|---:|---|
| `docs/phases/PHASE-00-harness-reset.md` | local file, 2026-06-05 | Phase 0 objective, artifacts, gates, done criteria |
| VeIR repository HEAD | `4b0978bddec0` | Bootstrap VeIR source state |
| llzk-lean repository HEAD | `ea2363f87bcc` | Companion source state |
| llzk-lean `lakefile.toml` | local file, 2026-06-05 | Declared `VeIR` dependency pin |
| llzk-lean `lake-manifest.json` | local file, 2026-06-05 | Resolved `VeIR` dependency pin |
| llzk-lean `.lake/packages/VeIR` | `09d5f00f0d2b`, dirty | Actual dependency checkout state |
| `scripts/llzk-diff.sh` | local file, 2026-06-05 | Differential helper contract and exit codes |
| `scripts/check-llzk-quality-gates.sh` | local file, 2026-06-05 | Strict compatibility wrapper plus explicit local-only opt-out |

Evidence for the bootstrap state is captured under
`reviews/PHASE-00/evidence/`.

## External Sources

No external web source is trusted as canonical for Phase 0. The harness records
local refs and local command output only. Upstream LLZK, MLIR, and Lean docs may
be consulted for future phases, but any claim imported from them must be added
to this ledger with a retrieval date and exact URL or commit.

## Stale Historical Material

These files and references are useful context but are not canonical Phase 0
evidence unless a future review revalidates a specific claim:

- `REVIEW.md`
- `FOLLOWUP.md`
- `baseline.txt`
- Source comments pointing at deleted `harness/coverage.md`,
  `harness/differential.md`, `harness/porting-notes.md`,
  `harness/regions-design.md`, or `plan.md`
- Historical branch/date references to `llzkfelt_test1`

When using any of these, cite the exact local file and explain whether the claim
was revalidated against current refs.
