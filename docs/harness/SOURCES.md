# Source Ledger

Last reviewed: 2026-06-06

## Trusted Local Sources

| Source | Ref or retrieval | Use |
|---|---:|---|
| `docs/phases/PHASE-01-pins-and-repro.md` | local file, 2026-06-05 | Phase 1 objective, artifacts, gates, done criteria |
| Accepted VeIR pin | `d4cc1bf2d31beeca17eb2e8c9c7181d04af013a3` | Dependency commit llzk-lean must consume |
| Accepted VeIR branch | `felt-review-structural-close` | Remote branch containing the accepted commit |
| Accepted VeIR remote | `https://github.com/project-llzk/veir.git` | Canonical source repository for the accepted pin |
| Companion `llzk-lean/lakefile.toml` | local file, 2026-06-05 | Declared companion `VeIR` dependency pin |
| Companion `llzk-lean/lake-manifest.json` | local file, 2026-06-05 | Resolved companion `VeIR` dependency pin |
| Companion `.lake/packages/VeIR` | clean checkout at accepted pin | Actual dependency state used by llzk-lean |
| `scripts/harness/verify-companion-pin.sh` | local file, 2026-06-05 | Phase 1 companion pin agreement and cleanliness gate |
| `docs/phases/PHASE-02-llzk-source-truth.md` | local file, 2026-06-06 | Phase 2 source-truth objective, artifacts, gates, and done criteria |
| `docs/harness/LLZK_SOURCE.md` | local file, 2026-06-06 | Accepted LLZK Felt source ledger |
| Accepted LLZK source commit | `db922857bc5a88a9107627ef6b36a8b5e57bc5c2` | Exact `llzk-lib` source commit for Phase 2 Felt source facts |
| Accepted LLZK source ref | `../llzk-lib origin/main` | Fetched source ref selected for Phase 2 |
| Accepted LLZK field registry | `lib/Util/Field.cpp` at `db922857bc5a88a9107627ef6b36a8b5e57bc5c2` | Built-in field registry facts |
| Accepted LLZK Felt ops | `include/llzk/Dialect/Felt/IR/Ops.td` at `db922857bc5a88a9107627ef6b36a8b5e57bc5c2` | Felt op mnemonic ledger |
| `scripts/harness/verify-llzk-source.sh` | local file, 2026-06-06 | Phase 2 LLZK source-truth gate |
| `scripts/check-llzk-quality-gates.sh` | local file, 2026-06-05 | Strict compatibility wrapper |

Evidence for the dirty bootstrap state and the refreshed clean state is
captured under `reviews/PHASE-01/evidence/`.

## External Sources

The accepted remote branch was checked with `git ls-remote origin
refs/heads/felt-review-structural-close` and recorded under
`reviews/PHASE-01/evidence/accepted-remote-branch.txt`.

No web page, issue, or mutable branch name is trusted without the exact commit
hash above. For LLZK source facts, `origin/main` is accepted only through the
exact commit `db922857bc5a88a9107627ef6b36a8b5e57bc5c2`.

## Contextual Non-Canonical Material

These files and references are useful context but are not canonical Phase 1 pin
evidence unless a future review revalidates a specific claim:

- `REVIEW.md`
- `FOLLOWUP.md`
- `baseline.txt`
- Source comments pointing at deleted `harness/coverage.md`,
  `harness/differential.md`, `harness/porting-notes.md`,
  `harness/regions-design.md`, or `plan.md`
- Historical branch/date references to `llzkfelt_test1` in archived evidence or
  old notes
- Local `../llzk-lib` worktree files while the worktree remains at
  `30b0fa1eb77de154ff60c13fa88ef286d8b01c65`
