# Harness Gates

Last reviewed: 2026-06-05

## Gate Inventory

| Gate | Command | Expected Phase 0 behavior | What it proves |
|---|---|---|---|
| Local doctor | `scripts/harness/doctor.sh` | Passes from VeIR root | Repo layout, bootstrap HEAD, required tools, canonical docs, scripts, and skills are present |
| Companion doctor | `scripts/harness/doctor.sh --companion-llzk-lean ../llzk-lean` | Fails in strict mode while the llzk-lean Lake `VeIR` checkout is dirty | Dirty dependency state is visible and cannot silently count as acceptance evidence |
| Exploratory companion doctor | `scripts/harness/doctor.sh --mode exploratory --companion-llzk-lean ../llzk-lean` | Passes with warnings | Local investigation can proceed while still reporting the dirty dependency |
| Doc freshness | `scripts/harness/check-doc-freshness.sh` | Passes when canonical docs and review disposition exist | Phase metadata and canonical harness docs are present and reviewed |
| Skill validation | `scripts/harness/validate-skills.sh` | Passes when every repo-local skill has required sections | Repo-local skills are concise and auditable |
| Compatibility wrapper | `scripts/check-llzk-quality-gates.sh` | Runs local harness gates and a strict companion check via `LLZK_LEAN_ROOT` or `../llzk-lean`; fails while the companion dependency is dirty | The old gate no longer reports success when companion state is hidden |
| Local-only wrapper | `VEIR_HARNESS_LOCAL_ONLY=1 scripts/check-llzk-quality-gates.sh` | Passes local layout checks but prints that it is not acceptance evidence | Local-only use is explicit and cannot be mistaken for full Phase 0 acceptance |

## Non-Claims

Phase 0 does not prove:

- Felt semantic parity.
- Strategy A differential coverage.
- Strategy E certificate coverage.
- Full lit-suite or `lake test` acceptance.

Those claims require future phase files and fresh evidence.
