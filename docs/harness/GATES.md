# Harness Gates

Last reviewed: 2026-06-06

## Gate Inventory

| Gate | Command | Expected behavior | What it proves |
|---|---|---|---|
| LLZK source truth | `scripts/harness/verify-llzk-source.sh --llzk-lib ../llzk-lib` | Passes only when the accepted LLZK source commit is available, `origin/main` equals the accepted commit, the source ledger records the accepted commit, the accepted Felt op set matches the ledger, and VeIR `feltPrime` matches the accepted field registry | Phase 2 source facts are exact-ref based and VeIR's field registry mirror matches LLZK source |
| Local doctor | `scripts/harness/doctor.sh` | Passes from VeIR root, warning only if current HEAD differs from bootstrap input or no companion was supplied | Repo layout, tools, canonical docs, scripts, skills, and current ref visibility are present |
| Companion pin verification | `scripts/harness/verify-companion-pin.sh --companion-llzk-lean ../llzk-lean` | Passes only when llzk-lean Lake file URLs/revs, manifest `type`/`inputRev`, and dependency checkout all match the accepted commit and the checkout is clean | llzk-lean is not consuming hidden dependency edits or a spoofed source |
| Companion doctor | `scripts/harness/doctor.sh --companion-llzk-lean ../llzk-lean` | Runs local checks and strict companion pin verification | The strict VeIR harness sees the companion pin state |
| Doc freshness | `scripts/harness/check-doc-freshness.sh` | Passes when Phase 1 docs and review evidence are present | Phase metadata and review state are current |
| Skill validation | `scripts/harness/validate-skills.sh` | Passes when repo-local skills have required sections | Repo-local skills are concise and auditable |
| Compatibility wrapper | `scripts/check-llzk-quality-gates.sh` | Runs local harness gates and strict companion pin verification through `LLZK_LEAN_ROOT` or `../llzk-lean` | The legacy entry point cannot report success while the companion pin is dirty or mismatched |
| Local-only wrapper | `VEIR_HARNESS_LOCAL_ONLY=1 scripts/check-llzk-quality-gates.sh` | Passes local layout checks but prints that it is not acceptance evidence | Local-only use is explicit and cannot be mistaken for full Phase 1 acceptance |

## Reproducible-Pin Failures

## LLZK Source-Truth Failures

`scripts/harness/verify-llzk-source.sh --llzk-lib ../llzk-lib` must fail if:

- `../llzk-lib` is missing or not a git checkout.
- The accepted source commit
  `db922857bc5a88a9107627ef6b36a8b5e57bc5c2` is unavailable.
- `../llzk-lib origin/main` differs from the accepted source commit.
- `docs/harness/LLZK_SOURCE.md` does not record the accepted source commit or
  `lib/Util/Field.cpp`.
- `include/llzk/Dialect/Felt/IR/Ops.td` does not define the accepted 18-op
  Felt ledger: `const`, `add`, `sub`, `mul`, `pow`, `div`, `uintdiv`,
  `sintdiv`, `umod`, `smod`, `neg`, `inv`, `bit_and`, `bit_or`, `bit_xor`,
  `bit_not`, `shl`, `shr`.
- `lib/Util/Field.cpp::initKnownFields` does not define `bn128`, `bn254`,
  `grumpkin`, `babybear`, `goldilocks`, `mersenne31`, and `koalabear` as
  recorded in `docs/harness/LLZK_SOURCE.md`.
- VeIR `feltPrime` disagrees with the accepted field registry.

`scripts/harness/verify-companion-pin.sh` must fail if:

- Companion `lakefile.toml` and `lake-manifest.json` disagree.
- Companion `lakefile.toml` or `lake-manifest.json` names a VeIR source URL
  other than `https://github.com/project-llzk/veir.git`.
- Companion `lake-manifest.json` does not record VeIR as a `git` dependency.
- Either companion Lake file names a commit other than
  `d4cc1bf2d31beeca17eb2e8c9c7181d04af013a3`.
- Companion `lake-manifest.json` records a VeIR `inputRev` other than
  `d4cc1bf2d31beeca17eb2e8c9c7181d04af013a3`.
- Companion `.lake/packages/VeIR` HEAD differs from the manifest rev.
- Companion `.lake/packages/VeIR` has any modified, deleted, staged, or
  untracked file.

## Non-Claims

Phase 1 does not prove:

- Felt semantic parity.
- Strategy A differential coverage.
- Strategy E certificate coverage.
- Full lit-suite or `lake test` acceptance.
- Missing Felt operation semantics beyond the registry source facts. Phase 2
  does not port additional Felt operations.
