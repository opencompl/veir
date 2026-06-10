# Harness Gates

Last reviewed: 2026-06-10

## Gate Inventory

| Gate | Command | Expected behavior | What it proves |
|---|---|---|---|
| Strategy A Phase 6 bootstrap | `scripts/harness/check-doc-freshness.sh` | Passes only when Phase 6 is active, the Phase 6 review workspace exists, Phase 5 is marked completed, exact-polarity guard evidence remains present, and the source ledger records the Phase 6 phase file plus local test infrastructure | Phase 6 starts from the companion clean-pin exact-polarity corpus without claiming full Strategy A acceptance |
| Felt operation gap ledger | `scripts/harness/check-doc-freshness.sh` | Passes only when the Phase 3 review workspace exists, `docs/harness/FELT_OP_GAPS.md` is present, exactly 18 accepted LLZK Felt mnemonic rows appear, and every unsupported operation row is still marked as a gap | Phase 5 continues from the complete documented operation-gap map instead of implicit or stale coverage claims |
| LLZK source truth | `scripts/harness/verify-llzk-source.sh --llzk-lib ../llzk-lib` | Passes only when the accepted LLZK source remote, commit, and `origin/main` match, the source ledger records every gated source file, the accepted Felt op set and representative syntax/fold facts match the ledger, and VeIR `feltPrime` matches the accepted field registry | Phase 2 source facts are exact-ref and exact-remote based, and VeIR's field registry mirror matches LLZK source |
| Local doctor | `scripts/harness/doctor.sh` | Passes from VeIR root, warning only if current HEAD differs from bootstrap input or no companion was supplied | Repo layout, tools, canonical docs, scripts, skills, and current ref visibility are present |
| Companion pin verification | `scripts/harness/verify-companion-pin.sh --companion-llzk-lean ../llzk-lean` | Passes only when llzk-lean Lake file URLs/revs, manifest `type`/`inputRev`, and dependency checkout all match the accepted commit and the checkout is clean | llzk-lean is not consuming hidden dependency edits or a spoofed source |
| Companion doctor | `scripts/harness/doctor.sh --companion-llzk-lean ../llzk-lean` | Runs local checks and strict companion pin verification | The strict VeIR harness sees the companion pin state |
| Doc freshness | `scripts/harness/check-doc-freshness.sh` | Passes when current phase docs, Phase 3 review workspace, required Phase 3 evidence outputs, Phase 2 source evidence, dated harness docs, and expected success markers in the evidence are present | Phase metadata, review state, and closeout evidence are current |
| Skill validation | `scripts/harness/validate-skills.sh` | Passes when repo-local skills have required sections | Repo-local skills are concise and auditable |
| Compatibility wrapper | `scripts/check-llzk-quality-gates.sh` | Runs local harness gates and strict companion pin verification through `LLZK_LEAN_ROOT` or `../llzk-lean` | The legacy entry point cannot report success while the companion pin is dirty or mismatched |
| Local-only wrapper | `VEIR_HARNESS_LOCAL_ONLY=1 scripts/check-llzk-quality-gates.sh` | Passes local layout checks but prints that it is not acceptance evidence | Local-only use is explicit and cannot be mistaken for full acceptance |
| Phase 4 workspace differential gate | `LLZK_OPT=/nix/store/awcw2wiypa02sl5vx4xm06qwji68xz3h-llzk-debug-2.0.0/bin/llzk-opt VEIR_DIFF=../veir/scripts/llzk-diff.sh ./differential/run-differential.sh --canonicalize differential/corpus` | Runs workspace VeIR's canonicalization-aware diff script over the companion reviewed seed corpus | Initial Phase 4 evidence exists, but remains workspace evidence until llzk-lean's clean VeIR dependency pin consumes this script |
| Phase 5 clean-pin implementation gate | `LLZK_OPT=/nix/store/awcw2wiypa02sl5vx4xm06qwji68xz3h-llzk-debug-2.0.0/bin/llzk-opt ./differential/run-differential.sh --canonicalize differential/corpus` | Runs the canonical differential through llzk-lean's default clean `.lake/packages/VeIR` dependency script with no `VEIR_DIFF` override | The canonicalization-aware diff script has been consumed through a clean dependency pin and supports the Phase 6 divergence burn-down baseline |
| Phase 6 divergence burn-down baseline | same as Phase 5 clean-pin implementation gate | Companion llzk-lean remains `21 pass (incl. expected-diverge), 0 fail` until a reviewed Phase 6 change reduces or reclassifies a divergence | Prevents Phase 6 from starting on a weakened Strategy A baseline |

## Reproducible-Pin Failures

## LLZK Source-Truth Failures

`scripts/harness/check-doc-freshness.sh` must fail if:

- `docs/phases/PHASE-06-strategy-a-divergence-burndown.md` is missing.
- `docs/phases/PHASE-05-strategy-a-pin-and-corpus.md` is not marked completed
  and superseded by Phase 6.
- `docs/phases/PHASE-04-strategy-a-differential.md` is missing.
- `docs/phases/PHASE-03-felt-op-gap-ledger.md` is missing.
- `docs/harness/CURRENT.md` does not name Phase 6 as active.
- `docs/harness/SOURCES.md` does not record `scripts/llzk-diff.sh`,
  `docs/phases/PHASE-06-strategy-a-divergence-burndown.md`, Phase 5
  exact-polarity guard evidence,
  `/nix/store/awcw2wiypa02sl5vx4xm06qwji68xz3h-llzk-debug-2.0.0/bin/llzk-opt`,
  and `/home/alh/llvm-project`.
- `docs/harness/FELT_OP_GAPS.md` is missing.
- `docs/harness/FELT_OP_GAPS.md` has anything other than exactly 18 operation
  rows, or omits or duplicates any accepted LLZK Felt mnemonic:
  `const`, `add`, `sub`, `mul`, `pow`, `div`, `uintdiv`, `sintdiv`, `umod`,
  `smod`, `neg`, `inv`, `bit_and`, `bit_or`, `bit_xor`, `bit_not`, `shl`,
  `shr`.
- `docs/harness/FELT_OP_GAPS.md` stops marking `pow`, `div`, `uintdiv`,
  `sintdiv`, `umod`, `smod`, `inv`, `bit_and`, `bit_or`, `bit_xor`,
  `bit_not`, `shl`, or `shr` as missing from `Data.Felt`/`InterpModel` and as
  `Gap`.
- `reviews/PHASE-03` lacks a request, findings file, disposition file,
  adversarial-review file, or evidence README.
- `reviews/PHASE-04` lacks a request, findings file, disposition file,
  adversarial-review file, or evidence README.
- `reviews/PHASE-05` lacks a request, findings file, disposition file,
  adversarial-review file, or evidence README.
- `reviews/PHASE-06` lacks a request, findings file, disposition file,
  adversarial-review file, or evidence README.
- `reviews/PHASE-03/evidence` lacks nonempty Phase 3 outputs for doc
  freshness, LLZK source truth, companion pin verification, companion doctor,
  quality gates, skill validation, lake build, or adversarial review.
- Phase 3 evidence files are nonempty but omit their expected success markers,
  including `0 fail` summaries, `Build completed successfully`, strict companion
  doctor success in the quality-gates output, and adversarial proof that no
  missing-operation semantics or VeIR source changes were introduced.
- While `scripts/check-llzk-quality-gates.sh` is generating
  `quality-gates.txt`, the freshness gate defers validation of the wrapper's
  own completion markers; a standalone freshness run after the wrapper validates
  the completed `quality-gates.txt` file.
- Phase 4 bootstrap docs claim Strategy A pass-pipeline acceptance before the
  reviewed canonicalization command and corpus evidence exist.
- Canonicalization evidence omits the accepted `LLZK_OPT` path, omits the
  reviewed workspace script or clean pin bump, or leaves divergences
  unclassified.
- Phase 5 bootstrap docs claim clean-pin Strategy A acceptance before the
  default dependency canonicalization command and corpus evidence exist.
- Phase 6 bootstrap docs claim full Strategy A acceptance, omit the Phase 5
  exact-polarity baseline, or fail to mark Phase 5 completed.

`scripts/harness/verify-llzk-source.sh --llzk-lib ../llzk-lib` must fail if:

- `../llzk-lib` is missing or not a git checkout.
- `../llzk-lib origin` is not
  `git@github.com:project-llzk/llzk-lib.git`.
- The accepted source commit
  `db922857bc5a88a9107627ef6b36a8b5e57bc5c2` is unavailable.
- `../llzk-lib origin/main` differs from the accepted source commit.
- `docs/harness/LLZK_SOURCE.md` does not record the accepted source remote,
  accepted source commit, or every ledgered source file.
- `include/llzk/Dialect/Felt/IR/Ops.td` does not define the accepted 18-op
  Felt ledger: `const`, `add`, `sub`, `mul`, `pow`, `div`, `uintdiv`,
  `sintdiv`, `umod`, `smod`, `neg`, `inv`, `bit_and`, `bit_or`, `bit_xor`,
  `bit_not`, `shl`, `shr`.
- Any ledgered Felt source file is missing from the accepted commit.
- The ledgered attribute, interface, folder, lit, or unit-test source facts
  checked by the gate disappear or stop matching the accepted source.
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
  `220cd215579b435c3c22ce86b34a3f4ce2ca276e`.
- Companion `lake-manifest.json` records a VeIR `inputRev` other than
  `220cd215579b435c3c22ce86b34a3f4ce2ca276e`.
- Companion `.lake/packages/VeIR` HEAD differs from the manifest rev.
- Companion `.lake/packages/VeIR` has any modified, deleted, staged, or
  untracked file.

## Non-Claims

The current harness does not prove:

- Felt semantic parity.
- Complete Strategy A differential coverage beyond the current 15-pattern Felt
  rewrite matrix.
- Strategy E certificate coverage.
- Full lit-suite or `lake test` acceptance.
- Missing Felt operation semantics beyond the registry source facts.
- Phase 6 divergence burn-down has not yet reduced expected divergences. Phase 5
  clean-pin corpus evidence expands the Felt rewrite-pattern matrix but does not
  expand certificates, complete all Strategy A corpus coverage, or port missing
  operations. Phase 4 workspace evidence remains historical seed evidence; Phase
  6 implementation evidence must preserve the clean dependency baseline.
