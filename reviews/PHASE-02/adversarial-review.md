# Phase 2 Preflight Adversarial Review

Repository: veir
Reviewed: 2026-06-06

## Checks Run

- Phase 1 companion pin verification passed against `../llzk-lean`.
- Phase 1 compatibility wrapper passed.
- `../llzk-lib` refs were inspected with `git rev-parse HEAD origin/main`.
- `../llzk-lib` local `main` resolves to
  `30b0fa1eb77de154ff60c13fa88ef286d8b01c65`.
- Fetched `../llzk-lib origin/main` resolves to
  `db922857bc5a88a9107627ef6b36a8b5e57bc5c2`.
- Fetched `origin/main` Felt source was inspected through `git show`.

## Result

Phase 1 pin reproducibility is structurally sound, but Phase 2 must treat
`llzk-lib origin/main` at `db922857bc5a88a9107627ef6b36a8b5e57bc5c2` as the
accepted source-truth candidate and fix VeIR's stale field registry before any
semantic parity claim can be trusted.

## Fresh Review After Phase 2 Edits

Reviewed: 2026-06-06

### Findings

- The first source gate proved only that field names and prime strings appeared
  somewhere. It did not prove that `lib/Util/Field.cpp` mapped each field to
  the accepted prime or that VeIR `feltPrime` mirrored those pairs. This would
  have let a stale `bn128`/`bn254` branch pass if the right numbers appeared
  elsewhere.
- llzk-lean cannot claim it consumes the Phase 2 registry update until a clean
  VeIR commit containing the update is selected and propagated through its Lake
  pin.

### Disposition

- Fixed the source gate by checking exact `insert(NAME, PRIME)` source lines and
  exact `feltPrime` field-to-prime branches for all seven accepted built-ins.
- Pin propagation remains pending until llzk-lean updates its accepted VeIR pin
  to the new Phase 2 commit.
