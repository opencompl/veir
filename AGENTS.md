# VeIR Agent Entry

This repository is the project-llzk fork of VeIR. Treat
`docs/harness/CURRENT.md` as the active source of truth before doing Felt,
LLZK, or differential-harness work.

Required first checks:

- Read `docs/harness/CURRENT.md`, `docs/harness/GATES.md`, and
  `docs/harness/SOURCES.md`; read `docs/harness/PINS.md` before touching
  companion pin or Lake metadata.
- Run `scripts/harness/doctor.sh` from the repository root.
- If the task involves llzk-lean, also run:
  `scripts/harness/doctor.sh --companion-llzk-lean ../llzk-lean`.
- For pin, review, or phase-close work involving llzk-lean, run:
  `scripts/harness/verify-companion-pin.sh --companion-llzk-lean ../llzk-lean`.

Policy:

- Do not treat historical `harness/*.md`, `plan.md`, or deleted parity notes as
  canonical unless `docs/harness/SOURCES.md` explicitly revalidates them.
- Do not accept dirty `llzk-lean/.lake/packages/VeIR` state as release or review
  evidence. Use `--mode exploratory` only for local investigation and report it.
- Keep phase evidence under the active phase directory
  (`reviews/PHASE-01/evidence/` for the current pin phase) when changing
  canonical harness docs, pins, or gates.
