# Review Protocol

Last reviewed: 2026-06-06

## Scope

Every phase must have a review workspace under `reviews/<PHASE>/` containing:

- `request.md`
- `findings.md`
- `disposition.md`
- `adversarial-review.md`
- `evidence/`

Each claim in canonical harness docs must cite either a local source in
`docs/harness/SOURCES.md`, command output under `evidence/`, or an explicitly
trusted external source added to the source ledger.

## Severity

- Critical: harness can report acceptance while hiding dirty or mismatched
  source state.
- High: a gate reports success while skipping a required check.
- Medium: canonical docs are ambiguous, stale, or not reproducible.
- Low: wording, formatting, or convenience issues that do not affect evidence.

## Disposition

Findings must be marked as one of:

- `fixed`
- `accepted-risk`
- `deferred`
- `invalid`

A phase cannot close with undispositioned Critical or High findings.
