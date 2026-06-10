# Phase 6 Review Request

Repository: veir
Created: 2026-06-10

Review the Phase 6 Strategy A divergence burn-down bootstrap and first
implementation target.

Scope:

- Phase 6 is active and starts from companion llzk-lean's Phase 5 clean-pin
  exact-polarity corpus.
- Phase 5 findings are closed before Phase 6 implementation work starts.
- The bootstrap does not claim full Strategy A acceptance.
- Companion clean-pin evidence remains separated from workspace overrides.
- The first implementation target updates `scripts/llzk-diff.sh` so canonical
  mode runs `felt-combine,dce`, then companion llzk-lean consumes
  `a0bb2fc8e6d38ab068247dfc6506ba63f5feb953` as the clean pin.
- Companion llzk-lean reclassifies the DCE-only registered add/sub/mul
  constant-fold divergences while keeping the canonical corpus at
  `21 pass (incl. expected-diverge), 0 fail`.
