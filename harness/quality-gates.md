# Quality gates

Automated and manual checks that defend against the failure modes
encountered during the 2026-05-15 → 2026-05-17 session
(`SESSION_RETRO_2026-05-17.md`). Each gate names the bug class it
prevents.

These complement (not replace) `harness/evaluation-criteria.md` —
that doc defines "done"; this doc defines "what gates the definition
of done relies on, and how each is enforced."

---

## §1. Gate: differential test before declaring a Symbol-bearing port done

**Prevents**: Gotcha 3-class bug (wrong attribute encoding shipped
silently). Cost paid in this session: 2 port bugs + ~20 min triage.

**How**:
- Any dialect with a `Symbol` trait or `SymbolRefAttr`-bearing op
  must have a corresponding differential test that *parses through
  `llzk-opt`* (not just runs `veir-opt` on its own output).
- The differential test runs as part of the per-dialect port checklist
  (`harness/dialect-port-checklist.md` Phase 6). If `llzk-opt` is on
  `$PATH` (or `$LLZK_OPT` is set), the diff must pass before the port
  ships. If `llzk-opt` is missing, the diff stays UNSUPPORTED and the
  port can still ship — but the next time `llzk-opt` is available,
  the diff is required to pass or be XFAIL'd with a documented reason.
- Differential tests use `// REQUIRES: llzk-opt` to skip on hosts
  without it. Use `// XFAIL: llzk-opt` only when the divergence is
  documented in `coverage.md` and gated on another phase
  (e.g. "needs `function.def` wrapper, lifts at Phase G.1").

**Enforcement**: PR review + the lit suite. CI (see §6) when active.

---

## §2. Gate: no new `sorry` or `axiom` in proof files

**Prevents**: silent bitrot in the verified-pass story. The existing
~179 `sorry`s in `Veir/Passes/` are legacy and tolerated, but new
proof files in `Veir/Passes/<Dialect>/Proofs.lean` and
`Veir/Data/<Dialect>/` must be clean.

**How**:
- Every commit that adds or modifies a file under
  `Veir/Passes/*/Proofs.lean`, `Veir/Data/*/`, or new files anywhere
  under `Veir/Dialects/LLZK/` must contain no `sorry` or `axiom`
  keyword in *non-comment* code (any modifier: `public`, `private`,
  `protected`, `noncomputable`). The canonical check is
  `scripts/check-llzk-quality-gates.sh` which strips Lean comments
  (line `--` and block `/- ... -/` / `/-- ... -/`) before grepping.
- The pass-implementation files (`Veir/Passes/<Dialect>/Combine.lean`,
  etc.) may use `sorry` for rewriter precondition discharge — that's
  the established pattern (see `harness/coverage.md` §Verification
  machinery, "Pattern preconditions discharged" row). But the *proof
  file* is held to the higher bar.
- Phase F (regions) implementation may temporarily introduce
  `axiom`s during prototyping; each must be paired with a removal
  plan (cf. `Veir/Dominance.lean`'s 9 axioms that exist by design but
  are tracked in §Verification machinery).

**Enforcement**: pre-commit reminder in `harness/checkpoint-protocol.md`
§3 (Build gates). CI when active.

---

## §3. Gate: `harness/coverage.md` reflects code state

**Prevents**: doc/code drift. Caught twice by audit agents this
session (stale test counts; misleading "shape checks" phrasing).

**How**:
- Per `harness/coverage.md` §Maintenance protocol: any commit that
  changes a row's status updates `harness/coverage.md` in the same
  commit. Tooling enforcement: a CI check that diffs `Veir/Dialects/LLZK/`
  and `Test/LLZK/` against `coverage.md`'s rows; flags rows that
  reference code paths that no longer exist or fail to mention paths
  that do.
- Build/lit counts in `plan.md` and `harness/coverage.md` and
  `baseline.txt` must reconcile. The single source of truth is the
  most recent `baseline.txt` entry. CI can grep the count out of
  `baseline.txt` and check it matches anywhere else it's referenced.

**Enforcement**: PR review + `harness/evaluation-criteria.md` §A.4
(Coverage and notes). CI when active.

---

## §4. Gate: pre-flight cache check before a Nix build

**Prevents**: 24-hour LLVM source compile when Cachix doesn't actually
hold the variant we asked for.

**How**:
- Before kicking off `nix build '.#<target>'`, run:
  ```bash
  nix path-info --derivation '.#<target>' --json 2>/dev/null \
    | jq -r 'keys[]' \
    | xargs nix store ping --substituters 'https://veridise-public.cachix.org' 2>&1 \
    | head
  ```
  or simpler:
  ```bash
  nix build '.#<target>' --dry-run 2>&1 | grep -E "would be (fetched|built)"
  ```
  If the `--dry-run` output includes any "would be built" lines for
  LLVM/MLIR/clang, abort and try a different variant (`.#mlir` is
  most likely to be cached separately).
- Record the time-to-build of any variant you do build in
  `harness/differential.md` §3.1, so the next person knows what to
  expect.

**Enforcement**: documented in `harness/differential.md` §3.1.

---

## §5. Gate: audit agent run at the end of every batch

**Prevents**: accumulated small issues (style inconsistencies,
docstring drift, missing invalid.mlir pairs). Caught real issues
twice this session (BoolAssertProperties silent coercion; phrasing
ambiguity).

**How**:
- After every "tier batch" or every 3-5 ports, spawn a focused audit
  agent with the brief in `harness/audit-agent-prompt.md` (to be
  created — see §10). The prompt should reference the specific files
  changed since the last audit and ask for real/nit/drift/no-issues
  categories.
- Audit findings either become commits (fixes) or rows in
  `harness/porting-notes.md` (lessons). Never silently ignored.

**Enforcement**: included as Phase 7.5 in
`harness/dialect-port-checklist.md` for tier-batch close-out.

---

## §6. Gate: CI workflow

**Prevents**: regressions discoverable only by manual runs.

**Status**: ✅ established 2026-05-17. Two workflows now cover this:

- **Upstream `.github/workflows/lean_action_ci.yml`** (pre-existing)
  runs `lake build`, `lake test`, and `uv run lit Test/`. This already
  exercises the LLZK ports' identity + invalid + verified-pass tests
  on every push/PR.
- **`.github/workflows/llzk-quality-gates.yml`** (added 2026-05-17)
  runs `scripts/check-llzk-quality-gates.sh` — a pure-text Python
  check (no Lean build needed) enforcing gates §2, §3, §7 from this
  doc. Fast (~5s on CI).

Still NOT covered:
- A separate manual-dispatch workflow for differential testing. Open
  question because building `llzk-opt` in CI without robust Cachix
  coverage takes ~24h. Could be: weekly schedule + Cachix-only mode
  (skip if cache misses). Deferred.

---

## §7. Gate: pushed tags match local tags

**Prevents**: milestone tags that exist locally but not on origin
(e.g., `verif-felt-combine-v2` was created locally and discovered to
be unpushed only when the user asked).

**How**:
- After tagging, always push with `git push --tags`. Or, set
  `git config --global push.followTags true` to auto-push annotated
  tags with their commit.
- Add to `harness/checkpoint-protocol.md` §5 (Merge protocol) as an
  explicit post-tag step.

**Enforcement**: `harness/checkpoint-protocol.md` §5.

---

## §8. Gate: bash scripts are tested in both verbose and quiet modes

**Prevents**: `set -e` + `[[ ... ]] && cmd` class of silent failure
(the `log()` bug in `llzk-diff.sh`).

**How**:
- Any new bash script in `scripts/` should have a 3-line smoke test
  that runs it with `VEIR_DIFF_VERBOSE=0` and `VEIR_DIFF_VERBOSE=1`
  (or equivalent flags) on a known-good input, and asserts both exit
  0.
- Avoid `[[ ... ]] && cmd` patterns under `set -e`. Use explicit
  `if`. This is documented inline in `scripts/llzk-diff.sh`'s
  `log()` definition; new scripts should follow.

**Enforcement**: PR review for new scripts.

---

## §9. Gate: Phase F design note before Phase F implementation

**Prevents**: regions / symbol-table architecture being implemented
piecemeal without a coherent design.

**Status**: ✅ established 2026-05-17 — `harness/regions-design.md`
lands the design. Key surprise documented there: structural region
support is already in VEIR's verified IR; the design narrows to
what semantic invariants + consumer dialects to add. Estimate
revised from 3-6 weeks to 2-4 weeks (Alternative B, recommended).

**Enforcement**: Phase F.2–F.5 implementation commits must reference
`harness/regions-design.md` §8 sub-phase numbers.

---

## §10. Gate: per-batch agent audit prompt

**Prevents**: ad-hoc audit briefs that miss areas. Codifies the
audit-agent recipe.

**Status**: ✅ established 2026-05-17 — `harness/audit-agent-prompt.md`
captures the template that worked twice this session, with
substitution checklist and response-handling protocol.

**Enforcement**: PR review for tier-batch close-out; checklist item
in `harness/dialect-port-checklist.md` Phase 8.

---

## Roll-up: which gates would have caught each session bug?

| Bug | Gate that catches it |
|---|---|
| Gotcha 3 wrong (sym_name as @x) | §1 (differential as port gate) |
| 24h Nix build | §4 (pre-flight cache check) |
| BoolAssertProperties silent attr coercion | §5 (audit agent) |
| Stale coverage counts | §3 (coverage consistency) |
| `verif-felt-combine-v2` tag unpushed | §7 (pushed tags) |
| `[[ ... ]] && cmd` silent abort | §8 (script smoke test) |

All six caught by some gate. The session's improvement is making
those gates explicit and enforceable.

---

## Open gate items

- Differential CI workflow with cache-only build: deferred until
  there's a tractable answer to the 24h-cold-build problem.

All other gates are established as of 2026-05-17.
