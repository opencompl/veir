# Session Playbook — LLZK→Lean/VEIR verification work

> The bootstrap entry point. **One front = one session.** Open a fresh session,
> jump to that front's section, follow it top to bottom. Created 2026-06-01.
>
> Continuity is provided by: (1) the persistent memory file (auto-loaded;
> `llzk-lean-review.md`), (2) this file, (3) `veir/REVIEW.md` +
> `veir/FOLLOWUP.md` + `llzk-lean/docs/REVIEW.md`, (4) feature-branch commits.
> You should not need to re-derive anything — read, then continue.

---

## 0. Shared environment (true for every session)

**Repos & branches**
- `~/LLZK/llzk-lib` — C++ ground truth. **Read-only.** `main`.
- `~/LLZK/veir` — Lean MLIR + Felt port. Branch **`felt-review-structural-close`**.
- `~/LLZK/llzk-lean` — the bridge (Strategy A/E). Branch **`felt-review`**.
- Current accepted llzk-lean VEIR dependency pin:
  `project-llzk/veir@d52917ca4a57c4094b1aa61dd413aca4e1c2a56e`; see
  `docs/harness/PINS.md` and `../llzk-lean/docs/harness/PINS.md`.

**Toolchains / builds (persist on disk — reuse, do not rebuild from scratch)**
- veir pins Lean **v4.30.0-rc2**; llzk-lean pins **v4.30.0**. Both `.lake` build
  trees already exist.
- Mathlib: if a dep needs (re)building, run `lake exe cache get` first (avoids a
  multi-hour source build).
- Prebuilt `llzk-opt`: `/nix/store/awcw2wiypa02sl5vx4xm06qwji68xz3h-llzk-debug-2.0.0/bin/llzk-opt`
  (if gone: `ls /nix/store | grep llzk-debug`).
- MLIR dev (for the C++ checker, Front 4): `/nix/store/6jhpdnnfmwbzv4c8k4nf1vr898dd024w-mlir-debug-20.1.8-dev`
  (`ls /nix/store | grep mlir-debug`); `cmake`: `ls /nix/store | grep cmake-4`; `g++` is on PATH.
- `lean-lsp` MCP server is configured in `~/LLZK/.mcp.json`, pinned to
  `--lean-project-path ~/LLZK/llzk-lean`. If prompted on startup, approve it
  (`/mcp`). It exposes `lean_goal`, `lean_multi_attempt`, `lean_diagnostic_messages`,
  `lean_verify`, `lean_local_search`, etc.

**The fast dev loop (important).** `lean-lsp` operates on **llzk-lean**'s build
(`.lake/packages/VeIR` — the pinned clean dependency copy). That checkout must
stay clean for acceptance work. For exploratory proof iteration, develop in a
scratch `.lean` file in `~/LLZK/llzk-lean` using
`lean_multi_attempt`/`lean_diagnostic_messages`, then transplant the finished
proof into the veir repo and confirm with
`cd ~/LLZK/veir && lake build <module>` (incremental, seconds). Before claiming
review or phase acceptance, run
`cd ~/LLZK/llzk-lean && scripts/harness/verify-pins.sh --workspace-veir ../veir`.
Caveat: the veir build uses rc2; lean-lsp uses final — they have agreed so far,
but the veir build and the strict pin gates are the source of truth.

**Verify Lean (axiom audit).** Build the module, then:
```
cd ~/LLZK/veir
printf 'import Veir.Passes.Felt.Combine\nopen Veir.FeltPass\n#print axioms <name>\n' > /tmp/ax.lean
lake env lean /tmp/ax.lean   # want: [propext, Classical.choice, Quot.sound] — NO sorryAx, NO Veir.WfIRContext.Dom
```

**Delegate proving.** Use the `lean4:sorry-filler-deep` agent (it has the lean-lsp
tools) for intricate precondition discharge; run in background; verify its output
yourself (`#print axioms`) before landing.

**Key artifacts**
- `veir/Veir/Passes/Felt/RewriteLemmas.lean` — reusable lemma library + the
  verified patterns. *This is the asset every Lean front builds on.*
- `veir/REVIEW.md` (§0 = remediation log), `veir/FOLLOWUP.md` (backlog),
  `llzk-lean/docs/REVIEW.md`.

**Per-session protocol (every session)**
1. *Open:* read this front's section + the memory file + the cited `REVIEW.md`
   section. Confirm branch + that `.lake` builds exist + lean-lsp connected.
2. *Work:* one front only. Delegate heavy proofs to agents; coordinate + verify.
3. *Close — Definition of Done:* target builds green; `#print axioms` clean for
   anything claimed verified; update `REVIEW.md`/`FOLLOWUP.md` + the memory file;
   run the relevant strict harness/pin gates; `git commit` on the feature branch
   (no push unless asked). Optionally invoke the `lean4:checkpoint` skill.

**Dependency note:** only one hard edge — **F3 waits on F2's field-model
decision.** F1, F4, F5, F6, F7 are independent and may run in any order / as
parallel sessions.

---

## F1 — Widen the structural close (13 remaining Felt patterns) — ✅ DONE (2026-06-02)

**STATUS: COMPLETE.** All 15/15 patterns sorry-free + axiom-clean (commit
`3fb22d4fc`); verified by `lake build` + `#print axioms` + fresh-agent
adversarial re-review. Section retained below for the recipe/history.

**Goal.** Make the other 13 `Combine.lean` patterns sorry-free + axiom-clean,
mirroring `right_identity_zero_add` (projection) and `constant_fold_add`
(synthesis) already done in `RewriteLemmas.lean`.

**Prereq.** None — `RewriteLemmas.lean` library is ready. No blockers.

**First task (do this before the patterns): generalize `matchOp_inBounds`.**
It is currently `felt.add`-specific (the `decide` that `default.opType ≠ felt.add`).
Add per-opcode in-bounds wrappers `matchMul_inBounds`, `matchSub_inBounds`,
`matchNeg_inBounds`, `matchConst_inBounds` (each `decide`s `default.opType ≠ <that
opcode>`), or generalize to `matchOp_inBounds (opType) (h : default_op ≠ opType)`.
Mirror `matchAdd_inBounds`'s proof.

**The 13, grouped by shape (reuse the matching recipe):**
- *Projection (`replaceValue` + `eraseOp`; copy `right_identity_zero_add`):*
  `right_identity_one_mul`, `neg_neg_to_self`, `add_sub_const_cancel`,
  `sub_add_const_cancel`. Guards needed: region-count, result≠operand.
- *Synthesis, single `createOp` (copy `constant_fold_add`):* `constant_fold_sub`,
  `constant_fold_mul` (+ keep the VC3 field-type guard), `constant_fold_neg`
  (unary — `matchNeg`), `self_subtraction_to_zero`, `right_zero_mul`,
  `add_neg_to_zero`, `add_const_swap`. Guards: region-count, op-has-parent.
- *Synthesis, TWO `createOp`s (harder — sequence two createOp postconditions):*
  `assoc_const_fold_add`, `assoc_const_fold_mul`. Budget extra time; may need a
  `createOp`-then-`createOp` composition lemma.

**Plan.** Chunk ~4–5 patterns per session. Per pattern: develop in a llzk-lean
scratch (reuse `RewriteLemmas` lemmas via `import`), delegate the precondition
discharge to a `sorry-filler-deep` agent, then move the finished def into
`RewriteLemmas.lean` (replacing the matched `Combine.lean` def, which is deleted
and referenced via import — same as the 2 done).

**Verify / DoD.** `cd ~/LLZK/veir && lake build Veir.Passes.Felt.Combine` green;
`#print axioms` on each new pattern shows no `sorryAx`/`Dom`; update `REVIEW.md`
§0 (N of 15 done) + memory; commit.

**Watch for.** New `WfIRContext` gaps beyond the three known (region count,
result≠operand, op-has-parent) → handle with a sound guard, document it.

---

## F2 — Interpreter-semantics keystone (SCOPING SPIKE first) — ✅ DONE (2026-06-02)

**STATUS: COMPLETE.** Memo + go/no-go in `FOLLOWUP.md` §F2; a real axiom-clean
PoC landed (`Veir/Passes/Felt/InterpModel.lean`). **Go on F3 at the value level;
defer the whole-program keystone** (multi-week framework, rests on `Dom` axiom).
Q1 field model DECIDED (name→prime registry + `Nat`-canonical felt value,
Mathlib confined to a bridge file). Section retained below for the original spec.


**Goal of the spike (1 session, do NOT commit to full execution yet):** decide
whether a closed *"this rewrite provably preserves program semantics"* theorem is
reachable for Felt on current VEIR, and at what cost.

**The problem to scope.** `Veir/Interpreter/Basic.lean`'s `interpretOp'` returns
`none` for every `OpCode.felt` (felt is not interpreted). `RuntimeValue` is
`LLVM.Int`/`BitVec`/`reg` — **not `ZMod p`** — and `!felt.type` carries **no
runtime prime** (field-agnostic IR). So there is no canonical runtime meaning to
bridge `Veir.Data.Felt.add` to.

**Spike questions to answer:**
1. Minimal viable Felt interpreter: add a `RuntimeValue.felt`? Over what — a
   fixed prime, a parameterized field, or `ZMod p` with `p` threaded from where?
   (The IR doesn't pin `p`; `FeltConstAttr.fieldType` may name a field but the
   prime isn't in the IR.) What's the least-bad modeling choice?
2. Does proving `interpret(rewrite ctx) = interpret(ctx)` for a peephole need
   `WfIRContext.Dom`? (Likely yes, for use-def reasoning — note no VEIR pass has
   such a theorem today.)
3. Effort estimate for ONE pattern end-to-end (semantic preservation), and
   whether it generalizes.

**Deliverable.** A feasibility memo appended to `veir/FOLLOWUP.md` (new §) +
a go/no-go recommendation. **This gates F3 and the "verified drop-in" end goal**,
so run it early.

**Verify / DoD.** Memo written; if a proof-of-concept fragment is attempted, it
builds; memory + FOLLOWUP updated; commit (docs only unless a real lemma lands).

---

## F3 — Port the missing 13 Felt ops (BLOCKED on F2)

**Goal.** Wire the opcode-only stubs (`div`, `inv`, `pow`, `uintdiv`, `sintdiv`,
`umod`, `smod`, `bit_and/or/xor/not`, `shl`, `shr`) — Properties/OpInfo/matchers/
folds/proofs — i.e. the field- and prime-dependent ops.

**Blocker.** The field/prime model decision from **F2's spike** (these ops need
primality: `inv`/`div`, `modExp` for `pow`, bitwidth for shifts/bit ops). Do not
start until F2 says how the field is modeled.

**Reference.** LLZK's fold semantics are the spec — see `llzk-lib/lib/Dialect/
Felt/IR/Ops.cpp` (`field->reduce`, `field->inv`, `modExp`, `toSigned`) and the
field registry (`Util/Field.cpp`). Mirror `veir/REVIEW.md` §2 faithfulness table.

**Verify / DoD.** Per op: matcher + fold pattern + soundness theorem; build green;
axiom audit; `REVIEW.md` op-coverage table updated; commit.

---

## F4 — Strategy E: real C++ certificate matcher (independent)

**Goal.** Replace the fail-closed stubs `DefaultMatcher::matchOpShape` /
`checkConds` in `llzk-lean/checker/src/CertChecker.cpp` (currently `return false`
under `#ifdef LLZK_HAVE_MLIR`) with real MLIR-backed matching, per the inline
TODO sketch; build with MLIR; then reflective cert derivation + complete catalog.

**Bootstrap.**
```
cd ~/LLZK/llzk-lean/checker
MLIR_DIR=$(ls -d /nix/store/*mlir-debug-20.1.8-dev)/lib/cmake/mlir   # adjust
cmake -B build -DCMAKE_BUILD_TYPE=Debug -DMLIR_DIR="$MLIR_DIR" -DLLVM_DIR=...
cmake --build build && ctest --test-dir build --output-on-failure
```
Read `llzk-lean/docs/strategy-e-certificates.md` + `checker/README.md` first.

**Plan.** (1) get an MLIR-enabled build (sets `LLZK_HAVE_MLIR`); (2) implement
`matchOpShape` (op kind, operands, const value, commutative) and `checkConds`
(the 6 side conditions, using `OperandPath`); (3) test against hand-authored LLZK
MLIR inputs; (4) Lean-side: reflective catalog from `Combine.lean` (kills the
hand-authored drift, finding C2/H1); (5) emit the full 15-pattern catalog.

**Verify / DoD.** `ctest` green incl. real-IR matching tests; catalog matches
emitter (CI `diff`); `strategy-e-certificates.md` + `REVIEW.md` updated; commit
in llzk-lean.

---

## F5 — Strategy A: make the differential real (independent)

**Goal.** Today the harness is parse-print over one const file and never runs
`felt-combine`. Make it run `veir-opt -p=felt-combine` and `llzk-opt
--canonicalize` over a felt-arithmetic corpus; the 2 verified patterns are the
first targets.

**Bootstrap.** Read `llzk-lean/docs/strategy-a-oracle.md` +
`llzk-lean/differential/README.md` + `differential/run-differential.sh`. `veir-opt`:
`cd ~/LLZK/llzk-lean && lake exe veir-opt`. `llzk-opt`: the nix path in §0.

**Plan.** (1) extend `scripts/llzk-diff.sh` (veir) to pass the canonicalize/pass
flags; (2) author a felt corpus (one positive + one no-fire per pattern, generic
MLIR); (3) wire the verified patterns first; (4) keep the normalizer honest (the
field is carried by the outer `!felt.type` — see REVIEW.md VH2). NOTE: VH1 parser
parity is resolved and the `expected-divergence/named_field_const.mlir` caveat is
stale — re-test and likely move it to `felt/`.

**Verify / DoD.** Harness runs both tools with passes enabled, green on the
corpus; corpus covers the verified patterns; docs updated; commit.

---

## F6 — Broader VEIR audit (independent; agent fan-out)

**Goal.** The audit beyond Felt (`veir/FOLLOWUP.md` §1). Headline = the **axiom
inventory**.

**Plan (mostly read-only fan-out, then verify sharp findings):**
- `grep -rn "^axiom\|^ *axiom " ~/LLZK/veir/Veir` → classify each (esp.
  `WfIRContext.Dom`): definitional vs load-bearing.
- Sorry census across all modules; confirm `InstCombine`/`RISCV64`/`DCE` counts.
- Orphan proofs: confirm `Combines/Proofs.lean` + `InstructionSelection/Proofs.lean`
  are imported by nobody (so `lake build` skips them) — decide wire-in vs delete.
- Interpreter dialect coverage; the ~15 remaining dangling doc refs.

**Verify / DoD.** A `VEIR-AUDIT.md` (new, in veir) with the axiom inventory +
sorry census + findings catalog; memory updated; commit.

---

## F7 — Upstream sync + PRs (hygiene; anytime)

**Goal.** Follow the runbook in `veir/FOLLOWUP.md` §2 to sync from
`opencompl/veir`, and open PRs for the two feature branches.

**Plan.** (1) `git remote add upstream https://github.com/opencompl/veir.git`;
`git fetch upstream`; review `git log --oneline origin/main..upstream/main`. (2)
Merge on a branch, resolving conflicts in `Veir/Dialects/LLZK/*`, `Felt/*`,
`Attribute.lean`, `AttrParser.lean`. (3) Toolchain bump if upstream moved;
`lake exe cache get`; `lake build` green; re-axiom-audit the Felt proofs. (4) Bump
the `llzk-lean` Lake pin deliberately, regenerate the manifest, refresh the
dependency checkout, then run both Phase 1 pin gates:
`llzk-lean/scripts/harness/verify-pins.sh --workspace-veir ../veir` and
`veir/scripts/harness/verify-companion-pin.sh --companion-llzk-lean ../llzk-lean`.
(5) PRs via `gh` (target `project-llzk`). Harden steps 1–4 into
`scripts/upstream-sync.sh`.

**Verify / DoD.** Green build post-merge; Felt proofs still axiom-clean; runbook
scripted; PRs opened; commit.

---

## Progress ledger (update at the end of each session)
- 2026-06-01 — Review complete (both repos); fixes VC1/VC3/VM1 + H4; **structural
  close spike: 2/15 patterns sorry-free + axiom-clean** in `RewriteLemmas.lean`;
  this playbook written. Next: **F1**.
- 2026-06-02 — **F2 DONE (scoping spike + PoC).** Feasibility memo + go/no-go in
  `FOLLOWUP.md` §F2. Landed a real axiom-clean bridge lemma
  (`Veir.FeltInterp.interpretAdd_const_zero`, `[propext, Quot.sound]`) +
  Mathlib-free felt interpreter model `Veir/Passes/Felt/InterpModel.lean`
  (registry + const/add/sub/mul/neg). **Go on F3 at the value-refinement level;
  defer whole-program `interpret = interpret`** (needs a new interpreter-
  simulation framework + missing `eraseOp` lemmas + the `Dom` axiom). Q1 field
  model decided (name→prime registry; `Nat`-canonical felt value; Mathlib only in
  a bridge file). F3 now unblocked.
- 2026-06-02 — **F1 DONE. All 15/15 Felt patterns sorry-free + axiom-clean**
  (`[propext, Classical.choice, Quot.sound]`), verified by `lake build
  Veir.Passes.Felt.Combine` + `#print axioms` on each. All patterns moved into
  `RewriteLemmas.lean` on three reusable tails (`projectToOperand`,
  `replaceWithNewOp`, `replaceWithBinOpOfConst`) + a per-matcher in-bounds lemma
  library; `Combine.lean` defines no pattern itself. VC3 cross-field guard
  preserved. REVIEW.md §0 updated.
- 2026-06-05 — **Phase 1 reproducible pins active.** llzk-lean consumes
  `project-llzk/veir@d52917ca4a57c4094b1aa61dd413aca4e1c2a56e` through Lake
  metadata and a clean dependency checkout; both repos now document strict
  remote URL/type/rev/inputRev/cleanliness gates. Next candidates: F3 value-level
  Felt interpreter refinements, F4 Strategy E matcher, F5 Strategy A differential,
  F6 broader VEIR audit, or F7 upstream sync.
