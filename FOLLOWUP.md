# VEIR — Follow-up / Backlog (beyond the Felt-dialect review)

> Created 2026-06-01. Companion to `REVIEW.md` (which is Felt-port-specific).
> These are deliberately-deferred items surfaced during the Felt review that
> deserve their own dedicated effort. Nothing here is done yet.

---

## 1. Broader VEIR audit (everything that is NOT the Felt dialect)

**Why.** The review so far covered only the Felt dialect port. VEIR is much
larger, and several things were noticed *in passing* that warrant a dedicated,
adversarial pass — some bear directly on the assurance story (axioms, sorries)
and on how much of VEIR we can trust as the substrate.

**Known-in-passing observations to start from (verify + expand):**

- **`WfIRContext.Dom` is an AXIOM.** VEIR axiomatizes SSA dominance
  (`Veir/Dominance.lean`); the dominance lemmas (e.g.
  `IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates`,
  `OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!`) are
  built on it. This is a **first-class trust-base item**: any rewrite proof
  that uses dominance depends on this axiom unless it is discharged by runtime
  guards (as we did for the Felt patterns). A full audit should enumerate
  **every `axiom` in VEIR** and classify each (definitional convenience vs.
  load-bearing assumption).
- **`WfIRContext` encodes only structural well-formedness** — not per-opcode
  shape constraints (e.g. region counts) and not dominance. This is why every
  pass `sorry`s its rewriter preconditions. Worth deciding project-wide
  whether to (a) strengthen `WfIRContext`/the matchers, or (b) standardize the
  defensive-guard technique.
- **Heavy `sorry` use in other passes:** `InstCombine.lean` (~45),
  `InstructionSelection/RISCV64.lean` (~127), `CastsReconciliation` (~11),
  `DCE` (no soundness proof at all). A `#print axioms` / `sorry` inventory
  across the whole tree would quantify the real verified surface.
- **Orphan proof files:** `Veir/Passes/Combines/Proofs.lean` and
  `Veir/Passes/InstructionSelection/Proofs.lean` are imported by nobody, so
  `lake build` does NOT check them (they can bit-rot silently). Confirm and
  decide whether to wire them in or delete. (By contrast `Felt/Proofs.lean`
  *is* on the build path — good.)
- **Interpreter coverage:** `Veir/Interpreter/Basic.lean` handles
  arith/llvm/riscv/cf/comb/hw and returns `none` for everything else (Felt is
  not in the interpreter; value domain is fixed-width `LLVM.Int`/`BitVec`, not
  `ZMod p`). A broader audit should map which dialects have interpreter
  semantics and whether any pass has a closed rewrite→interpreter
  soundness theorem (so far: none found).
- **Dangling doc references** (the "remove dev docs" commit `5ed914831`
  deleted `harness/*.md`, `FELT_PARITY_ASSESSMENT_*.md`, `plan.md`, etc., but
  ~15 live source/test/script references to them remain — see `REVIEW.md`
  VM1/VM2). The Felt-critical ones were re-pointed; the rest are open.

**Suggested method.** Mirror the Felt review: a full `#print axioms` + `sorry`
inventory across all modules; an adversarial fan-out by subsystem (each dialect,
the interpreter, the pass infra, the verifier, the WellFormed/Dom layer); then
reviewer re-verification of sharp findings. Deliverable: a `REVIEW.md`-style
catalog for VEIR-at-large, with the **axiom inventory** as the headline.

---

## 2. Upstream sync from `opencompl/veir` (we are a fork)

**Why.** This repo is the `project-llzk/veir` fork, which carries the LLZK Felt
port not present upstream. Upstream `opencompl/veir` continues to add features;
we should pull periodically to stay current — but carefully, because the Felt
port and the LLZK-dialect work are local divergences.

**Current state (verify before acting):**
- Remote configured is `project-llzk/veir` only; **`opencompl/veir` is NOT
  configured as a git remote** despite the README telling users to "fetch from
  `opencompl/veir` directly and merge as needed." HEAD is even with
  `origin/main` (project-llzk).
- The Felt port is a reasonably **isolated** linear chain of `Phase E.*` /
  `Tier 1+2` / `Felt:` commits, with one prior explicit
  `Merge upstream changes from opencompl/veir` (`9e665c696`). So merges have
  been done before and are feasible.
- **Toolchain:** this fork pins Lean `v4.30.0-rc2`; `llzk-lean` pins
  `v4.30.0`. Upstream may have moved; a sync likely involves a toolchain bump
  (and re-running `lake exe cache get` for the matching Mathlib).

**Risks to plan for:**
- Merge conflicts with the local LLZK-dialect files (`Veir/Dialects/LLZK/*`,
  `Veir/Passes/Felt/*`, the LLZK attribute/parser additions in
  `Veir/IR/Attribute.lean`, `Veir/Parser/AttrParser.lean`).
- Upstream refactors to the `Rewriter`/`WfRewriter`/`WellFormed` layer could
  invalidate the Felt-port precondition proofs (the reusable lemma library
  from the structural-close spike depends on those signatures).
- The `llzk-lean` Lake pin (`lakefile.toml` → `project-llzk/veir @ <rev>`)
  must be bumped deliberately after any sync, and the proof basis re-checked
  (axiom audit on `Veir.Passes.Felt.Proofs`).

**Suggested procedure (document + script it):**
1. `git remote add upstream https://github.com/opencompl/veir.git`
2. `git fetch upstream`; review `git log --oneline origin/main..upstream/main`
   to see what's new.
3. Merge/rebase on a branch; resolve conflicts in the LLZK-local files.
4. Bump `lean-toolchain` if upstream moved; `lake exe cache get`; `lake build`
   (must be green) + re-run the Felt FileCheck tests + a `#print axioms` check
   on the Felt proofs.
5. Bump the `llzk-lean` `lakefile.toml` pin to the new `project-llzk/veir`
   rev, then `lake update` (regenerates `lake-manifest.json`) and rebuild.
6. Re-run the differential harness once it is meaningful (see `REVIEW.md` VH2).

This should become a documented, repeatable "upstream sync" runbook (ideally a
small script under `scripts/`), since the fork will need it recurringly.

---

## 3. Pointers
- Felt-port findings: `REVIEW.md` (this repo).
- Bridge / assurance story: `../llzk-lean/docs/REVIEW.md`.
- Structural-close spike (reusable lemma library + closed patterns):
  `../llzk-lean/Spike3.lean` (to be moved into `Veir/Passes/Felt/` per the
  step-4 plan).
