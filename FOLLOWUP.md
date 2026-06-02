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

## F2 — Interpreter-semantics keystone: feasibility memo + go/no-go (2026-06-02)

> Deliverable of the F2 scoping spike (`../veir/SESSIONS.md` §F2). Decides
> whether a closed *"this rewrite provably preserves program semantics"*
> theorem is reachable for Felt on current VEIR, and at what cost. **This gates
> F3 and the "verified drop-in" end goal.** A proof-of-concept was landed (see
> "What was landed" below); this section is its writeup, for non-Lean colleagues.

### TL;DR / go-no-go

- **The value-level bridge is DONE and cheap.** The thing the review flagged as
  missing — `Veir.Data.Felt` never connected to anything a program *runs* — is
  now closed for the `add x 0 → x` rewrite by a real, axiom-clean lemma
  (`Veir.FeltInterp.interpretAdd_const_zero`, `[propext, Quot.sound]`). This is
  **the same assurance tier as VEIR's best existing correctness proofs** (the
  instruction-selection `*_refinement` lemmas) — actually a notch beyond, since
  it runs through a real interpreter function, not only an abstract data op.
- **The whole-program theorem (`interpret(rewrite ctx) = interpret(ctx)`) is
  NOT a per-pattern follow-up. It is a multi-week framework build, and it rests
  on the `WfIRContext.Dom` axiom.** No VEIR pass has such a theorem today; the
  substrate to even state-and-prove it (an interpreter-simulation relation
  across structural IR edits) does not exist and partly *cannot be stated yet*
  with the current rewriter lemmas.
- **Recommendation: GO on F3, scoped to the value level. NO-GO (defer) on the
  whole-program keystone** until/unless it becomes a deliberate, separately
  budgeted research effort. F3 should wire the interpreter and prove value-level
  `*_refinement`-style lemmas for each fold (the tractable, high-value tier),
  *not* attempt program-equivalence per pattern.

### What was landed (the PoC, real and checked)

`Veir/Passes/Felt/InterpModel.lean` (built on the default path via
`Combine.lean`; axiom-audited in veir's own toolchain):
- A felt runtime-value model `FeltVal.felt p val` and minimal `interpretOp'`
  arms for `const`/`add`/`sub`/`mul`/`neg`, mirroring `Arith.interpretOp'`.
- A field-name→prime registry `feltPrime`, mirroring LLZK
  `Util/Field.cpp::initKnownFields`.
- **The bridge lemma `interpretAdd_const_zero`**: interpreting
  `felt.add x (felt.const 0)` returns *exactly* `x`'s runtime value. Axiom
  audit: `[propext, Quot.sound]` — no `sorryAx`, no `Classical.choice`, no
  `WfIRContext.Dom`.

### Q1 — How to model the field (DECIDED)

`!felt.type` carries an optional field *name* but **no prime**; the prime lives
in LLZK's registry, keyed by name (bn254, babybear, goldilocks, …); an unnamed
field is "filled in by the backend" (no runtime meaning). Decision, three parts:

1. **Resolve the prime by a name→prime registry** mirroring `initKnownFields`
   (`feltPrime`). Unnamed/unknown field ⇒ `none` (uninterpreted). This is the
   only faithful source of the modulus.
2. **Represent a felt runtime value as a canonical `Nat` in `[0, p)` carrying
   its own `p`** (`FeltVal.felt p val`), with `Nat`-modular arithmetic — exactly
   how LLZK's executable folder works (`Field::reduce`). Rejected: `ZMod p` in
   the runtime value, because **it forces Mathlib onto the core, Mathlib-free
   `Interpreter/Basic.lean`** — a heavy architectural cost. (Confirmed: the core
   interpreter imports no Mathlib today.) The `ZMod p`/`Veir.Data.Felt`
   correspondence belongs in a *separate* proof file (the only place Mathlib
   enters), keeping the executable interpreter dependency-light.
3. **The basic ops (`add`/`sub`/`mul`/`neg`) need no primality** and hold in
   every modulus — matching the universally-`p`-quantified identities in
   `Proofs.lean`. Primality enters only for `div`/`inv`/`pow`/bit-width ops
   (F3's harder half).

### Q2 — Does the whole-program theorem need `WfIRContext.Dom`? (YES)

Proving `interpret(after) = interpret(before)` for a peephole requires use-def
reasoning: that the replacement value is in scope at every use, that no later op
redefines it, and that erasing the matched op (now use-less) changes nothing.
Those facts are exactly what `Veir/Interpreter/Lemmas.lean`'s dominance lemmas
provide (`getOperandValues_setResultValues_of_dominates`, `setResultValues_comm`,
…) — and every one of them consumes `ctxDom : ctx.Dom`. `WfIRContext.Dom` is an
**opaque axiom** (`Veir/Dominance.lean` is by its own header "a placeholder…
currently only contains axioms"). Unlike the *structural* preconditions (which
F1 discharged with defensive runtime guards), semantics **cannot** be
guard-discharged — you genuinely need the dominance facts — so any whole-program
felt theorem will be **conditional on the `Dom` axiom**. Honest, but it means the
keystone inherits VEIR's single largest trust-base assumption.

### Q3 — Effort for ONE pattern end-to-end, and does it generalize?

- **Value-level (what was landed): ~hours per pattern, fully axiom-clean.**
  Mechanical, mirrors `Proofs.lean`. Generalizes trivially across the 15
  patterns. This is the right F3 target.
- **Whole-program (`interpret = interpret`): multi-week, research-grade, and
  blocked on missing substrate.** It decomposes into (i) the value-level lemma
  [done], (ii) "`replaceValue` preserves interpretation of all other ops, given
  operand-value agreement" and (iii) "`eraseOp` of a use-less op preserves
  interpretation". (ii)/(iii) require a **new interpreter-simulation framework**:
  a relation between the pre/post variable-states preserved across each step, an
  induction over `interpretOpList`, and handling the `partial_fixpoint` CFG
  layer. It also needs `eraseOp` postcondition lemmas that **do not exist and are
  flagged in-source as "quite complex to state"** (`OpResultPtr.get!_eraseOp`,
  `OpOperandPtr.get!_eraseOp`, `BlockOperandPtr.get!_eraseOp` in
  `Rewriter/GetSet/DetachOp.lean`). It does NOT generalize per-pattern cheaply —
  the framework is the cost; once built, patterns become cheaper. **No VEIR pass
  has attempted this**, so there is no precedent to copy and the ceiling is set
  by VEIR's maturity, not by the Felt port.

### F3 guidance (unblocked by this memo)

- Adopt the Q1 model: name→prime registry, `Nat`-canonical runtime felt value,
  Mathlib confined to a `ZMod`/`Data.Felt` bridge file.
- Wire `RuntimeValue.felt` + `Felt.interpretOp'` into the core interpreter for
  all 18 ops (Mathlib-free); `div`/`inv`/`pow` need the prime + primality.
- Prove value-level `*_refinement`-style soundness per fold (cheap, axiom-clean).
- Treat program-equivalence as out of scope unless separately greenlit.

---

## 3. Pointers
- Felt-port findings: `REVIEW.md` (this repo).
- **F2 interpreter-semantics PoC: `Veir/Passes/Felt/InterpModel.lean`** + the §F2
  memo above.
- Bridge / assurance story: `../llzk-lean/docs/REVIEW.md`.
- Structural-close spike (reusable lemma library + closed patterns):
  `../llzk-lean/Spike3.lean` (to be moved into `Veir/Passes/Felt/` per the
  step-4 plan).
