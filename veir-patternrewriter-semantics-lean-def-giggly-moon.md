# Plan: lift local-rewrite soundness to function/module refinement

## Context

[Veir/PatternRewriter/Semantics.lean](Veir/PatternRewriter/Semantics.lean) was just created (commit `fb1f8d294`). It defines the *local* soundness obligation [`LocalRewritePattern.PreservesSemantics`](Veir/PatternRewriter/Semantics.lean#L100-L115): rewriting one matched op into `newOps`/`newValues` simulates the matched op step-for-step, under a state refinement [`InterpreterState.isRefinedByAt`](Veir/Interpreter/Refinement/Basic.lean#L146) (which now carries an explicit value renaming `σ` as its last argument; see PR 5) and the SSA invariant [`EquationLemmaAt`](Veir/Interpreter/EquationLemma.lean#L118-L123).

We want the *global* payoff: a sound pattern, applied to a program, refines every function — i.e. [`OperationPtr.isModuleRefinedBy`](Veir/Interpreter/Refinement/Basic.lean#L110-L116) / [`isRefinedByAsFunction`](Veir/Interpreter/Refinement/Basic.lean#L72-L80). This is what makes `PreservesSemantics` worth discharging for concrete patterns.

**Decisions (confirmed with user):**
- **Headline = single rewrite step → module refinement.** One rewrite at one matched op ⟹ `isModuleRefinedBy ctx mod mod newCtx`, built on a per-function lemma. The full `applyInContext` fixpoint driver (opaque `partial def` while-loops) is out of scope here.
- **State it against an abstract `RewrittenAt` relation**, not the concrete [`fromLocalRewrite`](Veir/PatternRewriter/Basic.lean#L248-L266); connecting the two (and filling its `sorry`s) is a deferred milestone.
- **Upstream incrementally**: the work is sliced into the small, self-contained, *`sorry`-free* PRs below, each independently reviewable and mergeable. Within a PR, develop with `sorry` placeholders; merge only when clean.

## Core difficulty (drives the slicing)

`interpretFunction` walks the CFG; `PreservesSemantics` is a flat `interpretOpList newOps` statement. The walk decomposes as `interpretFunction → interpretRegion → interpretBlockCFG → interpretBlock → interpretOpChain → interpretOp` ([Basic.lean:1151-1279](Veir/Interpreter/Basic.lean#L1151-L1279)). Two existing lemmas bridge chain→list and let us cut a block into `pre ++ [op] ++ post` — the shape `PreservesSemantics` consumes:
[`interpretOpChain_eq_interpretTerminatedOpList_of_firstOp`](Veir/Interpreter/Lemmas.lean#L322), [`interpretTerminatedOpList_append`](Veir/Interpreter/Lemmas.lean#L270).

What is **missing**: (a) any lemma relating interpretation to context edits, and (b) — fundamentally — **monotonicity of interpretation under `⊒`**. Because `interpretFunction` runs with `valuesSource ⊒ valuesTarget` (refined, not equal) arguments, every op consumes refined inputs from the first one, so the proof rests on per-op monotonicity that does not yet exist. Crucially, **(b) is independent of the rewrite** and is the natural first half of the upstreaming.

**Cross-context from the start (decision).** `InterpreterState ctx` is *indexed by the context*, and the rewrite payoff (PR 7/8) relates a source in `ctx` to a rewritten program in `newCtx` — *different* contexts, hence different state types. A same-context `InterpreterState.isRefinedBy` workhorse therefore cannot even be *stated* at the rewrite boundary. The codebase provides the right currency: [`InterpreterState.isRefinedByAt`](Veir/Interpreter/Refinement/Basic.lean#L146) is `{ctx ctx'}`-polymorphic, gated by `dominatesIp val insertPoint`, and now carries an **explicit renaming** `σ : {v // v.InBounds ctx.raw} → {v // v.InBounds ctx'.raw}` (a source value `val` is matched against `σ ⟨val, _⟩` on the target). It is exactly what [`PreservesSemantics`](Veir/PatternRewriter/Semantics.lean#L97) consumes. So **Group 1 is stated cross-context over `isRefinedByAt` from the get-go**, not over a same-context relation. For the *unchanged* majority the renaming is the **identity-on-`ValuePtr` embedding** `⟨v, h⟩ ↦ ⟨v, mono h⟩` carrying `InBounds`-monotonicity (supplied by [`WithCreatedOps.inBounds_mono`](Veir/PatternRewriter/Semantics.lean#L31-L35) for the create-only `newCtx`; on the erased-op `newCtx` of PR 7/8 it sends `op`'s gone results to arbitrary in-bounds junk, harmless because they are non-dominating). The non-trivial renaming enters only at the rewrite boundary (PR 5/7). Because `σ` is subtype-typed there is **no `σ = id` abbreviation** — even the "same values" case is this explicit embedding, not a literal `id`. This (i) makes the monotonicity lemmas directly reusable for `pre`/`post`/non-`B` blocks across `ctx`/`newCtx`, folding the PR 6 clause-4 *frame* obligation (intrinsic-data agreement of untouched ops) into the monotonicity hypotheses rather than a separate transport lemma; (ii) keeps the insert-point gating, which is the natural invariant to *advance* (`before op → after op`) through a block in PR 3. The same-context `isRefinedBy` statement falls out as the `ctx' = ctx` corollary if PR 4's diagonal wants it. Note also: the cf-action component must be compared by **refinement, not equality** — terminators (`func.return`/branch) carry refined-not-equal value payloads, so action equality is unprovable for them.

## Upstreaming roadmap

### Group 1 — interpreter monotonicity under refinement (no rewrite knowledge)

Self-contained; reviewers need no rewrite context. Culminates in a standalone, independently-useful theorem.

- **PR 1 — `interpretOp'` is monotone under `⊒` (the semantic gate).**
  Define what "monotone" means for the dialect step's `(resultValues, mem, action)` result under `⊒` on operands, and prove it for the existing ops. The result relation is `resultValues ⊒ · ∧ mem = · ∧ action` **refined** (a `ControlFlowAction.isRefinedBy`: same constructor, equal `dest`, value payload `⊒` — *not* equality, which fails for `func.return`/branch). Stated context-free (no `ctx` here — `interpretOp'` takes raw `operands`/`mem`), so cross-context is a non-issue at this layer; it is PR 2 that introduces contexts. *Feasibility gate*: if any op is non-monotone the global theorem is false — settle this first. Likely **split per op-group** (e.g. `arith`, memory ops, control) into a few sibling PRs, each tiny and self-contained. Lives near the `interpretOp'` definitions. (Draft already in [Lemmas.lean](Veir/Interpreter/Lemmas.lean) `monotonicity` section as `interpretOp'_mono`, currently `sorry` and using action *equality* — fix to action refinement.)

- **PR 2 — `interpretOp` is monotone under a *cross-context* state refinement (Tier D workhorse).**
  Lift PR 1 through [`getOperandValues`](Veir/Interpreter/Basic.lean#L1154) (refined state ⇒ refined operand array) and [`setResultValues?`](Veir/Interpreter/Basic.lean#L1158). **Stated cross-context over [`isRefinedByAt`](Veir/Interpreter/Refinement/Basic.lean#L146) (under the identity-on-`ValuePtr` embedding renaming)**: `state : InterpreterState ctx`, `state' : InterpreterState ctx'`, related at `InsertPoint.before op`, **plus frame hypotheses** that `op` has identical intrinsic data in both contexts (`getOpType!`/`getProperties!`/`getResultTypes!`/`getSuccessors!`/operands agree across `ctx`/`ctx'`) so both sides run the same dialect step. Conclusion: `interpretOp` results related by `isRefinedByAt` at `InsertPoint.after op` + cf-action refined. This fuses monotonicity with the PR 6 clause-4 frame, so it applies directly to untouched ops across `ctx`/`newCtx`; the same-context `isRefinedBy` version is the `ctx' = ctx` corollary. Depends on PR 1. Reuse `interpretOp_some_iff`, `getOperandValues_setResultValues?_of_dominates`, `getOperandValues_isRefinedBy`, `setResultValues?_isRefinedBy` ([Veir/Interpreter/Lemmas.lean](Veir/Interpreter/Lemmas.lean), [Refinement/Lemmas.lean](Veir/Interpreter/Refinement/Lemmas.lean)). (Draft `interpretOp_mono` exists but is same-context + action-equality — restate.) **Soundness check for the advance:** `before op → after op` is valid because `op`'s results are the only new dominating values; confirm the `dominatesIp` step.

- **PR 3 — `interpretOpList` / `interpretTerminatedOpList` monotone over an identical list, cross-context.**
  Induction over the list using PR 2, **threading `isRefinedByAt` and advancing the insert point op-by-op** (entry `before` first op → exit `after` last op); refined entry state + per-op frame agreement ⟹ refined exit + refined cf. Cross-context (`ctx`/`ctx'`) so it serves `pre`/`post`/non-`B` directly. Depends on PR 2.

- **PR 4 — `interpretFunction` monotone under argument refinement.**
  Diagonal instance `op.isRefinedByAsFunction ctx op ctx` (`ctx' = ctx`, frame hypotheses trivial). `interpretBlockCFG` simulation by `partial_fixpoint` induction ([Basic.lean:1236-1248](Veir/Interpreter/Basic.lean#L1236-L1248)) carrying "incoming args refined + entry states related (`isRefinedByAt`)", using PR 3 per block and the chain→list bridge; then `interpretRegion`/`interpretFunction`. Capstone of Group 1: a clean reflexivity-under-refined-arguments theorem (not currently in [Refinement/Lemmas.lean](Veir/Interpreter/Refinement/Lemmas.lean), which only has value/array/`FunctionResult` refl). Because PR 2/3 are already cross-context, PR 8's per-function step reuses the *same* CFG induction with `ctx`/`newCtx` rather than needing a separate transport. Depends on PR 3.

### Group 2 — the rewrite relation and the local→global lift

Builds the rewrite-specific layer on top of Group 1.

- **PR 5 — renaming-aware state refinement.** *(Core landed.)*
  After erasing `op` the post-region references `newValues`, not `op`'s results, so a relation matching the *same* `ValuePtr` on both sides cannot survive the boundary. **Already implemented:** [`VariableState.isRefinedByAt`](Veir/Interpreter/Refinement/Basic.lean#L134) / [`InterpreterState.isRefinedByAt`](Veir/Interpreter/Refinement/Basic.lean#L146) now carry an explicit **subtype renaming** `σ : {v // v.InBounds ctx.raw} → {v // v.InBounds ctx'.raw}` as their last argument (matching `val` against `σ ⟨val, _⟩`); reflexivity is the same-context identity case [`isRefinedByAt_refl`](Veir/Interpreter/Refinement/Lemmas.lean#L73) and transitivity composes renamings [`isRefinedByAt_trans`](Veir/Interpreter/Refinement/Lemmas.lean#L84) (`σ₂ ∘ σ₁`). *(Declaration names carry no `σ`; only the renaming argument is denoted `σ`.)* **Remaining:** (a) the **identity-on-`ValuePtr` embedding** for untouched values (InBounds-mono via [`WithCreatedOps.inBounds_mono`](Veir/PatternRewriter/Semantics.lean#L31-L35)), threaded by `pre`/non-`B`/`PreservesSemantics`; (b) the concrete rewrite renaming (the identity embedding except `op.getResult i ↦ newValues[i]`); (c) propagation lemmas (how the renaming commutes with `getOperandValues` / the per-op step) so PR 7-iii can interpret `post'` under it. Self-contained infra.

- **PR 6 — define `RewrittenAt` + structural frame lemmas.**
  `RewrittenAt ctx op newOps newValues newCtx : Prop` capturing the net edit, with clauses:
  1. created/inserted ops: `WithCreatedOps` + [`ReturnOps`](Veir/PatternRewriter/Semantics.lean#L69-L73) + [`ReturnValues`](Veir/PatternRewriter/Semantics.lean#L78-L81) (reuse as-is);
  2. `op` erased; every other op still `InBounds newCtx`;
  3. block `B = op`'s block: list `pre ++ [op] ++ post` (ctx) becomes `pre ++ newOps ++ post'` (`post'` = `post` with `op.getResult i` operands redirected to `newValues[i]`); all other blocks identical;
  4. intrinsic-data frame: surviving ops agree on `getOpType!`/`getProperties!`/`getResultTypes!`/`getSuccessors!`/operands (mod. clause 3) — this is exactly the **frame hypothesis already consumed by the cross-context PR 2/3** (no separate context-independence lemma needed; `RewrittenAt` just has to *supply* clause 4 to feed them);
  5. structure frame: `func`/`mod` pointers, parents, region counts, CFG edges preserved.
  Reuses [`WithCreatedOps.inBounds_mono`](Veir/PatternRewriter/Semantics.lean#L31-L35) etc. **Split if large**: 6a (def + clauses 1–2) / 6b (clauses 3–5). Pure IR-level; reviewable as "the net effect of a local rewrite."

- **PR 7 — block-`B` simulation consuming `PreservesSemantics`.**
  Split `pre ++ [op] ++ post` with `interpretTerminatedOpList_append`:
  (i) `pre` identical → PR 3 (cross-context, fed clause-4 frame agreement) gives refined state across `ctx`/`newCtx` + establishes `EquationLemmaAt (before op)` both sides (thread via [`interpretOp_equationLemmaAt`](Veir/Interpreter/EquationLemma.lean#L125-L130));
  (ii) `[op]` vs `newOps` → apply [`PreservesSemantics`](Veir/PatternRewriter/Semantics.lean#L100-L115), yielding `sourceValues ⊒ targetValues`; **bridge** the create-only `newCtx` of `PreservesSemantics` to the inserted/erased `newCtx` via clause-4 frame;
  (iii) `post` vs `post'` → PR 3 under the PR-5 renaming, seeded by (ii). Depends on PRs 2,3,5,6.

- **PR 8 — headline: `RewrittenAt.isRefinedByAsFunction` + `RewrittenAt.isModuleRefinedBy`.**
  Per-function: same CFG simulation as PR 4, but block `B` uses PR 7 while all other blocks reuse PR 3/4 identical-list machinery. Module: quantify over top-level `func.func`s, witness `func₂ := func₁` (clauses 2,5 preserve `IsTopLevelFuncWithName` and `InBounds`). Depends on PRs 4,7. New file `Veir/PatternRewriter/Soundness.lean`.

### Group 3 — connect to the concrete driver (deferred)

- **PR 9 — `fromLocalRewrite → RewrittenAt`.** Fill the [`fromLocalRewrite` `sorry`s](Veir/PatternRewriter/Basic.lean#L259-L265) and derive clauses 1–5 from the `insertOp`/`replaceValue`/`eraseOp` specs. Separate effort; not required for the headline (which is stated over `RewrittenAt`).

## Files

- **New:** `Veir/PatternRewriter/Soundness.lean` (PRs 6–8: `RewrittenAt`, block-`B` simulation, headline).
- **Extend:** [Veir/Interpreter/Lemmas.lean](Veir/Interpreter/Lemmas.lean) (PRs 2–4 interpreter monotonicity), [Veir/Interpreter/Refinement/Lemmas.lean](Veir/Interpreter/Refinement/Lemmas.lean) (PR 5 renaming refinement + glue — core relation/refl/trans already landed in [Refinement/Basic.lean](Veir/Interpreter/Refinement/Basic.lean#L134) + [Lemmas.lean](Veir/Interpreter/Refinement/Lemmas.lean#L73)), and near the `interpretOp'` definitions (PR 1).

## Reusable existing infrastructure

- Bridges: [`interpretOpChain_eq_interpretTerminatedOpList_of_firstOp`](Veir/Interpreter/Lemmas.lean#L322), [`interpretTerminatedOpList_append`](Veir/Interpreter/Lemmas.lean#L270), `interpretOpList_append`.
- Invariant threading: [`interpretOp_equationLemmaAt`](Veir/Interpreter/EquationLemma.lean#L125-L130) and the `EquationHolds`/dominance lemmas in that file.
- Refinement algebra: refl/trans at every level in [Veir/Interpreter/Refinement/Lemmas.lean](Veir/Interpreter/Refinement/Lemmas.lean) — state-level [`isRefinedByAt_trans`](Veir/Interpreter/Refinement/Lemmas.lean#L84) now composes renamings (`σ₂ ∘ σ₁`); [`isRefinedByAt_refl`](Veir/Interpreter/Refinement/Lemmas.lean#L73) is the same-context identity case.
- Created-ops frame: [`WithCreatedOps.inBounds_mono`](Veir/PatternRewriter/Semantics.lean#L31-L35) and siblings.
- Operand frame: `VariableState.getOperandValues_setResultValues?_of_dominates`, `interpretOp_some_iff` ([Veir/Interpreter/Lemmas.lean](Veir/Interpreter/Lemmas.lean)).

## Risks / open issues

- **Per-op monotonicity (gate, PR 1).** If `interpretOp'` is non-monotone under `⊒` the theorem is false — de-risk first. Volume scales with the op set (hence the per-group split). The memory-op group is the sharpest gate (a store of a refined-not-equal value at an equal address must keep memory *equal*, per `FunctionResult`'s `mem` equality); sequence non-terminator value ops first, memory ops next. The cf-action component is **refinement, not equality** (terminators carry refined payloads).
- **Cross-context statement (PR 2/3).** Stating monotonicity over `isRefinedByAt` with frame hypotheses (rather than same-context `isRefinedBy`) is the deliberate up-front cost that avoids a separate transport lemma later; the `before op → after op` insert-point advance must be discharged from "op's results are the only new dominating values."
- **Renaming (PR 5).** The renaming-carrying relation + composition algebra are now landed (subtype-typed `σ` argument on `isRefinedByAt`; `isRefinedByAt_refl`/`_trans`). Remaining friction: (i) erasing `op` forces a `op.result ↦ newValue` renaming in the post-region invariant; (ii) because `σ` is subtype-typed, even the cross-context *identity* case is an explicit `InBounds`-mono embedding (not a free `id`), so every Group-1 / `pre` lemma must thread it — clean for the create-only `newCtx` (`WithCreatedOps.inBounds_mono`), with erased values mapped to non-dominating junk. Localized but non-trivial.
- **`partial_fixpoint` CFG induction (PR 4)** with loops/branches is the hardest control-flow step; the single-block edit keeps non-`B` blocks trivial.
- **Create-only vs final context bridge (PR 7-ii).**
- **Driver extension out of scope:** reaching `applyInContext` needs refactoring the `partial def` while-loops + transitivity composition (`isModuleRefinedBy_trans` exists for that day).

## Verification

- Develop with the `lean-lsp` MCP tools: `lean_goal`/`lean_term_goal` at proof positions, `lean_diagnostic_messages` per file, `lean_multi_attempt` to try `grind`/`simp` combos (the repo is `grind`-heavy). `lean_build` only after new imports.
- Each PR must merge **`sorry`-free**: confirm with `lean_verify` (no `sorryAx` dependency) on its headline declarations before opening the PR.
- After PR 9, sanity-check the full chain on a concrete pattern (e.g. `right_identity_zero_add` in [Veir/Passes/Combines/Combine.lean](Veir/Passes/Combines/Combine.lean)).
