import Veir.Interpreter.Refinement.Monotonicity
import Veir.PatternRewriter.Semantics

/-!
# `RewrittenAt`: the net effect of a single local rewrite

This file defines `RewrittenAt`, an *abstract* relation capturing the net edit performed by a single
local rewrite: a matched operation `op` (in `ctx`) is replaced by a list of new operations `newOps`
producing `newValues`, yielding a new context `newCtx`. The value renaming `σ` identifying surviving
values across the two contexts is *not* a parameter: it is fixed to `rewriteMapping` (the identity
except on `op`'s results, which are redirected to `newValues`). This is definitionally the same
renaming as `LocalRewritePattern.mapping`, but kept independent of the concrete driver so that
`RewrittenAt` stays decoupled from it.

`RewrittenAt` is stated abstractly — decoupled from the concrete `fromLocalRewrite` driver — so the
soundness lift (block-`B` simulation, the headline refinement theorems) can be developed against it
directly; connecting it to `fromLocalRewrite` is a deferred milestone (PR 9).

The clauses describe the edit as the composition *insert `newOps` before `op`* → *redirect each use of
`op`'s `i`-th result to `newValues[i]`* → *erase `op`*:

1. **created values/ops** — `newValues` has one entry per result of `op`, all in bounds of `newCtx`;
   `newOps` are exactly the operations fresh to `newCtx`.
2. **`op` erased, others survive** — `op` is no longer in bounds of `newCtx`; every other operation
   of `ctx` still is.
3. **block list shape** — in the block `B` containing `op`, the operation list `pre ++ [op] ++ post`
   becomes `pre ++ newOps ++ post` (the operations of `post` are the same pointers, only their
   operands are redirected — that redirection is recorded by `σ` in clause 4); every other block has
   an identical operation list.
4. **intrinsic-data frame** — every surviving operation satisfies `CrossContextFrame` under `σ`
   (op-type/properties/result-types/successors agree; operands/results map through `σ`; `op` verified
   in `newCtx`) — exactly what `interpretOp_monotone_at`/`interpretOpList_monoAt` consume.
5. **structure frame** — blocks stay in bounds (successor transport), and parent operations of
   surviving operations are preserved (so `IsTopLevelFuncWithName` transports).
6. **result well-formedness** — `newCtx` is dominance-well-formed, and every member of `newOps` is
   verified in `newCtx`; this discharges target progress when the source hits UB at the matched op.
-/

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
The value renaming performed by a single local rewrite: the identity on every value except the
results of `op`, which are redirected to the produced `newValues` index-by-index.

This is definitionally the same renaming as `LocalRewritePattern.mapping`, but it is kept independent
of the concrete `LocalRewritePattern` driver so that `RewrittenAt` (and the soundness lift built on
it) stays decoupled from the driver. The in-bounds witnesses `mapResultsInBounds`/`mapNonResultsInBounds`
play the role of the driver's `Return*` obligations.
-/
def rewriteMapping {ctx newCtx : WfIRContext OpCode}
    (op : OperationPtr) (newValues : Array ValuePtr)
    (mapResultsInBounds : ∀ (index : Nat), index < (op.getResults! ctx.raw).size →
      newValues[index]!.InBounds newCtx.raw)
    (mapNonResultsInBounds : ∀ (v : ValuePtr), v.InBounds ctx.raw →
      v ∉ op.getResults! ctx.raw → v.InBounds newCtx.raw) :
    ValueMapping ctx newCtx :=
  fun ⟨v, vInBounds⟩ =>
    if h : v ∈ op.getResults! ctx.raw then
      ⟨newValues[(op.getResults! ctx.raw).idxOf v]!, mapResultsInBounds _ (by grind)⟩
    else
      ⟨v, mapNonResultsInBounds v vInBounds h⟩

/-- `rewriteMapping` fixes `op`'s results onto `newValues` index-by-index: applying it to the result
array yields `newValues` exactly. This needs only that the sizes match (`newValuesSize`); the
distinctness of `op`'s result pointers (each is `⟨op, i⟩`) makes `idxOf (getResult i) = i`. -/
theorem rewriteMapping_applyToArray_getResults {ctx newCtx : WfIRContext OpCode}
    (op : OperationPtr) (newValues : Array ValuePtr)
    (mapResultsInBounds : ∀ (index : Nat), index < (op.getResults! ctx.raw).size →
      newValues[index]!.InBounds newCtx.raw)
    (mapNonResultsInBounds : ∀ (v : ValuePtr), v.InBounds ctx.raw →
      v ∉ op.getResults! ctx.raw → v.InBounds newCtx.raw)
    (newValuesSize : newValues.size = op.getNumResults! ctx.raw) :
    (rewriteMapping op newValues mapResultsInBounds mapNonResultsInBounds).applyToArray
      (op.getResults! ctx.raw) = newValues := by
  apply Array.ext
  · simp [newValuesSize]
  · intro i h1 h2
    have hsize : i < (op.getResults! ctx.raw).size := by grind
    simp only [ValueMapping.applyToArray, Array.getElem_map, Array.getElem_attach,
      rewriteMapping]
    rw [dif_pos (Array.getElem_mem hsize)]
    have hmem := OperationPtr.getResults!.mem_getResult (op := op) (ctx := ctx.raw)
      (index := i) (by grind)
    have hidx : (op.getResults! ctx.raw).idxOf (op.getResults! ctx.raw)[i] = i := by
      rw [OperationPtr.getResults!.getElem_eq_getResult (by grind)]
      have hge := OperationPtr.getResult_eq_of_idxOf_getResults! hmem rfl
      grind
    simp [hidx, getElem!_pos, h2]

/-- The in-bounds witness for the redirect branch of `rewriteMapping`: each result index of `op`
selects a value of `newValues` that is in bounds of the target context. Derived from `newValuesSize`
(the index is within `newValues`) and `newValuesInBounds` (every member is in bounds). This is the
witness `rewriteMapping` expects; previously it was carried as a `RewrittenAt` field. -/
theorem rewriteMapping_resultsInBounds {ctx newCtx : WfIRContext OpCode}
    (op : OperationPtr) (newValues : Array ValuePtr)
    (newValuesSize : newValues.size = op.getNumResults! ctx.raw)
    (newValuesInBounds : ∀ v ∈ newValues, v.InBounds newCtx.raw) :
    ∀ (index : Nat), index < (op.getResults! ctx.raw).size →
      newValues[index]!.InBounds newCtx.raw := by
  intro index hidx
  have hsize : index < newValues.size := by
    rw [newValuesSize, ← OperationPtr.getResults!.size_eq_getNumResults!]; exact hidx
  rw [getElem!_pos newValues index hsize]
  exact newValuesInBounds _ (Array.getElem_mem hsize)

/-- `LocalRewritePattern.mapping` and `rewriteMapping` (for the same `op`/`newValues`) agree on the
underlying value pointer, regardless of their (possibly different) target contexts: both fix every
non-result and send `op`'s `i`-th result onto `newValues`'s `i`-th entry. The two mappings have
different codomains (`mapping`'s is the pattern's create-only context, `rewriteMapping`'s is the
driver's edited context), so only the `.val` projection — which is context-independent — is compared.
This bridges the `PreservesSemantics` refinement (stated with `mapping`) to `hRW.σ`. -/
theorem mapping_val_eq_rewriteMapping_val {ctx newCtxA newCtxB : WfIRContext OpCode}
    {pattern : LocalRewritePattern OpCode} {op : OperationPtr}
    {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    (hpat : pattern ctx op = some (newCtxA, some (newOps, newValues)))
    (hRVIB : pattern.ReturnValuesInBounds) (hRV : pattern.ReturnValues)
    (hRCC : pattern.ReturnCtxChanges)
    {mapResultsInBounds : ∀ (index : Nat), index < (op.getResults! ctx.raw).size →
      newValues[index]!.InBounds newCtxB.raw}
    {mapNonResultsInBounds : ∀ (v : ValuePtr), v.InBounds ctx.raw →
      v ∉ op.getResults! ctx.raw → v.InBounds newCtxB.raw}
    {v : ValuePtr} (vIn1 : v.InBounds ctx.raw) (vIn2 : v.InBounds ctx.raw) :
    (LocalRewritePattern.mapping hpat hRVIB hRV hRCC ⟨v, vIn1⟩).val
      = (rewriteMapping op newValues mapResultsInBounds mapNonResultsInBounds ⟨v, vIn2⟩).val := by
  by_cases h : v ∈ op.getResults! ctx.raw
  · simp only [LocalRewritePattern.mapping, rewriteMapping, dif_pos h]
  · simp only [LocalRewritePattern.mapping, rewriteMapping, dif_neg h]

/--
`RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn'` asserts that
`newCtx` is obtained from `ctx` by the single local rewrite that replaces `op` with `newOps`
(producing `newValues`). The renaming identifying surviving values across the two contexts is *not* a
parameter: it is the function `RewrittenAt.σ` of the instance, defined as `rewriteMapping op newValues
h.mapResultsInBounds h.mapNonResultsInBounds` (the redirect-branch witness `RewrittenAt.mapResultsInBounds`
is derived from `newValuesSize`/`newValuesInBounds`; the identity-branch witness `mapNonResultsInBounds`
is a field below). `block` is the block containing `op`, `pre`/`post` the
operation lists before/after `op` in `block`, and `blockIn`/`blockIn'` the in-bounds witnesses for
`block` in the source/target contexts. See the module docstring for the clauses.
-/
structure RewrittenAt
    (ctx : WfIRContext OpCode) (op : OperationPtr)
    (newOps : Array OperationPtr) (newValues : Array ValuePtr)
    (newCtx : WfIRContext OpCode) (opIn : op.InBounds ctx.raw)
    (block : BlockPtr) (pre post : Array OperationPtr)
    (blockIn : block.InBounds ctx.raw) (blockIn' : block.InBounds newCtx.raw) : Prop where
  /-- The operations contained in each block. -/
  srcList : block.operationList ctx.raw ctx.wellFormed blockIn = pre ++ #[op] ++ post
  tgtList : block.operationList newCtx.raw newCtx.wellFormed blockIn' = pre ++ newOps ++ post
  otherBlocks : ∀ (b : BlockPtr) (bIn : b.InBounds ctx.raw) (bIn' : b.InBounds newCtx.raw),
      b ≠ block →
      b.operationList ctx.raw ctx.wellFormed bIn = b.operationList newCtx.raw newCtx.wellFormed bIn'
  -- Clause 1: created values/ops.
  /-- `newValues` carries one value per result of `op`. -/
  newValuesSize : newValues.size = op.getNumResults! ctx.raw
  /-- All produced values are in bounds of the target context. -/
  newValuesInBounds : ∀ v ∈ newValues, v.InBounds newCtx.raw
  /-- `newOps` are exactly the operations fresh to the target context. -/
  newOpsFresh : ∀ newOp, newOp ∈ newOps ↔ (newOp.InBounds newCtx.raw ∧ ¬ newOp.InBounds ctx.raw)
  /-- In-bounds witness for the identity branch of `σ` (`rewriteMapping`): every value that is not a
  result of `op` survives into the target context. -/
  mapNonResultsInBounds : ∀ (v : ValuePtr), v.InBounds ctx.raw →
    v ∉ op.getResults! ctx.raw → v.InBounds newCtx.raw
  -- Clause 2: `op` erased, others survive.
  /-- The matched operation is erased. -/
  opErased : ¬ op.InBounds newCtx.raw
  survives : ∀ (o : OperationPtr), o.InBounds ctx.raw → o ≠ op → o.InBounds newCtx.raw
  -- Clause 4: intrinsic-data frame for survivors.
  /-- Every surviving operation carries identical intrinsic data, modulo the renaming `σ`. -/
  frame : ∀ (o : OperationPtr) (oIn : o.InBounds ctx.raw) (oIn' : o.InBounds newCtx.raw),
    o ≠ op →
      (rewriteMapping op newValues
        (rewriteMapping_resultsInBounds op newValues newValuesSize newValuesInBounds)
        mapNonResultsInBounds).PreservesOperation
        o o oIn oIn'
  -- Clause 5: structure frame.
  /-- Blocks stay in bounds — successor-`InBounds` transport. -/
  blocksInBounds : ∀ (b : BlockPtr), b.InBounds ctx.raw → b.InBounds newCtx.raw
  /-- The number of arguments of every in-bounds block is preserved: op-list edits never add or
  remove block arguments. -/
  blockNumArgsPreserved : ∀ (bl : BlockPtr), bl.InBounds ctx.raw →
    bl.getNumArguments! newCtx.raw = bl.getNumArguments! ctx.raw
  /-- Every block argument's type is preserved. Note the full `Block.arguments` record is *not*
  preserved: each `BlockArgument` carries the head (`firstUse`) of its def-use chain, which the
  rewrite mutates (erasing `op` detaches its operands; redirecting `op`'s result-uses onto a forwarded
  `newValue` that is itself a block argument grows that argument's chain). The SSA-relevant data — the
  argument count (`blockNumArgsPreserved`) and per-argument type — is what survives and is all the
  block-argument frame consequences below need. -/
  blockArgTypesPreserved : ∀ (bl : BlockPtr), bl.InBounds ctx.raw →
    ∀ i, i < bl.getNumArguments! ctx.raw →
      (bl.getArgument i : ValuePtr).getType! newCtx.raw = (bl.getArgument i : ValuePtr).getType! ctx.raw
  blockDominatesPreserved : ∀ (b₁ b₂ : BlockPtr), b₁.InBounds ctx.raw → b₂.InBounds ctx.raw →
    (b₁.dominates b₂ newCtx ↔ b₁.dominates b₂ ctx)
  -- Clause 6: result well-formedness.
  /-- The target context is dominance-well-formed. -/
  newCtxDom : newCtx.Dom
  newCtxVerif : newCtx.Verified
  -- Clause 7: value-renaming frame for block arguments (PR 9 / `LocalRewritePattern.mapping`).
  /-- Every produced value dominates the post-insertion point in `block` — the `newCtx` analog of
  "after `op`", i.e. the end of the inserted `newOps` span (`afterLast newOps (atStart! block)`). This
  is the genuine SSA-validity condition on produced values, satisfied both by results of inserted
  `newOps` (defined within the span) and by forwarded pre-existing values in scope at `op`. It replaces
  the old `newValuesAreResults`, admitting general forwarding (`x + 0 → x`): `x` may be a block
  argument *or* a result of an operation defined before `op` — the latter is what the dominance-scoped
  `ReflectsResults` and `ReturnValuesDominate` together make sound (a forwarded surviving-op result
  cannot collide with `op`'s own result by SSA antisymmetry). -/
  newValuesDominate : ∀ v ∈ newValues,
    v.dominatesIp (InsertPoint.afterLast newOps.toList newCtx.raw
      (InsertPoint.atStart! block newCtx.raw)) newCtx
  -- Clause 8: region/block structure frame (the rewrite edits only operation lists).
  /-- The region list of every surviving operation is preserved: the rewrite only edits the operation
  list of `block`, never region structure. Gives equal region counts and equal region pointers across
  the two contexts (used to relate `interpretFunction`/`interpretRegion`). -/
  opRegionsPreserved : ∀ (o : OperationPtr), o.InBounds ctx.raw → o ≠ op →
    (o.get! newCtx.raw).regions = (o.get! ctx.raw).regions
  /-- The first block of every region is preserved by the rewrite, so `interpretRegion` starts the
  CFG walk from the same entry block in both contexts. -/
  regionFirstBlockPreserved : ∀ (r : RegionPtr), r.InBounds ctx.raw →
    (r.get! newCtx.raw).firstBlock = (r.get! ctx.raw).firstBlock
  /-- The enclosing operation of every surviving operation is preserved: the rewrite only edits
  operation lists, never the block→region→operation parent pointers along a survivor's spine. This is
  the "parent operations of surviving operations are preserved" promise of clause 5, and it is what
  lets `IsTopLevelFuncWithName` transport across the rewrite (so the module-refinement lift can pick
  the same surviving function in the target context). It is stated as an implication rather than a raw
  equality because a detached source region could in principle be attached when the rewrite creates a
  new operation — but a survivor that is *already* enclosed by some `enclosing` (its spine is fully
  parented) keeps that enclosing operation. -/
  getParentOpPreserved : ∀ (o enclosing : OperationPtr), o.InBounds ctx.raw → o ≠ op →
    o.getParentOp! ctx.raw = some enclosing →
    o.getParentOp! newCtx.raw = some enclosing
  -- Clause 9: the matched operation is not a function.
  /-- The matched operation `op` is not a function: it does not have exactly one region. Functions
  (the operations `interpretFunction` runs) have exactly one region, so this guarantees every function
  operation is distinct from `op` — the rewrite matches an operation *inside* a function body, never a
  function itself. This lets `interpretFunction_refinement` conclude `funcOp ≠ op` for any function it
  interprets, hence that the function survives the rewrite. -/
  opNotFunction : op.getNumRegions! ctx.raw ≠ 1

/-! ## Structural frame lemmas -/

variable {ctx newCtx : WfIRContext OpCode} {op : OperationPtr}
  {newOps : Array OperationPtr} {newValues : Array ValuePtr}
  {opIn : op.InBounds ctx.raw}
  {block : BlockPtr} {pre post : Array OperationPtr}
  {blockIn : block.InBounds ctx.raw} {blockIn' : block.InBounds newCtx.raw}

namespace RewrittenAt

/-- In-bounds witness for the redirect branch of `σ` (`rewriteMapping`): each produced value is in
bounds of the target context. Derived from `newValuesSize`/`newValuesInBounds` (it used to be a field).
Exposed under the `RewrittenAt` namespace so the `rewriteMapping` callsites can keep writing
`h.mapResultsInBounds`. -/
theorem mapResultsInBounds
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ (index : Nat), index < (op.getResults! ctx.raw).size →
      newValues[index]!.InBounds newCtx.raw :=
  rewriteMapping_resultsInBounds op newValues h.newValuesSize h.newValuesInBounds

/-- The fixed renaming performed by the rewrite: `rewriteMapping` applied to the in-bounds witnesses
carried by the `RewrittenAt` instance. This is *not* a parameter of `RewrittenAt`; it is a function of
the instance (the lemmas below refer to it as `h.σ`). -/
abbrev σ (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ValueMapping ctx newCtx :=
  rewriteMapping op newValues h.mapResultsInBounds h.mapNonResultsInBounds

/-- `σ` fixes every value that is not a result of `op`. `LocalRewritePattern.mapping` is the identity
except on `op`'s results (which it redirects to `newValues`), so every other value — in particular
every block argument, which is never an `op` result — is left untouched: `rewriteMapping` takes its
`else` branch. This used to be a field; it is purely a fact about `rewriteMapping`, independent of the
other `RewrittenAt` data. It discharges the `hFix`/`hReflectArgs` frame hypotheses of
`setArgumentValues?_isRefinedByAt`. -/
theorem mappingFixesNonResults
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    (v : ValuePtr) (vIn : v.InBounds ctx.raw) (hv : v ∉ op.getResults! ctx.raw) :
    ((rewriteMapping op newValues
        (rewriteMapping_resultsInBounds op newValues h.newValuesSize h.newValuesInBounds)
        h.mapNonResultsInBounds) ⟨v, vIn⟩).val = v := by
  simp only [rewriteMapping, dif_neg hv]

/-- `op` lives in `block`: derived from `srcList`, since `op` occurs in `block`'s operation list. -/
theorem opParent (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    (op.get! ctx.raw).parent = some block :=
  (BlockPtr.operationList.mem opIn).mpr (by rw [h.srcList]; simp [Array.mem_append])

/-- Every new operation is in bounds of the target context. -/
theorem newOpsInBounds (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ newOp ∈ newOps, newOp.InBounds newCtx.raw :=
  fun newOp hmem => ((h.newOpsFresh newOp).mp hmem).1

/-- New operations are fresh: none of them is in bounds of the source context. -/
theorem newOps_not_inBounds_source (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ newOp ∈ newOps, ¬ newOp.InBounds ctx.raw :=
  fun newOp hmem => ((h.newOpsFresh newOp).mp hmem).2

/-- The matched operation is not among the new operations (it is erased, they are fresh). -/
theorem op_not_mem_newOps (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    op ∉ newOps := by
  intro hmem
  exact (h.newOps_not_inBounds_source op hmem) opIn

/-- A surviving operation carries the `CrossContextFrame` data — repackaged so the source/target
in-bounds proofs do not need to be supplied at the call site. -/
theorem frame_of_ne (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    {o : OperationPtr} (oIn : o.InBounds ctx.raw) (hne : o ≠ op) :
    (h.σ).PreservesOperation o o oIn (h.survives o oIn hne) :=
  h.frame o oIn (h.survives o oIn hne) hne

/-- Every `pre` operation is in bounds of the source context (it lies in the source block list). -/
theorem preInBounds (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ o ∈ pre.toList, o.InBounds ctx.raw := by
  intro o ho
  have hchain := BlockPtr.operationListWF ctx.raw block blockIn ctx.wellFormed
  rw [h.srcList] at hchain
  exact hchain.arrayInBounds (by simp only [Array.mem_append]; grind)

/-- Every `post` operation is in bounds of the source context (it lies in the source block list). -/
theorem postInBounds (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ o ∈ post.toList, o.InBounds ctx.raw := by
  intro o ho
  have hchain := BlockPtr.operationListWF ctx.raw block blockIn ctx.wellFormed
  rw [h.srcList] at hchain
  exact hchain.arrayInBounds (by simp only [Array.mem_append]; grind)

/-- `op` does not appear in `pre`: the source block list `pre ++ #[op] ++ post` is `Nodup`. -/
theorem opNotMemPre (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    op ∉ pre.toList := by
  have hchain := BlockPtr.operationListWF ctx.raw block blockIn ctx.wellFormed
  have hnodup := BlockPtr.OpChain_array_toList_Nodup hchain
  rw [h.srcList] at hnodup
  simp only [Array.append_assoc, Array.toList_append, List.nodup_append] at hnodup
  grind

/-- `op` does not appear in `post`: the source block list `pre ++ #[op] ++ post` is `Nodup`. -/
theorem opNotMemPost (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    op ∉ post.toList := by
  have hchain := BlockPtr.operationListWF ctx.raw block blockIn ctx.wellFormed
  have hnodup := BlockPtr.OpChain_array_toList_Nodup hchain
  rw [h.srcList] at hnodup
  simp only [Array.append_assoc, Array.toList_append, List.nodup_append] at hnodup
  grind

/-- Every `pre` operation is in bounds of the target context (it lies in the target block list). -/
theorem preInBounds' (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ o ∈ pre.toList, o.InBounds newCtx.raw := by
  intro o ho
  have hchain := BlockPtr.operationListWF newCtx.raw block blockIn' newCtx.wellFormed
  rw [h.tgtList] at hchain
  exact hchain.arrayInBounds (by simp only [Array.mem_append]; grind)

/-- Every new operation is in bounds of the target context, as a `List` membership statement. -/
theorem newOpsInBounds' (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ o ∈ newOps.toList, o.InBounds newCtx.raw :=
  fun o ho => h.newOpsInBounds o (by simpa using ho)

/-- Every `post` operation is in bounds of the target context (it lies in the target block list). -/
theorem postInBounds' (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ o ∈ post.toList, o.InBounds newCtx.raw := by
  intro o ho
  have hchain := BlockPtr.operationListWF newCtx.raw block blockIn' newCtx.wellFormed
  rw [h.tgtList] at hchain
  exact hchain.arrayInBounds (by simp only [Array.mem_append]; grind)

/-- Every `pre` operation has `block` as its parent in the source context (it lies in the source
block list). -/
theorem preParent (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ o ∈ pre.toList, ∃ block, (o.get! ctx.raw).parent = some block := by
  intro o ho
  have hchain := BlockPtr.operationListWF ctx.raw block blockIn ctx.wellFormed
  rw [h.srcList] at hchain
  exact ⟨block, hchain.opParent (by simp only [Array.mem_append]; grind)⟩

/-- Every `pre` operation has `block` as its parent in the target context (it lies in the target
block list). -/
theorem preParent' (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ o ∈ pre.toList, ∃ block, (o.get! newCtx.raw).parent = some block := by
  intro o ho
  have hchain := BlockPtr.operationListWF newCtx.raw block blockIn' newCtx.wellFormed
  rw [h.tgtList] at hchain
  exact ⟨block, hchain.opParent (by simp only [Array.mem_append]; grind)⟩

/-- Every new operation has `block` as its parent in the target context (it lies in the target
block list). -/
theorem newOpsParent' (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ o ∈ newOps.toList, ∃ block, (o.get! newCtx.raw).parent = some block := by
  intro o ho
  have hchain := BlockPtr.operationListWF newCtx.raw block blockIn' newCtx.wellFormed
  rw [h.tgtList] at hchain
  exact ⟨block, hchain.opParent (by simp only [Array.mem_append]; grind)⟩

/-- Every `post` operation has `block` as its parent in the target context (it lies in the target
block list). -/
theorem postParent' (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ o ∈ post.toList, ∃ block, (o.get! newCtx.raw).parent = some block := by
  intro o ho
  have hchain := BlockPtr.operationListWF newCtx.raw block blockIn' newCtx.wellFormed
  rw [h.tgtList] at hchain
  exact ⟨block, hchain.opParent (by simp only [Array.mem_append]; grind)⟩

/-- Every `pre` operation has `block` as its parent in the source context. -/
theorem preParentEq (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ o ∈ pre.toList, (o.get! ctx.raw).parent = some block := by
  intro o ho
  have hchain := BlockPtr.operationListWF ctx.raw block blockIn ctx.wellFormed
  rw [h.srcList] at hchain
  exact hchain.opParent (by simp only [Array.mem_append]; grind)

/-- Every `pre` operation has `block` as its parent in the target context. -/
theorem preParentEq' (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ o ∈ pre.toList, (o.get! newCtx.raw).parent = some block := by
  intro o ho
  have hchain := BlockPtr.operationListWF newCtx.raw block blockIn' newCtx.wellFormed
  rw [h.tgtList] at hchain
  exact hchain.opParent (by simp only [Array.mem_append]; grind)

/-- Every new operation has `block` as its parent in the target context. -/
theorem newOpsParentEq' (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ o ∈ newOps.toList, (o.get! newCtx.raw).parent = some block := by
  intro o ho
  have hchain := BlockPtr.operationListWF newCtx.raw block blockIn' newCtx.wellFormed
  rw [h.tgtList] at hchain
  exact hchain.opParent (by simp only [Array.mem_append]; grind)

/-- Every `post` operation has `block` as its parent in the source context. -/
theorem postParentEq (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ o ∈ post.toList, (o.get! ctx.raw).parent = some block := by
  intro o ho
  have hchain := BlockPtr.operationListWF ctx.raw block blockIn ctx.wellFormed
  rw [h.srcList] at hchain
  exact hchain.opParent (by simp only [Array.mem_append]; grind)

/-- Every `post` operation has `block` as its parent in the target context. -/
theorem postParentEq' (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ∀ o ∈ post.toList, (o.get! newCtx.raw).parent = some block := by
  intro o ho
  have hchain := BlockPtr.operationListWF newCtx.raw block blockIn' newCtx.wellFormed
  rw [h.tgtList] at hchain
  exact hchain.opParent (by simp only [Array.mem_append]; grind)

/-! ### Block-argument frame consequences (clause 7) -/

/-- The number of arguments of any in-bounds block is preserved by the rewrite. -/
theorem numArgsEq (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    {bl : BlockPtr} (blIn : bl.InBounds ctx.raw) :
    bl.getNumArguments! newCtx.raw = bl.getNumArguments! ctx.raw :=
  h.blockNumArgsPreserved bl blIn

/-- The type of any (in-range) block argument is preserved by the rewrite. -/
theorem argType_eq (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    {bl : BlockPtr} (blIn : bl.InBounds ctx.raw) (i : Nat) (hi : i < bl.getNumArguments! ctx.raw) :
    (bl.getArgument i : ValuePtr).getType! newCtx.raw = (bl.getArgument i : ValuePtr).getType! ctx.raw :=
  h.blockArgTypesPreserved bl blIn i hi

/-- A block argument is never a result of `op` (distinct `ValuePtr` constructors). -/
theorem blockArg_notMem_getResults
    (_h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    {bl : BlockPtr} {i : Nat} :
    (bl.getArgument i : ValuePtr) ∉ op.getResults! ctx.raw := by
  simp only [OperationPtr.getResults!.mem_iff_exists_index]
  rintro ⟨index, _, heq⟩
  simp [BlockPtr.getArgument, OperationPtr.getResult_def] at heq

/-- `σ` fixes block-argument pointers: it maps `bl.getArgument i` to itself. Discharges the `hFix`
hypothesis of `setArgumentValues?_isRefinedByAt`. -/
theorem mappingFixesArg
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    {bl : BlockPtr} {i : Nat} (vIn : (bl.getArgument i : ValuePtr).InBounds ctx.raw) :
    (h.σ ⟨(bl.getArgument i : ValuePtr), vIn⟩).val = (bl.getArgument i : ValuePtr) :=
  h.mappingFixesNonResults _ vIn h.blockArg_notMem_getResults

/-- `σ` fixes a block's argument array: applying it to `bl`'s source arguments yields the same
arguments in the target context. Discharges the `hArgs` hypothesis of
`setArgumentValues?_isRefinedByAt`. -/
theorem argsApplyToArray
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    {bl : BlockPtr} (blIn : bl.InBounds ctx.raw) :
    bl.getArguments! newCtx.raw = h.σ.applyToArray (bl.getArguments! ctx.raw) := by
  apply Array.ext
  · simp [h.numArgsEq blIn]
  · intro i h1 _h2
    simp only [BlockPtr.getArguments!.size_eq_getNumArguments!] at h1
    have hi : i < bl.getNumArguments! ctx.raw := h.numArgsEq blIn ▸ h1
    simp only [ValueMapping.applyToArray, Array.getElem_map, Array.getElem_attach,
      BlockPtr.getArguments!.getElem_eq_getArgument h1,
      BlockPtr.getArguments!.getElem_eq_getArgument hi]
    exact (h.mappingFixesArg (i := i) (bl := bl) (by grind)).symm

/-- A result of `op` is mapped by `σ` into `newValues`. -/
theorem mapping_getResult_mem_newValues
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    {val : ValuePtr} (valIn : val.InBounds ctx.raw) (hMem : val ∈ op.getResults! ctx.raw) :
    (h.σ ⟨val, valIn⟩).val ∈ newValues := by
  have hx : (h.σ ⟨val, valIn⟩).val ∈ (h.σ).applyToArray (op.getResults! ctx.raw) := by
    simp only [ValueMapping.applyToArray, Array.mem_map, Array.mem_attach, true_and]
    exact ⟨⟨val, hMem⟩, rfl⟩
  rw [rewriteMapping_applyToArray_getResults op newValues h.mapResultsInBounds
    h.mapNonResultsInBounds h.newValuesSize] at hx
  exact hx

/-- The block-argument *pointer* array of `bl` is identical across the two contexts: `getArguments!`
is `getArgument` mapped over `range (getNumArguments! ·)`, so it depends only on the argument count,
which the rewrite preserves (`blockNumArgsPreserved`). -/
theorem getArguments!_eq
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    {bl : BlockPtr} (blIn : bl.InBounds ctx.raw) :
    bl.getArguments! newCtx.raw = bl.getArguments! ctx.raw := by
  simp only [BlockPtr.getArguments!, h.blockNumArgsPreserved bl blIn]

/-- `σ` never maps an in-scope value onto one of `bl`'s block arguments unless it already is that
block argument: a value not in `bl`'s arguments is either fixed by `σ` (so stays out of the
arguments), or a result `r` of `op` and then a cross-block antisymmetry argument applies. If `bl` is
`block` itself, `r` does not dominate `block`'s entry (SSA), contradicting `hdom`. If `bl ≠ block`,
then the image `σ r` (which dominates the post-insertion point inside `block`) being a `bl`-argument
would force `bl` to dominate `block`, while `hdom` forces `block` to dominate `bl`; antisymmetry gives
`bl = block`, a contradiction. Discharges the `hImageNotArg` hypothesis of
`setArgumentValues?_isRefinedByAt`. -/
theorem mappingImageNotArg
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    (ctxDom : ctx.Dom)
    {bl : BlockPtr} (blIn : bl.InBounds ctx.raw) {val : ValuePtr} (valIn : val.InBounds ctx.raw)
    (hNotArg : val ∉ bl.getArguments! ctx.raw)
    (hdom : val.dominatesIp (InsertPoint.atStart! bl ctx.raw) ctx) :
    (h.σ ⟨val, valIn⟩).val ∉ bl.getArguments! newCtx.raw := by
  by_cases hMem : val ∈ op.getResults! ctx.raw
  · -- `val` is a result `r` of `op`, which lives in `block`.
    have opInBlock : op ∈ block.operationList ctx.raw ctx.wellFormed blockIn := by
      rw [h.srcList]; simp
    by_cases hbl : bl = block
    · -- `bl = block`: `r` cannot dominate `block`'s own entry (SSA), contradicting `hdom`.
      subst hbl
      exact absurd hdom (ctxDom.opResult_not_dominatesIp_atStart! opIn blockIn opInBlock hMem)
    · -- `bl ≠ block`: cross-block antisymmetry rules out `σ r ∈ bl.args`.
      intro hσMem
      have hImgMem := h.mapping_getResult_mem_newValues valIn hMem
      have hσDom := h.newValuesDominate _ hImgMem
      have hops : ∀ o ∈ newOps.toList,
          o ∈ block.operationList newCtx.raw newCtx.wellFormed blockIn' := by
        intro o ho
        rw [Array.mem_toList_iff] at ho
        rw [h.tgtList]
        exact Array.mem_append.mpr (Or.inl (Array.mem_append.mpr (Or.inr ho)))
      have hBlDomBlock : bl.dominates block newCtx :=
        WfIRContext.Dom.block_dominates_of_arg_dominatesIp_afterLast h.newCtxDom
          (h.blocksInBounds bl blIn) blockIn' hσMem hops hσDom
      have hBlockDomBl : block.dominates bl newCtx :=
        (h.blockDominatesPreserved block bl blockIn blIn).mpr
          (WfIRContext.Dom.block_dominates_of_opResult_dominatesIp_atStart! ctxDom opIn blockIn blIn
            opInBlock hMem hdom)
      exact hbl (BlockPtr.dominates_antisymm hBlDomBlock hBlockDomBl)
  · rw [h.getArguments!_eq blIn, h.mappingFixesNonResults val valIn hMem]
    exact hNotArg

/-- Every new operation is verified in the target context. Derived from `newCtxVerif`: the target
context is verified, so every in-bounds operation (in particular every `newOp`) satisfies its local
invariants. -/
theorem newOpsVerif
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    (o : OperationPtr) (oIn : o.InBounds newCtx.raw) (_ : o ∈ newOps) :
    o.Verified newCtx oIn :=
  OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants h.newCtxVerif oIn

/-- The number of regions of a surviving operation is preserved by the rewrite. -/
theorem getNumRegions_eq
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    {o : OperationPtr} (oIn : o.InBounds ctx.raw) (hne : o ≠ op) :
    o.getNumRegions newCtx.raw (h.survives o oIn hne) = o.getNumRegions ctx.raw oIn := by
  simp only [OperationPtr.getNumRegions, ← OperationPtr.get!_eq_get, h.opRegionsPreserved o oIn hne]

/-- The `i`-th region pointer of a surviving operation is preserved by the rewrite. -/
theorem getRegion_eq
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    {o : OperationPtr} (oIn : o.InBounds ctx.raw) (hne : o ≠ op)
    (i : Nat) (hi : i < o.getNumRegions ctx.raw oIn) :
    o.getRegion newCtx.raw i (h.survives o oIn hne) (by rw [h.getNumRegions_eq oIn hne]; exact hi)
      = o.getRegion ctx.raw i oIn hi := by
  simp only [OperationPtr.getRegion, ← OperationPtr.get!_eq_get, h.opRegionsPreserved o oIn hne]

end RewrittenAt

/-! ## Block-`B` simulation (PR 7)

The simulation for the rewritten block `B`: interpreting `B`'s operation list `pre ++ [op] ++ post`
in the source context is refined by interpreting `pre ++ newOps ++ post` in the target context, under
the rewrite renaming `σ`.

The proof (below) splits the list with `interpretTerminatedOpList_append` and dispatches on the source
outcome at the matched operation `op`:

* **`pre` (identical list)** — cross-context monotonicity `interpretOpList_monoAt` (PR 3), fed the
  `CrossContextFrame`s of clause 4; this also threads `EquationLemmaAt`/`DefinesDominating` to `op`.
* **`[op]` vs `newOps`** — the local op-step simulation `hOpSim`, which PR 8 discharges from
  `PreservesSemantics` (bridging its create-only context to the inserted/erased `newCtx` via clause 4).
* **`post` (same pointers, redirected operands)** — `interpretOpList_monoAt` again, now under `σ`,
  seeded by the post-`op` state from the previous regime.
* **source `.ub` at `op`** — a source `ub` refines any target outcome, so no target-progress argument
  is needed: cross-context monotonicity (`interpretOpList_monoAt`) discharges this regime directly.

The `hOpSim` hypothesis is the local op→`newOps` simulation, stated so PR 8 can supply it: refined,
SSA-valid entry states map a source `interpretOp op` step onto a target `interpretOpList newOps` run,
preserving `σ`-refinement and refining the (optional) control-flow action.
-/

/-- Membership/in-bounds for the source block list `pre ++ [op] ++ post`. -/
theorem sourceListIn {ctx : WfIRContext OpCode} {op : OperationPtr} {pre post : Array OperationPtr}
    (opIn : op.InBounds ctx.raw)
    (preIn : ∀ o ∈ pre.toList, o.InBounds ctx.raw) (postIn : ∀ o ∈ post.toList, o.InBounds ctx.raw) :
    ∀ o ∈ pre.toList ++ [op] ++ post.toList, o.InBounds ctx.raw := by
  intro o ho
  simp only [List.mem_append, List.mem_singleton] at ho
  rcases ho with (h | h) | h
  · exact preIn o h
  · exact h ▸ opIn
  · exact postIn o h

/-- Membership/in-bounds for the target block list `pre ++ newOps ++ post`. -/
theorem targetListIn {newCtx : WfIRContext OpCode} {pre newOps post : Array OperationPtr}
    (preIn' : ∀ o ∈ pre.toList, o.InBounds newCtx.raw)
    (newOpsIn' : ∀ o ∈ newOps.toList, o.InBounds newCtx.raw)
    (postIn' : ∀ o ∈ post.toList, o.InBounds newCtx.raw) :
    ∀ o ∈ pre.toList ++ newOps.toList ++ post.toList, o.InBounds newCtx.raw := by
  intro o ho
  simp only [List.mem_append] at ho
  rcases ho with (h | h) | h
  · exact preIn' o h
  · exact newOpsIn' o h
  · exact postIn' o h

/--
The local op-step simulation consumed by the block-`B` proof: under `σ`-refined, SSA-valid entry
states, the source `interpretOp op` step is refined by the target `interpretOpList newOps` run,
preserving `σ`-refinement of the states and refining the optional control-flow action.

PR 8 discharges this from `LocalRewritePattern.PreservesSemantics` (with `σ = LocalRewritePattern.mapping`),
bridging the create-only context where `PreservesSemantics` is stated to the inserted/erased `newCtx`.

The `hCouple` hypothesis records that the target scope point `p'` is the *image of `before op`* under the
rewrite: every value dominating `before op` in the source still dominates `p'` in the target. This is
what lets the bridge move the source-side `PreservesSemantics` refinement (scoped at `before op` in the
create-only context) onto the given `hRef` (scoped at `p'` in `newCtx`). It holds at the sole call site,
where `p'` is the `newOps` insertion point `afterLast pre (atStart! block)` — the point `op` occupied.
-/
def OpStepSimulation
    {ctx newCtx : WfIRContext OpCode} (op : OperationPtr) (newOps : Array OperationPtr)
    (μ : ValueMapping ctx newCtx) (opIn : op.InBounds ctx.raw)
    (newOpsIn' : ∀ o ∈ newOps.toList, o.InBounds newCtx.raw) : Prop :=
  ∀ (s : InterpreterState ctx) (s' : InterpreterState newCtx)
    (p' : InsertPoint) (p'In : p'.InBounds newCtx.raw)
    (qIn : (InsertPoint.after! op ctx.raw).InBounds ctx.raw)
    (q'In : (InsertPoint.afterLast newOps.toList newCtx.raw p').InBounds newCtx.raw),
    (∀ (v : ValuePtr) (vIn : v.InBounds ctx.raw),
      v.dominatesIp (InsertPoint.before op) ctx → (μ ⟨v, vIn⟩).val.dominatesIp p' newCtx) →
    s.isRefinedByAt s' μ (InsertPoint.before op) p' →
    s.EquationLemmaAt (InsertPoint.before op) →
    s'.EquationLemmaAt p' p'In →
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState newCtx × Option ControlFlowAction) =>
        r₁.1.isRefinedByAt r₂.1 μ
          (InsertPoint.after! op ctx.raw) (InsertPoint.afterLast newOps.toList newCtx.raw p')
          qIn q'In ∧
        ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOp op s)
      (interpretOpList newOps.toList s' newOpsIn')

/-- A prefix of an operation chain slice is itself an operation chain slice (the boundary `.next`-link
to the dropped suffix is the only condition lost, and it is not required for the prefix alone). -/
theorem BlockPtr.OpChainSlice.append_left {ctx : IRContext OpInfo} {block : BlockPtr} :
    ∀ {a b : List OperationPtr}, block.OpChainSlice ctx (a ++ b) →
      block.OpChainSlice ctx a := by
  intro a
  induction a with
  | nil => intro b _; exact BlockPtr.OpChainSlice.nil
  | cons x xs ih =>
    intro b h
    simp only [List.cons_append, BlockPtr.OpChainSlice.cons_iff] at h ⊢
    obtain ⟨hin, hparent, hnext, htail⟩ := h
    exact ⟨hin, hparent, fun c hc => hnext c (by cases xs <;> simp_all), ih htail⟩

/-- A suffix of an operation chain slice is itself an operation chain slice (dropping a prefix only
loses the boundary `.next`-link into the suffix, which the suffix alone does not require). -/
theorem BlockPtr.OpChainSlice.append_right {ctx : IRContext OpInfo} {block : BlockPtr} :
    ∀ {a b : List OperationPtr}, block.OpChainSlice ctx (a ++ b) →
      block.OpChainSlice ctx b := by
  intro a
  induction a with
  | nil => intro b h; simpa using h
  | cons x xs ih =>
    intro b h
    rw [List.cons_append, BlockPtr.OpChainSlice.cons_iff] at h
    exact ih h.2.2.2

/-- The trailing `.next`-link of an operation chain slice `l ++ [x]`: the last operation of `l` points
to `x`. -/
theorem BlockPtr.OpChainSlice.getLast?_next_eq {ctx : IRContext OpInfo} {block : BlockPtr}
    {l : List OperationPtr} {x lastOp : OperationPtr}
    (h : block.OpChainSlice ctx (l ++ [x])) (hl : l.getLast? = some lastOp) :
    (lastOp.get! ctx).next = some x := by
  induction l with
  | nil => simp at hl
  | cons a t ih =>
    rw [List.cons_append, BlockPtr.OpChainSlice.cons_iff] at h
    obtain ⟨_, _, hnext, htail⟩ := h
    cases t with
    | nil =>
      obtain rfl : a = lastOp := by simpa using hl
      exact hnext x (by simp)
    | cons b t' => exact ih htail (by simpa using hl)

/-- An operation chain slice characterized by its per-element data: every operation is in bounds, has
the expected parent, and links by `.next` to its successor in the list. -/
theorem BlockPtr.OpChainSlice.of_getElem {ctx : IRContext OpInfo} {block : BlockPtr}
    {l : List OperationPtr}
    (hin : ∀ o ∈ l, o.InBounds ctx)
    (hparent : ∀ o ∈ l, (o.get! ctx).parent = some block)
    (hnext : ∀ (i : Nat) (hi : i + 1 < l.length),
      ((l[i]'(Nat.lt_of_succ_lt hi)).get! ctx).next = some (l[i + 1]'hi)) :
    block.OpChainSlice ctx l := by
  induction l with
  | nil => exact BlockPtr.OpChainSlice.nil
  | cons a l ih =>
    rw [BlockPtr.OpChainSlice.cons_iff]
    refine ⟨hin a (by simp), hparent a (by simp), fun b hb => ?_,
      ih (fun o ho => hin o (List.mem_cons_of_mem a ho))
        (fun o ho => hparent o (List.mem_cons_of_mem a ho)) (fun i hi => ?_)⟩
    · cases l with
      | nil => simp at hb
      | cons a' l' =>
        simp only [List.head?_cons, Option.some.injEq] at hb
        subst hb
        simpa using hnext 0 (by simp only [List.length_cons]; omega)
    · have hh := hnext (i + 1) (by simp only [List.length_cons]; omega)
      simp only [List.getElem_cons_succ] at hh
      exact hh

/-- The operations of a block (its `OpChain` array) form an operation chain slice of that block. -/
theorem BlockPtr.OpChain.opChainSlice {ctx : WfIRContext OpCode} {block : BlockPtr}
    {array : Array OperationPtr} (h : BlockPtr.OpChain block ctx.raw array) :
    block.OpChainSlice ctx.raw array.toList := by
  apply BlockPtr.OpChainSlice.of_getElem
  · intro o ho; exact h.arrayInBounds (by simpa using ho)
  · intro o ho; exact h.opParent (by simpa using ho)
  · intro i hi
    have hsize : i + 1 < array.size := by simpa using hi
    have hnext := h.next (i := i) (Nat.lt_of_succ_lt hsize)
    rw [Array.getElem?_eq_getElem hsize] at hnext
    simpa using hnext

/-- The source block list `pre ++ [op] ++ post` is an operation chain slice of `block`. -/
theorem RewrittenAt.srcChain
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    block.OpChainSlice ctx.raw (pre.toList ++ [op] ++ post.toList) := by
  have hchain := BlockPtr.operationListWF ctx.raw block blockIn ctx.wellFormed
  rw [h.srcList] at hchain
  simpa using hchain.opChainSlice

/-- The target block list `pre ++ newOps ++ post` is an operation chain slice of `block`. -/
theorem RewrittenAt.tgtChain
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    block.OpChainSlice newCtx.raw (pre.toList ++ newOps.toList ++ post.toList) := by
  have hchain := BlockPtr.operationListWF newCtx.raw block blockIn' newCtx.wellFormed
  rw [h.tgtList] at hchain
  simpa using hchain.opChainSlice

/-- The first operation of `block` in the target context is the head of the target block list
`pre ++ newOps ++ post` (the block's op chain via `tgtList`/`OpChain.first`). -/
theorem RewrittenAt.tgtFirstOp
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    (block.get! newCtx.raw).firstOp = (pre.toList ++ newOps.toList ++ post.toList).head? := by
  have hchain := BlockPtr.operationListWF newCtx.raw block blockIn' newCtx.wellFormed
  rw [h.tgtList] at hchain
  rw [hchain.first]
  simp [List.head?_eq_getElem?, ← Array.toList_append]

/-- The first operation of `block` in the source context is the head of the source block list
`pre ++ [op] ++ post` (the block's op chain via `srcList`/`OpChain.first`). -/
theorem RewrittenAt.srcFirstOp
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    (block.get! ctx.raw).firstOp = (pre.toList ++ [op] ++ post.toList).head? := by
  have hchain := BlockPtr.operationListWF ctx.raw block blockIn ctx.wellFormed
  rw [h.srcList] at hchain
  rw [hchain.first]
  simp [List.head?_eq_getElem?, ← Array.getElem?_toList]

/-- The source prefix `pre ++ [op]` is an operation chain slice of `block`. -/
theorem RewrittenAt.preChainOp
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    block.OpChainSlice ctx.raw (pre.toList ++ [op]) :=
  h.srcChain.append_left

/-- The target `pre` segment is an operation chain slice of `block`. -/
theorem RewrittenAt.preChain'
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    block.OpChainSlice newCtx.raw pre.toList := by
  have hc := h.tgtChain
  rw [List.append_assoc] at hc
  exact hc.append_left

/-- The target `post` segment is an operation chain slice of `block`. -/
theorem RewrittenAt.postChain'
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    block.OpChainSlice newCtx.raw post.toList :=
  h.tgtChain.append_right


/-- Bridge `interpretOpList_equationLemmaAt` to the *before-`nextOp`* framing used by the block
simulation: given an operation chain slice `ops ++ [nextOp]` and a run of `ops` that completes without
a terminator, the resulting state satisfies the SSA invariant at the point *before* `nextOp` — the
operation that follows the run in the chain. (`interpretOpList_equationLemmaAt` concludes at the point
*after* the last run operation; the chain link `getLast?_next_eq` identifies that point with
`before nextOp`.) -/
theorem interpretOpList_equationLemmaAt_before {ctx : WfIRContext OpCode}
    {block : BlockPtr} {ops : List OperationPtr} {nextOp : OperationPtr}
    {state state' : InterpreterState ctx}
    (ctxDom : ctx.Dom)
    (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw)
    (nextOpIn : nextOp.InBounds ctx.raw)
    (hChain : block.OpChainSlice ctx.raw (ops ++ [nextOp]))
    (stateWf : ∀ fst (h : fst ∈ ops ++ [nextOp]), (ops ++ [nextOp]).head? = some fst →
                 state.EquationLemmaAt (.before fst)
                   (by simp only [List.mem_append, List.mem_singleton] at h
                       rcases h with h | h
                       · exact opsIn fst h
                       · exact h ▸ nextOpIn))
    (hrun : interpretOpList ops state opsIn = some (.ok (state', none))) :
    state'.EquationLemmaAt (.before nextOp) nextOpIn := by
  cases ops with
  | nil =>
    rw [interpretOpList_nil] at hrun
    obtain rfl : state = state' := by grind
    exact stateWf nextOp (by simp) (by simp)
  | cons a l =>
    obtain ⟨lastOp, hlast⟩ : ∃ lastOp, (a :: l).getLast? = some lastOp := by
      cases hg : (a :: l).getLast? with
      | none => simp at hg
      | some x => exact ⟨x, rfl⟩
    have hEq := interpretOpList_equationLemmaAt ctxDom hChain.append_left (by simp)
      (stateWf a (by simp) (by simp)) hlast hrun
    simp only [InsertPoint.after_eq_of_some_next (hChain.getLast?_next_eq hlast)] at hEq
    exact hEq

/-- Bridge `interpretOpList_DefinesDominating` to the *before-`nextOp`* framing: given an operation
chain slice `ops ++ [nextOp]` and a run of `ops` that completes without a terminator, the resulting
state defines every value dominating the point *before* `nextOp`. -/
theorem interpretOpList_DefinesDominating_before {ctx : WfIRContext OpCode}
    {block : BlockPtr} {ops : List OperationPtr} {nextOp : OperationPtr}
    {state state' : InterpreterState ctx}
    (ctxDom : ctx.Dom)
    (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw)
    (nextOpIn : nextOp.InBounds ctx.raw)
    (hChain : block.OpChainSlice ctx.raw (ops ++ [nextOp]))
    (stateDom : ∀ fst (h : fst ∈ ops ++ [nextOp]), (ops ++ [nextOp]).head? = some fst →
                 state.DefinesDominating (.before fst)
                   (by simp only [List.mem_append, List.mem_singleton] at h
                       rcases h with h | h
                       · exact opsIn fst h
                       · exact h ▸ nextOpIn))
    (hrun : interpretOpList ops state opsIn = some (.ok (state', none))) :
    state'.DefinesDominating (.before nextOp) nextOpIn := by
  cases ops with
  | nil =>
    rw [interpretOpList_nil] at hrun
    obtain rfl : state = state' := by grind
    exact stateDom nextOp (by simp) (by simp)
  | cons a l =>
    obtain ⟨lastOp, hlast⟩ : ∃ lastOp, (a :: l).getLast? = some lastOp := by
      cases hg : (a :: l).getLast? with
      | none => simp at hg
      | some x => exact ⟨x, rfl⟩
    have hDom := interpretOpList_DefinesDominating ctxDom hChain.append_left (by simp)
      (stateDom a (by simp) (by simp)) hlast hrun
    simp only [InsertPoint.after_eq_of_some_next (hChain.getLast?_next_eq hlast)] at hDom
    exact hDom

/-- Landing `EquationLemmaAt` at the `afterLast` end point of a block prefix. Running a block-prefix
`ops` (a chain slice starting at the block entry) from a state satisfying the SSA invariant at the
block start yields a state satisfying it at `afterLast ops (atStart! block)` — the point reached just
after the prefix. This is the target-side feeder for `OpStepSimulation`'s new `s'.EquationLemmaAt p'`
hypothesis, where `p'` is the `newOps` insertion point `afterLast pre (atStart! block)`. -/
theorem interpretOpList_equationLemmaAt_afterLast_atStart {ctx : WfIRContext OpCode}
    {block : BlockPtr} {ops : List OperationPtr} {state state' : InterpreterState ctx}
    (ctxDom : ctx.Dom) (bIn : block.InBounds ctx.raw)
    (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw)
    (hChain : block.OpChainSlice ctx.raw ops)
    (hFirstOfHead : ∀ h, ops.head? = some h → (block.get! ctx.raw).firstOp = some h)
    (hstart : state.EquationLemmaAt (InsertPoint.atStart! block ctx.raw)
      ((InsertPoint.inBounds_atStart! ctx.wellFormed bIn).mpr bIn))
    (pIn : (InsertPoint.afterLast ops ctx.raw (InsertPoint.atStart! block ctx.raw)).InBounds ctx.raw)
    (hrun : interpretOpList ops state opsIn = some (.ok (state', none))) :
    state'.EquationLemmaAt
      (InsertPoint.afterLast ops ctx.raw (InsertPoint.atStart! block ctx.raw)) pIn := by
  cases ops with
  | nil =>
    rw [interpretOpList_nil] at hrun
    obtain rfl : state = state' := by grind
    simpa only [InsertPoint.afterLast_nil] using hstart
  | cons a t =>
    obtain ⟨lastOp, hlast⟩ : ∃ lastOp, (a :: t).getLast? = some lastOp := by
      cases hg : (a :: t).getLast? with
      | none => simp at hg
      | some x => exact ⟨x, rfl⟩
    have hfa : (block.get! ctx.raw).firstOp = some a := hFirstOfHead a (by simp)
    have eqPtS : ∀ {p₁ p₂ : InsertPoint} {w1 : p₁.InBounds ctx.raw} {w2 : p₂.InBounds ctx.raw},
        p₁ = p₂ → state.EquationLemmaAt p₁ w1 → state.EquationLemmaAt p₂ w2 := by
      intro p₁ p₂ w1 w2 hp h; subst hp; exact h
    have hstart' : state.EquationLemmaAt (InsertPoint.before a) :=
      eqPtS (by simp only [InsertPoint.atStart!, hfa]) hstart
    have hEq := interpretOpList_equationLemmaAt ctxDom hChain (by simp) hstart' hlast hrun
    have lastIn : lastOp.InBounds ctx.raw :=
      hChain.inBounds_of_mem lastOp (List.mem_of_getLast? hlast)
    have lastParent : (lastOp.get! ctx.raw).parent = some block :=
      hChain.parent_of_mem lastOp (List.mem_of_getLast? hlast)
    have hpt : InsertPoint.afterLast (a :: t) ctx.raw (InsertPoint.atStart! block ctx.raw)
        = InsertPoint.after lastOp ctx.raw block := by
      simp only [InsertPoint.afterLast, hlast]
      rw [InsertPoint.after!_eq_after lastParent lastIn]
    have eqPt : ∀ {p₁ p₂ : InsertPoint} {w1 : p₁.InBounds ctx.raw} {w2 : p₂.InBounds ctx.raw},
        p₁ = p₂ → state'.EquationLemmaAt p₁ w1 → state'.EquationLemmaAt p₂ w2 := by
      intro p₁ p₂ w1 w2 hp h; subst hp; exact h
    exact eqPt hpt.symm hEq

/-- Interpreting a singleton operation list is interpreting the operation. -/
theorem interpretOpList_singleton {ctx : WfIRContext OpCode} {op : OperationPtr}
    {state : InterpreterState ctx} (h : ∀ o ∈ [op], o.InBounds ctx.raw) :
    interpretOpList [op] state h = interpretOp op state (h op (by simp)) := by
  rw [interpretOpList_cons]
  rcases interpretOp op state (h op (by simp)) with _ | (⟨s, a⟩ | _)
  · rfl
  · cases a <;> simp [interpretOpList_nil]
  · rfl

/-- The end point of `l₁ ++ l₂` is the end point of `l₂` started from the end point of `l₁`. -/
theorem InsertPoint.afterLast_append (l₁ l₂ : List OperationPtr) (ctx : IRContext OpInfo)
    (fb : InsertPoint) :
    InsertPoint.afterLast (l₁ ++ l₂) ctx fb
      = InsertPoint.afterLast l₂ ctx (InsertPoint.afterLast l₁ ctx fb) := by
  induction l₁ generalizing fb with
  | nil => simp
  | cons a xs ih =>
    simp only [List.cons_append, InsertPoint.afterLast_cons]
    exact ih _

/--
Sequential composition of *scoped* cross-context refinement over `interpretOpList`. If interpreting
the prefix `l₁`/`m₁` refines at the points `(afterLast l₁ p, afterLast m₁ p')` (`hPrefix`), and —
whenever the prefixes both run to completion without a terminator into scoped-refined states —
interpreting the suffixes `l₂`/`m₂` refines at the final points (`hCont`), then interpreting
`l₁ ++ l₂` refines `m₁ ++ m₂` at the final points.

The prefix may terminate (produce a control-flow action) only when the source suffix `l₂` is empty
(`hPreNoTerm`), in which case the target suffix `m₂` is also empty (`hM2Nil`); this keeps the result
scope point pinned to the prefix end, which is then the final point.
-/
theorem isRefinedBy_interpretOpList_seqCompose
    {ctx ctx' : WfIRContext OpCode} {μ : ValueMapping ctx ctx'}
    {l₁ l₂ m₁ m₂ : List OperationPtr}
    {s : InterpreterState ctx} {s' : InterpreterState ctx'}
    {p p' : InsertPoint}
    (qIn : (InsertPoint.afterLast l₁ ctx.raw p).InBounds ctx.raw)
    (q'In : (InsertPoint.afterLast m₁ ctx'.raw p').InBounds ctx'.raw)
    (rIn : (InsertPoint.afterLast (l₁ ++ l₂) ctx.raw p).InBounds ctx.raw)
    (r'In : (InsertPoint.afterLast (m₁ ++ m₂) ctx'.raw p').InBounds ctx'.raw)
    (hl : ∀ o ∈ l₁ ++ l₂, o.InBounds ctx.raw)
    (hm : ∀ o ∈ m₁ ++ m₂, o.InBounds ctx'.raw)
    (hM2Nil : l₂ = [] → m₂ = [])
    (hPreNoTerm : l₂ ≠ [] → ∀ s2 cf,
      interpretOpList l₁ s (fun o ho => hl o (List.mem_append_left _ ho)) ≠ some (.ok (s2, some cf)))
    (hPrefix : Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedByAt r₂.1 μ
          (InsertPoint.afterLast l₁ ctx.raw p) (InsertPoint.afterLast m₁ ctx'.raw p') qIn q'In ∧
        ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOpList l₁ s (fun o ho => hl o (List.mem_append_left _ ho)))
      (interpretOpList m₁ s' (fun o ho => hm o (List.mem_append_left _ ho))))
    (hCont : ∀ (s2 : InterpreterState ctx) (s2' : InterpreterState ctx'),
        s2.isRefinedByAt s2' μ
          (InsertPoint.afterLast l₁ ctx.raw p) (InsertPoint.afterLast m₁ ctx'.raw p') qIn q'In →
        interpretOpList l₁ s (fun o ho => hl o (List.mem_append_left _ ho)) = some (.ok (s2, none)) →
        interpretOpList m₁ s' (fun o ho => hm o (List.mem_append_left _ ho)) = some (.ok (s2', none)) →
        Interp.isRefinedBy
          (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
               (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
            r₁.1.isRefinedByAt r₂.1 μ
              (InsertPoint.afterLast (l₁ ++ l₂) ctx.raw p)
              (InsertPoint.afterLast (m₁ ++ m₂) ctx'.raw p') rIn r'In ∧
            ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
          (interpretOpList l₂ s2 (fun o ho => hl o (List.mem_append_right _ ho)))
          (interpretOpList m₂ s2' (fun o ho => hm o (List.mem_append_right _ ho)))) :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedByAt r₂.1 μ
          (InsertPoint.afterLast (l₁ ++ l₂) ctx.raw p)
          (InsertPoint.afterLast (m₁ ++ m₂) ctx'.raw p') rIn r'In ∧
        ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOpList (l₁ ++ l₂) s hl)
      (interpretOpList (m₁ ++ m₂) s' hm) := by
  rw [interpretOpList_append, interpretOpList_append]
  rcases hsrc : interpretOpList l₁ s (fun o ho => hl o (List.mem_append_left _ ho)) with
    _ | (⟨s2, a⟩ | _)
  · simp [Interp.isRefinedBy]
  · rw [hsrc] at hPrefix
    simp only [Interp.isRefinedBy_ok_target_iff] at hPrefix
    obtain ⟨⟨s2', a'⟩, htgt, hsRef, haRef⟩ := hPrefix
    rw [htgt]
    cases a with
    | none =>
      have ha' : a' = none := by cases a' <;> simp_all [ControlFlowAction.optionIsRefinedBy]
      subst ha'
      exact hCont s2 s2' hsRef hsrc htgt
    | some cf =>
      -- The prefix terminated: only possible when `l₂ = []` (else `hPreNoTerm`), and then `m₂ = []`.
      by_cases hl2 : l₂ = []
      · obtain rfl := hl2
        obtain rfl := hM2Nil rfl
        obtain ⟨cf', ha', hcf⟩ : ∃ cf', a' = some cf' ∧ cf.isRefinedBy cf' := by
          cases a' <;> simp_all [ControlFlowAction.optionIsRefinedBy]
        subst ha'
        simp only [Interp.isRefinedBy_ok_target_iff]
        refine ⟨_, rfl, ?_, by simpa [ControlFlowAction.optionIsRefinedBy] using hcf⟩
        -- The result point `afterLast (l₁ ++ []) = afterLast l₁`, where `hsRef` already lands.
        simpa using hsRef
      · exact absurd hsrc (hPreNoTerm hl2 s2 cf)
  · simp

/-- For a block whose op-chain starts with a slice `l ++ [x]`, running `l` from the block entry
`atStart!` ends at the point just before `x`. Used to bridge the scoped `interpretOpList_monoAt`
end point (`afterLast l (atStart! block)`) to the next operation's entry point in the block. -/
theorem afterLast_atStart!_eq_before_of_chain {ctx : WfIRContext OpCode} {block : BlockPtr}
    {l : List OperationPtr} {x : OperationPtr}
    (hChain : block.OpChainSlice ctx.raw (l ++ [x]))
    (hHead : (block.get! ctx.raw).firstOp = (l ++ [x]).head?) :
    InsertPoint.afterLast l ctx.raw (InsertPoint.atStart! block ctx.raw) = InsertPoint.before x := by
  cases l with
  | nil =>
    simp only [List.nil_append, List.head?_cons] at hHead
    simp only [InsertPoint.afterLast_nil, InsertPoint.atStart!, hHead]
  | cons a t =>
    obtain ⟨lastOp, hlast⟩ : ∃ lastOp, (a :: t).getLast? = some lastOp := by
      cases hg : (a :: t).getLast? with
      | none => simp at hg
      | some y => exact ⟨y, rfl⟩
    have hmem : lastOp ∈ (a :: t) ++ [x] :=
      List.mem_append_left _ (List.mem_of_getLast? hlast)
    have hnext : (lastOp.get! ctx.raw).next = some x := hChain.getLast?_next_eq hlast
    have lastIn : lastOp.InBounds ctx.raw := hChain.inBounds_of_mem lastOp hmem
    have lastParent : (lastOp.get! ctx.raw).parent = some block := hChain.parent_of_mem lastOp hmem
    simp only [InsertPoint.afterLast, hlast]
    rw [InsertPoint.after!_eq_after lastParent lastIn, InsertPoint.after_eq_of_some_next hnext]

/-- Running a block's *entire* operation list from its entry lands at the block end: the end point of
the full chain is `atEnd block`. (For an empty block, `firstOp = none`, so `atStart! = atEnd` already.) -/
theorem afterLast_operationList_atStart!_eq_atEnd {ctx : WfIRContext OpCode} {b : BlockPtr}
    (bIn : b.InBounds ctx.raw) :
    InsertPoint.afterLast (b.operationList ctx.raw ctx.wellFormed bIn).toList ctx.raw
      (InsertPoint.atStart! b ctx.raw) = InsertPoint.atEnd b := by
  have hchain := BlockPtr.operationListWF ctx.raw b bIn ctx.wellFormed
  cases hg : (b.operationList ctx.raw ctx.wellFormed bIn).toList.getLast? with
  | none =>
    have hnil : (b.operationList ctx.raw ctx.wellFormed bIn).toList = [] :=
      List.getLast?_eq_none_iff.mp hg
    have hsize : (b.operationList ctx.raw ctx.wellFormed bIn).size = 0 := by
      rw [← Array.length_toList, hnil]; rfl
    have hfirst : (b.get! ctx.raw).firstOp = none := by
      rw [hchain.first, Array.getElem?_eq_none (by omega)]
    rw [hnil]
    simp only [InsertPoint.afterLast_nil, InsertPoint.atStart!, hfirst]
  | some last =>
    have hmem : last ∈ (b.operationList ctx.raw ctx.wellFormed bIn).toList := List.mem_of_getLast? hg
    have hmem' : last ∈ b.operationList ctx.raw ctx.wellFormed bIn := by simpa using hmem
    have lastParent : (last.get! ctx.raw).parent = some b := hchain.opParent hmem'
    have lastIn : last.InBounds ctx.raw := hchain.arrayInBounds hmem'
    have hlastOp : (b.get! ctx.raw).lastOp = some last := by
      rw [hchain.last, ← Array.getElem?_toList, ← Array.length_toList,
        ← List.getLast?_eq_getElem?]
      exact hg
    have hnext : (last.get! ctx.raw).next = none :=
      (BlockPtr.OpChain.next!_eq_none_iff_lastOp!_eq_self lastIn hchain lastParent).mpr hlastOp
    simp only [InsertPoint.afterLast, hg]
    rw [InsertPoint.after!_eq_after lastParent lastIn]
    grind [InsertPoint.after]

/-- If running `a ++ b` never produces a control-flow action, then running the prefix `a` never does
either: an action from `a` would short-circuit `interpretOpList (a ++ b)` to that same action.
Bridges the whole-list `hFrontNoCf` (from `hSrcSplit`) to the prefix non-termination obligations of
`isRefinedBy_interpretOpList_seqCompose`. -/
theorem interpretOpList_append_noCf_left {ctx : WfIRContext OpCode} {a b : List OperationPtr}
    {state : InterpreterState ctx} (hab : ∀ o ∈ a ++ b, o.InBounds ctx.raw)
    (h : ∀ (s2 : InterpreterState ctx) (cf : ControlFlowAction),
      interpretOpList (a ++ b) state hab ≠ some (.ok (s2, some cf))) :
    ∀ (s2 : InterpreterState ctx) (cf : ControlFlowAction),
      interpretOpList a state (fun o ho => hab o (List.mem_append_left _ ho))
        ≠ some (.ok (s2, some cf)) := by
  intro s2 cf hc
  refine h s2 cf ?_
  rw [interpretOpList_append]
  simp only [hc]

/-- If running `a ++ b` never produces a control-flow action, and `a` runs to completion without one,
then running the suffix `b` from the resulting state never produces one either. The run-local suffix
analogue of `interpretOpList_append_noCf_left`. -/
theorem interpretOpList_append_noCf_right {ctx : WfIRContext OpCode} {a b : List OperationPtr}
    {state s2 : InterpreterState ctx} (hab : ∀ o ∈ a ++ b, o.InBounds ctx.raw)
    (h : ∀ (s3 : InterpreterState ctx) (cf : ControlFlowAction),
      interpretOpList (a ++ b) state hab ≠ some (.ok (s3, some cf)))
    (hrun : interpretOpList a state (fun o ho => hab o (List.mem_append_left _ ho))
      = some (.ok (s2, none))) :
    ∀ (s3 : InterpreterState ctx) (cf : ControlFlowAction),
      interpretOpList b s2 (fun o ho => hab o (List.mem_append_right _ ho))
        ≠ some (.ok (s3, some cf)) := by
  intro s3 cf hc
  refine h s3 cf ?_
  rw [interpretOpList_append, hrun]
  simp only [hc]

/-- If running the whole list never produces a control-flow action, neither does running its init
segment `dropLast`. Feeds the run-local `hInitNoCf` of `interpretOpList_monoAt` from a whole-list
non-branching fact (used for the `pre` segment). -/
theorem interpretOpList_dropLast_noCf {ctx : WfIRContext OpCode} :
    ∀ (ops : List OperationPtr) (state : InterpreterState ctx) (hIn : ∀ o ∈ ops, o.InBounds ctx.raw),
    (∀ (s2 : InterpreterState ctx) (cf : ControlFlowAction),
      interpretOpList ops state hIn ≠ some (.ok (s2, some cf))) →
    ∀ (s2 : InterpreterState ctx) (cf : ControlFlowAction),
      interpretOpList ops.dropLast state (fun o ho => hIn o (List.dropLast_subset ops ho))
        ≠ some (.ok (s2, some cf)) := by
  intro ops
  induction ops with
  | nil => intro state hIn _ s2 cf hc; simp only [List.dropLast_nil, interpretOpList_nil] at hc; grind
  | cons a l ih =>
    rcases l with _ | ⟨b, rest⟩
    · intro state hIn _ s2 cf hc
      simp only [List.dropLast, interpretOpList_nil] at hc; grind
    · intro state hIn hwhole s2 cf hc
      simp only [List.dropLast_cons_cons, interpretOpList_cons] at hc
      rcases hi : interpretOp a state (hIn a (by simp)) with _ | (⟨s, act⟩ | _)
      · simp only [hi] at hc; grind
      · simp only [hi] at hc
        cases act with
        | none =>
          refine ih s (fun o ho => hIn o (List.mem_cons_of_mem a ho)) ?_ s2 cf hc
          intro s3 cf3 hc3
          refine hwhole s3 cf3 ?_
          rw [interpretOpList_cons]; simp only [hi]; exact hc3
        | some cf' =>
          exact hwhole s cf' (by rw [interpretOpList_cons]; simp only [hi])
      · simp only [hi] at hc; grind

/--
**Block-`B` simulation (scoped).** Interpreting the source block list `pre ++ [op] ++ post` is
refined by interpreting the target block list `pre ++ newOps ++ post`, with the scoped state
refinement `isRefinedByAt` carried from the block entry `(atStart! block)` to the end of the block.

The proof composes the three regimes via the scoped `isRefinedBy_interpretOpList_seqCompose`:
* **`pre` (identical list)** — scoped cross-context monotonicity `interpretOpList_monoAt`, advancing
  the scope point from `atStart! block` to `before op` (source) / the corresponding target point.
* **`[op]` vs `newOps`** — the scoped local op-step simulation `hOpSim`, after threading the SSA
  invariant `EquationLemmaAt` from block entry through `pre` to `op`.
* **`post` (same pointers, redirected operands)** — scoped cross-context monotonicity, fed the
  target `DefinesDominating` derived from `hTgtDefDom` and the completed target prefix run.

Non-branching is supplied as the single whole-list `hSrcSplit` (the source list splits as
`front ++ [term]` with `front` never branching from any state), mirroring the driver's `hSrcSplit`
clause so `interpretBlock_refinement` can forward it verbatim. From it the proof derives:
* the `hPreNoTerm` hypotheses of the scoped `seqCompose` — `pre` (and `pre ++ [op]` when
  `post ≠ []`) is a prefix of `front`, so `interpretOpList_append_noCf_left` makes it non-branching;
* the per-segment non-branching fed to `interpretOpList_monoAt`, threaded along the actual run
  (`pre`/`post.dropLast` are run-local prefixes of `front`).
-/
theorem RewrittenAt.blockSimulation
    (hRW : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    (newCtxVerif : newCtx.Verified)
    (hCtxDom : ctx.Dom)
    {state : InterpreterState ctx} {state' : InterpreterState newCtx}
    (hState : state.isRefinedByAt state' hRW.σ
      (InsertPoint.atStart! block ctx.raw) (InsertPoint.atStart! block newCtx.raw))
    (hTgtDefDom : state'.DefinesDominating (InsertPoint.atStart! block newCtx.raw)
      ((InsertPoint.inBounds_atStart! newCtx.wellFormed blockIn').mpr blockIn'))
    (hEqLem : ∀ fst (hfst : (block.get! ctx.raw).firstOp = some fst),
      state.EquationLemmaAt (.before fst))
    (hTgtEqLem : state'.EquationLemmaAt (InsertPoint.atStart! block newCtx.raw)
      ((InsertPoint.inBounds_atStart! newCtx.wellFormed blockIn').mpr blockIn'))
    (hSrcSplit : ∃ (front : List OperationPtr) (term : OperationPtr)
        (frontIn : ∀ o ∈ front, o.InBounds ctx.raw),
        (pre.toList ++ [op] ++ post.toList) = front ++ [term] ∧
        (∀ (s s' : InterpreterState ctx) (cf : ControlFlowAction),
            interpretOpList front s frontIn ≠ some (.ok (s', some cf))))
    (hOpSim : OpStepSimulation op newOps hRW.σ opIn hRW.newOpsInBounds') :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × ControlFlowAction)
           (r₂ : InterpreterState newCtx × ControlFlowAction) =>
        r₁.1.isRefinedByAt r₂.1 hRW.σ
          (InsertPoint.afterLast (pre.toList ++ [op] ++ post.toList) ctx.raw
            (InsertPoint.atStart! block ctx.raw))
          (InsertPoint.afterLast (pre.toList ++ newOps.toList ++ post.toList) newCtx.raw
            (InsertPoint.atStart! block newCtx.raw))
          (InsertPoint.afterLast_inBounds ctx.wellFormed
            ((InsertPoint.inBounds_atStart! ctx.wellFormed blockIn).mpr blockIn)
            (fun o ho => ⟨block, hRW.srcChain.parent_of_mem o ho⟩)
            (sourceListIn opIn hRW.preInBounds hRW.postInBounds))
          (InsertPoint.afterLast_inBounds newCtx.wellFormed
            ((InsertPoint.inBounds_atStart! newCtx.wellFormed blockIn').mpr blockIn')
            (fun o ho => ⟨block, hRW.tgtChain.parent_of_mem o ho⟩)
            (targetListIn hRW.preInBounds' hRW.newOpsInBounds' hRW.postInBounds')) ∧
        r₁.2.isRefinedBy r₂.2)
      (interpretTerminatedOpList (pre.toList ++ [op] ++ post.toList) state
        (sourceListIn opIn hRW.preInBounds hRW.postInBounds))
      (interpretTerminatedOpList (pre.toList ++ newOps.toList ++ post.toList) state'
        (targetListIn hRW.preInBounds' hRW.newOpsInBounds' hRW.postInBounds')) := by
  have ctxDom' : newCtx.Dom := hRW.newCtxDom
  -- Proof-irrelevant congruence for `interpretOpList`'s in-bounds witness, used to move
  -- non-branching facts between syntactically-different-but-equal op lists.
  have iopl_congr : ∀ {cc : WfIRContext OpCode} {l l' : List OperationPtr} (s : InterpreterState cc)
      (hl : ∀ o ∈ l, o.InBounds cc.raw) (hl' : ∀ o ∈ l', o.InBounds cc.raw),
      l = l' → interpretOpList l s hl = interpretOpList l' s hl' := by
    intro cc l l' s hl hl' h; subst h; rfl
  -- The source list and its non-branching `front` prefix (from `hSrcSplit`).
  obtain ⟨front, term, frontIn, hSplit, hFrontNoCf⟩ := hSrcSplit
  have hfrontEq : front = (pre.toList ++ [op] ++ post.toList).dropLast := by
    rw [hSplit, List.dropLast_concat]
  subst hfrontEq
  -- `pre` never branches from any state (it is a prefix of `front`).
  have hpreNB : ∀ (s s2 : InterpreterState ctx) (cf : ControlFlowAction),
      interpretOpList pre.toList s hRW.preInBounds ≠ some (.ok (s2, some cf)) := by
    intro s s2 cf hc
    refine hFrontNoCf s s2 cf ?_
    rw [iopl_congr s frontIn (l' := pre.toList ++ ([op] ++ post.toList).dropLast)
      (by intro o ho; exact frontIn o (by
        rw [List.append_assoc, List.dropLast_append_of_ne_nil (by simp)]; exact ho))
      (by rw [List.append_assoc, List.dropLast_append_of_ne_nil (by simp)]),
      interpretOpList_append]
    simp only [hc]
  -- `pre ++ [op]` never branches from any state (used when `post ≠ []`).
  have hpreOpNB : post.toList ≠ [] → ∀ (s s2 : InterpreterState ctx) (cf : ControlFlowAction),
      interpretOpList (pre.toList ++ [op]) s
        (fun o ho => hRW.srcChain.inBounds_of_mem o (by
          simp only [List.mem_append] at ho ⊢; exact Or.inl ho)) ≠ some (.ok (s2, some cf)) := by
    intro hpost s s2 cf hc
    refine hFrontNoCf s s2 cf ?_
    rw [iopl_congr s frontIn (l' := (pre.toList ++ [op]) ++ post.toList.dropLast)
      (by intro o ho; exact frontIn o (by
        rw [List.dropLast_append_of_ne_nil hpost]; exact ho))
      (by rw [List.dropLast_append_of_ne_nil hpost]),
      interpretOpList_append]
    simp only [hc]
  -- Point bridges: running `pre` from the block start lands just before `op`.
  have hPreEndSrc : InsertPoint.afterLast pre.toList ctx.raw (InsertPoint.atStart! block ctx.raw)
      = InsertPoint.before op :=
    afterLast_atStart!_eq_before_of_chain hRW.preChainOp
      (by rw [hRW.srcFirstOp, List.head?_append]; simp)
  -- The `interpretOpList` refinement, assembled below by nested scoped `seqCompose`.
  have hOpList : Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState newCtx × Option ControlFlowAction) =>
        r₁.1.isRefinedByAt r₂.1 hRW.σ
          (InsertPoint.afterLast (pre.toList ++ [op] ++ post.toList) ctx.raw
            (InsertPoint.atStart! block ctx.raw))
          (InsertPoint.afterLast (pre.toList ++ newOps.toList ++ post.toList) newCtx.raw
            (InsertPoint.atStart! block newCtx.raw))
          (InsertPoint.afterLast_inBounds ctx.wellFormed
            ((InsertPoint.inBounds_atStart! ctx.wellFormed blockIn).mpr blockIn)
            (fun o ho => ⟨block, hRW.srcChain.parent_of_mem o ho⟩)
            (sourceListIn opIn hRW.preInBounds hRW.postInBounds))
          (InsertPoint.afterLast_inBounds newCtx.wellFormed
            ((InsertPoint.inBounds_atStart! newCtx.wellFormed blockIn').mpr blockIn')
            (fun o ho => ⟨block, hRW.tgtChain.parent_of_mem o ho⟩)
            (targetListIn hRW.preInBounds' hRW.newOpsInBounds' hRW.postInBounds')) ∧
        ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOpList (pre.toList ++ [op] ++ post.toList) state
        (sourceListIn opIn hRW.preInBounds hRW.postInBounds))
      (interpretOpList (pre.toList ++ newOps.toList ++ post.toList) state'
        (targetListIn hRW.preInBounds' hRW.newOpsInBounds' hRW.postInBounds')) := by
    refine isRefinedBy_interpretOpList_seqCompose (l₂ := post.toList) (m₂ := post.toList)
      (p := InsertPoint.atStart! block ctx.raw) (p' := InsertPoint.atStart! block newCtx.raw)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    -- qIn
    · exact InsertPoint.afterLast_inBounds ctx.wellFormed
        ((InsertPoint.inBounds_atStart! ctx.wellFormed blockIn).mpr blockIn)
        (fun o ho => ⟨block, hRW.preChainOp.parent_of_mem o ho⟩)
        (fun o ho => hRW.preChainOp.inBounds_of_mem o ho)
    -- q'In
    · exact InsertPoint.afterLast_inBounds newCtx.wellFormed
        ((InsertPoint.inBounds_atStart! newCtx.wellFormed blockIn').mpr blockIn')
        (fun o ho => ⟨block, hRW.tgtChain.append_left.parent_of_mem o ho⟩)
        (fun o ho => hRW.tgtChain.append_left.inBounds_of_mem o ho)
    -- hM2Nil
    · exact id
    -- hPreNoTerm (only when `post ≠ []`)
    · exact fun h => hpreOpNB h state
    -- hPrefix: `pre` then `[op]` vs `newOps` (inner seqCompose)
    · refine isRefinedBy_interpretOpList_seqCompose (l₂ := [op]) (m₂ := newOps.toList)
        (p := InsertPoint.atStart! block ctx.raw) (p' := InsertPoint.atStart! block newCtx.raw)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      -- qIn'
      · exact InsertPoint.afterLast_inBounds ctx.wellFormed
          ((InsertPoint.inBounds_atStart! ctx.wellFormed blockIn).mpr blockIn)
          (fun o ho => ⟨block, hRW.preChainOp.append_left.parent_of_mem o ho⟩)
          (fun o ho => hRW.preInBounds o ho)
      -- q'In'
      · exact InsertPoint.afterLast_inBounds newCtx.wellFormed
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed blockIn').mpr blockIn')
          (fun o ho => ⟨block, hRW.preChain'.parent_of_mem o ho⟩)
          (fun o ho => hRW.preInBounds' o ho)
      -- hM2Nil'
      · intro h; simp at h
      -- hPreNoTerm'
      · exact fun _ => hpreNB state
      -- hPrefix': `pre` via cross-context monotonicity
      · refine interpretOpList_monoAt newCtxVerif hCtxDom ctxDom'
          (fun o ho => hRW.preInBounds o ho) (fun o ho => hRW.preInBounds' o ho)
          hRW.preChainOp.append_left hRW.preChain'
          ((InsertPoint.inBounds_atStart! ctx.wellFormed blockIn).mpr blockIn)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed blockIn').mpr blockIn')
          hState hTgtDefDom
          (fun o ho => hRW.frame o (hRW.preInBounds o ho) (hRW.preInBounds' o ho)
            (fun heq => hRW.opNotMemPre (heq ▸ ho))) ?_ ?_
        · -- hPointsHead
          intro h
          have hsf : (block.get! ctx.raw).firstOp = some (pre.toList.head h) := by
            rw [hRW.srcFirstOp]; simp [List.head?_append, List.head?_eq_some_head h]
          have htf : (block.get! newCtx.raw).firstOp = some (pre.toList.head h) := by
            rw [hRW.tgtFirstOp]; simp [List.head?_append, List.head?_eq_some_head h]
          exact ⟨by simp only [InsertPoint.atStart!, hsf], by simp only [InsertPoint.atStart!, htf]⟩
        · -- hInitNoCf
          exact interpretOpList_dropLast_noCf pre.toList state
            (fun o ho => hRW.preInBounds o ho) (hpreNB state)
      -- hCont': `[op]` vs `newOps` via `hOpSim`
      · intro s2 s2' hsRef hrunS hrunT
        have p'In : (InsertPoint.afterLast pre.toList newCtx.raw
            (InsertPoint.atStart! block newCtx.raw)).InBounds newCtx.raw :=
          InsertPoint.afterLast_inBounds newCtx.wellFormed
            ((InsertPoint.inBounds_atStart! newCtx.wellFormed blockIn').mpr blockIn')
            (fun o ho => ⟨block, hRW.preChain'.parent_of_mem o ho⟩)
            (fun o ho => hRW.preInBounds' o ho)
        have hEq : s2.EquationLemmaAt (InsertPoint.before op) opIn :=
          interpretOpList_equationLemmaAt_before hCtxDom hRW.preInBounds opIn hRW.preChainOp
            (fun fst _ hhd => hEqLem fst (by rw [hRW.srcFirstOp, List.head?_append, hhd]; rfl)) hrunS
        -- Target `EquationLemmaAt` at the `newOps` insertion point, threading `hTgtEqLem` through `pre`.
        have hTgtEq : s2'.EquationLemmaAt
            (InsertPoint.afterLast pre.toList newCtx.raw (InsertPoint.atStart! block newCtx.raw)) p'In :=
          interpretOpList_equationLemmaAt_afterLast_atStart ctxDom' blockIn' hRW.preInBounds'
            hRW.preChain'
            (fun h hh => by rw [hRW.tgtFirstOp, List.head?_append, List.head?_append, hh]; rfl)
            hTgtEqLem p'In hrunT
        -- Transport the source scope point `afterLast pre (atStart!)` to `before op` (witness-free).
        have congrPt : ∀ {p₁ p₂ : InsertPoint} {w1 : p₁.InBounds ctx.raw} {w1' w2'}
            {w2 : p₂.InBounds ctx.raw}, p₁ = p₂ →
            s2.isRefinedByAt s2' hRW.σ p₁ (InsertPoint.afterLast pre.toList newCtx.raw
              (InsertPoint.atStart! block newCtx.raw)) w1 w1' →
            s2.isRefinedByAt s2' hRW.σ p₂ (InsertPoint.afterLast pre.toList newCtx.raw
              (InsertPoint.atStart! block newCtx.raw)) w2 w2' := by
          intro p₁ p₂ w1 w1' w2' w2 hp h; subst hp; exact h
        -- `afterLast pre (atStart! block)` is the target image of `before op` (the prefix `pre` and the
        -- block are unchanged by the rewrite), so a value dominating `before op` in the source dominates
        -- the `newOps` insertion point in the target. Sound cross-context dominance fact.
        have hCouple : ∀ (v : ValuePtr) (vIn : v.InBounds ctx.raw),
            v.dominatesIp (InsertPoint.before op) ctx →
            (hRW.σ ⟨v, vIn⟩).val.dominatesIp (InsertPoint.afterLast pre.toList newCtx.raw
              (InsertPoint.atStart! block newCtx.raw)) newCtx :=
          sorry
        have hres := hOpSim s2 s2'
          (InsertPoint.afterLast pre.toList newCtx.raw (InsertPoint.atStart! block newCtx.raw))
          p'In
          (InsertPoint.after!_inBounds ctx.wellFormed hRW.opParent opIn)
          (InsertPoint.afterLast_inBounds newCtx.wellFormed p'In hRW.newOpsParent'
            (fun o ho => hRW.newOpsInBounds' o ho))
          hCouple (congrPt hPreEndSrc hsRef) hEq hTgtEq
        rw [interpretOpList_singleton]
        have hP1 : InsertPoint.afterLast (pre.toList ++ [op]) ctx.raw
            (InsertPoint.atStart! block ctx.raw) = InsertPoint.after! op ctx.raw := by
          rw [InsertPoint.afterLast_append, InsertPoint.afterLast_singleton]
        have hP2 : InsertPoint.afterLast (pre.toList ++ newOps.toList) newCtx.raw
            (InsertPoint.atStart! block newCtx.raw)
            = InsertPoint.afterLast newOps.toList newCtx.raw
                (InsertPoint.afterLast pre.toList newCtx.raw
                  (InsertPoint.atStart! block newCtx.raw)) := by
          rw [InsertPoint.afterLast_append]
        simp only [hP1, hP2]
        exact hres
    -- hCont: `post` via cross-context monotonicity
    · intro s2 s2' hsRef2 hrunS2 hrunT2
      have pInMono : (InsertPoint.afterLast (pre.toList ++ [op]) ctx.raw
          (InsertPoint.atStart! block ctx.raw)).InBounds ctx.raw :=
        InsertPoint.afterLast_inBounds ctx.wellFormed
          ((InsertPoint.inBounds_atStart! ctx.wellFormed blockIn).mpr blockIn)
          (fun o ho => ⟨block, hRW.preChainOp.parent_of_mem o ho⟩)
          (fun o ho => hRW.preChainOp.inBounds_of_mem o ho)
      have p'InMono : (InsertPoint.afterLast (pre.toList ++ newOps.toList) newCtx.raw
          (InsertPoint.atStart! block newCtx.raw)).InBounds newCtx.raw :=
        InsertPoint.afterLast_inBounds newCtx.wellFormed
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed blockIn').mpr blockIn')
          (fun o ho => ⟨block, hRW.tgtChain.append_left.parent_of_mem o ho⟩)
          (fun o ho => hRW.tgtChain.append_left.inBounds_of_mem o ho)
      -- Witness-free transport of a `DefinesDominating` scope point along an equality.
      have ddT : ∀ {st : InterpreterState newCtx} {p₁ p₂ : InsertPoint}
          {w1 : p₁.InBounds newCtx.raw} {w2 : p₂.InBounds newCtx.raw},
          p₁ = p₂ → st.DefinesDominating p₁ w1 → st.DefinesDominating p₂ w2 := by
        intro st p₁ p₂ w1 w2 hp h; subst hp; exact h
      -- Target `DefinesDominating` at the post entry, advancing `hTgtDefDom` through `pre ++ newOps`.
      have tgtDefDomPost : s2'.DefinesDominating
          (InsertPoint.afterLast (pre.toList ++ newOps.toList) newCtx.raw
            (InsertPoint.atStart! block newCtx.raw)) p'InMono := by
        by_cases hpn : pre.toList ++ newOps.toList = []
        · have hs2' : state' = s2' := by
            have hr := hrunT2
            rw [iopl_congr state' _ (by simp) hpn, interpretOpList_nil] at hr
            exact (Prod.mk.inj (UBOr.ok.inj (Option.some.inj hr))).1
          exact ddT (by rw [hpn]; rfl) (hs2' ▸ hTgtDefDom)
        · obtain ⟨fstOp, hfst⟩ : ∃ fstOp, (pre.toList ++ newOps.toList).head? = some fstOp := by
            cases hc : pre.toList ++ newOps.toList with
            | nil => exact absurd hc hpn
            | cons a t => exact ⟨a, rfl⟩
          obtain ⟨lastOp, hlast⟩ : ∃ lastOp, (pre.toList ++ newOps.toList).getLast? = some lastOp := by
            cases hc : (pre.toList ++ newOps.toList).getLast? with
            | none => rw [List.getLast?_eq_none_iff] at hc; exact absurd hc hpn
            | some x => exact ⟨x, rfl⟩
          have hStartTgt : InsertPoint.atStart! block newCtx.raw = InsertPoint.before fstOp := by
            have hf : (block.get! newCtx.raw).firstOp = some fstOp := by
              rw [hRW.tgtFirstOp, List.head?_append, hfst]; rfl
            simp only [InsertPoint.atStart!, hf]
          have hdd := interpretOpList_DefinesDominating ctxDom' hRW.tgtChain.append_left hfst
            (ddT hStartTgt hTgtDefDom) hlast hrunT2
          have lastIn := hRW.tgtChain.append_left.inBounds_of_mem lastOp (List.mem_of_getLast? hlast)
          have lastParent := hRW.tgtChain.append_left.parent_of_mem lastOp (List.mem_of_getLast? hlast)
          refine ddT ?_ hdd
          rw [InsertPoint.afterLast, hlast]
          exact (InsertPoint.after!_eq_after lastParent lastIn).symm
      -- Both points coincide at `before (post.head)` when `post ≠ []`.
      have hPointsHeadPost : ∀ (h : post.toList ≠ []),
          InsertPoint.afterLast (pre.toList ++ [op]) ctx.raw (InsertPoint.atStart! block ctx.raw)
            = InsertPoint.before (post.toList.head h) ∧
          InsertPoint.afterLast (pre.toList ++ newOps.toList) newCtx.raw
            (InsertPoint.atStart! block newCtx.raw) = InsertPoint.before (post.toList.head h) := by
        intro h
        obtain ⟨hd, tl, htl⟩ : ∃ hd tl, post.toList = hd :: tl := by
          cases hc : post.toList with
          | nil => exact absurd hc h
          | cons a t => exact ⟨a, t, rfl⟩
        have hhd : post.toList.head h = hd := by simp [htl]
        rw [hhd]
        have hreassoc : ∀ (l : List OperationPtr),
            (l ++ [hd]) ++ tl = l ++ [op] ++ (hd :: tl) → True := fun _ _ => trivial
        refine ⟨afterLast_atStart!_eq_before_of_chain ?_ ?_, afterLast_atStart!_eq_before_of_chain ?_ ?_⟩
        · have hc := hRW.srcChain
          rw [htl] at hc
          have hc2 : block.OpChainSlice ctx.raw (((pre.toList ++ [op]) ++ [hd]) ++ tl) := by
            rw [show ((pre.toList ++ [op]) ++ [hd]) ++ tl = pre.toList ++ [op] ++ (hd :: tl) from by
              simp]
            exact hc
          exact hc2.append_left
        · rw [hRW.srcFirstOp, htl]; simp [List.head?_append, List.append_assoc]
        · have hc := hRW.tgtChain
          rw [htl] at hc
          have hc2 : block.OpChainSlice newCtx.raw (((pre.toList ++ newOps.toList) ++ [hd]) ++ tl) := by
            rw [show ((pre.toList ++ newOps.toList) ++ [hd]) ++ tl
                = pre.toList ++ newOps.toList ++ (hd :: tl) from by simp]
            exact hc
          exact hc2.append_left
        · rw [hRW.tgtFirstOp, htl]; simp [List.head?_append, List.append_assoc]
      -- `post.dropLast` never branches from `s2` (suffix of the non-branching `front`).
      have hInitNoCfPost : ∀ (s3 : InterpreterState ctx) (cf : ControlFlowAction),
          interpretOpList post.toList.dropLast s2
            (fun o ho => hRW.postInBounds o (List.dropLast_subset post.toList ho))
            ≠ some (.ok (s3, some cf)) := by
        by_cases hpe : post.toList = []
        · intro s3 cf hc
          rw [iopl_congr s2 _ (by simp) (show post.toList.dropLast = [] by simp [hpe]),
            interpretOpList_nil] at hc
          exact absurd (Prod.mk.inj (UBOr.ok.inj (Option.some.inj hc))).2 (by simp)
        · have hfpost : (pre.toList ++ [op] ++ post.toList).dropLast
              = (pre.toList ++ [op]) ++ post.toList.dropLast := List.dropLast_append_of_ne_nil hpe
          have hab : ∀ o ∈ (pre.toList ++ [op]) ++ post.toList.dropLast, o.InBounds ctx.raw :=
            fun o ho => frontIn o (by rw [hfpost]; exact ho)
          have h : ∀ (s3 : InterpreterState ctx) (cf : ControlFlowAction),
              interpretOpList ((pre.toList ++ [op]) ++ post.toList.dropLast) state hab
                ≠ some (.ok (s3, some cf)) := by
            intro s3 cf hc
            exact hFrontNoCf state s3 cf ((iopl_congr state hab frontIn hfpost.symm).symm.trans hc)
          exact interpretOpList_append_noCf_right hab h hrunS2
      have hresPost := interpretOpList_monoAt newCtxVerif hCtxDom ctxDom'
        (fun o ho => hRW.postInBounds o ho) (fun o ho => hRW.postInBounds' o ho)
        hRW.srcChain.append_right hRW.postChain'
        pInMono p'InMono hsRef2 tgtDefDomPost
        (fun o ho => hRW.frame o (hRW.postInBounds o ho) (hRW.postInBounds' o ho)
          (fun heq => hRW.opNotMemPost (heq ▸ ho)))
        hPointsHeadPost hInitNoCfPost
      have hSp : InsertPoint.afterLast (pre.toList ++ [op] ++ post.toList) ctx.raw
          (InsertPoint.atStart! block ctx.raw)
          = InsertPoint.afterLast post.toList ctx.raw
              (InsertPoint.afterLast (pre.toList ++ [op]) ctx.raw
                (InsertPoint.atStart! block ctx.raw)) :=
        InsertPoint.afterLast_append (pre.toList ++ [op]) post.toList ctx.raw _
      have hTp : InsertPoint.afterLast (pre.toList ++ newOps.toList ++ post.toList) newCtx.raw
          (InsertPoint.atStart! block newCtx.raw)
          = InsertPoint.afterLast post.toList newCtx.raw
              (InsertPoint.afterLast (pre.toList ++ newOps.toList) newCtx.raw
                (InsertPoint.atStart! block newCtx.raw)) :=
        InsertPoint.afterLast_append (pre.toList ++ newOps.toList) post.toList newCtx.raw _
      simp only [hSp, hTp]
      exact hresPost
  -- Convert the op-list refinement to the terminated-list refinement (source UB refines anything).
  simp only [interpretTerminatedOpList, bind]
  rcases hsrc : interpretOpList (pre.toList ++ [op] ++ post.toList) state
      (sourceListIn opIn hRW.preInBounds hRW.postInBounds) with _ | (⟨s, act⟩ | _)
  · simp [Interp.isRefinedBy]
  · simp only [hsrc, Interp.isRefinedBy_ok_target_iff] at hOpList
    obtain ⟨⟨s', act'⟩, htgt, hsRef, hactRef⟩ := hOpList
    simp only [htgt]
    cases act with
    | none => simp [Interp.isRefinedBy]
    | some cf =>
      have ⟨cf', hact', hcfRef⟩ : ∃ cf', act' = some cf' ∧ cf.isRefinedBy cf' := by
        cases act' with
        | none => exact absurd hactRef (by simp [ControlFlowAction.optionIsRefinedBy])
        | some cf' => exact ⟨cf', rfl, hactRef⟩
      subst hact'
      exact ⟨hsRef, hcfRef⟩
  · exact Interp.isRefinedBy_ub_target

/-- Bridge `interpretBlock` to a `setArgumentValues?` followed by `interpretTerminatedOpList` over the
block's operation list. When the block is empty (`firstOp = none`) the operation list is empty and both
sides are `none`; otherwise `interpretOpChain` from the first operation is the terminated run of the
list. -/
theorem interpretBlock_eq_setArgumentValues?_interpretTerminatedOpList
    {ctx : WfIRContext OpCode} {b : BlockPtr} (bIn : b.InBounds ctx.raw)
    (values : Array RuntimeValue) (state : InterpreterState ctx) :
    interpretBlock b values state bIn =
    (state.variables.setArgumentValues? b values bIn).bind (fun newVars =>
      interpretTerminatedOpList (b.operationList ctx.raw ctx.wellFormed bIn).toList
        ⟨newVars, state.memory⟩ (by grind [BlockPtr.operationListWF, BlockPtr.OpChain])) := by
  simp only [interpretBlock, liftM, monadLift, MonadLift.monadLift, bind]
  rcases hsa : state.variables.setArgumentValues? b values bIn with _ | newVars
  · simp
  · simp only [Option.bind_some]
    have hchain := BlockPtr.operationListWF ctx.raw b bIn ctx.wellFormed
    split
    · -- Empty block: the operation list has size 0.
      next h =>
        have hfirst := hchain.first
        rw [BlockPtr.get!_eq_get bIn, h] at hfirst
        have hsize : (b.operationList ctx.raw ctx.wellFormed bIn).size = 0 := by
          rcases Nat.eq_zero_or_pos (b.operationList ctx.raw ctx.wellFormed bIn).size with h0 | h0
          · exact h0
          · rw [Array.getElem?_eq_getElem h0] at hfirst; simp at hfirst
        have htl : (b.operationList ctx.raw ctx.wellFormed bIn).toList = [] := by
          rw [← List.length_eq_zero_iff]; simpa using hsize
        simp only [htl, interpretTerminatedOpList_nil]
    · next firstOp h =>
        rw [interpretOpChain_eq_interpretTerminatedOpList_of_firstOp bIn
          (by rw [BlockPtr.get!_eq_get bIn]; exact h)]

/-- The block entry point `atStart!` of a non-empty block is exactly the point before its first
operation (the head of its operation list). Bridges the `hPointsHead` obligation of
`interpretTerminatedOpList_monoAt` when the scope point is the block entry. -/
theorem atStart!_eq_before_head {ctx : WfIRContext OpCode} {b : BlockPtr}
    (bIn : b.InBounds ctx.raw)
    (hne : (b.operationList ctx.raw ctx.wellFormed bIn).toList ≠ []) :
    InsertPoint.atStart! b ctx.raw
      = InsertPoint.before ((b.operationList ctx.raw ctx.wellFormed bIn).toList.head hne) := by
  have hchain := BlockPtr.operationListWF ctx.raw b bIn ctx.wellFormed
  have hfirst : (b.get! ctx.raw).firstOp
      = some ((b.operationList ctx.raw ctx.wellFormed bIn).toList.head hne) := by
    rw [hchain.first, ← Array.getElem?_toList, ← List.head?_eq_getElem?, List.head?_eq_some_head hne]
  simp [InsertPoint.atStart!, hfirst]

/-! ## Stage C: `interpretBlock` refinement for every block

Lifts the block-`B` simulation (and cross-context monotonicity for the unchanged blocks) to the full
`interpretBlock` of *any* block `b`, dispatching `b = block` vs. `b ≠ block`. The source-entry SSA
invariant on the post-`setArgumentValues?` state (`hSrcInv`) and the local op-step simulation
(`hOpSim`) are supplied by the caller (the CFG induction, Stage D).
-/

/--
**Stage C — `interpretBlock` refinement (all blocks).** For any in-bounds block `b`, refined entry
states and arguments, plus the per-entry SSA/dominance invariants on the post-argument states, give a
refinement of `interpretBlock b` across the rewrite. Dispatches on whether `b` is the rewritten block.
-/
theorem RewrittenAt.interpretBlock_refinement
    (hRW : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    (newCtxVerif : newCtx.Verified)
    (hCtxDom : ctx.Dom)
    {b : BlockPtr} (bIn : b.InBounds ctx.raw)
    {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState newCtx}
    (hState : state.isRefinedByAt state' hRW.σ (.blockEntry b) (.blockEntry b)
      bIn (hRW.blocksInBounds b bIn))
    (hVals : values ⊒ values')
    (hSrcInv : ∀ newVars, state.variables.setArgumentValues? b values bIn = some newVars →
        ∀ fst (hfst : (b.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars state.memory).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind))
    (hTgtInv : ∀ newVars',
        state'.variables.setArgumentValues? b values' (hRW.blocksInBounds b bIn) = some newVars' →
        (InterpreterState.mk newVars' state'.memory).DefinesDominating
          (InsertPoint.atStart! b newCtx.raw)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed (hRW.blocksInBounds b bIn)).mpr
            (hRW.blocksInBounds b bIn)))
    (hTgtEqInv : ∀ newVars',
        state'.variables.setArgumentValues? b values' (hRW.blocksInBounds b bIn) = some newVars' →
        (InterpreterState.mk newVars' state'.memory).EquationLemmaAt
          (InsertPoint.atStart! b newCtx.raw)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed (hRW.blocksInBounds b bIn)).mpr
            (hRW.blocksInBounds b bIn)))
    (hSrcSplitB : ∃ (front : List OperationPtr) (term : OperationPtr)
        (frontIn : ∀ o ∈ front, o.InBounds ctx.raw) (_termIn : term.InBounds ctx.raw),
        (b.operationList ctx.raw ctx.wellFormed bIn).toList = front ++ [term] ∧
        (∀ (s s' : InterpreterState ctx) (cf : ControlFlowAction),
            interpretOpList front s frontIn ≠ some (.ok (s', some cf))))
    (hOpSim : OpStepSimulation op newOps hRW.σ opIn hRW.newOpsInBounds') :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × ControlFlowAction)
           (r₂ : InterpreterState newCtx × ControlFlowAction) =>
        r₁.1.isRefinedByAt r₂.1 hRW.σ (InsertPoint.atEnd b) (InsertPoint.atEnd b)
          bIn (hRW.blocksInBounds b bIn) ∧ r₁.2.isRefinedBy r₂.2)
      (interpretBlock b values state bIn)
      (interpretBlock b values' state' (hRW.blocksInBounds b bIn)) := by
  have bIn' := hRW.blocksInBounds b bIn
  -- Proof-irrelevant `interpretOpList` list-congruence (used to relabel `dropLast`/`front`).
  have iopl_congr : ∀ {cc : WfIRContext OpCode} {l l' : List OperationPtr} (s : InterpreterState cc)
      (hl : ∀ o ∈ l, o.InBounds cc.raw) (hl' : ∀ o ∈ l', o.InBounds cc.raw),
      l = l' → interpretOpList l s hl = interpretOpList l' s hl' := by
    intro cc l l' s hl hl' h; subst h; rfl
  rw [interpretBlock_eq_setArgumentValues?_interpretTerminatedOpList bIn,
      interpretBlock_eq_setArgumentValues?_interpretTerminatedOpList bIn']
  rcases hsa : state.variables.setArgumentValues? b values bIn with _ | newVars
  · simp [Interp.isRefinedBy]
  · -- Target also sets its block arguments, into a `σ`-refined state (Stage A).
    -- The source succeeded, so its arguments conform; refinement (`hVals`) and argument-type
    -- preservation (`argType_eq`) carry that conformance to the target arguments.
    have tgtConforms : ∀ j, j < b.getNumArguments! newCtx.raw →
        (values'[j]!).Conforms ((b.getArguments! newCtx.raw)[j]!.getType! newCtx.raw) := by
      intro j hj
      rw [BlockPtr.getArguments!.getElem!_eq_getArgument hj]
      have hPt : values[j]! ⊒ values'[j]! := by
        obtain ⟨hsize, hpt⟩ := hVals
        by_cases h : j < values.size
        · exact hpt j h
        · rw [getElem!_neg values j h, getElem!_neg values' j (hsize ▸ h)]
          exact RuntimeValue.isRefinedBy_refl _
      rw [hRW.argType_eq bIn j (hRW.numArgsEq bIn ▸ hj)]
      exact RuntimeValue.Conforms_of_isRefinedBy hPt
        ((VariableState.setArgumentValues?_isSome_iff_conforms state.variables).mpr ⟨newVars, hsa⟩ j
          (hRW.numArgsEq bIn ▸ hj))
    obtain ⟨newVars', hsa', hpsRefVar⟩ := VariableState.setArgumentValues?_isRefinedByAt
      bIn bIn' hState.2 hVals (hRW.argsApplyToArray bIn)
      (fun val valIn hNotArg hdom => hRW.mappingImageNotArg hCtxDom bIn valIn hNotArg hdom)
      tgtConforms hsa
    have hpsRef : (InterpreterState.mk newVars state.memory).isRefinedByAt
        ⟨newVars', state'.memory⟩ hRW.σ
        (InsertPoint.atStart! b ctx.raw) (InsertPoint.atStart! b newCtx.raw) := ⟨hState.1, hpsRefVar⟩
    have hTgtDD := hTgtInv newVars' hsa'
    simp only [hsa', Option.bind_some]
    -- Running `b`'s whole operation list from the entry lands at `atEnd b` (both contexts).
    have hSp : InsertPoint.afterLast (b.operationList ctx.raw ctx.wellFormed bIn).toList ctx.raw
        (InsertPoint.atStart! b ctx.raw) = InsertPoint.atEnd b :=
      afterLast_operationList_atStart!_eq_atEnd bIn
    by_cases hbB : b = block
    · -- Rewritten block `B`: rewrite the op-lists and apply the block-`B` simulation.
      subst hbB
      have hsrc : (b.operationList ctx.raw ctx.wellFormed bIn).toList
          = pre.toList ++ [op] ++ post.toList := by rw [hRW.srcList]; simp
      have htgt : (b.operationList newCtx.raw newCtx.wellFormed bIn').toList
          = pre.toList ++ newOps.toList ++ post.toList := by rw [hRW.tgtList]; simp
      have hTp : InsertPoint.afterLast (pre.toList ++ newOps.toList ++ post.toList) newCtx.raw
          (InsertPoint.atStart! b newCtx.raw) = InsertPoint.atEnd b := by
        rw [← htgt]; exact afterLast_operationList_atStart!_eq_atEnd bIn'
      have hSplit : ∃ (front : List OperationPtr) (term : OperationPtr)
          (frontIn : ∀ o ∈ front, o.InBounds ctx.raw),
          (pre.toList ++ [op] ++ post.toList) = front ++ [term] ∧
          (∀ (s s' : InterpreterState ctx) (cf : ControlFlowAction),
              interpretOpList front s frontIn ≠ some (.ok (s', some cf))) := by
        obtain ⟨front, term, frontIn, _termIn, harr, hno⟩ := hSrcSplitB
        exact ⟨front, term, frontIn, by rw [← hsrc]; exact harr, hno⟩
      have hEqLemArg : ∀ fst (hfst : (b.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars state.memory).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind) :=
        fun fst hfst => hSrcInv newVars hsa fst hfst
      have hTgtEqLemArg := hTgtEqInv newVars' hsa'
      have hbs := hRW.blockSimulation newCtxVerif hCtxDom hpsRef hTgtDD hEqLemArg hTgtEqLemArg hSplit
        hOpSim
      simp only [hsrc] at hSp
      simp only [hsrc, htgt]
      simp only [hSp, hTp] at hbs
      exact hbs
    · -- Other block: op-lists identical, apply scoped cross-context monotonicity.
      have hother := hRW.otherBlocks b bIn bIn' hbB
      have chainSrc := BlockPtr.operationListWF ctx.raw b bIn ctx.wellFormed
      have chainTgt := BlockPtr.operationListWF newCtx.raw b bIn' newCtx.wellFormed
      have hlistEq : (b.operationList newCtx.raw newCtx.wellFormed bIn').toList
          = (b.operationList ctx.raw ctx.wellFormed bIn).toList :=
        (congrArg Array.toList hother).symm
      have hTp : InsertPoint.afterLast (b.operationList ctx.raw ctx.wellFormed bIn).toList newCtx.raw
          (InsertPoint.atStart! b newCtx.raw) = InsertPoint.atEnd b := by
        rw [← hlistEq]; exact afterLast_operationList_atStart!_eq_atEnd bIn'
      have opsIn : ∀ o ∈ (b.operationList ctx.raw ctx.wellFormed bIn).toList,
          o.InBounds ctx.raw := fun o ho => chainSrc.arrayInBounds (by simpa using ho)
      have opsIn' : ∀ o ∈ (b.operationList ctx.raw ctx.wellFormed bIn).toList,
          o.InBounds newCtx.raw := by
        intro o ho; rw [← hlistEq] at ho; exact chainTgt.arrayInBounds (by simpa using ho)
      have hChainSrc : b.OpChainSlice ctx.raw (b.operationList ctx.raw ctx.wellFormed bIn).toList :=
        chainSrc.opChainSlice
      have hChainTgt : b.OpChainSlice newCtx.raw (b.operationList ctx.raw ctx.wellFormed bIn).toList := by
        rw [← hlistEq]; exact chainTgt.opChainSlice
      have hne_op : ∀ o ∈ (b.operationList ctx.raw ctx.wellFormed bIn).toList, o ≠ op := by
        intro o ho heq; subst heq; exact hRW.opErased (opsIn' o ho)
      have hFrame : ∀ o, (h : o ∈ (b.operationList ctx.raw ctx.wellFormed bIn).toList) →
          (hRW.σ).PreservesOperation o o := fun o h => hRW.frame_of_ne (opsIn o h) (hne_op o h)
      obtain ⟨front, term, frontIn, _termIn, harr, hno⟩ := hSrcSplitB
      have hdrop : (b.operationList ctx.raw ctx.wellFormed bIn).toList.dropLast = front := by
        rw [harr, List.dropLast_concat]
      have hPH : ∀ (h : (b.operationList ctx.raw ctx.wellFormed bIn).toList ≠ []),
          InsertPoint.atStart! b ctx.raw
            = .before ((b.operationList ctx.raw ctx.wellFormed bIn).toList.head h) ∧
          InsertPoint.atStart! b newCtx.raw
            = .before ((b.operationList ctx.raw ctx.wellFormed bIn).toList.head h) := by
        intro h
        refine ⟨atStart!_eq_before_head bIn h, ?_⟩
        have hne' : (b.operationList newCtx.raw newCtx.wellFormed bIn').toList ≠ [] := by
          rw [hlistEq]; exact h
        rw [atStart!_eq_before_head bIn' hne']
        congr 1
        have hh : (b.operationList newCtx.raw newCtx.wellFormed bIn').toList.head?
            = (b.operationList ctx.raw ctx.wellFormed bIn).toList.head? := by rw [hlistEq]
        rw [List.head?_eq_some_head hne', List.head?_eq_some_head h] at hh
        exact Option.some.inj hh
      have hInitNoCf : ∀ (s2 : InterpreterState ctx) (cf : ControlFlowAction),
          interpretOpList (b.operationList ctx.raw ctx.wellFormed bIn).toList.dropLast
            ⟨newVars, state.memory⟩
            (fun o ho => opsIn o (List.dropLast_subset _ ho)) ≠ some (.ok (s2, some cf)) := by
        intro s2 cf hcontra
        apply hno ⟨newVars, state.memory⟩ s2 cf
        rw [← iopl_congr ⟨newVars, state.memory⟩
          (fun o ho => opsIn o (List.dropLast_subset _ ho)) frontIn hdrop]
        exact hcontra
      have hmono := interpretTerminatedOpList_monoAt newCtxVerif hCtxDom hRW.newCtxDom
        opsIn opsIn' hChainSrc hChainTgt
        (p := InsertPoint.atStart! b ctx.raw) (p' := InsertPoint.atStart! b newCtx.raw)
        (by grind) (by grind) hpsRef hTgtDD hFrame hPH hInitNoCf
      simp only [hlistEq]
      simp only [hSp, hTp] at hmono
      exact hmono

/-! ## Stage B bundling: cross-block invariant re-establishment

When interpreting a block `b` yields a `.branch res succ`, the entry invariant on `b`'s post-argument
state is threaded through `b`'s operation chain to its terminator's exit, then crossed over the CFG
edge into `succ` (Stage B-core establishment lemmas), giving the entry invariant on `succ`'s
post-argument state. The block's operation list is supplied split as `front ++ [term]` with `term` the
terminator; `hFrontNoCf` (only the last operation branches) certifies the control-flow action comes
from `term`. These structural facts are supplied by the driver (Stage D).
-/

/-- Decompose a branching block run. If interpreting `b` (whose operation list is `front ++ [term]`,
with `front` never branching) yields `.branch res succ`, then `b`'s arguments are set, `front` runs to
completion without a terminator, and the terminator `term` produces the branch. -/
theorem interpretBlock_branch_split
    {ctx : WfIRContext OpCode} {b succ : BlockPtr} (bIn : b.InBounds ctx.raw)
    {values res : Array RuntimeValue} {state exitState : InterpreterState ctx}
    {front : List OperationPtr} {term : OperationPtr}
    (frontIn : ∀ o ∈ front, o.InBounds ctx.raw) (termIn : term.InBounds ctx.raw)
    (harr : (b.operationList ctx.raw ctx.wellFormed bIn).toList = front ++ [term])
    (hFrontNoCf : ∀ (s s' : InterpreterState ctx) (cf : ControlFlowAction),
        interpretOpList front s frontIn ≠ some (.ok (s', some cf)))
    (hRun : interpretBlock b values state bIn = some (.ok (exitState, .branch res succ))) :
    ∃ newVars s',
      state.variables.setArgumentValues? b values bIn = some newVars ∧
      interpretOpList front ⟨newVars, state.memory⟩ frontIn = some (.ok (s', none)) ∧
      interpretOp term s' termIn = some (.ok (exitState, some (.branch res succ))) := by
  rw [interpretBlock_eq_setArgumentValues?_interpretTerminatedOpList bIn] at hRun
  rcases hsa : state.variables.setArgumentValues? b values bIn with _ | newVars
  · rw [hsa] at hRun; simp at hRun
  · rw [hsa] at hRun
    simp only [Option.bind_some] at hRun
    refine ⟨newVars, ?_⟩
    -- Rewrite the block list to `front ++ [term]` and split the terminated run.
    simp only [harr] at hRun
    rw [interpretTerminatedOpList_append] at hRun
    rcases hfront : interpretOpList front ⟨newVars, state.memory⟩ frontIn with _ | (⟨s', act⟩ | _) <;>
      simp only [hfront] at hRun
    · grind
    · cases act with
      | none =>
        rcases hterm : interpretOp term s' termIn with _ | (⟨s'', act'⟩ | _) <;>
          simp only [hterm, interpretTerminatedOpList_cons] at hRun
        · grind
        · cases act' with
          | none => simp only [interpretTerminatedOpList_nil] at hRun; grind
          | some cf => exact ⟨s', rfl, rfl, by grind⟩
        · grind
      | some cf => exact absurd hfront (hFrontNoCf _ _ _)
    · grind

/-- The terminator `term` (the last operation of `b`'s op list `front ++ [term]`) has `b` as parent
and is the block's last operation (`next = none`). -/
theorem operationList_split_term_facts {ctx : WfIRContext OpCode} {b : BlockPtr}
    (bIn : b.InBounds ctx.raw) {front : List OperationPtr} {term : OperationPtr}
    (termIn : term.InBounds ctx.raw)
    (harr : (b.operationList ctx.raw ctx.wellFormed bIn).toList = front ++ [term]) :
    (term.get! ctx.raw).parent = some b ∧ (term.get! ctx.raw).next = none ∧
    b.OpChainSlice ctx.raw (front ++ [term]) ∧
    (b.get! ctx.raw).firstOp = (front ++ [term]).head? := by
  have chain := BlockPtr.operationListWF ctx.raw b bIn ctx.wellFormed
  have hmemL : term ∈ (b.operationList ctx.raw ctx.wellFormed bIn).toList := by rw [harr]; simp
  have hmem : term ∈ b.operationList ctx.raw ctx.wellFormed bIn := by simpa using hmemL
  have hparent : (term.get! ctx.raw).parent = some b := chain.opParent hmem
  have hlen : (b.operationList ctx.raw ctx.wellFormed bIn).size = front.length + 1 := by
    have := congrArg List.length harr; simpa using this
  have hlast : (b.get! ctx.raw).lastOp = some term := by
    rw [chain.last,
        show (b.operationList ctx.raw ctx.wellFormed bIn).size - 1 = front.length from by omega,
        ← Array.getElem?_toList, harr]
    simp
  have hnext : (term.get! ctx.raw).next = none :=
    (BlockPtr.OpChain.next!_eq_none_iff_lastOp!_eq_self termIn chain hparent).mpr hlast
  have hchain : b.OpChainSlice ctx.raw (front ++ [term]) := by
    rw [← harr]; exact chain.opChainSlice
  have hfirst : (b.get! ctx.raw).firstOp = (front ++ [term]).head? := by
    rw [chain.first, ← harr]
    simp [List.head?_eq_getElem?, Array.getElem?_toList]
  exact ⟨hparent, hnext, hchain, hfirst⟩

/-- **Source-side cross-block re-establishment.** Threads `EquationLemmaAt` from `b`'s entry, through
its operation chain to the terminator's exit, then across the CFG edge into `succ`. -/
theorem interpretBlock_branch_equationLemmaAt_succ
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom)
    {b succ : BlockPtr} (bIn : b.InBounds ctx.raw) (succIn : succ.InBounds ctx.raw)
    {values res : Array RuntimeValue} {state exitState : InterpreterState ctx}
    {front : List OperationPtr} {term : OperationPtr}
    (frontIn : ∀ o ∈ front, o.InBounds ctx.raw) (termIn : term.InBounds ctx.raw)
    (harr : (b.operationList ctx.raw ctx.wellFormed bIn).toList = front ++ [term])
    (hFrontNoCf : ∀ (s s' : InterpreterState ctx) (cf : ControlFlowAction),
        interpretOpList front s frontIn ≠ some (.ok (s', some cf)))
    (hEntryInv : ∀ newVars, state.variables.setArgumentValues? b values bIn = some newVars →
        ∀ fst (_hfst : (b.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars state.memory).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind))
    (hRun : interpretBlock b values state bIn = some (.ok (exitState, .branch res succ))) :
    ∀ newVars', exitState.variables.setArgumentValues? succ res succIn = some newVars' →
      ∀ sfst (_hsfst : (succ.get! ctx.raw).firstOp = some sfst),
        (InterpreterState.mk newVars' exitState.memory).EquationLemmaAt (.before sfst)
          (by have := ctx.wellFormed.inBounds; grind) := by
  intro newVars' hArgs sfst hsfst
  obtain ⟨newVars, s', hSetArgs, hFrontRun, hTermRun⟩ :=
    interpretBlock_branch_split bIn frontIn termIn harr hFrontNoCf hRun
  obtain ⟨hparent, hnext, hchain, hfirst⟩ := operationList_split_term_facts bIn termIn harr
  -- Thread `EquationLemmaAt` from entry through `front` to the point before `term`.
  have hBeforeTerm : s'.EquationLemmaAt (.before term) termIn :=
    interpretOpList_equationLemmaAt_before ctxDom frontIn termIn hchain
      (fun fst _ hhead => by
        refine hEntryInv newVars hSetArgs fst ?_
        rw [hfirst]; exact hhead)
      hFrontRun
  -- Step across the terminator to its exit, then across the CFG edge into `succ`.
  have hAfterTerm := interpretOp_equationLemmaAt ctxDom hBeforeTerm hparent hTermRun
  have succMem : succ ∈ term.getSuccessors! ctx.raw :=
    interpretOp_branch_dest_mem_getSuccessors! hTermRun
  have hlast : (b.get! ctx.raw).lastOp = some term := by grind
  have hSucc : succ ∈ b.getSuccessors! ctx.raw := by
    simp only [BlockPtr.getSuccessors!, hlast]; exact succMem
  have hAtEnd : InsertPoint.after term ctx.raw b hparent termIn = InsertPoint.atEnd b := by
    grind [InsertPoint.after]
  have hAtStart : InsertPoint.atStart! succ ctx.raw = InsertPoint.before sfst := by
    simp [InsertPoint.atStart!, hsfst]
  simp only [hAtEnd] at hAfterTerm
  have result := InterpreterState.EquationLemmaAt.setArgumentValues?_succ_entry ctxDom bIn
    hSucc hAfterTerm hArgs
  simp only [hAtStart] at result
  exact result

/-- **Target-side cross-block re-establishment.** Threads `DefinesDominating` from `b`'s entry, through
its operation chain to the terminator's exit, then across the CFG edge into `succ`. -/
theorem interpretBlock_branch_definesDominating_succ
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom)
    {b succ : BlockPtr} (bIn : b.InBounds ctx.raw) (succIn : succ.InBounds ctx.raw)
    {values res : Array RuntimeValue} {state exitState : InterpreterState ctx}
    {front : List OperationPtr} {term : OperationPtr}
    (frontIn : ∀ o ∈ front, o.InBounds ctx.raw) (termIn : term.InBounds ctx.raw)
    (harr : (b.operationList ctx.raw ctx.wellFormed bIn).toList = front ++ [term])
    (hFrontNoCf : ∀ (s s' : InterpreterState ctx) (cf : ControlFlowAction),
        interpretOpList front s frontIn ≠ some (.ok (s', some cf)))
    (hEntryInv : ∀ newVars, state.variables.setArgumentValues? b values bIn = some newVars →
        ∀ fst (_hfst : (b.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars state.memory).DefinesDominating (.before fst)
            (by have := ctx.wellFormed.inBounds; grind))
    (hRun : interpretBlock b values state bIn = some (.ok (exitState, .branch res succ))) :
    ∀ newVars', exitState.variables.setArgumentValues? succ res succIn = some newVars' →
      ∀ sfst (_hsfst : (succ.get! ctx.raw).firstOp = some sfst),
        (InterpreterState.mk newVars' exitState.memory).DefinesDominating (.before sfst)
          (by have := ctx.wellFormed.inBounds; grind) := by
  intro newVars' hArgs sfst hsfst
  obtain ⟨newVars, s', hSetArgs, hFrontRun, hTermRun⟩ :=
    interpretBlock_branch_split bIn frontIn termIn harr hFrontNoCf hRun
  obtain ⟨hparent, hnext, hchain, hfirst⟩ := operationList_split_term_facts bIn termIn harr
  have hBeforeTerm : s'.DefinesDominating (.before term) termIn :=
    interpretOpList_DefinesDominating_before ctxDom frontIn termIn hchain
      (fun fst _ hhead => by
        refine hEntryInv newVars hSetArgs fst ?_
        rw [hfirst]; exact hhead)
      hFrontRun
  have hAfterTerm := interpretOp_DefinesDominating ctxDom hBeforeTerm hparent hTermRun
  have succMem : succ ∈ term.getSuccessors! ctx.raw :=
    interpretOp_branch_dest_mem_getSuccessors! hTermRun
  have hlast : (b.get! ctx.raw).lastOp = some term := by grind
  have hSucc : succ ∈ b.getSuccessors! ctx.raw := by
    simp only [BlockPtr.getSuccessors!, hlast]; exact succMem
  have hAtEnd : InsertPoint.after term ctx.raw b hparent termIn = InsertPoint.atEnd b := by
    grind [InsertPoint.after]
  have hAtStart : InsertPoint.atStart! succ ctx.raw = InsertPoint.before sfst := by
    simp [InsertPoint.atStart!, hsfst]
  simp only [hAtEnd] at hAfterTerm
  have result := InterpreterState.DefinesDominating.setArgumentValues?_succ_entry ctxDom bIn
    hSucc hAfterTerm hArgs
  simp only [hAtStart] at result
  exact result

/-- **Target-side cross-block re-establishment (`atStart!` framing).** Like
`interpretBlock_branch_definesDominating_succ`, but states both the entry invariant and the
re-established successor invariant at the block-entry point `atStart!` (rather than `before` the first
operation), so no first-operation case split is needed by callers. -/
theorem interpretBlock_branch_definesDominating_succ_atStart
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom)
    {b succ : BlockPtr} (bIn : b.InBounds ctx.raw) (succIn : succ.InBounds ctx.raw)
    {values res : Array RuntimeValue} {state exitState : InterpreterState ctx}
    {front : List OperationPtr} {term : OperationPtr}
    (frontIn : ∀ o ∈ front, o.InBounds ctx.raw) (termIn : term.InBounds ctx.raw)
    (harr : (b.operationList ctx.raw ctx.wellFormed bIn).toList = front ++ [term])
    (hFrontNoCf : ∀ (s s' : InterpreterState ctx) (cf : ControlFlowAction),
        interpretOpList front s frontIn ≠ some (.ok (s', some cf)))
    (hEntryInv : ∀ newVars, state.variables.setArgumentValues? b values bIn = some newVars →
        (InterpreterState.mk newVars state.memory).DefinesDominating (.atStart! b ctx.raw)
          (by have := ctx.wellFormed.inBounds; grind))
    (hRun : interpretBlock b values state bIn = some (.ok (exitState, .branch res succ))) :
    ∀ newVars', exitState.variables.setArgumentValues? succ res succIn = some newVars' →
      (InterpreterState.mk newVars' exitState.memory).DefinesDominating (.atStart! succ ctx.raw)
        (by have := ctx.wellFormed.inBounds; grind) := by
  intro newVars' hArgs
  obtain ⟨newVars, s', hSetArgs, hFrontRun, hTermRun⟩ :=
    interpretBlock_branch_split bIn frontIn termIn harr hFrontNoCf hRun
  obtain ⟨hparent, hnext, hchain, hfirst⟩ := operationList_split_term_facts bIn termIn harr
  have hBeforeTerm : s'.DefinesDominating (.before term) termIn :=
    interpretOpList_DefinesDominating_before ctxDom frontIn termIn hchain
      (fun fst _ hhead => by
        have hfo : (b.get! ctx.raw).firstOp = some fst := by rw [hfirst]; exact hhead
        have hdd := hEntryInv newVars hSetArgs
        have heq : InsertPoint.atStart! b ctx.raw = .before fst := by simp [InsertPoint.atStart!, hfo]
        simp only [heq] at hdd
        exact hdd)
      hFrontRun
  have hAfterTerm := interpretOp_DefinesDominating ctxDom hBeforeTerm hparent hTermRun
  have succMem : succ ∈ term.getSuccessors! ctx.raw :=
    interpretOp_branch_dest_mem_getSuccessors! hTermRun
  have hlast : (b.get! ctx.raw).lastOp = some term := by grind
  have hSucc : succ ∈ b.getSuccessors! ctx.raw := by
    simp only [BlockPtr.getSuccessors!, hlast]; exact succMem
  have hAtEnd : InsertPoint.after term ctx.raw b hparent termIn = InsertPoint.atEnd b := by
    grind [InsertPoint.after]
  simp only [hAtEnd] at hAfterTerm
  exact InterpreterState.DefinesDominating.setArgumentValues?_succ_entry ctxDom bIn
    hSucc hAfterTerm hArgs

/-- **Target-side cross-block re-establishment of `EquationLemmaAt` (`atStart!` framing).** The
`EquationLemmaAt` analogue of `interpretBlock_branch_definesDominating_succ_atStart`: threads the SSA
invariant from `b`'s entry through its operation chain to the terminator's exit, then across the CFG
edge into `succ`, stating both the entry and re-established successor invariants at `atStart!`. -/
theorem interpretBlock_branch_equationLemmaAt_succ_atStart
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom)
    {b succ : BlockPtr} (bIn : b.InBounds ctx.raw) (succIn : succ.InBounds ctx.raw)
    {values res : Array RuntimeValue} {state exitState : InterpreterState ctx}
    {front : List OperationPtr} {term : OperationPtr}
    (frontIn : ∀ o ∈ front, o.InBounds ctx.raw) (termIn : term.InBounds ctx.raw)
    (harr : (b.operationList ctx.raw ctx.wellFormed bIn).toList = front ++ [term])
    (hFrontNoCf : ∀ (s s' : InterpreterState ctx) (cf : ControlFlowAction),
        interpretOpList front s frontIn ≠ some (.ok (s', some cf)))
    (hEntryInv : ∀ newVars, state.variables.setArgumentValues? b values bIn = some newVars →
        (InterpreterState.mk newVars state.memory).EquationLemmaAt (.atStart! b ctx.raw)
          (by have := ctx.wellFormed.inBounds; grind))
    (hRun : interpretBlock b values state bIn = some (.ok (exitState, .branch res succ))) :
    ∀ newVars', exitState.variables.setArgumentValues? succ res succIn = some newVars' →
      (InterpreterState.mk newVars' exitState.memory).EquationLemmaAt (.atStart! succ ctx.raw)
        (by have := ctx.wellFormed.inBounds; grind) := by
  intro newVars' hArgs
  obtain ⟨newVars, s', hSetArgs, hFrontRun, hTermRun⟩ :=
    interpretBlock_branch_split bIn frontIn termIn harr hFrontNoCf hRun
  obtain ⟨hparent, hnext, hchain, hfirst⟩ := operationList_split_term_facts bIn termIn harr
  have hBeforeTerm : s'.EquationLemmaAt (.before term) termIn :=
    interpretOpList_equationLemmaAt_before ctxDom frontIn termIn hchain
      (fun fst _ hhead => by
        have hfo : (b.get! ctx.raw).firstOp = some fst := by rw [hfirst]; exact hhead
        have heq := hEntryInv newVars hSetArgs
        have hpt : InsertPoint.atStart! b ctx.raw = .before fst := by
          simp [InsertPoint.atStart!, hfo]
        simp only [hpt] at heq
        exact heq)
      hFrontRun
  have hAfterTerm := interpretOp_equationLemmaAt ctxDom hBeforeTerm hparent hTermRun
  have succMem : succ ∈ term.getSuccessors! ctx.raw :=
    interpretOp_branch_dest_mem_getSuccessors! hTermRun
  have hlast : (b.get! ctx.raw).lastOp = some term := by grind
  have hSucc : succ ∈ b.getSuccessors! ctx.raw := by
    simp only [BlockPtr.getSuccessors!, hlast]; exact succMem
  have hAtEnd : InsertPoint.after term ctx.raw b hparent termIn = InsertPoint.atEnd b := by
    grind [InsertPoint.after]
  simp only [hAtEnd] at hAfterTerm
  exact InterpreterState.EquationLemmaAt.setArgumentValues?_succ_entry ctxDom bIn
    hSucc hAfterTerm hArgs

/-- **Cross-edge transport of the scoped entry relation.** Given the full scoped state refinement at
the predecessor's exit (`atEnd b`), produce the incoming-edge scoped relation at the successor's
entry (`.blockEntry succ`). This is a pure scope-weakening (`isRefinedByAt.weaken`): a value in
`succ`'s incoming-edge scope dominates `succ`'s entry and is not one of `succ`'s arguments, so by
`value_dominatesIp_successor_entry` it already dominated `b`'s exit, where the exit relation applies.
The same argument holds on the target side, value-for-value (no `σ`-image reasoning needed). -/
theorem RewrittenAt.transport_succ_entry
    (hRW : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    (hCtxDom : ctx.Dom)
    {b succ : BlockPtr} (bIn : b.InBounds ctx.raw) (succIn : succ.InBounds ctx.raw)
    (succIn' : succ.InBounds newCtx.raw)
    (hsucc : succ ∈ b.getSuccessors! ctx.raw) (hsucc' : succ ∈ b.getSuccessors! newCtx.raw)
    {s : InterpreterState ctx} {s' : InterpreterState newCtx}
    (h : s.isRefinedByAt s' hRW.σ (InsertPoint.atEnd b) (InsertPoint.atEnd b)
      bIn (hRW.blocksInBounds b bIn)) :
    s.isRefinedByAt s' hRW.σ (.blockEntry succ) (.blockEntry succ)
      succIn succIn' :=
  h.weaken
    (fun _val hsc =>
      (WfIRContext.Dom.value_dominatesIp_successor_entry hCtxDom bIn hsucc hsc.1).resolve_right hsc.2)
    (fun _val hsc =>
      (WfIRContext.Dom.value_dominatesIp_successor_entry hRW.newCtxDom
        (hRW.blocksInBounds b bIn) hsucc' hsc.1).resolve_right hsc.2)

/-- A branching block run lands in one of the block's CFG successors. -/
theorem interpretBlock_branch_mem_getSuccessors!
    {ctx : WfIRContext OpCode} {b succ : BlockPtr} (bIn : b.InBounds ctx.raw)
    {values res : Array RuntimeValue} {state exitState : InterpreterState ctx}
    {front : List OperationPtr} {term : OperationPtr}
    (frontIn : ∀ o ∈ front, o.InBounds ctx.raw) (termIn : term.InBounds ctx.raw)
    (harr : (b.operationList ctx.raw ctx.wellFormed bIn).toList = front ++ [term])
    (hFrontNoCf : ∀ (s s' : InterpreterState ctx) (cf : ControlFlowAction),
        interpretOpList front s frontIn ≠ some (.ok (s', some cf)))
    (hRun : interpretBlock b values state bIn = some (.ok (exitState, .branch res succ))) :
    succ ∈ b.getSuccessors! ctx.raw := by
  obtain ⟨newVars, s', hSetArgs, hFrontRun, hTermRun⟩ :=
    interpretBlock_branch_split bIn frontIn termIn harr hFrontNoCf hRun
  obtain ⟨hparent, hnext, hchain, hfirst⟩ := operationList_split_term_facts bIn termIn harr
  have succMem : succ ∈ term.getSuccessors! ctx.raw :=
    interpretOp_branch_dest_mem_getSuccessors! hTermRun
  have hlast : (b.get! ctx.raw).lastOp = some term := by grind
  simp only [BlockPtr.getSuccessors!, hlast]; exact succMem

/-! ## Stage D: `interpretBlockCFG` refinement (the CFG walk)

Lifts the per-block refinement (Stage C, `interpretBlock_refinement`) to the whole CFG walk via the
`partial_fixpoint` induction on `interpretBlockCFG`. The induction threads the source-entry SSA
invariant `EquationLemmaAt` across CFG edges with `interpretBlock_branch_equationLemmaAt_succ`. No
target-progress argument is needed: a source `ub` refines any target outcome (including a
non-terminating `none`), so the source-UB case closes trivially.
-/

/--
**Stage D — `interpretBlockCFG` refinement.** Interpreting the CFG from any in-bounds block `b` in
the source context is refined by interpreting it from `b` in the target context, under the rewrite
renaming `σ`. The per-block terminator splits `hSrcSplit` (only the last operation of each block
branches) are supplied by the driver (PR 9).
-/
theorem RewrittenAt.interpretBlockCFG_refinement
    (hRW : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    (newCtxVerif : newCtx.Verified)
    (hCtxDom : ctx.Dom)
    (hOpSim : OpStepSimulation op newOps hRW.σ opIn hRW.newOpsInBounds')
    (hSrcSplit : ∀ (b : BlockPtr) (bIn : b.InBounds ctx.raw),
      ∃ (front : List OperationPtr) (term : OperationPtr)
        (frontIn : ∀ o ∈ front, o.InBounds ctx.raw) (_termIn : term.InBounds ctx.raw),
        (b.operationList ctx.raw ctx.wellFormed bIn).toList = front ++ [term] ∧
        (∀ (s s' : InterpreterState ctx) (cf : ControlFlowAction),
            interpretOpList front s frontIn ≠ some (.ok (s', some cf))))
    (hTgtSplit : ∀ (b : BlockPtr) (bIn' : b.InBounds newCtx.raw),
      ∃ (front : List OperationPtr) (term : OperationPtr)
        (frontIn : ∀ o ∈ front, o.InBounds newCtx.raw) (_termIn : term.InBounds newCtx.raw),
        (b.operationList newCtx.raw newCtx.wellFormed bIn').toList = front ++ [term] ∧
        (∀ (s s' : InterpreterState newCtx) (cf : ControlFlowAction),
            interpretOpList front s frontIn ≠ some (.ok (s', some cf))))
    {b : BlockPtr} (bIn : b.InBounds ctx.raw)
    {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState newCtx}
    (hState : state.isRefinedByAt state' hRW.σ (.blockEntry b) (.blockEntry b)
      bIn (hRW.blocksInBounds b bIn))
    (hVals : values ⊒ values')
    (hSrcInv : ∀ newVars, state.variables.setArgumentValues? b values bIn = some newVars →
        ∀ fst (hfst : (b.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars state.memory).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind))
    (hTgtInv : ∀ newVars',
        state'.variables.setArgumentValues? b values' (hRW.blocksInBounds b bIn) = some newVars' →
        (InterpreterState.mk newVars' state'.memory).DefinesDominating
          (InsertPoint.atStart! b newCtx.raw)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed (hRW.blocksInBounds b bIn)).mpr
            (hRW.blocksInBounds b bIn)))
    (hTgtEqInv : ∀ newVars',
        state'.variables.setArgumentValues? b values' (hRW.blocksInBounds b bIn) = some newVars' →
        (InterpreterState.mk newVars' state'.memory).EquationLemmaAt
          (InsertPoint.atStart! b newCtx.raw)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed (hRW.blocksInBounds b bIn)).mpr
            (hRW.blocksInBounds b bIn))) :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
           (r₂ : InterpreterState newCtx × Array RuntimeValue) =>
        r₁.1.memory = r₂.1.memory ∧ r₁.2 ⊒ r₂.2)
      (interpretBlockCFG b values state bIn)
      (interpretBlockCFG b values' state' (hRW.blocksInBounds b bIn)) := by
  refine interpretBlockCFG.fixpoint_induct
    (motive := fun g => ∀ (b : BlockPtr) (bIn : b.InBounds ctx.raw)
      (values values' : Array RuntimeValue)
      (state : InterpreterState ctx) (state' : InterpreterState newCtx),
      state.isRefinedByAt state' hRW.σ (.blockEntry b) (.blockEntry b)
        bIn (hRW.blocksInBounds b bIn) → values ⊒ values' →
      (∀ newVars, state.variables.setArgumentValues? b values bIn = some newVars →
        ∀ fst (hfst : (b.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars state.memory).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind)) →
      (∀ newVars',
        state'.variables.setArgumentValues? b values' (hRW.blocksInBounds b bIn) = some newVars' →
        (InterpreterState.mk newVars' state'.memory).DefinesDominating
          (InsertPoint.atStart! b newCtx.raw)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed (hRW.blocksInBounds b bIn)).mpr
            (hRW.blocksInBounds b bIn))) →
      (∀ newVars',
        state'.variables.setArgumentValues? b values' (hRW.blocksInBounds b bIn) = some newVars' →
        (InterpreterState.mk newVars' state'.memory).EquationLemmaAt
          (InsertPoint.atStart! b newCtx.raw)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed (hRW.blocksInBounds b bIn)).mpr
            (hRW.blocksInBounds b bIn))) →
      Interp.isRefinedBy
        (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
             (r₂ : InterpreterState newCtx × Array RuntimeValue) =>
          r₁.1.memory = r₂.1.memory ∧ r₁.2 ⊒ r₂.2)
        (g b values state bIn)
        (interpretBlockCFG b values' state' (hRW.blocksInBounds b bIn)))
    ?admissible ?step b bIn values values' state state' hState hVals hSrcInv hTgtInv hTgtEqInv
  case admissible =>
    -- Peel the (dependent) leading `∀ b` together with the `g b` application with
    -- `admissible_pi_apply`, the remaining (non-dependent) binders with `admissible_pi`, the
    -- `g b values state bIn` applications with `admissible_apply`, and close at the `none`-bottom.
    apply Lean.Order.admissible_pi_apply
      (P := fun (b : BlockPtr) (gb : Array RuntimeValue → InterpreterState ctx →
              b.InBounds ctx.raw → Interp (InterpreterState ctx × Array RuntimeValue)) =>
        ∀ (bIn : b.InBounds ctx.raw) (values values' : Array RuntimeValue)
          (state : InterpreterState ctx) (state' : InterpreterState newCtx),
          state.isRefinedByAt state' hRW.σ (.blockEntry b) (.blockEntry b)
            bIn (hRW.blocksInBounds b bIn) → values ⊒ values' →
          (∀ newVars, state.variables.setArgumentValues? b values bIn = some newVars →
            ∀ fst (hfst : (b.get! ctx.raw).firstOp = some fst),
              (InterpreterState.mk newVars state.memory).EquationLemmaAt (.before fst)
                (by have := ctx.wellFormed.inBounds; grind)) →
          (∀ newVars',
            state'.variables.setArgumentValues? b values' (hRW.blocksInBounds b bIn) = some newVars' →
            (InterpreterState.mk newVars' state'.memory).DefinesDominating
              (InsertPoint.atStart! b newCtx.raw)
              ((InsertPoint.inBounds_atStart! newCtx.wellFormed (hRW.blocksInBounds b bIn)).mpr
                (hRW.blocksInBounds b bIn))) →
          (∀ newVars',
            state'.variables.setArgumentValues? b values' (hRW.blocksInBounds b bIn) = some newVars' →
            (InterpreterState.mk newVars' state'.memory).EquationLemmaAt
              (InsertPoint.atStart! b newCtx.raw)
              ((InsertPoint.inBounds_atStart! newCtx.wellFormed (hRW.blocksInBounds b bIn)).mpr
                (hRW.blocksInBounds b bIn))) →
          Interp.isRefinedBy
            (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
                 (r₂ : InterpreterState newCtx × Array RuntimeValue) =>
              r₁.1.memory = r₂.1.memory ∧ r₁.2 ⊒ r₂.2)
            (gb values state bIn)
            (interpretBlockCFG b values' state' (hRW.blocksInBounds b bIn)))
    intro b
    apply Lean.Order.admissible_pi; intro bIn
    apply Lean.Order.admissible_pi; intro values
    apply Lean.Order.admissible_pi; intro values'
    apply Lean.Order.admissible_pi; intro state
    apply Lean.Order.admissible_pi; intro state'
    apply Lean.Order.admissible_pi; intro hState
    apply Lean.Order.admissible_pi; intro hVals
    apply Lean.Order.admissible_pi; intro hSrcInv
    apply Lean.Order.admissible_pi; intro hTgtInv
    apply Lean.Order.admissible_pi; intro hTgtEqInv
    apply Lean.Order.admissible_apply
      (P := fun (_v : Array RuntimeValue) (gv : InterpreterState ctx → b.InBounds ctx.raw →
              Interp (InterpreterState ctx × Array RuntimeValue)) =>
        Interp.isRefinedBy
          (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
               (r₂ : InterpreterState newCtx × Array RuntimeValue) =>
            r₁.1.memory = r₂.1.memory ∧ r₁.2 ⊒ r₂.2)
          (gv state bIn) (interpretBlockCFG b values' state' (hRW.blocksInBounds b bIn)))
      (x := values)
    apply Lean.Order.admissible_apply
      (P := fun (_s : InterpreterState ctx) (gs : b.InBounds ctx.raw →
              Interp (InterpreterState ctx × Array RuntimeValue)) =>
        Interp.isRefinedBy
          (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
               (r₂ : InterpreterState newCtx × Array RuntimeValue) =>
            r₁.1.memory = r₂.1.memory ∧ r₁.2 ⊒ r₂.2)
          (gs bIn) (interpretBlockCFG b values' state' (hRW.blocksInBounds b bIn)))
      (x := state)
    apply Lean.Order.admissible_apply
      (P := fun (_h : b.InBounds ctx.raw) (gh : Interp (InterpreterState ctx × Array RuntimeValue)) =>
        Interp.isRefinedBy
          (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
               (r₂ : InterpreterState newCtx × Array RuntimeValue) =>
            r₁.1.memory = r₂.1.memory ∧ r₁.2 ⊒ r₂.2)
          gh (interpretBlockCFG b values' state' (hRW.blocksInBounds b bIn)))
      (x := bIn)
    exact Lean.Order.admissible_flatOrder _ trivial
  case step =>
    intro g IH b bIn values values' state state' hState hVals hSrcInv hTgtInv hTgtEqInv
    have hBlk := hRW.interpretBlock_refinement newCtxVerif hCtxDom bIn hState hVals hSrcInv hTgtInv
      hTgtEqInv (hSrcSplit b bIn) hOpSim
    rw [interpretBlockCFG]
    rcases hsrc : interpretBlock b values state bIn with _ | (⟨s, act⟩ | _)
    · -- Source block run fails: the CFG step is `none`, refinement is trivial.
      simp only [hsrc, Interp.isRefinedBy_none_target]
    · -- Source block run succeeds with exit state `s` and control-flow action `act`.
      rw [hsrc] at hBlk
      simp only [Interp.isRefinedBy_ok_target_iff] at hBlk
      obtain ⟨⟨s', act'⟩, htgt, hsRef, hactRef⟩ := hBlk
      cases act with
      | «return» r =>
        -- A `return`: both CFG walks stop here. The target action is a `return` of refined values.
        obtain ⟨r', hact', hr⟩ : ∃ r', act' = .return r' ∧ r ⊒ r' := by
          cases act' <;> simp_all [ControlFlowAction.isRefinedBy]
        subst hact'
        simp only [hsrc, htgt, Interp.isRefinedBy]
        exact ⟨hsRef.1, hr⟩
      | branch r succ =>
        -- A `branch`: the target action branches to the *same* successor with refined values.
        obtain ⟨r', hact', hr⟩ : ∃ r', act' = .branch r' succ ∧ r ⊒ r' := by
          cases act' <;> simp_all [ControlFlowAction.isRefinedBy]
        subst hact'
        by_cases hsuccIn : succ.InBounds ctx.raw
        · -- Successor in bounds: both walks recurse into `succ`; close with the IH, threading the
          -- source SSA invariant, the target dominance invariant, and the scoped entry relation
          -- across the CFG edge.
          have bIn' := hRW.blocksInBounds b bIn
          obtain ⟨front, term, frontIn, termIn, harr, hFrontNoCf⟩ := hSrcSplit b bIn
          obtain ⟨frontT, termT, frontInT, termInT, harrT, hFrontNoCfT⟩ := hTgtSplit b bIn'
          have hSrcInvSucc := interpretBlock_branch_equationLemmaAt_succ hCtxDom bIn hsuccIn
            frontIn termIn harr hFrontNoCf hSrcInv hsrc
          have hsucc : succ ∈ b.getSuccessors! ctx.raw :=
            interpretBlock_branch_mem_getSuccessors! bIn frontIn termIn harr hFrontNoCf hsrc
          have hsucc' : succ ∈ b.getSuccessors! newCtx.raw :=
            interpretBlock_branch_mem_getSuccessors! bIn' frontInT termInT harrT hFrontNoCfT htgt
          have hStateSucc := hRW.transport_succ_entry hCtxDom bIn hsuccIn
            (hRW.blocksInBounds succ hsuccIn) hsucc hsucc' hsRef
          have hTgtInvSucc := interpretBlock_branch_definesDominating_succ_atStart hRW.newCtxDom
            bIn' (hRW.blocksInBounds succ hsuccIn) frontInT termInT harrT hFrontNoCfT hTgtInv htgt
          have hTgtEqInvSucc := interpretBlock_branch_equationLemmaAt_succ_atStart hRW.newCtxDom
            bIn' (hRW.blocksInBounds succ hsuccIn) frontInT termInT harrT hFrontNoCfT hTgtEqInv htgt
          simp only [hsrc, htgt, dif_pos hsuccIn, dif_pos (hRW.blocksInBounds succ hsuccIn)]
          exact IH succ hsuccIn r r' s s' hStateSucc hr hSrcInvSucc hTgtInvSucc hTgtEqInvSucc
        · -- Successor out of bounds in the source: the source CFG step is `none`, refinement trivial.
          simp only [hsrc, dif_neg hsuccIn, Interp.isRefinedBy_none_target]
    · -- Source block run is UB, which is refined by any target outcome.
      simp only [hsrc, Interp.ub, Interp.isRefinedBy_ub_target]

/-! ## Stage E: `interpretRegion` / `interpretFunction` refinement

Wraps the CFG-walk refinement (Stage D) up through `interpretRegion` and `interpretFunction`. A
function operation `funcOp` survives the rewrite: it has exactly one region, whereas the matched op
`op` has not (clause 9 / `opNotFunction`), so `funcOp ≠ op`. The rewrite therefore preserves the
function's single region, its entry block, and the entry first-op, and the whole-function
interpretation refines. The fresh empty entry state is `σ`-refined in both contexts (no variables,
same memory); the source-entry SSA invariant on it is supplied by the caller (PR 9 / the module-level
driver), exactly as in Stage D.
-/

/-- The fresh, empty interpreter state satisfies the scoped relation at any pair of refinement
points: it defines no variables, so the constraint is vacuous (and the memories coincide). -/
theorem InterpreterState.empty_isRefinedByAt {ctx ctx' : WfIRContext OpCode}
    (μ : ValueMapping ctx ctx') (mem : MemoryState) (s s' : RefinementPoint)
    (sIn : s.InBounds ctx.raw) (s'In : s'.InBounds ctx'.raw) :
    (InterpreterState.mk (VariableState.empty ctx) mem).isRefinedByAt
      (InterpreterState.mk (VariableState.empty ctx') mem) μ s s' sIn s'In := by
  refine ⟨rfl, ?_⟩
  intro val valIn _ _ sv tv hget _
  simp [VariableState.getVar?, VariableState.empty] at hget

/-- Lift a `σ`-refinement of two region runs to a `FunctionResult` refinement of the corresponding
function runs: `interpretFunction` post-processes `interpretRegion` by keeping only the final memory
and the returned values, and `InterpreterState.isRefinedByAt` already entails equal memories, so the
refinement is preserved by that projection. -/
theorem Interp.isRefinedBy_functionResult_of_region {ctx ctx' : WfIRContext OpCode}
    {a : Interp (InterpreterState ctx × Array RuntimeValue)}
    {b : Interp (InterpreterState ctx' × Array RuntimeValue)}
    (h : Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
           (r₂ : InterpreterState ctx' × Array RuntimeValue) =>
        r₁.1.memory = r₂.1.memory ∧ r₁.2 ⊒ r₂.2) a b) :
    Interp.isRefinedBy FunctionResult.isRefinedBy
      (a >>= fun x => pure (x.1.memory, x.2))
      (b >>= fun x => pure (x.1.memory, x.2)) := by
  rcases a with _ | (⟨sf, sres⟩ | _)
  · exact Interp.isRefinedBy_none_target
  · simp only [Interp.isRefinedBy_ok_target_iff] at h
    obtain ⟨⟨sf', sres'⟩, htgt, hsRef, hresRef⟩ := h
    subst htgt
    exact ⟨hsRef, hresRef⟩
  · exact Interp.isRefinedBy_ub_target

/-- Lift a `σ`-refinement of two region runs to an array refinement of the corresponding module runs:
`interpretModule` post-processes `interpretRegion` by keeping only the returned values, so the
value-array refinement carried by the region refinement is exactly what survives. -/
theorem Interp.isRefinedBy_moduleResult_of_region {ctx ctx' : WfIRContext OpCode}
    {a : Interp (InterpreterState ctx × Array RuntimeValue)}
    {b : Interp (InterpreterState ctx' × Array RuntimeValue)}
    (h : Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
           (r₂ : InterpreterState ctx' × Array RuntimeValue) =>
        r₁.1.memory = r₂.1.memory ∧ r₁.2 ⊒ r₂.2) a b) :
    Interp.isRefinedBy RuntimeValue.arrayIsRefinedBy
      (a >>= fun x => pure x.2)
      (b >>= fun x => pure x.2) := by
  rcases a with _ | (⟨sf, sres⟩ | _)
  · exact Interp.isRefinedBy_none_target
  · simp only [Interp.isRefinedBy_ok_target_iff] at h
    obtain ⟨⟨sf', sres'⟩, htgt, _hsRef, hresRef⟩ := h
    subst htgt
    exact hresRef
  · exact Interp.isRefinedBy_ub_target

/--
**Stage E — `interpretRegion` refinement.** Interpreting the source region `r` in the source context
is refined by interpreting the (equal) target region `r'` in the target context, under the rewrite
renaming `σ`. The two region pointers coincide (`hrr`) because the rewrite preserves the function's
single region; the rewrite further preserves `r`'s first block (clause 8), so both walks enter the CFG
at the same entry block, where the per-entry source SSA invariant `hSrcInv` feeds the Stage-D CFG
refinement.
-/
theorem RewrittenAt.interpretRegion_refinement
    (hRW : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    (newCtxVerif : newCtx.Verified)
    (hCtxDom : ctx.Dom)
    (hOpSim : OpStepSimulation op newOps hRW.σ opIn hRW.newOpsInBounds')
    (hSrcSplit : ∀ (b : BlockPtr) (bIn : b.InBounds ctx.raw),
      ∃ (front : List OperationPtr) (term : OperationPtr)
        (frontIn : ∀ o ∈ front, o.InBounds ctx.raw) (_termIn : term.InBounds ctx.raw),
        (b.operationList ctx.raw ctx.wellFormed bIn).toList = front ++ [term] ∧
        (∀ (s s' : InterpreterState ctx) (cf : ControlFlowAction),
            interpretOpList front s frontIn ≠ some (.ok (s', some cf))))
    (hTgtSplit : ∀ (b : BlockPtr) (bIn' : b.InBounds newCtx.raw),
      ∃ (front : List OperationPtr) (term : OperationPtr)
        (frontIn : ∀ o ∈ front, o.InBounds newCtx.raw) (_termIn : term.InBounds newCtx.raw),
        (b.operationList newCtx.raw newCtx.wellFormed bIn').toList = front ++ [term] ∧
        (∀ (s s' : InterpreterState newCtx) (cf : ControlFlowAction),
            interpretOpList front s frontIn ≠ some (.ok (s', some cf))))
    {r r' : RegionPtr} (rIn : r.InBounds ctx.raw) (rIn' : r'.InBounds newCtx.raw)
    (hrr : r' = r)
    {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState newCtx}
    (hState : ∀ (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw),
        state.isRefinedByAt state' hRW.σ (.blockEntry entryBlock) (.blockEntry entryBlock)
          entryIn (hRW.blocksInBounds entryBlock entryIn))
    (hVals : values ⊒ values')
    (hSrcInv : ∀ (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw)
        (newVars : VariableState ctx),
        state.variables.setArgumentValues? entryBlock values entryIn = some newVars →
        ∀ fst (hfst : (entryBlock.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars state.memory).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind))
    (hTgtInv : ∀ (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw)
        (newVars' : VariableState newCtx),
        state'.variables.setArgumentValues? entryBlock values'
          (hRW.blocksInBounds entryBlock entryIn) = some newVars' →
        (InterpreterState.mk newVars' state'.memory).DefinesDominating
          (InsertPoint.atStart! entryBlock newCtx.raw)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed
            (hRW.blocksInBounds entryBlock entryIn)).mpr (hRW.blocksInBounds entryBlock entryIn)))
    (hTgtEqInv : ∀ (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw)
        (newVars' : VariableState newCtx),
        state'.variables.setArgumentValues? entryBlock values'
          (hRW.blocksInBounds entryBlock entryIn) = some newVars' →
        (InterpreterState.mk newVars' state'.memory).EquationLemmaAt
          (InsertPoint.atStart! entryBlock newCtx.raw)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed
            (hRW.blocksInBounds entryBlock entryIn)).mpr (hRW.blocksInBounds entryBlock entryIn))) :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
           (r₂ : InterpreterState newCtx × Array RuntimeValue) =>
        r₁.1.memory = r₂.1.memory ∧ r₁.2 ⊒ r₂.2)
      (interpretRegion r values state rIn)
      (interpretRegion r' values' state' rIn') := by
  subst hrr
  unfold interpretRegion
  -- The rewrite preserves the region's first block (clause 8): both walks enter the same entry block.
  have hfb : (r'.get newCtx.raw rIn').firstBlock = (r'.get ctx.raw rIn).firstBlock := by
    rw [← RegionPtr.get!_eq_get rIn, ← RegionPtr.get!_eq_get rIn']
    exact hRW.regionFirstBlockPreserved r' rIn
  -- Case on the source first block; the target enters the same block by `hfb`.
  split
  · -- Empty region: the source run is `none`, refinement is trivial.
    exact Interp.isRefinedBy_none_target
  · rename_i entryBlock heq
    -- The entry block is in bounds (it is the region's first block).
    have entryIn : entryBlock.InBounds ctx.raw := by
      have hmaybe := RegionPtr.firstBlock!_inBounds ctx.wellFormed.inBounds rIn
      rw [Option.maybe_def] at hmaybe
      exact hmaybe entryBlock (by rw [RegionPtr.get!_eq_get rIn]; exact heq)
    have hentry : (r'.get ctx.raw rIn).firstBlock = some entryBlock := heq
    split
    · -- Target empty: contradicts `hfb` + `hentry`.
      rename_i heqt
      have h1 : (r'.get newCtx.raw rIn').firstBlock = none := heqt
      rw [hfb, hentry] at h1
      simp at h1
    · rename_i entryBlock' heqt
      have hee : entryBlock' = entryBlock := by
        have h1 : (r'.get newCtx.raw rIn').firstBlock = some entryBlock' := heqt
        rw [hfb, hentry] at h1
        simpa using h1.symm
      subst entryBlock'
      exact hRW.interpretBlockCFG_refinement newCtxVerif hCtxDom hOpSim hSrcSplit hTgtSplit entryIn
        (hState entryBlock entryIn) hVals
        (fun newVars h fst hfst => hSrcInv entryBlock entryIn newVars h fst hfst)
        (fun newVars' h => hTgtInv entryBlock entryIn newVars' h)
        (fun newVars' h => hTgtEqInv entryBlock entryIn newVars' h)

/--
**Stage E — `interpretFunction` refinement (monotonicity).** Interpreting a function operation
`funcOp` on refined arguments in the source context is refined by interpreting it in the target
context, under the rewrite renaming `σ`. `funcOp` survives the rewrite because it is a function (one
region) while the matched op `op` is not (clause 9 / `opNotFunction`), so the single region — and with
it the entry CFG walk — is preserved. The empty entry state is `σ`-refined; the source-entry SSA
invariant on it (`hSrcInv`) is supplied by the caller.
-/
theorem RewrittenAt.interpretFunction_refinement
    (hRW : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    (newCtxVerif : newCtx.Verified)
    (hCtxDom : ctx.Dom)
    (hOpSim : OpStepSimulation op newOps hRW.σ opIn hRW.newOpsInBounds')
    (hSrcSplit : ∀ (b : BlockPtr) (bIn : b.InBounds ctx.raw),
      ∃ (front : List OperationPtr) (term : OperationPtr)
        (frontIn : ∀ o ∈ front, o.InBounds ctx.raw) (_termIn : term.InBounds ctx.raw),
        (b.operationList ctx.raw ctx.wellFormed bIn).toList = front ++ [term] ∧
        (∀ (s s' : InterpreterState ctx) (cf : ControlFlowAction),
            interpretOpList front s frontIn ≠ some (.ok (s', some cf))))
    (hTgtSplit : ∀ (b : BlockPtr) (bIn' : b.InBounds newCtx.raw),
      ∃ (front : List OperationPtr) (term : OperationPtr)
        (frontIn : ∀ o ∈ front, o.InBounds newCtx.raw) (_termIn : term.InBounds newCtx.raw),
        (b.operationList newCtx.raw newCtx.wellFormed bIn').toList = front ++ [term] ∧
        (∀ (s s' : InterpreterState newCtx) (cf : ControlFlowAction),
            interpretOpList front s frontIn ≠ some (.ok (s', some cf))))
    {funcOp : OperationPtr} (funcOpIn : funcOp.InBounds ctx.raw)
    (funcOpIn' : funcOp.InBounds newCtx.raw)
    {values values' : Array RuntimeValue} {mem : MemoryState}
    (hVals : values ⊒ values')
    (hSrcInv : ∀ (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw)
        (newVars : VariableState ctx),
        (VariableState.empty ctx).setArgumentValues? entryBlock values entryIn = some newVars →
        ∀ fst (hfst : (entryBlock.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars mem).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind))
    (hTgtInv : ∀ (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw)
        (newVars' : VariableState newCtx),
        (VariableState.empty newCtx).setArgumentValues? entryBlock values'
          (hRW.blocksInBounds entryBlock entryIn) = some newVars' →
        (InterpreterState.mk newVars' mem).DefinesDominating
          (InsertPoint.atStart! entryBlock newCtx.raw)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed
            (hRW.blocksInBounds entryBlock entryIn)).mpr (hRW.blocksInBounds entryBlock entryIn)))
    (hTgtEqInv : ∀ (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw)
        (newVars' : VariableState newCtx),
        (VariableState.empty newCtx).setArgumentValues? entryBlock values'
          (hRW.blocksInBounds entryBlock entryIn) = some newVars' →
        (InterpreterState.mk newVars' mem).EquationLemmaAt
          (InsertPoint.atStart! entryBlock newCtx.raw)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed
            (hRW.blocksInBounds entryBlock entryIn)).mpr (hRW.blocksInBounds entryBlock entryIn))) :
    Interp.isRefinedBy FunctionResult.isRefinedBy
      (interpretFunction funcOp values mem funcOpIn)
      (interpretFunction funcOp values' mem funcOpIn') := by
  unfold interpretFunction
  by_cases hNum : funcOp.getNumRegions ctx.raw funcOpIn = 1
  · -- `funcOp` is a function (one region), so it is not the matched op `op` (clause 9), hence survives.
    have hNe : funcOp ≠ op := by
      rintro rfl
      exact hRW.opNotFunction (by rw [OperationPtr.getNumRegions!_eq_getNumRegions funcOpIn]; exact hNum)
    have hNum' : funcOp.getNumRegions newCtx.raw funcOpIn' = 1 := by
      rw [show funcOp.getNumRegions newCtx.raw funcOpIn'
            = funcOp.getNumRegions ctx.raw funcOpIn from hRW.getNumRegions_eq funcOpIn hNe]
      exact hNum
    -- Both functions proceed (the `≠ 1` guard is false on each side).
    rw [dif_neg (by rw [hNum]; simp), dif_neg (by rw [hNum']; simp)]
    -- The single region is preserved: same pointer, in bounds in both contexts.
    have hi : (0 : Nat) < funcOp.getNumRegions ctx.raw funcOpIn := by rw [hNum]; omega
    have hi' : (0 : Nat) < funcOp.getNumRegions newCtx.raw funcOpIn' := by rw [hNum']; omega
    have hReg : funcOp.getRegion newCtx.raw 0 funcOpIn' hi' = funcOp.getRegion ctx.raw 0 funcOpIn hi :=
      hRW.getRegion_eq funcOpIn hNe 0 hi
    have rIn : (funcOp.getRegion ctx.raw 0 funcOpIn hi).InBounds ctx.raw := by
      rw [← OperationPtr.getRegion!_eq_getRegion hi]
      exact OperationPtr.getRegions!_inBounds ctx.wellFormed.inBounds funcOpIn (by grind)
    have rIn' : (funcOp.getRegion newCtx.raw 0 funcOpIn' hi').InBounds newCtx.raw := by
      rw [← OperationPtr.getRegion!_eq_getRegion hi']
      exact OperationPtr.getRegions!_inBounds newCtx.wellFormed.inBounds funcOpIn'
        (by rw [OperationPtr.getNumRegions!_eq_getNumRegions funcOpIn']; exact hi')
    -- The single region is preserved, so its interpretation refines (Stage E region lemma).
    have hregRef := hRW.interpretRegion_refinement newCtxVerif hCtxDom hOpSim hSrcSplit hTgtSplit
      rIn rIn' hReg (state := ⟨.empty ctx, mem⟩) (state' := ⟨.empty newCtx, mem⟩)
      (fun entryBlock entryIn => InterpreterState.empty_isRefinedByAt hRW.σ mem
        (.blockEntry entryBlock) (.blockEntry entryBlock)
        entryIn (hRW.blocksInBounds entryBlock entryIn))
      hVals
      (fun entryBlock entryIn newVars h fst hfst => hSrcInv entryBlock entryIn newVars h fst hfst)
      (fun entryBlock entryIn newVars' h => hTgtInv entryBlock entryIn newVars' h)
      (fun entryBlock entryIn newVars' h => hTgtEqInv entryBlock entryIn newVars' h)
    -- The function result keeps only the final memory and returned values of the region run.
    show Interp.isRefinedBy FunctionResult.isRefinedBy
      ((interpretRegion (funcOp.getRegion ctx.raw 0 funcOpIn hi) values ⟨.empty ctx, mem⟩ rIn)
        >>= fun x => pure (x.1.memory, x.2))
      ((interpretRegion (funcOp.getRegion newCtx.raw 0 funcOpIn' hi') values' ⟨.empty newCtx, mem⟩ rIn')
        >>= fun x => pure (x.1.memory, x.2))
    exact Interp.isRefinedBy_functionResult_of_region hregRef
  · -- `funcOp` is not a function: the source run is `none`, refinement is trivial.
    rw [dif_pos (by simpa using hNum)]
    exact Interp.isRefinedBy_none_target

/--
**Stage E — `interpretModule` refinement (monotonicity).** Interpreting a module operation
`moduleOp` in the source context is refined by interpreting it in the target context, under the
rewrite renaming `σ`. As with `interpretFunction`, `moduleOp` survives the rewrite because it has a
single region while the matched op `op` does not (clause 9 / `opNotFunction`), so the region — and its
entry CFG walk — is preserved. The module starts from the fresh empty state (no variables, empty
memory, no arguments); the source-entry SSA invariant on it (`hSrcInv`) is supplied by the caller.
-/
theorem RewrittenAt.interpretModule_refinement
    (hRW : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    (newCtxVerif : newCtx.Verified)
    (hCtxDom : ctx.Dom)
    (hOpSim : OpStepSimulation op newOps hRW.σ opIn hRW.newOpsInBounds')
    (hSrcSplit : ∀ (b : BlockPtr) (bIn : b.InBounds ctx.raw),
      ∃ (front : List OperationPtr) (term : OperationPtr)
        (frontIn : ∀ o ∈ front, o.InBounds ctx.raw) (_termIn : term.InBounds ctx.raw),
        (b.operationList ctx.raw ctx.wellFormed bIn).toList = front ++ [term] ∧
        (∀ (s s' : InterpreterState ctx) (cf : ControlFlowAction),
            interpretOpList front s frontIn ≠ some (.ok (s', some cf))))
    (hTgtSplit : ∀ (b : BlockPtr) (bIn' : b.InBounds newCtx.raw),
      ∃ (front : List OperationPtr) (term : OperationPtr)
        (frontIn : ∀ o ∈ front, o.InBounds newCtx.raw) (_termIn : term.InBounds newCtx.raw),
        (b.operationList newCtx.raw newCtx.wellFormed bIn').toList = front ++ [term] ∧
        (∀ (s s' : InterpreterState newCtx) (cf : ControlFlowAction),
            interpretOpList front s frontIn ≠ some (.ok (s', some cf))))
    {moduleOp : OperationPtr} (moduleOpIn : moduleOp.InBounds ctx.raw)
    (moduleOpIn' : moduleOp.InBounds newCtx.raw)
    (hSrcInv : ∀ (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw)
        (newVars : VariableState ctx),
        (VariableState.empty ctx).setArgumentValues? entryBlock #[] entryIn = some newVars →
        ∀ fst (hfst : (entryBlock.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars MemoryState.empty).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind))
    (hTgtInv : ∀ (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw)
        (newVars' : VariableState newCtx),
        (VariableState.empty newCtx).setArgumentValues? entryBlock #[]
          (hRW.blocksInBounds entryBlock entryIn) = some newVars' →
        (InterpreterState.mk newVars' MemoryState.empty).DefinesDominating
          (InsertPoint.atStart! entryBlock newCtx.raw)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed
            (hRW.blocksInBounds entryBlock entryIn)).mpr (hRW.blocksInBounds entryBlock entryIn)))
    (hTgtEqInv : ∀ (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw)
        (newVars' : VariableState newCtx),
        (VariableState.empty newCtx).setArgumentValues? entryBlock #[]
          (hRW.blocksInBounds entryBlock entryIn) = some newVars' →
        (InterpreterState.mk newVars' MemoryState.empty).EquationLemmaAt
          (InsertPoint.atStart! entryBlock newCtx.raw)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed
            (hRW.blocksInBounds entryBlock entryIn)).mpr (hRW.blocksInBounds entryBlock entryIn))) :
    Interp.isRefinedBy RuntimeValue.arrayIsRefinedBy
      (interpretModule ctx moduleOp moduleOpIn)
      (interpretModule newCtx moduleOp moduleOpIn') := by
  unfold interpretModule
  by_cases hNum : moduleOp.getNumRegions ctx.raw moduleOpIn = 1
  · -- `moduleOp` has one region, so it is not the matched op `op` (clause 9), hence survives.
    have hNe : moduleOp ≠ op := by
      rintro rfl
      exact hRW.opNotFunction (by rw [OperationPtr.getNumRegions!_eq_getNumRegions moduleOpIn]; exact hNum)
    have hNum' : moduleOp.getNumRegions newCtx.raw moduleOpIn' = 1 := by
      rw [show moduleOp.getNumRegions newCtx.raw moduleOpIn'
            = moduleOp.getNumRegions ctx.raw moduleOpIn from hRW.getNumRegions_eq moduleOpIn hNe]
      exact hNum
    -- Both modules proceed (the `≠ 1` guard is false on each side).
    rw [dif_neg (by rw [hNum]; simp), dif_neg (by rw [hNum']; simp)]
    -- The single region is preserved: same pointer, in bounds in both contexts.
    have hi : (0 : Nat) < moduleOp.getNumRegions ctx.raw moduleOpIn := by rw [hNum]; omega
    have hi' : (0 : Nat) < moduleOp.getNumRegions newCtx.raw moduleOpIn' := by rw [hNum']; omega
    have hReg : moduleOp.getRegion newCtx.raw 0 moduleOpIn' hi' = moduleOp.getRegion ctx.raw 0 moduleOpIn hi :=
      hRW.getRegion_eq moduleOpIn hNe 0 hi
    have rIn : (moduleOp.getRegion ctx.raw 0 moduleOpIn hi).InBounds ctx.raw := by
      rw [← OperationPtr.getRegion!_eq_getRegion hi]
      exact OperationPtr.getRegions!_inBounds ctx.wellFormed.inBounds moduleOpIn (by grind)
    have rIn' : (moduleOp.getRegion newCtx.raw 0 moduleOpIn' hi').InBounds newCtx.raw := by
      rw [← OperationPtr.getRegion!_eq_getRegion hi']
      exact OperationPtr.getRegions!_inBounds newCtx.wellFormed.inBounds moduleOpIn'
        (by rw [OperationPtr.getNumRegions!_eq_getNumRegions moduleOpIn']; exact hi')
    -- The single region is preserved, so its interpretation refines (Stage E region lemma).
    have hregRef := hRW.interpretRegion_refinement newCtxVerif hCtxDom hOpSim hSrcSplit hTgtSplit
      rIn rIn' hReg (state := InterpreterState.empty ctx) (state' := InterpreterState.empty newCtx)
      (fun entryBlock entryIn => InterpreterState.empty_isRefinedByAt hRW.σ
        MemoryState.empty (.blockEntry entryBlock) (.blockEntry entryBlock)
        entryIn (hRW.blocksInBounds entryBlock entryIn))
      (RuntimeValue.arrayIsRefinedBy_refl #[])
      (fun entryBlock entryIn newVars h fst hfst => hSrcInv entryBlock entryIn newVars h fst hfst)
      (fun entryBlock entryIn newVars' h => hTgtInv entryBlock entryIn newVars' h)
      (fun entryBlock entryIn newVars' h => hTgtEqInv entryBlock entryIn newVars' h)
    -- The module result keeps only the returned values of the region run.
    show Interp.isRefinedBy RuntimeValue.arrayIsRefinedBy
      ((interpretRegion (moduleOp.getRegion ctx.raw 0 moduleOpIn hi) #[] (InterpreterState.empty ctx) rIn)
        >>= fun x => pure x.2)
      ((interpretRegion (moduleOp.getRegion newCtx.raw 0 moduleOpIn' hi') #[] (InterpreterState.empty newCtx) rIn')
        >>= fun x => pure x.2)
    exact Interp.isRefinedBy_moduleResult_of_region hregRef
  · -- `moduleOp` has no single region: the source run is `none`, refinement is trivial.
    rw [dif_pos (by simpa using hNum)]
    exact Interp.isRefinedBy_none_target

/--
**Stage E — module refinement (`isModuleRefinedBy`).** A rewrite refines a module: every top-level
`func.func` of `moduleOp` in the source context is refined, as a function, by the *same* operation in
the target context. The surviving function is its own witness — it is distinct from the matched `op`
(a `func.func` has one region by verification, `op` has none), so it survives the rewrite, keeps its
op type and `sym_name` (`frame`), and keeps `moduleOp` as its enclosing operation
(`getParentOpPreserved`); the per-function refinement is exactly `interpretFunction_refinement`.
-/
theorem RewrittenAt.isModuleRefinedBy
    (hRW : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    (ctxVerif : ctx.Verified)
    (newCtxVerif : newCtx.Verified)
    (hCtxDom : ctx.Dom)
    (hOpSim : OpStepSimulation op newOps hRW.σ opIn hRW.newOpsInBounds')
    (hSrcSplit : ∀ (b : BlockPtr) (bIn : b.InBounds ctx.raw),
      ∃ (front : List OperationPtr) (term : OperationPtr)
        (frontIn : ∀ o ∈ front, o.InBounds ctx.raw) (_termIn : term.InBounds ctx.raw),
        (b.operationList ctx.raw ctx.wellFormed bIn).toList = front ++ [term] ∧
        (∀ (s s' : InterpreterState ctx) (cf : ControlFlowAction),
            interpretOpList front s frontIn ≠ some (.ok (s', some cf))))
    (hTgtSplit : ∀ (b : BlockPtr) (bIn' : b.InBounds newCtx.raw),
      ∃ (front : List OperationPtr) (term : OperationPtr)
        (frontIn : ∀ o ∈ front, o.InBounds newCtx.raw) (_termIn : term.InBounds newCtx.raw),
        (b.operationList newCtx.raw newCtx.wellFormed bIn').toList = front ++ [term] ∧
        (∀ (s s' : InterpreterState newCtx) (cf : ControlFlowAction),
            interpretOpList front s frontIn ≠ some (.ok (s', some cf))))
    (hSrcInv : ∀ (_funcOp : OperationPtr) (values : Array RuntimeValue) (mem : MemoryState)
        (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw) (newVars : VariableState ctx),
        (VariableState.empty ctx).setArgumentValues? entryBlock values entryIn = some newVars →
        ∀ fst (hfst : (entryBlock.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars mem).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind))
    (hTgtInv : ∀ (_funcOp : OperationPtr) (values' : Array RuntimeValue) (mem : MemoryState)
        (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw) (newVars' : VariableState newCtx),
        (VariableState.empty newCtx).setArgumentValues? entryBlock values'
          (hRW.blocksInBounds entryBlock entryIn) = some newVars' →
        (InterpreterState.mk newVars' mem).DefinesDominating
          (InsertPoint.atStart! entryBlock newCtx.raw)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed
            (hRW.blocksInBounds entryBlock entryIn)).mpr (hRW.blocksInBounds entryBlock entryIn)))
    (hTgtEqInv : ∀ (_funcOp : OperationPtr) (values' : Array RuntimeValue) (mem : MemoryState)
        (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw) (newVars' : VariableState newCtx),
        (VariableState.empty newCtx).setArgumentValues? entryBlock values'
          (hRW.blocksInBounds entryBlock entryIn) = some newVars' →
        (InterpreterState.mk newVars' mem).EquationLemmaAt
          (InsertPoint.atStart! entryBlock newCtx.raw)
          ((InsertPoint.inBounds_atStart! newCtx.wellFormed
            (hRW.blocksInBounds entryBlock entryIn)).mpr (hRW.blocksInBounds entryBlock entryIn)))
    {moduleOp : OperationPtr} :
    moduleOp.isModuleRefinedBy ctx moduleOp newCtx := by
  intro func₁ func₁In name hTop
  -- A verified `func.func` has one region, while `op` has none, so the function survives.
  have hfuncVerif : func₁.Verified ctx func₁In :=
    OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants ctxVerif func₁In
  have hOneRegion : func₁.getNumRegions! ctx.raw = 1 :=
    OperationPtr.Verified.func_func hfuncVerif hTop.isFunc
  have hne : func₁ ≠ op := by rintro rfl; exact hRW.opNotFunction hOneRegion
  have func₁In' : func₁.InBounds newCtx.raw := hRW.survives func₁ func₁In hne
  have hframe := hRW.frame_of_ne func₁In hne
  refine ⟨func₁, func₁In', ⟨?_, ?_, ?_⟩, ?_⟩
  · -- The op type `.func .func` is preserved.
    rw [hframe.opType]; exact hTop.isFunc
  · -- The `sym_name` property is preserved (transport the `props` frame across the op-type equality).
    rw [hTop.hasName]
    have hOT : func₁.getOpType! newCtx.raw = func₁.getOpType! ctx.raw := hframe.opType
    have hp : func₁.getProperties! newCtx.raw (func₁.getOpType! newCtx.raw)
            = hOT ▸ func₁.getProperties! ctx.raw (func₁.getOpType! ctx.raw) := hframe.props
    have hF : func₁.getOpType! ctx.raw = OpCode.func Func.func := hTop.isFunc
    clear hSrcInv hTgtInv hSrcSplit hTgtSplit hOpSim hframe hTop
    grind
  · -- The enclosing operation `moduleOp` is preserved.
    exact hRW.getParentOpPreserved func₁ moduleOp func₁In hne hTop.isTopLevel
  · -- The per-function refinement is Stage E.
    intro values valuesTarget mem hVals
    exact hRW.interpretFunction_refinement newCtxVerif hCtxDom hOpSim hSrcSplit hTgtSplit
      func₁In func₁In' hVals
      (fun entryBlock entryIn newVars h fst hfst =>
        hSrcInv func₁ values mem entryBlock entryIn newVars h fst hfst)
      (fun entryBlock entryIn newVars' h =>
        hTgtInv func₁ valuesTarget mem entryBlock entryIn newVars' h)
      (fun entryBlock entryIn newVars' h =>
        hTgtEqInv func₁ valuesTarget mem entryBlock entryIn newVars' h)

/-! ## PR 9: connecting the concrete driver `fromLocalRewrite` to `RewrittenAt`

The whole soundness lift above is developed against the abstract `RewrittenAt` relation. This section
bridges it to the concrete driver `RewritePattern.fromLocalRewrite`: when the driver runs the rewrite
branch (the pattern matched `op`, producing `newOps`/`newValues`) and succeeds with output rewriter
`rewriter'`, the net edit `rewriter.ctx ↦ rewriter'.ctx` is exactly a `RewrittenAt` instance.

### Keystone: the driver's net context is a pure `WfRewriter` fold

`fromLocalRewrite` threads a `PatternRewriter` (carrying a worklist) through three IR edits:
*insert each `newOp` before `op`*, *redirect each result `op.getResult i` to `newValues[i]`*, and
*erase `op`*. Each `PatternRewriter` primitive (`insertOp`/`replaceValue`/`eraseOp`) only touches the
`.ctx` field through the corresponding `WfRewriter` call; the worklist bookkeeping is inert for the
IR. So `rewriter'.ctx` is the pure fold of the underlying `WfRewriter` operations over the pattern's
output context `newCtxPat`, *independent of the worklist*. This decomposition is the keystone: every
`RewrittenAt` field is a statement about `rewriter'.ctx`, so it is only approachable once `rewriter'.ctx`
is characterized this way (via the existing `operationList_rewriter_insertOp`/`_eraseOp` and the
`*_insertOp`/`*_detachOp` GetSet libraries). -/

/-- An in-bounds operation that lives in `block` splits `block`'s operation list as
`pre ++ [op] ++ post` (its predecessors and successors in the block's op chain). -/
theorem BlockPtr.operationList_split_at_op {ctx : WfIRContext OpCode}
    {op : OperationPtr} {block : BlockPtr}
    (opIn : op.InBounds ctx.raw) (hParent : (op.get! ctx.raw).parent = some block)
    (blockIn : block.InBounds ctx.raw) :
    ∃ pre post, block.operationList ctx.raw ctx.wellFormed blockIn = pre ++ #[op] ++ post := by
  have hmem : op ∈ block.operationList ctx.raw ctx.wellFormed blockIn :=
    (BlockPtr.operationList.mem opIn).mp hParent
  obtain ⟨s, t, hst⟩ :=
    List.append_of_mem (a := op)
      (l := (block.operationList ctx.raw ctx.wellFormed blockIn).toList) (by simpa using hmem)
  exact ⟨s.toArray, t.toArray, by apply Array.toList_inj.mp; simp [hst]⟩

/-- Generic invariant transport across a monadic left fold in the `Option` monad: if a predicate `P`
is preserved by every successful step `f b a = some b'`, then it is preserved across the whole fold
(when it succeeds). The keystone fields below instantiate `P` with `InBounds`, `operationList`, … to
transport facts through the driver's `insertOp`/`replaceValue` folds. -/
theorem List.foldlM_option_invariant {α β : Type} {f : β → α → Option β} {P : β → Prop}
    (hstep : ∀ b a b', f b a = some b' → (P b' ↔ P b)) :
    ∀ {init s : β} {l : List α}, l.foldlM f init = some s → (P s ↔ P init) := by
  intro init s l
  induction l generalizing init with
  | nil =>
    intro h
    rw [List.foldlM_nil] at h
    obtain rfl : init = s := by simpa using h
    rfl
  | cons a t ih =>
    intro h
    rw [List.foldlM_cons] at h
    obtain ⟨b, hf, hb⟩ := Option.bind_eq_some_iff.mp h
    rw [ih hb, hstep init a b hf]

/-- `Array` version of `List.foldlM_option_invariant`. -/
theorem Array.foldlM_option_invariant {α β : Type} {f : β → α → Option β} {P : β → Prop}
    {init s : β} {xs : Array α}
    (hstep : ∀ b a b', f b a = some b' → (P b' ↔ P b))
    (h : Array.foldlM f init xs = some s) : P s ↔ P init := by
  rw [← Array.foldlM_toList] at h
  exact List.foldlM_option_invariant hstep h

/-- `PatternRewriter.insertOp` only edits the IR through its `WfRewriter.insertOp` call, which leaves
all `InBounds` facts unchanged. -/
theorem PatternRewriter.insertOp_ctx_inBounds {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {h1 h2} {ptr : GenericPtr}
    (h : PatternRewriter.insertOp b newOp ip h1 h2 = some b') :
    ptr.InBounds b'.ctx.raw ↔ ptr.InBounds b.ctx.raw := by
  unfold PatternRewriter.insertOp at h
  split at h
  · simp at h
  · rename_i newCtx hwf
    simp only [Option.some.injEq] at h
    subst h
    exact WfRewriter.insertOp_inBounds_iff hwf

/-- `PatternRewriter.replaceValue` only edits the IR through its `WfRewriter.replaceValue` call (the
worklist update leaves `.ctx` untouched), which leaves all `InBounds` facts unchanged. -/
theorem PatternRewriter.replaceValue_ctx_inBounds {b : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {ne oldIn newIn} {ptr : GenericPtr} :
    ptr.InBounds (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw ↔ ptr.InBounds b.ctx.raw := by
  unfold PatternRewriter.replaceValue
  simp only [addUsersInWorklist_same_ctx]
  exact WfRewriter.replaceValue_inBounds

/-- `PatternRewriter.eraseOp` sets `.ctx` to the total `WfRewriter.eraseOp` of the input context. -/
theorem PatternRewriter.eraseOp_ctx_eq {b b' : PatternRewriter OpCode} {op : OperationPtr}
    {r u hop} (h : PatternRewriter.eraseOp b op r u hop = some b') :
    b'.ctx = WfRewriter.eraseOp b.ctx op r u hop := by
  unfold PatternRewriter.eraseOp at h
  simp only [bind, Option.bind, Option.some.injEq] at h
  subst h
  rfl

/-! ### Keystone helpers: how the driver's insert/replace/erase folds reshape block op-lists.

These discharge the `tgtList`/`otherBlocks` fields of `RewrittenAt.of_fromLocalRewrite`. The insert
fold rewrites `block`'s list `pre ++ [op] ++ post` into `pre ++ newOps ++ [op] ++ post`, the replace
fold leaves every list untouched, and the final `eraseOp op` drops `op`, giving `pre ++ newOps ++ post`.
Every other block's list is untouched by all three stages. -/

/-- A `List.insertIdx` at the boundary index splices the new element just before the pivot. -/
private theorem List.insertIdx_mid {α} (pre l₂ : List α) (op a : α) :
    (pre ++ [op] ++ l₂).insertIdx pre.length a = pre ++ [a] ++ [op] ++ l₂ := by
  induction pre with
  | nil => simp [List.insertIdx]
  | cons hd tl ih =>
    simp only [List.cons_append, List.length_cons, List.insertIdx_succ_cons]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ih ⊢
    rw [ih]

/-- Array version of `List.insertIdx_mid`. -/
private theorem Array.insertIdx_mid {α} (pre post : Array α) (op a : α)
    (hle : pre.size ≤ (pre ++ #[op] ++ post).size) :
    (pre ++ #[op] ++ post).insertIdx pre.size a hle = pre ++ #[a] ++ #[op] ++ post := by
  apply Array.toList_inj.mp
  simp only [Array.toList_insertIdx, Array.toList_append, List.append_assoc]
  have := List.insertIdx_mid pre.toList post.toList op a
  simp only [List.append_assoc] at this
  simpa using this

/-- The index of the pivot in `pre ++ [op] ++ post` is `pre.size` when `op ∉ pre`. -/
private theorem Array.idxOf_mid {α} [BEq α] [LawfulBEq α] (pre post : Array α) (op : α)
    (h : op ∉ pre) : (pre ++ #[op] ++ post).idxOf op = pre.size := by
  rw [show pre ++ #[op] ++ post = pre ++ (#[op] ++ post) by simp]
  rw [Array.idxOf_append, Array.idxOf_append]; simp [h]

/-- Erasing the unique pivot from `pre ++ mid ++ [op] ++ post` removes exactly that occurrence. -/
private theorem Array.erase_mid {α} [BEq α] [LawfulBEq α] (pre mid post : Array α) (op : α)
    (h1 : op ∉ pre) (h2 : op ∉ mid) :
    (pre ++ mid ++ #[op] ++ post).erase op = pre ++ mid ++ post := by
  apply Array.toList_inj.mp
  have hm : op ∉ (pre ++ mid) := by simp only [Array.mem_append]; exact fun h => h.elim h1 h2
  simp only [Array.toList_erase, Array.toList_append, Array.append_assoc]
  rw [show pre.toList ++ (mid.toList ++ ([op] ++ post.toList))
        = (pre.toList ++ mid.toList) ++ ([op] ++ post.toList) by simp]
  rw [List.erase_append_right _ (by simpa using hm)]
  simp [List.erase_cons_head]

/-- `operationList` only depends on the underlying context, so equal contexts give equal lists. -/
theorem BlockPtr.operationList_congr {c₁ c₂ : WfIRContext OpInfo} (h : c₁ = c₂) {block : BlockPtr}
    (b1 : block.InBounds c₁.raw) (b2 : block.InBounds c₂.raw) :
    block.operationList c₁.raw c₁.wellFormed b1 = block.operationList c₂.raw c₂.wellFormed b2 := by
  subst h; rfl

/-- `WfRewriter.createOp` with no insertion point leaves every block's operation list unchanged. -/
theorem BlockPtr.operationList_WfRewriter_createOp_none {ctx newCtx : WfIRContext OpInfo}
    {opType : OpInfo} {resultTypes operands blockOperands regions properties}
    {h₁ h₂ h₃ h₄} {newOp : OperationPtr} {block : BlockPtr}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      none h₁ h₂ h₃ h₄ = some (newCtx, newOp))
    (blockIn : block.InBounds ctx.raw) (blockIn' : block.InBounds newCtx.raw) :
    block.operationList newCtx.raw newCtx.wellFormed blockIn' =
    block.operationList ctx.raw ctx.wellFormed blockIn := by
  simp only [WfRewriter.createOp] at h
  split at h
  · exact absurd h (by simp)
  · rename_i c op' hc
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simpa using BlockPtr.operationList_rewriter_createOp hc ctx.wellFormed

/-- A `WithCreatedOps` chain (the pattern only creates detached operations) leaves every block's
operation list unchanged. -/
theorem WfIRContext.WithCreatedOps.operationList_eq {ctx₁ ctx₂ : WfIRContext OpInfo}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂) {block : BlockPtr}
    (blockIn₁ : block.InBounds ctx₁.raw) :
    ∀ (blockIn₂ : block.InBounds ctx₂.raw),
      block.operationList ctx₂.raw ctx₂.wellFormed blockIn₂ =
      block.operationList ctx₁.raw ctx₁.wellFormed blockIn₁ := by
  induction h with
  | Nil ctx => intro blockIn₂; rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hwco hex ih =>
    intro blockIn₃
    obtain ⟨opType, resultTypes, operands, successors, regions, properties, k₁, k₂, k₃, k₄, hcreate⟩ := hex
    have hb₂ : block.InBounds ctx₂.raw := by
      have := hwco.inBounds_mono (GenericPtr.block block) (by grind); grind
    rw [BlockPtr.operationList_WfRewriter_createOp_none hcreate hb₂ blockIn₃]
    exact ih blockIn₁ hb₂

/-- The block operation list after a `WfRewriter.insertOp`: the new op is spliced into the insertion
point's block, every other block is untouched. -/
theorem BlockPtr.operationList_WfRewriter_insertOp {ctx ctx' : WfIRContext OpInfo}
    {newOp : OperationPtr} {ip : InsertPoint} {h1 h2} {block : BlockPtr}
    (h : WfRewriter.insertOp ctx newOp ip h1 h2 = some ctx')
    (blockIn : block.InBounds ctx.raw) (blockIn' : block.InBounds ctx'.raw) :
    block.operationList ctx'.raw ctx'.wellFormed blockIn' =
      if hb : ip.block! ctx.raw = some block then
        (block.operationList ctx.raw ctx.wellFormed blockIn).insertIdx
          (ip.idxIn ctx.raw block) newOp (by apply InsertPoint.idxIn.le_size_operationList)
      else block.operationList ctx.raw ctx.wellFormed blockIn := by
  simp only [WfRewriter.insertOp] at h
  split at h
  · exact absurd h (by simp)
  · rename_i c hc
    simp only [Option.pure_def, Option.some.injEq] at h
    obtain rfl := h
    exact BlockPtr.operationList_rewriter_insertOp hc ctx.wellFormed

/-- `PatternRewriter.insertOp` lift of `operationList_WfRewriter_insertOp`. -/
theorem PatternRewriter.insertOp_operationList {b b' : PatternRewriter OpInfo}
    {newOp : OperationPtr} {ip : InsertPoint} {h1 h2} {block : BlockPtr}
    (h : PatternRewriter.insertOp b newOp ip h1 h2 = some b')
    (blockIn : block.InBounds b.ctx.raw) (blockIn' : block.InBounds b'.ctx.raw) :
    block.operationList b'.ctx.raw b'.ctx.wellFormed blockIn' =
      if hb : ip.block! b.ctx.raw = some block then
        (block.operationList b.ctx.raw b.ctx.wellFormed blockIn).insertIdx
          (ip.idxIn b.ctx.raw block) newOp (by apply InsertPoint.idxIn.le_size_operationList)
      else block.operationList b.ctx.raw b.ctx.wellFormed blockIn := by
  unfold PatternRewriter.insertOp at h
  split at h
  · exact absurd h (by simp)
  · rename_i newCtx hwf
    simp only [Option.some.injEq] at h; subst h
    exact BlockPtr.operationList_WfRewriter_insertOp hwf blockIn blockIn'

/-- `PatternRewriter.insertOp` preserves the parent of every operation other than the inserted one. -/
theorem PatternRewriter.insertOp_op_parent {b b' : PatternRewriter OpInfo}
    {newOp op : OperationPtr} {ip : InsertPoint} {h1 h2}
    (h : PatternRewriter.insertOp b newOp ip h1 h2 = some b') (hne : op ≠ newOp) :
    (op.get! b'.ctx.raw).parent = (op.get! b.ctx.raw).parent := by
  unfold PatternRewriter.insertOp at h
  split at h
  · exact absurd h (by simp)
  · rename_i newCtx hwf
    simp only [Option.some.injEq] at h; subst h
    have := OperationPtr.parent!_wfRewriter_insertOp (operation := op) hwf
    simpa [hne] using this

/-- `PatternRewriter.insertOp` preserves all `InBounds` facts. -/
theorem PatternRewriter.insertOp_genericPtr_inBounds {b b' : PatternRewriter OpInfo}
    {newOp : OperationPtr} {ptr : GenericPtr} {ip : InsertPoint} {h1 h2}
    (h : PatternRewriter.insertOp b newOp ip h1 h2 = some b') :
    ptr.InBounds b'.ctx.raw ↔ ptr.InBounds b.ctx.raw := by
  unfold PatternRewriter.insertOp at h
  split at h
  · exact absurd h (by simp)
  · rename_i newCtx hwf
    simp only [Option.some.injEq] at h; subst h
    exact WfRewriter.insertOp_inBounds_iff hwf

/-- `WfRewriter.replaceValue` only redirects operands, leaving every block's operation list intact. -/
theorem BlockPtr.operationList_WfRewriter_replaceValue {ctx : WfIRContext OpInfo}
    {oldValue newValue : ValuePtr} {ne : oldValue ≠ newValue}
    {oldIn : oldValue.InBounds ctx.raw} {newIn : newValue.InBounds ctx.raw}
    {block : BlockPtr} (blockIn : block.InBounds ctx.raw)
    (blockIn' : block.InBounds (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw) :
    block.operationList (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw
        (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).wellFormed blockIn' =
    block.operationList ctx.raw ctx.wellFormed blockIn := by
  have hchain : BlockPtr.OpChain block
      (WfRewriter.replaceValue ctx oldValue newValue ne oldIn newIn).raw
      (block.operationList ctx.raw ctx.wellFormed blockIn) := by
    apply BlockPtr.OpChain_unchanged
      (BlockPtr.operationListWF ctx.raw block blockIn ctx.wellFormed) blockIn'
    · grind
    · grind
    · intro opPtr hop hpar; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind
    · intro opPtr hop hpar; refine ⟨?_, ?_⟩ <;> grind
  grind

/-- `PatternRewriter.replaceValue` lift of `operationList_WfRewriter_replaceValue`. -/
theorem PatternRewriter.replaceValue_operationList {b : PatternRewriter OpInfo}
    {oldVal newVal : ValuePtr} {ne oldIn newIn} {block : BlockPtr}
    (blockIn : block.InBounds b.ctx.raw)
    (blockIn' : block.InBounds (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw) :
    block.operationList (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw
        (b.replaceValue oldVal newVal ne oldIn newIn).ctx.wellFormed blockIn' =
    block.operationList b.ctx.raw b.ctx.wellFormed blockIn := by
  have hctx : (b.replaceValue oldVal newVal ne oldIn newIn).ctx
      = WfRewriter.replaceValue b.ctx oldVal newVal ne oldIn newIn := by
    simp only [PatternRewriter.replaceValue, PatternRewriter.addUsersInWorklist_same_ctx]
  revert blockIn'
  rw [hctx]
  intro blockIn'
  exact BlockPtr.operationList_WfRewriter_replaceValue blockIn _

/-- `PatternRewriter.replaceValue` preserves all `InBounds` facts. -/
theorem PatternRewriter.replaceValue_genericPtr_inBounds {b : PatternRewriter OpInfo}
    {oldVal newVal : ValuePtr} {ne oldIn newIn} {ptr : GenericPtr} :
    ptr.InBounds (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw ↔ ptr.InBounds b.ctx.raw := by
  have hctx : (b.replaceValue oldVal newVal ne oldIn newIn).ctx
      = WfRewriter.replaceValue b.ctx oldVal newVal ne oldIn newIn := by
    simp only [PatternRewriter.replaceValue, PatternRewriter.addUsersInWorklist_same_ctx]
  rw [hctx]; exact WfRewriter.replaceValue_inBounds

/-- `PatternRewriter.replaceValue` preserves block in-boundedness (the `BlockPtr`-headed form, so it
unifies against goals where the replace proofs are opaque). -/
theorem PatternRewriter.replaceValue_blockPtr_inBounds {b : PatternRewriter OpInfo}
    {oldVal newVal : ValuePtr} {ne oldIn newIn} {block : BlockPtr} :
    block.InBounds (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw ↔ block.InBounds b.ctx.raw := by
  have := PatternRewriter.replaceValue_genericPtr_inBounds (b := b) (oldVal := oldVal)
    (newVal := newVal) (ne := ne) (oldIn := oldIn) (newIn := newIn) (ptr := GenericPtr.block block)
  grind

/-- The block operation list after a `WfRewriter.eraseOp`: the erased op is dropped from its parent
block, every other block is untouched. -/
theorem BlockPtr.operationList_WfRewriter_eraseOp {ctx : WfIRContext OpInfo} {op : OperationPtr}
    {hr hu ho} {block : BlockPtr}
    (blockIn : block.InBounds ctx.raw)
    (blockIn' : block.InBounds (WfRewriter.eraseOp ctx op hr hu ho).raw) :
    block.operationList (WfRewriter.eraseOp ctx op hr hu ho).raw
        (WfRewriter.eraseOp ctx op hr hu ho).wellFormed blockIn'
      = if (op.get! ctx.raw).parent = block then
          (block.operationList ctx.raw ctx.wellFormed blockIn).erase op
        else block.operationList ctx.raw ctx.wellFormed blockIn := by
  simp only [WfRewriter.eraseOp]
  exact BlockPtr.operationList_rewriter_eraseOp ctx.wellFormed

/-- Folding `insertOp · (before op)` over a list of fresh ops splices them, in order, just before
`op` inside `op`'s block, leaving `op`'s membership/parent intact. -/
theorem PatternRewriter.foldlM_insertOp_before_opList
    {op : OperationPtr} {block : BlockPtr}
    {f : PatternRewriter OpInfo → OperationPtr → Option (PatternRewriter OpInfo)}
    (hf : ∀ b a b', f b a = some b' →
       ∃ (k1 : a.InBounds b.ctx.raw) (k2 : (InsertPoint.before op).InBounds b.ctx.raw),
         PatternRewriter.insertOp b a (InsertPoint.before op) k1 k2 = some b') :
    ∀ {l : List OperationPtr} {init s : PatternRewriter OpInfo} {pre post : Array OperationPtr},
    op.InBounds init.ctx.raw →
    List.foldlM f init l = some s →
    (op.get! init.ctx.raw).parent = some block →
    (∀ (hb : block.InBounds init.ctx.raw),
      block.operationList init.ctx.raw init.ctx.wellFormed hb = pre ++ #[op] ++ post) →
    op ∉ pre → op ∉ post → op ∉ l →
    op.InBounds s.ctx.raw ∧
    (op.get! s.ctx.raw).parent = some block ∧
    (∀ (hb : block.InBounds s.ctx.raw),
      block.operationList s.ctx.raw s.ctx.wellFormed hb = pre ++ l.toArray ++ #[op] ++ post) := by
  intro l
  induction l with
  | nil =>
    intro init s pre post hinit hfold hpar hlist _ _ _
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hfold
    subst hfold
    exact ⟨hinit, hpar, by intro hb; simpa using hlist hb⟩
  | cons a t ih =>
    intro init s pre post hinit hfold hpar hlist hpre hpost hnotmem
    rw [List.foldlM_cons] at hfold
    obtain ⟨b, hfa, htail⟩ := Option.bind_eq_some_iff.mp hfold
    obtain ⟨k1, k2, hins⟩ := hf init a b hfa
    have hblockInit : block.InBounds init.ctx.raw := by
      have := init.ctx.wellFormed.inBounds; grind
    have hane : op ≠ a := by intro h; subst h; exact hnotmem (by simp)
    have hopB : op.InBounds b.ctx.raw := by
      have := PatternRewriter.insertOp_genericPtr_inBounds (ptr := GenericPtr.operation op) hins
      grind
    have hparB : (op.get! b.ctx.raw).parent = some block := by
      rw [PatternRewriter.insertOp_op_parent hins hane]; exact hpar
    have hipblock : (InsertPoint.before op).block! init.ctx.raw = some block := by
      rw [InsertPoint.block!_before_eq]; exact hpar
    have hlistB : ∀ (hb : block.InBounds b.ctx.raw),
        block.operationList b.ctx.raw b.ctx.wellFormed hb = (pre ++ #[a]) ++ #[op] ++ post := by
      intro hb
      rw [PatternRewriter.insertOp_operationList hins hblockInit hb, dif_pos hipblock]
      simp only [InsertPoint.idxIn_before_eq, hlist hblockInit, Array.idxOf_mid pre post op hpre]
      exact Array.insertIdx_mid pre post op a _
    have hpre' : op ∉ pre ++ #[a] := by
      simp only [Array.mem_append, Array.mem_singleton]
      exact fun h => h.elim hpre (fun h => hane h)
    have hnotmemt : op ∉ t := fun h => hnotmem (List.mem_cons_of_mem a h)
    obtain ⟨hs, hsp, hsl⟩ := ih hopB htail hparB hlistB hpre' hpost hnotmemt
    refine ⟨hs, hsp, ?_⟩
    intro hb
    rw [hsl hb, show (a :: t).toArray = #[a] ++ t.toArray from List.toArray_cons a t]
    simp only [Array.append_assoc]

/-- A fold that preserves `c`'s operation list (and `c`'s in-boundedness) at every step preserves it
overall. -/
theorem PatternRewriter.foldlM_preserves_opList {α} {c : BlockPtr}
    {f : PatternRewriter OpInfo → α → Option (PatternRewriter OpInfo)}
    (hstep : ∀ b a b', f b a = some b' →
        (c.InBounds b.ctx.raw → c.InBounds b'.ctx.raw) ∧
        (∀ (hc : c.InBounds b.ctx.raw) (hc' : c.InBounds b'.ctx.raw),
          c.operationList b'.ctx.raw b'.ctx.wellFormed hc'
            = c.operationList b.ctx.raw b.ctx.wellFormed hc)) :
    ∀ {l : List α} {init s : PatternRewriter OpInfo},
    List.foldlM f init l = some s →
    ∀ (hc : c.InBounds init.ctx.raw) (hc' : c.InBounds s.ctx.raw),
      c.operationList s.ctx.raw s.ctx.wellFormed hc'
        = c.operationList init.ctx.raw init.ctx.wellFormed hc := by
  intro l
  induction l with
  | nil =>
    intro init s hfold hc hc'
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hfold
    subst hfold; rfl
  | cons a t ih =>
    intro init s hfold hc hc'
    rw [List.foldlM_cons] at hfold
    obtain ⟨b, hfa, htail⟩ := Option.bind_eq_some_iff.mp hfold
    obtain ⟨hinb, hop⟩ := hstep init a b hfa
    have hcb : c.InBounds b.ctx.raw := hinb hc
    rw [ih htail hcb hc', hop hc hcb]

/-- Folding `insertOp · (before op)` leaves every block other than `op`'s parent untouched. -/
theorem PatternRewriter.foldlM_insertOp_before_other
    {op : OperationPtr} {block c : BlockPtr} (hcb : c ≠ block)
    {f : PatternRewriter OpInfo → OperationPtr → Option (PatternRewriter OpInfo)}
    (hf : ∀ b a b', f b a = some b' →
       ∃ (k1 : a.InBounds b.ctx.raw) (k2 : (InsertPoint.before op).InBounds b.ctx.raw),
         PatternRewriter.insertOp b a (InsertPoint.before op) k1 k2 = some b') :
    ∀ {l : List OperationPtr} {init s : PatternRewriter OpInfo},
    op.InBounds init.ctx.raw →
    (op.get! init.ctx.raw).parent = some block →
    List.foldlM f init l = some s →
    op ∉ l →
    ∀ (hc : c.InBounds init.ctx.raw) (hc' : c.InBounds s.ctx.raw),
      c.operationList s.ctx.raw s.ctx.wellFormed hc'
        = c.operationList init.ctx.raw init.ctx.wellFormed hc := by
  intro l
  induction l with
  | nil =>
    intro init s hinit hpar hfold _ hc hc'
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hfold
    subst hfold; rfl
  | cons a t ih =>
    intro init s hinit hpar hfold hnotmem hc hc'
    rw [List.foldlM_cons] at hfold
    obtain ⟨b, hfa, htail⟩ := Option.bind_eq_some_iff.mp hfold
    obtain ⟨k1, k2, hins⟩ := hf init a b hfa
    have hane : op ≠ a := by intro h; subst h; exact hnotmem (by simp)
    have hcInB : c.InBounds b.ctx.raw := by
      have := PatternRewriter.insertOp_genericPtr_inBounds (ptr := GenericPtr.block c) hins
      grind
    have hopB : op.InBounds b.ctx.raw := by
      have := PatternRewriter.insertOp_genericPtr_inBounds (ptr := GenericPtr.operation op) hins
      grind
    have hparB : (op.get! b.ctx.raw).parent = some block := by
      rw [PatternRewriter.insertOp_op_parent hins hane]; exact hpar
    have hstep : c.operationList b.ctx.raw b.ctx.wellFormed hcInB
        = c.operationList init.ctx.raw init.ctx.wellFormed hc := by
      rw [PatternRewriter.insertOp_operationList hins hc hcInB, dif_neg ?_]
      rw [InsertPoint.block!_before_eq, hpar]
      simp only [Option.some.injEq]
      exact fun h => hcb h.symm
    rw [ih hopB hparB htail (fun h => hnotmem (List.mem_cons_of_mem a h)) hcInB hc', hstep]

/-! ### Keystone helpers: how the driver's pipeline frames a *survivor's* intrinsic data.

These discharge the `frame` field of `RewrittenAt.of_fromLocalRewrite`. For an operation `o ≠ op` the
driver leaves its op type, properties, result count, successors and result types untouched at every
stage (created ops, insert fold, replace fold, erase); only its operands are rewritten, and exactly by
the result→`newValues` redirect, which equals the value renaming `σ`. -/

/-- `createEmptyOp` leaves a pre-existing operation's properties (at every op code) untouched: it only
`set`s the fresh `newOp`'s record. The shipped `getProperties!_createEmptyOp` is code-specific. -/
theorem OperationPtr.getProperties!_createEmptyOp_ne {ctx ctx' : IRContext OpCode}
    {opType : OpCode} {properties : HasOpInfo.propertiesOf opType} {newOp operation : OperationPtr}
    {oc : OpCode}
    (h : Rewriter.createEmptyOp ctx opType properties = some (ctx', newOp))
    (hne : operation ≠ newOp) :
    operation.getProperties! ctx' oc = operation.getProperties! ctx oc := by
  simp only [Rewriter.createEmptyOp, OperationPtr.allocEmpty] at h
  grind [OperationPtr.getProperties!, OperationPtr.set, OperationPtr.get!]

/-- A `WfRewriter.createOp` leaves a pre-existing operation's properties (at every op code) untouched:
only the fresh `newOp` gets properties, and the init steps touch only results/regions/operands. The
code-specific `getProperties!_WfRewriter_createOp` covers only the created op's own type. -/
theorem OperationPtr.getProperties!_WfRewriter_createOp_ne {ctx ctx' : WfIRContext OpCode}
    {opType : OpCode} {resultTypes operands blockOperands regions properties h₁ h₂ h₃ h₄}
    {newOp operation : OperationPtr} {oc : OpCode}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties
      none h₁ h₂ h₃ h₄ = some (ctx', newOp))
    (hne : operation ≠ newOp) :
    operation.getProperties! ctx'.raw oc = operation.getProperties! ctx.raw oc := by
  simp only [WfRewriter.createOp] at h
  grind [Rewriter.createOp, OperationPtr.getProperties!_createEmptyOp_ne,
    OperationPtr.getProperties!_initOpRegions]

/-- Intrinsic operation data the rewrite driver leaves untouched for a *surviving* operation `o`: its
op type, properties (at every op code), result count, successors and result types. Operands are
deliberately excluded — the redirect fold rewrites them. Packaged as a single `Prop` so the driver's
folds can thread it through `Array.foldlM_option_invariant` in one shot. -/
def OperationPtr.SameIntrinsic (o : OperationPtr) (c c' : IRContext OpCode) : Prop :=
  o.getOpType! c' = o.getOpType! c ∧
  (∀ ot, o.getProperties! c' ot = o.getProperties! c ot) ∧
  o.getNumResults! c' = o.getNumResults! c ∧
  o.getSuccessors! c' = o.getSuccessors! c ∧
  o.getResultTypes! c' = o.getResultTypes! c

@[refl]
theorem OperationPtr.SameIntrinsic.rfl {o : OperationPtr} {c : IRContext OpCode} :
    o.SameIntrinsic c c := ⟨_root_.rfl, fun _ => _root_.rfl, _root_.rfl, _root_.rfl, _root_.rfl⟩

theorem OperationPtr.SameIntrinsic.symm {o : OperationPtr} {c c' : IRContext OpCode}
    (h : o.SameIntrinsic c c') : o.SameIntrinsic c' c :=
  ⟨h.1.symm, fun ot => (h.2.1 ot).symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

theorem OperationPtr.SameIntrinsic.trans {o : OperationPtr} {c c' c'' : IRContext OpCode}
    (h : o.SameIntrinsic c c') (h' : o.SameIntrinsic c' c'') : o.SameIntrinsic c c'' :=
  ⟨h'.1.trans h.1, fun ot => (h'.2.1 ot).trans (h.2.1 ot), h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1, h'.2.2.2.2.trans h.2.2.2.2⟩

/-- `PatternRewriter.insertOp` frames a survivor's intrinsic data (it only links a fresh op). -/
theorem PatternRewriter.insertOp_sameIntrinsic {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {h1 h2} {o : OperationPtr}
    (h : PatternRewriter.insertOp b newOp ip h1 h2 = some b') :
    o.SameIntrinsic b.ctx.raw b'.ctx.raw := by
  unfold PatternRewriter.insertOp at h
  split at h
  · simp at h
  · rename_i newCtx hwf
    simp only [Option.some.injEq] at h; subst h
    exact ⟨OperationPtr.getOpType!_wfRewriter_insertOp hwf,
      fun _ => OperationPtr.getProperties!_wfRewriter_insertOp hwf,
      OperationPtr.getNumResults!_wfRewriter_insertOp hwf,
      OperationPtr.getSuccessors!_wfRewriter_insertOp hwf,
      OperationPtr.getResultTypes!_wfRewriter_insertOp hwf⟩

/-- `PatternRewriter.insertOp` frames a survivor's operands. -/
theorem PatternRewriter.insertOp_getOperands {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {h1 h2} {o : OperationPtr}
    (h : PatternRewriter.insertOp b newOp ip h1 h2 = some b') :
    o.getOperands! b'.ctx.raw = o.getOperands! b.ctx.raw := by
  unfold PatternRewriter.insertOp at h
  split at h
  · simp at h
  · rename_i newCtx hwf
    simp only [Option.some.injEq] at h; subst h
    exact OperationPtr.getOperands!_wfRewriter_insertOp hwf

/-- `PatternRewriter.insertOp` leaves every operation's region count unchanged. -/
theorem PatternRewriter.insertOp_getNumRegions {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {h1 h2} {o : OperationPtr}
    (h : PatternRewriter.insertOp b newOp ip h1 h2 = some b') :
    o.getNumRegions! b'.ctx.raw = o.getNumRegions! b.ctx.raw := by
  unfold PatternRewriter.insertOp at h
  split at h
  · simp at h
  · rename_i newCtx hwf
    simp only [Option.some.injEq] at h; subst h
    exact OperationPtr.getNumRegions!_wfRewriter_insertOp hwf

/-- `PatternRewriter.insertOp` leaves every operation's region pointers unchanged. -/
theorem PatternRewriter.insertOp_getRegion {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {h1 h2} {o : OperationPtr} {idx : Nat}
    (h : PatternRewriter.insertOp b newOp ip h1 h2 = some b') :
    o.getRegion! b'.ctx.raw idx = o.getRegion! b.ctx.raw idx := by
  unfold PatternRewriter.insertOp at h
  split at h
  · simp at h
  · rename_i newCtx hwf
    simp only [Option.some.injEq] at h; subst h
    exact OperationPtr.getRegion!_wfRewriter_insertOp hwf

/-- `PatternRewriter.insertOp` leaves every region's entry block unchanged. -/
theorem PatternRewriter.insertOp_firstBlock {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {h1 h2} {r : RegionPtr}
    (h : PatternRewriter.insertOp b newOp ip h1 h2 = some b') :
    (r.get! b'.ctx.raw).firstBlock = (r.get! b.ctx.raw).firstBlock := by
  unfold PatternRewriter.insertOp at h
  split at h
  · simp at h
  · rename_i newCtx hwf
    simp only [Option.some.injEq] at h; subst h
    exact RegionPtr.firstBlock!_wfRewriter_insertOp hwf

/-- `PatternRewriter.replaceValue` frames every operation's intrinsic data (it only redirects
operands). -/
theorem PatternRewriter.replaceValue_sameIntrinsic {b : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {ne oldIn newIn} {o : OperationPtr} :
    o.SameIntrinsic b.ctx.raw (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw := by
  have hctx : (b.replaceValue oldVal newVal ne oldIn newIn).ctx
      = WfRewriter.replaceValue b.ctx oldVal newVal ne oldIn newIn := by
    simp only [PatternRewriter.replaceValue, PatternRewriter.addUsersInWorklist_same_ctx]
  rw [hctx]
  exact ⟨OperationPtr.getOpType!_WfRewriter_replaceValue,
    fun _ => OperationPtr.getProperties!_WfRewriter_replaceValue,
    OperationPtr.getNumResults!_WfRewriter_replaceValue,
    OperationPtr.getSuccessors!_WfRewriter_replaceValue,
    OperationPtr.getResultTypes!_WfRewriter_replaceValue⟩

/-- `PatternRewriter.replaceValue` rewrites a survivor's operands by the single-value redirect. -/
theorem PatternRewriter.replaceValue_getOperands {b : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {ne oldIn newIn} {o : OperationPtr} (hin : o.InBounds b.ctx.raw) :
    o.getOperands! (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw =
    (o.getOperands! b.ctx.raw).map (fun v => if v = oldVal then newVal else v) := by
  have hctx : (b.replaceValue oldVal newVal ne oldIn newIn).ctx
      = WfRewriter.replaceValue b.ctx oldVal newVal ne oldIn newIn := by
    simp only [PatternRewriter.replaceValue, PatternRewriter.addUsersInWorklist_same_ctx]
  rw [hctx]
  exact OperationPtr.getOperands!_WfRewriter_replaceValue hin

/-- `PatternRewriter.replaceValue` leaves every operation's region count unchanged. -/
theorem PatternRewriter.replaceValue_getNumRegions {b : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {ne oldIn newIn} {o : OperationPtr} :
    o.getNumRegions! (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw =
    o.getNumRegions! b.ctx.raw := by
  have hctx : (b.replaceValue oldVal newVal ne oldIn newIn).ctx
      = WfRewriter.replaceValue b.ctx oldVal newVal ne oldIn newIn := by
    simp only [PatternRewriter.replaceValue, PatternRewriter.addUsersInWorklist_same_ctx]
  rw [hctx]; exact OperationPtr.getNumRegions!_WfRewriter_replaceValue

/-- `PatternRewriter.replaceValue` leaves every operation's region pointers unchanged. -/
theorem PatternRewriter.replaceValue_getRegion {b : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {ne oldIn newIn} {o : OperationPtr} {idx : Nat} :
    o.getRegion! (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw idx =
    o.getRegion! b.ctx.raw idx := by
  have hctx : (b.replaceValue oldVal newVal ne oldIn newIn).ctx
      = WfRewriter.replaceValue b.ctx oldVal newVal ne oldIn newIn := by
    simp only [PatternRewriter.replaceValue, PatternRewriter.addUsersInWorklist_same_ctx]
  rw [hctx]; exact OperationPtr.getRegion!_WfRewriter_replaceValue

/-- `PatternRewriter.replaceValue` leaves every region's entry block unchanged. -/
theorem PatternRewriter.replaceValue_firstBlock {b : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {ne oldIn newIn} {r : RegionPtr} :
    (r.get! (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw).firstBlock =
    (r.get! b.ctx.raw).firstBlock := by
  have hctx : (b.replaceValue oldVal newVal ne oldIn newIn).ctx
      = WfRewriter.replaceValue b.ctx oldVal newVal ne oldIn newIn := by
    simp only [PatternRewriter.replaceValue, PatternRewriter.addUsersInWorklist_same_ctx]
  rw [hctx]; exact RegionPtr.firstBlock!_WfRewriter_replaceValue

/-- An operation's region list is determined by its region count and region pointers, so equal counts
plus equal pointers (at every index) give equal region lists across two contexts. -/
theorem OperationPtr.regions_eq_of {o : OperationPtr} {ctx ctx' : IRContext OpCode}
    (hsize : o.getNumRegions! ctx = o.getNumRegions! ctx')
    (helem : ∀ idx, o.getRegion! ctx idx = o.getRegion! ctx' idx) :
    (o.get! ctx).regions = (o.get! ctx').regions := by
  apply Array.ext
  · simpa only [OperationPtr.getNumRegions!] using hsize
  · intro i hi hi'
    have h := helem i
    simp only [OperationPtr.getRegion!] at h
    rwa [getElem!_pos _ i hi, getElem!_pos _ i hi'] at h

/-- A `WithCreatedOps` chain frames a survivor's intrinsic data (it only creates fresh ops). -/
theorem WfIRContext.WithCreatedOps.sameIntrinsic {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂) {o : OperationPtr} (oIn : o.InBounds ctx₁.raw) :
    o.SameIntrinsic ctx₁.raw ctx₂.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hwco hex ih =>
    obtain ⟨opType, rt, ops, succ, regs, props, k₁, k₂, k₃, k₄, hcreate⟩ := hex
    have ho2 : o.InBounds ctx₂.raw := by
      have := hwco.inBounds_mono (GenericPtr.operation o) (by grind); grind
    have hstep : o.SameIntrinsic ctx₂.raw ctx₃.raw := by
      refine ⟨by grind, fun ot => ?_, by grind, by grind, by grind⟩
      exact OperationPtr.getProperties!_WfRewriter_createOp_ne hcreate (by grind)
    exact (ih oIn).trans hstep

/-- A `WithCreatedOps` chain frames a survivor's operands (it only creates fresh ops). -/
theorem WfIRContext.WithCreatedOps.getOperands_eq {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂) {o : OperationPtr} (oIn : o.InBounds ctx₁.raw) :
    o.getOperands! ctx₂.raw = o.getOperands! ctx₁.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hwco hex ih =>
    obtain ⟨opType, rt, ops, succ, regs, props, k₁, k₂, k₃, k₄, hcreate⟩ := hex
    have ho2 : o.InBounds ctx₂.raw := by
      have := hwco.inBounds_mono (GenericPtr.operation o) (by grind); grind
    rw [OperationPtr.getOperands!_WfRewriter_createOp hcreate, if_neg (by grind)]
    exact ih oIn

/-- A `WithCreatedOps` chain frames a survivor's region count (it only creates fresh ops). -/
theorem WfIRContext.WithCreatedOps.getNumRegions_eq {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂) {o : OperationPtr} (oIn : o.InBounds ctx₁.raw) :
    o.getNumRegions! ctx₂.raw = o.getNumRegions! ctx₁.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hwco hex ih =>
    obtain ⟨opType, rt, ops, succ, regs, props, k₁, k₂, k₃, k₄, hcreate⟩ := hex
    have ho2 : o.InBounds ctx₂.raw := by
      have := hwco.inBounds_mono (GenericPtr.operation o) (by grind); grind
    rw [OperationPtr.getNumRegions!_WfRewriter_createOp hcreate, if_neg (by grind)]
    exact ih oIn

/-- A `WithCreatedOps` chain frames a survivor's region pointers (it only creates fresh ops). -/
theorem WfIRContext.WithCreatedOps.getRegion_eq {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂) {o : OperationPtr} (oIn : o.InBounds ctx₁.raw)
    (idx : Nat) :
    o.getRegion! ctx₂.raw idx = o.getRegion! ctx₁.raw idx := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hwco hex ih =>
    obtain ⟨opType, rt, ops, succ, regs, props, k₁, k₂, k₃, k₄, hcreate⟩ := hex
    have ho2 : o.InBounds ctx₂.raw := by
      have := hwco.inBounds_mono (GenericPtr.operation o) (by grind); grind
    rw [OperationPtr.getRegion!_WfRewriter_createOp hcreate, dif_neg (by grind)]
    exact ih oIn

/-- A `WithCreatedOps` chain frames every region's entry block (it only creates fresh ops). -/
theorem WfIRContext.WithCreatedOps.firstBlock_eq {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂) {r : RegionPtr} :
    (r.get! ctx₂.raw).firstBlock = (r.get! ctx₁.raw).firstBlock := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hwco hex ih =>
    obtain ⟨opType, rt, ops, succ, regs, props, k₁, k₂, k₃, k₄, hcreate⟩ := hex
    rw [RegionPtr.firstBlock!_WfRewriter_createOp hcreate]
    exact ih

/-! ### Block-argument count/type frame across the rewrite stages.

The rewrite never adds, removes, or retypes block arguments (it only edits operation lists and
def-use chains). The lemmas below lift the per-primitive `getNumArguments!`/`getType!` frame facts to
the `PatternRewriter` insert/replace folds and to `WithCreatedOps`; they discharge the
`blockNumArgsPreserved`/`blockArgTypesPreserved` fields of `RewrittenAt.of_fromLocalRewrite`. -/

/-- `PatternRewriter.insertOp` leaves every block's argument count unchanged. -/
theorem PatternRewriter.insertOp_getNumArguments {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {h1 h2} {bl : BlockPtr}
    (h : PatternRewriter.insertOp b newOp ip h1 h2 = some b') :
    bl.getNumArguments! b'.ctx.raw = bl.getNumArguments! b.ctx.raw := by
  unfold PatternRewriter.insertOp at h
  split at h
  · simp at h
  · rename_i newCtx hwf
    simp only [Option.some.injEq] at h; subst h
    exact BlockPtr.getNumArguments!_wfRewriter_insertOp hwf

/-- `PatternRewriter.insertOp` leaves every value's type unchanged. -/
theorem PatternRewriter.insertOp_getType {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {h1 h2} {v : ValuePtr}
    (h : PatternRewriter.insertOp b newOp ip h1 h2 = some b') :
    v.getType! b'.ctx.raw = v.getType! b.ctx.raw := by
  unfold PatternRewriter.insertOp at h
  split at h
  · simp at h
  · rename_i newCtx hwf
    simp only [Option.some.injEq] at h; subst h
    exact ValuePtr.getType!_wfRewriter_insertOp hwf

/-- `PatternRewriter.replaceValue` leaves every block's argument count unchanged. -/
theorem PatternRewriter.replaceValue_getNumArguments {b : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {ne oldIn newIn} {bl : BlockPtr} :
    bl.getNumArguments! (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw =
    bl.getNumArguments! b.ctx.raw := by
  have hctx : (b.replaceValue oldVal newVal ne oldIn newIn).ctx
      = WfRewriter.replaceValue b.ctx oldVal newVal ne oldIn newIn := by
    simp only [PatternRewriter.replaceValue, PatternRewriter.addUsersInWorklist_same_ctx]
  rw [hctx]; exact BlockPtr.getNumArguments!_WfRewriter_replaceValue

/-- `PatternRewriter.replaceValue` leaves every value's type unchanged. -/
theorem PatternRewriter.replaceValue_getType {b : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {ne oldIn newIn} {v : ValuePtr} :
    v.getType! (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw =
    v.getType! b.ctx.raw := by
  have hctx : (b.replaceValue oldVal newVal ne oldIn newIn).ctx
      = WfRewriter.replaceValue b.ctx oldVal newVal ne oldIn newIn := by
    simp only [PatternRewriter.replaceValue, PatternRewriter.addUsersInWorklist_same_ctx]
  rw [hctx]; exact ValuePtr.getType!_WfRewriter_replaceValue

/-- A `WithCreatedOps` chain leaves every block's argument count unchanged (it only creates fresh
ops). -/
theorem WfIRContext.WithCreatedOps.getNumArguments_eq {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂) (bl : BlockPtr) :
    bl.getNumArguments! ctx₂.raw = bl.getNumArguments! ctx₁.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hwco hex ih =>
    obtain ⟨opType, rt, ops, succ, regs, props, k₁, k₂, k₃, k₄, hcreate⟩ := hex
    rw [BlockPtr.getNumArguments!_WfRewriter_createOp hcreate]; exact ih

/-- A `WithCreatedOps` chain leaves every block argument's type unchanged: creating a fresh op only
fixes the types of that op's own (`opResult`) values, never any block argument. -/
theorem WfIRContext.WithCreatedOps.getType_blockArgument_eq {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂) (ba : BlockArgumentPtr) :
    (ValuePtr.blockArgument ba).getType! ctx₂.raw = (ValuePtr.blockArgument ba).getType! ctx₁.raw := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hwco hex ih =>
    obtain ⟨opType, rt, ops, succ, regs, props, k₁, k₂, k₃, k₄, hcreate⟩ := hex
    rw [ValuePtr.getType!_WfRewriter_createOp hcreate]; exact ih

/-- Fuse a left-fold of array `map`s into one `map` of left-folds. -/
theorem List.foldl_arrayMap_fusion {α β : Type} (l : List β) (g : β → α → α) (arr : Array α) :
    l.foldl (fun a b => a.map (fun x => g b x)) arr
      = arr.map (fun x => l.foldl (fun acc b => g b acc) x) := by
  induction l generalizing arr with
  | nil => simp
  | cons b t ih => simp only [List.foldl_cons, ih, Array.map_map, Function.comp_def]

/-- The result→`newValues` redirect fold, applied to a value that is *not* one of `op`'s results, is
the identity: no step's `oldVal` (an `op` result) ever matches. -/
theorem fold_replaceResult_eq_self (op : OperationPtr) :
    ∀ (l : List (ValuePtr × Nat)) (v : ValuePtr),
    (∀ q ∈ l, v ≠ (op.getResult q.2 : ValuePtr)) →
    l.foldl (fun acc q => if acc = (op.getResult q.2 : ValuePtr) then q.1 else acc) v = v := by
  intro l
  induction l with
  | nil => intro v _; rfl
  | cons q t ih =>
    intro v h
    rw [List.foldl_cons, if_neg (h q (by simp))]
    exact ih v (fun q' hq' => h q' (by simp [hq']))

/-- The redirect fold over `newValues.zipIdx`, applied to `op`'s `(start+k)`-th result, lands on
`newValues[k]`: every earlier step targets a different result so leaves it; the matching step sends it
to `newValues[k]`; later steps cannot touch `newValues[k]`, which is not an `op` result. -/
theorem fold_replaceResult_zipIdx_hit (op : OperationPtr) :
    ∀ (vs : List ValuePtr) (start k : Nat) (hk : k < vs.length),
    (∀ x ∈ vs, ∀ m, x ≠ (op.getResult m : ValuePtr)) →
    (vs.zipIdx start).foldl
        (fun acc q => if acc = (op.getResult q.2 : ValuePtr) then q.1 else acc)
        (op.getResult (start + k) : ValuePtr) = vs[k] := by
  intro vs
  induction vs with
  | nil => intro start k hk _; simp at hk
  | cons a t ih =>
    intro start k hk hrepl
    rw [List.zipIdx_cons, List.foldl_cons]
    match k with
    | 0 =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      exact fold_replaceResult_eq_self op (t.zipIdx (start + 1)) a
        (fun q hq => hrepl a (by simp) q.2)
    | k' + 1 =>
      have hne : (op.getResult (start + (k' + 1)) : ValuePtr) ≠ (op.getResult start : ValuePtr) := by
        simp only [OperationPtr.getResult, ne_eq, ValuePtr.opResult.injEq,
          OpResultPtr.mk.injEq, true_and]
        omega
      rw [if_neg hne, show start + (k' + 1) = (start + 1) + k' by omega,
        List.getElem_cons_succ]
      exact ih (start + 1) k' (by simpa using hk) (fun x hx m => hrepl x (by simp [hx]) m)

/-- The driver's redirect fold (`foldlM` of `replaceValue (op.getResult i) newValues[i]` over
`newValues.zipIdx`) rewrites a survivor's operand array by mapping each operand through the
single-result redirect, composed left-to-right. -/
theorem PatternRewriter.foldlM_replaceValue_getOperands {op o : OperationPtr}
    {f : PatternRewriter OpCode → (ValuePtr × Nat) → Option (PatternRewriter OpCode)}
    (hf : ∀ b q b', f b q = some b' →
        ∃ ne oldIn newIn, b.replaceValue (op.getResult q.2 : ValuePtr) q.1 ne oldIn newIn = b') :
    ∀ {l : List (ValuePtr × Nat)} {init s : PatternRewriter OpCode},
    List.foldlM f init l = some s → o.InBounds init.ctx.raw →
    o.getOperands! s.ctx.raw =
      l.foldl (fun arr q => arr.map (fun v => if v = (op.getResult q.2 : ValuePtr) then q.1 else v))
        (o.getOperands! init.ctx.raw) := by
  intro l
  induction l with
  | nil =>
    intro init s hfold _
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hfold
    subst hfold; rfl
  | cons q t ih =>
    intro init s hfold hin
    rw [List.foldlM_cons] at hfold
    obtain ⟨b, hfb, htail⟩ := Option.bind_eq_some_iff.mp hfold
    obtain ⟨ne, oldIn, newIn, hb⟩ := hf init q b hfb
    have hinb : o.InBounds b.ctx.raw := by
      rw [← hb]
      have h := PatternRewriter.replaceValue_genericPtr_inBounds (b := init)
        (oldVal := (op.getResult q.2 : ValuePtr)) (newVal := q.1) (ne := ne) (oldIn := oldIn)
        (newIn := newIn) (ptr := GenericPtr.operation o)
      grind
    have hstep : o.getOperands! b.ctx.raw
        = (o.getOperands! init.ctx.raw).map
            (fun v => if v = (op.getResult q.2 : ValuePtr) then q.1 else v) := by
      rw [← hb]; exact PatternRewriter.replaceValue_getOperands hin
    rw [List.foldl_cons, ih htail hinb, hstep]

/-- The driver's redirect fold over `newValues.zipIdx` realizes the value renaming `σ` pointwise: a
value that is one of `op`'s results `i` goes to `newValues[i]`, anything else is fixed. Requires that
no `newValue` is itself an `op` result (`hNoAlias`) so the sequential fold cannot chain redirects. -/
theorem fold_replaceResult_zipIdx_eq_sigma {ctx : WfIRContext OpCode}
    (op : OperationPtr) (newValues : Array ValuePtr)
    (hsize : newValues.size = op.getNumResults! ctx.raw)
    (hNoAlias : ∀ x ∈ newValues, ∀ m, x ≠ (op.getResult m : ValuePtr))
    (v : ValuePtr) :
    (newValues.zipIdx.toList).foldl
        (fun acc q => if acc = (op.getResult q.2 : ValuePtr) then q.1 else acc) v
      = if v ∈ op.getResults! ctx.raw
        then newValues[(op.getResults! ctx.raw).idxOf v]! else v := by
  rw [Array.toList_zipIdx]
  by_cases hv : v ∈ op.getResults! ctx.raw
  · rw [if_pos hv]
    obtain ⟨j, hj, hvj⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp hv
    have hidx : (op.getResults! ctx.raw).idxOf v = j := by
      have h1 : (op.getResult ((op.getResults! ctx.raw).idxOf v) : ValuePtr) = v :=
        OperationPtr.getResult_eq_of_idxOf_getResults! hv rfl
      have := h1.trans hvj.symm
      simp only [OperationPtr.getResult, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq,
        true_and] at this
      exact this
    have hjsize : j < newValues.toList.length := by
      rw [Array.length_toList]; omega
    have key := fold_replaceResult_zipIdx_hit op newValues.toList 0 j hjsize
      (by simpa [Array.mem_toList_iff] using hNoAlias)
    rw [Nat.zero_add] at key
    rw [hidx, show v = (op.getResult j : ValuePtr) from hvj.symm, key]
    rw [Array.getElem_toList]
    exact (getElem!_pos newValues j (by omega)).symm
  · rw [if_neg hv]
    apply fold_replaceResult_eq_self
    intro q hq hcontra
    apply hv
    rw [hcontra]
    refine OperationPtr.getResults!.mem_getResult ?_
    have hlt := List.snd_lt_of_mem_zipIdx (by simpa using hq)
    rw [Array.length_toList] at hlt; omega

/-- `rewriteMapping`'s `applyToArray` is, pointwise, the underlying value renaming: a value among
`op`'s results is redirected to the matching `newValue`, everything else is fixed. -/
theorem rewriteMapping_applyToArray_eq_map {ctx newCtx : WfIRContext OpCode}
    (op : OperationPtr) (newValues : Array ValuePtr) {mR mN} (arr : Array ValuePtr)
    (hin : ∀ v ∈ arr, v.InBounds ctx.raw) :
    (rewriteMapping (ctx := ctx) (newCtx := newCtx) op newValues mR mN).applyToArray arr hin
      = arr.map (fun v => if v ∈ op.getResults! ctx.raw
          then newValues[(op.getResults! ctx.raw).idxOf v]! else v) := by
  apply Array.ext
  · simp [ValueMapping.applyToArray]
  · intro i h1 h2
    simp only [ValueMapping.applyToArray, Array.getElem_map, Array.getElem_attach, rewriteMapping]
    split <;> grind

/-! ### Bridges from the `!`-checked driver operations to their proof-carrying counterparts.

`RewritePattern.fromLocalRewrite` drives the rewrite with the dynamically-checked `insertOp!`,
`replaceValue!`, and `eraseOp!` (each returns `none` if a precondition fails). When such a call
returns `some b'`, it agrees with the proof-carrying `insertOp`/`replaceValue`/`eraseOp` it reduces
to. These bridges expose that fact, letting the keystone fold lemmas below run unchanged against the
non-`!` API. -/

/-- When `insertOp!` succeeds it exhibits the proof-carrying `insertOp` call it reduces to. -/
theorem PatternRewriter.insertOp!_eq_some {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint}
    (h : b.insertOp! newOp ip = some b') :
    ∃ (h1 : newOp.InBounds b.ctx.raw) (h2 : ip.InBounds b.ctx.raw),
      PatternRewriter.insertOp b newOp ip h1 h2 = some b' := by
  unfold PatternRewriter.insertOp! at h
  split at h
  · rename_i hop
    split at h
    · exact ⟨hop, _, h⟩
    · simp at h
  · simp at h

/-- When `replaceValue!` succeeds it is the `replaceValue` of the same arguments. -/
theorem PatternRewriter.replaceValue!_eq_some {b b' : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr}
    (h : b.replaceValue! oldVal newVal = some b') :
    ∃ (ne : oldVal ≠ newVal) (oldIn : oldVal.InBounds b.ctx.raw) (newIn : newVal.InBounds b.ctx.raw),
      b.replaceValue oldVal newVal ne oldIn newIn = b' := by
  unfold PatternRewriter.replaceValue! at h
  split at h
  · rename_i hne
    split at h
    · rename_i hold
      split at h
      · rename_i hnew
        simp only [Option.some.injEq] at h
        exact ⟨hne, hold, hnew, h⟩
      · simp at h
    · simp at h
  · simp at h

/-- When `eraseOp!` succeeds it exhibits the proof-carrying `eraseOp` call it reduces to. -/
theorem PatternRewriter.eraseOp!_eq_some {b b' : PatternRewriter OpCode} {op : OperationPtr}
    (h : b.eraseOp! op = some b') :
    ∃ (r : op.getNumRegions! b.ctx.raw = 0) (u : (!op.hasUses! b.ctx.raw) = true)
      (hop : op.InBounds b.ctx.raw),
      PatternRewriter.eraseOp b op r u hop = some b' := by
  unfold PatternRewriter.eraseOp! at h
  split at h
  · rename_i hOp
    split at h
    · rename_i hRegions
      split at h
      · rename_i hUses
        exact ⟨hRegions, hUses, hOp, h⟩
      · simp at h
    · simp at h
  · simp at h

/-- `insertOp!` (when it succeeds) preserves all `InBounds` facts. -/
theorem PatternRewriter.insertOp!_ctx_inBounds {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {ptr : GenericPtr}
    (h : b.insertOp! newOp ip = some b') :
    ptr.InBounds b'.ctx.raw ↔ ptr.InBounds b.ctx.raw := by
  obtain ⟨h1, h2, h⟩ := PatternRewriter.insertOp!_eq_some h
  exact PatternRewriter.insertOp_ctx_inBounds h

/-- `insertOp!` (when it succeeds) frames a survivor's intrinsic data. -/
theorem PatternRewriter.insertOp!_sameIntrinsic {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {o : OperationPtr}
    (h : b.insertOp! newOp ip = some b') :
    o.SameIntrinsic b.ctx.raw b'.ctx.raw := by
  obtain ⟨h1, h2, h⟩ := PatternRewriter.insertOp!_eq_some h
  exact PatternRewriter.insertOp_sameIntrinsic h

/-- `insertOp!` (when it succeeds) frames a survivor's operands. -/
theorem PatternRewriter.insertOp!_getOperands {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {o : OperationPtr}
    (h : b.insertOp! newOp ip = some b') :
    o.getOperands! b'.ctx.raw = o.getOperands! b.ctx.raw := by
  obtain ⟨h1, h2, h⟩ := PatternRewriter.insertOp!_eq_some h
  exact PatternRewriter.insertOp_getOperands h

/-- `insertOp!` (when it succeeds) leaves every operation's region count unchanged. -/
theorem PatternRewriter.insertOp!_getNumRegions {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {o : OperationPtr}
    (h : b.insertOp! newOp ip = some b') :
    o.getNumRegions! b'.ctx.raw = o.getNumRegions! b.ctx.raw := by
  obtain ⟨h1, h2, h⟩ := PatternRewriter.insertOp!_eq_some h
  exact PatternRewriter.insertOp_getNumRegions h

/-- `insertOp!` (when it succeeds) leaves every operation's region pointers unchanged. -/
theorem PatternRewriter.insertOp!_getRegion {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {o : OperationPtr} {idx : Nat}
    (h : b.insertOp! newOp ip = some b') :
    o.getRegion! b'.ctx.raw idx = o.getRegion! b.ctx.raw idx := by
  obtain ⟨h1, h2, h⟩ := PatternRewriter.insertOp!_eq_some h
  exact PatternRewriter.insertOp_getRegion h

/-- `insertOp!` (when it succeeds) leaves every region's entry block unchanged. -/
theorem PatternRewriter.insertOp!_firstBlock {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {r : RegionPtr}
    (h : b.insertOp! newOp ip = some b') :
    (r.get! b'.ctx.raw).firstBlock = (r.get! b.ctx.raw).firstBlock := by
  obtain ⟨h1, h2, h⟩ := PatternRewriter.insertOp!_eq_some h
  exact PatternRewriter.insertOp_firstBlock h

/-- `insertOp!` (when it succeeds) leaves every block's argument count unchanged. -/
theorem PatternRewriter.insertOp!_getNumArguments {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {bl : BlockPtr}
    (h : b.insertOp! newOp ip = some b') :
    bl.getNumArguments! b'.ctx.raw = bl.getNumArguments! b.ctx.raw := by
  obtain ⟨h1, h2, h⟩ := PatternRewriter.insertOp!_eq_some h
  exact PatternRewriter.insertOp_getNumArguments h

/-- `insertOp!` (when it succeeds) leaves every value's type unchanged. -/
theorem PatternRewriter.insertOp!_getType {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {v : ValuePtr}
    (h : b.insertOp! newOp ip = some b') :
    v.getType! b'.ctx.raw = v.getType! b.ctx.raw := by
  obtain ⟨h1, h2, h⟩ := PatternRewriter.insertOp!_eq_some h
  exact PatternRewriter.insertOp_getType h

/-- `replaceValue!` (when it succeeds) preserves all `InBounds` facts. -/
theorem PatternRewriter.replaceValue!_ctx_inBounds {b b' : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {ptr : GenericPtr}
    (h : b.replaceValue! oldVal newVal = some b') :
    ptr.InBounds b'.ctx.raw ↔ ptr.InBounds b.ctx.raw := by
  obtain ⟨ne, oldIn, newIn, rfl⟩ := PatternRewriter.replaceValue!_eq_some h
  exact PatternRewriter.replaceValue_ctx_inBounds

/-- `replaceValue!` (when it succeeds) frames a survivor's intrinsic data. -/
theorem PatternRewriter.replaceValue!_sameIntrinsic {b b' : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {o : OperationPtr}
    (h : b.replaceValue! oldVal newVal = some b') :
    o.SameIntrinsic b.ctx.raw b'.ctx.raw := by
  obtain ⟨ne, oldIn, newIn, rfl⟩ := PatternRewriter.replaceValue!_eq_some h
  exact PatternRewriter.replaceValue_sameIntrinsic

/-- `replaceValue!` (when it succeeds) leaves every operation's region count unchanged. -/
theorem PatternRewriter.replaceValue!_getNumRegions {b b' : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {o : OperationPtr}
    (h : b.replaceValue! oldVal newVal = some b') :
    o.getNumRegions! b'.ctx.raw = o.getNumRegions! b.ctx.raw := by
  obtain ⟨ne, oldIn, newIn, rfl⟩ := PatternRewriter.replaceValue!_eq_some h
  exact PatternRewriter.replaceValue_getNumRegions

/-- `replaceValue!` (when it succeeds) leaves every operation's region pointers unchanged. -/
theorem PatternRewriter.replaceValue!_getRegion {b b' : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {o : OperationPtr} {idx : Nat}
    (h : b.replaceValue! oldVal newVal = some b') :
    o.getRegion! b'.ctx.raw idx = o.getRegion! b.ctx.raw idx := by
  obtain ⟨ne, oldIn, newIn, rfl⟩ := PatternRewriter.replaceValue!_eq_some h
  exact PatternRewriter.replaceValue_getRegion

/-- `replaceValue!` (when it succeeds) leaves every region's entry block unchanged. -/
theorem PatternRewriter.replaceValue!_firstBlock {b b' : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {r : RegionPtr}
    (h : b.replaceValue! oldVal newVal = some b') :
    (r.get! b'.ctx.raw).firstBlock = (r.get! b.ctx.raw).firstBlock := by
  obtain ⟨ne, oldIn, newIn, rfl⟩ := PatternRewriter.replaceValue!_eq_some h
  exact PatternRewriter.replaceValue_firstBlock

/-- `replaceValue!` (when it succeeds) leaves every block's argument count unchanged. -/
theorem PatternRewriter.replaceValue!_getNumArguments {b b' : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {bl : BlockPtr}
    (h : b.replaceValue! oldVal newVal = some b') :
    bl.getNumArguments! b'.ctx.raw = bl.getNumArguments! b.ctx.raw := by
  obtain ⟨ne, oldIn, newIn, rfl⟩ := PatternRewriter.replaceValue!_eq_some h
  exact PatternRewriter.replaceValue_getNumArguments

/-- `replaceValue!` (when it succeeds) leaves every value's type unchanged. -/
theorem PatternRewriter.replaceValue!_getType {b b' : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {v : ValuePtr}
    (h : b.replaceValue! oldVal newVal = some b') :
    v.getType! b'.ctx.raw = v.getType! b.ctx.raw := by
  obtain ⟨ne, oldIn, newIn, rfl⟩ := PatternRewriter.replaceValue!_eq_some h
  exact PatternRewriter.replaceValue_getType

/-! ### Helpers for the `getParentOpPreserved` field of `of_fromLocalRewrite`.

The enclosing-operation chain of a survivor is the composite `o → parent block → parent region →
parent operation`. The rewrite pipeline preserves each link: block and region parents are untouched
by op-list edits, a survivor's own parent is untouched (it is neither inserted nor erased), and a
region that is already attached cannot be re-attached (so its parent is stable). These lemmas package
those per-stage facts; the congruence lemma below then assembles them into `getParentOp!` stability. -/

/-- Membership-aware variant of `List.foldlM_option_invariant`: the per-step hypothesis may use that
the folded element comes from the list. Used to thread "the survivor is not the inserted op" through
the insert fold. -/
theorem List.foldlM_option_invariant_mem {α β : Type} {f : β → α → Option β} {P : β → Prop} :
    ∀ {l : List α} {init s : β},
      (∀ b a b', a ∈ l → f b a = some b' → (P b' ↔ P b)) →
      l.foldlM f init = some s → (P s ↔ P init)
  | [], init, s, _, h => by
    rw [List.foldlM_nil] at h
    obtain rfl : init = s := by simpa using h
    rfl
  | a :: t, init, s, hstep, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b, hf, hb⟩ := Option.bind_eq_some_iff.mp h
    have ih := List.foldlM_option_invariant_mem (l := t)
      (fun b a' b' hmem hfa => hstep b a' b' (List.mem_cons_of_mem a hmem) hfa) hb
    rw [ih, hstep init a b (by simp) hf]

/-- `getParentOp!` is stable between two contexts that agree on the relevant parent links: a
survivor's own parent block, every block's parent region, and every *already-parented* region's
parent operation. Stated as an implication on a concrete enclosing operation, which is all the
soundness lift needs (and is robust to detached regions being attached elsewhere). -/
theorem OperationPtr.getParentOp!_eq_of {c c' : IRContext OpCode} {o m : OperationPtr}
    (hfib : c.FieldsInBounds) (oIn : o.InBounds c)
    (hop : (o.get! c').parent = (o.get! c).parent)
    (hblk : ∀ b : BlockPtr, (b.get! c').parent = (b.get! c).parent)
    (hrgn : ∀ r : RegionPtr, r.InBounds c → (r.get! c).parent ≠ none →
      (r.get! c').parent = (r.get! c).parent)
    (h : o.getParentOp! c = some m) :
    o.getParentOp! c' = some m := by
  have key : ∀ d : IRContext OpCode, o.getParentOp! d =
      ((o.get! d).parent).bind (fun b => ((b.get! d).parent).bind (fun r => (r.get! d).parent)) := by
    intro d
    unfold OperationPtr.getParentOp!
    split
    · next heq => simp [heq]
    · next b heq =>
      split
      · next heq2 => simp [heq, heq2]
      · next r heq2 => simp [heq, heq2]
  rw [key c] at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  have hbIn : b.InBounds c := by grind [OperationPtr.parent!_inBounds]
  have hrIn : r.InBounds c := by grind [BlockPtr.parent!_inBounds]
  rw [key c', hop, hb]
  simp only [Option.bind_some, hblk b, hr,
    hrgn r hrIn (by rw [h]; exact Option.some_ne_none m)]
  exact h

/-- `PatternRewriter.insertOp` preserves every block's parent region. -/
theorem PatternRewriter.insertOp_blockParent {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {h1 h2} {block : BlockPtr}
    (h : PatternRewriter.insertOp b newOp ip h1 h2 = some b') :
    (block.get! b'.ctx.raw).parent = (block.get! b.ctx.raw).parent := by
  unfold PatternRewriter.insertOp at h
  split at h
  · simp at h
  · rename_i newCtx hwf
    simp only [Option.some.injEq] at h; subst h
    exact BlockPtr.parent!_wfRewriter_insertOp hwf

/-- `PatternRewriter.insertOp` preserves every region's parent operation. -/
theorem PatternRewriter.insertOp_regionParent {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {h1 h2} {r : RegionPtr}
    (h : PatternRewriter.insertOp b newOp ip h1 h2 = some b') :
    (r.get! b'.ctx.raw).parent = (r.get! b.ctx.raw).parent := by
  unfold PatternRewriter.insertOp at h
  split at h
  · simp at h
  · rename_i newCtx hwf
    simp only [Option.some.injEq] at h; subst h
    exact RegionPtr.parent!_wfRewriter_insertOp hwf

/-- `insertOp!` (when it succeeds) preserves every block's parent region. -/
theorem PatternRewriter.insertOp!_blockParent {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {block : BlockPtr}
    (h : b.insertOp! newOp ip = some b') :
    (block.get! b'.ctx.raw).parent = (block.get! b.ctx.raw).parent := by
  obtain ⟨h1, h2, h⟩ := PatternRewriter.insertOp!_eq_some h
  exact PatternRewriter.insertOp_blockParent h

/-- `insertOp!` (when it succeeds) preserves every region's parent operation. -/
theorem PatternRewriter.insertOp!_regionParent {b b' : PatternRewriter OpCode}
    {newOp : OperationPtr} {ip : InsertPoint} {r : RegionPtr}
    (h : b.insertOp! newOp ip = some b') :
    (r.get! b'.ctx.raw).parent = (r.get! b.ctx.raw).parent := by
  obtain ⟨h1, h2, h⟩ := PatternRewriter.insertOp!_eq_some h
  exact PatternRewriter.insertOp_regionParent h

/-- `insertOp!` (when it succeeds) preserves the parent of every operation other than the inserted
one. -/
theorem PatternRewriter.insertOp!_opParent {b b' : PatternRewriter OpCode}
    {newOp o : OperationPtr} {ip : InsertPoint}
    (h : b.insertOp! newOp ip = some b') (hne : o ≠ newOp) :
    (o.get! b'.ctx.raw).parent = (o.get! b.ctx.raw).parent := by
  obtain ⟨h1, h2, h⟩ := PatternRewriter.insertOp!_eq_some h
  exact PatternRewriter.insertOp_op_parent h hne

/-- `PatternRewriter.replaceValue` preserves every block's parent region. -/
theorem PatternRewriter.replaceValue_blockParent {b : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {ne oldIn newIn} {block : BlockPtr} :
    (block.get! (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw).parent =
    (block.get! b.ctx.raw).parent := by
  have hctx : (b.replaceValue oldVal newVal ne oldIn newIn).ctx
      = WfRewriter.replaceValue b.ctx oldVal newVal ne oldIn newIn := by
    simp only [PatternRewriter.replaceValue, PatternRewriter.addUsersInWorklist_same_ctx]
  rw [hctx]; exact BlockPtr.parent!_WfRewriter_replaceValue

/-- `PatternRewriter.replaceValue` preserves every region's parent operation. -/
theorem PatternRewriter.replaceValue_regionParent {b : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {ne oldIn newIn} {r : RegionPtr} :
    (r.get! (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw).parent =
    (r.get! b.ctx.raw).parent := by
  have hctx : (b.replaceValue oldVal newVal ne oldIn newIn).ctx
      = WfRewriter.replaceValue b.ctx oldVal newVal ne oldIn newIn := by
    simp only [PatternRewriter.replaceValue, PatternRewriter.addUsersInWorklist_same_ctx]
  rw [hctx]; exact RegionPtr.parent!_WfRewriter_replaceValue

/-- `PatternRewriter.replaceValue` preserves every operation's parent block. -/
theorem PatternRewriter.replaceValue_opParent {b : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {ne oldIn newIn} {o : OperationPtr} :
    (o.get! (b.replaceValue oldVal newVal ne oldIn newIn).ctx.raw).parent =
    (o.get! b.ctx.raw).parent := by
  have hctx : (b.replaceValue oldVal newVal ne oldIn newIn).ctx
      = WfRewriter.replaceValue b.ctx oldVal newVal ne oldIn newIn := by
    simp only [PatternRewriter.replaceValue, PatternRewriter.addUsersInWorklist_same_ctx]
  rw [hctx]; exact OperationPtr.parent!_WfRewriter_replaceValue

/-- `replaceValue!` (when it succeeds) preserves every block's parent region. -/
theorem PatternRewriter.replaceValue!_blockParent {b b' : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {block : BlockPtr}
    (h : b.replaceValue! oldVal newVal = some b') :
    (block.get! b'.ctx.raw).parent = (block.get! b.ctx.raw).parent := by
  obtain ⟨ne, oldIn, newIn, rfl⟩ := PatternRewriter.replaceValue!_eq_some h
  exact PatternRewriter.replaceValue_blockParent

/-- `replaceValue!` (when it succeeds) preserves every region's parent operation. -/
theorem PatternRewriter.replaceValue!_regionParent {b b' : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {r : RegionPtr}
    (h : b.replaceValue! oldVal newVal = some b') :
    (r.get! b'.ctx.raw).parent = (r.get! b.ctx.raw).parent := by
  obtain ⟨ne, oldIn, newIn, rfl⟩ := PatternRewriter.replaceValue!_eq_some h
  exact PatternRewriter.replaceValue_regionParent

/-- `replaceValue!` (when it succeeds) preserves every operation's parent block. -/
theorem PatternRewriter.replaceValue!_opParent {b b' : PatternRewriter OpCode}
    {oldVal newVal : ValuePtr} {o : OperationPtr}
    (h : b.replaceValue! oldVal newVal = some b') :
    (o.get! b'.ctx.raw).parent = (o.get! b.ctx.raw).parent := by
  obtain ⟨ne, oldIn, newIn, rfl⟩ := PatternRewriter.replaceValue!_eq_some h
  exact PatternRewriter.replaceValue_opParent

/-- A `WithCreatedOps` chain preserves every block's parent region (it only creates fresh ops). -/
theorem WfIRContext.WithCreatedOps.blockParent_eq {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂) {b : BlockPtr} :
    (b.get! ctx₂.raw).parent = (b.get! ctx₁.raw).parent := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hwco hex ih =>
    obtain ⟨opType, rt, ops, succ, regs, props, k₁, k₂, k₃, k₄, hcreate⟩ := hex
    rw [BlockPtr.parent!_WfRewriter_createOp hcreate]
    exact ih

/-- A `WithCreatedOps` chain preserves a survivor's parent block (it only creates fresh ops). -/
theorem WfIRContext.WithCreatedOps.opParent_eq {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂) {o : OperationPtr} (oIn : o.InBounds ctx₁.raw) :
    (o.get! ctx₂.raw).parent = (o.get! ctx₁.raw).parent := by
  induction h with
  | Nil => rfl
  | CreatedOp ctx₁ ctx₂ ctx₃ hwco hex ih =>
    obtain ⟨opType, rt, ops, succ, regs, props, k₁, k₂, k₃, k₄, hcreate⟩ := hex
    have ho2 : o.InBounds ctx₂.raw := by
      have := hwco.inBounds_mono (GenericPtr.operation o) (by grind); grind
    rw [OperationPtr.parent!_WfRewriter_createOp hcreate, if_neg (by grind)]
    exact ih oIn

/-- A `WithCreatedOps` chain preserves the parent operation of every *already-parented* in-bounds
region. The parent operation `P` is a survivor whose region list is preserved (`getRegion_eq`), and a
region is in its parent op's region list (wellformedness `region_parent`), so the link is stable. -/
theorem WfIRContext.WithCreatedOps.regionParent_eq_of_parented {ctx₁ ctx₂ : WfIRContext OpCode}
    (h : WfIRContext.WithCreatedOps ctx₁ ctx₂) {r : RegionPtr}
    (rIn : r.InBounds ctx₁.raw) (hpar : (r.get! ctx₁.raw).parent ≠ none) :
    (r.get! ctx₂.raw).parent = (r.get! ctx₁.raw).parent := by
  rcases hP : (r.get! ctx₁.raw).parent with _ | P
  · exact absurd hP hpar
  · have hPIn₁ : P.InBounds ctx₁.raw := by
      have := RegionPtr.parent!_inBounds ctx₁.wellFormed.inBounds rIn; grind
    have hPIn₂ : P.InBounds ctx₂.raw := by
      have := h.inBounds_mono (GenericPtr.operation P) (by grind); grind
    have rIn₂ : r.InBounds ctx₂.raw := by
      have := h.inBounds_mono (GenericPtr.region r) (by grind); grind
    obtain ⟨i, hi, hreg⟩ := ((ctx₁.wellFormed.operations P hPIn₁).region_parent r rIn).mpr hP
    have hnum : P.getNumRegions! ctx₂.raw = P.getNumRegions! ctx₁.raw := h.getNumRegions_eq hPIn₁
    have hregeq : P.getRegion! ctx₂.raw i = P.getRegion! ctx₁.raw i := h.getRegion_eq hPIn₁ i
    have hr₂ : (r.get! ctx₂.raw).parent = some P :=
      ((ctx₂.wellFormed.operations P hPIn₂).region_parent r rIn₂).mp
        ⟨i, by rw [hnum]; exact hi, by rw [hregeq]; exact hreg⟩
    rw [hr₂]

/--
**PR 9 — bridge from the concrete driver.** When `fromLocalRewrite` runs the rewrite branch for a
matched, in-bounds, region-free `op` that lives inside a block, and the pattern satisfies the four
`Return*` correctness obligations, the driver's output context `rewriter'.ctx` is related to the input
`rewriter.ctx` by a `RewrittenAt` instance (the existential supplies the block and the surrounding
`pre`/`post` operation lists). This is the concrete instance the abstract soundness lift consumes.

`opNotFunction` (clause 9) follows from `hOpRegions` (`op` has no regions, so in particular not one).
The remaining structural fields are discharged from the keystone fold decomposition plus the
`Return*` obligations; this is the deferred proof effort.
-/
theorem RewrittenAt.of_fromLocalRewrite
    {pattern : LocalRewritePattern OpCode}
    (hValid : pattern.Valid)
    (hSrcDom : rewriter.ctx.Dom)
    (hSrcVerif : rewriter.ctx.Verified)
    (hpat : pattern rewriter.ctx op = some (newCtxPat, some (newOps, newValues)))
    (hdriver : RewritePattern.fromLocalRewrite pattern rewriter op opInBounds = some rewriter') :
    ∃ (block : BlockPtr) (pre post : Array OperationPtr)
      (blockIn : block.InBounds rewriter.ctx.raw) (blockIn' : block.InBounds rewriter'.ctx.raw),
      (op.get! rewriter.ctx.raw).parent = some block ∧
      RewrittenAt rewriter.ctx op newOps newValues rewriter'.ctx opInBounds
        block pre post blockIn blockIn' ∧
      (∀ o ∈ newOps.toList,
        o.SameIntrinsic newCtxPat.raw rewriter'.ctx.raw ∧
        ((∀ v ∈ o.getOperands! newCtxPat.raw, v.InBounds rewriter'.ctx.raw) →
          o.getOperands! newCtxPat.raw = o.getOperands! rewriter'.ctx.raw)) := by
  -- `op` has a parent block: the driver inserts every `newOp` *before* `op`, and an insertion before
  -- a parentless op fails, so a successful `fromLocalRewrite` witnesses `op`'s parent. This recovers
  -- the block (and the parent equation) that the previous statement took as a hypothesis.
  obtain ⟨block, hOpParent⟩ : ∃ block, (op.get! rewriter.ctx.raw).parent = some block := by
    have h := hdriver
    simp only [RewritePattern.fromLocalRewrite, hpat] at h
    obtain ⟨block, hpar, -⟩ := Option.bind_eq_some_iff.mp h
    exact ⟨block, hpar⟩
  obtain ⟨-, hReturnCtxChanges, hReturnOps, hReturnValues, hReturnValuesInBounds,
    hReturnValuesNotOwnResults, hReturnValuesDominate, hMatchedOpHasNoRegions, -,
    hRewritePreservesDom, hRewritePreservesVerified, hRewriteNewValuesDominate,
    hRewritePreservesBlockDominance⟩ := hValid
  -- `op` has no regions: this is one of the pattern's validity obligations.
  have hOpRegions : op.getNumRegions! rewriter.ctx.raw = 0 :=
    hMatchedOpHasNoRegions rewriter.ctx op newCtxPat newOps newValues hpat
  -- `block` is in bounds of the source context: it is the parent of the in-bounds `op`.
  have blockIn : block.InBounds rewriter.ctx.raw := by
    have := rewriter.ctx.wellFormed.inBounds; grind
  -- Split `block`'s source operation list at `op` into the surrounding `pre`/`post`.
  obtain ⟨pre, post, hsrcList⟩ :=
    BlockPtr.operationList_split_at_op opInBounds hOpParent blockIn
  -- Keystone reduction: the driver's worklist bookkeeping is inert for the IR, so `hdriver` reduces
  -- to a pure `WfRewriter` fold (`bind_pure_comp` turns each loop body `· >>= pure ∘ .yield` into a
  -- functor map; `Array.forIn_yield_eq_foldlM` turns the `forIn` loops into `foldlM`s). After this,
  -- `hdriver` reads: insert every `newOp` before `op`, redirect each result to `newValues`, erase
  -- `op` — the middle operands-collection loop is dead (its result is discarded). Every `RewrittenAt`
  -- field below is a fact about the resulting `rewriter'.ctx` read off this fold.
  -- Keep the un-reduced driver equation for the well-formedness obligations (`newCtxDom`/`newCtxVerif`),
  -- which are stated against `RewritePattern.fromLocalRewrite`; `hdriver` itself is reduced below.
  have hdriverOrig := hdriver
  unfold RewritePattern.fromLocalRewrite at hdriver
  rw [hpat] at hdriver
  simp only [bind_pure_comp, Array.forIn_yield_eq_foldlM, id_map'] at hdriver
  -- Peel the leading parent guard (`let _ ← (op.get! …).parent`): a successful driver witnesses `op`'s
  -- parent block. We already recovered it as `hOpParent` above, so this binding is discarded here.
  obtain ⟨_guardBlock, _hguardBlock, hdriver⟩ := Option.bind_eq_some_iff.mp hdriver
  -- Decompose the reduced driver into its three stages: insert-fold (→ `s₁`), replace-fold (→ `s₂`),
  -- then the final `eraseOp` of `op`. The middle operands-collection loop is discarded.
  obtain ⟨s₁, hfold1, hdriver⟩ := Option.bind_eq_some_iff.mp hdriver
  obtain ⟨s₂, hfold2, hdriver⟩ := Option.bind_eq_some_iff.mp hdriver
  obtain ⟨_arr, _hloop, herase⟩ := Option.bind_eq_some_iff.mp hdriver
  -- The driver erases `op` with the dynamically-checked `eraseOp!`; recover the proof-carrying
  -- `eraseOp` call it reduces to (shadowing `herase`) so the keystone `eraseOp` lemmas apply.
  obtain ⟨_eraseRegions, _eraseUses, _eraseIn, herase⟩ := PatternRewriter.eraseOp!_eq_some herase
  -- Bounds transport across the insert/replace folds: both preserve every `InBounds` fact, so `s₂.ctx`
  -- agrees with the pattern's output `newCtxPat` on bounds.
  have hbnd : ∀ ptr : GenericPtr, ptr.InBounds s₂.ctx.raw ↔ ptr.InBounds newCtxPat.raw := by
    intro ptr
    have h1 := Array.foldlM_option_invariant
      (P := fun b : PatternRewriter OpCode => ptr.InBounds b.ctx.raw)
      (fun b a b' h => PatternRewriter.insertOp!_ctx_inBounds h) hfold1
    have h2 := Array.foldlM_option_invariant
      (P := fun b : PatternRewriter OpCode => ptr.InBounds b.ctx.raw)
      (fun b a b' h => PatternRewriter.replaceValue!_ctx_inBounds h) hfold2
    exact h2.trans h1
  -- `block` survives into the pattern's output context (the pattern only creates ops).
  have hblockNewCtxPat : block.InBounds newCtxPat.raw :=
    (hReturnCtxChanges rewriter.ctx op newCtxPat newOps newValues hpat).inBounds_mono
      (GenericPtr.block block) (by grind)
  -- `block` survives the rewrite: bounds are preserved through the folds (`hbnd`) and the final
  -- `eraseOp` only removes `op` (an operation), never a block.
  have blockIn' : block.InBounds rewriter'.ctx.raw := by
    have hb := (hbnd (GenericPtr.block block)).mpr hblockNewCtxPat
    rw [PatternRewriter.eraseOp_ctx_eq herase]
    grind [WfRewriter.eraseOp]
  -- The pattern only creates operations, so every source pointer survives into `newCtxPat`.
  have hCreated : WfIRContext.WithCreatedOps rewriter.ctx newCtxPat :=
    hReturnCtxChanges rewriter.ctx op newCtxPat newOps newValues hpat
  -- Survival of non-`op` pointers into the final context: through the insert/replace folds (`hbnd`),
  -- then the final `eraseOp` (which only removes `op` and pointers it owns).
  have hSurviveOp : ∀ o : OperationPtr, o ≠ op → o.InBounds newCtxPat.raw →
      o.InBounds rewriter'.ctx.raw := by
    intro o hne ho
    have hb := (hbnd (GenericPtr.operation o)).mpr ho
    rw [PatternRewriter.eraseOp_ctx_eq herase]
    grind [WfRewriter.eraseOp]
  have hSurviveBlock : ∀ b : BlockPtr, b.InBounds newCtxPat.raw → b.InBounds rewriter'.ctx.raw := by
    intro b hb'
    have hb := (hbnd (GenericPtr.block b)).mpr hb'
    rw [PatternRewriter.eraseOp_ctx_eq herase]
    grind [WfRewriter.eraseOp]
  have hSurviveRegion : ∀ r : RegionPtr, r.InBounds newCtxPat.raw → r.InBounds rewriter'.ctx.raw := by
    intro r hr'
    have hb := (hbnd (GenericPtr.region r)).mpr hr'
    rw [PatternRewriter.eraseOp_ctx_eq herase]
    grind [WfRewriter.eraseOp]
  -- Bidirectional bounds for a non-`op` operation: the folds preserve all bounds and the final
  -- `eraseOp` removes only `op`, so an operation `≠ op` is in `rewriter'.ctx` iff it is in `newCtxPat`.
  have hOpBnd : ∀ o : OperationPtr, o ≠ op →
      (o.InBounds rewriter'.ctx.raw ↔ o.InBounds newCtxPat.raw) := by
    intro o hne
    have hb := hbnd (GenericPtr.operation o)
    rw [PatternRewriter.eraseOp_ctx_eq herase]
    grind [WfRewriter.eraseOp]
  -- Survival of a value that is not one of `op`'s results: the folds preserve bounds and `eraseOp`
  -- removes only `op` and the pointers it owns (so a value whose owner is `≠ op` survives).
  have hSurviveVal : ∀ v : ValuePtr, v.InBounds newCtxPat.raw →
      (∀ orp : OpResultPtr, v = ValuePtr.opResult orp → orp.op ≠ op) →
      v.InBounds rewriter'.ctx.raw := by
    intro v hv hcond
    have hb := (hbnd (GenericPtr.value v)).mpr hv
    rw [PatternRewriter.eraseOp_ctx_eq herase]
    grind [WfRewriter.eraseOp]
  -- === Keystone block-list facts (shared by the `tgtList`/`otherBlocks` fields). ===
  -- `op` is in bounds of the pattern's output and not among the freshly created `newOps`.
  have hopNewCtxPat : op.InBounds newCtxPat.raw := by
    have := hCreated.inBounds_mono (GenericPtr.operation op) (by grind); grind
  have hopNotNewOps : op ∉ newOps := fun hmem =>
    ((hReturnOps rewriter.ctx op newCtxPat newOps newValues hpat op).mp hmem).2 opInBounds
  -- `op` occurs once in `block`'s source list, so it is in neither `pre` nor `post`.
  have hoppre : op ∉ pre ∧ op ∉ post := by
    have hnodup := BlockPtr.OpChain_array_toList_Nodup
      (BlockPtr.operationListWF rewriter.ctx.raw block blockIn rewriter.ctx.wellFormed)
    rw [hsrcList] at hnodup
    simp only [Array.toList_append, List.nodup_append, List.mem_append] at hnodup
    exact ⟨fun h => hnodup.1.2.2 op (by simpa using h) op (by simp) rfl,
           fun h => hnodup.2.2 op (Or.inr (by simp)) op (by simpa using h) rfl⟩
  -- `block`'s list in the pattern output is still `pre ++ [op] ++ post` (only ops were created).
  have hlistInit : ∀ (hb : block.InBounds newCtxPat.raw),
      block.operationList newCtxPat.raw newCtxPat.wellFormed hb = pre ++ #[op] ++ post := by
    intro hb; rw [hCreated.operationList_eq blockIn hb, hsrcList]
  have hparInit : (op.get! newCtxPat.raw).parent = some block :=
    (BlockPtr.operationList.mem hopNewCtxPat).mpr
      (by rw [hlistInit hblockNewCtxPat]; simp [Array.mem_append])
  -- The two driver folds as `List.foldlM`s.
  have hfold1L := hfold1; rw [← Array.foldlM_toList] at hfold1L
  have hfold2L := hfold2; rw [← Array.foldlM_toList] at hfold2L
  -- Insert fold: `block`'s list becomes `pre ++ newOps ++ [op] ++ post`; `op` keeps its parent.
  obtain ⟨hopS1, hparS1, hlistS1⟩ :=
    PatternRewriter.foldlM_insertOp_before_opList
      (hf := fun b a b' hfa => PatternRewriter.insertOp!_eq_some hfa)
      hopNewCtxPat hfold1L hparInit hlistInit hoppre.1 hoppre.2 (by simpa using hopNotNewOps)
  have hblockS1 : block.InBounds s₁.ctx.raw := by have := s₁.ctx.wellFormed.inBounds; grind
  have hblockS2 : block.InBounds s₂.ctx.raw := by
    have := hbnd (GenericPtr.block block); grind
  -- Replace fold leaves `block`'s list untouched (`hstep` is inlined so `f` matches the driver's).
  have hblockListS2 : block.operationList s₂.ctx.raw s₂.ctx.wellFormed hblockS2
      = pre ++ newOps ++ #[op] ++ post := by
    rw [PatternRewriter.foldlM_preserves_opList (c := block)
      (hstep := by
        intro b a b' hfa
        obtain ⟨ne, oldIn, newIn, rfl⟩ := PatternRewriter.replaceValue!_eq_some hfa
        exact ⟨fun hcin => PatternRewriter.replaceValue_blockPtr_inBounds.mpr hcin,
          fun hc hc' => PatternRewriter.replaceValue_operationList hc hc'⟩)
      hfold2L hblockS1 hblockS2, hlistS1 hblockS1]
  have hopS2 : op.InBounds s₂.ctx.raw := by have := hbnd (GenericPtr.operation op); grind
  have hopParentS2 : (op.get! s₂.ctx.raw).parent = some block :=
    (BlockPtr.operationList.mem hopS2).mpr (by rw [hblockListS2]; simp [Array.mem_append])
  -- === Block-argument count/type frame (clause 7). The four stages — created ops, insert fold,
  -- replace fold, final `eraseOp` — each preserve argument counts and types. Counts are preserved
  -- unconditionally; argument types need only the block argument's in-bounds witness for the `eraseOp`
  -- stage. ===
  have hNumArgs : ∀ (bl : BlockPtr),
      bl.getNumArguments! rewriter'.ctx.raw = bl.getNumArguments! rewriter.ctx.raw := by
    intro bl
    have hCre : bl.getNumArguments! newCtxPat.raw = bl.getNumArguments! rewriter.ctx.raw :=
      hCreated.getNumArguments_eq bl
    have hIns : bl.getNumArguments! s₁.ctx.raw = bl.getNumArguments! newCtxPat.raw := by
      have h := Array.foldlM_option_invariant
        (P := fun b : PatternRewriter OpCode =>
          bl.getNumArguments! b.ctx.raw = bl.getNumArguments! newCtxPat.raw)
        (fun b a b' hh => by
          have := PatternRewriter.insertOp!_getNumArguments (bl := bl) hh
          constructor <;> intro hb <;> grind) hfold1
      exact h.mpr rfl
    have hRep : bl.getNumArguments! s₂.ctx.raw = bl.getNumArguments! s₁.ctx.raw := by
      have h := Array.foldlM_option_invariant
        (P := fun b : PatternRewriter OpCode =>
          bl.getNumArguments! b.ctx.raw = bl.getNumArguments! s₁.ctx.raw)
        (fun b a b' hh => by
          have hst : bl.getNumArguments! b'.ctx.raw = bl.getNumArguments! b.ctx.raw :=
            PatternRewriter.replaceValue!_getNumArguments hh
          constructor <;> intro hb <;> grind) hfold2
      exact h.mpr rfl
    have hErase : bl.getNumArguments! rewriter'.ctx.raw = bl.getNumArguments! s₂.ctx.raw := by
      rw [PatternRewriter.eraseOp_ctx_eq herase]
      exact BlockPtr.getNumArguments!_wfRewriter_eraseOp
    rw [hErase, hRep, hIns, hCre]
  have hArgTypes : ∀ (bl : BlockPtr), bl.InBounds rewriter.ctx.raw →
      ∀ i, i < bl.getNumArguments! rewriter.ctx.raw →
        (bl.getArgument i : ValuePtr).getType! rewriter'.ctx.raw =
        (bl.getArgument i : ValuePtr).getType! rewriter.ctx.raw := by
    intro bl blIn i hi
    -- Work with the explicit block-argument value `blockArgument ⟨bl, i⟩` (`getArgument i` is `⟨bl, i⟩`).
    have hv : (bl.getArgument i : ValuePtr) = ValuePtr.blockArgument ⟨bl, i⟩ := by
      rw [BlockPtr.getArgument_def]
    rw [hv]
    have hCre : (ValuePtr.blockArgument ⟨bl, i⟩).getType! newCtxPat.raw
        = (ValuePtr.blockArgument ⟨bl, i⟩).getType! rewriter.ctx.raw :=
      hCreated.getType_blockArgument_eq ⟨bl, i⟩
    have hIns : (ValuePtr.blockArgument ⟨bl, i⟩).getType! s₁.ctx.raw
        = (ValuePtr.blockArgument ⟨bl, i⟩).getType! newCtxPat.raw := by
      have h := Array.foldlM_option_invariant
        (P := fun b : PatternRewriter OpCode =>
          (ValuePtr.blockArgument ⟨bl, i⟩).getType! b.ctx.raw
            = (ValuePtr.blockArgument ⟨bl, i⟩).getType! newCtxPat.raw)
        (fun b a b' hh => by
          have := PatternRewriter.insertOp!_getType (v := (ValuePtr.blockArgument ⟨bl, i⟩)) hh
          constructor <;> intro hb <;> grind) hfold1
      exact h.mpr rfl
    have hRep : (ValuePtr.blockArgument ⟨bl, i⟩).getType! s₂.ctx.raw
        = (ValuePtr.blockArgument ⟨bl, i⟩).getType! s₁.ctx.raw := by
      have h := Array.foldlM_option_invariant
        (P := fun b : PatternRewriter OpCode =>
          (ValuePtr.blockArgument ⟨bl, i⟩).getType! b.ctx.raw
            = (ValuePtr.blockArgument ⟨bl, i⟩).getType! s₁.ctx.raw)
        (fun b a b' hh => by
          have hst : (ValuePtr.blockArgument ⟨bl, i⟩).getType! b'.ctx.raw
              = (ValuePtr.blockArgument ⟨bl, i⟩).getType! b.ctx.raw :=
            PatternRewriter.replaceValue!_getType hh
          constructor <;> intro hb <;> grind) hfold2
      exact h.mpr rfl
    -- `eraseOp` preserves the type of any *in-bounds* value; the `i`-th argument of the surviving
    -- block `bl` is in bounds of `rewriter'.ctx` because the count is preserved.
    have hblRew' : bl.InBounds rewriter'.ctx.raw :=
      hSurviveBlock bl (hCreated.inBounds_mono (GenericPtr.block bl) (by grind))
    have hvIn : (ValuePtr.blockArgument ⟨bl, i⟩).InBounds rewriter'.ctx.raw := by
      have hlt : i < bl.getNumArguments! rewriter'.ctx.raw := by rw [hNumArgs bl]; exact hi
      grind [BlockArgumentPtr.inBounds_def, BlockPtr.getNumArguments!_eq_getNumArguments]
    have hErase : (ValuePtr.blockArgument ⟨bl, i⟩).getType! rewriter'.ctx.raw
        = (ValuePtr.blockArgument ⟨bl, i⟩).getType! s₂.ctx.raw := by
      rw [PatternRewriter.eraseOp_ctx_eq herase]
      exact ValuePtr.getType!_wfRewriter_eraseOp (PatternRewriter.eraseOp_ctx_eq herase ▸ hvIn)
    rw [hErase, hRep, hIns, hCre]
  have hR : RewrittenAt rewriter.ctx op newOps newValues rewriter'.ctx opInBounds
      block pre post blockIn blockIn' := {
    -- Block-list shape: discharged for the source by the split lemma.
    srcList := hsrcList
    -- Target list: the insert fold turns `pre ++ [op] ++ post` into `pre ++ newOps ++ [op] ++ post`
    -- (`hblockListS2`), then `eraseOp op` drops the unique `op`, leaving `pre ++ newOps ++ post`.
    tgtList := by
      rw [BlockPtr.operationList_congr (PatternRewriter.eraseOp_ctx_eq herase) blockIn'
            (PatternRewriter.eraseOp_ctx_eq herase ▸ blockIn'),
          BlockPtr.operationList_WfRewriter_eraseOp (block := block) hblockS2,
          if_pos hopParentS2, hblockListS2]
      exact Array.erase_mid pre newOps post op hoppre.1 hopNotNewOps
    -- Other blocks: untouched by the created ops (`WithCreatedOps`), the insert fold (inserts target
    -- `block ≠ c`), the replace fold, and the final `eraseOp` (drops `op`, whose parent is `block ≠ c`).
    otherBlocks := by
      intro c cIn cIn' hcne
      -- `c` is in bounds throughout the rewrite.
      have hcNewCtxPat : c.InBounds newCtxPat.raw := by
        have := hCreated.inBounds_mono (GenericPtr.block c) (by grind); grind
      have hcS1 : c.InBounds s₁.ctx.raw := by
        have h1 := Array.foldlM_option_invariant
          (P := fun b : PatternRewriter OpCode => (GenericPtr.block c).InBounds b.ctx.raw)
          (fun b a b' h => PatternRewriter.insertOp!_ctx_inBounds h) hfold1
        grind
      have hcS2 : c.InBounds s₂.ctx.raw := by have := hbnd (GenericPtr.block c); grind
      have hcond : (op.get! s₂.ctx.raw).parent ≠ (c : Option BlockPtr) := by
        rw [hopParentS2]
        intro h
        have hbc : block = c := by simpa using h
        exact hcne hbc.symm
      -- `eraseOp op` leaves `c`'s list alone, since `op`'s parent is `block ≠ c`.
      rw [BlockPtr.operationList_congr (PatternRewriter.eraseOp_ctx_eq herase) cIn'
            (PatternRewriter.eraseOp_ctx_eq herase ▸ cIn'),
          BlockPtr.operationList_WfRewriter_eraseOp (block := c) hcS2, if_neg hcond]
      -- Replace fold leaves `c`'s list alone.
      rw [PatternRewriter.foldlM_preserves_opList (c := c)
        (hstep := by
          intro b a b' hfa
          obtain ⟨ne, oldIn, newIn, rfl⟩ := PatternRewriter.replaceValue!_eq_some hfa
          exact ⟨fun hcin => PatternRewriter.replaceValue_blockPtr_inBounds.mpr hcin,
            fun h1 h2 => PatternRewriter.replaceValue_operationList h1 h2⟩)
        hfold2L hcS1 hcS2]
      -- Insert fold leaves `c`'s list alone (inserts target `block ≠ c`).
      rw [PatternRewriter.foldlM_insertOp_before_other (c := c) (block := block) hcne
        (hf := fun b a b' hfa => PatternRewriter.insertOp!_eq_some hfa)
        hopNewCtxPat hparInit hfold1L (by simpa using hopNotNewOps) hcNewCtxPat hcS1]
      -- Created ops leave `c`'s list alone.
      exact (hCreated.operationList_eq cIn hcNewCtxPat).symm
    -- Number of produced values: directly from the pattern's `ReturnValues` obligation.
    newValuesSize := hReturnValues rewriter.ctx op opInBounds newCtxPat newOps newValues hpat
    -- Every produced value is in bounds of `newCtxPat` (`ReturnValuesInBounds`) and is not one of
    -- `op`'s own results (`ReturnValuesNotOwnResults`), so it survives the final `eraseOp op`
    -- (`hSurviveVal`, which only needs the value's owner to differ from `op`).
    newValuesInBounds := by
      intro v hv
      apply hSurviveVal v (hReturnValuesInBounds rewriter.ctx op newCtxPat newOps newValues hpat v hv)
      intro orp hvorp heq
      apply hReturnValuesNotOwnResults rewriter.ctx op newCtxPat newOps newValues hpat v hv orp.index
      obtain ⟨o', i'⟩ := orp
      grind [OperationPtr.getResult]
    -- `ReturnOps` characterizes `newOps` as fresh to `newCtxPat`; a `newOp ≠ op` has the same bounds
    -- in `newCtxPat` and `rewriter'.ctx` (`hOpBnd`), so the freshness transports.
    newOpsFresh := by
      intro newOp
      have hfresh := hReturnOps rewriter.ctx op newCtxPat newOps newValues hpat newOp
      constructor
      · intro hmem
        obtain ⟨h1, h2⟩ := hfresh.mp hmem
        have hne : newOp ≠ op := by rintro rfl; exact h2 opInBounds
        exact ⟨(hOpBnd newOp hne).mpr h1, h2⟩
      · rintro ⟨h1, h2⟩
        have hne : newOp ≠ op := by rintro rfl; exact h2 opInBounds
        exact hfresh.mpr ⟨(hOpBnd newOp hne).mp h1, h2⟩
    -- A value that is not a result of `op` survives: its owner (if any) is `≠ op`, so it is not one
    -- of the pointers `eraseOp` removes.
    mapNonResultsInBounds := by
      intro v vIn hv
      apply hSurviveVal v (hCreated.inBounds_mono (GenericPtr.value v) (by grind))
      rintro orp rfl horp
      apply hv
      rw [OperationPtr.getResults!.mem_iff_exists_index]
      refine ⟨orp.index, by grind, ?_⟩
      rw [OperationPtr.getResult_def]
      obtain ⟨o, i⟩ := orp
      simp_all
    -- `eraseOp op` deallocates `op`, so it is no longer in bounds of `rewriter'.ctx`.
    opErased := by
      rw [PatternRewriter.eraseOp_ctx_eq herase]
      grind [WfRewriter.eraseOp, Rewriter.eraseOp,
        OperationPtr.InBounds.ne_of_inBounds_OperationPtr_dealloc]
    -- Every operation `≠ op` survives: into `newCtxPat` (pattern only creates), then the folds/erase.
    survives := fun o hoIn hne =>
      hSurviveOp o hne (hCreated.inBounds_mono (GenericPtr.operation o) (by grind))
    -- `CrossContextFrame` under `σ`: created-ops/insert-fold/erase frame `o`'s intrinsic data
    -- (`SameIntrinsic`), the replace fold redirects its operands exactly as `σ` does, and `o`'s own
    -- results survive untouched. `reflect` uses that no `newValue` is a source-context result.
    frame := by
      intro o oIn oIn' hne
      have hNoAlias : ∀ x ∈ newValues, ∀ m, x ≠ (op.getResult m : ValuePtr) :=
        hReturnValuesNotOwnResults rewriter.ctx op newCtxPat newOps newValues hpat
      have hsize : newValues.size = op.getNumResults! rewriter.ctx.raw :=
        hReturnValues rewriter.ctx op opInBounds newCtxPat newOps newValues hpat
      -- `o` survives every stage in bounds.
      have hoNewCtxPat : o.InBounds newCtxPat.raw :=
        hCreated.inBounds_mono (GenericPtr.operation o) (by grind)
      have hoS1 : o.InBounds s₁.ctx.raw := by
        have h := Array.foldlM_option_invariant
          (P := fun b : PatternRewriter OpCode => (GenericPtr.operation o).InBounds b.ctx.raw)
          (fun b a b' hh => PatternRewriter.insertOp!_ctx_inBounds hh) hfold1
        grind
      have hoErase := PatternRewriter.eraseOp_ctx_eq herase ▸ oIn'
      -- (1) Intrinsic data is framed across the whole pipeline.
      have hcre : o.SameIntrinsic rewriter.ctx.raw newCtxPat.raw := hCreated.sameIntrinsic oIn
      have hins : o.SameIntrinsic newCtxPat.raw s₁.ctx.raw := by
        have h := Array.foldlM_option_invariant
          (P := fun b : PatternRewriter OpCode => o.SameIntrinsic newCtxPat.raw b.ctx.raw)
          (fun b a b' hh =>
            ⟨fun hb => hb.trans (PatternRewriter.insertOp!_sameIntrinsic hh).symm,
             fun hb => hb.trans (PatternRewriter.insertOp!_sameIntrinsic hh)⟩) hfold1
        exact h.mpr OperationPtr.SameIntrinsic.rfl
      have hrep : o.SameIntrinsic s₁.ctx.raw s₂.ctx.raw := by
        have h := Array.foldlM_option_invariant
          (P := fun b : PatternRewriter OpCode => o.SameIntrinsic s₁.ctx.raw b.ctx.raw)
          (fun b a b' hh => by
            have hst : o.SameIntrinsic b.ctx.raw b'.ctx.raw :=
              PatternRewriter.replaceValue!_sameIntrinsic hh
            exact ⟨fun hb => hb.trans hst.symm, fun hb => hb.trans hst⟩) hfold2
        exact h.mpr OperationPtr.SameIntrinsic.rfl
      have hers : o.SameIntrinsic s₂.ctx.raw rewriter'.ctx.raw := by
        rw [PatternRewriter.eraseOp_ctx_eq herase]
        exact ⟨OperationPtr.getOpType!_wfRewriter_eraseOp hoErase,
          fun _ => OperationPtr.getProperties!_wfRewriter_eraseOp hoErase,
          OperationPtr.getNumResults!_wfRewriter_eraseOp hoErase,
          OperationPtr.getSuccessors!_wfRewriter_eraseOp hoErase,
          OperationPtr.getResultTypes!_wfRewriter_eraseOp hoErase⟩
      have hsame : o.SameIntrinsic rewriter.ctx.raw rewriter'.ctx.raw :=
        hcre.trans (hins.trans (hrep.trans hers))
      -- (2) Operands are rewritten by the result→`newValues` redirect, which equals `σ`.
      have hopsErase : o.getOperands! rewriter'.ctx.raw = o.getOperands! s₂.ctx.raw := by
        rw [PatternRewriter.eraseOp_ctx_eq herase]
        exact OperationPtr.getOperands!_wfRewriter_eraseOp hoErase
      have hopsRepl : o.getOperands! s₂.ctx.raw
          = (newValues.zipIdx.toList).foldl
              (fun arr q => arr.map (fun v => if v = (op.getResult q.2 : ValuePtr) then q.1 else v))
              (o.getOperands! s₁.ctx.raw) :=
        PatternRewriter.foldlM_replaceValue_getOperands
          (hf := fun b q b' hfa => PatternRewriter.replaceValue!_eq_some hfa)
          hfold2L hoS1
      have hopsIns : o.getOperands! s₁.ctx.raw = o.getOperands! newCtxPat.raw := by
        have h := Array.foldlM_option_invariant
          (P := fun b : PatternRewriter OpCode =>
            o.getOperands! b.ctx.raw = o.getOperands! newCtxPat.raw)
          (fun b a b' hh => by
            have := PatternRewriter.insertOp!_getOperands (o := o) hh
            constructor <;> intro hb <;> grind) hfold1
        exact h.mpr rfl
      have hopsCre : o.getOperands! newCtxPat.raw = o.getOperands! rewriter.ctx.raw :=
        hCreated.getOperands_eq oIn
      -- Assemble `PreservesOperation` (fields: opType, props, resultTypes, successors, operands,
      -- results, reflect).
      refine ⟨hsame.1, ?_, hsame.2.2.2.2, hsame.2.2.2.1, ?_, ?_, ?_⟩
      · -- props
        rw [hsame.2.1]
        refine eq_of_heq (HEq.trans ?_ (eqRec_heq _ _).symm)
        rw [hsame.1]
      · -- operands
        rw [hopsErase, hopsRepl, hopsIns, hopsCre, List.foldl_arrayMap_fusion,
          rewriteMapping_applyToArray_eq_map]
        congr 1
        funext v
        exact fold_replaceResult_zipIdx_eq_sigma op newValues hsize hNoAlias v
      · -- results: `o`'s results are unchanged and fixed by `σ` (none is a result of `op`).
        have hres : o.getResults! rewriter'.ctx.raw = o.getResults! rewriter.ctx.raw := by
          simp only [OperationPtr.getResults!]; rw [hsame.2.2.1]
        rw [hres, rewriteMapping_applyToArray_eq_map]
        apply Array.ext
        · simp
        · intro i h1 _
          simp only [Array.getElem_map]
          have hidx : i < o.getNumResults! rewriter.ctx.raw := by
            simpa [OperationPtr.getResults!.size_eq_getNumResults!] using h1
          have hnotmem : (o.getResults! rewriter.ctx.raw)[i] ∉ op.getResults! rewriter.ctx.raw := by
            rw [OperationPtr.getResults!.getElem_eq_getResult hidx]
            intro hmem
            obtain ⟨k, _, hkeq⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp hmem
            simp only [OperationPtr.getResult, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq] at hkeq
            exact hne hkeq.1.symm
          rw [if_neg hnotmem]
      · -- reflect: SSA dominance rules out the only would-be collision. The reflection is required
        -- only for `val` in scope at `o` (`hValDom`). If `val` is a result of `op` redirected by `σ`
        -- onto `o`'s `i`-th result, then `op`'s result dominates `.before o` while `o`'s forwarded
        -- result (a source value, in scope at `op` by `ReturnValuesDominate`) dominates `.before op`
        -- — impossible for `o ≠ op` (`not_opResult_dominatesIp_before_cycle`).
        intro val valIn i hValDom hval
        by_cases hvr : val ∈ op.getResults! rewriter.ctx.raw
        · exfalso
          simp only [rewriteMapping, dif_pos hvr] at hval
          have hk : (op.getResults! rewriter.ctx.raw).idxOf val < newValues.size := by
            have hlt : (op.getResults! rewriter.ctx.raw).idxOf val
                < (op.getResults! rewriter.ctx.raw).size := Array.idxOf_lt_length_of_mem hvr
            simp only [OperationPtr.getResults!.size_eq_getNumResults!] at hlt; omega
          -- The forwarded value `σ val = (o.getResult i : ValuePtr)` is one of `newValues`.
          have hmem : (ValuePtr.opResult (o.getResult i)) ∈ newValues := by
            rw [← hval, getElem!_pos newValues _ hk]; exact Array.getElem_mem hk
          -- It is a *source* result of `o` (its index is framed by `hcre`), hence in scope at `op`
          -- (`ReturnValuesDominate`).
          have hvInPat := hReturnValuesInBounds rewriter.ctx op newCtxPat newOps newValues hpat _ hmem
          have hiSrc : i < o.getNumResults! rewriter.ctx.raw := by
            have hi := OpResultPtr.inBounds_OperationPtr_getNumResults! (o.getResult i) newCtxPat.raw
              (by simpa using hvInPat)
            simpa [hcre.2.2.1] using hi
          have hvRes : (ValuePtr.opResult (o.getResult i)) ∈ o.getResults! rewriter.ctx.raw :=
            OperationPtr.getResults!.mem_getResult hiSrc
          have hvInSrc : (ValuePtr.opResult (o.getResult i)).InBounds rewriter.ctx.raw := by
            simpa using OpResultPtr.inBounds_of (result := o.getResult i) oIn (by simpa using hiSrc)
          have hvDom := hReturnValuesDominate rewriter.ctx op newCtxPat newOps newValues hpat _ hmem hvInSrc
          exact hSrcDom.not_opResult_dominatesIp_before_cycle hne.symm hvr hValDom hvRes hvDom
        · simpa only [rewriteMapping, dif_neg hvr] using hval
    -- Blocks stay in bounds: into `newCtxPat`, then the folds/erase (erase removes only `op`).
    blocksInBounds := fun b hb =>
      hSurviveBlock b (hCreated.inBounds_mono (GenericPtr.block b) (by grind))
    -- Source dominance-wellformedness is propagated across the rewrite by the pattern obligation
    -- `RewritePreservesDom` (the driver-level counterpart of `PreservesSemantics`'s `ctxDom`).
    newCtxDom := hRewritePreservesDom rewriter op opInBounds rewriter' hdriverOrig hSrcDom
    -- As `newCtxDom`, via the source `rewriter.ctx.Verified` and the `RewritePreservesVerified`
    -- pattern obligation.
    newCtxVerif := hRewritePreservesVerified rewriter op opInBounds rewriter' hdriverOrig hSrcVerif
    -- Produced values dominate the post-insertion point in `block` (the SSA-validity condition:
    -- results of `newOps` are defined within the span, forwarded values are in scope throughout the
    -- block); discharged from the driver-level `RewriteNewValuesDominate` pattern obligation.
    newValuesDominate :=
      hRewriteNewValuesDominate rewriter op opInBounds rewriter' hdriverOrig block newCtxPat
        newOps newValues hOpParent hpat
    -- Operation-list edits leave block-argument counts and types untouched (the chain `hNumArgs` /
    -- `hArgTypes` established above). The full `arguments` record is not preserved — argument
    -- `firstUse` heads move as uses are redirected/erased — but count and type are, which is all the
    -- block-argument frame consequences (`numArgsEq`/`argType_eq`/`getArguments!_eq`) need.
    blockNumArgsPreserved := fun bl _ => hNumArgs bl
    blockArgTypesPreserved := hArgTypes
    -- Op-list edits inside `block` leave the CFG unchanged, so block-level dominance agrees across
    -- the two contexts. As with `newCtxDom`/`newCtxVerif`, this is propagated from the driver-level
    -- pattern obligation `RewritePreservesBlockDominance` (block-dominance preservation does not hold
    -- for an arbitrary op-list surgery, so it is discharged per concrete pattern).
    blockDominatesPreserved := fun b₁ b₂ h₁ h₂ =>
      hRewritePreservesBlockDominance rewriter op opInBounds rewriter' hdriverOrig b₁ b₂ h₁ h₂
    -- Op-list edits (create / insert / replace-value / erase) never touch a survivor's region list:
    -- chain the per-stage `getNumRegions!`/`getRegion!` frame facts and reassemble the array.
    opRegionsPreserved := by
      intro o oIn hne
      have hoNewCtxPat : o.InBounds newCtxPat.raw :=
        hCreated.inBounds_mono (GenericPtr.operation o) (by grind)
      have oIn' : o.InBounds rewriter'.ctx.raw := hSurviveOp o hne hoNewCtxPat
      have hoErase := PatternRewriter.eraseOp_ctx_eq herase ▸ oIn'
      -- (1) Region counts are framed across the whole pipeline.
      have hNum : o.getNumRegions! rewriter'.ctx.raw = o.getNumRegions! rewriter.ctx.raw := by
        have hcre : o.getNumRegions! newCtxPat.raw = o.getNumRegions! rewriter.ctx.raw :=
          hCreated.getNumRegions_eq oIn
        have hins : o.getNumRegions! s₁.ctx.raw = o.getNumRegions! newCtxPat.raw := by
          have h := Array.foldlM_option_invariant
            (P := fun b : PatternRewriter OpCode =>
              o.getNumRegions! b.ctx.raw = o.getNumRegions! newCtxPat.raw)
            (fun b a b' hh => by
              have := PatternRewriter.insertOp!_getNumRegions (o := o) hh
              constructor <;> intro hb <;> grind) hfold1
          exact h.mpr rfl
        have hrep : o.getNumRegions! s₂.ctx.raw = o.getNumRegions! s₁.ctx.raw := by
          have h := Array.foldlM_option_invariant
            (P := fun b : PatternRewriter OpCode =>
              o.getNumRegions! b.ctx.raw = o.getNumRegions! s₁.ctx.raw)
            (fun b a b' hh => by
              have hst : o.getNumRegions! b'.ctx.raw = o.getNumRegions! b.ctx.raw :=
                PatternRewriter.replaceValue!_getNumRegions hh
              constructor <;> intro hb <;> grind) hfold2
          exact h.mpr rfl
        have hers : o.getNumRegions! rewriter'.ctx.raw = o.getNumRegions! s₂.ctx.raw := by
          rw [PatternRewriter.eraseOp_ctx_eq herase]
          exact OperationPtr.getNumRegions!_wfRewriter_eraseOp hoErase
        exact hers.trans (hrep.trans (hins.trans hcre))
      -- (2) Region pointers are framed across the whole pipeline, index by index.
      have hReg : ∀ idx, o.getRegion! rewriter'.ctx.raw idx = o.getRegion! rewriter.ctx.raw idx := by
        intro idx
        have hcre : o.getRegion! newCtxPat.raw idx = o.getRegion! rewriter.ctx.raw idx :=
          hCreated.getRegion_eq oIn idx
        have hins : o.getRegion! s₁.ctx.raw idx = o.getRegion! newCtxPat.raw idx := by
          have h := Array.foldlM_option_invariant
            (P := fun b : PatternRewriter OpCode =>
              o.getRegion! b.ctx.raw idx = o.getRegion! newCtxPat.raw idx)
            (fun b a b' hh => by
              have := PatternRewriter.insertOp!_getRegion (o := o) (idx := idx) hh
              constructor <;> intro hb <;> grind) hfold1
          exact h.mpr rfl
        have hrep : o.getRegion! s₂.ctx.raw idx = o.getRegion! s₁.ctx.raw idx := by
          have h := Array.foldlM_option_invariant
            (P := fun b : PatternRewriter OpCode =>
              o.getRegion! b.ctx.raw idx = o.getRegion! s₁.ctx.raw idx)
            (fun b a b' hh => by
              have hst : o.getRegion! b'.ctx.raw idx = o.getRegion! b.ctx.raw idx :=
                PatternRewriter.replaceValue!_getRegion hh
              constructor <;> intro hb <;> grind) hfold2
          exact h.mpr rfl
        have hers : o.getRegion! rewriter'.ctx.raw idx = o.getRegion! s₂.ctx.raw idx := by
          rw [PatternRewriter.eraseOp_ctx_eq herase]
          exact OperationPtr.getRegion!_wfRewriter_eraseOp hoErase
        exact hers.trans (hrep.trans (hins.trans hcre))
      exact OperationPtr.regions_eq_of hNum hReg
    -- Op-list edits (create / insert / replace-value / erase) never touch a region's entry block:
    -- chain the per-stage `firstBlock` frame facts across the pipeline.
    regionFirstBlockPreserved := by
      intro r _
      have hcre : (r.get! newCtxPat.raw).firstBlock = (r.get! rewriter.ctx.raw).firstBlock :=
        hCreated.firstBlock_eq
      have hins : (r.get! s₁.ctx.raw).firstBlock = (r.get! newCtxPat.raw).firstBlock := by
        have h := Array.foldlM_option_invariant
          (P := fun b : PatternRewriter OpCode =>
            (r.get! b.ctx.raw).firstBlock = (r.get! newCtxPat.raw).firstBlock)
          (fun b a b' hh => by
            have := PatternRewriter.insertOp!_firstBlock (r := r) hh
            constructor <;> intro hb <;> grind) hfold1
        exact h.mpr rfl
      have hrep : (r.get! s₂.ctx.raw).firstBlock = (r.get! s₁.ctx.raw).firstBlock := by
        have h := Array.foldlM_option_invariant
          (P := fun b : PatternRewriter OpCode =>
            (r.get! b.ctx.raw).firstBlock = (r.get! s₁.ctx.raw).firstBlock)
          (fun b a b' hh => by
            have hst : (r.get! b'.ctx.raw).firstBlock = (r.get! b.ctx.raw).firstBlock :=
              PatternRewriter.replaceValue!_firstBlock hh
            constructor <;> intro hb <;> grind) hfold2
        exact h.mpr rfl
      have hers : (r.get! rewriter'.ctx.raw).firstBlock = (r.get! s₂.ctx.raw).firstBlock := by
        rw [PatternRewriter.eraseOp_ctx_eq herase]
        exact RegionPtr.firstBlock!_wfRewriter_eraseOp
      exact hers.trans (hrep.trans (hins.trans hcre))
    -- The enclosing operation of every survivor is preserved: block/op/region parents are framed
    -- across the whole pipeline, then assembled by `getParentOp!_eq_of`.
    getParentOpPreserved := by
      intro o enclosing oIn hne hpar
      have honotnew : o ∉ newOps := fun hm =>
        ((hReturnOps rewriter.ctx op newCtxPat newOps newValues hpat o).mp hm).2 oIn
      have oInPat : o.InBounds newCtxPat.raw := by
        have := hCreated.inBounds_mono (GenericPtr.operation o) (by grind); grind
      have oIn' : o.InBounds rewriter'.ctx.raw := hSurviveOp o hne oInPat
      -- Block-parent preservation (unconditional at every stage).
      have hblk : ∀ bl : BlockPtr,
          (bl.get! rewriter'.ctx.raw).parent = (bl.get! rewriter.ctx.raw).parent := by
        intro bl
        have hcre : (bl.get! newCtxPat.raw).parent = (bl.get! rewriter.ctx.raw).parent :=
          hCreated.blockParent_eq
        have hins : (bl.get! s₁.ctx.raw).parent = (bl.get! newCtxPat.raw).parent := by
          have h := Array.foldlM_option_invariant
            (P := fun b : PatternRewriter OpCode =>
              (bl.get! b.ctx.raw).parent = (bl.get! newCtxPat.raw).parent)
            (fun b a b' hh => by
              have := PatternRewriter.insertOp!_blockParent (block := bl) hh
              constructor <;> intro <;> grind) hfold1
          exact h.mpr rfl
        have hrep : (bl.get! s₂.ctx.raw).parent = (bl.get! s₁.ctx.raw).parent := by
          have h := Array.foldlM_option_invariant
            (P := fun b : PatternRewriter OpCode =>
              (bl.get! b.ctx.raw).parent = (bl.get! s₁.ctx.raw).parent)
            (fun b a b' hh => by
              have := PatternRewriter.replaceValue!_blockParent (block := bl) hh
              constructor <;> intro <;> grind) hfold2
          exact h.mpr rfl
        have hers : (bl.get! rewriter'.ctx.raw).parent = (bl.get! s₂.ctx.raw).parent := by
          rw [PatternRewriter.eraseOp_ctx_eq herase]; exact BlockPtr.parent!_wfRewriter_eraseOp
        exact hers.trans (hrep.trans (hins.trans hcre))
      -- Op-parent preservation for the survivor `o` (it is neither created, inserted, nor erased).
      have hop : (o.get! rewriter'.ctx.raw).parent = (o.get! rewriter.ctx.raw).parent := by
        have hcre : (o.get! newCtxPat.raw).parent = (o.get! rewriter.ctx.raw).parent :=
          hCreated.opParent_eq oIn
        have hins : (o.get! s₁.ctx.raw).parent = (o.get! newCtxPat.raw).parent := by
          have hL := hfold1; rw [← Array.foldlM_toList] at hL
          have h := List.foldlM_option_invariant_mem (l := newOps.toList)
            (P := fun b : PatternRewriter OpCode =>
              (o.get! b.ctx.raw).parent = (o.get! newCtxPat.raw).parent)
            (fun b a b' hmem hh => by
              have hane : o ≠ a := by rintro rfl; exact honotnew (by simpa using hmem)
              have := PatternRewriter.insertOp!_opParent (o := o) hh hane
              constructor <;> intro <;> grind) hL
          exact h.mpr rfl
        have hrep : (o.get! s₂.ctx.raw).parent = (o.get! s₁.ctx.raw).parent := by
          have h := Array.foldlM_option_invariant
            (P := fun b : PatternRewriter OpCode =>
              (o.get! b.ctx.raw).parent = (o.get! s₁.ctx.raw).parent)
            (fun b a b' hh => by
              have := PatternRewriter.replaceValue!_opParent (o := o) hh
              constructor <;> intro <;> grind) hfold2
          exact h.mpr rfl
        have hoErase := PatternRewriter.eraseOp_ctx_eq herase ▸ oIn'
        have hers : (o.get! rewriter'.ctx.raw).parent = (o.get! s₂.ctx.raw).parent := by
          rw [PatternRewriter.eraseOp_ctx_eq herase, OperationPtr.parent!_wfRewriter_eraseOp hoErase,
            if_neg hne]
        exact hers.trans (hrep.trans (hins.trans hcre))
      -- Region-parent preservation for parented in-bounds regions.
      have hrgn : ∀ r : RegionPtr, r.InBounds rewriter.ctx.raw →
          (r.get! rewriter.ctx.raw).parent ≠ none →
          (r.get! rewriter'.ctx.raw).parent = (r.get! rewriter.ctx.raw).parent := by
        intro r rIn hrne
        have hcre : (r.get! newCtxPat.raw).parent = (r.get! rewriter.ctx.raw).parent :=
          hCreated.regionParent_eq_of_parented rIn hrne
        have hins : (r.get! s₁.ctx.raw).parent = (r.get! newCtxPat.raw).parent := by
          have h := Array.foldlM_option_invariant
            (P := fun b : PatternRewriter OpCode =>
              (r.get! b.ctx.raw).parent = (r.get! newCtxPat.raw).parent)
            (fun b a b' hh => by
              have := PatternRewriter.insertOp!_regionParent (r := r) hh
              constructor <;> intro <;> grind) hfold1
          exact h.mpr rfl
        have hrep : (r.get! s₂.ctx.raw).parent = (r.get! s₁.ctx.raw).parent := by
          have h := Array.foldlM_option_invariant
            (P := fun b : PatternRewriter OpCode =>
              (r.get! b.ctx.raw).parent = (r.get! s₁.ctx.raw).parent)
            (fun b a b' hh => by
              have := PatternRewriter.replaceValue!_regionParent (r := r) hh
              constructor <;> intro <;> grind) hfold2
          exact h.mpr rfl
        have hers : (r.get! rewriter'.ctx.raw).parent = (r.get! s₂.ctx.raw).parent := by
          rw [PatternRewriter.eraseOp_ctx_eq herase]; exact RegionPtr.parent!_wfRewriter_eraseOp
        exact hers.trans (hrep.trans (hins.trans hcre))
      exact OperationPtr.getParentOp!_eq_of rewriter.ctx.wellFormed.inBounds oIn hop hblk hrgn hpar
    -- `op` is not a function: it has no regions, so in particular not exactly one.
    opNotFunction := by simp [hOpRegions]
  }
  -- **`newOps` frame** (PR 8): each created `newOp` carries its intrinsic data unchanged through the
  -- insert/replace/erase pipeline, and — provided its operands survive into `rewriter'.ctx` — the
  -- redirect fold is inert on it, because the only values the fold rewrites are `op`'s results, which
  -- are erased and hence out of bounds in `rewriter'.ctx`.
  refine ⟨block, pre, post, blockIn, blockIn', hOpParent, hR, ?_⟩
  intro o ho
  have hoIn' : o.InBounds rewriter'.ctx.raw := hR.newOpsInBounds o (by simpa using ho)
  have hoNewCtxPat : o.InBounds newCtxPat.raw :=
    ((hReturnOps rewriter.ctx op newCtxPat newOps newValues hpat o).mp (by simpa using ho)).1
  have hoErase := PatternRewriter.eraseOp_ctx_eq herase ▸ hoIn'
  -- (1) Intrinsic data is framed from `newCtxPat` (creation) through the insert/replace folds and the
  -- final erase.
  have hins : o.SameIntrinsic newCtxPat.raw s₁.ctx.raw := by
    have h := Array.foldlM_option_invariant
      (P := fun b : PatternRewriter OpCode => o.SameIntrinsic newCtxPat.raw b.ctx.raw)
      (fun b a b' hh =>
        ⟨fun hb => hb.trans (PatternRewriter.insertOp!_sameIntrinsic hh).symm,
         fun hb => hb.trans (PatternRewriter.insertOp!_sameIntrinsic hh)⟩) hfold1
    exact h.mpr OperationPtr.SameIntrinsic.rfl
  have hrep : o.SameIntrinsic s₁.ctx.raw s₂.ctx.raw := by
    have h := Array.foldlM_option_invariant
      (P := fun b : PatternRewriter OpCode => o.SameIntrinsic s₁.ctx.raw b.ctx.raw)
      (fun b a b' hh => by
        have hst : o.SameIntrinsic b.ctx.raw b'.ctx.raw :=
          PatternRewriter.replaceValue!_sameIntrinsic hh
        exact ⟨fun hb => hb.trans hst.symm, fun hb => hb.trans hst⟩) hfold2
    exact h.mpr OperationPtr.SameIntrinsic.rfl
  have hers : o.SameIntrinsic s₂.ctx.raw rewriter'.ctx.raw := by
    rw [PatternRewriter.eraseOp_ctx_eq herase]
    exact ⟨OperationPtr.getOpType!_wfRewriter_eraseOp hoErase,
      fun _ => OperationPtr.getProperties!_wfRewriter_eraseOp hoErase,
      OperationPtr.getNumResults!_wfRewriter_eraseOp hoErase,
      OperationPtr.getSuccessors!_wfRewriter_eraseOp hoErase,
      OperationPtr.getResultTypes!_wfRewriter_eraseOp hoErase⟩
  refine ⟨hins.trans (hrep.trans hers), ?_⟩
  -- (2) Operand equality under the "operands survive" premise: the redirect fold is the identity.
  intro hInPrem
  have hoS1 : o.InBounds s₁.ctx.raw := by
    have h := Array.foldlM_option_invariant
      (P := fun b : PatternRewriter OpCode => (GenericPtr.operation o).InBounds b.ctx.raw)
      (fun b a b' hh => PatternRewriter.insertOp!_ctx_inBounds hh) hfold1
    grind
  have hopsErase : o.getOperands! rewriter'.ctx.raw = o.getOperands! s₂.ctx.raw := by
    rw [PatternRewriter.eraseOp_ctx_eq herase]
    exact OperationPtr.getOperands!_wfRewriter_eraseOp hoErase
  have hopsRepl : o.getOperands! s₂.ctx.raw
      = (newValues.zipIdx.toList).foldl
          (fun arr q => arr.map (fun v => if v = (op.getResult q.2 : ValuePtr) then q.1 else v))
          (o.getOperands! s₁.ctx.raw) :=
    PatternRewriter.foldlM_replaceValue_getOperands
      (hf := fun b q b' hfa => PatternRewriter.replaceValue!_eq_some hfa)
      hfold2L hoS1
  have hopsIns : o.getOperands! s₁.ctx.raw = o.getOperands! newCtxPat.raw := by
    have h := Array.foldlM_option_invariant
      (P := fun b : PatternRewriter OpCode =>
        o.getOperands! b.ctx.raw = o.getOperands! newCtxPat.raw)
      (fun b a b' hh => by
        have := PatternRewriter.insertOp!_getOperands (o := o) hh
        constructor <;> intro hb <;> grind) hfold1
    exact h.mpr rfl
  -- `op`'s results are out of bounds in `rewriter'.ctx` (op erased), so a surviving operand is never
  -- one of them.
  have hResNotIn : ∀ m, ¬ ((op.getResult m : ValuePtr)).InBounds rewriter'.ctx.raw := by
    intro m hIn
    rw [ValuePtr.inBounds_opResult, OpResultPtr.inBounds_def] at hIn
    obtain ⟨hop, _⟩ := hIn
    simp only [OperationPtr.getResult_def] at hop
    exact hR.opErased hop
  rw [hopsErase, hopsRepl, hopsIns, List.foldl_arrayMap_fusion]
  symm
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_map]
    apply fold_replaceResult_eq_self
    intro q _ hcontra
    exact hResNotIn q.2 (hcontra ▸ hInPrem _ (Array.getElem_mem h2))

/-! ### PR 8 foundation: list interpretation depends only on each op's local data

`interpretOp` reads the context only through an operation's *local* data — its operands, type,
properties, result types, successors, and result pointers — plus the variable map and memory. It
never consults `.parent`, `.next`, or block membership. So if those data fields agree across two
contexts and the states share the same underlying variable map and memory, the runs are *literally
equal* (projected onto the context-independent data: the variable map, the memory, and the optional
control-flow action). This `SameData` frame is the key to PR 8: the driver's edits (insert `newOps`
before `op`, redirect `op`'s results, erase `op`) are inert on `newOps`' interpreted data, so a run
of `newOps` transports unchanged from the create-only `newCtxPat` to the inserted/erased
`rewriter'.ctx`. -/

/-- The context-independent data of an interpreter-state/action result: the variable map, the memory,
and the optional control-flow action. Two `interpretOp`/`interpretOpList` results "agree as data" when
their projections under `interpProj` are equal — this is meaningful *across* contexts, where the
result states have different types but a common underlying `ExtHashMap`/`MemoryState`. -/
def interpProj {ctx : WfIRContext OpCode} :
    Interp (InterpreterState ctx × Option ControlFlowAction) →
    Option (UBOr (Std.ExtHashMap ValuePtr RuntimeValue × MemoryState × Option ControlFlowAction)) :=
  Option.map (UBOr.map (fun p => (p.1.variables.variables, p.1.memory, p.2)))

/-- Cross-context agreement of `setVar?` on the underlying variable map: with the same starting map
and the same target-type (`getType!` agrees), the conformance check and the insert coincide. -/
theorem VariableState.setVar?_variables_eq_of_dataEq
    {ctxA ctxB : WfIRContext OpCode} {var : ValuePtr} {val : RuntimeValue}
    {varStateA : VariableState ctxA} {varStateB : VariableState ctxB} {iA iB}
    (hVars : varStateA.variables = varStateB.variables)
    (hType : var.getType! ctxA.raw = var.getType! ctxB.raw) :
    (varStateA.setVar? var val iA).map (·.variables)
      = (varStateB.setVar? var val iB).map (·.variables) := by
  simp only [VariableState.setVar?, hType, hVars]
  split <;> simp

/-- Cross-context agreement of `setResultValues?` on the underlying variable map: the loop sets the
context-independent result pointers `op.getResult i` to the same values with the same per-result
conformance check (`getType!` agrees), so it produces the same map (or fails on both sides). -/
theorem VariableState.setResultValues?_loop_variables_eq_of_dataEq
    {ctxA ctxB : WfIRContext OpCode} {op : OperationPtr} {resValues : Array RuntimeValue}
    {varStateA : VariableState ctxA} {varStateB : VariableState ctxB}
    (hVars : varStateA.variables = varStateB.variables)
    (hType : ∀ i, (ValuePtr.opResult (op.getResult i)).getType! ctxA.raw
                = (ValuePtr.opResult (op.getResult i)).getType! ctxB.raw)
    {idx : Nat} {iA hiA hsA iB hiB hsB} :
    (varStateA.setResultValues?_loop op resValues idx iA hiA hsA).map (·.variables)
      = (varStateB.setResultValues?_loop op resValues idx iB hiB hsB).map (·.variables) := by
  induction idx generalizing varStateA varStateB with
  | zero => simp [VariableState.setResultValues?_loop, hVars]
  | succ i ih =>
    simp only [VariableState.setResultValues?_loop, Option.bind_eq_bind]
    have hstep := VariableState.setVar?_variables_eq_of_dataEq (val := resValues[i])
      (varStateA := varStateA) (varStateB := varStateB) (iA := by grind) (iB := by grind)
      hVars (hType i)
    rcases hA : varStateA.setVar? (op.getResult i) resValues[i] with _ | varStateA' <;>
      rcases hB : varStateB.setVar? (op.getResult i) resValues[i] with _ | varStateB' <;>
      simp only [hA, hB, Option.map_none, Option.map_some] at hstep
    · rfl
    · exact absurd hstep (by simp)
    · exact absurd hstep (by simp)
    · exact ih (by simpa using hstep)

/-- Cross-context agreement of `setResultValues?` on the underlying variable map. -/
theorem VariableState.setResultValues?_variables_eq_of_dataEq
    {ctxA ctxB : WfIRContext OpCode} {op : OperationPtr} {resValues : Array RuntimeValue}
    {varStateA : VariableState ctxA} {varStateB : VariableState ctxB} {iA iB}
    (hVars : varStateA.variables = varStateB.variables)
    (hNum : op.getNumResults! ctxA.raw = op.getNumResults! ctxB.raw)
    (hType : ∀ i, (ValuePtr.opResult (op.getResult i)).getType! ctxA.raw
                = (ValuePtr.opResult (op.getResult i)).getType! ctxB.raw) :
    (varStateA.setResultValues? op resValues iA).map (·.variables)
      = (varStateB.setResultValues? op resValues iB).map (·.variables) := by
  simp only [VariableState.setResultValues?, hNum]
  split
  · exact VariableState.setResultValues?_loop_variables_eq_of_dataEq hVars hType
  · rfl

/-- **`interpretOp` data-equality frame.** If an operation's local data (operands, type, properties,
result types, successors) and its result pointers' types agree across two contexts, and the two
states share the same underlying variable map and memory, then the two `interpretOp` runs agree under
`interpProj` — i.e. they produce the same variable map, memory, and control-flow action (or both fail
identically). No parents/dominance involved. -/
theorem interpretOp_interpProj_eq_of_dataEq
    {ctxA ctxB : WfIRContext OpCode} {op : OperationPtr} {oInA : op.InBounds ctxA.raw}
    {oInB : op.InBounds ctxB.raw}
    (hOpType : op.getOpType! ctxA.raw = op.getOpType! ctxB.raw)
    (hProps : op.getProperties! ctxA.raw (op.getOpType! ctxA.raw)
            = hOpType ▸ op.getProperties! ctxB.raw (op.getOpType! ctxB.raw))
    (hResTypes : op.getResultTypes! ctxA.raw = op.getResultTypes! ctxB.raw)
    (hSucc : op.getSuccessors! ctxA.raw = op.getSuccessors! ctxB.raw)
    (hOperands : op.getOperands! ctxA.raw = op.getOperands! ctxB.raw)
    (hNum : op.getNumResults! ctxA.raw = op.getNumResults! ctxB.raw)
    (hType : ∀ i, (ValuePtr.opResult (op.getResult i)).getType! ctxA.raw
                = (ValuePtr.opResult (op.getResult i)).getType! ctxB.raw)
    {sA : InterpreterState ctxA} {sB : InterpreterState ctxB}
    (hVars : sA.variables.variables = sB.variables.variables)
    (hMem : sA.memory = sB.memory) :
    interpProj (interpretOp op sA oInA) = interpProj (interpretOp op sB oInB) := by
  -- Operand values agree: same operand pointers (`hOperands`), same map (`getVar?` is a pure lookup).
  have hgv : sA.variables.getVar? = sB.variables.getVar? := by
    funext v; simp only [VariableState.getVar?, hVars]
  have hOps : sA.variables.getOperandValues op = sB.variables.getOperandValues op := by
    simp only [VariableState.getOperandValues, hOperands, hgv]
  -- The pure `interpretOp'` step agrees (same opType/props/resultTypes/successors/operands/memory).
  have hInterp : ∀ ov mem, op.interpret ctxA.raw ov mem = op.interpret ctxB.raw ov mem := by
    intro ov mem
    simp only [OperationPtr.interpret, hResTypes, hSucc]
    exact interpretOp'_opType_cast hOpType hProps
  -- `setResultValues?` agrees on the underlying map for any result values / in-bounds proofs.
  have hsetMap : ∀ (rv : Array RuntimeValue) p q,
      (sA.variables.setResultValues? op rv p).map (·.variables)
        = (sB.variables.setResultValues? op rv q).map (·.variables) :=
    fun rv _ _ => VariableState.setResultValues?_variables_eq_of_dataEq hVars hNum hType
  -- A successful (`ok`) run is mirrored across the two contexts, componentwise (operands agree, the
  -- pure step agrees, memory agrees, and `setResultValues?` agrees on the variable map). Stated
  -- generically so it applies in *both* directions (the four data hypotheses are symmetric).
  have okMirror : ∀ {ctx1 ctx2 : WfIRContext OpCode} (s1 : InterpreterState ctx1)
      (s2 : InterpreterState ctx2) (oi1 : op.InBounds ctx1.raw) (oi2 : op.InBounds ctx2.raw) st1 act1,
      s1.variables.getOperandValues op = s2.variables.getOperandValues op →
      (∀ ov m, op.interpret ctx1.raw ov m = op.interpret ctx2.raw ov m) →
      s1.memory = s2.memory →
      (∀ rv p q, (s1.variables.setResultValues? op rv p).map (·.variables)
        = (s2.variables.setResultValues? op rv q).map (·.variables)) →
      interpretOp op s1 oi1 = some (.ok (st1, act1)) →
      ∃ st2, interpretOp op s2 oi2 = some (.ok (st2, act1)) ∧
        st2.variables.variables = st1.variables.variables ∧ st2.memory = st1.memory := by
    intro ctx1 ctx2 s1 s2 oi1 oi2 st1 act1 hop hin hmem hset h
    obtain ⟨ov, rv, mem', vs', hov, hint, hsetv, rfl⟩ := interpretOp_some_iff.mp h
    have hov2 : s2.variables.getOperandValues op = some ov := hop ▸ hov
    have hint2 : op.interpret ctx2.raw ov s2.memory = some (.ok (rv, mem', act1)) := by
      rw [← hin ov s2.memory, ← hmem]; exact hint
    have hsetv' : s1.variables.setResultValues? op rv oi1 = some vs' := hsetv
    have hsetEq := hset rv oi1 oi2
    rw [hsetv', Option.map_some] at hsetEq
    rcases hsB : s2.variables.setResultValues? op rv oi2 with _ | vs2
    · rw [hsB, Option.map_none] at hsetEq; exact absurd hsetEq.symm (by simp)
    · refine ⟨⟨vs2, mem'⟩, interpretOp_some_iff.mpr ⟨ov, rv, mem', vs2, hov2, hint2, hsB, rfl⟩, ?_, rfl⟩
      rw [hsB, Option.map_some] at hsetEq
      exact (Option.some_inj.mp hsetEq).symm
  -- A `ub` run is likewise mirrored (operands agree, the pure step's `ub` agrees).
  have ubMirror : ∀ {ctx1 ctx2 : WfIRContext OpCode} (s1 : InterpreterState ctx1)
      (s2 : InterpreterState ctx2) (oi1 : op.InBounds ctx1.raw) (oi2 : op.InBounds ctx2.raw),
      s1.variables.getOperandValues op = s2.variables.getOperandValues op →
      (∀ ov m, op.interpret ctx1.raw ov m = op.interpret ctx2.raw ov m) →
      s1.memory = s2.memory →
      interpretOp op s1 oi1 = some .ub → interpretOp op s2 oi2 = some .ub := by
    intro ctx1 ctx2 s1 s2 oi1 oi2 hop hin hmem h
    obtain ⟨ov, hov, hint⟩ := interpretOp_ub_iff.mp h
    refine interpretOp_ub_iff.mpr ⟨ov, hop ▸ hov, ?_⟩
    rw [← hin ov s2.memory, ← hmem]; exact hint
  -- Dispatch on the source result and mirror onto the target.
  rcases hA : interpretOp op sA oInA with _ | (⟨stA, actA⟩ | _)
  · -- A `none`: the target is `none` too — otherwise mirroring back would make A succeed.
    rcases hB : interpretOp op sB oInB with _ | (⟨stB, actB⟩ | _)
    · simp [interpProj]
    · obtain ⟨stA', hA', _⟩ := okMirror sB sA oInB oInA stB actB hOps.symm
        (fun ov m => (hInterp ov m).symm) hMem.symm (fun rv p q => (hsetMap rv q p).symm) hB
      rw [hA] at hA'; exact absurd hA' (by simp)
    · exact absurd (ubMirror sB sA oInB oInA hOps.symm (fun ov m => (hInterp ov m).symm) hMem.symm hB
        |>.symm.trans hA) (by simp)
  · obtain ⟨stB, hB, hvars, hmem⟩ := okMirror sA sB oInA oInB stA actA hOps hInterp hMem hsetMap hA
    simp only [interpProj, hB, Option.map_some, UBOr.map, hvars, hmem]
  · rw [ubMirror sA sB oInA oInB hOps hInterp hMem hA]
    rfl

/-- Two interpreter states "agree as data" when they share the underlying variable map and memory.
Phantom-typed by their (possibly different) contexts. -/
def InterpreterState.SameData {ctxA ctxB : WfIRContext OpCode}
    (sA : InterpreterState ctxA) (sB : InterpreterState ctxB) : Prop :=
  sA.variables.variables = sB.variables.variables ∧ sA.memory = sB.memory

/-- The local data of an operation agrees across two contexts: its type, properties, result types,
successors, operand pointers, result count, and result-pointer types coincide. This is exactly what
`interpretOp`/`interpretOpList` consume, so it is the precondition of the data-equality frame. -/
structure OpDataEq (op : OperationPtr) (ctxA ctxB : WfIRContext OpCode) : Prop where
  opType : op.getOpType! ctxA.raw = op.getOpType! ctxB.raw
  props : op.getProperties! ctxA.raw (op.getOpType! ctxA.raw)
            = opType ▸ op.getProperties! ctxB.raw (op.getOpType! ctxB.raw)
  resTypes : op.getResultTypes! ctxA.raw = op.getResultTypes! ctxB.raw
  succ : op.getSuccessors! ctxA.raw = op.getSuccessors! ctxB.raw
  operands : op.getOperands! ctxA.raw = op.getOperands! ctxB.raw
  numResults : op.getNumResults! ctxA.raw = op.getNumResults! ctxB.raw
  resElemType : ∀ i, (ValuePtr.opResult (op.getResult i)).getType! ctxA.raw
                  = (ValuePtr.opResult (op.getResult i)).getType! ctxB.raw

/-- `interpProj` inverts at an `ok` outcome: the projection is `ok (vars, mem, act)` exactly when the
run is `ok (st, act)` for some state `st` whose data is `(vars, mem)`. -/
theorem interpProj_eq_ok_iff {ctx : WfIRContext OpCode}
    {X : Interp (InterpreterState ctx × Option ControlFlowAction)}
    {vars : Std.ExtHashMap ValuePtr RuntimeValue} {mem : MemoryState} {act : Option ControlFlowAction} :
    interpProj X = some (.ok (vars, mem, act)) ↔
    ∃ st, X = some (.ok (st, act)) ∧ st.variables.variables = vars ∧ st.memory = mem := by
  rcases X with _ | (⟨st, a⟩ | _) <;> simp [interpProj, UBOr.map] <;> grind

/-- Per-op `ok`-transport: under `OpDataEq` and same-data entry states, a source `ok` step is mirrored
by a target `ok` step with the same control-flow action and same-data result. -/
theorem interpretOp_sameData_transport {ctxA ctxB : WfIRContext OpCode} {op : OperationPtr}
    {sA : InterpreterState ctxA} {sB : InterpreterState ctxB}
    (hData : OpDataEq op ctxA ctxB) (hsame : sA.SameData sB)
    {oInA : op.InBounds ctxA.raw} {oInB : op.InBounds ctxB.raw}
    {st : InterpreterState ctxA} {act : Option ControlFlowAction}
    (h : interpretOp op sA oInA = some (.ok (st, act))) :
    ∃ st', interpretOp op sB oInB = some (.ok (st', act)) ∧ st.SameData st' := by
  have he := interpretOp_interpProj_eq_of_dataEq (oInA := oInA) (oInB := oInB)
    hData.opType hData.props hData.resTypes hData.succ hData.operands hData.numResults
    hData.resElemType hsame.1 hsame.2
  rw [h] at he
  have hP : interpProj (interpretOp op sB oInB) = some (.ok (st.variables.variables, st.memory, act)) := by
    rw [← he]; simp [interpProj, UBOr.map]
  obtain ⟨st', hB, hv, hm⟩ := interpProj_eq_ok_iff.mp hP
  exact ⟨st', hB, hv.symm, hm.symm⟩

/-- **`interpretOpList` data-equality transport.** Over an identical op list whose every operation has
matching local data across the two contexts, a successful (`ok`) run transports from same-data entry
states to same-data result states, preserving the control-flow action. The driver's edits are inert on
`newOps`' data, so this is what carries a `newOps` run from `newCtxPat` to `rewriter'.ctx`. -/
theorem interpretOpList_sameData_transport {ctxA ctxB : WfIRContext OpCode} {ops : List OperationPtr}
    (oInA : ∀ o ∈ ops, o.InBounds ctxA.raw) (oInB : ∀ o ∈ ops, o.InBounds ctxB.raw)
    (hData : ∀ o ∈ ops, OpDataEq o ctxA ctxB)
    {sA : InterpreterState ctxA} {sB : InterpreterState ctxB} (hsame : sA.SameData sB)
    {sA2 : InterpreterState ctxA} {cf : Option ControlFlowAction}
    (h : interpretOpList ops sA oInA = some (.ok (sA2, cf))) :
    ∃ sB2, interpretOpList ops sB oInB = some (.ok (sB2, cf)) ∧ sA2.SameData sB2 := by
  induction ops generalizing sA sB with
  | nil =>
    rw [interpretOpList_nil] at h
    injection h with h1; injection h1 with h2; rw [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨sB, interpretOpList_nil, hsame⟩
  | cons a l ih =>
    rw [interpretOpList_cons] at h
    rcases hA : interpretOp a sA (oInA a (by simp)) with _ | (⟨sMid, act⟩ | _)
    · rw [hA] at h; injection h
    · obtain ⟨sMidB, hB, hsmid⟩ :=
        interpretOp_sameData_transport (hData a (by simp)) hsame (oInB := oInB a (by simp)) hA
      rw [interpretOpList_cons, hB]
      rw [hA] at h
      cases act with
      | none =>
        exact ih (fun o ho => oInA o (by simp [ho])) (fun o ho => oInB o (by simp [ho]))
          (fun o ho => hData o (by simp [ho])) hsmid h
      | some c =>
        injection h with h1; injection h1 with h2; rw [Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨sMidB, rfl, hsmid⟩
    · rw [hA] at h; injection h with h1; injection h1

/-- Assemble `OpDataEq` from `SameIntrinsic` (which the driver's edits preserve for a surviving op)
plus agreement of the operand pointers (which must be established separately, since the redirect fold
rewrites operands). The intrinsic fields come straight from `SameIntrinsic` (note its reversed
direction); `resElemType` reads the per-index result type off `getResultTypes!` in range and a
defaulted record out of range. -/
theorem OpDataEq.of_sameIntrinsic {op : OperationPtr} {ctxA ctxB : WfIRContext OpCode}
    (hIntr : op.SameIntrinsic ctxA.raw ctxB.raw)
    (hOperands : op.getOperands! ctxA.raw = op.getOperands! ctxB.raw) :
    OpDataEq op ctxA ctxB where
  opType := hIntr.1.symm
  props := by
    have hty : op.getOpType! ctxA.raw = op.getOpType! ctxB.raw := hIntr.1.symm
    have hprops := hIntr.2.1 (op.getOpType! ctxB.raw)
    refine eq_of_heq (HEq.trans ?_ (eqRec_heq _ _).symm)
    rw [hprops, hty]
  resTypes := hIntr.2.2.2.2.symm
  succ := hIntr.2.2.2.1.symm
  operands := hOperands
  numResults := hIntr.2.2.1.symm
  resElemType := by
    intro i
    rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult]
    by_cases hi : i < op.getNumResults! ctxA.raw
    · have hA := OperationPtr.getResultTypes!.getElem!_eq (op := op) (ctx := ctxA.raw) hi
      have hB := OperationPtr.getResultTypes!.getElem!_eq (op := op) (ctx := ctxB.raw)
        (by rw [← hIntr.2.2.1.symm]; exact hi)
      rw [← hA, ← hB, hIntr.2.2.2.2.symm]
    · -- Out of range: the `getResult` pointer is out of bounds in *both* contexts (result counts
      -- agree), so each `get!` reads the same defaulted record.
      have hnA : (op.getResult i).get! ctxA.raw = default := by
        apply OpResultPtr.get!_of_not_inBounds
        rw [OpResultPtr.inBounds_def]
        rintro ⟨hop, hlt⟩
        simp only [OperationPtr.getResult_def] at hop hlt
        rw [← OperationPtr.getNumResults!_eq_getNumResults hop] at hlt
        omega
      have hnB : (op.getResult i).get! ctxB.raw = default := by
        apply OpResultPtr.get!_of_not_inBounds
        rw [OpResultPtr.inBounds_def]
        rintro ⟨hop, hlt⟩
        simp only [OperationPtr.getResult_def] at hop hlt
        rw [← OperationPtr.getNumResults!_eq_getNumResults hop, hIntr.2.2.1] at hlt
        omega
      rw [hnA, hnB]

/-- A successful (`ok`) `interpretOp` step forces every operand of `op` to be live in the entry
state's variable map (`getOperandValues` reads them all). -/
theorem interpretOp_operands_mem_of_ok {ctx : WfIRContext OpCode} {op : OperationPtr}
    {s : InterpreterState ctx} {oIn : op.InBounds ctx.raw}
    {st : InterpreterState ctx} {act : Option ControlFlowAction}
    (h : interpretOp op s oIn = some (.ok (st, act))) :
    ∀ v ∈ op.getOperands! ctx.raw, v ∈ s.variables.variables := by
  obtain ⟨ov, rv, mem', vs', hov, -, -, -⟩ := interpretOp_some_iff.mp h
  obtain ⟨hsize, hgv⟩ := VariableState.getOperandValues_eq_some_iff.mp hov
  intro v hv
  obtain ⟨i, hi, hiv⟩ := OperationPtr.getOperands!.mem_iff_exists_index.mp hv
  have := hgv i hi
  rw [hiv] at this
  rw [Std.ExtHashMap.mem_iff_isSome_getElem?]; rw [VariableState.getVar?] at this
  rw [this]; rfl

/-- **`interpretOpList` data-equality transport, redirect variant.** Same as
`interpretOpList_sameData_transport`, but `OpDataEq` need not hold unconditionally: it suffices that
each op's data agrees *once its operands are known to be in bounds of `ctxB`* (`hData`), together with
a "clean redirect" hypothesis (`hClean`) that the operands themselves agree under that in-bounds
premise. During a successful source run every executed op's operands are live in the shared variable
map, hence in bounds of `ctxB` (via the target state's `variablesIn`), so the redirect is inert. -/
theorem interpretOpList_sameData_transport_redirect {ctxA ctxB : WfIRContext OpCode}
    {ops : List OperationPtr}
    (oInA : ∀ o ∈ ops, o.InBounds ctxA.raw) (oInB : ∀ o ∈ ops, o.InBounds ctxB.raw)
    (hClean : ∀ o ∈ ops, (∀ v ∈ o.getOperands! ctxA.raw, v.InBounds ctxB.raw) →
      o.getOperands! ctxA.raw = o.getOperands! ctxB.raw)
    (hData : ∀ o ∈ ops, o.getOperands! ctxA.raw = o.getOperands! ctxB.raw → OpDataEq o ctxA ctxB)
    {sA : InterpreterState ctxA} {sB : InterpreterState ctxB} (hsame : sA.SameData sB)
    {sA2 : InterpreterState ctxA} {cf : Option ControlFlowAction}
    (h : interpretOpList ops sA oInA = some (.ok (sA2, cf))) :
    ∃ sB2, interpretOpList ops sB oInB = some (.ok (sB2, cf)) ∧ sA2.SameData sB2 := by
  induction ops generalizing sA sB with
  | nil =>
    rw [interpretOpList_nil] at h
    injection h with h1; injection h1 with h2; rw [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨sB, interpretOpList_nil, hsame⟩
  | cons a l ih =>
    rw [interpretOpList_cons] at h
    rcases hA : interpretOp a sA (oInA a (by simp)) with _ | (⟨sMid, act⟩ | _)
    · rw [hA] at h; injection h
    · -- Derive `OpDataEq a ctxA ctxB`: `a`'s operands are live in `sA`'s map, hence (via `SameData`
      -- and `sB`'s `variablesIn`) in bounds of `ctxB`; `hClean`/`hData` then apply.
      have hmem := interpretOp_operands_mem_of_ok hA
      have hInB : ∀ v ∈ a.getOperands! ctxA.raw, v.InBounds ctxB.raw := by
        intro v hv
        exact sB.variables.variablesIn v (hsame.1 ▸ hmem v hv)
      have hData' : OpDataEq a ctxA ctxB := hData a (by simp) (hClean a (by simp) hInB)
      obtain ⟨sMidB, hB, hsmid⟩ :=
        interpretOp_sameData_transport hData' hsame (oInB := oInB a (by simp)) hA
      rw [interpretOpList_cons, hB]
      rw [hA] at h
      cases act with
      | none =>
        exact ih (fun o ho => oInA o (by simp [ho])) (fun o ho => oInB o (by simp [ho]))
          (fun o ho => hClean o (by simp [ho])) (fun o ho => hData o (by simp [ho])) hsmid h
      | some c =>
        injection h with h1; injection h1 with h2; rw [Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨sMidB, rfl, hsmid⟩
    · rw [hA] at h; injection h with h1; injection h1

/-! ### PR 9, final bridge: the driver refines every module

Composing the two endpoints — `RewrittenAt.of_fromLocalRewrite` (the driver's net edit *is* a
`RewrittenAt` instance) and `RewrittenAt.isModuleRefinedBy` (a `RewrittenAt` instance refines every
module) — gives the headline driver-level soundness statement: running `fromLocalRewrite` for a
matched, in-bounds `op` on a `Valid` pattern over a verified, dominance-wellformed context refines
every module.

This is the **composition skeleton**: the easy side-conditions of `isModuleRefinedBy` are discharged
here (`ctxVerif`/`hCtxDom` are the source hypotheses; `newCtxVerif` is the pattern's
`rewritePreservesVerified` obligation applied to the driver run). The remaining four are the
*semantic* bridges, left as `sorry` for now:
* `hOpSim` — bridge the pattern's value-level `PreservesSemantics` to the scoped
  `OpStepSimulation` on `hRW.σ` (requires `hRW.σ = LocalRewritePattern.mapping hpat`);
* `hSrcSplit`/`hTgtSplit` — every verified block is `front ++ [terminator]` with `front` never
  yielding a control-flow action;
* `hSrcInv`/`hTgtInv` — the function-entry base case: the empty state with entry block-arguments set
  satisfies `EquationLemmaAt`/`DefinesDominating` at the entry point.
-/
theorem RewrittenAt.isModuleRefinedBy_of_fromLocalRewrite
    {pattern : LocalRewritePattern OpCode}
    (hValid : pattern.Valid)
    (hSrcDom : rewriter.ctx.Dom)
    (hSrcVerif : rewriter.ctx.Verified)
    (hpat : pattern rewriter.ctx op = some (newCtxPat, some (newOps, newValues)))
    (hdriver : RewritePattern.fromLocalRewrite pattern rewriter op opInBounds = some rewriter')
    (hSrcSplit : ∀ (b : BlockPtr) (bIn : b.InBounds rewriter.ctx.raw),
      ∃ (front : List OperationPtr) (term : OperationPtr)
        (frontIn : ∀ o ∈ front, o.InBounds rewriter.ctx.raw) (_termIn : term.InBounds rewriter.ctx.raw),
        (b.operationList rewriter.ctx.raw rewriter.ctx.wellFormed bIn).toList = front ++ [term] ∧
        (∀ (s s' : InterpreterState rewriter.ctx) (cf : ControlFlowAction),
            interpretOpList front s frontIn ≠ some (.ok (s', some cf))))
    (hTgtSplit : ∀ (b : BlockPtr) (bIn' : b.InBounds rewriter'.ctx.raw),
      ∃ (front : List OperationPtr) (term : OperationPtr)
        (frontIn : ∀ o ∈ front, o.InBounds rewriter'.ctx.raw) (_termIn : term.InBounds rewriter'.ctx.raw),
        (b.operationList rewriter'.ctx.raw rewriter'.ctx.wellFormed bIn').toList = front ++ [term] ∧
        (∀ (s s' : InterpreterState rewriter'.ctx) (cf : ControlFlowAction),
            interpretOpList front s frontIn ≠ some (.ok (s', some cf))))
    (hSrcInv : ∀ (_funcOp : OperationPtr) (values : Array RuntimeValue) (mem : MemoryState)
        (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds rewriter.ctx.raw)
        (newVars : VariableState rewriter.ctx),
        (VariableState.empty rewriter.ctx).setArgumentValues? entryBlock values entryIn = some newVars →
        ∀ fst (hfst : (entryBlock.get! rewriter.ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars mem).EquationLemmaAt (.before fst)
            (by have := rewriter.ctx.wellFormed.inBounds; grind))
    (hTgtInv : ∀ (_funcOp : OperationPtr) (values' : Array RuntimeValue) (mem : MemoryState)
        (entryBlock : BlockPtr) (entryIn' : entryBlock.InBounds rewriter'.ctx.raw)
        (newVars' : VariableState rewriter'.ctx),
        (VariableState.empty rewriter'.ctx).setArgumentValues? entryBlock values' entryIn' = some newVars' →
        (InterpreterState.mk newVars' mem).DefinesDominating
          (InsertPoint.atStart! entryBlock rewriter'.ctx.raw)
          ((InsertPoint.inBounds_atStart! rewriter'.ctx.wellFormed entryIn').mpr entryIn'))
    (hTgtEqInv : ∀ (_funcOp : OperationPtr) (values' : Array RuntimeValue) (mem : MemoryState)
        (entryBlock : BlockPtr) (entryIn' : entryBlock.InBounds rewriter'.ctx.raw)
        (newVars' : VariableState rewriter'.ctx),
        (VariableState.empty rewriter'.ctx).setArgumentValues? entryBlock values' entryIn' = some newVars' →
        (InterpreterState.mk newVars' mem).EquationLemmaAt
          (InsertPoint.atStart! entryBlock rewriter'.ctx.raw)
          ((InsertPoint.inBounds_atStart! rewriter'.ctx.wellFormed entryIn').mpr entryIn'))
    {moduleOp : OperationPtr} :
    moduleOp.isModuleRefinedBy rewriter.ctx moduleOp rewriter'.ctx := by
  -- The driver's net edit is a `RewrittenAt` instance.
  obtain ⟨block, pre, post, blockIn, blockIn', hOpParent, hRW, hNewOpsFrame⟩ :=
    RewrittenAt.of_fromLocalRewrite hValid hSrcDom hSrcVerif hpat hdriver
  -- The target context is verified: the pattern's `rewritePreservesVerified` obligation propagates
  -- source verification across the driver run.
  have newCtxVerif : rewriter'.ctx.Verified :=
    hValid.rewritePreservesVerified rewriter op opInBounds rewriter' hdriver hSrcVerif
  -- `RewrittenAt.isModuleRefinedBy` consumes the instance; the easy well-formedness side-conditions
  -- are discharged here, the four semantic bridges remain.
  -- `hSrcSplit`/`hTgtSplit`/`hSrcInv` discharge positionally; `hTgtInv` is restated with a target
  -- in-bounds binder, so reroute the source binder through `hRW.blocksInBounds`.
  refine hRW.isModuleRefinedBy hSrcVerif newCtxVerif hSrcDom ?hOpSim hSrcSplit hTgtSplit hSrcInv
    ?hTgtInv ?hTgtEqInv
  case hTgtInv =>
    intro _funcOp values' mem entryBlock entryIn newVars' h
    exact hTgtInv _funcOp values' mem entryBlock (hRW.blocksInBounds entryBlock entryIn) newVars' h
  case hTgtEqInv =>
    intro _funcOp values' mem entryBlock entryIn newVars' h
    exact hTgtEqInv _funcOp values' mem entryBlock (hRW.blocksInBounds entryBlock entryIn) newVars' h
  case hOpSim =>
    -- === PR 8, step 3: bridge `pattern.PreservesSemantics` to `OpStepSimulation op newOps hRW.σ`. ===
    -- `hValid.preservesSemantics` (at `ctx := rewriter.ctx`) supplies the *source* side exactly:
    -- `interpretOp op` in `rewriter.ctx` refined by `interpretOpList newOps` in the pattern's create-only
    -- context `newCtxPat`. The target side (`rewriter'.ctx`) is reached with the **data-equality frame**
    -- (`interpretOpList_sameData_transport_redirect`): `interpretOp`/`interpretOpList` read a context
    -- only through each op's *local* data (operands/type/properties/result-types/successors/results),
    -- never through parents or dominance, so a `newOps` run transports unchanged between `newCtxPat` and
    -- `rewriter'.ctx` (whose op-data agree by `hNewOpsFrame`) — sidestepping the scoped-refinement/parent
    -- obstruction that blocked earlier attempts.
    intro s s' p' p'In qIn q'In hCouple hRef hEqLem hEqLem'
    -- Split on the source op step; `none`/`.ub` outcomes make the refinement trivial.
    rcases hsrc : interpretOp op s with _ | (⟨newState, cf⟩ | _)
    · -- `none` (interpreter stuck): refinement trivial.
      simp only [Interp.isRefinedBy]
    -- === ok-case: the source op step succeeds with result state `newState` and action `cf`. ===
    · -- (A) Rebuild `s'` (a state over the *driver* context `rewriter'.ctx`) as a state `sPat` over the
      -- pattern's create-only context `newCtxPat`. `rewriter'.ctx` is `newCtxPat` with `op` erased and its
      -- result-uses redirected, so every value in bounds of `rewriter'.ctx` is in bounds of `newCtxPat`
      -- with the same type. These are two cross-context frame facts between the pattern context and the
      -- driver context (the driver internals produce `rewriter'.ctx` *from* `newCtxPat`), isolated here.
      have hBoundsBA : ∀ v : ValuePtr, v.InBounds rewriter'.ctx.raw → v.InBounds newCtxPat.raw :=
        sorry
      have hTypeBA : ∀ v : ValuePtr, v.InBounds rewriter'.ctx.raw →
          v.getType! newCtxPat.raw = v.getType! rewriter'.ctx.raw :=
        sorry
      let sPat : InterpreterState newCtxPat :=
        { variables :=
            { variables := s'.variables.variables
              conforms := fun val var hmem hval => by
                rw [hTypeBA val (s'.variables.variablesIn val hmem)]
                exact s'.variables.conforms val var hmem hval
              variablesIn := fun val hmem => hBoundsBA val (s'.variables.variablesIn val hmem) }
          memory := s'.memory }
      have hsPatData : sPat.SameData s' := ⟨rfl, rfl⟩
      -- `op` survives into the pattern's create-only context (it is only erased by the *driver*).
      have opInPat : op.InBounds newCtxPat.raw := by
        have := (hValid.returnCtxChanges rewriter.ctx op newCtxPat newOps newValues hpat).inBounds_mono
          (GenericPtr.operation op) (by grind)
        grind
      -- (C) The successful source step defines all of `op`'s results, so `sourceValues` exists.
      obtain ⟨sourceValues, hSourceValues⟩ :
          ∃ sv, (op.getResults rewriter.ctx.raw).mapM (newState.variables.getVar? ·) = some sv := by
        obtain ⟨ov, rv, mem', vs', hov, hint, hset, hst⟩ := interpretOp_some_iff.mp hsrc
        rw [← OperationPtr.getResults!_eq_getResults opInBounds]
        refine ⟨rv, (Array.mapM_eq_some_iff_of_size_eq ?_).mpr ?_⟩
        · grind
        · intro i hi
          have hi' : i < op.getNumResults! rewriter.ctx.raw := by grind
          rw [OperationPtr.getResults!.getElem!_eq_getResult hi', hst]
          exact VariableState.getVar?_getResult_of_setResultValues? hi' hset
      -- (B) `sPat` satisfies the SSA invariant at `.before op`, transported from `s'`'s invariant at
      -- `p'` across the `newCtxPat`/`rewriter'.ctx` data frame and the `p' ↔ .before op` point image.
      have hSPatEqLem : sPat.EquationLemmaAt (InsertPoint.before op) (by grind) := sorry
      -- (D-in) Reconcile the given `hRW.σ`-refinement at `(.before op, p')` (target `rewriter'.ctx`) into
      -- the `LocalRewritePattern.mapping`-refinement at `(.before op, .before op)` (target `newCtxPat`)
      -- that `preservesSemantics` consumes. `mapping` and `hRW.σ` agree on `.val`
      -- (`mapping_val_eq_rewriteMapping_val`); `sPat` shares `s'`'s data; the target scope moves from
      -- `p'` to the create-only `.before op` (the point image of the rewrite).
      have hRefInput : s.isRefinedByAt sPat
          (LocalRewritePattern.mapping hpat hValid.returnValuesInBounds hValid.returnValues
            hValid.returnCtxChanges) (.at (.before op)) (.at (.before op)) := by
        refine ⟨hRef.1, ?_⟩
        intro val valIn hSrc _hTgt sv tv hsv htv
        -- `mapping` and `hRW.σ` send `val` to the same value pointer.
        have hval_eq : ((LocalRewritePattern.mapping hpat hValid.returnValuesInBounds
            hValid.returnValues hValid.returnCtxChanges) ⟨val, valIn⟩).val
            = (hRW.σ ⟨val, valIn⟩).val :=
          mapping_val_eq_rewriteMapping_val hpat hValid.returnValuesInBounds hValid.returnValues
            hValid.returnCtxChanges valIn valIn
        -- Invoke `hRef` at `val`: source scope `hSrc`; target scope at `p'` from `hCouple`.
        refine hRef.2 val valIn hSrc (hCouple val valIn hSrc) sv tv hsv ?_
        -- `sPat` shares `s'`'s variable map, and both mappings agree on `.val`, so the lookups match.
        have hkey : s'.variables.getVar? (hRW.σ ⟨val, valIn⟩)
            = sPat.variables.getVar? ((LocalRewritePattern.mapping hpat hValid.returnValuesInBounds
                hValid.returnValues hValid.returnCtxChanges) ⟨val, valIn⟩) := by
          simp only [VariableState.getVar?, hsPatData.1, hval_eq]
        rw [hkey]; exact htv
      -- (D) Apply the pattern's `PreservesSemantics` in the create-only context.
      obtain ⟨newState', hRunPat, hMemEq, targetValues, hTargetValues, hValRef⟩ :=
        hValid.preservesSemantics rewriter.ctx hSrcDom hSrcVerif op opInBounds
          newCtxPat newOps newValues hpat s hEqLem newState cf hsrc sourceValues hSourceValues
          sPat hSPatEqLem hRefInput
      -- (E) Transport the create-only `newOps` run to the driver context via the redirect data-frame.
      obtain ⟨sTgt, hRunTgt, hSameRes⟩ :=
        interpretOpList_sameData_transport_redirect
          (ctxA := newCtxPat) (ctxB := rewriter'.ctx) (ops := newOps.toList)
          (fun o ho => ((hValid.returnOps rewriter.ctx op newCtxPat newOps newValues hpat o).mp
            (by simpa using ho)).1) hRW.newOpsInBounds'
          (fun o ho => (hNewOpsFrame o ho).2)
          (fun o ho hop => OpDataEq.of_sameIntrinsic (hNewOpsFrame o ho).1 hop)
          hsPatData hRunPat
      -- Land the `Interp.isRefinedBy` goal: the target run reaches `.ok (sTgt, cf)`.
      rw [hRunTgt]
      simp only [Interp.isRefinedBy]
      refine ⟨?_, ?_⟩
      · -- (F) The result states are `hRW.σ`-refined at `(after! op, afterLast newOps p')`.
        -- Memory agrees: `newState.memory = newState'.memory` (`preservesSemantics`) `= sTgt.memory`
        -- (the redirect transport preserves data).
        refine ⟨hMemEq.trans hSameRes.2, ?_⟩
        -- Variable refinement, by cases on the source value `val`:
        -- • `val = op.getResult i` (source scope `after! op` adds exactly `op`'s results): `σ` sends it
        --   to `newValues[i]`; `sTgt` shares `newState'`'s map (`hSameRes`), so the target value is
        --   `targetValues[i]!` and the source value `sourceValues[i]!`, refined by `hValRef`.
        -- • surviving `val` (dominates `before op`, ∉ `newOps`-results): `interpretOp`/`interpretOpList`
        --   leave `getVar? val` untouched, so source = `s.getVar? val`, target = `s'.getVar? val`; the
        --   output target scope `afterLast newOps p'` steps back to `p'` *within* `rewriter'.ctx` (`val`
        --   is not a `newOps` result), where `hRef` applies. This is SOUND for arbitrary `p'` — no
        --   before-op↔p' cross-context transport — but still needs a list-level `interpretOpList`
        --   `getVar?`-preservation lemma and an intra-context `afterLast newOps → p'` dominance step-back
        --   lemma, neither of which exists yet.
        sorry
      · -- Control-flow actions coincide (`cf` on both sides).
        exact ControlFlowAction.optionIsRefinedBy_refl cf
    · -- `.ub` (source undefined behaviour): refinement trivial.
      simp only [Interp.isRefinedBy]

end Veir
