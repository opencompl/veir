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
   in `newCtx`) — exactly what `interpretOp_monotone`/`interpretOpList_monotone` consume.
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

/--
`RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn'` asserts that
`newCtx` is obtained from `ctx` by the single local rewrite that replaces `op` with `newOps`
(producing `newValues`). The renaming identifying surviving values across the two contexts is *not* a
parameter: it is the function `RewrittenAt.σ` of the instance, defined as `rewriteMapping op newValues
h.mapResultsInBounds h.mapNonResultsInBounds` (the in-bounds witnesses `mapResultsInBounds`/
`mapNonResultsInBounds` are fields below). `block` is the block containing `op`, `pre`/`post` the
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
  /-- In-bounds witness for the redirect branch of `σ` (`rewriteMapping`): each produced value is in
  bounds of the target context. (Derivable from `newValuesSize`/`newValuesInBounds`, but kept as a
  field so `σ := RewrittenAt.σ` is total without re-deriving it.) -/
  mapResultsInBounds : ∀ (index : Nat), index < (op.getResults! ctx.raw).size →
    newValues[index]!.InBounds newCtx.raw
  /-- In-bounds witness for the identity branch of `σ` (`rewriteMapping`): every value that is not a
  result of `op` survives into the target context. -/
  mapNonResultsInBounds : ∀ (v : ValuePtr), v.InBounds ctx.raw →
    v ∉ op.getResults! ctx.raw → v.InBounds newCtx.raw
  -- Clause 2: `op` erased, others survive.
  /-- The matched operation is erased. -/
  opErased : ¬ op.InBounds newCtx.raw
  /-- Every operation other than `op` survives into the target context. -/
  survives : ∀ (o : OperationPtr), o.InBounds ctx.raw → o ≠ op → o.InBounds newCtx.raw
  -- Clause 4: intrinsic-data frame for survivors.
  /-- Every surviving operation carries identical intrinsic data, modulo the renaming `σ`. -/
  frame : ∀ (o : OperationPtr) (oIn : o.InBounds ctx.raw) (oIn' : o.InBounds newCtx.raw),
    o ≠ op →
      (rewriteMapping op newValues mapResultsInBounds mapNonResultsInBounds).PreservesOperation
        o o oIn oIn'
  -- Clause 5: structure frame.
  /-- Blocks stay in bounds — successor-`InBounds` transport. -/
  blocksInBounds : ∀ (b : BlockPtr), b.InBounds ctx.raw → b.InBounds newCtx.raw
  /-- Parent operations of surviving operations are preserved. -/
  parentOps : ∀ (o : OperationPtr), o.InBounds ctx.raw → o ≠ op →
    o.getParentOp! newCtx.raw = o.getParentOp! ctx.raw
  -- Clause 6: result well-formedness.
  /-- The target context is dominance-well-formed. -/
  newCtxDom : newCtx.Dom
  newCtxVerif : newCtx.Verified
  -- Clause 7: value-renaming frame for block arguments (PR 9 / `LocalRewritePattern.mapping`).
  /-- `σ` fixes every value that is not a result of `op`. `LocalRewritePattern.mapping` is the
  identity except on `op`'s results (which it redirects to `newValues`), so every other value — in
  particular every block argument, which is never an `op` result — is left untouched. This is what
  discharges the `hFix`/`hReflectArgs` frame hypotheses of `setArgumentValues?_isRefinedBy`. -/
  mappingFixesNonResults : ∀ (v : ValuePtr) (vIn : v.InBounds ctx.raw),
    v ∉ op.getResults! ctx.raw →
      ((rewriteMapping op newValues mapResultsInBounds mapNonResultsInBounds) ⟨v, vIn⟩).val = v
  /-- Every produced value is an operation result, never a block argument (in the concrete driver they
  are results of `newOps`). Together with `mappingFixesNonResults`, this lets `σ` reflect a block
  argument only from that same block argument. -/
  newValuesAreResults : ∀ v ∈ newValues, ∃ opr : OpResultPtr, v = ValuePtr.opResult opr
  /-- The block-argument list of every block is preserved by the rewrite (it only edits operations).
  Gives equal argument counts and argument types across the two contexts. -/
  blockArgsPreserved : ∀ (bl : BlockPtr), bl.InBounds ctx.raw →
    (bl.get! newCtx.raw).arguments = (bl.get! ctx.raw).arguments
  -- Clause 8: region/block structure frame (the rewrite edits only operation lists).
  /-- Regions stay in bounds — region-`InBounds` transport (mirrors `blocksInBounds`). -/
  regionsInBounds : ∀ (r : RegionPtr), r.InBounds ctx.raw → r.InBounds newCtx.raw
  /-- The region list of every surviving operation is preserved: the rewrite only edits the operation
  list of `block`, never region structure. Gives equal region counts and equal region pointers across
  the two contexts (used to relate `interpretFunction`/`interpretRegion`). -/
  opRegionsPreserved : ∀ (o : OperationPtr), o.InBounds ctx.raw → o ≠ op →
    (o.get! newCtx.raw).regions = (o.get! ctx.raw).regions
  /-- The first block of every region is preserved by the rewrite, so `interpretRegion` starts the
  CFG walk from the same entry block in both contexts. -/
  regionFirstBlockPreserved : ∀ (r : RegionPtr), r.InBounds ctx.raw →
    (r.get! newCtx.raw).firstBlock = (r.get! ctx.raw).firstBlock
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

/-- The fixed renaming performed by the rewrite: `rewriteMapping` applied to the in-bounds witnesses
carried by the `RewrittenAt` instance. This is *not* a parameter of `RewrittenAt`; it is a function of
the instance (the lemmas below refer to it as `h.σ`). -/
abbrev σ (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn') :
    ValueMapping ctx newCtx :=
  rewriteMapping op newValues h.mapResultsInBounds h.mapNonResultsInBounds

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
    bl.getNumArguments! newCtx.raw = bl.getNumArguments! ctx.raw := by
  simp only [BlockPtr.getNumArguments!, h.blockArgsPreserved bl blIn]

/-- The type of any block argument is preserved by the rewrite. -/
theorem argType_eq (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    {bl : BlockPtr} (blIn : bl.InBounds ctx.raw) (i : Nat) :
    (bl.getArgument i : ValuePtr).getType! newCtx.raw = (bl.getArgument i : ValuePtr).getType! ctx.raw := by
  simp only [ValuePtr.getType!_blockArgument, BlockArgumentPtr.get!, BlockPtr.getArgument_block,
    BlockPtr.getArgument_index, h.blockArgsPreserved bl blIn]

/-- A block argument is never a result of `op` (distinct `ValuePtr` constructors). -/
theorem blockArg_notMem_getResults
    (_h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    {bl : BlockPtr} {i : Nat} :
    (bl.getArgument i : ValuePtr) ∉ op.getResults! ctx.raw := by
  simp only [OperationPtr.getResults!.mem_iff_exists_index]
  rintro ⟨index, _, heq⟩
  simp [BlockPtr.getArgument, OperationPtr.getResult_def] at heq

/-- `σ` fixes block-argument pointers: it maps `bl.getArgument i` to itself. Discharges the `hFix`
hypothesis of `setArgumentValues?_isRefinedBy`. -/
theorem mappingFixesArg
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    {bl : BlockPtr} {i : Nat} (vIn : (bl.getArgument i : ValuePtr).InBounds ctx.raw) :
    (h.σ ⟨(bl.getArgument i : ValuePtr), vIn⟩).val = (bl.getArgument i : ValuePtr) :=
  h.mappingFixesNonResults _ vIn h.blockArg_notMem_getResults

/-- `σ` fixes a block's argument array: applying it to `bl`'s source arguments yields the same
arguments in the target context. Discharges the `hArgs` hypothesis of
`setArgumentValues?_isRefinedBy`. -/
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

/-- `σ` reflects block-argument pointers: the only value it maps onto `bl.getArgument i` is
`bl.getArgument i` itself (results map into `newValues`, which are never block arguments). Discharges
the `hReflectArgs` hypothesis of `setArgumentValues?_isRefinedBy`. -/
theorem mappingReflectsArg
    (h : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    {bl : BlockPtr} (val : ValuePtr) (valIn : val.InBounds ctx.raw) (i : Nat)
    (heq : (h.σ ⟨val, valIn⟩).val = (bl.getArgument i : ValuePtr)) :
    val = (bl.getArgument i : ValuePtr) := by
  by_cases hMem : val ∈ op.getResults! ctx.raw
  · exfalso
    have hmem := h.mapping_getResult_mem_newValues valIn hMem
    rw [heq] at hmem
    obtain ⟨opr, hopr⟩ := h.newValuesAreResults _ hmem
    simp [BlockPtr.getArgument] at hopr
  · rw [h.mappingFixesNonResults val valIn hMem] at heq
    exact heq

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

* **`pre` (identical list)** — cross-context monotonicity `interpretOpList_monotone` (PR 3), fed the
  `CrossContextFrame`s of clause 4; this also threads `EquationLemmaAt`/`DefinesDominating` to `op`.
* **`[op]` vs `newOps`** — the local op-step simulation `hOpSim`, which PR 8 discharges from
  `PreservesSemantics` (bridging its create-only context to the inserted/erased `newCtx` via clause 4).
* **`post` (same pointers, redirected operands)** — `interpretOpList_mono` again, now under `σ`,
  seeded by the post-`op` state from the previous regime.
* **source `.ub` at `op`** — a source `ub` refines any target outcome, so no target-progress argument
  is needed: cross-context monotonicity (`interpretOpList_mono`) discharges this regime directly.

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
-/
def OpStepSimulation
    {ctx newCtx : WfIRContext OpCode} (op : OperationPtr) (newOps : Array OperationPtr)
    (μ : ValueMapping ctx newCtx) (opIn : op.InBounds ctx.raw)
    (newOpsIn' : ∀ o ∈ newOps.toList, o.InBounds newCtx.raw) : Prop :=
  ∀ (s : InterpreterState ctx) (s' : InterpreterState newCtx),
    s.isRefinedBy s' μ →
    s.EquationLemmaAt (InsertPoint.before op) →
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState newCtx × Option ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 μ ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
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

/-- Interpreting a singleton operation list is interpreting the operation. -/
theorem interpretOpList_singleton {ctx : WfIRContext OpCode} {op : OperationPtr}
    {state : InterpreterState ctx} (h : ∀ o ∈ [op], o.InBounds ctx.raw) :
    interpretOpList [op] state h = interpretOp op state (h op (by simp)) := by
  rw [interpretOpList_cons]
  rcases interpretOp op state (h op (by simp)) with _ | (⟨s, a⟩ | _)
  · rfl
  · cases a <;> simp [interpretOpList_nil]
  · rfl

/--
Sequential composition of cross-context refinement over `interpretOpList`. If interpreting the
prefix `l₁`/`m₁` refines (`hPrefix`), and — whenever the prefixes both run to completion without a
terminator into `σ`-refined states — interpreting the suffixes `l₂`/`m₂` refines (`hCont`), then
interpreting `l₁ ++ l₂` refines `m₁ ++ m₂`. The target must make progress under a UB source
(`hTgtProgress`), which the caller discharges from the verified, SSA-well-formed target chain.
-/
theorem isRefinedBy_interpretOpList_seqCompose
    {ctx ctx' : WfIRContext OpCode} {μ : ValueMapping ctx ctx'}
    {l₁ l₂ m₁ m₂ : List OperationPtr}
    {s : InterpreterState ctx} {s' : InterpreterState ctx'}
    (hl : ∀ o ∈ l₁ ++ l₂, o.InBounds ctx.raw)
    (hm : ∀ o ∈ m₁ ++ m₂, o.InBounds ctx'.raw)
    (hPrefix : Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 μ ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOpList l₁ s (fun o ho => hl o (List.mem_append_left _ ho)))
      (interpretOpList m₁ s' (fun o ho => hm o (List.mem_append_left _ ho))))
    (hCont : ∀ (s2 : InterpreterState ctx) (s2' : InterpreterState ctx'),
        s2.isRefinedBy s2' μ →
        interpretOpList l₁ s (fun o ho => hl o (List.mem_append_left _ ho)) = some (.ok (s2, none)) →
        interpretOpList m₁ s' (fun o ho => hm o (List.mem_append_left _ ho)) = some (.ok (s2', none)) →
        Interp.isRefinedBy
          (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
               (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
            r₁.1.isRefinedBy r₂.1 μ ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
          (interpretOpList l₂ s2 (fun o ho => hl o (List.mem_append_right _ ho)))
          (interpretOpList m₂ s2' (fun o ho => hm o (List.mem_append_right _ ho)))) :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState ctx' × Option ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 μ ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
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
      obtain ⟨cf', ha', hcf⟩ : ∃ cf', a' = some cf' ∧ cf.isRefinedBy cf' := by
        cases a' <;> simp_all [ControlFlowAction.optionIsRefinedBy]
      subst ha'
      exact ⟨hsRef, hcf⟩
  · simp

/--
**Block-`B` simulation.** Interpreting the source block list `pre ++ [op] ++ post` is refined by
interpreting the target block list `pre ++ newOps ++ post` (the `post` operations are the same
pointers — their operands are redirected, recorded by `σ` in clause 4).

Stated over the op-lists directly; PR 8 obtains the lists and the source/target chain-and-parent
structure from `RewrittenAt.srcList`/`tgtList` (clause 3), the source-entry `EquationLemmaAt`/target
`DefinesDominating` invariants from the per-block invariant `I`, and supplies `hOpSim` from
`PreservesSemantics`.

The proof composes the three regimes via `isRefinedBy_interpretOpList_seqCompose`:
* **`pre` (identical list)** — cross-context monotonicity `hPre` (PR 3), fed the clause-4 frames.
* **`[op]` vs `newOps`** — the local op-step simulation `hOpSim`, after threading the SSA invariant
  `EquationLemmaAt` from block entry through `pre` to `op` (`interpretOpList_equationLemmaAt`).
* **`post` (same pointers, redirected operands)** — cross-context monotonicity `hPost` (PR 3) under
  `σ`, applicable from any pair of `σ`-refined post-`op` states.

No target-progress argument is needed: a source `ub` refines any target outcome, so cross-context
monotonicity (`interpretOpList_mono`) and `isRefinedBy_interpretOpList_seqCompose` discharge the
source-UB case directly. The target-side `DefinesDominating` invariant is therefore unused by the
proof, but kept in the signature (`_hDefDom'`) for the Stage D / PR 8 contract.
-/
theorem RewrittenAt.blockSimulation
    (hRW : RewrittenAt ctx op newOps newValues newCtx opIn block pre post blockIn blockIn')
    (newCtxVerif : newCtx.Verified)
    {state : InterpreterState ctx} {state' : InterpreterState newCtx}
    (hState : state.isRefinedBy state' hRW.σ)
    -- Source dominance well-formedness (PR 8 supplies it from the function-level `ctx.Dom` assumption).
    (hCtxDom : ctx.Dom)
    -- Source-side SSA invariant at block entry: threads `EquationLemmaAt` up to `op` (PR 8 supplies
    -- it from invariant `I`; the source `pre`-chain is derived via `RewrittenAt.preChainOp`).
    (hEqLem : ∀ fst (hfst : (block.get! ctx.raw).firstOp = some fst),
      state.EquationLemmaAt (.before fst))
    (hOpSim : OpStepSimulation op newOps hRW.σ opIn hRW.newOpsInBounds') :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × ControlFlowAction)
           (r₂ : InterpreterState newCtx × ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 hRW.σ ∧ r₁.2.isRefinedBy r₂.2)
      (interpretTerminatedOpList (pre.toList ++ [op] ++ post.toList) state
        (sourceListIn opIn hRW.preInBounds hRW.postInBounds))
      (interpretTerminatedOpList (pre.toList ++ newOps.toList ++ post.toList) state'
        (targetListIn hRW.preInBounds' hRW.newOpsInBounds' hRW.postInBounds')) := by
  -- In-bounds witnesses for `pre`/`post`/`newOps`, derived from the block lists `hRW.srcList` /
  -- `hRW.tgtList` (membership in an `operationList` implies in-bounds).
  have preIn := hRW.preInBounds
  have postIn := hRW.postInBounds
  have preIn' := hRW.preInBounds'
  have newOpsIn' := hRW.newOpsInBounds'
  have postIn' := hRW.postInBounds'
  -- Regime 1 (`pre`, identical list): cross-context monotonicity (PR 3), fed the
  -- `CrossContextFrame`s of clause 4 (`hRW.frame_of_ne`, since every `pre` op survives and `≠ op`).
  -- Threads `σ`-refinement and (in the full proof) the `EquationLemmaAt`/`DefinesDominating`
  -- invariants from block entry up to `op`.
  have hPre : Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
           (r₂ : InterpreterState newCtx × Option ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 hRW.σ ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
      (interpretOpList pre.toList state preIn)
      (interpretOpList pre.toList state' preIn') := by
    exact interpretOpList_mono newCtxVerif preIn preIn' hState
      (fun o h => hRW.frame o (preIn o h) (preIn' o h) (fun heq => hRW.opNotMemPre (heq ▸ h)))
  -- Regime 3 (`post`, same pointers / redirected operands): cross-context monotonicity (PR 3)
  -- under `σ`, applicable from any pair of `σ`-refined post-`op` states. Each `post` op survives
  -- and `≠ op`, so clause 4 supplies its frame under `σ` (operands redirected through `σ`).
  have hPost : ∀ (s : InterpreterState ctx) (s' : InterpreterState newCtx),
      s.isRefinedBy s' hRW.σ →
      Interp.isRefinedBy
        (fun (r₁ : InterpreterState ctx × Option ControlFlowAction)
             (r₂ : InterpreterState newCtx × Option ControlFlowAction) =>
          r₁.1.isRefinedBy r₂.1 hRW.σ ∧ ControlFlowAction.optionIsRefinedBy r₁.2 r₂.2)
        (interpretOpList post.toList s postIn)
        (interpretOpList post.toList s' postIn') := by
    intro s s' hs
    exact interpretOpList_mono newCtxVerif postIn postIn' hs
      (fun o h => hRW.frame o (postIn o h) (postIn' o h) (fun heq => hRW.opNotMemPost (heq ▸ h)))
  -- Assembly. Prove the op-list refinement over `pre ++ [op] ++ post` vs `pre ++ newOps ++ post` by
  -- two nested `isRefinedBy_interpretOpList_seqCompose` applications (inner: `pre`/`[op]` vs
  -- `pre`/`newOps`; outer: append `post`), threading `EquationLemmaAt` (source, for `hOpSim`) and
  -- `DefinesDominating` (target, for `hPost`); the UB-source obligation is the verified target run's
  -- progress. Then convert to the terminated lists, dispatching the source-UB case via `hPostTerm`.
  -- In-bounds helpers for the intermediate prefixes `pre ++ [op]` (source) and `pre ++ newOps`
  -- (target).
  have hpreOpIn : ∀ o ∈ pre.toList ++ [op], o.InBounds ctx.raw := by
    intro o ho; simp only [List.mem_append, List.mem_singleton] at ho
    rcases ho with h | h
    · exact preIn o h
    · exact h ▸ opIn
  have hpreNewIn' : ∀ o ∈ pre.toList ++ newOps.toList, o.InBounds newCtx.raw := by
    intro o ho; simp only [List.mem_append] at ho
    rcases ho with h | h
    · exact preIn' o h
    · exact newOpsIn' o h
  -- Inner composition: `pre ++ [op]` (source) refined by `pre ++ newOps` (target).
  have hInner := isRefinedBy_interpretOpList_seqCompose
    (l₁ := pre.toList) (l₂ := [op]) (m₁ := pre.toList) (m₂ := newOps.toList)
    hpreOpIn hpreNewIn' hPre
    (fun s1 s1' hs1Ref hrunSrc hrunTgt => by
      -- Thread the SSA invariant `EquationLemmaAt` from block entry through `pre` to `op`.
      have hEq1 : s1.EquationLemmaAt (.before op) opIn :=
        interpretOpList_equationLemmaAt_before hCtxDom preIn opIn hRW.preChainOp
          (fun fst _ hhead => hEqLem fst
            (by rw [hRW.srcFirstOp]; simp only [List.head?_append, hhead, Option.some_or]))
          hrunSrc
      rw [interpretOpList_singleton]
      exact hOpSim s1 s1' hs1Ref hEq1)
  -- Outer composition: append `post` on both sides.
  have hFull := isRefinedBy_interpretOpList_seqCompose
    (l₁ := pre.toList ++ [op]) (l₂ := post.toList)
    (m₁ := pre.toList ++ newOps.toList) (m₂ := post.toList)
    (sourceListIn opIn preIn postIn) (targetListIn preIn' newOpsIn' postIn')
    hInner
    (fun s2 s2' hs2Ref hrunSrc hrunTgt => hPost s2 s2' hs2Ref)
  -- Convert the op-list refinement to the terminated-list refinement: the source-UB case is
  -- refined by any target outcome (monotonicity now discharges target progress internally).
  simp only [interpretTerminatedOpList, bind]
  rcases hs : interpretOpList (pre.toList ++ [op] ++ post.toList) state
      (sourceListIn opIn preIn postIn) with _ | (⟨sf, act⟩ | _)
  · simp [Interp.isRefinedBy]
  · rw [hs] at hFull
    simp only [Interp.isRefinedBy_ok_target_iff] at hFull
    obtain ⟨⟨sf', act'⟩, htgt, hsRef, hactRef⟩ := hFull
    rw [htgt]
    cases act with
    | none => simp [Interp.isRefinedBy]
    | some cf =>
      obtain ⟨cf', hact', hcfRef⟩ : ∃ cf', act' = some cf' ∧ cf.isRefinedBy cf' := by
        cases act' <;> simp_all [ControlFlowAction.optionIsRefinedBy]
      subst hact'
      exact ⟨hsRef, hcfRef⟩
  · -- Source-UB case: a source `ub` is refined by any target outcome.
    simp [Interp.isRefinedBy]

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
    (hState : state.isRefinedBy state' hRW.σ)
    (hVals : values ⊒ values')
    (hSrcInv : ∀ newVars, state.variables.setArgumentValues? b values bIn = some newVars →
        ∀ fst (hfst : (b.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars state.memory).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind))
    (hOpSim : OpStepSimulation op newOps hRW.σ opIn hRW.newOpsInBounds') :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × ControlFlowAction)
           (r₂ : InterpreterState newCtx × ControlFlowAction) =>
        r₁.1.isRefinedBy r₂.1 hRW.σ ∧ r₁.2.isRefinedBy r₂.2)
      (interpretBlock b values state bIn)
      (interpretBlock b values' state' (hRW.blocksInBounds b bIn)) := by
  have bIn' := hRW.blocksInBounds b bIn
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
      rw [hRW.argType_eq bIn]
      exact RuntimeValue.Conforms_of_isRefinedBy hPt
        ((VariableState.setArgumentValues?_isSome_iff_conforms state.variables).mpr ⟨newVars, hsa⟩ j
          (hRW.numArgsEq bIn ▸ hj))
    obtain ⟨newVars', hsa', hpsRefVar⟩ := VariableState.setArgumentValues?_isRefinedBy
      hState.2 hVals bIn bIn' (hRW.argsApplyToArray bIn)
      (fun val valIn arg hMem heq => by
        obtain ⟨i, _hi, rfl⟩ := BlockPtr.getArguments!.mem_iff_exists_index.mp hMem
        exact hRW.mappingReflectsArg val valIn i heq)
      tgtConforms hsa
    have hpsRef : (InterpreterState.mk newVars state.memory).isRefinedBy
        ⟨newVars', state'.memory⟩ hRW.σ := ⟨hState.1, hpsRefVar⟩
    simp only [hsa', Option.bind_some]
    by_cases hbB : b = block
    · -- Rewritten block `B`: rewrite the op-lists and apply the block-`B` simulation.
      subst hbB
      have hsrc : (b.operationList ctx.raw ctx.wellFormed bIn).toList
          = pre.toList ++ [op] ++ post.toList := by rw [hRW.srcList]; simp
      have htgt : (b.operationList newCtx.raw newCtx.wellFormed bIn').toList
          = pre.toList ++ newOps.toList ++ post.toList := by rw [hRW.tgtList]; simp
      simp only [hsrc, htgt]
      grind [hRW.blockSimulation]
    · -- Other block: op-lists identical, apply cross-context monotonicity.
      have hother := hRW.otherBlocks b bIn bIn' hbB
      have chainSrc := BlockPtr.operationListWF ctx.raw b bIn ctx.wellFormed
      have chainTgt := BlockPtr.operationListWF newCtx.raw b bIn' newCtx.wellFormed
      simp only [hother]
      have opsIn : ∀ o ∈ (b.operationList newCtx.raw newCtx.wellFormed bIn').toList,
          o.InBounds ctx.raw := by
        intro o ho
        rw [← hother] at ho
        exact chainSrc.arrayInBounds (by simpa using ho)
      have opsIn' : ∀ o ∈ (b.operationList newCtx.raw newCtx.wellFormed bIn').toList,
          o.InBounds newCtx.raw := fun o ho => chainTgt.arrayInBounds (by simpa using ho)
      have hne_op : ∀ o ∈ (b.operationList newCtx.raw newCtx.wellFormed bIn').toList, o ≠ op := by
        intro o ho heq; subst heq; exact hRW.opErased (opsIn' o ho)
      have hFrame : ∀ o, (h : o ∈ (b.operationList newCtx.raw newCtx.wellFormed bIn').toList) →
          (hRW.σ).PreservesOperation o o := fun o h => hRW.frame_of_ne (opsIn o h) (hne_op o h)
      exact interpretTerminatedOpList_mono newCtxVerif opsIn opsIn' hpsRef hFrame

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
    {b : BlockPtr} (bIn : b.InBounds ctx.raw)
    {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState newCtx}
    (hState : state.isRefinedBy state' hRW.σ)
    (hVals : values ⊒ values')
    (hSrcInv : ∀ newVars, state.variables.setArgumentValues? b values bIn = some newVars →
        ∀ fst (hfst : (b.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars state.memory).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind)) :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
           (r₂ : InterpreterState newCtx × Array RuntimeValue) =>
        r₁.1.isRefinedBy r₂.1 hRW.σ ∧ r₁.2 ⊒ r₂.2)
      (interpretBlockCFG b values state bIn)
      (interpretBlockCFG b values' state' (hRW.blocksInBounds b bIn)) := by
  refine interpretBlockCFG.fixpoint_induct
    (motive := fun g => ∀ (b : BlockPtr) (bIn : b.InBounds ctx.raw)
      (values values' : Array RuntimeValue)
      (state : InterpreterState ctx) (state' : InterpreterState newCtx),
      state.isRefinedBy state' hRW.σ → values ⊒ values' →
      (∀ newVars, state.variables.setArgumentValues? b values bIn = some newVars →
        ∀ fst (hfst : (b.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars state.memory).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind)) →
      Interp.isRefinedBy
        (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
             (r₂ : InterpreterState newCtx × Array RuntimeValue) =>
          r₁.1.isRefinedBy r₂.1 hRW.σ ∧ r₁.2 ⊒ r₂.2)
        (g b values state bIn)
        (interpretBlockCFG b values' state' (hRW.blocksInBounds b bIn)))
    ?admissible ?step b bIn values values' state state' hState hVals hSrcInv
  case admissible =>
    -- Peel the (dependent) leading `∀ b` together with the `g b` application with
    -- `admissible_pi_apply`, the remaining (non-dependent) binders with `admissible_pi`, the
    -- `g b values state bIn` applications with `admissible_apply`, and close at the `none`-bottom.
    apply Lean.Order.admissible_pi_apply
      (P := fun (b : BlockPtr) (gb : Array RuntimeValue → InterpreterState ctx →
              b.InBounds ctx.raw → Interp (InterpreterState ctx × Array RuntimeValue)) =>
        ∀ (bIn : b.InBounds ctx.raw) (values values' : Array RuntimeValue)
          (state : InterpreterState ctx) (state' : InterpreterState newCtx),
          state.isRefinedBy state' hRW.σ → values ⊒ values' →
          (∀ newVars, state.variables.setArgumentValues? b values bIn = some newVars →
            ∀ fst (hfst : (b.get! ctx.raw).firstOp = some fst),
              (InterpreterState.mk newVars state.memory).EquationLemmaAt (.before fst)
                (by have := ctx.wellFormed.inBounds; grind)) →
          Interp.isRefinedBy
            (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
                 (r₂ : InterpreterState newCtx × Array RuntimeValue) =>
              r₁.1.isRefinedBy r₂.1 hRW.σ ∧ r₁.2 ⊒ r₂.2)
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
    apply Lean.Order.admissible_apply
      (P := fun (_v : Array RuntimeValue) (gv : InterpreterState ctx → b.InBounds ctx.raw →
              Interp (InterpreterState ctx × Array RuntimeValue)) =>
        Interp.isRefinedBy
          (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
               (r₂ : InterpreterState newCtx × Array RuntimeValue) =>
            r₁.1.isRefinedBy r₂.1 hRW.σ ∧ r₁.2 ⊒ r₂.2)
          (gv state bIn) (interpretBlockCFG b values' state' (hRW.blocksInBounds b bIn)))
      (x := values)
    apply Lean.Order.admissible_apply
      (P := fun (_s : InterpreterState ctx) (gs : b.InBounds ctx.raw →
              Interp (InterpreterState ctx × Array RuntimeValue)) =>
        Interp.isRefinedBy
          (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
               (r₂ : InterpreterState newCtx × Array RuntimeValue) =>
            r₁.1.isRefinedBy r₂.1 hRW.σ ∧ r₁.2 ⊒ r₂.2)
          (gs bIn) (interpretBlockCFG b values' state' (hRW.blocksInBounds b bIn)))
      (x := state)
    apply Lean.Order.admissible_apply
      (P := fun (_h : b.InBounds ctx.raw) (gh : Interp (InterpreterState ctx × Array RuntimeValue)) =>
        Interp.isRefinedBy
          (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
               (r₂ : InterpreterState newCtx × Array RuntimeValue) =>
            r₁.1.isRefinedBy r₂.1 hRW.σ ∧ r₁.2 ⊒ r₂.2)
          gh (interpretBlockCFG b values' state' (hRW.blocksInBounds b bIn)))
      (x := bIn)
    exact Lean.Order.admissible_flatOrder _ trivial
  case step =>
    intro g IH b bIn values values' state state' hState hVals hSrcInv
    have hBlk := hRW.interpretBlock_refinement newCtxVerif hCtxDom bIn hState hVals hSrcInv hOpSim
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
        exact ⟨hsRef, hr⟩
      | branch r succ =>
        -- A `branch`: the target action branches to the *same* successor with refined values.
        obtain ⟨r', hact', hr⟩ : ∃ r', act' = .branch r' succ ∧ r ⊒ r' := by
          cases act' <;> simp_all [ControlFlowAction.isRefinedBy]
        subst hact'
        by_cases hsuccIn : succ.InBounds ctx.raw
        · -- Successor in bounds: both walks recurse into `succ`; close with the IH, threading the
          -- source-entry SSA invariant across the CFG edge.
          obtain ⟨front, term, frontIn, termIn, harr, hFrontNoCf⟩ := hSrcSplit b bIn
          have hSrcInvSucc := interpretBlock_branch_equationLemmaAt_succ hCtxDom bIn hsuccIn
            frontIn termIn harr hFrontNoCf hSrcInv hsrc
          simp only [hsrc, htgt, dif_pos hsuccIn, dif_pos (hRW.blocksInBounds succ hsuccIn)]
          exact IH succ hsuccIn r r' s s' hsRef hr hSrcInvSucc
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

/-- The fresh, empty interpreter state (no variables, memory `mem`) in the source context is refined
by the fresh empty state in the target context under any renaming `σ`: they define no variables (so
the variable-refinement obligation is vacuous) and share the same memory. -/
theorem InterpreterState.empty_isRefinedBy {ctx ctx' : WfIRContext OpCode}
    (μ : ValueMapping ctx ctx') (mem : MemoryState) :
    (InterpreterState.mk (VariableState.empty ctx) mem).isRefinedBy
      (InterpreterState.mk (VariableState.empty ctx') mem) μ := by
  refine ⟨rfl, ?_⟩
  intro val valIn sourceVar hget
  simp [VariableState.getVar?, VariableState.empty] at hget

/-- Lift a `σ`-refinement of two region runs to a `FunctionResult` refinement of the corresponding
function runs: `interpretFunction` post-processes `interpretRegion` by keeping only the final memory
and the returned values, and `InterpreterState.isRefinedBy` already entails equal memories, so the
refinement is preserved by that projection. -/
theorem Interp.isRefinedBy_functionResult_of_region {ctx ctx' : WfIRContext OpCode}
    {μ : ValueMapping ctx ctx'}
    {a : Interp (InterpreterState ctx × Array RuntimeValue)}
    {b : Interp (InterpreterState ctx' × Array RuntimeValue)}
    (h : Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
           (r₂ : InterpreterState ctx' × Array RuntimeValue) =>
        r₁.1.isRefinedBy r₂.1 μ ∧ r₁.2 ⊒ r₂.2) a b) :
    Interp.isRefinedBy FunctionResult.isRefinedBy
      (a >>= fun x => pure (x.1.memory, x.2))
      (b >>= fun x => pure (x.1.memory, x.2)) := by
  rcases a with _ | (⟨sf, sres⟩ | _)
  · exact Interp.isRefinedBy_none_target
  · simp only [Interp.isRefinedBy_ok_target_iff] at h
    obtain ⟨⟨sf', sres'⟩, htgt, hsRef, hresRef⟩ := h
    subst htgt
    exact ⟨hsRef.1, hresRef⟩
  · exact Interp.isRefinedBy_ub_target

/-- Lift a `σ`-refinement of two region runs to an array refinement of the corresponding module runs:
`interpretModule` post-processes `interpretRegion` by keeping only the returned values, so the
value-array refinement carried by the region refinement is exactly what survives. -/
theorem Interp.isRefinedBy_moduleResult_of_region {ctx ctx' : WfIRContext OpCode}
    {μ : ValueMapping ctx ctx'}
    {a : Interp (InterpreterState ctx × Array RuntimeValue)}
    {b : Interp (InterpreterState ctx' × Array RuntimeValue)}
    (h : Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
           (r₂ : InterpreterState ctx' × Array RuntimeValue) =>
        r₁.1.isRefinedBy r₂.1 μ ∧ r₁.2 ⊒ r₂.2) a b) :
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
    {r r' : RegionPtr} (rIn : r.InBounds ctx.raw) (rIn' : r'.InBounds newCtx.raw)
    (hrr : r' = r)
    {values values' : Array RuntimeValue}
    {state : InterpreterState ctx} {state' : InterpreterState newCtx}
    (hState : state.isRefinedBy state' hRW.σ)
    (hVals : values ⊒ values')
    (hSrcInv : ∀ (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw)
        (newVars : VariableState ctx),
        state.variables.setArgumentValues? entryBlock values entryIn = some newVars →
        ∀ fst (hfst : (entryBlock.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars state.memory).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind)) :
    Interp.isRefinedBy
      (fun (r₁ : InterpreterState ctx × Array RuntimeValue)
           (r₂ : InterpreterState newCtx × Array RuntimeValue) =>
        r₁.1.isRefinedBy r₂.1 hRW.σ ∧ r₁.2 ⊒ r₂.2)
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
      exact hRW.interpretBlockCFG_refinement newCtxVerif hCtxDom hOpSim hSrcSplit entryIn
        hState hVals (fun newVars h fst hfst => hSrcInv entryBlock entryIn newVars h fst hfst)

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
    {funcOp : OperationPtr} (funcOpIn : funcOp.InBounds ctx.raw)
    (funcOpIn' : funcOp.InBounds newCtx.raw)
    {values values' : Array RuntimeValue} {mem : MemoryState}
    (hVals : values ⊒ values')
    (hSrcInv : ∀ (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw)
        (newVars : VariableState ctx),
        (VariableState.empty ctx).setArgumentValues? entryBlock values entryIn = some newVars →
        ∀ fst (hfst : (entryBlock.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars mem).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind)) :
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
    have hregRef := hRW.interpretRegion_refinement newCtxVerif hCtxDom hOpSim hSrcSplit rIn rIn' hReg
      (state := ⟨.empty ctx, mem⟩) (state' := ⟨.empty newCtx, mem⟩)
      (InterpreterState.empty_isRefinedBy hRW.σ mem) hVals
      (fun entryBlock entryIn newVars h fst hfst => hSrcInv entryBlock entryIn newVars h fst hfst)
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
    {moduleOp : OperationPtr} (moduleOpIn : moduleOp.InBounds ctx.raw)
    (moduleOpIn' : moduleOp.InBounds newCtx.raw)
    (hSrcInv : ∀ (entryBlock : BlockPtr) (entryIn : entryBlock.InBounds ctx.raw)
        (newVars : VariableState ctx),
        (VariableState.empty ctx).setArgumentValues? entryBlock #[] entryIn = some newVars →
        ∀ fst (hfst : (entryBlock.get! ctx.raw).firstOp = some fst),
          (InterpreterState.mk newVars MemoryState.empty).EquationLemmaAt (.before fst)
            (by have := ctx.wellFormed.inBounds; grind)) :
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
    have hregRef := hRW.interpretRegion_refinement newCtxVerif hCtxDom hOpSim hSrcSplit rIn rIn' hReg
      (state := InterpreterState.empty ctx) (state' := InterpreterState.empty newCtx)
      (InterpreterState.empty_isRefinedBy hRW.σ MemoryState.empty)
      (RuntimeValue.arrayIsRefinedBy_refl #[])
      (fun entryBlock entryIn newVars h fst hfst => hSrcInv entryBlock entryIn newVars h fst hfst)
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

set_option warn.sorry false in
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
    (hReturnOps : pattern.ReturnOps)
    (hReturnCtxChanges : pattern.ReturnCtxChanges)
    (hReturnValuesInBounds : pattern.ReturnValuesInBounds)
    (hReturnValues : pattern.ReturnValues)
    {rewriter rewriter' : PatternRewriter OpCode}
    {op : OperationPtr} (opInBounds : op.InBounds rewriter.ctx.raw)
    {block : BlockPtr} (hOpParent : (op.get! rewriter.ctx.raw).parent = some block)
    (hOpRegions : op.getNumRegions! rewriter.ctx.raw = 0)
    {newCtxPat : WfIRContext OpCode} {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    (hpat : pattern rewriter.ctx op = some (newCtxPat, some (newOps, newValues)))
    (hdriver : RewritePattern.fromLocalRewrite pattern rewriter op opInBounds = some rewriter') :
    ∃ (pre post : Array OperationPtr)
      (blockIn : block.InBounds rewriter.ctx.raw) (blockIn' : block.InBounds rewriter'.ctx.raw),
      RewrittenAt rewriter.ctx op newOps newValues rewriter'.ctx opInBounds
        block pre post blockIn blockIn' := by
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
  unfold RewritePattern.fromLocalRewrite at hdriver
  rw [hpat] at hdriver
  simp only [bind_pure_comp, Array.forIn_yield_eq_foldlM, id_map'] at hdriver
  -- Decompose the reduced driver into its three stages: insert-fold (→ `s₁`), replace-fold (→ `s₂`),
  -- then the final `eraseOp` of `op`. The middle operands-collection loop is discarded.
  obtain ⟨s₁, hfold1, hdriver⟩ := Option.bind_eq_some_iff.mp hdriver
  obtain ⟨s₂, hfold2, hdriver⟩ := Option.bind_eq_some_iff.mp hdriver
  obtain ⟨_arr, _hloop, herase⟩ := Option.bind_eq_some_iff.mp hdriver
  -- Bounds transport across the insert/replace folds: both preserve every `InBounds` fact, so `s₂.ctx`
  -- agrees with the pattern's output `newCtxPat` on bounds.
  have hbnd : ∀ ptr : GenericPtr, ptr.InBounds s₂.ctx.raw ↔ ptr.InBounds newCtxPat.raw := by
    intro ptr
    have h1 := Array.foldlM_option_invariant
      (P := fun b : PatternRewriter OpCode => ptr.InBounds b.ctx.raw)
      (fun b a b' h => PatternRewriter.insertOp_ctx_inBounds h) hfold1
    have h2 := Array.foldlM_option_invariant
      (P := fun b : PatternRewriter OpCode => ptr.InBounds b.ctx.raw)
      (fun b a b' h => by
        rw [Option.some.injEq] at h; subst h; exact PatternRewriter.replaceValue_ctx_inBounds) hfold2
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
  refine ⟨pre, post, blockIn, blockIn', ?_⟩
  exact {
    -- Block-list shape: discharged for the source by the split lemma.
    srcList := hsrcList
    -- TODO(PR 9, keystone): `operationList_rewriter_insertOp` (newOps before op) +
    -- `operationList_rewriter_eraseOp` (op removed) on the fold decomposition.
    tgtList := by sorry
    -- TODO(PR 9, keystone): insert/erase only touch `block`'s list (other blocks unchanged).
    otherBlocks := by sorry
    -- Number of produced values: directly from the pattern's `ReturnValues` obligation.
    newValuesSize := hReturnValues rewriter.ctx op opInBounds newCtxPat newOps newValues hpat
    -- TODO(PR 9, keystone): `ReturnValuesInBounds` gives in-bounds of `newCtxPat`; transport
    -- through insert/replace/erase (bounds monotonic, none of the `newValues` is `op`'s results).
    newValuesInBounds := by sorry
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
    -- TODO(PR 9, keystone): from `ReturnValuesInBounds` + bounds transport.
    mapResultsInBounds := by sorry
    -- TODO(PR 9, keystone): non-results survive (bounds transport minus erase-of-op).
    mapNonResultsInBounds := by sorry
    -- `eraseOp op` deallocates `op`, so it is no longer in bounds of `rewriter'.ctx`.
    opErased := by
      rw [PatternRewriter.eraseOp_ctx_eq herase]
      grind [WfRewriter.eraseOp, Rewriter.eraseOp,
        OperationPtr.InBounds.ne_of_inBounds_OperationPtr_dealloc]
    -- Every operation `≠ op` survives: into `newCtxPat` (pattern only creates), then the folds/erase.
    survives := fun o hoIn hne =>
      hSurviveOp o hne (hCreated.inBounds_mono (GenericPtr.operation o) (by grind))
    -- TODO(PR 9, keystone): `CrossContextFrame` under `σ`; `*_insertOp`/`*_detachOp` GetSet lemmas
    -- give unchanged type/props/results/successors, `replaceValue` redirects operands = `σ.applyToArray`.
    frame := by sorry
    -- Blocks stay in bounds: into `newCtxPat`, then the folds/erase (erase removes only `op`).
    blocksInBounds := fun b hb =>
      hSurviveBlock b (hCreated.inBounds_mono (GenericPtr.block b) (by grind))
    -- TODO(PR 9, keystone): parent ops of survivors preserved (op-list edits don't move other ops).
    parentOps := by sorry
    -- TODO(PR 9, keystone): `WfRewriter` ops preserve dominance well-formedness.
    newCtxDom := by sorry
    -- TODO(PR 9, keystone): `WfRewriter` ops preserve `Verified`.
    newCtxVerif := by sorry
    -- `σ` (`rewriteMapping`) is the identity off `op`'s results: it takes the `else` branch.
    mappingFixesNonResults := fun v vIn hv => by
      simp only [rewriteMapping, dif_neg hv]
    -- TODO(PR 9, keystone): each produced value is a result of some `newOp` (from the driver).
    newValuesAreResults := by sorry
    -- TODO(PR 9, keystone): operation-list edits leave block-argument lists untouched.
    blockArgsPreserved := by sorry
    -- Regions stay in bounds: into `newCtxPat`, then the folds/erase (erase removes only `op`).
    regionsInBounds := fun r hr =>
      hSurviveRegion r (hCreated.inBounds_mono (GenericPtr.region r) (by grind))
    -- TODO(PR 9, keystone): op-list edits leave survivors' region lists untouched.
    opRegionsPreserved := by sorry
    -- TODO(PR 9, keystone): op-list edits leave region entry blocks untouched.
    regionFirstBlockPreserved := by sorry
    -- `op` is not a function: it has no regions, so in particular not exactly one.
    opNotFunction := by simp [hOpRegions]
  }

end Veir
