import Veir.Prelude
import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.ForLean
import Veir.Rewriter.GetSet
import Veir.Rewriter.WfRewriter

open Std (HashMap)

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

namespace PatternRewriter

section array_inv

variable [Hashable α] [DecidableEq α] [BEq α]

abbrev ArrayInv (stack : Array (Option α)) (index : HashMap α Nat) :=
  ∀ (op : α) (i : Nat), index[op]? = some i → stack[i]? = some op

omit [DecidableEq α] in
@[grind .]
theorem ArrayInv.pop_nones (h : ArrayInv (α := α) stack index) : ArrayInv (stack.popWhile (· = none)) index := by
  grind [Array.getElem_of_getElem?, Array.getElem?_popWhile_of_false]

end array_inv

/--
- A worklist of operations to be processed by the pattern rewriter.
- This is essentially a LIFO stack, but we can also remove operations in O(1) time.
-/
@[grind]
structure Worklist where
  stack: Array (Option OperationPtr)
  indexInStack: HashMap OperationPtr Nat
  wf_index : ArrayInv stack indexInStack

def Worklist.empty : Worklist where
  stack := #[]
  indexInStack := HashMap.emptyWithCapacity
  wf_index := by grind

instance : Inhabited Worklist := ⟨Worklist.empty⟩

def Worklist.isEmpty (worklist: Worklist) : Bool :=
  worklist.indexInStack.size = 0

def Worklist.push (worklist: Worklist) (op: OperationPtr) : Worklist :=
  if h : worklist.indexInStack.contains op then
    worklist
  else
    let newIndex := worklist.stack.size
    { stack := worklist.stack.push (some op),
      indexInStack := worklist.indexInStack.insert op newIndex,
      wf_index := by grind }

def Worklist.pop (worklist: Worklist) : (Option OperationPtr) × Worklist :=
  let newStack := worklist.stack.popWhile (· = none)
  let hwf : ArrayInv newStack worklist.indexInStack := by grind
  let worklist := { worklist with stack := newStack, wf_index := hwf }
  if h : newStack.size = 0 then
    (none, { stack := newStack, indexInStack := HashMap.emptyWithCapacity, wf_index := by grind })
  else
    have hlen : 0 < newStack.size := by grind
    have : ((newStack.back hlen) ≠ none) := by grind
    let op := (newStack.back (by grind)).get (by cases h : newStack.back <;> grind [Option.isSome])
    have := hwf
    let newWorklist : Worklist := {
      stack := newStack.pop,
      indexInStack := worklist.indexInStack.erase op,
      wf_index := by grind
    }
    (op, newWorklist)

def Worklist.remove (worklist: Worklist) (op: OperationPtr) : Worklist :=
  match h : worklist.indexInStack.get? op with
  | some index =>
    { stack := worklist.stack.set index none (by grind),
      indexInStack := worklist.indexInStack.erase op
      wf_index := by grind
    }
  | none =>
    worklist

-- TODO: remove this lemma and/or move it somewhere reasonable
@[local grind →]
theorem OperationPtr.inBounds_of_mem_operations_keys (ctx : IRContext OpInfo) :
    (op ∈ ctx.operations.keys) → op.InBounds ctx := by
  grind [OperationPtr.InBounds]

/--
- Populate a worklist with all operations that exist in the given context, and that have
- a parent operation.
-/
def Worklist.createFromContext (ctx: WfIRContext OpInfo) : Worklist := Id.run do
  let mut worklist := Worklist.empty
  for h : op in ctx.raw.operations.keys do
    if (op.get ctx.raw (by grind)).parent.isSome then
      worklist := worklist.push op
  worklist

end PatternRewriter

@[grind]
structure PatternRewriter (OpInfo : Type) [HasOpInfo OpInfo] where
  ctx: WfIRContext OpInfo
  hasDoneAction: Bool
  worklist: PatternRewriter.Worklist

instance : Inhabited (PatternRewriter OpInfo) :=
  ⟨{ ctx := default, hasDoneAction := false, worklist := default }⟩

variable {rewriter : PatternRewriter OpInfo}

namespace PatternRewriter

private def addUseChainUserInWorklist (rewriter: PatternRewriter OpInfo) (useChain: Option OpOperandPtr) (maxIteration : Nat)
    (huc : useChain.maybe OpOperandPtr.InBounds rewriter.ctx.raw := by grind) : PatternRewriter OpInfo :=
  match maxIteration with
  | maxIteration + 1 =>
    match useChain with
    | some use =>
      let useStruct := (use.get rewriter.ctx.raw (by grind))
      let userOp := useStruct.owner
      let nextUse := useStruct.nextUse
      let rewriter := {rewriter with worklist := rewriter.worklist.push userOp}
      rewriter.addUseChainUserInWorklist nextUse maxIteration
    | none => rewriter
  | 0 => rewriter

@[simp, grind =]
theorem addUseChainUserInWorklist_same_ctx
    {rewriter : PatternRewriter OpInfo}
    {huc : Option.maybe OpOperandPtr.InBounds useChain rewriter.ctx.raw}:
    (addUseChainUserInWorklist rewriter useChain maxIteration huc).ctx = rewriter.ctx := by
  induction maxIteration generalizing rewriter useChain
  · grind [addUseChainUserInWorklist]
  · simp [addUseChainUserInWorklist]; grind

-- TODO: move this somewhere
@[local grind .]
theorem ValuePtr.inBounds_getFirstUse {value : ValuePtr} (hv : value.InBounds ctx.raw) :
    (value.getFirstUse ctx.raw hv).maybe OpOperandPtr.InBounds ctx.raw := by
  grind [Option.maybe]

private def addUsersInWorklist (rewriter: PatternRewriter OpInfo) (value: ValuePtr)
    (hv : value.InBounds rewriter.ctx.raw) : PatternRewriter OpInfo :=
  let useChain := value.getFirstUse rewriter.ctx.raw (by grind)
  rewriter.addUseChainUserInWorklist useChain 1_000_000_000 (by grind [Option.maybe])

@[grind =]
theorem addUsersInWorklist_same_ctx :
    (addUsersInWorklist rewriter value hv).ctx = rewriter.ctx := by
  simp [addUsersInWorklist]


def createOp (rewriter: PatternRewriter OpInfo) (opType: OpInfo)
    (resultTypes: Array TypeAttr) (operands: Array ValuePtr)
    (blockOperands: Array BlockPtr) (regions: Array RegionPtr) (properties: HasOpInfo.propertiesOf opType)
    (insertionPoint: Option InsertPoint)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds rewriter.ctx.raw)
    (hblockOperands : ∀ blockOper, blockOper ∈ blockOperands → blockOper.InBounds rewriter.ctx.raw)
    (hregions : ∀ region, region ∈ regions → region.InBounds rewriter.ctx.raw)
    (hins : insertionPoint.maybe InsertPoint.InBounds rewriter.ctx.raw) : Option ((PatternRewriter OpInfo) × OperationPtr) := do
  rlet (newCtx, op) ← WfRewriter.createOp rewriter.ctx opType resultTypes operands blockOperands regions properties insertionPoint hoper hblockOperands hregions hins
  if insertionPoint.isNone then
    ({ rewriter with ctx := newCtx}, op)
  else
    ({ rewriter with ctx := newCtx, hasDoneAction := true , worklist := rewriter.worklist.push op}, op)

/--
Create an operation and insert it at a given location, panicking if any operand, block operand,
or region is out of bounds, if the insertion point is out of bounds, or if the operation could
not be created.
-/
def createOp! (rewriter: PatternRewriter OpInfo) (opType: OpInfo)
    (resultTypes: Array TypeAttr) (operands: Array ValuePtr)
    (blockOperands: Array BlockPtr) (regions: Array RegionPtr) (properties: HasOpInfo.propertiesOf opType)
    (insertionPoint: Option InsertPoint) : Option ((PatternRewriter OpInfo) × OperationPtr) := do
  let (newCtx, op) ← WfRewriter.createOp! rewriter.ctx opType resultTypes operands blockOperands
    regions properties insertionPoint
  if insertionPoint.isNone then
    ({ rewriter with ctx := newCtx}, op)
  else
    ({ rewriter with ctx := newCtx, hasDoneAction := true , worklist := rewriter.worklist.push op}, op)

def insertOp (rewriter: PatternRewriter OpInfo) (op: OperationPtr) (ip : InsertPoint)
    (newOpIn: op.InBounds rewriter.ctx.raw := by grind) (insIn : ip.InBounds rewriter.ctx.raw)
    : Option (PatternRewriter OpInfo) := do
  rlet newCtx ← WfRewriter.insertOp rewriter.ctx op ip (by grind) (by grind)
  some { rewriter with
    ctx := newCtx,
    hasDoneAction := true,
    worklist := rewriter.worklist.push op,
  }

/--
Insert an operation at a given location, panicking if the operation or the insertion point is out
of bounds, or if the insertion point does not have a parent block.
-/
def insertOp! (rewriter: PatternRewriter OpInfo) (op: OperationPtr) (ip : InsertPoint)
    : PatternRewriter OpInfo :=
  { rewriter with
    ctx := WfRewriter.insertOp! rewriter.ctx op ip,
    hasDoneAction := true,
    worklist := rewriter.worklist.push op,
  }

/--
Walk a use chain and check that at most one operation besides `exceptOp` uses
the value: uses owned by `exceptOp` are ignored, and multiple uses from a
single other operation count as one user. Returns `false` when out of fuel.
-/
private def useChainHasAtMostOneUserBesides (ctx : IRContext OpInfo)
    (useChain : Option OpOperandPtr) (exceptOp : OperationPtr)
    (otherUser : Option OperationPtr) (maxIteration : Nat) : Bool :=
  match maxIteration with
  | maxIteration + 1 =>
    match useChain with
    | some use =>
      let useStruct := use.get! ctx
      let owner := useStruct.owner
      if owner = exceptOp ∨ otherUser = some owner then
        useChainHasAtMostOneUserBesides ctx useStruct.nextUse exceptOp otherUser maxIteration
      else if otherUser.isNone then
        useChainHasAtMostOneUserBesides ctx useStruct.nextUse exceptOp (some owner) maxIteration
      else
        false
    | none => true
  | 0 => false

def eraseOp (rewriter: PatternRewriter OpInfo) (op: OperationPtr)
    (opRegions : op.getNumRegions! rewriter.ctx.raw = 0 := by grind)
    (opUses : !op.hasUses! rewriter.ctx.raw := by grind)
    (hOp : op.InBounds rewriter.ctx.raw := by grind)
    : PatternRewriter OpInfo := Id.run do
  let ctx := rewriter.ctx.raw
  -- Ops defining this op's operands may become dead or newly canonicalizable
  -- once the uses from `op` disappear; re-enqueue those with at most one
  -- remaining user, mirroring MLIR's `addOperandsToWorklist`.
  let mut worklist := rewriter.worklist.remove op
  for operand in op.getOperands ctx hOp do
    let some defOp := operand.getDefiningOp! ctx | continue
    if useChainHasAtMostOneUserBesides ctx (operand.getFirstUse! ctx) op none 1_000_000_000 then
      worklist := worklist.push defOp
  return { rewriter with
    ctx := WfRewriter.eraseOp rewriter.ctx op opRegions opUses hOp,
    hasDoneAction := true,
    worklist
  }

/--
Erase an operation, panicking if the operation is out of bounds, has regions, or has uses.
-/
def eraseOp! (rewriter: PatternRewriter OpInfo) (op: OperationPtr)
    : PatternRewriter OpInfo :=
  if hOp : op.InBounds rewriter.ctx.raw then
    if opRegions : op.getNumRegions! rewriter.ctx.raw = 0 then
      if opUses : !op.hasUses! rewriter.ctx.raw then
        rewriter.eraseOp op opRegions opUses hOp
      else
        panic! "PatternRewriter.eraseOp! failed: operation has uses"
    else
      panic! "PatternRewriter.eraseOp! failed: operation has regions"
  else
    panic! "PatternRewriter.eraseOp! failed: operation is out of bounds"

def replaceOp (rewriter: PatternRewriter OpInfo) (oldOp newOp: OperationPtr)
    (opNe : oldOp ≠ newOp := by grind)
    (hpar : (oldOp.get! rewriter.ctx.raw).parent.isSome = true := by grind)
    (noRegions : oldOp.getNumRegions! rewriter.ctx.raw = 0 := by grind)
    (oldIn : oldOp.InBounds rewriter.ctx.raw := by grind)
    (newIn : newOp.InBounds rewriter.ctx.raw := by grind)
    : Option (PatternRewriter OpInfo) := do
  let mut rw : {r : PatternRewriter OpInfo // r.ctx = rewriter.ctx } := ⟨rewriter, by grind⟩
  for h : i in 0...(oldOp.getNumResults rewriter.ctx.raw (by grind)) do
    rw := ⟨rw.val.addUsersInWorklist (oldOp.getResult i) (by grind), by grind⟩
  let rewriter := rw.val
  let newCtx ← WfRewriter.replaceOp? rewriter.ctx oldOp newOp (by grind) (by grind) (by grind) (by grind)
  some { rewriter with
    ctx := newCtx,
    hasDoneAction := true,
    worklist := rewriter.worklist.remove oldOp |>.push newOp,
  }

/--
Replace all results of an operation with the results of another, erasing the replaced operation.
Panics if the two operations are equal, if the old operation has no parent or has regions, if
either operation is out of bounds, or if the operations have different numbers of results.
-/
def replaceOp! (rewriter: PatternRewriter OpInfo) (oldOp newOp: OperationPtr)
    : PatternRewriter OpInfo :=
  if oldIn : oldOp.InBounds rewriter.ctx.raw then Id.run do
    let mut rw : {r : PatternRewriter OpInfo // r.ctx = rewriter.ctx } := ⟨rewriter, by grind⟩
    for h : i in 0...(oldOp.getNumResults rewriter.ctx.raw oldIn) do
      rw := ⟨rw.val.addUsersInWorklist (oldOp.getResult i) (by grind), by grind⟩
    let rewriter := rw.val
    let newCtx := WfRewriter.replaceOp! rewriter.ctx oldOp newOp
    return { rewriter with
      ctx := newCtx,
      hasDoneAction := true,
      worklist := rewriter.worklist.remove oldOp |>.push newOp,
    }
  else
    panic! "PatternRewriter.replaceOp! failed: old operation is out of bounds"

def replaceValue (rewriter: PatternRewriter OpInfo) (oldVal newVal: ValuePtr)
    (neValues : oldVal ≠ newVal := by grind)
    (oldIn: oldVal.InBounds rewriter.ctx.raw := by grind)
    (newIn: newVal.InBounds rewriter.ctx.raw := by grind) : PatternRewriter OpInfo :=
  -- TODO: add users of oldVal to worklist
  let rewriter := rewriter.addUsersInWorklist oldVal (by grind)
  let ctx := WfRewriter.replaceValue rewriter.ctx oldVal newVal
  { rewriter with ctx, hasDoneAction := true}

/--
Replace all uses of a value by another value, panicking if the two values are equal, or if either
value is out of bounds.
-/
def replaceValue! (rewriter: PatternRewriter OpInfo) (oldVal newVal: ValuePtr)
    : PatternRewriter OpInfo :=
  if oldIn : oldVal.InBounds rewriter.ctx.raw then
    let rewriter := rewriter.addUsersInWorklist oldVal oldIn
    let ctx := WfRewriter.replaceValue! rewriter.ctx oldVal newVal
    { rewriter with ctx, hasDoneAction := true }
  else
    panic! "PatternRewriter.replaceValue! failed: old value is out of bounds"

def createBlock (rewriter: PatternRewriter OpInfo)
    (argTypes: Array TypeAttr)
    (insertPoint : Option BlockInsertPoint)
    (insertPointIn : insertPoint.maybe BlockInsertPoint.InBounds rewriter.ctx.raw := by grind)
    : Option (PatternRewriter OpInfo × BlockPtr) := do
  rlet (newCtx, op) ← WfRewriter.createBlock rewriter.ctx argTypes insertPoint (by grind)
  ({ rewriter with ctx := newCtx, hasDoneAction := true }, op)

def insertBlock (rewriter: PatternRewriter OpInfo) (block: BlockPtr) (ip : BlockInsertPoint)
    (newBlockIn: block.InBounds rewriter.ctx.raw := by grind)
    (ipIn : ip.InBounds rewriter.ctx.raw := by grind) : Option (PatternRewriter OpInfo) := do
  rlet newCtx ← WfRewriter.insertBlock rewriter.ctx block ip
  some { rewriter with
    ctx := newCtx,
    hasDoneAction := true
  }

end PatternRewriter

abbrev RewritePattern (OpInfo : Type) [HasOpInfo OpInfo] :=
  (rewriter : PatternRewriter OpInfo) → (op : OperationPtr) →
  (opInBounds : op.InBounds rewriter.ctx.raw) → Option (PatternRewriter OpInfo)

/--
  A local rewrite that can only replace a matched operation with a list of new operations.
  The pattern returns, if successful, a list of new operations to insert and a list of values to
  replace the old results with.
-/
abbrev LocalRewritePattern (OpInfo : Type) [HasOpInfo OpInfo] :=
  WfIRContext OpInfo → OperationPtr → Option (WfIRContext OpInfo × Option (Array OperationPtr × Array ValuePtr))

def RewritePattern.fromLocalRewrite (pattern : LocalRewritePattern OpInfo) : RewritePattern OpInfo :=
  fun rewriter op _opInBounds => do
    match pattern rewriter.ctx op with
    -- error while applying pattern
    | none => none
    -- no match
    | some (newCtx, none) => return {rewriter with ctx := newCtx, hasDoneAction := false}
    -- match and rewrite
    | some (newCtx, some (newOps, newRes)) =>
      let mut rewriter := { rewriter with ctx := newCtx, hasDoneAction := true }
      for newOp in newOps do
        rewriter := rewriter.insertOp! newOp (InsertPoint.before op)
      for (res, i) in newRes.zipIdx do
        rewriter := rewriter.replaceValue! (op.getResult i) res
      -- All results of `op` have been replaced above, so `op` is dead and can be erased.
      return rewriter.eraseOp! op

/--
  Greedy pattern application: transforms a list of patterns into a single pattern that applies
  them repeatedly in order.
-/
def RewritePattern.GreedyRewritePattern (patterns : Array (RewritePattern OpInfo)) : RewritePattern OpInfo :=
  fun rewriter op _ => do
    let hasDoneAction := rewriter.hasDoneAction
    let mut rewriter := { rewriter with hasDoneAction := false }
    for pattern in patterns do
      if opInBounds : op.InBounds rewriter.ctx.raw then
        match pattern rewriter op opInBounds with
        | some newRewriter =>
          rewriter := newRewriter
          if rewriter.hasDoneAction then
            return rewriter
        | none => failure
      else
        failure
    return { rewriter with hasDoneAction := hasDoneAction }

/--
- Apply the given rewrite pattern to all operations in the context (possibly multiple times).
- Return the new context, and a boolean indicating whether any changes were made.
- If any pattern failed, return none.
-/
private partial def RewritePattern.applyOnceInContext
    (pattern: RewritePattern OpInfo) (ctx: WfIRContext OpInfo) :
    Option (Bool × WfIRContext OpInfo) := do
  let worklist := PatternRewriter.Worklist.createFromContext ctx
  let mut rewriter : PatternRewriter OpInfo := { ctx, hasDoneAction := false, worklist }
  while !rewriter.worklist.isEmpty do
    let (opOpt, newWorklist) := rewriter.worklist.pop
    let op := opOpt.get!
    rewriter := { rewriter with worklist := newWorklist }
    if hin : op.InBounds rewriter.ctx.raw then
      -- Erase trivially dead operations directly, as in MLIR's greedy driver.
      if hdead : op.getNumRegions! rewriter.ctx.raw = 0
          ∧ !op.hasUses! rewriter.ctx.raw
          ∧ !op.hasSideEffects rewriter.ctx.raw then
        rewriter := rewriter.eraseOp op hdead.1 hdead.2.1 hin
      else
        rewriter ← pattern rewriter op (by grind)
    else
      failure
  pure (rewriter.hasDoneAction, rewriter.ctx)

def RewritePattern.applyInContext (pattern: RewritePattern OpInfo)
    (ctx: WfIRContext OpInfo) : Option (WfIRContext OpInfo) := do
  let mut hasDoneAction := true
  let mut ctx := ctx
  while hasDoneAction do
    let (lastHasDoneAction, newCtx) ← pattern.applyOnceInContext ctx
    ctx := newCtx
    hasDoneAction := lastHasDoneAction
  pure ctx
