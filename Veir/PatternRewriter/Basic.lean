module

public import Veir.Rewriter.WfRewriter
public import Veir.Interfaces.DeadCodeInterfaces
public import Veir.Interfaces.FunctionInterfaces


import all Veir.IR.Basic

public section

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

/-- Push an operation during initial seeding, where the traversal visits it only once. -/
@[inline]
private def Worklist.pushNew (worklist : Worklist) (op : OperationPtr) : Worklist :=
  let newIndex := worklist.stack.size
  { stack := worklist.stack.push (some op)
    indexInStack := worklist.indexInStack.insert op newIndex
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
      let userOp := use.getOwner rewriter.ctx.raw (by grind)
      let nextUse := use.getNextUse rewriter.ctx.raw (by grind)
      let rewriter := {rewriter with worklist := rewriter.worklist.push userOp}
      rewriter.addUseChainUserInWorklist nextUse maxIteration
    | none => rewriter
  | 0 => rewriter

@[simp, grind =]
private theorem addUseChainUserInWorklist_same_ctx
    {rewriter : PatternRewriter OpInfo}
    {huc : Option.maybe OpOperandPtr.InBounds useChain rewriter.ctx.raw}:
    (addUseChainUserInWorklist rewriter useChain maxIteration huc).ctx = rewriter.ctx := by
  induction maxIteration generalizing rewriter useChain
  · grind [addUseChainUserInWorklist]
  · simp [addUseChainUserInWorklist]; grind

-- TODO: move this somewhere
private theorem ValuePtr.inBounds_getFirstUse {value : ValuePtr} (hv : value.InBounds ctx.raw) :
    (value.getFirstUse ctx.raw hv).maybe OpOperandPtr.InBounds ctx.raw := by
  grind [Option.maybe_def]

private def addUsersInWorklist (rewriter: PatternRewriter OpInfo) (value: ValuePtr)
    (hv : value.InBounds rewriter.ctx.raw) : PatternRewriter OpInfo :=
  let useChain := value.getFirstUse rewriter.ctx.raw (by grind)
  rewriter.addUseChainUserInWorklist useChain 1_000_000_000 (by
    grind [Option.maybe_def, ValuePtr.inBounds_getFirstUse])

@[grind =]
private theorem addUsersInWorklist_same_ctx :
    (addUsersInWorklist rewriter value hv).ctx = rewriter.ctx := by
  simp [addUsersInWorklist]


def createOp (rewriter: PatternRewriter OpInfo) (opType: OpInfo)
    (resultTypes: Array TypeAttr) (operands: Array ValuePtr)
    (blockOperands: Array BlockPtr) (regions: Array RegionPtr) (properties: propertiesOf opType)
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
    (blockOperands: Array BlockPtr) (regions: Array RegionPtr) (properties: propertiesOf opType)
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
Set the properties of an operation in place, and re-enqueue it.
-/
def setProperties {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
    (rewriter: PatternRewriter OpInfo) (op: OperationPtr) (opCode : Dialect)
    (newProps : propertiesOf opCode)
    (opIn : op.InBounds rewriter.ctx.raw := by grind)
    (hprop : op.getOpType! rewriter.ctx.raw = opCode := by grind)
    : PatternRewriter OpInfo :=
  { rewriter with
    ctx := WfRewriter.setProperties rewriter.ctx op opCode newProps opIn hprop,
    hasDoneAction := true,
    worklist := rewriter.worklist.push op,
  }

/--
Set the properties of an operation in place, panicking if the operation is out of bounds, or if
the property types don't match.
-/
def setProperties! {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
    (rewriter: PatternRewriter OpInfo) (op: OperationPtr) (opCode : Dialect)
    (newProps : propertiesOf opCode) : PatternRewriter OpInfo :=
  if opIn : op.InBounds rewriter.ctx.raw then
    if hprop : op.getOpType! rewriter.ctx.raw = opCode then
      rewriter.setProperties op opCode newProps opIn hprop
    else
      panic! "PatternRewriter.setProperties! failed: property types don't match"
  else
    panic! "PatternRewriter.setProperties! failed: operation is out of bounds"

/--
Walk a use chain and check that at most one operation besides `exceptOp` uses
the value: uses owned by `exceptOp` are ignored, and multiple uses from a
single other operation count as one user. An out-of-bounds use reads as the
default `OpOperand`, whose `nextUse` is `none`, ending the walk.
-/
private partial def useChainHasAtMostOneUserBesides (ctx : IRContext OpInfo)
    (useChain : Option OpOperandPtr) (exceptOp : OperationPtr)
    (otherUser : Option OperationPtr) : Bool :=
  match useChain with
  | some use =>
    let owner := use.getOwner! ctx
    if owner = exceptOp ∨ otherUser = some owner then
      useChainHasAtMostOneUserBesides ctx (use.getNextUse! ctx) exceptOp otherUser
    else if otherUser.isNone then
      useChainHasAtMostOneUserBesides ctx (use.getNextUse! ctx) exceptOp (some owner)
    else
      false
  | none => true

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
    let some defOp := operand.definingOp? | continue
    if useChainHasAtMostOneUserBesides ctx (operand.getFirstUse! ctx) op none then
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

/--
Seed the worklist with the operations nested under `op` (not `op` itself), pushing them in
reverse post-order so that they are popped in post-order. (Erasing trivially dead operations
here rather than pushing them -- a trick from InstCombine that allows removal of chains of dead
operations -- is currently disabled.)
-/
private partial def seedNestedReversePostOrder (ctx : IRContext OpInfo) (worklist : Worklist)
    (op : OperationPtr) : Worklist := Id.run do
  let mut worklist := worklist
  let numRegions := op.getNumRegions! ctx
  for i in 0...numRegions do
    let mut block? := (op.getRegion! ctx (numRegions - 1 - i)).getLastBlock! ctx
    while let some block := block? do
      let mut child? := block.getLastOp! ctx
      while let some child := child? do
        let prev? := child.getPrevOp! ctx
        /- Disabled for now: erasing dead ops during seeding needs proofs we aren't ready for.
        if hdead : child.isTriviallyDead rewriter.ctx.raw then
          rewriter := if hin : child.InBounds rewriter.ctx.raw then
            { rewriter with
              ctx := WfRewriter.eraseOp rewriter.ctx child hdead.1 hdead.2.1 hin
              hasDoneAction := true }
          else
            panic! "PatternRewriter.seedNestedReversePostOrder: operation is out of bounds"
        else
        -/
        worklist := worklist.pushNew child
        worklist := seedNestedReversePostOrder ctx worklist child
        child? := prev?
      block? := block.getPrevBlock! ctx
  worklist

def replaceOp (rewriter: PatternRewriter OpInfo) (oldOp newOp: OperationPtr)
    (opNe : oldOp ≠ newOp := by grind)
    (hpar : (oldOp.getParent! rewriter.ctx.raw).isSome = true := by grind)
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
    -- Read the old results before the pattern consumes the context so it can update in place.
    let oldResults := op.getResults! rewriter.ctx.raw
    match pattern rewriter.ctx op with
    -- error while applying pattern
    | none => none
    -- no match
    | some (newCtx, none) => return {rewriter with ctx := newCtx, hasDoneAction := false}
    -- match and rewrite
    | some (newCtx, some (newOps, newRes)) =>
      guard (newRes.size = op.getNumResults! newCtx.raw)
      -- Cyclic SSA in unreachable code can alias a replacement with an old root result.
      guard (∀ value ∈ newRes, value ∉ oldResults)
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

/-- Pop and process one operation. Either delete the operation if it is trivially dead, or
apply the given pattern to it. -/
def RewritePattern.worklistStep (pattern : RewritePattern OpInfo)
    (rewriter : PatternRewriter OpInfo) : Option (PatternRewriter OpInfo) := do
  let (opOpt, newWorklist) := rewriter.worklist.pop
  let op := opOpt.get!
  let rewriter := { rewriter with worklist := newWorklist }
  if hin : op.InBounds rewriter.ctx.raw then
    if hdead : op.isTriviallyDead rewriter.ctx.raw ∧ (op.getEffects rewriter.ctx.raw).allocates = false then
      return rewriter.eraseOp op hdead.1.1 hdead.1.2.1 hin
    else
      pattern rewriter op hin
  else
    failure

/-- Process the current worklist. -/
def RewritePattern.runWorklist (pattern : RewritePattern OpInfo)
    (rewriter : PatternRewriter OpInfo) : Option (PatternRewriter OpInfo) := do
  if rewriter.worklist.isEmpty then return rewriter
  let next ← pattern.worklistStep rewriter
  pattern.runWorklist next
partial_fixpoint

/-- Apply the given rewrite pattern to all operations nested under `root` (possibly multiple times).
Return the new context, and a boolean indicating whether any changes were made. If any pattern
failed, return none. -/
private def RewritePattern.applyOnceInContext
    (pattern : RewritePattern OpInfo) (ctx : WfIRContext OpInfo) (root : OperationPtr) :
    Option (Bool × WfIRContext OpInfo) := do
  let rewriter : PatternRewriter OpInfo :=
    { ctx, hasDoneAction := false, worklist := PatternRewriter.seedNestedReversePostOrder ctx.raw .empty root }
  let final ← pattern.runWorklist rewriter
  pure (final.hasDoneAction, final.ctx)

/--
Apply the given rewrite pattern to the operations nested under `root`, visiting them in
post-order. Rounds are repeated until one makes no change, or until `maxRounds` rounds have run.
-/
def RewritePattern.applyInContext (pattern: RewritePattern OpInfo)
    (ctx: WfIRContext OpInfo) (root : OperationPtr) (maxRounds : Nat := 10) :
    Option (WfIRContext OpInfo) := do
  let mut ctx := ctx
  for _ in 0...maxRounds do
    let (changed, newCtx) ← pattern.applyOnceInContext ctx root
    ctx := newCtx
    if !changed then
      break
  pure ctx

/--
The function-like operations nested under `op`, in program order. The search does not enter
functions, since rewriting a function also covers anything nested in it.
-/
partial def collectNestedFunctions (ctx : IRContext OpInfo) (op : OperationPtr)
    (acc : Array OperationPtr := #[]) : Array OperationPtr := Id.run do
  let mut acc := acc
  for region in op.getRegions! ctx do
    let mut block? := region.getFirstBlock! ctx
    while let some block := block? do
      let mut child? := block.getFirstOp! ctx
      while let some child := child? do
        acc := if child.isFunctionLike ctx then acc.push child
          else collectNestedFunctions ctx child acc
        child? := child.getNextOp! ctx
      block? := block.getNextBlock! ctx
  acc

/--
Apply the given rewrite pattern to the body of each function nested under `root`, leaving
everything outside of functions alone. Code generation passes use this to lower functions but
not global initializers, which stay LLVM operations until they are printed, much as LLVM's
machine function passes never see the initializers that `AsmPrinter` emits.
-/
def RewritePattern.applyToFunctions (pattern: RewritePattern OpInfo)
    (ctx: WfIRContext OpInfo) (root : OperationPtr) (maxRounds : Nat := 10) :
    Option (WfIRContext OpInfo) := do
  let mut ctx := ctx
  for func in collectNestedFunctions ctx.raw root do
    ctx ← pattern.applyInContext ctx func maxRounds
  pure ctx

/-- Pop one candidate, skipping ineligible operations before either mutation branch. -/
def RewritePattern.worklistStepIf (pattern : RewritePattern OpInfo)
    (eligible : WfIRContext OpInfo → OperationPtr → Bool)
    (rewriter : PatternRewriter OpInfo) : Option (PatternRewriter OpInfo) := do
  let (opOpt, remaining) := rewriter.worklist.pop
  let op := opOpt.get!
  if op.InBounds rewriter.ctx.raw then
    if eligible rewriter.ctx op then pattern.worklistStep rewriter
    else pure { rewriter with worklist := remaining }
  else failure

/-- Process the worklist with a context-dependent eligibility filter. -/
def RewritePattern.runWorklistIf (pattern : RewritePattern OpInfo)
    (eligible : WfIRContext OpInfo → OperationPtr → Bool)
    (rewriter : PatternRewriter OpInfo) : Option (PatternRewriter OpInfo) := do
  if rewriter.worklist.isEmpty then return rewriter
  let next ← pattern.worklistStepIf eligible rewriter
  pattern.runWorklistIf eligible next
partial_fixpoint

/-- One seeded, filtered worklist round. -/
def RewritePattern.applyOnceInContextIf (pattern : RewritePattern OpInfo)
    (eligible : WfIRContext OpInfo → OperationPtr → Bool)
    (ctx : WfIRContext OpInfo) (root : OperationPtr) :
    Option (Bool × WfIRContext OpInfo) := do
  let rewriter : PatternRewriter OpInfo :=
    { ctx, hasDoneAction := false, worklist := PatternRewriter.seedNestedReversePostOrder ctx.raw .empty root }
  let final ← pattern.runWorklistIf eligible rewriter
  pure (final.hasDoneAction, final.ctx)

/-- Bounded rounds, skipping unsupported candidates before rewriting and DCE. -/
def RewritePattern.applyInContextIf (pattern : RewritePattern OpInfo)
    (eligible : WfIRContext OpInfo → OperationPtr → Bool)
    (ctx : WfIRContext OpInfo) (root : OperationPtr) (maxRounds : Nat := 10) :
    Option (WfIRContext OpInfo) := do
  let mut ctx := ctx
  for _ in 0...maxRounds do
    let (changed, newCtx) ← pattern.applyOnceInContextIf eligible ctx root
    ctx := newCtx
    if !changed then break
  pure ctx

/-- Filtered rewriting of each nested function. -/
def RewritePattern.applyToFunctionsIf (pattern : RewritePattern OpInfo)
    (eligible : WfIRContext OpInfo → OperationPtr → Bool)
    (ctx : WfIRContext OpInfo) (root : OperationPtr) (maxRounds : Nat := 10) :
    Option (WfIRContext OpInfo) := do
  let mut ctx := ctx
  for func in collectNestedFunctions ctx.raw root do
    ctx ← pattern.applyInContextIf eligible ctx func maxRounds
  pure ctx
