import Veir.Prelude
import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.ForLean
import Veir.Rewriter.GetSetInBounds

open Std (HashMap)

namespace Veir

variable {dT : Type} [HasProperties dT]
variable {ctx : IRContext dT}

namespace PatternRewriter

section array_inv

variable [Hashable α] [DecidableEq α] [BEq α]

abbrev ArrayInv (stack : Array (Option α)) (index : HashMap α Nat) :=
  ∀ (op : α) (i : Nat), index[op]? = some i → stack[i]? = some op

set_option warn.sorry false in
@[grind .]
theorem ArrayInv.popNones (h : ArrayInv (α := α) stack index) : ArrayInv (stack.popWhile (· = none)) index := by
  sorry

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
theorem OperationPtr.inBounds_of_mem_operations_keys (ctx : IRContext dT) :
    (op ∈ ctx.operations.keys) → op.InBounds ctx := by
  grind [OperationPtr.InBounds]

/--
- Populate a worklist with all operations that exist in the given context, and that have
- a parent operation.
-/
def Worklist.createFromContext (ctx: IRContext dT) : Worklist := Id.run do
  let mut worklist := Worklist.empty
  for h : op in ctx.operations.keys do
    if (op.get ctx (by grind)).parent.isSome then
      worklist := worklist.push op
  worklist

end PatternRewriter

@[grind]
structure PatternRewriter (dT : Type) [HasProperties dT] where
  ctx: IRContext dT
  hasDoneAction: Bool
  worklist: PatternRewriter.Worklist
  ctx_fib : ctx.FieldsInBounds

variable {rewriter : PatternRewriter dT}

namespace PatternRewriter

private def addUseChainUserInWorklist (rewriter: PatternRewriter dT) (useChain: Option OpOperandPtr) (maxIteration : Nat)
    (huc : useChain.maybe OpOperandPtr.InBounds rewriter.ctx := by grind) : (PatternRewriter dT) :=
  match maxIteration with
  | maxIteration + 1 =>
    match useChain with
    | some use =>
      let useStruct := (use.get rewriter.ctx (by grind))
      let userOp := useStruct.owner
      let nextUse := useStruct.nextUse
      let rewriter := {rewriter with worklist := rewriter.worklist.push userOp}
      rewriter.addUseChainUserInWorklist nextUse maxIteration
    | none => rewriter
  | 0 => rewriter

@[simp, grind =]
theorem addUseChainUserInWorklist_same_ctx {rewriter : PatternRewriter dT} {huc : Option.maybe OpOperandPtr.InBounds useChain rewriter.ctx}:
    (addUseChainUserInWorklist rewriter useChain maxIteration huc).ctx = rewriter.ctx := by
  induction maxIteration generalizing rewriter useChain
  · grind [addUseChainUserInWorklist]
  · simp [addUseChainUserInWorklist]; grind

-- TODO: move this somewhere
@[local grind .]
theorem ValuePtr.inBounds_getFirstUse {value : ValuePtr} (hv : value.InBounds ctx) (hx : ctx.FieldsInBounds) :
    (value.getFirstUse ctx hv).maybe OpOperandPtr.InBounds ctx := by
  grind [Option.maybe]

private def addUsersInWorklist (rewriter: PatternRewriter dT) (value: ValuePtr) (hv : value.InBounds rewriter.ctx) : PatternRewriter dT :=
  let useChain := value.getFirstUse rewriter.ctx (by grind)
  rewriter.addUseChainUserInWorklist useChain 1_000_000_000 (by grind [Option.maybe])

@[grind =]
theorem addUsersInWorklist_same_ctx :
    (addUsersInWorklist rewriter value hv).ctx = rewriter.ctx := by
  simp [addUsersInWorklist]


def createOp (rewriter: PatternRewriter dT) (opType: dT)
    (resultTypes: Array TypeAttr) (operands: Array ValuePtr)
    (blockOperands: Array BlockPtr) (regions: Array RegionPtr) (properties: HasProperties.propertiesOf opType)
    (insertionPoint: Option InsertPoint)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds rewriter.ctx)
    (hblockOperands : ∀ blockOper, blockOper ∈ blockOperands → blockOper.InBounds rewriter.ctx)
    (hregions : ∀ region, region ∈ regions → region.InBounds rewriter.ctx)
    (hins : insertionPoint.maybe InsertPoint.InBounds rewriter.ctx) : Option ((PatternRewriter dT) × OperationPtr) := do
  rlet (newCtx, op) ← Rewriter.createOp rewriter.ctx opType resultTypes operands blockOperands regions properties insertionPoint hoper hblockOperands hregions hins (by grind)
  if h : insertionPoint.isNone then
    ({ rewriter with ctx := newCtx, ctx_fib := by grind }, op)
  else
    ({ rewriter with ctx := newCtx, hasDoneAction := true , worklist := rewriter.worklist.push op, ctx_fib := by grind }, op)

set_option warn.sorry false in
def insertOp (rewriter: PatternRewriter dT) (op: OperationPtr) (ip : InsertPoint)
    (newOpIn: op.InBounds rewriter.ctx := by grind) (insIn : ip.InBounds rewriter.ctx) : Option (PatternRewriter dT) := do
  let newCtx ← Rewriter.insertOp? rewriter.ctx op ip (by grind) (by grind) (by grind)
  some { rewriter with
    ctx := newCtx,
    hasDoneAction := true,
    worklist := rewriter.worklist.push op,
    ctx_fib := by sorry
  }

set_option warn.sorry false in
def eraseOp (rewriter: PatternRewriter dT) (op: OperationPtr)
    (hop : op.InBounds rewriter.ctx) : Option (PatternRewriter dT) := do
  let newCtx ← Rewriter.eraseOp rewriter.ctx op (by grind) hop
  some { rewriter with
    ctx := newCtx,
    hasDoneAction := true,
    worklist := rewriter.worklist.remove op,
    ctx_fib := by sorry
  }

set_option warn.sorry false in
def replaceOp (rewriter: PatternRewriter dT) (oldOp newOp: OperationPtr)
    (ho : oldOp.InBounds rewriter.ctx) (hn : newOp.InBounds rewriter.ctx)
    (hpar : (oldOp.get rewriter.ctx ho).parent.isSome) : Option (PatternRewriter dT) := do
  let mut rw : {r : PatternRewriter dT // r.ctx = rewriter.ctx } := ⟨rewriter, by grind⟩
  for h : i in 0...(oldOp.getNumResults rewriter.ctx (by grind)) do
    rw := ⟨rw.val.addUsersInWorklist (oldOp.getResult i) (by grind), by grind⟩
  let rewriter := rw.val
  let newCtx ← Rewriter.replaceOp? rewriter.ctx oldOp newOp (by grind) (by grind) (by grind) (by grind)
  some { rewriter with
    ctx := newCtx,
    hasDoneAction := true,
    worklist := rewriter.worklist.remove oldOp |>.push newOp,
    ctx_fib := by sorry -- relies on well-formedness!
  }

set_option warn.sorry false in
def replaceValue (rewriter: PatternRewriter dT) (oldVal newVal: ValuePtr)
    (oldIn: oldVal.InBounds rewriter.ctx := by grind)
    (newIn: newVal.InBounds rewriter.ctx := by grind) : Option (PatternRewriter dT) := do
  -- TODO: add users of oldVal to worklist
  let rewriter := rewriter.addUsersInWorklist oldVal (by grind)
  let ctx ← Rewriter.replaceValue? rewriter.ctx oldVal newVal (by grind) (by grind) (by grind)
  some { rewriter with
    ctx,
    ctx_fib := by sorry -- relies on well-formedness!
    hasDoneAction := true
  }

end PatternRewriter

abbrev RewritePattern (dT : Type) [HasProperties dT] := (PatternRewriter dT) → OperationPtr → Option (PatternRewriter dT)

/--
  A local rewrite that can only replace a matched operation with a list of new operations.
  The pattern returns, if successful, a list of new operations to insert and a list of values to
  replace the old results with.
-/
abbrev LocalRewritePattern (dT : Type) [HasProperties dT] :=
  IRContext dT → OperationPtr → Option (IRContext dT × Option (Array OperationPtr × Array ValuePtr))

set_option warn.sorry false in
def RewritePattern.fromLocalRewrite (pattern : LocalRewritePattern dT) : RewritePattern dT :=
  fun rewriter op => do
    match pattern rewriter.ctx op with
    -- error while applying pattern
    | none => none
    -- no match
    | some (newCtx, none) => return {rewriter with ctx := newCtx, ctx_fib := by sorry, hasDoneAction := false}
    -- match and rewrite
    | some (newCtx, some (newOps, newRes)) =>
      let mut rewriter := { rewriter with ctx := newCtx, hasDoneAction := true, ctx_fib := by sorry }
      for newOp in newOps do
        rewriter ← rewriter.insertOp newOp (InsertPoint.before op) (by sorry) (by sorry)
      for (res, i) in newRes.zipIdx do
        rewriter ← rewriter.replaceValue (op.getResult i) res (by sorry) (by sorry)
      let mut operands : Array ValuePtr := #[]
      for i in 0...op.getNumOperands rewriter.ctx (by sorry) do
        operands := operands.push (op.getOperand! rewriter.ctx i)
      rewriter ← rewriter.eraseOp op (by sorry)
      return rewriter

/--
- Apply the given rewrite pattern to all operations in the context (possibly multiple times).
- Return the new context, and a boolean indicating whether any changes were made.
- If any pattern failed, return none.
-/
private partial def RewritePattern.applyOnceInContext (pattern: RewritePattern dT) (ctx: IRContext dT) (hx : ctx.FieldsInBounds) :
    Option (Bool × {ctx : IRContext dT // ctx.FieldsInBounds}) := do
  let worklist := PatternRewriter.Worklist.createFromContext ctx
  let mut rewriter : PatternRewriter dT := { ctx, hasDoneAction := false, worklist, ctx_fib := hx }
  while !rewriter.worklist.isEmpty do
    let (opOpt, newWorklist) := rewriter.worklist.pop
    let op := opOpt.get!
    rewriter := { rewriter with worklist := newWorklist }
    rewriter ← pattern rewriter op
  pure (rewriter.hasDoneAction, ⟨rewriter.ctx, rewriter.ctx_fib⟩)

def RewritePattern.applyInContext (pattern: RewritePattern dT) (ctx: IRContext dT) (hx : ctx.FieldsInBounds) : Option (IRContext dT) := do
  let mut hasDoneAction := true
  let mut ctx : { ctx : IRContext dT // ctx.FieldsInBounds } := ⟨ctx, hx⟩
  while hasDoneAction do
    let (lastHasDoneAction, newCtx) ← pattern.applyOnceInContext ctx.val (by grind)
    ctx := newCtx
    hasDoneAction := lastHasDoneAction
  pure ctx.val
