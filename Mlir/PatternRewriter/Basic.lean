import Mlir.Prelude
import Mlir.Core.Basic
import Mlir.Rewriter.Builder
import Mlir.ForLean
import Mlir.Rewriter.BuilderInBounds

open Std (HashMap)

namespace Mlir.PatternRewriter

section array_inv

variable [Hashable α] [DecidableEq α] [BEq α]

abbrev ArrayInv (stack : Array (Option α)) (index : HashMap α Nat) :=
  ∀ (op : α) (i : Nat), index[op]? = some i → stack[i]? = some op

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
theorem OperationPtr.inBounds_of_mem_operations_keys (ctx : IRContext) :
    (op ∈ ctx.operations.keys) → op.InBounds ctx := by
  grind [OperationPtr.InBounds]

/--
- Populate a worklist with all operations that exist in the given context, and that have
- a parent operation.
-/
def Worklist.createFromContext (ctx: IRContext) : Worklist := Id.run do
  let mut worklist := Worklist.empty
  for h : op in ctx.operations.keys do
    if (op.get ctx (by grind)).parent.isSome then
      worklist := worklist.push op
  worklist.remove ctx.topLevelOp

end PatternRewriter

@[grind]
structure PatternRewriter where
  ctx: IRContext
  hasDoneAction: Bool
  worklist: PatternRewriter.Worklist
  ctx_fib : ctx.FieldsInBounds

namespace PatternRewriter

private def addUseChainUserInWorklist (rewriter: PatternRewriter) (useChain: Option OpOperandPtr) (maxIteration : Nat)
    (huc : useChain.maybe OpOperandPtr.InBounds rewriter.ctx := by grind) : PatternRewriter :=
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
theorem addUseChainUserInWorklist_same_ctx :
    (addUseChainUserInWorklist rewriter useChain maxIteration huc).ctx = rewriter.ctx := by
  induction maxIteration generalizing rewriter useChain
  · grind [addUseChainUserInWorklist]
  · simp [addUseChainUserInWorklist]; grind

-- TODO: move this somewhere
@[local grind .]
theorem ValuePtr.inBounds_getFirstUse {value : ValuePtr} {ctx} (hv : value.InBounds ctx) (hx : ctx.FieldsInBounds) :
    (value.getFirstUse ctx hv).maybe OpOperandPtr.InBounds ctx := by
  grind [Option.maybe]

private def addUsersInWorklist (rewriter: PatternRewriter) (value: ValuePtr) (hv : value.InBounds rewriter.ctx) : PatternRewriter :=
  let useChain := value.getFirstUse rewriter.ctx (by grind)
  rewriter.addUseChainUserInWorklist useChain 1_000_000_000 (by grind [Option.maybe])

@[grind =]
theorem addUsersInWorklist_same_ctx :
    (addUsersInWorklist rewriter value hv).ctx = rewriter.ctx := by
  simp [addUsersInWorklist]

def createOp (rewriter: PatternRewriter) (opType: Nat)
    (numResults: Nat) (operands: Array ValuePtr) (numRegions: Nat) (properties: UInt64)
    (insertionPoint: Option InsertPoint)
    (hoper : ∀ oper, oper ∈ operands → oper.InBounds rewriter.ctx)
    (hins : insertionPoint.maybe InsertPoint.InBounds rewriter.ctx) : Option (PatternRewriter × OperationPtr) := do
  rlet (newCtx, op) ← Builder.createOp rewriter.ctx opType numResults operands numRegions properties insertionPoint hoper hins (by grind)
  if h : insertionPoint.isNone then
    ({ rewriter with ctx := newCtx, ctx_fib := by grind }, op)
  else
    ({ rewriter with ctx := newCtx, hasDoneAction := true , worklist := rewriter.worklist.push op, ctx_fib := by grind }, op)

def insertOp (rewriter: PatternRewriter) (op: OperationPtr) (ip : InsertPoint)
    (newOpIn: op.InBounds rewriter.ctx := by grind) (insIn : ip.InBounds rewriter.ctx) : Option PatternRewriter := do
  let newCtx ← Rewriter.insertOp? rewriter.ctx op ip (by grind) (by grind) (by grind)
  some { rewriter with
    ctx := newCtx,
    hasDoneAction := true,
    worklist := rewriter.worklist.push op,
    ctx_fib := by sorry
  }

def eraseOp (rewriter: PatternRewriter) (op: OperationPtr)
    (hop : op.InBounds rewriter.ctx) (hpar : (op.get rewriter.ctx hop).parent.isSome) : Option PatternRewriter := do
  let newCtx ← Rewriter.eraseOp rewriter.ctx op (by grind) hop hpar
  some { rewriter with
    ctx := newCtx,
    hasDoneAction := true,
    worklist := rewriter.worklist.remove op,
    ctx_fib := by sorry
  }

def replaceOp (rewriter: PatternRewriter) (oldOp newOp: OperationPtr)
    (ho : oldOp.InBounds rewriter.ctx) (hn : newOp.InBounds rewriter.ctx)
    (hpar : (oldOp.get rewriter.ctx ho).parent.isSome) : Option PatternRewriter := do
  let mut rw : {r : PatternRewriter // r.ctx = rewriter.ctx } := ⟨rewriter, by grind⟩
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

def replaceValue (rewriter: PatternRewriter) (oldVal newVal: ValuePtr)
    (oldIn: oldVal.InBounds rewriter.ctx := by grind)
    (newIn: newVal.InBounds rewriter.ctx := by grind) : Option PatternRewriter := do
  -- TODO: add users of oldVal to worklist
  let rewriter := rewriter.addUsersInWorklist oldVal (by grind)
  let ctx ← Rewriter.replaceValue? rewriter.ctx oldVal newVal (by grind) (by grind) (by grind)
  some { rewriter with
    ctx,
    ctx_fib := by sorry -- relies on well-formedness!
    hasDoneAction := true
  }

end PatternRewriter

abbrev RewritePattern := PatternRewriter → OperationPtr → Option (PatternRewriter)

/--
- Apply the given rewrite pattern to all operations in the context (possibly multiple times).
- Return the new context, and a boolean indicating whether any changes were made.
- If any pattern failed, return none.
-/
private partial def RewritePattern.applyOnceInContext (pattern: RewritePattern) (ctx: IRContext) (hx : ctx.FieldsInBounds) :
    Option (Bool × {ctx : IRContext // ctx.FieldsInBounds}) := do
  let worklist := PatternRewriter.Worklist.createFromContext ctx
  let mut rewriter : PatternRewriter := { ctx, hasDoneAction := false, worklist, ctx_fib := hx }
  while !rewriter.worklist.isEmpty do
    let (opOpt, newWorklist) := rewriter.worklist.pop
    let op := opOpt.get!
    rewriter := { rewriter with worklist := newWorklist }
    rewriter ← pattern rewriter op
  pure (rewriter.hasDoneAction, ⟨rewriter.ctx, rewriter.ctx_fib⟩)

def RewritePattern.applyInContext (pattern: RewritePattern) (ctx: IRContext) (hx : ctx.FieldsInBounds) : Option IRContext := do
  let mut hasDoneAction := true
  let mut ctx : { ctx : IRContext // ctx.FieldsInBounds } := ⟨ctx, hx⟩
  while hasDoneAction do
    let (lastHasDoneAction, newCtx) ← pattern.applyOnceInContext ctx.val (by grind)
    ctx := newCtx
    hasDoneAction := lastHasDoneAction
  pure ctx.val
