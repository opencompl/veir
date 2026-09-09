module

public import CTree.Iter
public import Veir.Interpreter.Basic
import Veir.Interfaces.FunctionInterfaces
import all CTree.Iter
import all Init.Internal.Order.Basic
public import Veir.Interpreter.CTree
public import Veir.Dialects.LLVM.Interpreter

public section

open CTree
open Lean.Order

namespace Veir.CTreeInterpreter

/-- No custom choices yet. -/
abbrev C (_ : Empty) : Type := Empty

abbrev Tree (α : Type) := CTree (UBE ⊕ₑ ErrorE) C α

/-- Allow CTree iteration to contain recursive region interpretation. -/
@[local partial_fixpoint_monotone]
private theorem iter_mono {α I X : Type} [PartialOrder α]
    (body : α → I → Tree (I ⊕ X)) (i : I) (hbody : monotone body) :
    monotone (fun x => CTree.iter (body x) i) := by
  intro x y hxy
  have h : CTree.iter (body x) ⊑ CTree.iter (body y) := by
    apply CTree.iter.fixpoint_induct (body x) (fun f => f ⊑ CTree.iter (body y))
    · unfold admissible
      intro c hc h
      exact csup_le hc h
    · intro f hf j
      rw [CTree.iter.eq_def]
      apply PartialOrder.rel_trans (MonoBind.bind_mono_left (hbody x y hxy j))
      apply MonoBind.bind_mono_right
      intro r
      cases r with
      | inl k => exact CTree.tau1_mono _ id (fun _ _ h => h) _ _ (hf k)
      | inr r => exact PartialOrder.rel_refl
  exact h i

/--
Interpret an opcode given its properties, result types, and runtime operands.
The toy `scf.if` and `scf.yield` use unregistered operation names because the IR
has no SCF dialect yet. Only the selected region is interpreted; its yielded
values become the `if` results, without returning from the enclosing block.
-/
def interpretOp' (opType : OpCode) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (_blockOperands : Array BlockPtr)
    (regions : Array RegionPtr := #[])
    (runRegion : RegionPtr → Tree (Array RuntimeValue) := fun _ => fail)
    : Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .llvm opType => do
    Llvm.interpretOpCTree opType properties resultTypes operands _blockOperands
  | .builtin .unregistered => do
    if properties.opName == "scf.if".toUTF8 then
      let [.int 1 (.val condition)] := operands.toList
        | fail
      if regions.size != 2 then
        return ← fail
      let some region := regions[if condition.toNat == 0 then 1 else 0]?
        | fail
      let results ← runRegion region
      return (results, none)
    else if properties.opName == "scf.yield".toUTF8 then
      if !resultTypes.isEmpty || !regions.isEmpty then
        return ← fail
      return (#[], some (.return operands))
    else
      fail
  | .func .return => return (#[], some (.return operands))
  | _ => fail

mutual

/--
Read an operation's inputs, interpret it, and assign its result values to the
variable state, checking that they have the right types. Nested regions see
the current variables; only their yielded values escape into the outer state.
-/
def interpretOp (op : OperationPtr) {ctx : WfIRContext OpCode}
    (state : VariableState ctx) (inBounds : op.InBounds ctx.raw := by grind)
    : Tree (VariableState ctx × Option ControlFlowAction) := do
  let some operands := state.getOperandValues op
    | fail
  let opType := op.getOpType! ctx.raw
  let (resultValues, action) ← interpretOp' opType (op.getProperties! ctx.raw opType)
    (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw)
    (op.getRegions! ctx.raw) (fun region => do
      if h : region.InBounds ctx.raw then
        let (_, results) ← interpretRegion region #[] state h
        return results
      else
        fail)
  let some state := state.setResultValues? op resultValues inBounds
    | fail
  return (state, action)
partial_fixpoint monotonicity by
  unfold interpretOp'
  repeat' first | monotonicity | assumption

/--
Set block arguments, then walk the linked list of operations using CTree
iteration. Thread the variable state through each operation and stop at the
first control-flow action. Reaching the end (including an empty block) returns
`none`, so blocks containing only constants need no additional operation type.
-/
def interpretBlock (blockPtr : BlockPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : VariableState ctx)
    (blockInBounds : blockPtr.InBounds ctx.raw := by grind)
    : Tree (VariableState ctx × Option ControlFlowAction) := do
  if values.size != blockPtr.getNumArguments! ctx.raw then
    return ← fail
  let some state := state.setArgumentValues? blockPtr values blockInBounds
    | fail
  CTree.iter (fun (next, state) => do
    match next with
    | none => return .inr (state, none)
    | some op =>
      if h : op.InBounds ctx.raw then
        let (state, action) ← interpretOp op state h
        match action with
        | some action => return .inr (state, some action)
        | none => return .inl ((op.get ctx.raw).next, state)
      else
        fail
    ((blockPtr.get ctx.raw).firstOp, state)
partial_fixpoint

/--
Interpret a region starting at its first block, passing `values` as its arguments.
Follow branch actions, passing their values to the destination block, until a
return action yields the final variable state and the region's result values.
CTree iteration also represents CFG loops that do not terminate. An empty
region or a block that finishes without a control-flow action is an error.
-/
def interpretRegion (region : RegionPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : VariableState ctx)
    (regionIn : region.InBounds ctx.raw := by grind)
    : Tree (VariableState ctx × Array RuntimeValue) := do
  let some firstBlock := (region.get ctx.raw regionIn).firstBlock
    | fail
  CTree.iter (fun (block, values, state) => do
    if h : block.InBounds ctx.raw then
      let (state, action) ← interpretBlock block values state h
      match action with
      | some (.return results) => return .inr (state, results)
      | some (.branch args dest) => return .inl (dest, args, state)
      | none => fail
    else
      fail
    (firstBlock, values, state)
partial_fixpoint

end

/--
Interpret a function body with the given runtime arguments. Each invocation
starts with a fresh variable state, so caller variables are not visible in the
function. Return only the function's results; this toy interpreter has no memory.
-/
def interpretFunction (op : OperationPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (opIn : op.InBounds ctx.raw := by grind)
    : Tree (Array RuntimeValue) := do
  if !op.isFunctionLike ctx.raw then
    return ← fail
  if h : op.getNumRegions ctx.raw ≠ 1 then
    fail
  else
    let (_, results) ← interpretRegion (FunctionOpInterface.getFunctionBody op ctx.raw)
      values (.empty ctx)
    return results

end Veir.CTreeInterpreter
