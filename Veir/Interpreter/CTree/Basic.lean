module

public import CTree.Iter
public import Veir.Interpreter.CTree.Effects
import Veir.Interfaces.FunctionInterfaces
import all CTree.Iter
import all Init.Internal.Order.Basic
public import Veir.Interpreter.CTree
public import Veir.Dialects.LLVM.Interpreter

public section

open CTree
open Lean.Order

namespace Veir.CTreeInterpreter

variable {ctx : WfIRContext OpCode}

/-- Allow CTree iteration to contain recursive region interpretation. -/
@[local partial_fixpoint_monotone]
private theorem iter_mono {α I X : Type} [PartialOrder α]
    (body : α → I → Tree ctx (I ⊕ X)) (i : I) (hbody : monotone body) :
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
      | inl k =>
        exact CTree.tauG_mono _ (.inl .c1) (fun t _ => t)
          (fun _ _ h _ => h) _ _ (hf k)
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
    (blockOperands : Array BlockPtr) (mem : MemoryState)
    (regions : Array RegionPtr := #[])
    (runRegion : RegionPtr → Tree ctx (MemoryState × Array RuntimeValue) := fun _ => fail)
    : Tree ctx (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .llvm opType => do
    Llvm.interpretOpCTree opType properties resultTypes operands blockOperands mem
  | .builtin .unregistered => do
    if properties.opName == "scf.if".toUTF8 then
      let [.int 1 (.val condition)] := operands.toList
        | fail
      if regions.size != 2 then
        return ← fail
      let some region := regions[if condition.toNat == 0 then 1 else 0]?
        | fail
      let (mem, results) ← runRegion region
      return (results, mem, none)
    else if properties.opName == "scf.yield".toUTF8 then
      if !resultTypes.isEmpty || !regions.isEmpty then
        return ← fail
      return (#[], mem, some (.return operands))
    else
      fail
  | .func .return => return (#[], mem, some (.return operands))
  | other => monadLift (Veir.interpretOp' other properties resultTypes operands blockOperands mem)

mutual

/-- Read inputs and write outputs through SSA effects. No variable store is
captured by this tree or by its continuations. Memory retains the existing LLVM
semantics; nested scopes preserve captured variables and propagate memory. -/
def interpretOp (op : OperationPtr) (mem : MemoryState)
    (_inBounds : op.InBounds ctx.raw := by grind)
    : Tree ctx (MemoryState × Option ControlFlowAction) := do
  let operands ← CTree.trigger (SubE := SSAE ctx) (.readOperands op)
  let opType := op.getOpType! ctx.raw
  let (resultValues, mem, action) ← interpretOp' opType (op.getProperties! ctx.raw opType)
    (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) mem
    (op.getRegions! ctx.raw) (fun region => do
      if h : region.InBounds ctx.raw then
        CTree.trigger (SubE := SSAE ctx) (.enterScope true)
        let result ← interpretRegion region #[] mem h
        CTree.trigger (SubE := SSAE ctx) .leaveScope
        return result
      else fail)
  -- No assignment is needed for a correctly result-free operation. Keep the
  -- handler's arity/type check for every other combination, including errors.
  if !resultValues.isEmpty || op.getNumResults! ctx.raw != 0 then
    CTree.trigger (SubE := SSAE ctx) (.writeResults op resultValues)
  return (mem, action)
partial_fixpoint monotonicity by
  unfold interpretOp'
  repeat' first | monotonicity | assumption

/-- Set block arguments via the handler and interpret until a control-flow
operation or the end of the block. The iteration state contains no SSA map. -/
def interpretBlock (blockPtr : BlockPtr) (values : Array RuntimeValue)
    (mem : MemoryState) (blockInBounds : blockPtr.InBounds ctx.raw := by grind)
    : Tree ctx (MemoryState × Option ControlFlowAction) := do
  CTree.trigger (SubE := SSAE ctx) (.writeArguments blockPtr values)
  CTree.iter (fun (next, mem) => do
    match next with
    | none => return .inr (mem, none)
    | some op =>
      if h : op.InBounds ctx.raw then
        let (mem, action) ← interpretOp op mem h
        match action with
        | some action => return .inr (mem, some action)
        | none => return .inl ((op.get ctx.raw).next, mem)
      else fail)
    ((blockPtr.get ctx.raw).firstOp, mem)
partial_fixpoint

/-- Interpret a nested region using the handler's current scope. -/
def interpretRegion (region : RegionPtr) (values : Array RuntimeValue)
    (mem : MemoryState) (regionIn : region.InBounds ctx.raw := by grind)
    : Tree ctx (MemoryState × Array RuntimeValue) := do
  let some firstBlock := (region.get ctx.raw regionIn).firstBlock | fail
  CTree.iter (fun (block, values, mem) => do
    if h : block.InBounds ctx.raw then
      let (mem, action) ← interpretBlock block values mem h
      match action with
      | some (.return results) => return .inr (mem, results)
      | some (.branch args dest) => return .inl (dest, args, mem)
      | none => fail
    else fail)
    (firstBlock, values, mem)
partial_fixpoint

end

/-- Interpret a function with a fresh SSA scope. The concrete runner performs
all SSA updates; continuations retain only IR, memory and individual values.
A single iteration walks the function CFG, including backedges. -/
def interpretFunction (op : OperationPtr) (values : Array RuntimeValue)
    (opIn : op.InBounds ctx.raw := by grind) (mem : MemoryState := .empty)
    : Tree ctx (MemoryState × Array RuntimeValue) := do
  if !op.isFunctionLike ctx.raw then return ← fail
  if h : op.getNumRegions ctx.raw ≠ 1 then fail
  else
    let region := FunctionOpInterface.getFunctionBody op ctx.raw
    let some block := (region.get! ctx.raw).firstBlock | fail
    if hb : block.InBounds ctx.raw then
      CTree.trigger (SubE := SSAE ctx) (.enterScope false)
      CTree.trigger (SubE := SSAE ctx) (.writeArguments block values)
      CTree.iter (fun (next, mem) => do
        let some current := next | fail
        if hc : current.InBounds ctx.raw then
          let (mem, action) ← interpretOp current mem hc
          match action with
          | none => return .inl ((current.get ctx.raw hc).next, mem)
          | some (.return results) =>
            CTree.trigger (SubE := SSAE ctx) .leaveScope
            return .inr (mem, results)
          | some (.branch args dest) =>
            if hd : dest.InBounds ctx.raw then
              CTree.trigger (SubE := SSAE ctx) (.writeArguments dest args)
              return .inl ((dest.get ctx.raw hd).firstOp, mem)
            else fail
        else fail)
        ((block.get ctx.raw hb).firstOp, mem)
    else fail

end Veir.CTreeInterpreter
