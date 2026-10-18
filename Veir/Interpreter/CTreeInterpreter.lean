module

public import Veir.Interpreter.Basic
public import Veir.Interpreter.CTree
public import Veir.Dialects.LLVM.Interpreter

public section

open CTree

namespace Veir.CTree

set_option linter.unusedVariables false in
/--
Interpret an opcode given its properties, result types, and runtime operands.
Regions may be called using the `runRegion` function, which triggers a `RunRegionE` effect.

This calls the dialect-specific interpreters, which can be either CTree-based or Interp-based.
-/
def interpretOp' (opType : OpCode) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (blockOperands : Array BlockPtr) (mem : MemoryState)
    (regions : Array RegionPtr := #[])
    : RegionTree ctx MemoryState (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  match opType with
  /- The LLVM dialect has a CTree-based interpreter. -/
  | .llvm opType =>
    CTree.interp (fun e => CTree.trigger (SubE := ErrorE ⊕ₑ UBE) e)
      (Llvm.interpretOpCTree opType properties resultTypes operands blockOperands mem)
  /- Other dialects rely on lifting the `Interp`-based interpreter. -/
  | opType =>
    monadLift <| Veir.interpretOp' opType properties resultTypes operands blockOperands mem

/-- Interpret an operation given an operation pointer and an interpreter state. -/
def interpretOp (op : OperationPtr) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (inBounds : op.InBounds ctx.raw := by grind)
    : RegionTree ctx (InterpreterState ctx) (InterpreterState ctx × Option ControlFlowAction) := do
  let some operands := state.variables.getOperandValues op
    | fail
  let opType := op.getOpType ctx.raw inBounds
  let opCTree := (interpretOp' opType (op.getProperties ctx.raw opType)
    (op.getResultTypes ctx.raw) operands (op.getSuccessors ctx.raw) state.memory
    (op.getRegions ctx.raw))
  /- Call the dialect-specific operation interpreter.
  While the user-defined interpreter calls region with a `MemoryState`, we here attach the
  `InterpreterState` as well. This prevents the user from using the `InterpreterState` directly. -/
  let (resultValues, mem, action) ← CTree.interp (fun
    | .inl ⟨region, values, memoryState, inBounds⟩ => do
      let (state, results) ← runRegion region values
        ({ variables := state.variables, memory := memoryState } : InterpreterState ctx) inBounds
      return (state.memory, results)
    | .inr e => CTree.trigger (SubE := ErrorE ⊕ₑ UBE) e)
    opCTree
  let some variables := state.variables.setResultValues? op resultValues inBounds
    | fail
  return (⟨variables, mem⟩, action)

/--
A location where interpretation occurs during `interpretCFG`.
It is either a block in bounds with its argument values, or an operation in bounds.
-/
abbrev interpretCFG.StateLocation (ctx : WfIRContext OpCode) :=
  ({bb : BlockPtr // bb.InBounds ctx.raw} × Array RuntimeValue) ⊕ {op : OperationPtr // op.InBounds ctx.raw}

/--
Interpret one block entry or operation in the region's CFG, returning a tree of possible outcomes
and next locations to interpret.
-/
def interpretCFG.iter {ctx : WfIRContext OpCode} (location : interpretCFG.StateLocation ctx)
    (state : InterpreterState ctx)
    : RegionTree ctx (InterpreterState ctx)
        ((interpretCFG.StateLocation ctx × InterpreterState ctx) ⊕
          (InterpreterState ctx × Array RuntimeValue)) := do
  match location with
  | .inl (⟨block, blockInBounds⟩, values) =>
    if values.size != block.getNumArguments ctx.raw then
      return ← fail
    let some variables := state.variables.setArgumentValues? block values | fail
    rlet some firstOp := block.getFirstOp ctx.raw | fail
    return .inl (.inr ⟨firstOp, by grind⟩, ⟨variables, state.memory⟩)
  | .inr ⟨op, opInBounds⟩ =>
    let (state, action) ← interpretOp op state opInBounds
    match action with
    | some (.return results) => return .inr (state, results)
    | some (.branch args dest) =>
      if h : dest.InBounds ctx.raw then
        return .inl (.inl (⟨dest, h⟩, args), state)
      else
        fail
    | none =>
      rlet some nextOp := op.getNextOp ctx.raw | fail
      return .inl (.inr ⟨nextOp, by grind⟩, state)

/-- Interpret a region's CFG starting at its entry block, leaving nested region calls as effects. -/
def interpretCFG (region : RegionPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (inBounds : region.InBounds ctx.raw := by grind)
    : RegionTree ctx (InterpreterState ctx) (InterpreterState ctx × Array RuntimeValue) := do
  rlet some firstBlock := region.getFirstBlock ctx.raw | fail
  /- Iterate (possibly infinitely) over the region's blocks and operations. -/
  CTree.iter (fun (next, state) => interpretCFG.iter next state)
    (.inl (⟨firstBlock, by grind⟩, values), state)

/-- Interpret a region starting at its entry block with the given values. -/
def interpretRegion (region : RegionPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (inBounds : region.InBounds ctx.raw := by grind)
    : Tree (InterpreterState ctx × Array RuntimeValue) :=
  CTree.mrec (E := RunRegionE ctx (InterpreterState ctx)) (fun ⟨region, values, state, inBounds⟩ =>
    interpretCFG region values state inBounds) ⟨region, values, state, inBounds⟩

/-- Interpret a function body with the given runtime arguments. -/
def interpretFunction (op : OperationPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (opIn : op.InBounds ctx.raw := by grind)
    : Tree (Array RuntimeValue) := do
  let some funcOp := FunctionOp.of? op ctx.raw | fail
  if h : op.getNumRegions ctx.raw ≠ 1 then
    fail
  else
    let (_, results) ← interpretRegion funcOp.getFunctionBody
      values (.empty ctx)
    return results

end Veir.CTree
