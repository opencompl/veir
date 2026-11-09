module

public import Veir.Interpreter.Basic
public import Veir.Interpreter.CTree
public import Veir.Interfaces.CallInterfaces
public import Veir.Dialects.Builtin.Interpreter
public import Veir.Dialects.LLVM.Interpreter
public import Veir.Dialects.GMIR.Interpreter

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
    : CTree ((ErrorE ⊕ₑ UBE)) FreezeC (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .llvm opType =>
    Llvm.interpretOpCTree opType properties resultTypes operands blockOperands mem
  | .gmir opType =>
    GMIR.interpretOpCTree opType properties resultTypes operands blockOperands mem
  | .builtin opType =>
    Builtin.interpretOpCTree opType properties resultTypes operands blockOperands mem
  /- Other dialects rely on lifting the `Interp`-based interpreter. -/
  | opType =>
    monadLift <| Veir.interpretOp' opType properties resultTypes operands blockOperands mem

/-- Interpret a call-like operation by triggering a `CallE` effect on a pointer to its callee. -/
def interpretCall (op : OperationPtr) {ctx : WfIRContext OpCode} (callOp : CallOp ctx.raw op)
    (operands : Array RuntimeValue) (state : InterpreterState ctx)
    (inBounds : op.InBounds ctx.raw := by grind)
    : RegionTree ctx (InterpreterState ctx) (InterpreterState ctx × Option ControlFlowAction) := do
  let properties := op.getProperties! ctx.raw (op.getOpType! ctx.raw)
  let calleePtr ← match callOp.callOpInterface.getCallableForCallee? properties operands with
    | some (.symbol callee) => do
      let some name := callee.getName? >>= String.fromUTF8? | fail
      let some calleePtr := state.memory.pointerToGlobal ("@" ++ name) | fail
      pure calleePtr
    | some (.value (.addr (.val calleePtr))) => pure calleePtr
    | some (.value (.addr .poison)) => ub
    | _ => fail
  let arguments := callOp.callOpInterface.getArgOperands properties operands
  let (memory, results) ← CTree.trigger (SubE := CallE) ⟨calleePtr, arguments, state.memory⟩
  let some variables := state.variables.setResultValues? op results inBounds | fail
  return (⟨variables, memory⟩, none)

/-- Interpret an operation given an operation pointer and an interpreter state. -/
def interpretOp (op : OperationPtr) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (inBounds : op.InBounds ctx.raw := by grind)
    : RegionTree ctx (InterpreterState ctx) (InterpreterState ctx × Option ControlFlowAction) := do
  let some operands := state.variables.getOperandValues op
    | fail
  /- Calls are handled here, as dialect interpreters cannot trigger `CallE`. -/
  if let some callOp := CallOp.of? op ctx.raw then
    return ← interpretCall op callOp operands state
  let opType := op.getOpType ctx.raw inBounds
  let opCTree := (interpretOp' opType (op.getProperties ctx.raw opType)
    (op.getResultTypes ctx.raw) operands (op.getSuccessors ctx.raw) state.memory
    (op.getRegions ctx.raw))
  let opCTreeWithRegion : RegionTree _ _ _ := CTree.interp CTree.trigger opCTree
  /- Call the dialect-specific operation interpreter.
  While the user-defined interpreter calls region with a `MemoryState`, we here attach the
  `InterpreterState` as well. This prevents the user from using the `InterpreterState` directly. -/
  let (resultValues, mem, action) ← CTree.interp (fun
    | .inl ⟨region, values, memoryState, inBounds⟩ => do
      let (state, results) ← runRegion region values
        ({ variables := state.variables, memory := memoryState } : InterpreterState ctx) inBounds
      return (state.memory, results)
    | .inr e => CTree.trigger (SubE := CallE ⊕ₑ (ErrorE ⊕ₑ UBE)) e)
    opCTreeWithRegion
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
    : FunctionTree (InterpreterState ctx × Array RuntimeValue) :=
  CTree.mrec (E := RunRegionE ctx (InterpreterState ctx)) (fun ⟨region, values, state, inBounds⟩ =>
    interpretCFG region values state inBounds) ⟨region, values, state, inBounds⟩

/-- Interpret a function body with the given runtime arguments and initial memory. -/
def interpretFunction (op : OperationPtr) (values : Array RuntimeValue) (mem : MemoryState)
    {ctx : WfIRContext OpCode} (opIn : op.InBounds ctx.raw := by grind)
    : FunctionTree (MemoryState × Array RuntimeValue) := do
  let some funcOp := FunctionOp.of? op ctx.raw | fail
  if h : op.getNumRegions ctx.raw ≠ 1 then
    fail
  else
    let (state, results) ← interpretRegion funcOp.getFunctionBody
      values ⟨.empty ctx, mem⟩
    return (state.memory, results)

/-- Maps each function object to its function. -/
abbrev FunctionMap := Std.HashMap Nat OperationPtr

/-- The function in `functions` whose object starts at `callee`, if any. -/
def functionAt? (functions : FunctionMap) (memory : MemoryState)
    (callee : Data.Pointer) : Option OperationPtr := do
  let object ← memory.getObject? callee
  guard (object.base = callee.address)
  functions[callee.object]?

/--
Interpret the function calls of `tree` by running the callees in `functions`. Calling a pointer
that does not point to the start of a function's object is undefined behavior.
-/
def resolveCalls (functions : FunctionMap) {ctx : WfIRContext OpCode}
    (tree : FunctionTree α) : Tree α :=
  CTree.interp_mrec (E := CallE) (fun ⟨callee, arguments, memory⟩ => do
    let some funcPtr := functionAt? functions memory callee | ub
    if h : funcPtr.InBounds ctx.raw then
      interpretFunction (ctx := ctx) funcPtr arguments memory
    else
      fail) tree

end Veir.CTree
