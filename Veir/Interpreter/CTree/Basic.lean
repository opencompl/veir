module

public import Veir.Interpreter.Basic
public import Veir.Interpreter.CTree
public import Veir.Dialects.LLVM.Interpreter

public section

open CTree

namespace Veir.CTreeInterpreter

/-- A CTree with the error and UB effect, and the freeze choice. -/
abbrev Tree (α : Type) := CTree (ErrorE ⊕ₑ UBE) FreezeC α

/-!
# Region Effect

This section defines the effect of running a region, which includes its arguments and the state
passed to its body.
-/

/-- A region call, including its arguments and the state visible to its body. -/
structure RunRegionEIn (σ : Type) where
  region : RegionPtr
  values : Array RuntimeValue
  state : σ

/-- A region returns its final state and its yielded values. -/
abbrev RunRegionE (σ : Type) (_ : RunRegionEIn σ) : Type :=
  σ × Array RuntimeValue

/-- Trees whose region calls have not yet been interpreted. -/
abbrev RegionTree (σ α : Type) := CTree (RunRegionE σ ⊕ₑ (ErrorE ⊕ₑ UBE)) FreezeC α

/-- Request region execution without choosing its recursive interpretation. -/
def runRegion (region : RegionPtr) (values : Array RuntimeValue) (state : σ)
    : RegionTree σ (σ × Array RuntimeValue) :=
  CTree.trigger (SubE := RunRegionE σ) ⟨region, values, state⟩

/--
Interpret an opcode given its properties, result types, and runtime operands.
This is just a prototype for, to make sure that everything works.

This is the code that is dialect-specific.
-/
def interpretOp' (opType : OpCode) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (blockOperands : Array BlockPtr) (mem : MemoryState)
    (regions : Array RegionPtr := #[])
    : RegionTree MemoryState (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .llvm opType =>
    CTree.interp (fun e => CTree.trigger (SubE := ErrorE ⊕ₑ UBE) e)
      (Llvm.interpretOpCTree opType properties resultTypes operands blockOperands mem)
  | .builtin .unregistered => do
    if properties.opName == "scf.if".toUTF8 then
      let [.int 1 (.val condition)] := operands.toList
        | fail
      if regions.size != 2 then
        return ← fail
      let some region := regions[if condition.toNat == 0 then 1 else 0]?
        | fail
      -- Run a region by triggering an effect.
      -- We pass it the current memory state. The rest of the interpreter state will be attached
      -- to the effect in callers of this function.
      let (mem, results) ← runRegion region #[] mem
      return (results, mem, none)
    else if properties.opName == "scf.yield".toUTF8 then
      if !resultTypes.isEmpty || !regions.isEmpty then
        return ← fail
      return (#[], mem, some (.return operands))
    else
      fail
  | .func .return => return (#[], mem, some (.return operands))
  | _ => fail

/--
Read an operation's inputs, interpret it, and assign its result values to the
variable state, checking that they have the right types.
-/
def interpretOp (op : OperationPtr) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (inBounds : op.InBounds ctx.raw := by grind)
    : RegionTree (InterpreterState ctx) (InterpreterState ctx × Option ControlFlowAction) := do
  let some operands := state.variables.getOperandValues op
    | fail
  let opType := op.getOpType! ctx.raw
  -- Call the dialect-specific operation interpreter.
  -- While the user-defined interpreter calls region with a `MemoryState`, we here attach the
  -- `InterpreterState` as well.
  let (resultValues, mem, action) ← CTree.interp (fun
    | .inl call => do
      let (state, results) ← runRegion call.region call.values
        ({ variables := state.variables, memory := call.state } : InterpreterState ctx)
      return (state.memory, results)
    | .inr e => CTree.trigger (SubE := ErrorE ⊕ₑ UBE) e)
    (interpretOp' opType (op.getProperties! ctx.raw opType)
      (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) state.memory
      (op.getRegions! ctx.raw))
  let some variables := state.variables.setResultValues? op resultValues inBounds
    | fail
  return (⟨variables, mem⟩, action)

/--
Interpret a region's CFG starting at its entry block, leaving nested region calls as effects.
A single CTree iteration alternates between entering a block (assigning its
arguments) and executing its operations.
-/
def interpretCFG (region : RegionPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    : RegionTree (InterpreterState ctx) (InterpreterState ctx × Array RuntimeValue) :=
  if h : region.InBounds ctx.raw then do
    let some firstBlock := (region.get ctx.raw h).firstBlock
      | fail
    CTree.iter (fun ((next, state) :
        ((BlockPtr × Array RuntimeValue) ⊕ OperationPtr) × InterpreterState ctx) => do
      match next with
      | .inl (block, values) =>
        if h : block.InBounds ctx.raw then
          if values.size != block.getNumArguments! ctx.raw then
            return ← fail
          let some variables := state.variables.setArgumentValues? block values h
            | fail
          let some firstOp := (block.get ctx.raw).firstOp
            | fail
          return .inl (.inr firstOp, ⟨variables, state.memory⟩)
        else
          fail
      | .inr op =>
        if h : op.InBounds ctx.raw then
          let (state, action) ← interpretOp op state h
          match action with
          | some (.return results) => return .inr (state, results)
          | some (.branch args dest) => return .inl (.inl (dest, args), state)
          | none =>
            let some nextOp := (op.get ctx.raw).next
              | fail
            return .inl (.inr nextOp, state)
        else
          fail)
      (.inl (firstBlock, values), state)
  else
    fail

/-- Interpret region calls recursively, removing the `RunRegionE` effect. -/
def interpretRegion (region : RegionPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (_regionIn : region.InBounds ctx.raw := by grind)
    : Tree (InterpreterState ctx × Array RuntimeValue) :=
  CTree.mrec (E := RunRegionE (InterpreterState ctx)) (fun call =>
    interpretCFG call.region call.values call.state) ⟨region, values, state⟩

/--
Interpret a function body with the given runtime arguments. Each invocation
starts with fresh variables and memory. Return the function's results after
handling all region-call effects.
-/
def interpretFunction (op : OperationPtr) (values : Array RuntimeValue)
    {ctx : WfIRContext OpCode} (opIn : op.InBounds ctx.raw := by grind)
    : Tree (Array RuntimeValue) := do
  let some funcOp := FunctionOp.of? op ctx.raw
    | fail
  if h : op.getNumRegions ctx.raw ≠ 1 then
    fail
  else
    let (_, results) ← interpretRegion funcOp.getFunctionBody
      values (.empty ctx)
    return results

end Veir.CTreeInterpreter
