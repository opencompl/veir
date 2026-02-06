import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.ForLean
import Veir.IR.WellFormed
import Veir.PatternRewriter.Basic

/-!
  # Veir Interpreter

  This file contains a simple interpreter for a subset of the Veir IR.

  The interpreter maintains a mapping from IR values (`ValuePtr`) to runtime
  values (`UInt64`). Each supported operation reads its operands from this
  mapping and writes its results back into it.

  The interpreter walks the linked list of operations in a block. It continues
  until a `func.return` is encountered, at which point the returned values are
  collected and propagated to the caller.
-/

namespace Veir

/--
  The representation of a vaule in the interpreter.
-/
abbrev RuntimeValue := UInt64

/--
  The state of the interpreter at a given point in time.
  It includes a mapping from IR values to their runtime values.
-/
structure InterpreterState where
  variables : Std.HashMap ValuePtr RuntimeValue

/--
  Set the value of a variable.
-/
def InterpreterState.setVar (state : InterpreterState) (var : ValuePtr) (val : RuntimeValue)
    : InterpreterState :=
  { state with variables := state.variables.insert var val }

/--
  Get the value of a variable, if the variable exists.
-/
def InterpreterState.getVar? (state : InterpreterState) (var : ValuePtr)
    : Option RuntimeValue :=
  state.variables[var]?

/--
  Create an interpreter state with no variables defined.
-/
def InterpreterState.empty : InterpreterState :=
  { variables := Std.HashMap.emptyWithCapacity 8 }

/--
  How the control flow should proceed after interpreting an operation.
  - `return` indicates that the current block should return with the given values.
  - `continue` indicates that the interpreter should continue to the next operation in the block.
-/
inductive ControlFlowAction where
  | return (vals : Array RuntimeValue)
  | continue

/--
  Interprets a single operation given the runtime values of its operands.
  Returns the result runtime values and a control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  returns `none`.
-/
def interpretOp' (ctx : IRContext) (opPtr : OperationPtr) (operands: Array RuntimeValue)
    (opPtrInBounds : opPtr.InBounds ctx := by grind)
    : Option ((Array RuntimeValue) × ControlFlowAction) :=
  let op := opPtr.get ctx (by grind)
  match op.opType with
  | .arith_constant => do
    let valueAttrPtr := op.properties
    return (#[op.properties], .continue)
  | .arith_addi => do
    let #[lhs, rhs] := operands | none
    return (#[lhs + rhs], .continue)
  | .func_return => do
    return (#[], .return operands)
  | _ => none

/--
  Interprets a single operation given the current interpreter state.
  Returns an updated interpreter state and a control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  returns `none`.
-/
def interpretOp (ctx : IRContext) (opPtr : OperationPtr) (state : InterpreterState)
    (opPtrInBounds : opPtr.InBounds ctx := by grind)
    : Option (InterpreterState × ControlFlowAction) := do
  let operands ← (0...opPtr.getNumOperands ctx).toArray.mapM (fun idx =>
    let operand := opPtr.getOperand! ctx idx
    state.getVar? operand)
  let (resultValues, action) ← interpretOp' ctx opPtr operands
  let newState := state
  let newState := (0...opPtr.getNumResults ctx).toArray.foldl (fun s idx =>
    let result := opPtr.getResult idx
    let value := resultValues[idx]!
    s.setVar result value) newState
  return (newState, action)

/--
  Interprets a list of operations, starting from the given operation pointer.
  Returns an array of values corresponding to the values returned by the block, if any.
  Continues to interpret operations until a `return` control flow action is encountered,
  or the end of the block is reached.
  Returns `none` if any errors occur during interpretation.
-/
def interpretOpList (ctx : IRContext) (op : OperationPtr) (state : InterpreterState)
    (opInBounds : op.InBounds ctx := by grind) (wf : ctx.WellFormed := by grind)
    : Option (Array RuntimeValue) := do
  let (state, action) ← interpretOp ctx op state
  match action with
  | .continue =>
    rlet next ← (op.get ctx).next
    interpretOpList ctx next state
  | .return results =>
    return results
partial_fixpoint

/--
  Interprets a block of operations, starting from the first operation in the block.
  Returns the values returned by the block, if any.
  Returns `none` if any errors occur during interpretation.
-/
def interpretBlock (ctx : IRContext) (blockPtr : BlockPtr) (state : InterpreterState) (blockInBounds : blockPtr.InBounds ctx := by grind) (wf : ctx.WellFormed := by grind) : Option (Array RuntimeValue) := do
  let block := blockPtr.get ctx (by grind)
  rlet firstOp ← (blockPtr.get ctx).firstOp
  interpretOpList ctx firstOp state

/--
  Interprets a bulitin.module operation.
  This is done by interpreting the first block of the first region of the operation.
  Reurns the values returned by the block.
  If any errors occur during interpretation, returns `none`.
-/
def interpretModule (ctx : IRContext) (op : OperationPtr)
    (opIn : op.InBounds ctx := by grind) (wf : ctx.WellFormed := by grind)
    : Option (Array RuntimeValue) := do
  if h: op.getNumRegions ctx ≠ 1 then
    none
  else
    rlet block ← ((op.getRegion ctx 0).get ctx).firstBlock
    interpretBlock ctx block InterpreterState.empty

end Veir
