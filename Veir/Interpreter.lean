import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.ForLean
import Veir.IR.WellFormed
import Veir.PatternRewriter.Basic
import Veir.Dialects.LLVM.Int.Basic

open Veir.Dialects.LLVM.Int
abbrev IntBv := Veir.Dialects.LLVM.Int.Int

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
inductive RuntimeValue where
| int (bitwidth : Nat) (value : IntBv bitwidth)
deriving Inhabited

instance : ToString (RuntimeValue) where
  toString
    | .int _ val => ToString.toString val

/--
  The state of the interpreter at a given point in time.
  It includes a mapping from IR values to their runtime values.
-/
structure InterpreterState where
  variables : Std.HashMap ValuePtr RuntimeValue

/--
  Set the value of a variable.
-/
def InterpreterState.setVar (state : InterpreterState) (var : ValuePtr) (val : RuntimeValue) :
    InterpreterState :=
  {state with variables := state.variables.insert var val}

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
  Interpret a single operation given the runtime values of its operands.
  Return the result runtime values and a control flow action indicating how
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
    let value := op.properties
    let res ← op.results[0]?
    let .integerType bw := res.type.val
      | none
    return (#[.int bw.bitwidth (.val (BitVec.ofNat bw.bitwidth value.toNat))], .continue)
  | .arith_addi => do
    let #[.int bw lhs, .int bw' rhs] := operands | none
    if h: bw' ≠ bw then none else
    let rhs := Dialects.LLVM.Int.cast rhs (by simp at h; exact h)
    return (#[.int bw (lhs + rhs)], .continue)
  | .func_return => do
    return (#[], .return operands)
  | _ => none

/--
  Interpret a single operation given the current interpreter state.
  Return an updated interpreter state and a control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  return `none`.
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
  Interpret a list of operations, starting from the given operation pointer.
  Return an array of values corresponding to the values returned by the block, if any.
  Continue to interpret operations until a `return` control flow action is encountered,
  or the end of the block is reached.
  Return `none` if any errors occur during interpretation.
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
  Interpret a block of operations, starting from the first operation in the block.
  Return the values returned by the block, if any.
  Return `none` if any errors occur during interpretation.
-/
def interpretBlock (ctx : IRContext) (blockPtr : BlockPtr) (state : InterpreterState) (blockInBounds : blockPtr.InBounds ctx := by grind) (wf : ctx.WellFormed := by grind) : Option (Array RuntimeValue) := do
  let block := blockPtr.get ctx (by grind)
  rlet firstOp ← (blockPtr.get ctx).firstOp
  interpretOpList ctx firstOp state

/--
  Interpret a builtin.module operation.
  This is done by interpreting the first block of the first region of the operation.
  Return the values returned by the block.
  If any errors occur during interpretation, return `none`.
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
