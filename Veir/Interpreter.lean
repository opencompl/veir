import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.ForLean
import Veir.IR.WellFormed
import Veir.PatternRewriter.Basic
import Veir.Dialects.LLVM.Int.Basic

open Veir.Dialects
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
| int (bitwidth : Nat) (value : LLVM.Int bitwidth)
| modInt (modulus : Int) (value : Int)
deriving Inhabited

instance : ToString (RuntimeValue) where
  toString
    | .int _ val => ToString.toString val
    | .modInt modulus value => s!"{value} (mod {modulus})"

/--
  Normalize an integer in `Z/modulusZ`.
  Returns `none` if `modulus <= 0`.
-/
def normalizeMod? (modulus value : Int) : Option Int := do
  if modulus <= 0 then
    none
  else
    let reduced := value % modulus
    if reduced < 0 then
      some (reduced + modulus)
    else
      some reduced

/--
  Convert a runtime value to an integer.
  Poison values are not supported by the current mod-arith semantics.
-/
def RuntimeValue.toInt? : RuntimeValue → Option Int
  | .int _ (.val value) => some value.toNat
  | .int _ .poison => none
  | .modInt _ value => some value

/--
  Interpret a runtime value under a target modulus.
  If `strictModulus` is true, a `modInt` value must already carry the same modulus.
-/
def RuntimeValue.toModInt? (self : RuntimeValue) (modulus : Int) (strictModulus : Bool := false) :
    Option Int := do
  match self with
  | .modInt currentModulus value =>
    if strictModulus && currentModulus ≠ modulus then
      none
    else
      normalizeMod? modulus value
  | _ =>
    normalizeMod? modulus (← self.toInt?)

/--
  Build a runtime value for an integer type.
  Negative integers are currently unsupported in this conversion.
-/
def mkIntegerRuntimeValue? (bitwidth : Nat) (value : Int) : Option RuntimeValue := do
  if value < 0 then
    none
  else
    some (.int bitwidth (.val (BitVec.ofNat bitwidth value.toNat)))

/--
  Build a runtime value for a result type from a mathematical integer value.
-/
def mkRuntimeValueForType? (resultType : TypeAttr) (value : Int) : Option RuntimeValue := do
  match resultType.val with
  | .integerType intType =>
    mkIntegerRuntimeValue? intType.bitwidth value
  | .modArithType modType =>
    let normalized ← normalizeMod? modType.modulus value
    some (.modInt modType.modulus normalized)
  | _ =>
    none

/--
  Get the type of a result by index.
-/
def Operation.resultType? (op : Operation) (index : Nat := 0) : Option TypeAttr := do
  let result ← op.results[index]?
  pure result.type

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
    let value := opPtr.getProperties! ctx .arith_constant
    let res ← op.results[0]?
    let .integerType bw := res.type.val
      | none
    return (#[.int bw.bitwidth
      (.val (BitVec.ofNat bw.bitwidth value.value.value.toNat))], .continue)
  | .arith_addi => do
    let #[.int bw lhs, .int bw' rhs] := operands | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (lhs + rhs)], .continue)
  | .mod_arith_constant => do
    let resultType ← op.resultType?
    let .modArithType modType := resultType.val
      | none
    let valueProp := opPtr.getProperties! ctx .mod_arith_constant
    let value ← normalizeMod? modType.modulus valueProp.value.value
    return (#[.modInt modType.modulus value], .continue)
  | .mod_arith_add => do
    let resultType ← op.resultType?
    let .modArithType modType := resultType.val
      | none
    let #[lhs, rhs] := operands | none
    let lhs ← lhs.toModInt? modType.modulus true
    let rhs ← rhs.toModInt? modType.modulus true
    let value ← normalizeMod? modType.modulus (lhs + rhs)
    return (#[.modInt modType.modulus value], .continue)
  | .mod_arith_sub => do
    let resultType ← op.resultType?
    let .modArithType modType := resultType.val
      | none
    let #[lhs, rhs] := operands | none
    let lhs ← lhs.toModInt? modType.modulus true
    let rhs ← rhs.toModInt? modType.modulus true
    let value ← normalizeMod? modType.modulus (lhs - rhs)
    return (#[.modInt modType.modulus value], .continue)
  | .mod_arith_mul => do
    let resultType ← op.resultType?
    let .modArithType modType := resultType.val
      | none
    let #[lhs, rhs] := operands | none
    let lhs ← lhs.toModInt? modType.modulus true
    let rhs ← rhs.toModInt? modType.modulus true
    let value ← normalizeMod? modType.modulus (lhs * rhs)
    return (#[.modInt modType.modulus value], .continue)
  | .mod_arith_mac => do
    let resultType ← op.resultType?
    let .modArithType modType := resultType.val
      | none
    let #[lhs, rhs, acc] := operands | none
    let lhs ← lhs.toModInt? modType.modulus true
    let rhs ← rhs.toModInt? modType.modulus true
    let acc ← acc.toModInt? modType.modulus true
    let value ← normalizeMod? modType.modulus (lhs * rhs + acc)
    return (#[.modInt modType.modulus value], .continue)
  | .mod_arith_reduce => do
    let resultType ← op.resultType?
    let .modArithType modType := resultType.val
      | none
    let #[value] := operands | none
    let value ← value.toModInt? modType.modulus
    return (#[.modInt modType.modulus value], .continue)
  | .mod_arith_barrett_reduce => do
    let resultType ← op.resultType?
    let .modArithType modType := resultType.val
      | none
    let #[value] := operands | none
    let value ← value.toModInt? modType.modulus
    return (#[.modInt modType.modulus value], .continue)
  | .mod_arith_encapsulate => do
    let resultType ← op.resultType?
    let .modArithType modType := resultType.val
      | none
    let #[value] := operands | none
    let value ← value.toModInt? modType.modulus
    return (#[.modInt modType.modulus value], .continue)
  | .mod_arith_mod_switch => do
    let resultType ← op.resultType?
    let .modArithType modType := resultType.val
      | none
    let #[value] := operands | none
    let value ← value.toModInt? modType.modulus
    return (#[.modInt modType.modulus value], .continue)
  | .mod_arith_subifge => do
    let resultType ← op.resultType?
    let .modArithType modType := resultType.val
      | none
    let #[lhs, rhs] := operands | none
    let lhs ← lhs.toModInt? modType.modulus true
    let rhs ← rhs.toModInt? modType.modulus true
    let value := if lhs >= rhs then lhs - rhs else lhs
    let value ← normalizeMod? modType.modulus value
    return (#[.modInt modType.modulus value], .continue)
  | .mod_arith_extract => do
    let resultType ← op.resultType?
    let #[value] := operands | none
    let value ← value.toInt?
    let resultValue ← mkRuntimeValueForType? resultType value
    return (#[resultValue], .continue)
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
