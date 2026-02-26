import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.ForLean
import Veir.IR.WellFormed
import Veir.PatternRewriter.Basic
import Veir.Data.LLVM.Int.Basic

open Veir.Data
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
  The representation of a value in the interpreter.
-/
inductive RuntimeValue where
| int (bitwidth : Nat) (value : LLVM.Int bitwidth)
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
def interpretOp' (ctx : IRContext OpCode) (opPtr : OperationPtr) (operands: Array RuntimeValue)
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
    return (#[.int bw (LLVM.Int.add lhs rhs)], .continue)
  | .llvm_constant => do
    let value := opPtr.getProperties! ctx .llvm_constant
    let res ← op.results[0]?
    let .integerType bw := res.type.val
      | none
    return (#[.int bw.bitwidth
      (.val (BitVec.ofNat bw.bitwidth value.value.value.toNat))], .continue)
  | .llvm_add => do
    let #[.int bw lhs, .int bw' rhs] := operands | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.add lhs rhs)], .continue)
  | .llvm_mul => do
    let #[.int bw lhs, .int bw' rhs] := operands | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.mul lhs rhs)], .continue)
  | .func_return => do
    return (#[], .return operands)
  /- the bitblastable semantics of RISC-V assembly instructions are proven
    equivalent to the official Sail model
    https://github.com/opencompl/riscv-lean/blob/main/RISCV/Instructions.lean -/
  | .riscv_li => do
    let value := opPtr.getProperties! ctx .riscv_li
    let res ← op.results[0]?
    let bw : IntegerType := {bitwidth := 64}
    let .integerType bw := res.type.val
      | none
    return (#[.int 64
      (.val (BitVec.ofNat 64 value.value.value.toNat))], .continue)
  | .riscv_lui => do
    let value := opPtr.getProperties! ctx .riscv_li

    let #[.int bw lhs] := operands | none
    let res ← op.results[0]?
    let bw' : IntegerType := {bitwidth := 64}
    let .integerType bw' := res.type.val
      | none
    let imm := BitVec.ofNat 20 value.value.value.toNat
    return (#[.int 64 (.val (BitVec.signExtend 64 (imm ++ (0x0 : BitVec 12))))], .continue)
  | .riscv_auipc => sorry
  | .riscv_addi => sorry
  | .riscv_slti => sorry
  | .riscv_sltiu => sorry
  | .riscv_andi => sorry
  | .riscv_ori => sorry
  | .riscv_xori => sorry
  | .riscv_addiw => sorry
  | .riscv_slli => sorry
  | .riscv_srli => sorry
  | .riscv_srai => sorry
  | .riscv_add => sorry
  | .riscv_sub => sorry
  | .riscv_sll => sorry
  | .riscv_slt => sorry
  | .riscv_sltu => sorry
  | .riscv_xor => sorry
  | .riscv_srl => sorry
  | .riscv_sra => sorry
  | .riscv_or => sorry
  | .riscv_and => sorry
  | .riscv_slliw => sorry
  | .riscv_srliw => sorry
  | .riscv_sraiw => sorry
  | .riscv_addw => sorry
  | .riscv_subw => sorry
  | .riscv_sllw => sorry
  | .riscv_srlw => sorry
  | .riscv_sraw => sorry
  | .riscv_rem => sorry
  | .riscv_remu => sorry
  | .riscv_remw => sorry
  | .riscv_remuw => sorry
  | .riscv_mul => sorry
  | .riscv_mulh => sorry
  | .riscv_mulhu => sorry
  | .riscv_mulhsu => sorry
  | .riscv_mulw => sorry
  | .riscv_div => sorry
  | .riscv_divw => sorry
  | .riscv_divu => sorry
  | .riscv_divuw => sorry
  | .riscv_adduw => sorry
  | .riscv_sh1adduw => sorry
  | .riscv_sh2adduw => sorry
  | .riscv_sh3adduw => sorry
  | .riscv_sh1add => sorry
  | .riscv_sh2add => sorry
  | .riscv_sh3add => sorry
  | .riscv_slliuw => sorry
  | .riscv_andn => sorry
  | .riscv_orn => sorry
  | .riscv_xnor => sorry
  | .riscv_max => sorry
  | .riscv_maxu => sorry
  | .riscv_min => sorry
  | .riscv_minu => sorry
  | .riscv_rol => sorry
  | .riscv_ror => sorry
  | .riscv_rolw => sorry
  | .riscv_rorw => sorry
  | .riscv_sextb => sorry
  | .riscv_sexth => sorry
  | .riscv_zexth => sorry
  | .riscv_clz => sorry
  | .riscv_clzw => sorry
  | .riscv_ctz => sorry
  | .riscv_ctzw => sorry
  | .riscv_roriw => sorry
  | .riscv_rori => sorry
  | .riscv_bclr => sorry
  | .riscv_bext => sorry
  | .riscv_binv => sorry
  | .riscv_bset => sorry
  | .riscv_bclri => sorry
  | .riscv_bexti => sorry
  | .riscv_binvi => sorry
  | .riscv_bseti => sorry
  | .riscv_pack => sorry
  | .riscv_packh => sorry
  | .riscv_packw => sorry
  | _ => none

/--
  Interpret a single operation given the current interpreter state.
  Return an updated interpreter state and a control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  return `none`.
-/
def interpretOp (ctx : IRContext OpCode) (opPtr : OperationPtr) (state : InterpreterState)
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
def interpretOpList (ctx : IRContext OpCode) (op : OperationPtr) (state : InterpreterState)
    (opInBounds : op.InBounds ctx := by grind) (wf : ctx.WellFormed := by grind)
    : Option (Array RuntimeValue) := do
  let (state, action) ← interpretOp ctx op state
  match action with
  | .continue =>
    rlet next ← (op.get ctx).next
    interpretOpList ctx next state
  | .return results =>
    return results
termination_by op.idxInParentFromTail ctx
decreasing_by grind

/--
  Interpret a block of operations, starting from the first operation in the block.
  Return the values returned by the block, if any.
  Return `none` if any errors occur during interpretation.
-/
def interpretBlock (ctx : IRContext OpCode) (blockPtr : BlockPtr) (state : InterpreterState) (blockInBounds : blockPtr.InBounds ctx := by grind) (wf : ctx.WellFormed := by grind) : Option (Array RuntimeValue) := do
  let block := blockPtr.get ctx (by grind)
  rlet firstOp ← (blockPtr.get ctx).firstOp
  interpretOpList ctx firstOp state

/--
  Interpret a builtin.module operation.
  This is done by interpreting the first block of the first region of the operation.
  Return the values returned by the block.
  If any errors occur during interpretation, return `none`.
-/
def interpretModule (ctx : IRContext OpCode) (op : OperationPtr)
    (opIn : op.InBounds ctx := by grind) (wf : ctx.WellFormed := by grind)
    : Option (Array RuntimeValue) := do
  if h: op.getNumRegions ctx ≠ 1 then
    none
  else
    rlet block ← ((op.getRegion ctx 0).get ctx).firstBlock
    interpretBlock ctx block InterpreterState.empty

end Veir
