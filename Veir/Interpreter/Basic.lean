import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.ForLean
import Veir.IR.WellFormed
import Veir.PatternRewriter.Basic
import Veir.Data.LLVM.Int.Basic
import Veir.Data.RISCV.Reg.Basic
import Veir.Properties

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

variable {OpInfo : Type} [HasOpInfo OpInfo]

/--
  The representation of a value in the interpreter.
-/
inductive RuntimeValue where
| int (bitwidth : Nat) (value : LLVM.Int bitwidth)
| reg (value : RISCV.Reg)
deriving Inhabited

instance : ToString (RuntimeValue) where
  toString
    | .int _ val => ToString.toString val
    | .reg val => ToString.toString val

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
  Get the value of the operands of an operation.
  If any operand is not in the state, return `none`.
-/
def InterpreterState.getOperandValues (state : InterpreterState)
    (ctx : IRContext OpInfo) (op : OperationPtr) : Option (Array RuntimeValue) := do
  (op.getOperands! ctx).mapM state.getVar?

def InterpreterState.setResultValues_loop (state : InterpreterState)
    (ctx : IRContext OpInfo) (op : OperationPtr) (resultValues : Array RuntimeValue) (i : Nat) : InterpreterState :=
  match i with
  | 0 => state
  | i + 1 =>
    let result := op.getResult i
    let value := resultValues[i]!
    let newState := state.setVar result value
    InterpreterState.setResultValues_loop newState ctx op resultValues i

/--
  Set the values of the results of an operation.
-/
def InterpreterState.setResultValues (state : InterpreterState) (ctx : IRContext OpInfo)
    (op : OperationPtr) (resultValues : Array RuntimeValue) : InterpreterState :=
  InterpreterState.setResultValues_loop state ctx op resultValues (op.getNumResults! ctx)

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
  Interpret a single operation given its opcode, type-dependent properties,
  result types, and the runtime values of its operands.
  Return the result runtime values and a control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  returns `none`.
-/
def interpretOp' (opType : OpCode) (properties : HasOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    : Option ((Array RuntimeValue) × ControlFlowAction) :=
  match opType with
  | .arith_constant => do
    let resType ← resultTypes[0]?
    let .integerType bw := resType.val
      | none
    return (#[.int bw.bitwidth
      (.val (BitVec.ofInt bw.bitwidth properties.value.value))], .continue)
  | .arith_addi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.add lhs rhs properties.nsw properties.nuw)], .continue)
  | .arith_subi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sub lhs rhs properties.nsw properties.nuw)], .continue)
  | .arith_muli => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.mul lhs rhs properties.nsw properties.nuw)], .continue)
  | .arith_divui => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.udiv lhs rhs properties.exact)], .continue)
  | .arith_divsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sdiv lhs rhs properties.exact)], .continue)
  | .arith_remui => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.urem lhs rhs)], .continue)
  | .arith_remsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.srem lhs rhs)], .continue)
  | .arith_shli => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.shl lhs rhs properties.nsw properties.nuw)], .continue)
  | .arith_shrsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.ashr lhs rhs properties.exact)], .continue)
  | .arith_shrui => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.lshr lhs rhs properties.exact)], .continue)
  | .arith_andi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.and lhs rhs)], .continue)
  | .arith_ori => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.or lhs rhs properties.disjoint)], .continue)
  | .arith_xori => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.xor lhs rhs)], .continue)
  | .llvm_constant => do
    let resType ← resultTypes[0]?
    let .integerType bw := resType.val
      | none
    return (#[.int bw.bitwidth
      (.val (BitVec.ofInt bw.bitwidth properties.value.value))], .continue)
  | .llvm_add => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.add lhs rhs properties.nsw properties.nuw)], .continue)
  | .llvm_sub => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sub lhs rhs properties.nsw properties.nuw)], .continue)
  | .llvm_mul => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.mul lhs rhs properties.nsw properties.nuw)], .continue)
  | .llvm_sdiv => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sdiv lhs rhs properties.exact)], .continue)
  | .llvm_udiv => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.udiv lhs rhs properties.exact)], .continue)
  | .llvm_srem => do
    let #[.int bw lhs, .int bw' rhs] := operands | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.srem lhs rhs)], .continue)
  | .llvm_urem => do
    let #[.int bw lhs, .int bw' rhs] := operands | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.urem lhs rhs)], .continue)
  | .llvm_shl => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.shl lhs rhs properties.nsw properties.nuw)], .continue)
  | .llvm_lshr => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.lshr lhs rhs properties.exact)], .continue)
  | .llvm_ashr => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.ashr lhs rhs properties.exact)], .continue)
  | .llvm_and => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.and lhs rhs)], .continue)
  | .llvm_or => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.or lhs rhs properties.disjoint)], .continue)
  | .llvm_xor => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.xor lhs rhs)], .continue)
  | .func_return => do
    return (#[], .return operands)
  /- Bitblastable semantics of RISC-V assembly instructions. -/
  | .riscv_li => do
    let imm := BitVec.ofInt 64 properties.value.value
    return (#[.reg (RISCV.li imm)], .continue)
  | .riscv_lui => do
    let imm := BitVec.ofInt 20 properties.value.value
    return (#[.reg (RISCV.lui imm)], .continue)
  | .riscv_auipc => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 20 properties.value.value
    return (#[.reg (RISCV.auipc imm op)], .continue)
  | .riscv_addi => do
    let #[.reg op] := operands | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.addi imm op)], .continue)
  | .riscv_slti => do
    let #[.reg op] := operands | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.slti imm op)], .continue)
  | .riscv_sltiu => do
    let #[.reg op] := operands | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.sltiu imm op)], .continue)
  | .riscv_andi => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.andi imm op)], .continue)
  | .riscv_ori => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.ori imm op)], .continue)
  | .riscv_xori => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.xori imm op)], .continue)
  | .riscv_addiw => do
    let #[.reg op] := operands | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.addiw imm op)], .continue)
  | .riscv_slli => do
    let #[.reg op] := operands | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.slli imm op)], .continue)
  | .riscv_srli => do
    let #[.reg op] := operands | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.srli imm op)], .continue)
  | .riscv_srai => do
    let #[.reg op] := operands | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.srai imm op)], .continue)
  | .riscv_add => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.add op2 op1)], .continue)
  | .riscv_sub => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.sub op2 op1)], .continue)
  | .riscv_sll => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.sll op2 op1)], .continue)
  | .riscv_slt => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.slt op2 op1)], .continue)
  | .riscv_sltu => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.sltu op2 op1)], .continue)
  | .riscv_xor => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.xor op2 op1)], .continue)
  | .riscv_srl => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.srl op2 op1)], .continue)
  | .riscv_sra => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.sra op2 op1)], .continue)
  | .riscv_or => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.or op2 op1)], .continue)
  | .riscv_and => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.and op2 op1)], .continue)
  | .riscv_slliw => do
    let #[.reg op1] := operands | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.slliw imm op1)], .continue)
  | .riscv_srliw => do
    let #[.reg op1] := operands | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.srliw imm op1)], .continue)
  | .riscv_sraiw => do
    let #[.reg op1] := operands | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.sraiw imm op1)], .continue)
  | .riscv_addw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.addw op2 op1)], .continue)
  | .riscv_subw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.subw op2 op1)], .continue)
  | .riscv_sllw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.sllw op2 op1)], .continue)
  | .riscv_srlw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.srlw op2 op1)], .continue)
  | .riscv_sraw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.sraw op2 op1)], .continue)
  | .riscv_rem => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.rem op2 op1)], .continue)
  | .riscv_remu => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.remu op2 op1)], .continue)
  | .riscv_remw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.remw op2 op1)], .continue)
  | .riscv_remuw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.remuw op2 op1)], .continue)
  | .riscv_mul => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.mul op2 op1)], .continue)
  | .riscv_mulh => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.mulh op2 op1)], .continue)
  | .riscv_mulhu => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.mulhu op2 op1)], .continue)
  | .riscv_mulhsu => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.mulhsu op2 op1)], .continue)
  | .riscv_mulw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.mulw op2 op1)], .continue)
  | .riscv_div => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.div op2 op1)], .continue)
  | .riscv_divw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.divw op2 op1)], .continue)
  | .riscv_divu => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.divu op2 op1)], .continue)
  | .riscv_divuw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.divuw op2 op1)], .continue)
  | .riscv_adduw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.adduw op2 op1)], .continue)
  | .riscv_sh1adduw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.sh1adduw op2 op1)], .continue)
  | .riscv_sh2adduw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.sh2adduw op2 op1)], .continue)
  | .riscv_sh3adduw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.sh3adduw op2 op1)], .continue)
  | .riscv_sh1add => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.sh1add op2 op1)], .continue)
  | .riscv_sh2add => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.sh2add op2 op1)], .continue)
  | .riscv_sh3add => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.sh3add op2 op1)], .continue)
  | .riscv_slliuw => do
    let #[.reg op1] := operands | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.slliuw imm op1)], .continue)
  | .riscv_andn => do
    let #[.reg op1, .reg op2,] := operands | none
    return (#[.reg (RISCV.andn op2 op1)], .continue)
  | .riscv_orn => do
    let #[.reg op1, .reg op2,] := operands | none
    return (#[.reg (RISCV.orn op2 op1)], .continue)
  | .riscv_xnor => do
    let #[.reg op1, .reg op2,] := operands | none
    return (#[.reg (RISCV.xnor op2 op1)], .continue)
  | .riscv_max => do
    let #[.reg op1, .reg op2,] := operands | none
    return (#[.reg (RISCV.max op2 op1)], .continue)
  | .riscv_maxu => do
    let #[.reg op1, .reg op2,] := operands | none
    return (#[.reg (RISCV.maxu op2 op1)], .continue)
  | .riscv_min => do
    let #[.reg op1, .reg op2,] := operands | none
    return (#[.reg (RISCV.min op2 op1)], .continue)
  | .riscv_minu => do
    let #[.reg op1, .reg op2,] := operands | none
    return (#[.reg (RISCV.minu op2 op1)], .continue)
  | .riscv_rol => do
    let #[.reg op1, .reg op2,] := operands | none
    return (#[.reg (RISCV.rol op2 op1)], .continue)
  | .riscv_ror => do
    let #[.reg op1, .reg op2,] := operands | none
    return (#[.reg (RISCV.ror op2 op1)], .continue)
  | .riscv_rolw => do
    let #[.reg op1, .reg op2,] := operands | none
    return (#[.reg (RISCV.rolw op2 op1)], .continue)
  | .riscv_rorw => do
    let #[.reg op1, .reg op2,] := operands | none
    return (#[.reg (RISCV.rorw op2 op1)], .continue)
  | .riscv_sextb => do
    let #[.reg op] := operands | none
    return (#[.reg (RISCV.sextb op)], .continue)
  | .riscv_sexth => do
    let #[.reg op] := operands | none
    return (#[.reg (RISCV.sexth op)], .continue)
  | .riscv_zexth => do
    let #[.reg op] := operands | none
    return (#[.reg (RISCV.zexth op)], .continue)
  | .riscv_clz => do
    let #[.reg op] := operands | none
    return (#[.reg (RISCV.clz op)], .continue)
  | .riscv_clzw => do
    let #[.reg op] := operands | none
    return (#[.reg (RISCV.clzw op)], .continue)
  | .riscv_ctz => do
    let #[.reg op] := operands | none
    return (#[.reg (RISCV.ctz op)], .continue)
  | .riscv_ctzw => do
    let #[.reg op] := operands | none
    return (#[.reg (RISCV.ctzw op)], .continue)
  | .riscv_roriw => do
    let #[.reg op1] := operands | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.roriw imm op1)], .continue)
  | .riscv_rori => do
    let #[.reg op1] := operands | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.rori imm op1)], .continue)
  | .riscv_bclr => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.bclr op2 op1)], .continue)
  | .riscv_bext => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.bext op2 op1)], .continue)
  | .riscv_binv => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.binv op2 op1)], .continue)
  | .riscv_bset => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.bset op2 op1)], .continue)
  | .riscv_bclri => do
    let #[.reg op] := operands | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bclri imm op)], .continue)
  | .riscv_bexti => do
    let #[.reg op] := operands | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bexti imm op)], .continue)
  | .riscv_binvi => do
    let #[.reg op] := operands | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.binvi imm op)], .continue)
  | .riscv_bseti => do
    let #[.reg op] := operands | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bseti imm op)], .continue)
  | .riscv_pack => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.pack op2 op1)], .continue)
  | .riscv_packh => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.packh op2 op1)], .continue)
  | .riscv_packw => do
    let #[.reg op1, .reg op2] := operands | none
    return (#[.reg (RISCV.packw op2 op1)], .continue)
  | _ => none

/--
  Interpret a single operation given the current interpreter state.
  Return an updated interpreter state and a control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  return `none`.
-/
def interpretOp (ctx : IRContext OpCode) (op : OperationPtr) (state : InterpreterState)
    : Option (InterpreterState × ControlFlowAction) := do
  let operands ← state.getOperandValues ctx op
  let opType := op.getOpType! ctx
  let (resultValues, action) ← interpretOp' opType (op.getProperties! ctx opType) ((op.get! ctx).results.map (·.type)) operands
  let newState := state.setResultValues ctx op resultValues
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
