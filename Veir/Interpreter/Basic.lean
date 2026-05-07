import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.ForLean
import Veir.IR.WellFormed
import Veir.PatternRewriter.Basic
import Veir.Data.LLVM.Int.Basic
import Veir.Data.RISCV.Reg.Basic
import Veir.Data.Casting
import Veir.Properties
import Veir.GlobalOpInfo

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
  variables : Std.ExtHashMap ValuePtr RuntimeValue

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

@[ext]
theorem InterpreterState.ext {s₁ s₂ : InterpreterState} :
    (∀ var, s₁.getVar? var = s₂.getVar? var) →
    s₁ = s₂ := by
  rcases s₁; rcases s₂
  simp only [getVar?, mk.injEq]
  grind

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
  Set the values of block arguments.
-/
def InterpreterState.setArgumentValues (state : InterpreterState) (ctx : IRContext OpInfo)
    (block : BlockPtr) (values : Array RuntimeValue) : InterpreterState :=
  let rec loop (state : InterpreterState) (i : Nat) :=
    match i with
    | 0 => state
    | i + 1 =>
      let arg := block.getArgument i
      let value := values[i]!
      let newState := state.setVar arg value
      loop newState i
  loop state (block.getNumArguments! ctx)

/--
  Create an interpreter state with no variables defined.
-/
def InterpreterState.empty : InterpreterState :=
  { variables := Std.ExtHashMap.emptyWithCapacity 8 }

/--
  How the control flow should proceed after interpreting a terminator.
  - `return` indicates that the current block should return with the given values.
  - `branch` indicates that the interpreter should jump to another block
-/
inductive ControlFlowAction where
  | return (vals : Array RuntimeValue)
  | branch (vals : Array RuntimeValue) (dest : BlockPtr)

def Arith.interpretOp' (opType : Veir.Arith) (properties : HasDialectOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    : Option ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .constant => do
    let resType ← resultTypes[0]?
    let .integerType bw := resType.val
      | none
    return (#[.int bw.bitwidth
      (.val (BitVec.ofInt bw.bitwidth properties.value.value))], none)
  | .addi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.add lhs rhs properties.nsw properties.nuw)], none)
  | .subi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sub lhs rhs properties.nsw properties.nuw)], none)
  | .muli => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.mul lhs rhs properties.nsw properties.nuw)], none)
  | .divui => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.udiv lhs rhs properties.exact)], none)
  | .divsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sdiv lhs rhs properties.exact)], none)
  | .remui => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.urem lhs rhs)], none)
  | .remsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.srem lhs rhs)], none)
  | .shli => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.shl lhs rhs properties.nsw properties.nuw)], none)
  | .shrsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.ashr lhs rhs properties.exact)], none)
  | .shrui => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.lshr lhs rhs properties.exact)], none)
  | .andi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.and lhs rhs)], none)
  | .ori => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.or lhs rhs properties.disjoint)], none)
  | .xori => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.xor lhs rhs)], none)
  | .trunci => do
    let [.int w val] := operands.toList | none
    let resType ← resultTypes[0]?
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth >= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.trunc val resBw.bitwidth properties.nsw properties.nuw (by omega))], none)
  | .extui => do
    let [.int w val] := operands.toList | none
    let resType ← resultTypes[0]?
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.zext val resBw.bitwidth properties.nneg (by omega))], none)
  | .extsi => do
    let [.int w val] := operands.toList | none
    let resType ← resultTypes[0]?
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.sext val resBw.bitwidth (by omega))], none)
  | .select => do
    let [.int 1 cond, .int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simpa using h)
    return (#[.int bw (LLVM.Int.select cond lhs rhs)], none)
  | _ => none

def Llvm.interpretOp' (opType : Veir.Llvm) (properties : HasDialectOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    : Option ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .constant => do
    let resType ← resultTypes[0]?
    let .integerType bw := resType.val
      | none
    return (#[.int bw.bitwidth (LLVM.Int.constant bw.bitwidth properties.value.value)], none)
  | .add => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.add lhs rhs properties.nsw properties.nuw)], none)
  | .sub => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sub lhs rhs properties.nsw properties.nuw)], none)
  | .mul => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.mul lhs rhs properties.nsw properties.nuw)], none)
  | .sdiv => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sdiv lhs rhs properties.exact)], none)
  | .udiv => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.udiv lhs rhs properties.exact)], none)
  | .srem => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.srem lhs rhs)], none)
  | .urem => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.urem lhs rhs)], none)
  | .shl => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.shl lhs rhs properties.nsw properties.nuw)], none)
  | .lshr => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.lshr lhs rhs properties.exact)], none)
  | .ashr => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.ashr lhs rhs properties.exact)], none)
  | .and => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.and lhs rhs)], none)
  | .or => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.or lhs rhs properties.disjoint)], none)
  | .xor => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.xor lhs rhs)], none)
  | .trunc => do
    let [.int w val] := operands.toList | none
    let resType ← resultTypes[0]?
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth >= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.trunc val resBw.bitwidth properties.nsw properties.nuw (by omega))], none)
  | .zext => do
    let [.int w val] := operands.toList | none
    let resType ← resultTypes[0]?
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.zext val resBw.bitwidth properties.nneg (by omega))], none)
  | .sext => do
    let [.int w val] := operands.toList | none
    let resType ← resultTypes[0]?
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.sext val resBw.bitwidth (by omega))], none)
  | .icmp => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simpa using h)
    let some p := LLVM.IntPred.fromNat properties.value.value.toNat | none
    return (#[.int 1 (LLVM.Int.icmp lhs rhs p)], none)
  | .return => do
    return (#[], some (.return operands))
  | .br => do
    let [dest] := blockOperands.toList | none
    return (#[], some (.branch operands dest))
  | .cond_br => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.int 1 (.val cond)) := operands[0]? | none
    let some trueSize := properties.operandSegmentSizes.values[1]? | none
    let trueSize := trueSize.toNat
    if cond = 1#1 then
      return (#[], some (.branch (operands.extract 1 (trueSize + 1)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 1) operands.size) destFalse))
  | _ => none

def Riscv.interpretOp' (opType : Veir.Riscv) (properties : HasDialectOpInfo.propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    : Option ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .li => do
    let imm := BitVec.ofInt 64 properties.value.value
    return (#[.reg (RISCV.li imm)], none)
  | .lui => do
    let imm := BitVec.ofInt 20 properties.value.value
    return (#[.reg (RISCV.lui imm)], none)
  | .auipc => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 20 properties.value.value
    return (#[.reg (RISCV.auipc imm op)], none)
  | .addi => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.addi imm op)], none)
  | .slti => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.slti imm op)], none)
  | .sltiu => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.sltiu imm op)], none)
  | .andi => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.andi imm op)], none)
  | .ori => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.ori imm op)], none)
  | .xori => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.xori imm op)], none)
  | .addiw => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.addiw imm op)], none)
  | .slli => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.slli imm op)], none)
  | .srli => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.srli imm op)], none)
  | .srai => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.srai imm op)], none)
  | .add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.add op2 op1)], none)
  | .sub => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sub op2 op1)], none)
  | .sll => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sll op2 op1)], none)
  | .slt => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.slt op2 op1)], none)
  | .sltu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sltu op2 op1)], none)
  | .xor => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.xor op2 op1)], none)
  | .srl => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.srl op2 op1)], none)
  | .sra => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sra op2 op1)], none)
  | .or => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.or op2 op1)], none)
  | .and => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.and op2 op1)], none)
  | .slliw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.slliw imm op1)], none)
  | .srliw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.srliw imm op1)], none)
  | .sraiw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.sraiw imm op1)], none)
  | .addw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.addw op2 op1)], none)
  | .subw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.subw op2 op1)], none)
  | .sllw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sllw op2 op1)], none)
  | .srlw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.srlw op2 op1)], none)
  | .sraw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sraw op2 op1)], none)
  | .rem => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.rem op2 op1)], none)
  | .remu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remu op2 op1)], none)
  | .remw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remw op2 op1)], none)
  | .remuw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remuw op2 op1)], none)
  | .mul => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mul op2 op1)], none)
  | .mulh => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulh op2 op1)], none)
  | .mulhu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulhu op2 op1)], none)
  | .mulhsu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulhsu op2 op1)], none)
  | .mulw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulw op2 op1)], none)
  | .div => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.div op2 op1)], none)
  | .divw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divw op2 op1)], none)
  | .divu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divu op2 op1)], none)
  | .divuw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divuw op2 op1)], none)
  | .adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.adduw op2 op1)], none)
  | .sh1adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh1adduw op2 op1)], none)
  | .sh2adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh2adduw op2 op1)], none)
  | .sh3adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh3adduw op2 op1)], none)
  | .sh1add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh1add op2 op1)], none)
  | .sh2add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh2add op2 op1)], none)
  | .sh3add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh3add op2 op1)], none)
  | .slliuw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.slliuw imm op1)], none)
  | .andn => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.andn op2 op1)], none)
  | .orn => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.orn op2 op1)], none)
  | .xnor => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.xnor op2 op1)], none)
  | .max => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.max op2 op1)], none)
  | .maxu => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.maxu op2 op1)], none)
  | .min => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.min op2 op1)], none)
  | .minu => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.minu op2 op1)], none)
  | .rol => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rol op2 op1)], none)
  | .ror => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.ror op2 op1)], none)
  | .rolw => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rolw op2 op1)], none)
  | .rorw => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rorw op2 op1)], none)
  | .sextb => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sextb op)], none)
  | .sexth => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sexth op)], none)
  | .zexth => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zexth op)], none)
  | .clz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.clz op)], none)
  | .clzw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.clzw op)], none)
  | .ctz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.ctz op)], none)
  | .ctzw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.ctzw op)], none)
  | .cpop => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.cpop op)], none)
  | .cpopw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.cpopw op)], none)
  | .roriw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.roriw imm op1)], none)
  | .rori => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.rori imm op1)], none)
  | .bclr => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bclr op2 op1)], none)
  | .bext => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bext op2 op1)], none)
  | .binv => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.binv op2 op1)], none)
  | .bset => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bset op2 op1)], none)
  | .bclri => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bclri imm op)], none)
  | .bexti => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bexti imm op)], none)
  | .binvi => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.binvi imm op)], none)
  | .bseti => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bseti imm op)], none)
  | .pack => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.pack op2 op1)], none)
  | .packh => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.packh op2 op1)], none)
  | .packw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.packw op2 op1)], none)
  | .mv => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.mv op)], none)
  | .not => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.not op)], none)
  | .neg => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.neg op)], none)
  | .negw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.negw op)], none)
  | .sextw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sextw op)], none)
  | .zextb => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zextb op)], none)
  | .zextw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zextw op)], none)
  | .seqz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.seqz op)], none)
  | .snez => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.snez op)], none)
  | .sltz=> do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sltz op)], none)
  | .sgtz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sgtz op)], none)
  | _ => none

def Cf.interpretOp' (opType : Veir.Cf) (properties : HasDialectOpInfo.propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    : Option ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .br => do
    let [dest] := blockOperands.toList | none
    return (#[], some (.branch operands dest))
  | .cond_br => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.int 1 (.val cond)) := operands[0]? | none
    let some trueSize := properties.operandSegmentSizes.values[1]? | none
    let trueSize := trueSize.toNat
    if cond = 1#1 then
      return (#[], some (.branch (operands.extract 1 (trueSize + 1)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 1) operands.size) destFalse))

/--
  Interpret a single operation given its opcode, type-dependent properties,
  result types, and the runtime values of its operands.
  Return the result runtime values and an optional control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  returns `none`.
-/
def interpretOp' (opType : OpCode) (properties : HasOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    : Option ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .arith arithOp => do
    Arith.interpretOp' arithOp properties resultTypes operands blockOperands
  | .llvm llvmOp => do
    Llvm.interpretOp' llvmOp properties resultTypes operands blockOperands
  | .riscv riscvOp => do
    Riscv.interpretOp' riscvOp properties resultTypes operands blockOperands
  | .cf cfOp => do
    Cf.interpretOp' cfOp properties resultTypes operands blockOperands
  | .func .return => do
    return (#[], some (.return operands))
  | .builtin .unrealized_conversion_cast => do
    let resType ← resultTypes[0]?
    match resType.val, operands.toList with
    | .registerType _, [.int _bw val] =>
      return (#[.reg (LLVM.Int.toReg val )], none)
    | .integerType _bw, [.reg val] =>
      let .integerType resBw := resType.val | none
      return (#[.int resBw.bitwidth (RISCV.Reg.toInt val resBw.bitwidth)], none)
    | _ , _ => none
  | _ => none

/--
  Interpret a single operation given the current interpreter state.
  Return an updated interpreter state and a control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  return `none`.
-/
def interpretOp (ctx : IRContext OpCode) (op : OperationPtr) (state : InterpreterState)
    : Option (InterpreterState × Option ControlFlowAction) := do
  let operands ← state.getOperandValues ctx op
  let opType := op.getOpType! ctx
  let (resultValues, action) ← interpretOp' opType (op.getProperties! ctx opType) (op.getResultTypes! ctx) operands (op.getSuccessors! ctx)
  let newState := state.setResultValues ctx op resultValues
  return (newState, action)

/--
  Interpret a list of operations, starting from the given operation pointer.
  Continue to interpret operations until a terminator is encountered,
  or the end of the block is reached.
  Return a ControlFlowAction indicating how to continue the interpretation.
  Return `none` if any errors occur during interpretation.
-/
def interpretOpList (ctx : IRContext OpCode) (op : OperationPtr) (state : InterpreterState)
    (opInBounds : op.InBounds ctx := by grind) (wf : ctx.WellFormed := by grind)
    : Option ControlFlowAction := do
  let (state, action) ← interpretOp ctx op state
  match action with
  | none =>
    rlet next ← (op.get ctx).next
    interpretOpList ctx next state
  | some action =>
    return action
termination_by op.idxInParentFromTail ctx
decreasing_by grind

/--
  Interpret a block of operations, starting from the first operation in the block.
  Return a ControlFlowAction indicating how to continue the interpretation.
  Return `none` if any errors occur during interpretation.
-/
def interpretBlock (ctx : IRContext OpCode) (blockPtr : BlockPtr) (state : InterpreterState) (blockInBounds : blockPtr.InBounds ctx := by grind) (wf : ctx.WellFormed := by grind) : Option ControlFlowAction := do
  let block := blockPtr.get ctx (by grind)
  rlet firstOp ← (blockPtr.get ctx).firstOp
  interpretOpList ctx firstOp state

/--
  Interpret a CFG, starting from the given block.
  Return the values eventually returned, if any.
  Return `none` if any errors occur during interpretation.
-/
def interpretBlockCFG (ctx : IRContext OpCode) (blockPtr : BlockPtr) (state : InterpreterState) (blockInBounds : blockPtr.InBounds ctx := by grind) (wf : ctx.WellFormed := by grind) : Option (Array RuntimeValue) := do
  match interpretBlock ctx blockPtr state blockInBounds wf with
  | some (.return res) => some res
  | some (.branch res succ) =>
    if h : succ.InBounds ctx then
      let state := state.setArgumentValues ctx succ res
      interpretBlockCFG ctx succ state h wf else none
  | none => none
partial_fixpoint

/--
  Interpret a region, starting from its first block.
  Return the values eventually returned, or `none` if any errors occur during interpretation.
-/
def interpretRegion (ctx : IRContext OpCode) (region : RegionPtr) (state : InterpreterState) (regionIn : region.InBounds ctx := by grind) (wf : ctx.WellFormed := by grind) : Option (Array RuntimeValue) := do
  rlet block ← (region.get ctx).firstBlock
  interpretBlockCFG ctx block state

/--
  Interpret a builtin.module operation.
  This is done by interpreting the unique region of the operation.
  Return the values eventually returned, or `none` if any errors occur during interpretation.
-/
def interpretModule (ctx : IRContext OpCode) (op : OperationPtr)
    (opIn : op.InBounds ctx := by grind) (wf : ctx.WellFormed := by grind)
    : Option (Array RuntimeValue) := do
  if h: op.getNumRegions ctx ≠ 1 then
    none
  else
    interpretRegion ctx (op.getRegion ctx 0) InterpreterState.empty

end Veir
