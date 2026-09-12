module

public import Veir.RuntimeValue
public import Veir.Interpreter.Memory
public import Veir.Interpreter.Util
public import Veir.IR.WellFormed
public import Veir.GlobalOpInfo
public import Veir.DataLayout.RISCV64
public import Veir.Data.Felt

import Veir.Data.Comb.Basic
import Veir.Data.HW.Basic
import Veir.Data.Casting
import Veir.Interfaces.FunctionInterfaces

public section

open Veir.Data
/-!
  # Veir Interpreter

  This file contains a simple interpreter for a subset of the Veir IR.

  The interpreter walks the linked list of operations in a block. It continues
  until a `func.return` is encountered, at which point the returned values are
  collected and propagated to the caller.
-/

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : WfIRContext OpInfo}

def Arith.interpretOp' (opType : Veir.Arith) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    : Interp ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .constant => do
    let some resType := resultTypes[0]? | none
    let .integerType bw := resType.val
      | none
    return (#[.int bw.bitwidth
      (.val (BitVec.ofInt bw.bitwidth properties.value.value))], none)
  | .addi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.add lhs rhs properties.attr.nsw properties.attr.nuw)], none)
  | .subi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sub lhs rhs properties.attr.nsw properties.attr.nuw)], none)
  | .muli => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.mul lhs rhs properties.attr.nsw properties.attr.nuw)], none)
  | .divui => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    Interp.checkUnsignedDivision rhs
    return (#[.int bw (LLVM.Int.udiv lhs rhs properties.exact)], none)
  | .divsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    Interp.checkSignedDivision lhs rhs
    return (#[.int bw (LLVM.Int.sdiv lhs rhs properties.exact)], none)
  | .remui => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    Interp.checkUnsignedDivision rhs
    return (#[.int bw (LLVM.Int.urem lhs rhs)], none)
  | .remsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    Interp.checkSignedDivision lhs rhs
    return (#[.int bw (LLVM.Int.srem lhs rhs)], none)
  | .shli => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.shl lhs rhs properties.attr.nsw properties.attr.nuw)], none)
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
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth >= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.trunc val resBw.bitwidth properties.attr.nsw properties.attr.nuw (by omega))], none)
  | .extui => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.zext val resBw.bitwidth properties.nneg (by omega))], none)
  | .extsi => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.sext val resBw.bitwidth (by omega))], none)
  | .select => do
    let [.int 1 cond, .int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simpa using h)
    return (#[.int bw (LLVM.Int.select cond lhs rhs)], none)
  | .cmpi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    -- `arith.cmpi` lowers to `llvm.icmp`; the arith and LLVM predicate encodings
    -- coincide, so `properties.predicate` is used directly. Result is `i1`.
    return (#[.int 1 (LLVM.Int.icmp lhs rhs properties.predicate)], none)
  | .maxsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.smax lhs rhs)], none)
  | .minsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.smin lhs rhs)], none)
  | .maxui => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.umax lhs rhs)], none)
  | .minui => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.umin lhs rhs)], none)
  | .addui_extended => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    -- Two results: the `w`-bit sum, then the `i1` unsigned-overflow flag.
    return (#[.int bw (LLVM.Int.add lhs rhs),
              .int 1 (LLVM.Int.uaddOverflowFlag lhs rhs)], none)
  | .subui_extended => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    -- Two results: the `w`-bit difference, then the `i1` borrow flag, which is
    -- set exactly when `lhs <u rhs`.
    return (#[.int bw (LLVM.Int.sub lhs rhs),
              .int 1 (LLVM.Int.usubOverflowFlag lhs rhs)], none)
  | .mulsi_extended => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    -- Two results: the low half (same as `muli`), then the signed high half.
    return (#[.int bw (LLVM.Int.mul lhs rhs),
              .int bw (LLVM.Int.smulHigh lhs rhs)], none)
  | .mului_extended => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    -- Two results: the low half (same as `muli`), then the unsigned high half.
    return (#[.int bw (LLVM.Int.mul lhs rhs),
              .int bw (LLVM.Int.umulHigh lhs rhs)], none)
  | .ceildivui => do
    let [.int bw a, .int bw' b] := operands.toList | none
    if h: bw' ≠ bw then none else
    let b := b.cast (by simp at h; exact h)
    -- Lowering (arith ExpandOps): `a == 0 ? 0 : ((a - 1) udiv b) + 1`. The
    -- `udiv` makes a zero (or poison) divisor undefined behaviour, exactly as
    -- for `arith.divui`.
    Interp.checkUnsignedDivision b
    let zero : LLVM.Int bw := .val 0
    let one : LLVM.Int bw := .val 1
    let isZero := LLVM.Int.icmp a zero .eq
    let quotient := LLVM.Int.udiv (LLVM.Int.sub a one) b
    let plusOne := LLVM.Int.add quotient one
    return (#[.int bw (LLVM.Int.select isZero zero plusOne)], none)
  | .ceildivsi => do
    let [.int bw a, .int bw' b] := operands.toList | none
    if h: bw' ≠ bw then none else
    let b := b.cast (by simp at h; exact h)
    -- Lowering (arith ExpandOps): `z = a sdiv b;`
    -- `(a != z*b) && ((a<0) == (b<0)) ? z + 1 : z`. The intermediate `mul`/`add`
    -- carry no overflow flags (they wrap).
    let zero : LLVM.Int bw := .val 0
    let one : LLVM.Int bw := .val 1
    -- UB gating mirrors `arith.divsi` (divide-by-zero, INT_MIN / -1).
    Interp.checkSignedDivision a b
    let z := LLVM.Int.sdiv a b
    let notExact := LLVM.Int.icmp a (LLVM.Int.mul z b) .ne
    let signEqual := LLVM.Int.icmp (LLVM.Int.icmp a zero .slt) (LLVM.Int.icmp b zero .slt) .eq
    let cond := LLVM.Int.and notExact signEqual
    return (#[.int bw (LLVM.Int.select cond (LLVM.Int.add z one) z)], none)
  | .floordivsi => do
    let [.int bw a, .int bw' b] := operands.toList | none
    if h: bw' ≠ bw then none else
    let b := b.cast (by simp at h; exact h)
    -- Lowering (arith ExpandOps): `z = a sdiv b;`
    -- `(a != z*b) && ((a<0) != (b<0)) ? z - 1 : z`. The intermediate `mul`/`add`
    -- carry no overflow flags (they wrap).
    let zero : LLVM.Int bw := .val 0
    let negOne : LLVM.Int bw := .val (BitVec.allOnes bw)
    -- UB gating mirrors `arith.divsi` (divide-by-zero, INT_MIN / -1).
    Interp.checkSignedDivision a b
    let z := LLVM.Int.sdiv a b
    let notExact := LLVM.Int.icmp a (LLVM.Int.mul z b) .ne
    let signOpposite := LLVM.Int.icmp (LLVM.Int.icmp a zero .slt) (LLVM.Int.icmp b zero .slt) .ne
    let cond := LLVM.Int.and notExact signOpposite
    return (#[.int bw (LLVM.Int.select cond (LLVM.Int.add z negOne) z)], none)


/-- Matches two integer operands and casts them to the expected bitwidth `bw`. -/
private def ModArith.binaryOperands (bw : Nat) (operands : Array RuntimeValue) :
    Option (LLVM.Int bw × LLVM.Int bw) := do
  let [RuntimeValue.int bw' lhs, RuntimeValue.int bw'' rhs] := operands.toList | none
  if h : bw' = bw ∧ bw'' = bw then
    return (lhs.cast h.left, rhs.cast h.right)
  else
    none

def ModArith.interpretOp' (opType : Veir.Mod_Arith) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    : Interp ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .constant => do
    let some resType := resultTypes[0]? | none
    let .modArithType ⟨⟨mod, ⟨bw⟩⟩⟩ := resType.val | none
    let res := LLVM.Int.constant bw (properties.value.value % mod)
    return (#[RuntimeValue.int bw res], none)
  | .add => do
    let some resType := resultTypes[0]? | none
    let .modArithType ⟨⟨mod, ⟨bw⟩⟩⟩ := resType.val | none
    let some (lhs, rhs) := ModArith.binaryOperands bw operands | none
    let res :=
      match lhs.toNat?, rhs.toNat? with
      | some lhs, some rhs => LLVM.Int.constant bw ((lhs + rhs) % mod)
      | _, _ => LLVM.Int.poison
    return (#[RuntimeValue.int bw res], none)
  | .sub => do
    let some resType := resultTypes[0]? | none
    let .modArithType ⟨⟨mod, ⟨bw⟩⟩⟩ := resType.val | none
    let some (lhs, rhs) := ModArith.binaryOperands bw operands | none
    let res :=
      match lhs.toNat?, rhs.toNat? with
      | some lhs, some rhs => LLVM.Int.constant bw ((Int.ofNat lhs - rhs) % mod)
      | _, _ => LLVM.Int.poison
    return (#[RuntimeValue.int bw res], none)
  | .mul => do
    let some resType := resultTypes[0]? | none
    let .modArithType ⟨⟨mod, ⟨bw⟩⟩⟩ := resType.val | none
    let some (lhs, rhs) := ModArith.binaryOperands bw operands | none
    let res :=
      match lhs.toNat?, rhs.toNat? with
      | some lhs, some rhs => LLVM.Int.constant bw ((lhs * rhs) % mod)
      | _, _ => LLVM.Int.poison
    return (#[RuntimeValue.int bw res], none)


/-- Match two felt operands whose field type is exactly `fieldType`. -/
private def Felt.binaryOperands (fieldType : FeltType) (operands : Array RuntimeValue) :
    Option (Nat × Nat) := do
  let [RuntimeValue.felt lhsType lhs, RuntimeValue.felt rhsType rhs] := operands.toList
    | none
  guard (lhsType = fieldType ∧ rhsType = fieldType)
  return (lhs, rhs)

/-- Match one felt operand whose field type is exactly `fieldType`. -/
private def Felt.unaryOperand (fieldType : FeltType) (operands : Array RuntimeValue) :
    Option Nat := do
  let [RuntimeValue.felt operandType operand] := operands.toList | none
  guard (operandType = fieldType)
  return operand

/-- Resolve the named field carried by the unique Felt result type. -/
private def Felt.resultField? (resultTypes : Array TypeAttr) : Option (FeltType × Nat) := do
  let [⟨.feltType fieldType, _⟩] := resultTypes.toList | none
  let prime ← FeltSemantics.prime? fieldType
  return (fieldType, prime)

/-- Interpret the field-native Felt operations supported by the core interpreter. -/
def Felt.interpretOp' (opType : Veir.Felt) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (_blockOperands : Array BlockPtr) :
    Interp (Array RuntimeValue × Option ControlFlowAction) :=
  match opType with
  | .const => do
    let (fieldType, prime) ← Felt.resultField? resultTypes
    if properties.value.fieldType ≠ fieldType then none else
      let value := FeltSemantics.reduce prime properties.value.value
      return (#[.felt fieldType value], none)
  | .add => do
    let (fieldType, prime) ← Felt.resultField? resultTypes
    let (lhs, rhs) ← Felt.binaryOperands fieldType operands
    return (#[.felt fieldType (FeltSemantics.add prime lhs rhs)], none)
  | .sub => do
    let (fieldType, prime) ← Felt.resultField? resultTypes
    let (lhs, rhs) ← Felt.binaryOperands fieldType operands
    return (#[.felt fieldType (FeltSemantics.sub prime lhs rhs)], none)
  | .mul => do
    let (fieldType, prime) ← Felt.resultField? resultTypes
    let (lhs, rhs) ← Felt.binaryOperands fieldType operands
    return (#[.felt fieldType (FeltSemantics.mul prime lhs rhs)], none)
  | .neg => do
    let (fieldType, prime) ← Felt.resultField? resultTypes
    let operand ← Felt.unaryOperand fieldType operands
    return (#[.felt fieldType (FeltSemantics.neg prime operand)], none)
  | _ => none


def Llvm.interpretOp' (opType : Veir.Llvm) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState) (layout : DataLayout := .riscv64)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .mlir__constant => do
    let some resType := resultTypes[0]? | none
    match properties.value with
    | .integer intAttr =>
      let .integerType bw := resType.val
        | none
      let origbw := intAttr.type.bitwidth
      let rawbits := BitVec.ofInt origbw intAttr.value
      let extended := match origbw with
        | 1 => rawbits.zeroExtend bw.bitwidth
        | _ => rawbits.signExtend bw.bitwidth
      return (#[.int bw.bitwidth (LLVM.Int.val extended)], mem, none)
    | .float floatAttr =>
      let .floatType bw := resType.val
        | none
      return (#[.float floatAttr.type floatAttr.value], mem, none)
    | .dense denseAttr =>
      none
    | .string _ =>
      none
  | .mlir__poison => do
    let some resType := resultTypes[0]? | none
    let .integerType bw := resType.val | none
    return (#[.int bw.bitwidth (LLVM.Int.mlir_poison bw.bitwidth)], mem, none)
  | .mlir__zero => do
    let some resType := resultTypes[0]? | none
    match resType.val with
    | .integerType bw =>
      return (#[.int bw.bitwidth (LLVM.Int.val (BitVec.ofNat bw.bitwidth 0))], mem, none)
    | .llvmPointerType _ => return (#[.addr .null], mem, none)
    | _ => none
  | .add => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.add lhs rhs properties.nsw properties.nuw)], mem, none)
  | .sub => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sub lhs rhs properties.nsw properties.nuw)], mem, none)
  | .mul => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.mul lhs rhs properties.nsw properties.nuw)], mem, none)
  | .sdiv => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    Interp.checkSignedDivision lhs rhs
    return (#[.int bw (LLVM.Int.sdiv lhs rhs properties.exact)], mem, none)
  | .udiv => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    Interp.checkUnsignedDivision rhs
    return (#[.int bw (LLVM.Int.udiv lhs rhs properties.exact)], mem, none)
  | .srem => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    Interp.checkSignedDivision lhs rhs
    return (#[.int bw (LLVM.Int.srem lhs rhs)], mem, none)
  | .urem => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    Interp.checkUnsignedDivision rhs
    return (#[.int bw (LLVM.Int.urem lhs rhs)], mem, none)
  | .shl => do
    let [lhs, .int bw' rhs] := operands.toList | none
    match lhs with
    | .int bw lhs =>
      if h: bw' ≠ bw then none else
      let rhs := rhs.cast (by simp at h; exact h)
      return (#[.int bw (LLVM.Int.shl lhs rhs properties.nsw properties.nuw)], mem, none)
    | .byte bw lhs =>
      if h: bw' ≠ bw then none else
      if properties.nsw then none else
      let rhs := rhs.cast (by simp at h; exact h)
      return (#[.byte bw (LLVM.Byte.shl lhs rhs properties.nuw)], mem, none)
    | _ => none
  | .lshr => do
    let [lhs, .int bw' rhs] := operands.toList | none
    match lhs with
    | .int bw lhs =>
      if h: bw' ≠ bw then none else
      let rhs := rhs.cast (by simp at h; exact h)
      return (#[.int bw (LLVM.Int.lshr lhs rhs properties.exact)], mem, none)
    | .byte bw lhs =>
      if h: bw' ≠ bw then none else
      let rhs := rhs.cast (by simp at h; exact h)
      return (#[.byte bw (LLVM.Byte.lshr lhs rhs properties.exact)], mem, none)
    | _ => none
  | .ashr => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.ashr lhs rhs properties.exact)], mem, none)
  | .intr__fshl => do
    let [.int bw a, .int bw' b, .int bw'' c] := operands.toList | none
    if h: bw' ≠ bw then none else
    if h'': bw'' ≠ bw then none else
    let b := b.cast (by simp at h; exact h)
    let c := c.cast (by simp at h''; exact h'')
    return (#[.int bw (LLVM.Int.fshl a b c)], mem, none)
  | .intr__fshr => do
    let [.int bw a, .int bw' b, .int bw'' c] := operands.toList | none
    if h: bw' ≠ bw then none else
    if h'': bw'' ≠ bw then none else
    let b := b.cast (by simp at h; exact h)
    let c := c.cast (by simp at h''; exact h'')
    return (#[.int bw (LLVM.Int.fshr a b c)], mem, none)
  | .intr__ctlz => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (LLVM.Int.ctlz x properties.is_zero_poison)], mem, none)
  | .intr__cttz => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (LLVM.Int.cttz x properties.is_zero_poison)], mem, none)
  | .intr__ctpop => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (LLVM.Int.ctpop x)], mem, none)
  | .intr__bswap => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (LLVM.Int.bswap x)], mem, none)
  | .intr__bitreverse => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (LLVM.Int.bitreverse x)], mem, none)
  | .and => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.and lhs rhs)], mem, none)
  | .or => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.or lhs rhs properties.disjoint)], mem, none)
  | .xor => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.xor lhs rhs)], mem, none)
  | .intr__smax => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.smax lhs rhs)], mem, none)
  | .intr__smin => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.smin lhs rhs)], mem, none)
  | .intr__umax => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.umax lhs rhs)], mem, none)
  | .intr__umin => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.umin lhs rhs)], mem, none)
  | .intr__abs => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (LLVM.Int.abs x properties.is_int_min_poison)], mem, none)
  | .intr__sadd__sat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.saddSat lhs rhs)], mem, none)
  | .intr__uadd__sat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.uaddSat lhs rhs)], mem, none)
  | .intr__ssub__sat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.ssubSat lhs rhs)], mem, none)
  | .intr__usub__sat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.usubSat lhs rhs)], mem, none)
  | .intr__sshl__sat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sshlSat lhs rhs)], mem, none)
  | .intr__ushl__sat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.ushlSat lhs rhs)], mem, none)
  | .trunc => do
    let [val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    match val with
    | .int w val =>
        let .integerType resBw := resType.val | none
        if h: resBw.bitwidth >= w then none else
        return (#[.int resBw.bitwidth (LLVM.Int.trunc val resBw.bitwidth properties.nsw properties.nuw (by omega))], mem, none)
    | .byte w val =>
        let .byteType resBw := resType.val | none
        if h: resBw.bitwidth >= w then none else
        return (#[.byte resBw.bitwidth (LLVM.Byte.trunc val resBw.bitwidth)], mem, none)
    | _ => none
  | .zext => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.zext val resBw.bitwidth properties.nneg (by omega))], mem, none)
  | .sext => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h: resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (LLVM.Int.sext val resBw.bitwidth (by omega))], mem, none)
  | .icmp => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simpa using h)
    return (#[.int 1 (LLVM.Int.icmp lhs rhs properties.predicate)], mem, none)
  | .select => do
    let [.int 1 cond, .int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simpa using h)
    return (#[.int bw (LLVM.Int.select cond lhs rhs)], mem, none)
  | .return => do
    return (#[], mem, some (.return operands))
  | .unreachable =>
    Interp.ub
  | .br => do
    let [dest] := blockOperands.toList | none
    return (#[], mem, some (.branch operands dest))
  | .cond_br => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some condVal := operands[0]? | none
    let some (trueSizeInt : Int) := properties.operandSegmentSizes.values[1]? | none
    let trueSize := trueSizeInt.toNat
    match condVal with
    | .int 1 (.val cond) =>
      if cond = 1#1 then
        return (#[], mem, some (.branch (operands.extract 1 (trueSize + 1)) destTrue))
      else
        return (#[], mem, some (.branch (operands.extract (trueSize + 1) operands.size) destFalse))
    | .int 1 .poison => Interp.ub
    | _ => none
  | .switch => do
    let some destDefault := blockOperands[0]? | none
    let some value := operands[0]? | none
    let some (defaultSizeInt : Int) := properties.operandSegmentSizes.values[1]? | none
    let defaultSize := defaultSizeInt.toNat
    let caseSegments := properties.case_operand_segments.values
    let some caseValues := properties.caseValues? | none
    /- A case value per case, or the switch cannot be read. -/
    if caseValues.size ≠ caseSegments.size then none else
    match value with
    | .int bw (.val v) =>
      let mut base := 1 + defaultSize
      for i in [0:caseSegments.size] do
        let some (countInt : Int) := caseSegments[i]? | none
        let count := countInt.toNat
        if v = BitVec.ofInt bw caseValues[i]! then
          let some dest := blockOperands[i + 1]? | none
          return (#[], mem, some (.branch (operands.extract base (base + count)) dest))
        base := base + count
      return (#[], mem, some (.branch (operands.extract 1 (1 + defaultSize)) destDefault))
    | .int _ .poison => Interp.ub
    | _ => none
  | .call => do
    /- The C and C++ allocation functions are modelled by name. Each
       allocation yields a fresh object, so pointers into different
       allocations never alias. The oracle decides whether `malloc`,
       `calloc` and `realloc` fail; `operator new` never does. -/
    let some callee := properties.callee | none
    match callee.value, operands.toList with
    | "@malloc", [.int _ size] =>
      let .val size := size | Interp.ub
      let (mem, ptr) := mem.heapAlloc size.toNat
      return (#[.addr ptr], mem, none)
    | "@calloc", [.int _ count, .int _ size] =>
      let .val count := count | Interp.ub
      let .val size := size | Interp.ub
      let (mem, ptr) := mem.heapAlloc (count.toNat * size.toNat)
      if ptr.isNull then return (#[.addr ptr], mem, none)
      let mem ← mem.storeBytes ptr (Array.replicate (count.toNat * size.toNat) (.value 0 0))
      return (#[.addr ptr], mem, none)
    | "@realloc", [.addr old, .int _ size] =>
      let .val size := size | Interp.ub
      if old.isNull then
        let (mem, ptr) := mem.heapAlloc size.toNat
        return (#[.addr ptr], mem, none)
      let some obj := mem.getObject? old | Interp.ub
      if old.offset ≠ 0 ∨ obj.kind ≠ .heap ∨ !obj.alive then Interp.ub
      let (mem', ptr) := mem.heapAlloc size.toNat
      if ptr.isNull then return (#[.addr ptr], mem', none)
      let mem ← mem'.storeBytes ptr (obj.bytes.extract 0 (min obj.bytes.size size.toNat))
      let mem ← mem.free old
      return (#[.addr ptr], mem, none)
    | "@_Znwm", [.int _ size] | "@_Znam", [.int _ size] =>
      let .val size := size | Interp.ub
      let (mem, ptr) := mem.alloc size.toNat .heap
      return (#[.addr ptr], mem, none)
    | "@free", [.addr ptr] | "@_ZdlPv", [.addr ptr] | "@_ZdaPv", [.addr ptr]
    | "@_ZdlPvm", [.addr ptr, _] | "@_ZdaPvm", [.addr ptr, _] =>
      let mem ← mem.free ptr
      return (#[], mem, none)
    | _, _ => none
  | .intr__lifetime__start => do
    let [.addr ptr] := operands.toList | none
    let mem ← mem.lifetimeStart ptr
    return (#[], mem, none)
  | .intr__lifetime__end => do
    let [.addr ptr] := operands.toList | none
    let mem ← mem.lifetimeEnd ptr
    return (#[], mem, none)
  | .mlir__addressof => do
    let some object := mem.globals[properties.global_name.value]? | none
    return (#[.addr ⟨object, 0⟩], mem, none)
  | .alloca => do
    let [.int _ (.val count)] := operands.toList | none
    /- `alloca T, N` reserves `N` strides of `T`, as in LLVM. -/
    let size ← layout.getTypeAllocSize properties.elem_type.val
    let (mem, ptr) := mem.alloc (size * count.toNat) .stack properties.alignment.value.toNat.toUInt64
    return (#[.addr ptr], mem, none)
  | .load => do
    let [.addr addr] := operands.toList | none
    let [type] := resultTypes.toList | none
    let val ← mem.llvmLoad addr type
    return (#[val], mem, none)
  | .store => do
    let [val, .addr addr] := operands.toList | none
    let mem ← mem.llvmStore addr val
    return (#[], mem, none)
  | .getelementptr => do
    /- only supports exactly one dynamic index for now -/
    let [.addr ptr, .int _ idx] := operands.toList | none
    /- The index scales by the element's stride, matching the `getTypeAllocSize`
       that `isel-riscv64` uses to lower this operation. -/
    let size ← layout.getTypeAllocSize properties.elem_type.val
    match idx with
    | .val idx =>
      /- Offsets wrap at 64 bits, so a negative index steps backwards. -/
      return (#[.addr ⟨ptr.object, UInt64.ofNat (ptr.offset.toNat + idx.toNat * size)⟩], mem, none)
    | .poison => Interp.ub
  | .intr__memcpy | .intr__memmove => do
    /- Bytes are copied as they are, so a pointer stored in the source keeps
       its provenance in the destination. -/
    let [.addr dst, .addr src, .int _ len] := operands.toList | none
    let .val len := len | Interp.ub
    let bytes ← mem.loadBytes src len.toNat
    let mem ← mem.storeBytes dst bytes
    return (#[], mem, none)
  | .intr__memset => do
    let [.addr dst, .int 8 v, .int _ len] := operands.toList | none
    let .val len := len | Interp.ub
    let byte : MemoryByte := match v with
      | .val v => .value (UInt8.ofBitVec v) 0
      | .poison => .poison
    let mem ← mem.storeBytes dst (Array.replicate len.toNat byte)
    return (#[], mem, none)
  | .ptrtoint => do
    let [.addr p] := operands.toList | none
    let [⟨.integerType bw, _⟩] := resultTypes.toList | none
    return (#[.int bw.bitwidth (.val (BitVec.ofNat bw.bitwidth (mem.address p).toNat))], mem, none)
  | .inttoptr => do
    let [.int _ v] := operands.toList | none
    match v with
    | .val v => return (#[.addr (mem.decode (UInt64.ofNat v.toNat))], mem, none)
    | .poison => return (#[.addr .null], mem, none) -- FIXME poison pointer
  | .freeze => do
    let [val] := operands.toList | none
    match val with
    | .int w val =>
        return (#[.int w val.freeze], mem, none)
    | .byte w val =>
        return (#[.byte w val.freeze], mem, none)
    | _ => none
  | .bitcast => do
    let [val] := operands.toList | none
    let [⟨type, _⟩] := resultTypes.toList | none
    let result ← do match val, type with
      | .int bw1 val', .integerType ⟨bw2⟩ =>
          if bw1 ≠ bw2 then .fail else .ok (val)
      | .int bw1 val', .byteType ⟨bw2⟩ =>
          if bw1 ≠ bw2 then .fail else .ok ((.byte bw1 $ LLVM.Byte.fromInt val'))
      | .byte bw1 val', .byteType ⟨bw2⟩ =>
          if bw1 ≠ bw2 then .fail else .ok (val)
      | .byte bw1 val', .integerType ⟨bw2⟩ =>
          if bw1 ≠ bw2 then .fail else .ok ((.int bw1 $ val'.toInt))
      | .byte bw val', .llvmPointerType _ =>
          if h : bw = 64 then .ok (.addr (mem.decode (val'.cast h).toUInt64)) else .fail
      | .addr val', .llvmPointerType _ => .ok (val)
      | .addr val', .byteType ⟨bw⟩ =>
          if h : bw = 64 then .ok ((.byte 64 $ LLVM.Byte.fromUInt64 (mem.address val'))) else .fail
      | _, _ => none
    return (#[result], mem, none)
  | _ => none

/-- Effective address of a RISC-V load/store: the base register value plus the
    sign-extended 12-bit immediate offset. -/
def riscvEffectiveAddr (base : BitVec 64) (offset : Int) : BitVec 64 :=
  base + (BitVec.ofInt 12 offset).signExtend 64

/-- For RISC-V sub-register loads. -/
inductive LoadExtension
  | signExt
  | zeroExt

/-- Read `bytes` of little-endian data from memory starting at the physical
    address `eaddr` and extend it to 64 bits according to `ext`. The object
    the address falls into is grown so that the access is in bounds where the
    gap to the next object allows it. -/
def riscvLoad (mem : MemoryState) (eaddr : BitVec 64) (bytes : Nat) (ext : LoadExtension) :
    Interp (BitVec 64 × MemoryState) := do
  let p := mem.decode (UInt64.ofBitVec eaddr)
  let mem := mem.ensureSize p bytes
  let ba ← mem.load p bytes
  let val := ba.toBitVecLE bytes
  let extended := match ext with
    | .signExt => val.signExtend 64
    | .zeroExt => val.setWidth 64
  return (extended, mem)

def Riscv.interpretOp' (opType : Veir.Riscv) (properties : propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    (mem : MemoryState)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .li => do
    let imm := BitVec.ofInt 64 properties.value.value
    return (#[.reg (RISCV.li imm)], mem, none)
  | .lui => do
    let imm := BitVec.ofInt 20 properties.value.value
    return (#[.reg (RISCV.lui imm)], mem, none)
  | .auipc => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 20 properties.value.value
    return (#[.reg (RISCV.auipc imm op)], mem, none)
  | .addi => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.addi imm op)], mem, none)
  | .slti => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.slti imm op)], mem, none)
  | .sltiu => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.sltiu imm op)], mem, none)
  | .andi => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.andi imm op)], mem, none)
  | .ori => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.ori imm op)], mem, none)
  | .xori => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.xori imm op)], mem, none)
  | .addiw => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 12 properties.value.value
    return (#[.reg (RISCV.addiw imm op)], mem, none)
  | .slli => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.slli imm op)], mem, none)
  | .srli => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.srli imm op)], mem, none)
  | .srai => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.srai imm op)], mem, none)
  | .add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.add op2 op1)], mem, none)
  | .sub => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sub op2 op1)], mem, none)
  | .sll => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sll op2 op1)], mem, none)
  | .slt => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.slt op2 op1)], mem, none)
  | .sltu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sltu op2 op1)], mem, none)
  | .xor => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.xor op2 op1)], mem, none)
  | .srl => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.srl op2 op1)], mem, none)
  | .sra => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sra op2 op1)], mem, none)
  | .or => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.or op2 op1)], mem, none)
  | .and => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.and op2 op1)], mem, none)
  | .slliw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.slliw imm op1)], mem, none)
  | .srliw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.srliw imm op1)], mem, none)
  | .sraiw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.sraiw imm op1)], mem, none)
  | .addw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.addw op2 op1)], mem, none)
  | .subw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.subw op2 op1)], mem, none)
  | .sllw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sllw op2 op1)], mem, none)
  | .srlw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.srlw op2 op1)], mem, none)
  | .sraw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sraw op2 op1)], mem, none)
  | .rem => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.rem op2 op1)], mem, none)
  | .remu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remu op2 op1)], mem, none)
  | .remw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remw op2 op1)], mem, none)
  | .remuw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remuw op2 op1)], mem, none)
  | .mul => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mul op2 op1)], mem, none)
  | .mulh => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulh op2 op1)], mem, none)
  | .mulhu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulhu op2 op1)], mem, none)
  | .mulhsu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulhsu op2 op1)], mem, none)
  | .mulw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulw op2 op1)], mem, none)
  | .div => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.div op2 op1)], mem, none)
  | .divw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divw op2 op1)], mem, none)
  | .divu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divu op2 op1)], mem, none)
  | .divuw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divuw op2 op1)], mem, none)
  | .adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.adduw op2 op1)], mem, none)
  | .sh1adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh1adduw op2 op1)], mem, none)
  | .sh2adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh2adduw op2 op1)], mem, none)
  | .sh3adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh3adduw op2 op1)], mem, none)
  | .sh1add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh1add op2 op1)], mem, none)
  | .sh2add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh2add op2 op1)], mem, none)
  | .sh3add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh3add op2 op1)], mem, none)
  | .slliuw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.slliuw imm op1)], mem, none)
  | .andn => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.andn op2 op1)], mem, none)
  | .orn => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.orn op2 op1)], mem, none)
  | .xnor => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.xnor op2 op1)], mem, none)
  | .max => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.max op2 op1)], mem, none)
  | .maxu => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.maxu op2 op1)], mem, none)
  | .min => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.min op2 op1)], mem, none)
  | .minu => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.minu op2 op1)], mem, none)
  | .rol => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rol op2 op1)], mem, none)
  | .ror => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.ror op2 op1)], mem, none)
  | .rolw => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rolw op2 op1)], mem, none)
  | .rorw => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rorw op2 op1)], mem, none)
  | .sextb => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sextb op)], mem, none)
  | .sexth => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sexth op)], mem, none)
  | .zexth => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zexth op)], mem, none)
  | .clz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.clz op)], mem, none)
  | .clzw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.clzw op)], mem, none)
  | .ctz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.ctz op)], mem, none)
  | .ctzw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.ctzw op)], mem, none)
  | .cpop => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.cpop op)], mem, none)
  | .cpopw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.cpopw op)], mem, none)
  | .orcb => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.orcb op)], mem, none)
  | .rev8 => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.rev8 op)], mem, none)
  | .roriw => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 5 properties.value.value
    return (#[.reg (RISCV.roriw imm op1)], mem, none)
  | .rori => do
    let [.reg op1] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.rori imm op1)], mem, none)
  | .bclr => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bclr op2 op1)], mem, none)
  | .bext => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bext op2 op1)], mem, none)
  | .binv => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.binv op2 op1)], mem, none)
  | .bset => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bset op2 op1)], mem, none)
  | .bclri => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bclri imm op)], mem, none)
  | .bexti => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bexti imm op)], mem, none)
  | .binvi => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.binvi imm op)], mem, none)
  | .bseti => do
    let [.reg op] := operands.toList | none
    let imm := BitVec.ofInt 6 properties.value.value
    return (#[.reg (RISCV.bseti imm op)], mem, none)
  | .pack => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.pack op2 op1)], mem, none)
  | .packh => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.packh op2 op1)], mem, none)
  | .packw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.packw op2 op1)], mem, none)
  | .czeroeqz => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.czeroeqz op2 op1)], mem, none)
  | .czeronez => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.czeronez op2 op1)], mem, none)
  | .mv => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.mv op)], mem, none)
  | .not => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.not op)], mem, none)
  | .neg => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.neg op)], mem, none)
  | .negw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.negw op)], mem, none)
  | .sextw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sextw op)], mem, none)
  | .zextb => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zextb op)], mem, none)
  | .zextw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zextw op)], mem, none)
  | .seqz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.seqz op)], mem, none)
  | .snez => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.snez op)], mem, none)
  | .sltz=> do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sltz op)], mem, none)
  | .sgtz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sgtz op)], mem, none)
  | .ld => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let (val, mem) ← riscvLoad mem eaddr 8 .zeroExt
    return (#[.reg $ .mk val], mem, none)
  | .lw => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let (val, mem) ← riscvLoad mem eaddr 4 .signExt
    return (#[.reg $ .mk val], mem, none)
  | .lwu => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let (val, mem) ← riscvLoad mem eaddr 4 .zeroExt
    return (#[.reg $ .mk val], mem, none)
  | .lh => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let (val, mem) ← riscvLoad mem eaddr 2 .signExt
    return (#[.reg $ .mk val], mem, none)
  | .lhu => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let (val, mem) ← riscvLoad mem eaddr 2 .zeroExt
    return (#[.reg $ .mk val], mem, none)
  | .lb => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let (val, mem) ← riscvLoad mem eaddr 1 .signExt
    return (#[.reg $ .mk val], mem, none)
  | .lbu => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let (val, mem) ← riscvLoad mem eaddr 1 .zeroExt
    return (#[.reg $ .mk val], mem, none)
  | .sd => do
    let [.reg { val }, .reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let p := mem.decode (UInt64.ofBitVec eaddr)
    let mem := mem.ensureSize p 8
    let mem ← mem.store p (UInt64.ofBitVec val).toByteArrayLE
    return (#[], mem, none)
  | .sw => do
    let [.reg { val }, .reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let p := mem.decode (UInt64.ofBitVec eaddr)
    let mem := mem.ensureSize p 4
    -- store only the low 4 bytes of the register
    let mem ← mem.store p ((UInt64.ofBitVec val).toByteArrayLE.extract 0 4)
    return (#[], mem, none)
  | .sh => do
    let [.reg { val }, .reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let p := mem.decode (UInt64.ofBitVec eaddr)
    let mem := mem.ensureSize p 2
    -- store only the low 2 bytes of the register
    let mem ← mem.store p ((UInt64.ofBitVec val).toByteArrayLE.extract 0 2)
    return (#[], mem, none)
  | .sb => do
    let [.reg { val }, .reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.value.value
    let p := mem.decode (UInt64.ofBitVec eaddr)
    let mem := mem.ensureSize p 1
    -- store only the low byte of the register
    let mem ← mem.store p ((UInt64.ofBitVec val).toByteArrayLE.extract 0 1)
    return (#[], mem, none)

def Riscv_Stack.interpretOp' (opType : Veir.Riscv_Stack) (properties : propertiesOf opType)
    (_resultTypes : Array TypeAttr) (_operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    (mem : MemoryState)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .alloca => do
    let (mem, ptr) := mem.alloc properties.size.value.toNat .stack properties.alignment.value.toNat.toUInt64
    return (#[.reg ⟨(mem.address ptr).toBitVec⟩], mem, none)

def Riscv_Cf.interpretOp' (opType : Veir.Riscv_Cf) (properties : propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    : Interp (Array RuntimeValue × Option ControlFlowAction) :=
  match opType with
  | .branch => do
    let [dest] := blockOperands.toList | none
    return (#[], some (.branch operands dest))
  | .beq => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if lhs == rhs then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .bne => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if lhs != rhs then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .blt => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if BitVec.slt lhs.val rhs.val then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .bge => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if !BitVec.slt lhs.val rhs.val then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .bltu => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if BitVec.ult lhs.val rhs.val then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .bgeu => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg lhs) := operands[0]? | none
    let some (RuntimeValue.reg rhs) := operands[1]? | none
    let some trueSize := properties.operandSegmentSizes.values[2]? | none
    let trueSize := trueSize.toNat
    if !BitVec.ult lhs.val rhs.val then
      return (#[], some (.branch (operands.extract 2 (trueSize + 2)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 2) operands.size) destFalse))
  | .beqz => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg cond) := operands[0]? | none
    let some trueSize := properties.operandSegmentSizes.values[1]? | none
    let trueSize := trueSize.toNat
    if cond.val = 0#64 then
      return (#[], some (.branch (operands.extract 1 (trueSize + 1)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 1) operands.size) destFalse))
  | .bnez => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (RuntimeValue.reg cond) := operands[0]? | none
    let some trueSize := properties.operandSegmentSizes.values[1]? | none
    let trueSize := trueSize.toNat
    if cond.val ≠ 0#64 then
      return (#[], some (.branch (operands.extract 1 (trueSize + 1)) destTrue))
    else
      return (#[], some (.branch (operands.extract (trueSize + 1) operands.size) destFalse))

def Rv64.interpretOp' (opType : Veir.Rv64) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (_operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    : Option ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .get_register => do
    let [⟨.registerType reg, _⟩] := resultTypes.toList | none
    if reg.index = some 0 then
      return (#[.reg ⟨0⟩], none)
    else
      none

def Cf.interpretOp' (opType : Veir.Cf) (properties : propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    : Interp ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .br => do
    let [dest] := blockOperands.toList | none
    return (#[], some (.branch operands dest))
  | .cond_br => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some condVal := operands[0]? | none
    let some (trueSizeInt : Int) := properties.operandSegmentSizes.values[1]? | none
    let trueSize := trueSizeInt.toNat
    match condVal with
    | .int 1 (.val cond) =>
      if cond = 1#1 then
        return (#[], some (.branch (operands.extract 1 (trueSize + 1)) destTrue))
      else
        return (#[], some (.branch (operands.extract (trueSize + 1) operands.size) destFalse))
    | .int 1 .poison => Interp.ub
    | _ => none

def Comb.interpretOp' (opType : Veir.Comb) (properties : propertiesOf opType)
    (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    : Option ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .add => do
    let l : List _ := operands.toList
    let .int w fst := l[0]! | none
    let some nl := l.mapM (
        fun e => do
          let .int w' val := e | none
          if h : w' ≠ w then none else
          return val.cast (by simpa using h)) | none
    return (#[.int w (Veir.Data.Comb.add nl)], none)
  | _ => none

def HW.interpretOp' (opType : Veir.HW) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (_blockOperands : Array BlockPtr)
    : Option ((Array RuntimeValue) × Option ControlFlowAction) :=
  match opType with
  | .constant => do
    let resType ← resultTypes[0]?
    let .integerType bw := resType.val
      | none
    return (#[.int bw.bitwidth
      (.val (Veir.Data.HW.constant (BitVec.ofInt bw.bitwidth properties.value.value)).val)], none)
  | _ => none
/--
  Interpret a single operation given its opcode, type-dependent properties,
  result types, and the runtime values of its operands.
  Return the result runtime values and an optional control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  returns `none`.
-/
def interpretOp' (opType : OpCode) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState) (layout : DataLayout := .riscv64)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .arith arithOp => do
    let (vals, act) ← Arith.interpretOp' arithOp properties resultTypes operands blockOperands
    return (vals, mem, act)
  | .mod_arith modArithOp => do
    let (vals, act) ← ModArith.interpretOp' modArithOp properties resultTypes operands blockOperands
    return (vals, mem, act)
  | .felt feltOp => do
    let (vals, act) ← Felt.interpretOp' feltOp properties resultTypes operands blockOperands
    return (vals, mem, act)
  | .llvm llvmOp => do
    Llvm.interpretOp' llvmOp properties resultTypes operands blockOperands mem layout
  | .riscv riscvOp => do
    Riscv.interpretOp' riscvOp properties resultTypes operands blockOperands mem
  | .riscv_cf riscvCfOp => do
    let (vals, act) ← Riscv_Cf.interpretOp' riscvCfOp properties resultTypes operands blockOperands
    return (vals, mem, act)
  | .riscv_stack riscvStackOp =>
    Riscv_Stack.interpretOp' riscvStackOp properties resultTypes operands blockOperands mem
  | .rv64 rv64Op => do
    let (vals, act) ← Rv64.interpretOp' rv64Op properties resultTypes operands blockOperands
    return (vals, mem, act)
  | .cf cfOp => do
    let (vals, act) ← Cf.interpretOp' cfOp properties resultTypes operands blockOperands
    return (vals, mem, act)
  | .comb combOp => do
    let (vals, act) ← Comb.interpretOp' combOp properties operands blockOperands
    return (vals, mem, act)
  | .hw hwOp => do
    let (vals, act) ← HW.interpretOp' hwOp properties resultTypes blockOperands
    return (vals, mem, act)
  | .func .return => do
    return (#[], mem, some (.return operands))
  | .cir .return => do
    return (#[], mem, some (.return operands))
  | .builtin .unrealized_conversion_cast => do
    let some resType := resultTypes[0]? | none
    match resType.val, operands.toList with
    | .registerType _, [.int _bw val] =>
      return (#[.reg (LLVM.Int.toReg val)], mem, none)
    | .registerType _, [.byte _bw val] =>
      return (#[.reg (LLVM.Byte.toReg val)], mem, none)
    | .registerType _, [.addr val] =>
      return (#[.reg ⟨(mem.address val).toBitVec⟩], mem, none)
    | .integerType _bw, [.reg val] =>
      let .integerType resBw := resType.val | none
      return (#[.int resBw.bitwidth (RISCV.Reg.toInt val resBw.bitwidth)], mem, none)
    | .byteType _bw, [.reg val] =>
      let .byteType resBw := resType.val | none
      return (#[.byte resBw.bitwidth (RISCV.Reg.toByte val resBw.bitwidth)], mem, none)
    | .llvmPointerType _, [.reg val] =>
      return (#[.addr (mem.decode ⟨val.val⟩)], mem, none)
    | _ , _ => none
  | _ => none

/-- Wrapper around `interpretOp'` that retrieves the operation type, properties,
result types, and successor blocks from the operation pointer. -/
abbrev OperationPtr.interpret (op : OperationPtr) (ctx : IRContext OpCode)
    (operandValues : Array RuntimeValue) (memory : MemoryState)
    (layout : DataLayout := .riscv64) :=
    interpretOp' (op.getOpType! ctx) (op.getProperties! ctx (op.getOpType! ctx))
    (op.getResultTypes! ctx) operandValues (op.getSuccessors! ctx) memory layout

/--
  Interpret a single operation given the current interpreter state.
  Return an updated interpreter state and a control flow action indicating how
  to continue the interpretation.
  If any error occurs during interpretation (e.g., unknown operation, missing variable),
  return `none`.
-/
@[expose]
def interpretOp (op : OperationPtr) {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (inBounds : op.InBounds ctx.raw := by grind)
    : Interp (InterpreterState ctx × Option ControlFlowAction) := do
  let some operands := state.variables.getOperandValues op | none
  let (resultValues, mem, action) ← op.interpret ctx operands state.memory
  let newVars ← state.variables.setResultValues? op resultValues
  let newState := ⟨newVars, mem⟩
  return (newState, action)

/--
  Interpret a chain of operations, starting from the given operation pointer.
  Continue to interpret operations until a terminator is encountered,
  or the end of the block is reached.
  Return a ControlFlowAction indicating how to continue the interpretation.
  Return `none` if any errors occur during interpretation.
-/
def interpretOpChain (op : OperationPtr) {ctx : WfIRContext OpCode} (state : InterpreterState ctx)
    (opInBounds : op.InBounds ctx.raw := by grind)
    : Interp (InterpreterState ctx × ControlFlowAction) := do
  let (state, action) ← interpretOp op state
  match action with
  | none =>
    rlet next ← (op.get ctx.raw).next
    interpretOpChain next state
  | some action =>
    return (state, action)
termination_by op.idxInParentFromTail ctx.raw
decreasing_by grind

/--
  Interpret a list of operations passed as a `List`, stopping at the first terminator.
  Return the new interpreter state, and an optional control flow action indicating how to
  continue the interpretation, with an absent control flow action indicating that the end of the
  list was reached without encountering a terminator.
  Return `none` if any errors occur during interpretation.
-/
def interpretOpList {ctx : WfIRContext OpCode} (ops : List OperationPtr)
    (state : InterpreterState ctx)
    (opInBounds : ∀ op ∈ ops, op.InBounds ctx.raw := by grind)
    : Interp (InterpreterState ctx × Option ControlFlowAction) :=
  match ops with
  | [] => return (state, none)
  | op :: ops => do
    let (state, action) ← interpretOp op state
    match action with
    | none => interpretOpList ops state (by grind)
    | some cf => return (state, cf)

/--
  Interpret a list of operations passed as a `List`, stopping at the first terminator.
  Return the new interpreter state, and a control flow action indicating how to continue the
  interpretation. If no terminator is encountered, return `none`.
  Return `none` if any errors occur during interpretation.
-/
@[expose]
def interpretTerminatedOpList {ctx : WfIRContext OpCode} (ops : List OperationPtr)
    (state : InterpreterState ctx)
    (opInBounds : ∀ op ∈ ops, op.InBounds ctx.raw := by grind)
    : Interp (InterpreterState ctx × ControlFlowAction) := do
  match ← interpretOpList ops state opInBounds with
  | (_, none) => none
  | (state, some cf) => return (state, cf)

/--
  Interpret a block of operations, starting from the first operation in the block.
  The block arguments are set from `values` before interpreting the operations.
  Return the resulting interpreter state and a ControlFlowAction indicating how
  to continue the interpretation.
  Return `none` if any errors occur during interpretation.
-/
def interpretBlock (blockPtr : BlockPtr) (values : Array RuntimeValue) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (blockInBounds : blockPtr.InBounds ctx.raw := by grind) :
    Interp (InterpreterState ctx × ControlFlowAction) := do
  let newVars ← state.variables.setArgumentValues? blockPtr values
  let state := ⟨newVars, state.memory⟩
  rlet firstOp ← (blockPtr.get ctx.raw).firstOp
  interpretOpChain firstOp state

/--
  Interpret a CFG, starting from the given block.
  The arguments of the starting block are set from `values`.
  Return the resulting interpreter state and values eventually returned, if any.
  Return `none` if any errors occur during interpretation.
-/
def interpretBlockCFG (blockPtr : BlockPtr) (values : Array RuntimeValue) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (blockInBounds : blockPtr.InBounds ctx.raw := by grind) :
    Interp (InterpreterState ctx × Array RuntimeValue) := do
  match interpretBlock blockPtr values state blockInBounds with
  | .ok (state, .return res) => .ok (state, res)
  | .ok (state, .branch res succ) =>
    if h : succ.InBounds ctx.raw then
      interpretBlockCFG succ res state h
    else
      .fail
  | .ub => .ub
  | .fail => .fail
partial_fixpoint

/--
  Interpret a region, starting from its first block.
  The arguments of the first block are set from `values`.
  Return the resulting interpreter state and values eventually returned, or `none`
  if any errors occur during interpretation.
-/
def interpretRegion (region : RegionPtr) (values : Array RuntimeValue) {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (regionIn : region.InBounds ctx.raw := by grind) :
    Interp (InterpreterState ctx × Array RuntimeValue) := do
  rlet block ← (region.get ctx.raw).firstBlock
  interpretBlockCFG block values state

/--
  Interpret an operation representing a function, given the runtime values of its arguments
  and the current memory state. Return the resulting memory state and the values eventually
  returned.

  Unlike the other interpreter functions, this does not take an `InterpreterState`:
  a function call starts with a fresh, empty variable state, since the caller's SSA
  values are not visible inside the callee.
-/
def interpretFunction (op : OperationPtr) (values : Array RuntimeValue) {ctx : WfIRContext OpCode}
    (mem : MemoryState) (opIn : op.InBounds ctx.raw := by grind) :
    Interp (MemoryState × Array RuntimeValue) := do
  if h : op.getNumRegions ctx.raw ≠ 1 then
    none
  else
    let state : InterpreterState ctx := ⟨.empty ctx, mem⟩
    let frameStart := mem.objects.size
    let (state, results) ← interpretRegion (FunctionOpInterface.getFunctionBody op ctx.raw) values state
    /- The function's stack objects die when it returns. -/
    return (state.memory.killStackObjectsFrom frameStart, results)

/--
  Interpret a builtin.module operation.
  This is done by interpreting the unique region of the operation.
  Return the values eventually returned, or `none` if any errors occur during interpretation.
-/
def interpretModule (ctx : WfIRContext OpCode) (op : OperationPtr)
    (opIn : op.InBounds ctx.raw := by grind) : Interp (Array RuntimeValue) := do
  if h: op.getNumRegions ctx.raw ≠ 1 then
    none
  else
    let (_state, results) ← interpretRegion (op.getRegion ctx.raw 0) #[] (InterpreterState.empty ctx)
    return results

end Veir
