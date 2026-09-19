module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.Arith.Properties
public import Veir.Dialects.LLVM.Properties
public import Veir.Dialects.LLVM.OpInfo
public import Veir.ConstantMaterialization
public import Veir.RuntimeValue.Basic
public import Veir.Interpreter.Interp
public import Veir.Data.LLVM.Int.Basic

meta import Veir.Meta.OpCode

open Veir.Data

namespace Veir

public section

@[opcodes]
inductive Arith where
| addi
| addui_extended
| andi
| ceildivsi
| ceildivui
| cmpi
| constant
| divsi
| divui
| extsi
| extui
| floordivsi
| maxsi
| maxui
| minsi
| minui
| muli
| mulsi_extended
| mului_extended
| ori
| remsi
| remui
| select
| shli
| shrsi
| shrui
| subi
| subui_extended
| trunci
| xori
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Arith.propertiesOf (op : Arith) : Type :=
match op with
| .constant => ArithConstantProperties
| .addi => ArithIntegerOverflowFlagsProperties
| .subi => ArithIntegerOverflowFlagsProperties
| .muli => ArithIntegerOverflowFlagsProperties
| .divsi => ExactProperties
| .divui => ExactProperties
| .cmpi => IcmpProperties
| .shli => ArithIntegerOverflowFlagsProperties
| .shrsi => ExactProperties
| .shrui => ExactProperties
| .ori => DisjointProperties
| .trunci => ArithIntegerOverflowFlagsProperties
| .extui => NnegProperties
| _ => Unit

def Arith.fromAttrDict
    (op : Arith) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Arith.propertiesOf op) := by
  cases op
  case constant => exact ArithConstantProperties.fromAttrDict attrDict
  case addi | subi | muli | shli | trunci =>
    exact ArithIntegerOverflowFlagsProperties.fromAttrDict attrDict
  case divsi | divui | shrsi | shrui =>
    exact ExactProperties.fromAttrDict attrDict
  case cmpi => exact IcmpProperties.fromAttrDictFor "arith.cmpi" attrDict
  case ori => exact DisjointProperties.fromAttrDict attrDict
  case extui => exact NnegProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Arith.toAttrDict
    (op : Arith) (props : Arith.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .constant =>
    (Std.HashMap.emptyWithCapacity 2).insert
      "value".toUTF8 (Attribute.integerAttr props.value)
  | .addi | .subi | .muli | .shli | .trunci => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    if props.attr.nsw || props.attr.nuw then
      dict := dict.insert
        "overflowFlags".toUTF8
        (Attribute.arithIntegerOverflowFlagsAttr props.attr)
    dict
  | .cmpi =>
    let value := IntegerAttr.mk (Int.ofNat props.predicate.toNat) (IntegerType.signless 64)
    (Std.HashMap.emptyWithCapacity 1).insert
      "predicate".toUTF8 (Attribute.integerAttr value)
  | .divsi | .divui | .shrsi | .shrui => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.exact then
      dict := dict.insert "isExact".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .ori => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.disjoint then
      dict := dict.insert "isDisjoint".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .extui => props.toAttrDict
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Arith.getEffects
    (_op : Arith) (_props : Arith.propertiesOf _op) : MemoryEffects :=
  .none

def Arith.isConstantLike (op : Arith) : Bool :=
  match op with
  | .constant => true
  | _ => false

def Arith.hasSSADominance (_op : Arith) (_index : Nat) : Bool :=
  true

#generate_dialect Arith

/-- Operations whose result is poison whenever any operand is poison. -/
def Arith.propagatesPoison : Arith → Bool
  | .addi | .andi | .ceildivsi | .ceildivui | .cmpi | .divsi | .divui
  | .extsi | .extui | .floordivsi | .maxsi | .maxui | .minsi | .minui
  | .muli | .ori | .remsi | .remui | .shli | .shrsi | .shrui | .subi
  | .trunci | .xori | .addui_extended | .subui_extended
  | .mulsi_extended | .mului_extended => true
  | .constant | .select => false

def Arith.tryFold (op : Arith) (_properties : Arith.propertiesOf op)
    (_resultTypes : Array TypeAttr) (constantOperands : Array (Option RuntimeValue)) :
    Option (Array FoldDecision) :=
  match op, constantOperands.toList with
  | .addi, [_, some (.int _ (.val bits))] =>
    if bits = 0 then some #[.useOperand 0] else none
  -- Adding zero cannot carry, so the overflow flag is a false `i1`.
  | .addui_extended, [_, some (.int _ (.val bits))] =>
    if bits = 0 then some #[.useOperand 0, .useConstant (.int 1 (.val 0#1))] else none
  | _, _ => none

instance : IsOpCode Arith where
  fromName := Arith.fromName
  name := Arith.name
  propertiesOf := Arith.propertiesOf
  fromAttrDict := Arith.fromAttrDict
  toAttrDict := Arith.toAttrDict

/--
Materialize integer results of folded arithmetic operations as `arith.constant`.
Poison is materialized as `llvm.mlir.poison`.
-/
def Arith.materializeConstant {OpInfo : Type} [HasOpInfo OpInfo] [HasDialect OpInfo Arith]
    [HasDialect OpInfo Llvm] (_op : Arith) (value : RuntimeValue) (type : TypeAttr) :
    Option (Materialized OpInfo) :=
  match value, type.val with
  | .int bw (.val value), .integerType intType =>
    if bw = intType.bitwidth then
      some (.of Arith.constant (ArithConstantProperties.mk (IntegerAttr.mk value.toInt intType)))
    else none
  | .int bw .poison, .integerType intType =>
    if bw = intType.bitwidth then some (.of Llvm.mlir__poison ()) else none
  | _, _ => none

/--
Verify an `arith` extended operation with two same-typed integer operands and
two results. The low result always matches the operand type; the high result
is either an `i1` overflow flag (`addui_extended` / `subui_extended`) or
another value of the operand type (`mulsi_extended` / `mului_extended`).
-/
def OperationPtr.verifyArithExtendedOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) (secondResultIsI1 : Bool) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 2
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerType
    s!"{instrName}: Expected operand 0 to have integer type"
  ((op.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerType
    s!"{instrName}: Expected operand 1 to have integer type"
  let operandType ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result 0 type to match operand type"
  let result1Type := ((op.getResult 1).get! ctx.raw).type
  if secondResultIsI1 then
    result1Type.verifyI1 s!"{instrName}: Expected i1 result 1"
  else if result1Type.val ≠ operandType.val then
    throw s!"{instrName}: Expected result 1 type to match operand type"

/--
Verify the local invariants of an `arith` operation in any operation-info type
containing the `arith` dialect.
-/
@[expose]
def Arith.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo] [HasDialect OpInfo Arith]
    (opType : Arith) (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .addi | .andi | .ceildivsi | .ceildivui | .divsi | .divui | .floordivsi
  | .maxsi | .maxui | .minsi | .minui | .muli | .ori | .remsi | .remui
  | .shli | .shrsi | .shrui | .subi | .xori => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyIntegerBinop ctx opIn
    pure ()
  | .addui_extended | .subui_extended => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyArithExtendedOp ctx opIn true
    pure ()
  | .mulsi_extended | .mului_extended => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyArithExtendedOp ctx opIn false
    pure ()
  | .cmpi => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyICmp ctx opIn
    pure ()
  | .constant => do
    op.checkIsNonNullIntegerType ctx opIn
    if op.getNumOperands ctx.raw opIn ≠ 0 then
      throw "Expected 0 operands"
    else if _ : op.getNumResults ctx.raw opIn ≠ 1 then
      throw "Expected 1 result"
    else if op.getNumRegions ctx.raw opIn ≠ 0 then
      throw "Expected 0 regions"
    else if op.getNumSuccessors ctx.raw opIn ≠ 0 then
      throw "Expected 0 successors"
    else
      let props : Arith.propertiesOf .constant :=
        op.getProperties! ctx.raw Arith.constant
      if props.value.type ≠ ((op.getResult 0).get ctx.raw).type.val then
        throw "Expected result type to be equal to the constant's type"
    pure ()
  | .extui | .extsi => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyIntegerExtTypes ctx opIn
    pure ()
  | .select => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifySelectTypes ctx opIn
    pure ()
  | .trunci => do
    op.checkIsNonNullIntegerType ctx opIn
    op.verifyTruncTypes ctx opIn false
    pure ()

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
    if LLVM.Int.isUnsignedDivisionUB rhs then Interp.ub
    return (#[.int bw (LLVM.Int.udiv lhs rhs properties.exact)], none)
  | .divsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    if LLVM.Int.isSignedDivisionUB lhs rhs then Interp.ub
    return (#[.int bw (LLVM.Int.sdiv lhs rhs properties.exact)], none)
  | .remui => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    if LLVM.Int.isUnsignedDivisionUB rhs then Interp.ub
    return (#[.int bw (LLVM.Int.urem lhs rhs)], none)
  | .remsi => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h: bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    if LLVM.Int.isSignedDivisionUB lhs rhs then Interp.ub
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
    if LLVM.Int.isUnsignedDivisionUB b then Interp.ub
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
    if LLVM.Int.isSignedDivisionUB a b then Interp.ub
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
    if LLVM.Int.isSignedDivisionUB a b then Interp.ub
    let z := LLVM.Int.sdiv a b
    let notExact := LLVM.Int.icmp a (LLVM.Int.mul z b) .ne
    let signOpposite := LLVM.Int.icmp (LLVM.Int.icmp a zero .slt) (LLVM.Int.icmp b zero .slt) .ne
    let cond := LLVM.Int.and notExact signOpposite
    return (#[.int bw (LLVM.Int.select cond (LLVM.Int.add z negOne) z)], none)

instance : HasOpInfo Arith where
  verifyLocalInvariants := Arith.verifyLocalInvariants
  tryFold := Arith.tryFold
  propagatesPoison := Arith.propagatesPoison
  getEffects := Arith.getEffects
  isConstantLike := Arith.isConstantLike
  hasSSADominance := Arith.hasSSADominance

end

end Veir
