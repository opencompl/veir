module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.Arith.Properties
public import Veir.Dialects.LLVM.Properties
public import Veir.Dialects.LLVM.OpInfo
public import Veir.ConstantMaterialization
meta import Veir.Meta.OpCode

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
    let value := IntegerAttr.mk (Int.ofNat props.predicate.toNat) (IntegerType.mk 64)
    (Std.HashMap.emptyWithCapacity 1).insert
      "predicate".toUTF8 (Attribute.integerAttr value)
  | .divsi | .divui | .shrsi | .shrui => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.exact then
      dict := dict.insert "exact".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .ori => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    if props.disjoint then
      dict := dict.insert "disjoint".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .extui => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    if props.nneg then
      dict := dict.insert "nneg".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | _ => Std.HashMap.emptyWithCapacity 0

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

instance : HasOpInfo Arith where
  verifyLocalInvariants := Arith.verifyLocalInvariants
  getEffects := Arith.getEffects
  isConstantLike := Arith.isConstantLike
  hasSSADominance := Arith.hasSSADominance

end

end Veir
