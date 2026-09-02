module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Felt.Properties
public import Veir.ConstantMaterialization
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Felt where
| const
| add
| sub
| mul
| pow
| div
| uintdiv
| sintdiv
| umod
| smod
| neg
| inv
| bit_and
| bit_or
| bit_xor
| bit_not
| shl
| shr
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Felt.propertiesOf (op : Felt) : Type :=
match op with
| .const => FeltConstProperties
| _ => Unit

/-- Reject properties on Felt operations whose schema carries none. -/
private def noProperties (attrDict : Std.HashMap ByteArray Attribute) :
    Except String Unit :=
  if attrDict.size > 0 then
    let plural := if attrDict.size = 1 then "property" else "properties"
    .error s!"felt: expected no properties, but got {attrDict.size} {plural}"
  else
    .ok ()

def Felt.fromAttrDict
    (op : Felt) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Felt.propertiesOf op) :=
  match op with
  | .const => FeltConstProperties.fromAttrDict attrDict
  | .add | .sub | .mul | .pow | .div | .uintdiv | .sintdiv | .umod | .smod
  | .neg | .inv | .bit_and | .bit_or | .bit_xor | .bit_not | .shl | .shr =>
    noProperties attrDict

def Felt.toAttrDict
    (op : Felt) (props : Felt.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .const =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "value".toUTF8 (Attribute.feltConstAttr props.value)
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Felt.getEffects
    (_op : Felt) (_props : Felt.propertiesOf _op) : MemoryEffects :=
  .none

def Felt.isConstantLike (op : Felt) : Bool :=
  match op with
  | .const => true
  | _ => false

def Felt.hasSSADominance (_op : Felt) (_index : Nat) : Bool :=
  true

#generate_dialect Felt

instance : IsOpCode Felt where
  fromName := Felt.fromName
  name := Felt.name
  propertiesOf := Felt.propertiesOf
  fromAttrDict := Felt.fromAttrDict
  toAttrDict := Felt.toAttrDict

/-- Materialize a concrete Felt interpreter value as `felt.const`. -/
def Felt.materializeConstant {OpInfo : Type} [HasOpInfo OpInfo] [HasDialect OpInfo Felt]
    (_op : Felt) (value : RuntimeValue) (type : TypeAttr) : Option (Materialized OpInfo) :=
  match value, type.val with
  | .felt valueType value, .feltType resultType =>
    if valueType = resultType then
      some (.of Felt.const
        (FeltConstProperties.mk (FeltConstAttr.mk (Int.ofNat value) resultType)))
    else none
  | _, _ => none

/-- Verify that a type is an LLZK felt type. -/
def TypeAttr.verifyFeltType (ty : TypeAttr) (msg : String) : Except String FeltType :=
  match ty.val with
  | .feltType type => pure type
  | type => throw s!"{msg}, but found {type} instead"

/-- Verify a binary felt operation, including its operand and result types. -/
def OperationPtr.verifyFeltBinOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 2 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType ← op.verifyOperandTypesMatch ctx 0 1
    s!"{instrName}: Expected operands to have the same type"
  let _ ← operandType.verifyFeltType s!"{instrName}: Expected operands to have FeltType"
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match operand type"

/-- Verify a unary felt operation, including its operand and result types. -/
def OperationPtr.verifyFeltUnOp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
  let _ ← operandType.verifyFeltType s!"{instrName}: Expected operand to have FeltType"
  op.verifyResultTypeMatches ctx operandType
    s!"{instrName}: Expected result type to match operand type"

/-- Verify a felt constant, including agreement between its attribute and result type. -/
def OperationPtr.verifyFeltConstOp {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Felt] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 0 1
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let resultType := ((op.getResult 0).get! ctx.raw).type
  let resultFeltType ← resultType.verifyFeltType
    s!"{instrName}: Expected result to have FeltType"
  let props := op.getProperties! ctx.raw Felt.const
  if props.value.fieldType ≠ resultFeltType then
    throw s!"{instrName}: Expected result type to match the constant's type"

/--
Verify the local invariants of a `felt` operation in any operation-info type
containing the `felt` dialect.
-/
@[expose]
def Felt.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Felt] (opType : Felt) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .const => op.verifyFeltConstOp ctx opIn
  | .add | .sub | .mul | .pow | .div
  | .uintdiv | .sintdiv | .umod | .smod
  | .bit_and | .bit_or | .bit_xor
  | .shl | .shr => op.verifyFeltBinOp ctx opIn
  | .neg | .inv | .bit_not => op.verifyFeltUnOp ctx opIn

instance : HasOpInfo Felt where
  verifyLocalInvariants := Felt.verifyLocalInvariants
  getEffects := Felt.getEffects
  isConstantLike := Felt.isConstantLike
  hasSSADominance := Felt.hasSSADominance

end

end Veir
