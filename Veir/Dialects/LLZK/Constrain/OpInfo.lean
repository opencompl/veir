module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

namespace LLZK

@[opcodes]
inductive Constrain where
| eq
/-- `constrain.in %arr, %tuple` — lookup-containment constraint. -/
| «in»
deriving Inhabited, Repr, Hashable, DecidableEq

end LLZK

@[expose, properties_of]
def LLZK.Constrain.propertiesOf (_op : LLZK.Constrain) : Type := Unit

private def noProperties (opName : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String Unit :=
  if attrDict.size > 0 then
    let plural := if attrDict.size = 1 then "property" else "properties"
    .error s!"{opName}: expected no properties, but got {attrDict.size} {plural}"
  else
    .ok ()

def LLZK.Constrain.fromAttrDict
    (op : LLZK.Constrain) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (LLZK.Constrain.propertiesOf op) :=
  match op with
  | .eq => noProperties "constrain.eq" attrDict
  | .«in» => noProperties "constrain.in" attrDict

def LLZK.Constrain.toAttrDict
    (_op : LLZK.Constrain) (_props : LLZK.Constrain.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

/--
`constrain.eq` and `constrain.in` emit constraints into the circuit. They
have no results, so they must report an effect or DCE would erase the
constraint system.
-/
def LLZK.Constrain.getEffects
    (_op : LLZK.Constrain) (_props : LLZK.Constrain.propertiesOf _op) : MemoryEffects :=
  .write

def LLZK.Constrain.isConstantLike (_op : LLZK.Constrain) : Bool := false

def LLZK.Constrain.hasSSADominance (_op : LLZK.Constrain) (_index : Nat) : Bool := true

#generate_dialect LLZK.Constrain

instance : IsOpCode LLZK.Constrain where
  fromName := LLZK.Constrain.fromName
  name := LLZK.Constrain.name
  propertiesOf := LLZK.Constrain.propertiesOf
  fromAttrDict := LLZK.Constrain.fromAttrDict
  toAttrDict := LLZK.Constrain.toAttrDict

private def Attribute.isSupportedLLZKConstrainEqType (type : Attribute) : Bool :=
  match type with
  | .integerType intType => intType.bitwidth = 1
  | .indexType _ | .feltType _ | .arrayType _ => true
  | _ => false

/-- Whether `candidate` is an element or trailing-dimensional subarray of `arrayType`. -/
private def isLLZKSubArrayOrElementType
    (arrayType : LLZK.ArrayType) (candidate : Attribute) : Bool :=
  match candidate with
  | .arrayType subArrayType =>
    if subArrayType.dims.size > arrayType.dims.size then
      false
    else
      decide (arrayType.dims.toList.drop (arrayType.dims.size - subArrayType.dims.size) =
        subArrayType.dims.toList ∧ arrayType.elementType = subArrayType.elementType)
  | elementType => decide (arrayType.elementType = elementType)

def LLZK.Constrain.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.Constrain] (opType : LLZK.Constrain) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .eq => do
    op.verifyPlainOpCounts ctx opIn 2 0
    let operandType ← op.verifyOperandTypesMatch ctx 0 1
      "constrain.eq: expected operands to have the same type"
    if !operandType.val.isSupportedLLZKConstrainEqType then
      throw s!"constrain.eq: unsupported operand type {operandType}"
  | .«in» => do
    op.verifyPlainOpCounts ctx opIn 2 0
    let lhsType := (op.getOperand! ctx.raw 0).getType! ctx.raw
    let rhsType := (op.getOperand! ctx.raw 1).getType! ctx.raw
    let .arrayType arrayType := lhsType.val
      | throw s!"constrain.in: expected first operand to have array type, got {lhsType}"
    if !arrayType.elementType.isSupportedLLZKConstrainEqType then
      throw s!"constrain.in: unsupported array element type {arrayType.elementType}"
    if !isLLZKSubArrayOrElementType arrayType rhsType.val then
      throw s!"constrain.in: {rhsType} is not an element or compatible subarray of {lhsType}"

instance : HasOpInfo LLZK.Constrain where
  verifyLocalInvariants := LLZK.Constrain.verifyLocalInvariants
  getEffects := LLZK.Constrain.getEffects
  isConstantLike := LLZK.Constrain.isConstantLike
  hasSSADominance := LLZK.Constrain.hasSSADominance

end

end Veir
