module

public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Interpreter.RuntimeValue.Tensor
public import Veir.Interpreter.Interp
public import Veir.Dialects.Tensor.Properties
public import Veir.Data.Tensor
meta import Veir.Meta.OpCode

namespace Veir

public section

open Veir.Data.Tensor (fitsSlice staticIndices?)

@[opcodes]
inductive Tensor where
| empty
| extract
| insert
| extract_slice
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, implicit_reducible, properties_of]
def Tensor.propertiesOf (op : Tensor) : Type :=
  match op with
  | .extract_slice => ExtractSliceProperties
  | _ => Unit

def Tensor.fromAttrDict
    (op : Tensor) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Tensor.propertiesOf op) := by
  cases op
  case extract_slice => exact ExtractSliceProperties.fromAttrDict attrDict
  all_goals exact expectNoProperties "tensor" attrDict

def Tensor.toAttrDict
    (op : Tensor) (props : Tensor.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .extract_slice => ExtractSliceProperties.toAttrDict props
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Tensor.getEffects
    (_op : Tensor) (_props : Tensor.propertiesOf _op) : MemoryEffects :=
  .none

def Tensor.isConstantLike (_op : Tensor) : Bool :=
  false

def Tensor.hasSSADominance (_op : Tensor) (_index : Nat) : Bool :=
  true

@[is_terminator]
def Tensor.isTerminator (_op : Tensor) : Bool :=
  false

#generate_dialect Tensor

instance : IsOpCode Tensor where
  fromName := Tensor.fromName
  name := Tensor.name
  propertiesOf := Tensor.propertiesOf
  fromAttrDict := Tensor.fromAttrDict
  toAttrDict := Tensor.toAttrDict

/-- Decode a length-`rank` dense array, rejecting negatives (MLIR dynamic sentinels). -/
private def decodeStaticNats (attr : DenseArrayAttr) (rank : Nat)
    (name instrName : String) : Except String (List Nat) := do
  if attr.values.size ≠ rank then
    throw s!"{instrName}: expected {rank} {name}, got {attr.values.size}"
  let mut out : List Nat := []
  for v in attr.values.toList do
    if v < 0 then
      throw s!"{instrName}: {name} entry {v} is negative (dynamic values are not supported)"
    out := out ++ [v.toNat]
  return out

def Tensor.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Tensor] (opType : Tensor) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (Tensor.name opType)
  let operandType (i : Nat) := (op.getOperand! ctx.raw i).getType! ctx.raw
  let resultType (i : Nat) := (op.getResult i).getType! ctx.raw
  let numOperands := op.getNumOperands ctx.raw opIn
  match opType with
  | .empty => do
    -- Tensor types are always statically shaped, so there are no dynamic size operands.
    op.verifyPlainOpCounts ctx opIn 0 1
    let _ ← (resultType 0).verifyTensorType s!"{instrName}: Expected result to be a tensor"
  | .extract => do
    if numOperands = 0 then
      throw s!"{instrName}: Expected a tensor operand"
    let source ← (operandType 0).verifyTensorType s!"{instrName}: Expected operand 0 to be a tensor"
    op.verifyPlainOpCounts ctx opIn (1 + source.shape.size) 1
    op.verifyIndexOperands ctx 1 source.shape.size instrName
    if (resultType 0).val ≠ source.elementType then
      throw s!"{instrName}: Expected result type to match the tensor element type"
  | .insert => do
    if numOperands < 2 then
      throw s!"{instrName}: Expected a scalar and a destination operand"
    let dest ← (operandType 1).verifyTensorType s!"{instrName}: Expected operand 1 to be a tensor"
    op.verifyPlainOpCounts ctx opIn (2 + dest.shape.size) 1
    op.verifyIndexOperands ctx 2 dest.shape.size instrName
    if (operandType 0).val ≠ dest.elementType then
      throw s!"{instrName}: Expected scalar type to match the tensor element type"
    op.verifyResultTypeMatches ctx (operandType 1)
      s!"{instrName}: Expected result type to match the destination type"
  | .extract_slice => do
    -- Static-only: one SSA source, no dynamics, no rank reduction.
    op.verifyPlainOpCounts ctx opIn 1 1
    let source ← (operandType 0).verifyTensorType s!"{instrName}: Expected operand 0 to be a tensor"
    let result ← (resultType 0).verifyTensorType s!"{instrName}: Expected result to be a tensor"
    let props : Tensor.propertiesOf .extract_slice :=
      HasDialect.toDialectProperties (OpInfo := OpInfo) Tensor.extract_slice
        (op.getProperties! ctx.raw (ofDialect OpInfo Tensor.extract_slice))
    let _ ← op.verifyOperandSegmentSizes ctx opIn props.operandSegmentSizes 4
    let rank := source.shape.size
    let offsets ← decodeStaticNats props.static_offsets rank "static_offsets" instrName
    let sizes ← decodeStaticNats props.static_sizes rank "static_sizes" instrName
    let strides ← decodeStaticNats props.static_strides rank "static_strides" instrName
    let expectedSizes := result.shape.toList.map (Int.ofNat ·)
    if props.static_sizes.values.toList ≠ expectedSizes then
      throw s!"{instrName}: static_sizes must equal the result shape \
        (rank-reducing and dynamic sizes are not supported)"
    if result.elementType ≠ source.elementType then
      throw s!"{instrName}: Expected result element type to match the source element type"
    if fitsSlice source.shape.toList offsets sizes strides ≠ true then
      throw s!"{instrName}: slice window does not fit inside the source shape"

/-- `empty` fills with element poison; `extract_slice` is static-only. -/
def Tensor.interpretOp' (opType : Veir.Tensor) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (_blockOperands : Array BlockPtr) :
    Interp (Array RuntimeValue × Option ControlFlowAction) :=
  match opType with
  | .empty => do
    let ⟨.tensorType ty, _⟩ ← resultTypes[0]? | none
    if h : ty.elementType.isType then
      let elemPoison ← RuntimeValue.getPoisonForType ⟨ty.elementType, h⟩
      return (#[RuntimeValue.emptyTensor ty.shape elemPoison], none)
    else none
  | .extract | .insert => none
  | .extract_slice =>
    match operands[0]? with
    | none => none
    | some tensor =>
      match resultTypes[0]? with
      | none => none
      | some resultType =>
        match resultType.cast? TensorType with
        | none => none
        | some resultTy =>
          match staticIndices? properties.static_offsets.values.toList,
                staticIndices? properties.static_sizes.values.toList,
                staticIndices? properties.static_strides.values.toList with
          | some offsets, some sizes, some strides =>
            match RuntimeValue.tensorExtractSlice tensor offsets sizes strides
                resultTy.shape with
            | none => none
            | some result => pure (#[result], none)
          | _, _, _ => none

instance : HasOpInfo Tensor where
  verifyLocalInvariants := Tensor.verifyLocalInvariants
  getEffects := Tensor.getEffects
  isConstantLike := Tensor.isConstantLike
  hasSSADominance := Tensor.hasSSADominance
  isTerminator := Tensor.isTerminator

end
