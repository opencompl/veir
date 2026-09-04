module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Cast.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

namespace LLZK

@[opcodes]
inductive Cast where
| tofelt
| toindex
deriving Inhabited, Repr, Hashable, DecidableEq

end LLZK

@[expose, properties_of]
def LLZK.Cast.propertiesOf (_op : LLZK.Cast) : Type := CastProperties

def LLZK.Cast.fromAttrDict
    (op : LLZK.Cast) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (LLZK.Cast.propertiesOf op) :=
  match op with
  | .tofelt => CastProperties.fromAttrDict "cast.tofelt" attrDict
  | .toindex => CastProperties.fromAttrDict "cast.toindex" attrDict

def LLZK.Cast.toAttrDict
    (op : LLZK.Cast) (props : LLZK.Cast.propertiesOf op) : Std.HashMap ByteArray Attribute :=
  props.toAttrDict

def LLZK.Cast.getEffects (_op : LLZK.Cast) (_props : LLZK.Cast.propertiesOf _op) : MemoryEffects :=
  .none

def LLZK.Cast.isConstantLike (_op : LLZK.Cast) : Bool := false

def LLZK.Cast.hasSSADominance (_op : LLZK.Cast) (_index : Nat) : Bool := true

#generate_dialect LLZK.Cast

instance : IsOpCode LLZK.Cast where
  fromName := LLZK.Cast.fromName
  name := LLZK.Cast.name
  propertiesOf := LLZK.Cast.propertiesOf
  fromAttrDict := LLZK.Cast.fromAttrDict
  toAttrDict := LLZK.Cast.toAttrDict

def LLZK.Cast.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.Cast] (opType : LLZK.Cast) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .tofelt => do
    op.verifyPlainOpCounts ctx opIn 1 1
    let operandType := (op.getOperandTypes! ctx.raw)[0]!
    if !(operandType.val matches Attribute.integerType { bitwidth := 1 } | Attribute.indexType _) then
      throw "cast.tofelt: Expected operand to have i1 or index type"
    let resultType := (op.getResultTypes! ctx.raw)[0]!
    if !(resultType.val matches Attribute.feltType _) then
      throw "cast.tofelt: Expected result to have FeltType"
  | .toindex => do
    op.verifyPlainOpCounts ctx opIn 1 1
    let operandType := (op.getOperandTypes! ctx.raw)[0]!
    if !(operandType.val matches Attribute.feltType _) then
      throw "cast.toindex: Expected operand to have FeltType"
    let resultType := (op.getResultTypes! ctx.raw)[0]!
    if !(resultType.val matches Attribute.indexType _) then
      throw "cast.toindex: Expected result to have index type"

instance : HasOpInfo LLZK.Cast where
  verifyLocalInvariants := LLZK.Cast.verifyLocalInvariants
  getEffects := LLZK.Cast.getEffects
  isConstantLike := LLZK.Cast.isConstantLike
  hasSSADominance := LLZK.Cast.hasSSADominance

end

end Veir
