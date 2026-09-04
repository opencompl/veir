module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

namespace LLZK

@[opcodes]
inductive Ram where
| load
| store
deriving Inhabited, Repr, Hashable, DecidableEq

end LLZK

@[expose, properties_of]
def LLZK.Ram.propertiesOf (_op : LLZK.Ram) : Type := Unit

/-- Reject properties on a RAM operation. -/
private def noProperties (opName : String) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String Unit :=
  if attrDict.size > 0 then
    let plural := if attrDict.size = 1 then "property" else "properties"
    .error s!"{opName}: expected no properties, but got {attrDict.size} {plural}"
  else
    .ok ()

def LLZK.Ram.fromAttrDict
    (op : LLZK.Ram) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (LLZK.Ram.propertiesOf op) :=
  match op with
  | .load => noProperties "ram.load" attrDict
  | .store => noProperties "ram.store" attrDict

def LLZK.Ram.toAttrDict
    (_op : LLZK.Ram) (_props : LLZK.Ram.propertiesOf _op) : Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

def LLZK.Ram.getEffects (op : LLZK.Ram) (_props : LLZK.Ram.propertiesOf op) : MemoryEffects :=
  match op with
  | .load => .read
  | .store => .write

def LLZK.Ram.isConstantLike (_op : LLZK.Ram) : Bool := false

def LLZK.Ram.hasSSADominance (_op : LLZK.Ram) (_index : Nat) : Bool := true

#generate_dialect LLZK.Ram

instance : IsOpCode LLZK.Ram where
  fromName := LLZK.Ram.fromName
  name := LLZK.Ram.name
  propertiesOf := LLZK.Ram.propertiesOf
  fromAttrDict := LLZK.Ram.fromAttrDict
  toAttrDict := LLZK.Ram.toAttrDict

def LLZK.Ram.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.Ram] (opType : LLZK.Ram) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .load => do
    op.verifyPlainOpCounts ctx opIn 1 1
    let addressType := (op.getOperandTypes! ctx.raw)[0]!
    if !(addressType.val matches Attribute.indexType _) then
      throw "ram.load: Expected address operand to have index type"
    let resultType := (op.getResultTypes! ctx.raw)[0]!
    if !(resultType.val matches Attribute.feltType _) then
      throw "ram.load: Expected result to have FeltType"
  | .store => do
    op.verifyPlainOpCounts ctx opIn 2 0
    let addressType := (op.getOperandTypes! ctx.raw)[0]!
    if !(addressType.val matches Attribute.indexType _) then
      throw "ram.store: Expected address operand to have index type"
    let valueType := (op.getOperandTypes! ctx.raw)[1]!
    if !(valueType.val matches Attribute.feltType _) then
      throw "ram.store: Expected value operand to have FeltType"

instance : HasOpInfo LLZK.Ram where
  verifyLocalInvariants := LLZK.Ram.verifyLocalInvariants
  getEffects := LLZK.Ram.getEffects
  isConstantLike := LLZK.Ram.isConstantLike
  hasSSADominance := LLZK.Ram.hasSSADominance

end

end Veir
