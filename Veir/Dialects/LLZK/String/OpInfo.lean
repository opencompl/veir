module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.String.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

namespace LLZK

@[opcodes]
inductive String where
| new
deriving Inhabited, Repr, Hashable, DecidableEq

end LLZK

@[expose, properties_of]
def LLZK.String.propertiesOf (op : LLZK.String) : Type :=
match op with
| .new => StringNewProperties

def LLZK.String.fromAttrDict
    (op : LLZK.String) (attrDict : Std.HashMap ByteArray Attribute) :=
  match op with
  | .new => StringNewProperties.fromAttrDict attrDict

def LLZK.String.toAttrDict
    (op : LLZK.String) (props : LLZK.String.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .new =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "value".toUTF8 (Attribute.stringAttr props.value)

@[get_effects]
def LLZK.String.getEffects
    (_op : LLZK.String) (_props : LLZK.String.propertiesOf _op) : MemoryEffects :=
  .none

def LLZK.String.isConstantLike (_op : LLZK.String) : Bool := true

def LLZK.String.hasSSADominance (_op : LLZK.String) (_index : Nat) : Bool := true

#generate_dialect LLZK.String

instance : IsOpCode LLZK.String where
  fromName := LLZK.String.fromName
  name := LLZK.String.name
  propertiesOf := LLZK.String.propertiesOf
  fromAttrDict := LLZK.String.fromAttrDict
  toAttrDict := LLZK.String.toAttrDict

def LLZK.String.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.String] (opType : LLZK.String) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) := do
  match opType with
  | .new => op.verifyPlainOpCounts ctx opIn 0 1

instance : HasOpInfo LLZK.String where
  verifyLocalInvariants := LLZK.String.verifyLocalInvariants
  getEffects := LLZK.String.getEffects
  isConstantLike := LLZK.String.isConstantLike
  hasSSADominance := LLZK.String.hasSSADominance

end

end Veir
