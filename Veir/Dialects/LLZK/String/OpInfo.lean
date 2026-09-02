module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.String.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive String_ where
| new
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def String_.propertiesOf (op : String_) : Type :=
match op with
| .new => StringNewProperties

def String_.fromAttrDict
    (op : String_) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (String_.propertiesOf op) := by
  cases op
  exact StringNewProperties.fromAttrDict attrDict

def String_.toAttrDict
    (op : String_) (props : String_.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .new =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "value".toUTF8 (Attribute.stringAttr props.value)

@[get_effects]
def String_.getEffects
    (_op : String_) (_props : String_.propertiesOf _op) : MemoryEffects :=
  .none

def String_.isConstantLike (_op : String_) : Bool := true

def String_.hasSSADominance (_op : String_) (_index : Nat) : Bool := true

#generate_dialect String_

instance : IsOpCode String_ where
  fromName := String_.fromName
  name := String_.name
  propertiesOf := String_.propertiesOf
  fromAttrDict := String_.fromAttrDict
  toAttrDict := String_.toAttrDict

def String_.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo String_] (opType : String_) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .new => op.verifyPlainOpCounts ctx opIn 0 1

instance : HasOpInfo String_ where
  verifyLocalInvariants := String_.verifyLocalInvariants
  getEffects := String_.getEffects
  isConstantLike := String_.isConstantLike
  hasSSADominance := String_.hasSSADominance

end

end Veir
