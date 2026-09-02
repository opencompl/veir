module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Include.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Include_ where
| from
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Include_.propertiesOf (op : Include_) : Type :=
match op with
| .from => IncludeFromProperties

def Include_.fromAttrDict
    (op : Include_) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Include_.propertiesOf op) := by
  cases op
  exact IncludeFromProperties.fromAttrDict attrDict

def Include_.toAttrDict
    (op : Include_) (props : Include_.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .from =>
    ((Std.HashMap.emptyWithCapacity 2).insert
      "sym_name".toUTF8 (Attribute.stringAttr props.sym_name)).insert
      "path".toUTF8 (Attribute.stringAttr props.path)

@[get_effects]
def Include_.getEffects
    (_op : Include_) (_props : Include_.propertiesOf _op) : MemoryEffects :=
  .unknown

def Include_.isConstantLike (_op : Include_) : Bool := false

def Include_.hasSSADominance (_op : Include_) (_index : Nat) : Bool := true

#generate_dialect Include_

instance : IsOpCode Include_ where
  fromName := Include_.fromName
  name := Include_.name
  propertiesOf := Include_.propertiesOf
  fromAttrDict := Include_.fromAttrDict
  toAttrDict := Include_.toAttrDict

def Include_.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Include_] (opType : Include_) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .from => op.verifyPlainOpCounts ctx opIn 0 0

instance : HasOpInfo Include_ where
  verifyLocalInvariants := Include_.verifyLocalInvariants
  getEffects := Include_.getEffects
  isConstantLike := Include_.isConstantLike
  hasSSADominance := Include_.hasSSADominance

end

end Veir
