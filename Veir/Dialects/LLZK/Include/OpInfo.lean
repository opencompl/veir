module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLZK.Include.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

namespace LLZK

@[opcodes]
inductive Include where
| from
deriving Inhabited, Repr, Hashable, DecidableEq

end LLZK

@[expose, properties_of]
def LLZK.Include.propertiesOf (op : LLZK.Include) : Type :=
match op with
| .from => IncludeFromProperties

def LLZK.Include.fromAttrDict
    (op : LLZK.Include) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (LLZK.Include.propertiesOf op) :=
  match op with
  | .from => IncludeFromProperties.fromAttrDict attrDict

def LLZK.Include.toAttrDict
    (op : LLZK.Include) (props : LLZK.Include.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .from =>
    ((Std.HashMap.emptyWithCapacity 2).insert
      "sym_name".toUTF8 (Attribute.stringAttr props.sym_name)).insert
      "path".toUTF8 (Attribute.stringAttr props.path)

@[get_effects]
def LLZK.Include.getEffects
    (_op : LLZK.Include) (_props : LLZK.Include.propertiesOf _op) : MemoryEffects :=
  .unknown

def LLZK.Include.isConstantLike (_op : LLZK.Include) : Bool := false

def LLZK.Include.hasSSADominance (_op : LLZK.Include) (_index : Nat) : Bool := true

#generate_dialect LLZK.Include

instance : IsOpCode LLZK.Include where
  fromName := LLZK.Include.fromName
  name := LLZK.Include.name
  propertiesOf := LLZK.Include.propertiesOf
  fromAttrDict := LLZK.Include.fromAttrDict
  toAttrDict := LLZK.Include.toAttrDict

def LLZK.Include.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.Include] (opType : LLZK.Include) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .from => do
    op.verifyPlainOpCounts ctx opIn 0 0
    match op.getParentOp! ctx.raw with
    | some parent =>
      if IsOpCode.name (parent.getOpType! ctx.raw) ≠ "builtin.module".toUTF8 then
        throw "include.from: Expected the parent operation to be a builtin.module"
    | none => throw "include.from: Expected the parent operation to be a builtin.module"

instance : HasOpInfo LLZK.Include where
  verifyLocalInvariants := LLZK.Include.verifyLocalInvariants
  getEffects := LLZK.Include.getEffects
  isConstantLike := LLZK.Include.isConstantLike
  hasSSADominance := LLZK.Include.hasSSADominance

end

end Veir
