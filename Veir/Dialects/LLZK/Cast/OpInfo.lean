module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Cast where
| tofelt
| toindex
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Cast.propertiesOf (_op : Cast) : Type := Unit

def Cast.fromAttrDict
    (_op : Cast) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Cast.propertiesOf _op) := .ok ()

def Cast.toAttrDict
    (_op : Cast) (_props : Cast.propertiesOf _op) : Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

def Cast.getEffects (_op : Cast) (_props : Cast.propertiesOf _op) : MemoryEffects :=
  .none

def Cast.isConstantLike (_op : Cast) : Bool := false

def Cast.hasSSADominance (_op : Cast) (_index : Nat) : Bool := true

#generate_dialect Cast

instance : IsOpCode Cast where
  fromName := Cast.fromName
  name := Cast.name
  propertiesOf := Cast.propertiesOf
  fromAttrDict := Cast.fromAttrDict
  toAttrDict := Cast.toAttrDict

def Cast.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Cast] (opType : Cast) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .tofelt | .toindex => op.verifyPlainOpCounts ctx opIn 1 1

instance : HasOpInfo Cast where
  verifyLocalInvariants := Cast.verifyLocalInvariants
  getEffects := Cast.getEffects
  isConstantLike := Cast.isConstantLike
  hasSSADominance := Cast.hasSSADominance

end

end Veir
