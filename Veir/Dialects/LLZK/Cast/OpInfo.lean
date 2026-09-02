module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
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
def LLZK.Cast.propertiesOf (_op : LLZK.Cast) : Type := Unit

def LLZK.Cast.fromAttrDict
    (_op : LLZK.Cast) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (LLZK.Cast.propertiesOf _op) := .ok ()

def LLZK.Cast.toAttrDict
    (_op : LLZK.Cast) (_props : LLZK.Cast.propertiesOf _op) : Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

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
  | .tofelt | .toindex => op.verifyPlainOpCounts ctx opIn 1 1

instance : HasOpInfo LLZK.Cast where
  verifyLocalInvariants := LLZK.Cast.verifyLocalInvariants
  getEffects := LLZK.Cast.getEffects
  isConstantLike := LLZK.Cast.isConstantLike
  hasSSADominance := LLZK.Cast.hasSSADominance

end

end Veir
