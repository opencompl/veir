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

def LLZK.Ram.fromAttrDict
    (_op : LLZK.Ram) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (LLZK.Ram.propertiesOf _op) := .ok ()

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
  | .load => op.verifyPlainOpCounts ctx opIn 1 1
  | .store => op.verifyPlainOpCounts ctx opIn 2 0

instance : HasOpInfo LLZK.Ram where
  verifyLocalInvariants := LLZK.Ram.verifyLocalInvariants
  getEffects := LLZK.Ram.getEffects
  isConstantLike := LLZK.Ram.isConstantLike
  hasSSADominance := LLZK.Ram.hasSSADominance

end

end Veir
