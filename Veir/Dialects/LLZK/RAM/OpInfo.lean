module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Ram where
| load
| store
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Ram.propertiesOf (_op : Ram) : Type := Unit

def Ram.fromAttrDict
    (_op : Ram) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Ram.propertiesOf _op) := .ok ()

def Ram.toAttrDict
    (_op : Ram) (_props : Ram.propertiesOf _op) : Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

def Ram.getEffects (op : Ram) (_props : Ram.propertiesOf op) : MemoryEffects :=
  match op with
  | .load => .read
  | .store => .write

def Ram.isConstantLike (_op : Ram) : Bool := false

def Ram.hasSSADominance (_op : Ram) (_index : Nat) : Bool := true

#generate_dialect Ram

instance : IsOpCode Ram where
  fromName := Ram.fromName
  name := Ram.name
  propertiesOf := Ram.propertiesOf
  fromAttrDict := Ram.fromAttrDict
  toAttrDict := Ram.toAttrDict

def Ram.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Ram] (opType : Ram) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .load => op.verifyPlainOpCounts ctx opIn 1 1
  | .store => op.verifyPlainOpCounts ctx opIn 2 0

instance : HasOpInfo Ram where
  verifyLocalInvariants := Ram.verifyLocalInvariants
  getEffects := Ram.getEffects
  isConstantLike := Ram.isConstantLike
  hasSSADominance := Ram.hasSSADominance

end

end Veir
