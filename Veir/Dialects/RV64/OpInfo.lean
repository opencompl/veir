module

public import Veir.IR.OpInfo
public import Veir.IR.Simp
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Rv64 where
| get_register
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Rv64.propertiesOf (op : Rv64) : Type :=
match op with
| _ => Unit

def Rv64.fromAttrDict
    (op : Rv64) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Rv64.propertiesOf op) := by
  cases op
  exact .ok ()

def Rv64.toAttrDict
    (_op : Rv64) (_props : Rv64.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

def Rv64.getEffects
    (_op : Rv64) (_props : Rv64.propertiesOf _op) : MemoryEffects :=
  .none

def Rv64.isConstantLike (_op : Rv64) : Bool :=
  false

def Rv64.hasSSADominance (_op : Rv64) (_index : Nat) : Bool :=
  true

#generate_dialect Rv64

instance : IsOpCode Rv64 where
  fromName := Rv64.fromName
  name := Rv64.name
  propertiesOf := Rv64.propertiesOf
  fromAttrDict := Rv64.fromAttrDict
  toAttrDict := Rv64.toAttrDict

/--
Verify the local invariants of an `rv64` operation in any operation-info type
containing the `rv64` dialect.
-/
def Rv64.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Rv64] (opType : Rv64) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .get_register => do
    op.verifyPlainOpCounts ctx opIn 0 1
    pure ()

instance : HasOpInfo Rv64 where
  verifyLocalInvariants := Rv64.verifyLocalInvariants
  getEffects := Rv64.getEffects
  isConstantLike := Rv64.isConstantLike
  hasSSADominance := Rv64.hasSSADominance

end

end Veir
