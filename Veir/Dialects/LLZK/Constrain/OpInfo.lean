module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

namespace LLZK

@[opcodes]
inductive Constrain where
| eq
/-- `constrain.in %arr, %tuple` — lookup-containment constraint. -/
| «in»
deriving Inhabited, Repr, Hashable, DecidableEq

end LLZK

@[expose, properties_of]
def LLZK.Constrain.propertiesOf (_op : LLZK.Constrain) : Type := Unit

def LLZK.Constrain.fromAttrDict
    (_op : LLZK.Constrain) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (LLZK.Constrain.propertiesOf _op) := .ok ()

def LLZK.Constrain.toAttrDict
    (_op : LLZK.Constrain) (_props : LLZK.Constrain.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

/--
`constrain.eq` and `constrain.in` emit constraints into the circuit. They
have no results, so they must report an effect or DCE would erase the
constraint system.
-/
def LLZK.Constrain.getEffects
    (_op : LLZK.Constrain) (_props : LLZK.Constrain.propertiesOf _op) : MemoryEffects :=
  .write

def LLZK.Constrain.isConstantLike (_op : LLZK.Constrain) : Bool := false

def LLZK.Constrain.hasSSADominance (_op : LLZK.Constrain) (_index : Nat) : Bool := true

#generate_dialect LLZK.Constrain

instance : IsOpCode LLZK.Constrain where
  fromName := LLZK.Constrain.fromName
  name := LLZK.Constrain.name
  propertiesOf := LLZK.Constrain.propertiesOf
  fromAttrDict := LLZK.Constrain.fromAttrDict
  toAttrDict := LLZK.Constrain.toAttrDict

def LLZK.Constrain.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo LLZK.Constrain] (opType : LLZK.Constrain) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .eq => op.verifyPlainOpCounts ctx opIn 2 0
  | .«in» => op.verifyPlainOpCounts ctx opIn 2 0

instance : HasOpInfo LLZK.Constrain where
  verifyLocalInvariants := LLZK.Constrain.verifyLocalInvariants
  getEffects := LLZK.Constrain.getEffects
  isConstantLike := LLZK.Constrain.isConstantLike
  hasSSADominance := LLZK.Constrain.hasSSADominance

end

end Veir
