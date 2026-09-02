module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Constrain where
| eq
/-- `constrain.in %arr, %tuple` — lookup-containment constraint. -/
| «in»
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Constrain.propertiesOf (_op : Constrain) : Type := Unit

def Constrain.fromAttrDict
    (_op : Constrain) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Constrain.propertiesOf _op) := .ok ()

def Constrain.toAttrDict
    (_op : Constrain) (_props : Constrain.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

/--
`constrain.eq` and `constrain.in` emit constraints into the circuit. They
have no results, so they must report an effect or DCE would erase the
constraint system.
-/
def Constrain.getEffects
    (_op : Constrain) (_props : Constrain.propertiesOf _op) : MemoryEffects :=
  .write

def Constrain.isConstantLike (_op : Constrain) : Bool := false

def Constrain.hasSSADominance (_op : Constrain) (_index : Nat) : Bool := true

#generate_dialect Constrain

instance : IsOpCode Constrain where
  fromName := Constrain.fromName
  name := Constrain.name
  propertiesOf := Constrain.propertiesOf
  fromAttrDict := Constrain.fromAttrDict
  toAttrDict := Constrain.toAttrDict

def Constrain.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Constrain] (opType : Constrain) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .eq => op.verifyPlainOpCounts ctx opIn 2 0
  | .«in» => op.verifyPlainOpCounts ctx opIn 2 0

instance : HasOpInfo Constrain where
  verifyLocalInvariants := Constrain.verifyLocalInvariants
  getEffects := Constrain.getEffects
  isConstantLike := Constrain.isConstantLike
  hasSSADominance := Constrain.hasSSADominance

end

end Veir
