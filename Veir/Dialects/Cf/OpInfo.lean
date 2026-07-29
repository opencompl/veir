module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.Cf.Properties
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive Cf where
| br
| cond_br
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Cf.propertiesOf (op : Cf) : Type :=
match op with
| .cond_br => CondBrProperties
| _ => Unit

def Cf.fromAttrDict
    (op : Cf) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Cf.propertiesOf op) := by
  cases op
  case cond_br => exact CondBrProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Cf.toAttrDict
    (op : Cf) (props : Cf.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .cond_br =>
    let dict := (Std.HashMap.emptyWithCapacity 2).insert
      "branch_weights".toUTF8 (.denseArrayAttr props.branch_weights)
    dict.insert "operandSegmentSizes".toUTF8
      (Attribute.denseArrayAttr props.operandSegmentSizes)
  | _ => Std.HashMap.emptyWithCapacity 0

def Cf.hasSideEffects (_op : Cf) (_props : Cf.propertiesOf _op) : Bool :=
  true

def Cf.readsMemory (_op : Cf) : Bool :=
  false

def Cf.isConstantLike (_op : Cf) : Bool :=
  false

def Cf.hasSSADominance (_op : Cf) (_index : Nat) : Bool :=
  true

instance : HasDialectOpInfo Cf where
  propertiesOf := Cf.propertiesOf
  fromAttrDict := Cf.fromAttrDict
  toAttrDict := Cf.toAttrDict
  hasSideEffects := Cf.hasSideEffects
  readsMemory := Cf.readsMemory
  isConstantLike := Cf.isConstantLike
  hasSSADominance := Cf.hasSSADominance

end

end Veir
