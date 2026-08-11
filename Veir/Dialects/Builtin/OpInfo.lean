module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.Builtin.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Builtin where
| unregistered
| module
| unrealized_conversion_cast
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Builtin.propertiesOf (op : Builtin) : Type :=
match op with
| .unregistered => UnregisteredProperties
| _ => Unit

def Builtin.fromAttrDict
    (op : Builtin) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Builtin.propertiesOf op) := by
  cases op
  case unregistered => exact UnregisteredProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Builtin.toAttrDict
    (op : Builtin) (props : Builtin.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .unregistered => Std.HashMap.ofList props.properties.entries.toList
  | _ => Std.HashMap.emptyWithCapacity 0

def Builtin.hasSideEffects (op : Builtin) (_props : Builtin.propertiesOf op) : Bool :=
  match op with
  | .unrealized_conversion_cast => false
  | _ => true

def Builtin.getEffects
    (op : Builtin) (_props : Builtin.propertiesOf op) : MemoryEffects :=
  match op with
  | .unrealized_conversion_cast => .none
  | _ => .readWrite

def Builtin.isConstantLike (_op : Builtin) : Bool :=
  false

def Builtin.hasSSADominance (op : Builtin) (_index : Nat) : Bool :=
  match op with
  | .module | .unregistered => false
  | _ => true

/-- A `builtin.module` body holds no terminator, and an unregistered operation
    makes no promise about its regions. -/
def Builtin.hasNoTerminator (op : Builtin) (_index : Nat) : Bool :=
  match op with
  | .module | .unregistered => true
  | _ => false

#generate_dialect Builtin

instance : HasOpInfo Builtin where
  fromName := Builtin.fromName
  name := Builtin.name
  propertiesOf := Builtin.propertiesOf
  fromAttrDict := Builtin.fromAttrDict
  toAttrDict := Builtin.toAttrDict
  hasSideEffects := Builtin.hasSideEffects
  getEffects := Builtin.getEffects
  isConstantLike := Builtin.isConstantLike
  hasSSADominance := Builtin.hasSSADominance
  hasNoTerminator := Builtin.hasNoTerminator

end

end Veir
