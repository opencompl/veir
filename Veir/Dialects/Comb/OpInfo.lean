module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.Comb.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Comb where
| add
| and
| concat
| divs
| divu
| extract
| icmp
| mods
| modu
| mul
| mux
| or
| parity
| replicate
| reverse
| shl
| shrs
| shru
| sub
| xor
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Comb.propertiesOf (op : Comb) : Type :=
match op with
| .extract => CombExtractProperties
| .icmp => CombIcmpProperties
| _ => Unit

def Comb.fromAttrDict
    (op : Comb) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Comb.propertiesOf op) := by
  cases op
  case extract => exact CombExtractProperties.fromAttrDict attrDict
  case icmp => exact CombIcmpProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Comb.toAttrDict
    (op : Comb) (props : Comb.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .extract =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "lowBit".toUTF8 (Attribute.integerAttr props.lowBit)
  | .icmp =>
    (Std.HashMap.emptyWithCapacity 1).insert
      "predicate".toUTF8 (Attribute.integerAttr props.predicate)
  | _ => Std.HashMap.emptyWithCapacity 0

def Comb.hasSideEffects (_op : Comb) (_props : Comb.propertiesOf _op) : Bool :=
  false

def Comb.readsMemory (_op : Comb) (_props : Comb.propertiesOf _op) : Bool :=
  false

def Comb.writesMemory (_op : Comb) (_props : Comb.propertiesOf _op) : Bool :=
  false

def Comb.isConstantLike (_op : Comb) : Bool :=
  false

def Comb.hasSSADominance (_op : Comb) (_index : Nat) : Bool :=
  true

#generate_dialect Comb

instance : HasDialectOpInfo Comb where
  fromName := Comb.fromName
  name := Comb.name
  propertiesOf := Comb.propertiesOf
  fromAttrDict := Comb.fromAttrDict
  toAttrDict := Comb.toAttrDict
  hasSideEffects := Comb.hasSideEffects
  readsMemory := Comb.readsMemory
  writesMemory := Comb.writesMemory
  isConstantLike := Comb.isConstantLike
  hasSSADominance := Comb.hasSSADominance

end

end Veir
