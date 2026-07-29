module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.ModArith.Properties
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive Mod_Arith where
| add
| constant
| mul
| sub
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Mod_Arith.propertiesOf (op : Mod_Arith) : Type :=
match op with
| .constant => ModArithConstantProperties
| .add | .sub | .mul => Unit

def Mod_Arith.fromAttrDict
    (op : Mod_Arith) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Mod_Arith.propertiesOf op) := by
  cases op
  case constant => exact ModArithConstantProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Mod_Arith.toAttrDict
    (op : Mod_Arith) (props : Mod_Arith.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .constant =>
    (Std.HashMap.emptyWithCapacity 2).insert
      "value".toUTF8 (Attribute.integerAttr props.value)
  | _ => Std.HashMap.emptyWithCapacity 0

def Mod_Arith.hasSideEffects
    (_op : Mod_Arith) (_props : Mod_Arith.propertiesOf _op) : Bool :=
  false

def Mod_Arith.readsMemory (_op : Mod_Arith) : Bool :=
  false

def Mod_Arith.isConstantLike (_op : Mod_Arith) : Bool :=
  false

def Mod_Arith.hasSSADominance (_op : Mod_Arith) (_index : Nat) : Bool :=
  true

instance : HasDialectOpInfo Mod_Arith where
  propertiesOf := Mod_Arith.propertiesOf
  fromAttrDict := Mod_Arith.fromAttrDict
  toAttrDict := Mod_Arith.toAttrDict
  hasSideEffects := Mod_Arith.hasSideEffects
  readsMemory := Mod_Arith.readsMemory
  isConstantLike := Mod_Arith.isConstantLike
  hasSSADominance := Mod_Arith.hasSSADominance
