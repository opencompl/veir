module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Test where
| test
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Test.propertiesOf (_op : Test) : Type :=
  Unit

def Test.fromAttrDict
    (_op : Test) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Test.propertiesOf _op) :=
  .ok ()

def Test.toAttrDict
    (_op : Test) (_props : Test.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Test.getEffects
    (_op : Test) (_props : Test.propertiesOf _op) : MemoryEffects :=
  .unknown

def Test.isConstantLike (_op : Test) : Bool :=
  false

def Test.getRegionKind (_op : Test) (_index : Nat) : RegionKind :=
  .Graph

def Test.hasSSADominance (_op : Test) (_index : Nat) : Bool :=
  false

def Test.hasNoTerminator (_op : Test) (_index : Nat) : Bool :=
  true

#generate_dialect Test

instance : HasOpInfo Test where
  fromName := Test.fromName
  name := Test.name
  propertiesOf := Test.propertiesOf
  fromAttrDict := Test.fromAttrDict
  toAttrDict := Test.toAttrDict
  getEffects := Test.getEffects
  isConstantLike := Test.isConstantLike
  getRegionKind := Test.getRegionKind
  hasSSADominance := Test.hasSSADominance
  hasNoTerminator := Test.hasNoTerminator

end

end Veir
