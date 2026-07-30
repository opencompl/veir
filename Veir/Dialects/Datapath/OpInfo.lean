module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive Datapath where
| compress
| partial_product
| pos_partial_product
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Datapath.propertiesOf (_op : Datapath) : Type :=
  Unit

def Datapath.fromAttrDict
    (_op : Datapath) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Datapath.propertiesOf _op) :=
  .ok ()

def Datapath.toAttrDict
    (_op : Datapath) (_props : Datapath.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

def Datapath.hasSideEffects
    (_op : Datapath) (_props : Datapath.propertiesOf _op) : Bool :=
  false

def Datapath.readsMemory (_op : Datapath) : Bool :=
  false

def Datapath.isConstantLike (_op : Datapath) : Bool :=
  false

def Datapath.hasSSADominance (_op : Datapath) (_index : Nat) : Bool :=
  true

#generate_dialect Datapath

instance : HasDialectOpInfo Datapath where
  fromName := Datapath.fromName
  name := Datapath.name
  propertiesOf := Datapath.propertiesOf
  fromAttrDict := Datapath.fromAttrDict
  toAttrDict := Datapath.toAttrDict
  hasSideEffects := Datapath.hasSideEffects
  readsMemory := Datapath.readsMemory
  isConstantLike := Datapath.isConstantLike
  hasSSADominance := Datapath.hasSSADominance

end

end Veir
