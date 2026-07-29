module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
meta import Veir.Meta.Attrs

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

def Datapath.hasSideEffects
    (_op : Datapath) (_props : Datapath.propertiesOf _op) : Bool :=
  false

def Datapath.readsMemory (_op : Datapath) : Bool :=
  false

def Datapath.isConstantLike (_op : Datapath) : Bool :=
  false

instance : HasDialectOpInfo Datapath where
  propertiesOf := Datapath.propertiesOf
  hasSideEffects := Datapath.hasSideEffects
  readsMemory := Datapath.readsMemory
  isConstantLike := Datapath.isConstantLike

end

end Veir
