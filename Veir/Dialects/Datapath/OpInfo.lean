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

instance : HasDialectOpInfo Datapath where
  propertiesOf := Datapath.propertiesOf

end

end Veir
