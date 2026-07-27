module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties

namespace Veir

public section

@[expose, properties_of]
def Datapath.propertiesOf (_op : Datapath) : Type :=
  Unit

instance : HasDialectOpInfo Datapath where
  propertiesOf := Datapath.propertiesOf

end

end Veir
