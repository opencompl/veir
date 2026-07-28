module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.OpCode

namespace Veir

public section

@[expose, properties_of]
def Test.propertiesOf (_op : Test) : Type :=
  Unit

instance : HasDialectOpInfo Test where
  propertiesOf := Test.propertiesOf

end

end Veir
