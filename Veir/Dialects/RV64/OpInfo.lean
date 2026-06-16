module

public import Veir.IR.OpInfo
public import Veir.Properties

namespace Veir

public section

@[expose, properties_of]
def Rv64.propertiesOf (op : Rv64) : Type :=
match op with
| _ => Unit

instance : HasDialectOpInfo Rv64 where
  propertiesOf := Rv64.propertiesOf

end

end Veir
