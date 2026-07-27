module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties

namespace Veir

public section

@[expose, properties_of]
def Builtin.propertiesOf (op : Builtin) : Type :=
match op with
| .unregistered => UnregisteredProperties
| _ => Unit

instance : HasDialectOpInfo Builtin where
  propertiesOf := Builtin.propertiesOf

end

end Veir
