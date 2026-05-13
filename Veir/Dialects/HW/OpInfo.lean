module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties

namespace Veir

public section

@[expose, properties_of]
def HW.propertiesOf (op : HW) : Type :=
match op with
| .module => HWModuleProperties
| _ => Unit

instance : HasDialectOpInfo HW where
  propertiesOf := HW.propertiesOf

end

end Veir
