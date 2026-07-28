module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.OpCode
public import Veir.Dialects.Cf.Properties

namespace Veir

public section

@[expose, properties_of]
def Cf.propertiesOf (op : Cf) : Type :=
match op with
| .cond_br => CondBrProperties
| _ => Unit

instance : HasDialectOpInfo Cf where
  propertiesOf := Cf.propertiesOf

end

end Veir
