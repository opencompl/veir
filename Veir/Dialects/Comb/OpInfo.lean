module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties

namespace Veir

public section

@[expose, properties_of]
def Comb.propertiesOf (op : Comb) : Type :=
match op with
| .extract => CombExtractProperties
| .icmp => CombIcmpProperties
| _ => Unit

instance : HasDialectOpInfo Comb where
  propertiesOf := Comb.propertiesOf

end

end Veir
