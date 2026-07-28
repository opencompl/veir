module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.Cf.Properties
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive Cf where
| br
| cond_br
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Cf.propertiesOf (op : Cf) : Type :=
match op with
| .cond_br => CondBrProperties
| _ => Unit

instance : HasDialectOpInfo Cf where
  propertiesOf := Cf.propertiesOf

end

end Veir
