module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.Builtin.Properties
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive Builtin where
| unregistered
| module
| unrealized_conversion_cast
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Builtin.propertiesOf (op : Builtin) : Type :=
match op with
| .unregistered => UnregisteredProperties
| _ => Unit

instance : HasDialectOpInfo Builtin where
  propertiesOf := Builtin.propertiesOf

end

end Veir
