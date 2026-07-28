module

public import Veir.IR.OpInfo
public import Veir.IR.Simp
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive Rv64 where
| get_register
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Rv64.propertiesOf (op : Rv64) : Type :=
match op with
| _ => Unit

instance : HasDialectOpInfo Rv64 where
  propertiesOf := Rv64.propertiesOf

end

end Veir
