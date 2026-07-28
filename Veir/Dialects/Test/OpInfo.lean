module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive Test where
| test
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Test.propertiesOf (_op : Test) : Type :=
  Unit

instance : HasDialectOpInfo Test where
  propertiesOf := Test.propertiesOf

end

end Veir
