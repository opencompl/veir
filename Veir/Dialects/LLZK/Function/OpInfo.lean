module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties
public import Veir.Dialects.LLZK.Function.Properties

namespace Veir

public section

@[expose, properties_of]
def Function_.propertiesOf (op : Function_) : Type :=
match op with
| .«def» => FunctionDefProperties
| .return => Unit

instance : HasDialectOpInfo Function_ where
  propertiesOf := Function_.propertiesOf

end

end Veir
