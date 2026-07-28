module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.OpCode
public import Veir.Dialects.Func.Properties

namespace Veir

public section

@[expose, properties_of]
def Func.propertiesOf (op : Func) : Type :=
match op with
| .func => FuncFuncProperties
| .call => FuncCallProperties
| _ => Unit

instance : HasDialectOpInfo Func where
  propertiesOf := Func.propertiesOf

end

end Veir
