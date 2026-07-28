module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.Func.Properties
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive Func where
| func
| call
| return
deriving Inhabited, Repr, Hashable, DecidableEq

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
