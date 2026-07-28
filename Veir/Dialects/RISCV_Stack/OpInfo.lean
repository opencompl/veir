module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.RISCV_Stack.Properties
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive Riscv_Stack where
| alloca
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Riscv_Stack.propertiesOf (op : Riscv_Stack) : Type :=
match op with
| .alloca => RISCVStackAllocaProperties

instance : HasDialectOpInfo Riscv_Stack where
  propertiesOf := Riscv_Stack.propertiesOf

end

end Veir
