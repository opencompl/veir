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

def Riscv_Stack.hasSideEffects
    (_op : Riscv_Stack) (_props : Riscv_Stack.propertiesOf _op) : Bool :=
  true

def Riscv_Stack.readsMemory (_op : Riscv_Stack) : Bool :=
  false

instance : HasDialectOpInfo Riscv_Stack where
  propertiesOf := Riscv_Stack.propertiesOf
  hasSideEffects := Riscv_Stack.hasSideEffects
  readsMemory := Riscv_Stack.readsMemory

end

end Veir
