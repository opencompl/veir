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

def Func.hasSideEffects (_op : Func) (_props : Func.propertiesOf _op) : Bool :=
  true

def Func.readsMemory (_op : Func) : Bool :=
  false

def Func.isConstantLike (_op : Func) : Bool :=
  false

instance : HasDialectOpInfo Func where
  propertiesOf := Func.propertiesOf
  hasSideEffects := Func.hasSideEffects
  readsMemory := Func.readsMemory
  isConstantLike := Func.isConstantLike

end

end Veir
