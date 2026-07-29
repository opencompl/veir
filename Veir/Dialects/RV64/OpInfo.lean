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

def Rv64.hasSideEffects (_op : Rv64) (_props : Rv64.propertiesOf _op) : Bool :=
  true

def Rv64.readsMemory (_op : Rv64) : Bool :=
  false

instance : HasDialectOpInfo Rv64 where
  propertiesOf := Rv64.propertiesOf
  hasSideEffects := Rv64.hasSideEffects
  readsMemory := Rv64.readsMemory

end

end Veir
