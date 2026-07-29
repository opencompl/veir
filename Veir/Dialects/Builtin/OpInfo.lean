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

def Builtin.hasSideEffects (op : Builtin) (_props : Builtin.propertiesOf op) : Bool :=
  match op with
  | .unrealized_conversion_cast => false
  | _ => true

def Builtin.readsMemory (_op : Builtin) : Bool :=
  false

instance : HasDialectOpInfo Builtin where
  propertiesOf := Builtin.propertiesOf
  hasSideEffects := Builtin.hasSideEffects
  readsMemory := Builtin.readsMemory

end

end Veir
