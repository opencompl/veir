module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.HW.Properties
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive HW where
| constant
| module
| output
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def HW.propertiesOf (op : HW) : Type :=
match op with
| .constant => HWConstantProperties
| .module => HWModuleProperties
| _ => Unit

def HW.hasSideEffects (op : HW) (_props : HW.propertiesOf op) : Bool :=
  match op with
  | .constant => false
  | _ => true

def HW.readsMemory (_op : HW) : Bool :=
  false

instance : HasDialectOpInfo HW where
  propertiesOf := HW.propertiesOf
  hasSideEffects := HW.hasSideEffects
  readsMemory := HW.readsMemory

end

end Veir
