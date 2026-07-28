module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.ModArith.Properties
meta import Veir.Meta.Attrs

namespace Veir

public section

@[opcodes]
inductive Mod_Arith where
| add
| constant
| mul
| sub
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Mod_Arith.propertiesOf (op : Mod_Arith) : Type :=
match op with
| .constant => ModArithConstantProperties
| .add | .sub | .mul => Unit

def Mod_Arith.hasSideEffects
    (_op : Mod_Arith) (_props : Mod_Arith.propertiesOf _op) : Bool :=
  false

instance : HasDialectOpInfo Mod_Arith where
  propertiesOf := Mod_Arith.propertiesOf
  hasSideEffects := Mod_Arith.hasSideEffects
