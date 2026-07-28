module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.OpCode
public import Veir.Dialects.ModArith.Properties

namespace Veir

public section

@[expose, properties_of]
def Mod_Arith.propertiesOf (op : Mod_Arith) : Type :=
match op with
| .constant => ModArithConstantProperties
| .add | .sub | .mul => Unit

instance : HasDialectOpInfo Mod_Arith where
  propertiesOf := Mod_Arith.propertiesOf
