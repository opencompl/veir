module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties

namespace Veir

public section

@[expose, properties_of]
def Arith.propertiesOf (op : Arith) : Type :=
match op with
-- TODO: Temporarily removed this as properties aren't supported in buffed yet, so we encode properties
-- with attributes
-- | .constant => ArithConstantProperties
-- | .addi => NswNuwProperties
| .subi => NswNuwProperties
-- | .muli => NswNuwProperties
| .divsi => ExactProperties
| .divui => ExactProperties
| .cmpi => IcmpProperties
| .shli => NswNuwProperties
| .shrsi => ExactProperties
| .shrui => ExactProperties
| .ori => DisjointProperties
| .trunci => NswNuwProperties
| .extui => NnegProperties
| _ => Unit

instance : HasDialectOpInfo Arith where
  propertiesOf := Arith.propertiesOf

end

end Veir
