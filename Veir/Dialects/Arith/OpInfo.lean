module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Properties

namespace Veir

public section

@[expose, properties_of]
def Arith.propertiesOf (op : Arith) : Type :=
match op with
-- TODO: Temporarily removed this as properties aren't supported in buffed yet, so we encode properties with attributes
| .subi => NswNuwProperties
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

def Arith.propertySize (op : Arith) : UInt64 :=
match op with
-- TODO: Temporarily removed this as properties aren't supported in buffed yet, so we encode properties with attributes
| .subi => 1
| .divsi => 1
| .divui => 1
| .cmpi => 1
| .shli => 1
| .shrsi => 1
| .shrui => 1
| .ori => 1
| .trunci => 1
| .extui => 1
| _ => 0

instance : HasDialectOpInfo Arith where
  propertiesOf := Arith.propertiesOf
  propertySize op := op.propertySize
  propertySize_small {op} := by cases op <;> simp [Arith.propertySize]

end

end Veir
