module

public import Veir.IR.OpInfo
public import Veir.Dialects.RV64.OpInfo
import all Veir.Dialects.RV64.OpInfo
public import Veir.IR.Simp
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode
import all Veir.IR.Attribute

namespace Veir

public section


/-- `rv64.get_register` with a register result type reads `x0` as zero. -/
theorem rv64_interpretOp'_get_register (property : propertiesOf Rv64.get_register)
    (reg : RegisterType) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr) :
    Rv64.interpretOp' .get_register property #[TypeAttr.of RegisterType reg] operands
        blockOperands =
      if reg.index = some 0 then some (#[.reg ⟨0⟩], none) else none := by
  simp [Rv64.interpretOp', TypeAttr.of, Attribute.of, -Attribute.registerType_eq_of]



end

end Veir
