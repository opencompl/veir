module

public import Veir.Interpreter.Basic

import all Veir.Dialects.RV64.OpInfo

public section

namespace Veir

/-- `rv64.get_register` of `x0` gives the register that holds zero. -/
theorem interpretOp'_rv64_get_register_x0 {properties : propertiesOf (OpCode.rv64 .get_register)}
    {operands : Array RuntimeValue} {successors : Array BlockPtr} {mem : MemoryState}
    {layout : DataLayout} :
    interpretOp' (.rv64 .get_register) properties #[(RegisterType.mk (some 0) : TypeAttr)]
        operands successors mem layout =
      .ok (#[.reg ⟨0⟩], mem, none) := by
  simp only [interpretOp', Rv64.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject]
  rfl

end Veir
