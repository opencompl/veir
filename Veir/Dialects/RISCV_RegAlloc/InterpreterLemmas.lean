module

public import Veir.Dialects.RISCV_RegAlloc.OpInfo
import all Veir.Dialects.RISCV_RegAlloc.OpInfo

public section

namespace Veir

/--
If `spill` succeeds on `operands`, then reloading the results of the spill returns `operands`.
-/
theorem Riscv_RegAlloc.reloading_returns_spilled_value
    {spillTypes reloadTypes : Array TypeAttr} {spillBlocks reloadBlocks : Array BlockPtr}
    {operands spilled : Array RuntimeValue} {action : Option ControlFlowAction}
    (h : Riscv_RegAlloc.interpretOp' .spill () spillTypes operands spillBlocks
      = some (spilled, action)) :
    Riscv_RegAlloc.interpretOp' .reload () reloadTypes spilled reloadBlocks
      = some (operands, none) := by
  match operands with
  | ⟨[.reg value]⟩ =>
   cases h
   rfl


end Veir
