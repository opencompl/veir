module

public import Veir.Interpreter.Basic

import all Veir.Dialects.RISCV_Cf.OpInfo

public section

namespace Veir

/-- `riscv_cf.branch` branches to its only successor with all of its operands. -/
@[simp]
theorem interpretOp'_riscv_cf_branch :
    interpretOp' (.riscv_cf .branch) properties resultTypes operands #[dest] mem layout =
      .ok (#[], mem, some (.branch operands dest)) := by
  grind [interpretOp', Riscv_Cf.interpretOp']

/--
  `riscv_cf.bnez` branches to its first successor with the first segment of its
  operands when its condition register is not zero, and to its second successor
  with the rest otherwise.
-/
theorem interpretOp'_riscv_cf_bnez {properties : propertiesOf (OpCode.riscv_cf .bnez)}
    {cond : Data.RISCV.Reg} (hCond : operands[0]? = some (.reg cond))
    (hSize : properties.operandSegmentSizes.values[1]? = some n) :
    interpretOp' (.riscv_cf .bnez) properties resultTypes operands #[destTrue, destFalse] mem
        layout =
      .ok (#[], mem, some (if cond.val ≠ 0#64 then .branch (operands.extract 1 (n.toNat + 1))
        destTrue else .branch (operands.extract (n.toNat + 1) operands.size) destFalse)) := by
  grind [interpretOp', Riscv_Cf.interpretOp']

end Veir
