module

public import Veir.Interpreter.Basic

import all Veir.Dialects.RISCV_Cf.OpInfo

public section

/-!
# What the RISC-V branches compute

The meaning that `interpretOp'` gives the `riscv_cf` branches, for proofs that
do not unfold the interpreter of the dialect.
-/

open Veir.Data

namespace Veir

/-- `riscv_cf.branch` branches to its only successor with all of its operands. -/
@[simp]
theorem interpretOp'_riscv_cf_branch {properties : propertiesOf (OpCode.riscv_cf .branch)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {dest : BlockPtr}
    {mem : MemoryState} {layout : DataLayout} :
    interpretOp' (.riscv_cf .branch) properties resultTypes operands #[dest] mem layout =
      .ok (#[], mem, some (.branch operands dest)) := by
  simp [interpretOp', Riscv_Cf.interpretOp']

/--
  `riscv_cf.bnez` on a register branches to its first successor with the first
  segment of its operands when the register is not zero, and to its second
  successor with the rest otherwise.
-/
theorem interpretOp'_riscv_cf_bnez {properties : propertiesOf (OpCode.riscv_cf .bnez)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {cond : RISCV.Reg} {n : Int}
    {destTrue destFalse : BlockPtr} {mem : MemoryState} {layout : DataLayout}
    (hCond : operands[0]? = some (.reg cond))
    (hSize : properties.operandSegmentSizes.values[1]? = some n) :
    interpretOp' (.riscv_cf .bnez) properties resultTypes operands #[destTrue, destFalse] mem
        layout =
      .ok (#[], mem, some (if cond.val ≠ 0#64 then .branch (operands.extract 1 (n.toNat + 1))
        destTrue else .branch (operands.extract (n.toNat + 1) operands.size) destFalse)) := by
  grind [interpretOp', Riscv_Cf.interpretOp']

end Veir
