module

public import Veir.Interpreter.Basic

import all Veir.Dialects.RISCV_Cf.OpInfo

public section

namespace Veir

/-- `riscv_cf.branch` branches to its only successor with all of its operands. -/
@[simp]
theorem interpretOp'_riscv_cf_branch {properties : propertiesOf (OpCode.riscv_cf .branch)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {dest : BlockPtr}
    {mem : MemoryState} {layout : DataLayout} :
    interpretOp' (.riscv_cf .branch) properties resultTypes operands #[dest] mem layout =
      .ok (#[], mem, some (.branch operands dest)) := by
  grind [interpretOp', Riscv_Cf.interpretOp']

/--
  `riscv_cf.bnez` branches to its first successor with the first segment of its
  operands when its condition register is not zero, and to its second successor
  with the rest otherwise.
-/
theorem interpretOp'_riscv_cf_bnez {properties : propertiesOf (OpCode.riscv_cf .bnez)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {cond : Data.RISCV.Reg} {n : Int}
    {destTrue destFalse : BlockPtr} {mem : MemoryState} {layout : DataLayout}
    (hCond : operands[0]? = some (.reg cond))
    (hSize : properties.operandSegmentSizes.values[1]? = some n) :
    interpretOp' (.riscv_cf .bnez) properties resultTypes operands #[destTrue, destFalse] mem
        layout =
      .ok (#[], mem, some (if cond.val ≠ 0#64 then .branch (operands.extract 1 (n.toNat + 1))
        destTrue else .branch (operands.extract (n.toNat + 1) operands.size) destFalse)) := by
  grind [interpretOp', Riscv_Cf.interpretOp']

/-!
  A compare-and-branch compares its first two operands, which are registers. It
  branches to its first successor with the next segment of its operands when the
  comparison holds, and to its second successor with the rest otherwise.
-/

theorem interpretOp'_riscv_cf_beq {properties : propertiesOf (OpCode.riscv_cf .beq)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {lhs rhs : Data.RISCV.Reg}
    {n : Int} {destTrue destFalse : BlockPtr} {mem : MemoryState} {layout : DataLayout}
    (hLhs : operands[0]? = some (.reg lhs)) (hRhs : operands[1]? = some (.reg rhs))
    (hSize : properties.operandSegmentSizes.values[2]? = some n) :
    interpretOp' (.riscv_cf .beq) properties resultTypes operands #[destTrue, destFalse] mem
        layout =
      .ok (#[], mem, some (if lhs.val = rhs.val then .branch (operands.extract 2 (n.toNat + 2))
        destTrue else .branch (operands.extract (n.toNat + 2) operands.size) destFalse)) := by
  simp only [interpretOp', Riscv_Cf.interpretOp', hLhs, hRhs, hSize]
  have hEq : lhs = rhs ↔ lhs.val = rhs.val := by cases lhs; cases rhs; simp
  by_cases h : lhs.val = rhs.val <;> simp [h, hEq, bind, pure]

theorem interpretOp'_riscv_cf_bne {properties : propertiesOf (OpCode.riscv_cf .bne)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {lhs rhs : Data.RISCV.Reg}
    {n : Int} {destTrue destFalse : BlockPtr} {mem : MemoryState} {layout : DataLayout}
    (hLhs : operands[0]? = some (.reg lhs)) (hRhs : operands[1]? = some (.reg rhs))
    (hSize : properties.operandSegmentSizes.values[2]? = some n) :
    interpretOp' (.riscv_cf .bne) properties resultTypes operands #[destTrue, destFalse] mem
        layout =
      .ok (#[], mem, some (if lhs.val ≠ rhs.val then .branch (operands.extract 2 (n.toNat + 2))
        destTrue else .branch (operands.extract (n.toNat + 2) operands.size) destFalse)) := by
  simp only [interpretOp', Riscv_Cf.interpretOp', hLhs, hRhs, hSize]
  have hEq : lhs = rhs ↔ lhs.val = rhs.val := by cases lhs; cases rhs; simp
  by_cases h : lhs.val = rhs.val <;> simp [h, hEq, bind, pure]

theorem interpretOp'_riscv_cf_blt {properties : propertiesOf (OpCode.riscv_cf .blt)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {lhs rhs : Data.RISCV.Reg}
    {n : Int} {destTrue destFalse : BlockPtr} {mem : MemoryState} {layout : DataLayout}
    (hLhs : operands[0]? = some (.reg lhs)) (hRhs : operands[1]? = some (.reg rhs))
    (hSize : properties.operandSegmentSizes.values[2]? = some n) :
    interpretOp' (.riscv_cf .blt) properties resultTypes operands #[destTrue, destFalse] mem
        layout =
      .ok (#[], mem, some (if lhs.val.slt rhs.val then .branch (operands.extract 2 (n.toNat + 2))
        destTrue else .branch (operands.extract (n.toNat + 2) operands.size) destFalse)) := by
  simp only [interpretOp', Riscv_Cf.interpretOp', hLhs, hRhs, hSize]
  by_cases h : lhs.val.slt rhs.val <;> simp [h, bind, pure]

theorem interpretOp'_riscv_cf_bge {properties : propertiesOf (OpCode.riscv_cf .bge)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {lhs rhs : Data.RISCV.Reg}
    {n : Int} {destTrue destFalse : BlockPtr} {mem : MemoryState} {layout : DataLayout}
    (hLhs : operands[0]? = some (.reg lhs)) (hRhs : operands[1]? = some (.reg rhs))
    (hSize : properties.operandSegmentSizes.values[2]? = some n) :
    interpretOp' (.riscv_cf .bge) properties resultTypes operands #[destTrue, destFalse] mem
        layout =
      .ok (#[], mem, some (if ¬ lhs.val.slt rhs.val then .branch (operands.extract 2 (n.toNat + 2))
        destTrue else .branch (operands.extract (n.toNat + 2) operands.size) destFalse)) := by
  simp only [interpretOp', Riscv_Cf.interpretOp', hLhs, hRhs, hSize]
  by_cases h : lhs.val.slt rhs.val <;> simp [h, bind, pure]

theorem interpretOp'_riscv_cf_bltu {properties : propertiesOf (OpCode.riscv_cf .bltu)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {lhs rhs : Data.RISCV.Reg}
    {n : Int} {destTrue destFalse : BlockPtr} {mem : MemoryState} {layout : DataLayout}
    (hLhs : operands[0]? = some (.reg lhs)) (hRhs : operands[1]? = some (.reg rhs))
    (hSize : properties.operandSegmentSizes.values[2]? = some n) :
    interpretOp' (.riscv_cf .bltu) properties resultTypes operands #[destTrue, destFalse] mem
        layout =
      .ok (#[], mem, some (if lhs.val.ult rhs.val then .branch (operands.extract 2 (n.toNat + 2))
        destTrue else .branch (operands.extract (n.toNat + 2) operands.size) destFalse)) := by
  simp only [interpretOp', Riscv_Cf.interpretOp', hLhs, hRhs, hSize]
  by_cases h : lhs.val.ult rhs.val <;> simp [h, bind, pure]

theorem interpretOp'_riscv_cf_bgeu {properties : propertiesOf (OpCode.riscv_cf .bgeu)}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {lhs rhs : Data.RISCV.Reg}
    {n : Int} {destTrue destFalse : BlockPtr} {mem : MemoryState} {layout : DataLayout}
    (hLhs : operands[0]? = some (.reg lhs)) (hRhs : operands[1]? = some (.reg rhs))
    (hSize : properties.operandSegmentSizes.values[2]? = some n) :
    interpretOp' (.riscv_cf .bgeu) properties resultTypes operands #[destTrue, destFalse] mem
        layout =
      .ok (#[], mem, some (if ¬ lhs.val.ult rhs.val then .branch (operands.extract 2 (n.toNat + 2))
        destTrue else .branch (operands.extract (n.toNat + 2) operands.size) destFalse)) := by
  simp only [interpretOp', Riscv_Cf.interpretOp', hLhs, hRhs, hSize]
  by_cases h : lhs.val.ult rhs.val <;> simp [h, bind, pure]

end Veir
