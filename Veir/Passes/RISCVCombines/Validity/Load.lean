module

import all Veir.Passes.RISCVCombines.Validity.Common

/-! CTree validity proofs for the RISC-V combines that match a load below their root. -/

namespace Veir.RISCV.CTreeProofs

open Puddle
open _root_.CTree

set_option linter.unusedSimpArgs false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Rv64.interpretOp'

attribute [local implicit_reducible] TypeAttr Veir._propertiesOf Riscv.propertiesOf

/-- A RISC-V load that succeeds returns the bytes it read, extended to a register, and leaves
memory unchanged. -/
@[local simp] theorem riscvLoad_reg_eq_ok {mem mem' : MemoryState} {eaddr : BitVec 64} {n : Nat}
    {ext : LoadExtension} {v : RuntimeValue} :
    (do
        let x ← riscvLoad mem eaddr n ext
        Interp.ok (#[RuntimeValue.reg ⟨x.fst⟩], x.snd, (none : Option ControlFlowAction))) =
      Interp.ok (#[v], mem', none) ↔
    ∃ bytes, mem.load (mem.decode (UInt64.ofBitVec eaddr)) n.toUInt64 = .ok bytes ∧
      v = .reg ⟨match ext with
        | .signExt => (bytes.toBitVecLE (8 * n)).signExtend 64
        | .zeroExt => (bytes.toBitVecLE (8 * n)).setWidth 64⟩ ∧
      mem' = mem := by
  simp only [riscvLoad]
  cases h : mem.load (mem.decode (UInt64.ofBitVec eaddr)) n.toUInt64 <;>
    cases ext <;> simp [h, Bind.bind] <;> grind

theorem zextb_lbu_valid : Puddle.CTree.Pattern.Valid (zextb_lbu_pattern) := by
  proveCombineValid using Data.RISCV.zextb_lbu

theorem andi_255_lbu_valid : Puddle.CTree.Pattern.Valid (andi_255_lbu_pattern) := by
  proveCombineValid using Data.RISCV.andi_255_lbu

theorem zextw_slliw_lbu_8_valid : Puddle.CTree.Pattern.Valid (zextw_slliw_lbu_pattern 8) := by
  proveCombineValid using Data.RISCV.zextw_slliw_lbu_8

theorem zextw_slliw_lbu_16_valid : Puddle.CTree.Pattern.Valid (zextw_slliw_lbu_pattern 16) := by
  proveCombineValid using Data.RISCV.zextw_slliw_lbu_16

theorem zextw_slliw_lbu_24_valid : Puddle.CTree.Pattern.Valid (zextw_slliw_lbu_pattern 24) := by
  proveCombineValid using Data.RISCV.zextw_slliw_lbu_24

theorem packh_low_bytes_valid : Puddle.CTree.Pattern.Valid (packh_low_bytes_pattern false) := by
  proveCombineValid using Data.RISCV.packh_low_bytes

theorem packh_low_bytes_commuted_valid : Puddle.CTree.Pattern.Valid (packh_low_bytes_pattern true) := by
  proveCombineValid using Data.RISCV.packh_low_bytes_commuted

theorem packh_high_bytes_valid : Puddle.CTree.Pattern.Valid (packh_high_bytes_pattern false) := by
  proveCombineValid using Data.RISCV.packh_high_bytes

theorem packh_high_bytes_commuted_valid : Puddle.CTree.Pattern.Valid (packh_high_bytes_pattern true) := by
  proveCombineValid using Data.RISCV.packh_high_bytes_commuted

theorem sextw_lw_valid : Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lw 1) := by
  proveCombineValid using Data.RISCV.sextw_lw

theorem sextw_lh_valid : Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lh 1) := by
  proveCombineValid using Data.RISCV.sextw_lh

theorem sextw_lb_valid : Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lb 1) := by
  proveCombineValid using Data.RISCV.sextw_lb

theorem sextw_lhu_valid : Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lhu 1) := by
  proveCombineValid using Data.RISCV.sextw_lhu

theorem sextw_lbu_valid : Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lbu 1) := by
  proveCombineValid using Data.RISCV.sextw_lbu

end Veir.RISCV.CTreeProofs
