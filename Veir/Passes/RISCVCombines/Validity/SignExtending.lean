module

import all Veir.Passes.RISCVCombines.Validity.Common

/-! CTree validity proofs for the RISC-V combines: `sextw` of a sign-extending producer. -/

namespace Veir.RISCV.CTreeProofs

open Puddle
open _root_.CTree

set_option linter.unusedSimpArgs false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Rv64.interpretOp'

attribute [local implicit_reducible] TypeAttr

theorem sextw_addw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .addw 2) := by
  proveCombineValid using Data.RISCV.sextw_addw

theorem sextw_addiw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .addiw 1) := by
  proveCombineValid using Data.RISCV.sextw_addiw

theorem sextw_subw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .subw 2) := by
  proveCombineValid using Data.RISCV.sextw_subw

theorem sextw_mulw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .mulw 2) := by
  proveCombineValid using Data.RISCV.sextw_mulw

theorem sextw_divw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .divw 2) := by
  proveCombineValid using Data.RISCV.sextw_divw

theorem sextw_divuw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .divuw 2) := by
  proveCombineValid using Data.RISCV.sextw_divuw

theorem sextw_remw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .remw 2) := by
  proveCombineValid using Data.RISCV.sextw_remw

theorem sextw_remuw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .remuw 2) := by
  proveCombineValid using Data.RISCV.sextw_remuw

theorem sextw_sllw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sllw 2) := by
  proveCombineValid using Data.RISCV.sextw_sllw

theorem sextw_slliw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .slliw 1) := by
  proveCombineValid using Data.RISCV.sextw_slliw

theorem sextw_srlw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .srlw 2) := by
  proveCombineValid using Data.RISCV.sextw_srlw

theorem sextw_srliw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .srliw 1) := by
  proveCombineValid using Data.RISCV.sextw_srliw

theorem sextw_sraw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sraw 2) := by
  proveCombineValid using Data.RISCV.sextw_sraw

theorem sextw_sraiw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sraiw 1) := by
  proveCombineValid using Data.RISCV.sextw_sraiw

theorem sextw_rolw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .rolw 2) := by
  proveCombineValid using Data.RISCV.sextw_rolw

theorem sextw_rorw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .rorw 2) := by
  proveCombineValid using Data.RISCV.sextw_rorw

theorem sextw_roriw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .roriw 1) := by
  proveCombineValid using Data.RISCV.sextw_roriw

theorem sextw_packw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .packw 2) := by
  proveCombineValid using Data.RISCV.sextw_packw

theorem sextw_lui_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lui 0) := by
  proveCombineValid using Data.RISCV.sextw_lui

theorem sextw_cpop_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .cpop 1) := by
  proveCombineValid using Data.RISCV.sextw_cpop

theorem sextw_cpopw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .cpopw 1) := by
  proveCombineValid using Data.RISCV.sextw_cpopw

theorem sextw_clz_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .clz 1) := by
  proveCombineValid using Data.RISCV.sextw_clz

theorem sextw_clzw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .clzw 1) := by
  proveCombineValid using Data.RISCV.sextw_clzw

theorem sextw_ctz_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .ctz 1) := by
  proveCombineValid using Data.RISCV.sextw_ctz

theorem sextw_ctzw_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .ctzw 1) := by
  proveCombineValid using Data.RISCV.sextw_ctzw

theorem sextw_slt_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .slt 2) := by
  proveCombineValid using Data.RISCV.sextw_slt

theorem sextw_sltu_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sltu 2) := by
  proveCombineValid using Data.RISCV.sextw_sltu

theorem sextw_slti_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .slti 1) := by
  proveCombineValid using Data.RISCV.sextw_slti

theorem sextw_sltiu_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sltiu 1) := by
  proveCombineValid using Data.RISCV.sextw_sltiu

theorem sextw_bext_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .bext 2) := by
  proveCombineValid using Data.RISCV.sextw_bext

theorem sextw_bexti_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .bexti 1) := by
  proveCombineValid using Data.RISCV.sextw_bexti

theorem sextw_sextb_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sextb 1) := by
  proveCombineValid using Data.RISCV.sextw_sextb

theorem sextw_sexth_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sexth 1) := by
  proveCombineValid using Data.RISCV.sextw_sexth

theorem sextw_zexth_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .zexth 1) := by
  proveCombineValid using Data.RISCV.sextw_zexth

theorem sextw_packh_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .packh 2) := by
  proveCombineValid using Data.RISCV.sextw_packh

theorem sextw_srai_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .srai 1 (fun p => 32#6 ≤ p.immField 6)) := by
  proveCombineValid using Data.RISCV.sextw_srai

theorem sextw_srli_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .srli 1 (fun p => 32#6 < p.immField 6)) := by
  proveCombineValid using Data.RISCV.sextw_srli

theorem sextw_andi_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .andi 1 (fun p => !(p.immField 12).msb)) := by
  proveCombineValid using Data.RISCV.sextw_andi

theorem sextw_ori_valid :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .ori 1 (fun p => (p.immField 12).msb)) := by
  proveCombineValid using Data.RISCV.sextw_ori

end Veir.RISCV.CTreeProofs
