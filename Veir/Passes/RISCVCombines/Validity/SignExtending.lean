module

import all Veir.Passes.RISCVCombines.Validity.Common
meta import Veir.Meta.ProofKind

/-! CTree validity proofs for the RISC-V combines: `sextw` of a sign-extending producer. -/

namespace Veir.RISCV.CTreeProofs

open Puddle
open _root_.CTree

set_option linter.unusedSimpArgs false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Rv64.interpretOp'

attribute [local implicit_reducible] TypeAttr

@[proof_bv]
theorem sextw_addw_valid (h : IsSignExtendingOpW .addw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .addw 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_addw

@[proof_bv]
theorem sextw_addiw_valid (h : IsSignExtendingOpW .addiw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .addiw 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_addiw

@[proof_bv]
theorem sextw_subw_valid (h : IsSignExtendingOpW .subw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .subw 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_subw

@[proof_bv]
theorem sextw_mulw_valid (h : IsSignExtendingOpW .mulw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .mulw 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_mulw

@[proof_bv]
theorem sextw_divw_valid (h : IsSignExtendingOpW .divw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .divw 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_divw

@[proof_bv]
theorem sextw_divuw_valid (h : IsSignExtendingOpW .divuw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .divuw 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_divuw

@[proof_bv]
theorem sextw_remw_valid (h : IsSignExtendingOpW .remw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .remw 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_remw

@[proof_bv]
theorem sextw_remuw_valid (h : IsSignExtendingOpW .remuw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .remuw 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_remuw

@[proof_bv]
theorem sextw_sllw_valid (h : IsSignExtendingOpW .sllw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sllw 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_sllw

@[proof_bv]
theorem sextw_slliw_valid (h : IsSignExtendingOpW .slliw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .slliw 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_slliw

@[proof_bv]
theorem sextw_srlw_valid (h : IsSignExtendingOpW .srlw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .srlw 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_srlw

@[proof_bv]
theorem sextw_srliw_valid (h : IsSignExtendingOpW .srliw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .srliw 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_srliw

@[proof_bv]
theorem sextw_sraw_valid (h : IsSignExtendingOpW .sraw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sraw 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_sraw

@[proof_bv]
theorem sextw_sraiw_valid (h : IsSignExtendingOpW .sraiw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sraiw 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_sraiw

@[proof_bv]
theorem sextw_rolw_valid (h : IsSignExtendingOpW .rolw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .rolw 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_rolw

@[proof_bv]
theorem sextw_rorw_valid (h : IsSignExtendingOpW .rorw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .rorw 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_rorw

@[proof_bv]
theorem sextw_roriw_valid (h : IsSignExtendingOpW .roriw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .roriw 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_roriw

@[proof_bv]
theorem sextw_packw_valid (h : IsSignExtendingOpW .packw 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .packw 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_packw

@[proof_bv]
theorem sextw_lui_valid (h : IsSignExtendingOpW .lui 0 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .lui 0 _ h) := by
  proveCombineValid using Data.RISCV.sextw_lui

@[proof_bv]
theorem sextw_cpop_valid (h : IsSignExtendingOpW .cpop 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .cpop 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_cpop

@[proof_bv]
theorem sextw_cpopw_valid (h : IsSignExtendingOpW .cpopw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .cpopw 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_cpopw

@[proof_bv]
theorem sextw_clz_valid (h : IsSignExtendingOpW .clz 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .clz 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_clz

@[proof_bv]
theorem sextw_clzw_valid (h : IsSignExtendingOpW .clzw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .clzw 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_clzw

@[proof_bv]
theorem sextw_ctz_valid (h : IsSignExtendingOpW .ctz 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .ctz 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_ctz

@[proof_bv]
theorem sextw_ctzw_valid (h : IsSignExtendingOpW .ctzw 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .ctzw 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_ctzw

@[proof_bv]
theorem sextw_slt_valid (h : IsSignExtendingOpW .slt 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .slt 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_slt

@[proof_bv]
theorem sextw_sltu_valid (h : IsSignExtendingOpW .sltu 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sltu 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_sltu

@[proof_bv]
theorem sextw_slti_valid (h : IsSignExtendingOpW .slti 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .slti 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_slti

@[proof_bv]
theorem sextw_sltiu_valid (h : IsSignExtendingOpW .sltiu 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sltiu 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_sltiu

@[proof_bv]
theorem sextw_bext_valid (h : IsSignExtendingOpW .bext 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .bext 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_bext

@[proof_bv]
theorem sextw_bexti_valid (h : IsSignExtendingOpW .bexti 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .bexti 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_bexti

@[proof_bv]
theorem sextw_sextb_valid (h : IsSignExtendingOpW .sextb 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sextb 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_sextb

@[proof_bv]
theorem sextw_sexth_valid (h : IsSignExtendingOpW .sexth 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .sexth 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_sexth

@[proof_bv]
theorem sextw_zexth_valid (h : IsSignExtendingOpW .zexth 1 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .zexth 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_zexth

@[proof_bv]
theorem sextw_packh_valid (h : IsSignExtendingOpW .packh 2 fun _ => true) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .packh 2 _ h) := by
  proveCombineValid using Data.RISCV.sextw_packh

@[proof_bv]
theorem sextw_srai_valid
    (h : IsSignExtendingOpW .srai 1 (fun p => 32#6 ≤ p.immField 6)) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .srai 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_srai

@[proof_bv]
theorem sextw_srli_valid
    (h : IsSignExtendingOpW .srli 1 (fun p => 32#6 < p.immField 6)) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .srli 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_srli

@[proof_bv]
theorem sextw_andi_valid
    (h : IsSignExtendingOpW .andi 1 (fun p => !(p.immField 12).msb)) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .andi 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_andi

@[proof_bv]
theorem sextw_ori_valid
    (h : IsSignExtendingOpW .ori 1 (fun p => (p.immField 12).msb)) :
    Puddle.CTree.Pattern.Valid (sextw_signExtendingOpW_pattern .ori 1 _ h) := by
  proveCombineValid using Data.RISCV.sextw_ori

end Veir.RISCV.CTreeProofs
