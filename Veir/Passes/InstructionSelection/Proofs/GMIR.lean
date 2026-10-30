module

public import Veir.Data.RISCV.Reg.Basic
public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting
public import Veir.Data.Refinement
public import Veir.Dialects.GMIR.Semantics

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
meta import Veir.Meta.Tactic.PBVDecide

import Veir.ForLean
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.RISCV.Reg.Lemmas
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Int.Lemmas
import all Veir.Data.LLVM.Int.Bitblast
import all Veir.Dialects.GMIR.Semantics
import all Veir.Data.Casting
import all Veir.Data.Refinement

public section

/-
  Elaborate the proofs one at a time: each `bv_decide` forks a SAT solver, and
  several forks from one large process fail with `ENOMEM` on a GitHub runner.
-/
set_option Elab.async false

/-!
  The correctness of the instruction selection of the RISC-V gMIR word operations, and of the
  `slti`/`sltiu` selection of `g_icmp`, whose result is the `i64` zero-extension of the comparison.

  A word operation (`GMIR.word`) any-extends its 32-bit result, so its refinement holds for the
  high bits that the hardware word instruction chooses: the sign extension of the result, which is
  the witness of each proof below.

  The other selections of `isel-riscv64` over composed or constant operands match gMIR operations with the semantics
  of the LLVM operations, so the lemmas of `Veir.Passes.InstructionSelection.Proofs` cover them:
  `andn_refinement`, `orn_refinement`, `xnor_refinement`, `orcb_refinement_y*`, and the
  `fold_*_sound` lemmas of the immediate forms composed with the register-register lowerings.
-/

namespace Veir.Data.RISCV

/-! ## Register-register word operations -/

/-- Prove the correctness of selecting `g_addw` as `riscv.addw`. -/
theorem gmir_addw_refinement (x y : LLVM.Int 64) (nsw nuw : Bool) :
    ∃ e, GMIR.word (LLVM.Int.add · · nsw nuw) x y e ⊒ RISCV.Reg.toInt (Data.RISCV.addw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64 :=
  ⟨(Data.RISCV.addw (LLVM.Int.toReg y) (LLVM.Int.toReg x)).val.extractLsb' 32 32, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of selecting `g_subw` as `riscv.subw`. -/
theorem gmir_subw_refinement (x y : LLVM.Int 64) (nsw nuw : Bool) :
    ∃ e, GMIR.word (LLVM.Int.sub · · nsw nuw) x y e ⊒ RISCV.Reg.toInt (Data.RISCV.subw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64 :=
  ⟨(Data.RISCV.subw (LLVM.Int.toReg y) (LLVM.Int.toReg x)).val.extractLsb' 32 32, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of selecting `g_mulw` as `riscv.mulw`. -/
theorem gmir_mulw_refinement (x y : LLVM.Int 64) (nsw nuw : Bool) :
    ∃ e, GMIR.word (LLVM.Int.mul · · nsw nuw) x y e ⊒ RISCV.Reg.toInt (Data.RISCV.mulw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64 :=
  ⟨(Data.RISCV.mulw (LLVM.Int.toReg y) (LLVM.Int.toReg x)).val.extractLsb' 32 32, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of selecting `g_sdivw` as `riscv.divw`. -/
theorem gmir_sdivw_refinement (x y : LLVM.Int 64) (exact : Bool) :
    ∃ e, GMIR.word (LLVM.Int.sdiv · · exact) x y e ⊒ RISCV.Reg.toInt (Data.RISCV.divw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64 :=
  ⟨(Data.RISCV.divw (LLVM.Int.toReg y) (LLVM.Int.toReg x)).val.extractLsb' 32 32, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of selecting `g_udivw` as `riscv.divuw`. -/
theorem gmir_udivw_refinement (x y : LLVM.Int 64) (exact : Bool) :
    ∃ e, GMIR.word (LLVM.Int.udiv · · exact) x y e ⊒ RISCV.Reg.toInt (Data.RISCV.divuw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64 :=
  ⟨(Data.RISCV.divuw (LLVM.Int.toReg y) (LLVM.Int.toReg x)).val.extractLsb' 32 32, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of selecting `g_uremw` as `riscv.remuw`. -/
theorem gmir_uremw_refinement (x y : LLVM.Int 64) :
    ∃ e, GMIR.word (LLVM.Int.urem · ·) x y e ⊒ RISCV.Reg.toInt (Data.RISCV.remuw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64 :=
  ⟨(Data.RISCV.remuw (LLVM.Int.toReg y) (LLVM.Int.toReg x)).val.extractLsb' 32 32, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of selecting `g_shlw` as `riscv.sllw`. -/
theorem gmir_shlw_refinement (x y : LLVM.Int 64) (nsw nuw : Bool) :
    ∃ e, GMIR.word (LLVM.Int.shl · · nsw nuw) x y e ⊒ RISCV.Reg.toInt (Data.RISCV.sllw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64 :=
  ⟨(Data.RISCV.sllw (LLVM.Int.toReg y) (LLVM.Int.toReg x)).val.extractLsb' 32 32, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of selecting `g_lshrw` as `riscv.srlw`. -/
theorem gmir_lshrw_refinement (x y : LLVM.Int 64) (exact : Bool) :
    ∃ e, GMIR.word (LLVM.Int.lshr · · exact) x y e ⊒ RISCV.Reg.toInt (Data.RISCV.srlw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64 :=
  ⟨(Data.RISCV.srlw (LLVM.Int.toReg y) (LLVM.Int.toReg x)).val.extractLsb' 32 32, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of selecting `g_ashrw` as `riscv.sraw`. -/
theorem gmir_ashrw_refinement (x y : LLVM.Int 64) (exact : Bool) :
    ∃ e, GMIR.word (LLVM.Int.ashr · · exact) x y e ⊒ RISCV.Reg.toInt (Data.RISCV.sraw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64 :=
  ⟨(Data.RISCV.sraw (LLVM.Int.toReg y) (LLVM.Int.toReg x)).val.extractLsb' 32 32, by unfold GMIR.word; veir_bv_decide⟩

/-! ## Word immediate forms

  The constant is the `i64` sign extension of the 12-bit immediate (`addiw`) or the 5-bit shift
  amount (`slliw`, `srliw`, `sraiw`), as `lowerBinaryImm` requires.
-/

/-- Prove the correctness of selecting `g_addw` with a constant amount as `riscv.addiw`. -/
theorem gmir_addw_imm_refinement (x : LLVM.Int 64) (imm : BitVec 12) (nsw nuw : Bool) :
    ∃ e, GMIR.word (LLVM.Int.add · · nsw nuw) x (LLVM.Int.val (imm.signExtend 64)) e ⊒ RISCV.Reg.toInt (Data.RISCV.addiw imm (LLVM.Int.toReg x)) 64 :=
  ⟨(Data.RISCV.addiw imm (LLVM.Int.toReg x)).val.extractLsb' 32 32, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of selecting `g_shlw` with a constant amount as `riscv.slliw`. -/
theorem gmir_shlw_imm_refinement (x : LLVM.Int 64) (imm : BitVec 5) (nsw nuw : Bool) :
    ∃ e, GMIR.word (LLVM.Int.shl · · nsw nuw) x (LLVM.Int.val (imm.setWidth 64)) e ⊒ RISCV.Reg.toInt (Data.RISCV.slliw imm (LLVM.Int.toReg x)) 64 :=
  ⟨(Data.RISCV.slliw imm (LLVM.Int.toReg x)).val.extractLsb' 32 32, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of selecting `g_lshrw` with a constant amount as `riscv.srliw`. -/
theorem gmir_lshrw_imm_refinement (x : LLVM.Int 64) (imm : BitVec 5) (exact : Bool) :
    ∃ e, GMIR.word (LLVM.Int.lshr · · exact) x (LLVM.Int.val (imm.setWidth 64)) e ⊒ RISCV.Reg.toInt (Data.RISCV.srliw imm (LLVM.Int.toReg x)) 64 :=
  ⟨(Data.RISCV.srliw imm (LLVM.Int.toReg x)).val.extractLsb' 32 32, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of selecting `g_ashrw` with a constant amount as `riscv.sraiw`. -/
theorem gmir_ashrw_imm_refinement (x : LLVM.Int 64) (imm : BitVec 5) (exact : Bool) :
    ∃ e, GMIR.word (LLVM.Int.ashr · · exact) x (LLVM.Int.val (imm.setWidth 64)) e ⊒ RISCV.Reg.toInt (Data.RISCV.sraiw imm (LLVM.Int.toReg x)) 64 :=
  ⟨(Data.RISCV.sraiw imm (LLVM.Int.toReg x)).val.extractLsb' 32 32, by unfold GMIR.word; veir_bv_decide⟩

/-! ## `slti`/`sltiu` selection of `g_icmp`

  Each theorem justifies one arm of `sltiImm?`, with the constant `C` that the immediate `imm`
  stands for: `sext(imm)`, or `sext(imm) - 1` for the `≤` predicates, whose immediate is `C + 1`.
  The unsigned `≤` form needs `imm ≠ 0`, which `sltiImm?` ensures by rejecting `C = -1`.
-/

/-- `g_icmp slt x, C` -> `slti imm x`. -/
theorem gmir_icmp_slt_imm_refinement (x : LLVM.Int 64) (imm : BitVec 12) :
    LLVM.Int.zext (Data.LLVM.Int.icmp x (LLVM.Int.val (imm.signExtend 64)) LLVM.IntPred.slt) 64 false
        (by decide) ⊒
      RISCV.Reg.toInt (Data.RISCV.slti imm (LLVM.Int.toReg x)) 64 := by
  veir_bv_decide

/-- `g_icmp ult x, C` -> `sltiu imm x`. -/
theorem gmir_icmp_ult_imm_refinement (x : LLVM.Int 64) (imm : BitVec 12) :
    LLVM.Int.zext (Data.LLVM.Int.icmp x (LLVM.Int.val (imm.signExtend 64)) LLVM.IntPred.ult) 64 false
        (by decide) ⊒
      RISCV.Reg.toInt (Data.RISCV.sltiu imm (LLVM.Int.toReg x)) 64 := by
  veir_bv_decide

/-- `g_icmp sge x, C` -> `xori 1#12 (slti imm x)`. -/
theorem gmir_icmp_sge_imm_refinement (x : LLVM.Int 64) (imm : BitVec 12) :
    LLVM.Int.zext (Data.LLVM.Int.icmp x (LLVM.Int.val (imm.signExtend 64)) LLVM.IntPred.sge) 64 false
        (by decide) ⊒
      RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.slti imm (LLVM.Int.toReg x))) 64 := by
  veir_bv_decide

/-- `g_icmp uge x, C` -> `xori 1#12 (sltiu imm x)`. -/
theorem gmir_icmp_uge_imm_refinement (x : LLVM.Int 64) (imm : BitVec 12) :
    LLVM.Int.zext (Data.LLVM.Int.icmp x (LLVM.Int.val (imm.signExtend 64)) LLVM.IntPred.uge) 64 false
        (by decide) ⊒
      RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.sltiu imm (LLVM.Int.toReg x))) 64 := by
  veir_bv_decide

/-- `g_icmp sle x, C` -> `slti imm x`. -/
theorem gmir_icmp_sle_imm_refinement (x : LLVM.Int 64) (imm : BitVec 12) :
    LLVM.Int.zext (Data.LLVM.Int.icmp x (LLVM.Int.val (imm.signExtend 64 - 1)) LLVM.IntPred.sle) 64 false
        (by decide) ⊒
      RISCV.Reg.toInt (Data.RISCV.slti imm (LLVM.Int.toReg x)) 64 := by
  veir_bv_decide

/-- `g_icmp ule x, C` -> `sltiu imm x`. -/
theorem gmir_icmp_ule_imm_refinement (x : LLVM.Int 64) (imm : BitVec 12) (h : imm ≠ 0) :
    LLVM.Int.zext (Data.LLVM.Int.icmp x (LLVM.Int.val (imm.signExtend 64 - 1)) LLVM.IntPred.ule) 64 false
        (by decide) ⊒
      RISCV.Reg.toInt (Data.RISCV.sltiu imm (LLVM.Int.toReg x)) 64 := by
  veir_bv_decide

end Veir.Data.RISCV
