module

public import Veir.Dialects.RISCV.Fold.Basic
public import Veir.Data.RISCV.Reg.Basic

import Veir.Meta.BVDecide
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.RISCV.Reg.Lemmas

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

public section

namespace Veir.Fold.Proofs.Riscv

open Veir.Data
open Data.RISCV

theorem add_zero (x : Reg) :
    Data.RISCV.add (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem sub_zero (x : Reg) :
    Data.RISCV.sub (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem xor_zero (x : Reg) :
    Data.RISCV.xor (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem or_zero (x : Reg) :
    Data.RISCV.or (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem or_all_ones (x : Reg) :
    Data.RISCV.or (Data.RISCV.li (BitVec.allOnes 64)) x =
      Data.RISCV.li (BitVec.allOnes 64) := by
  veir_bv_decide

theorem and_zero (x : Reg) :
    Data.RISCV.and (Data.RISCV.li 0) x = Data.RISCV.li 0 := by
  veir_bv_decide

theorem and_all_ones (x : Reg) :
    Data.RISCV.and (Data.RISCV.li (BitVec.allOnes 64)) x = x := by
  veir_bv_decide

theorem mul_zero (x : Reg) :
    Data.RISCV.mul (Data.RISCV.li 0) x = Data.RISCV.li 0 := by
  veir_bv_decide

theorem mul_one (x : Reg) :
    Data.RISCV.mul (Data.RISCV.li 1) x = x := by
  veir_bv_decide

theorem sll_zero (x : Reg) :
    Data.RISCV.sll (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem srl_zero (x : Reg) :
    Data.RISCV.srl (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem sra_zero (x : Reg) :
    Data.RISCV.sra (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem czeroeqz_zero (x : Reg) :
    Data.RISCV.czeroeqz (Data.RISCV.li 0) x = Data.RISCV.li 0 := by
  veir_bv_decide

theorem czeroeqz_nonzero (x c : Reg) (h : c.val ≠ 0) :
    Data.RISCV.czeroeqz c x = x := by
  veir_bv_decide

theorem czeronez_zero (x : Reg) :
    Data.RISCV.czeronez (Data.RISCV.li 0) x = x := by
  veir_bv_decide

theorem czeronez_nonzero (x c : Reg) (h : c.val ≠ 0) :
    Data.RISCV.czeronez c x = Data.RISCV.li 0 := by
  veir_bv_decide

theorem addi_zero (x : Reg) :
    Data.RISCV.addi 0 x = x := by
  veir_bv_decide

theorem ori_zero (x : Reg) :
    Data.RISCV.ori 0 x = x := by
  veir_bv_decide

theorem xori_zero (x : Reg) :
    Data.RISCV.xori 0 x = x := by
  veir_bv_decide

theorem andi_zero (x : Reg) :
    Data.RISCV.andi 0 x = Data.RISCV.li 0 := by
  veir_bv_decide

theorem slli_zero (x : Reg) :
    Data.RISCV.slli 0 x = x := by
  veir_bv_decide

theorem srli_zero (x : Reg) :
    Data.RISCV.srli 0 x = x := by
  veir_bv_decide

theorem srai_zero (x : Reg) :
    Data.RISCV.srai 0 x = x := by
  veir_bv_decide

end Veir.Fold.Proofs.Riscv
