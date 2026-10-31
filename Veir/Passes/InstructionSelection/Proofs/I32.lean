module

public import Veir.Data.RISCV.Reg.Basic
public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting
public import Veir.Data.Refinement

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
meta import Veir.Meta.Tactic.PBVDecide

import Veir.ForLean
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.RISCV.Reg.Lemmas
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Int.Lemmas
import all Veir.Data.LLVM.Int.Bitblast
import all Veir.Data.Casting
import all Veir.Data.Refinement

public section

/-
  Elaborate the proofs one at a time: each `bv_decide` forks a SAT solver, and
  several forks from one large process fail with `ENOMEM` on a GitHub runner.
-/
set_option Elab.async false

/-!
  The correctness of the lowering patterns of the i32 instruction selection path,
  in a module of their own: together with the 64-bit proofs they exhaust the memory
  of a GitHub runner.
-/

namespace Veir.Data.RISCV

/-! ## i32 lowering refinement proofs

  These proofs cover all operations added to the i32 isel path.
  The semantic model zero-extends i32 values when loading into a 64-bit
  register (`LLVM.Int.toReg`), so signed operations that inspect the sign
  bit must first `sextw`-extend the low 32 bits.
-/

theorem ashr_refinement_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.ashr x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sraw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

theorem mul_refinement_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.mul x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.mulw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

theorem sdiv_refinement_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.sdiv x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.divw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

theorem udiv_refinement_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.udiv x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.divuw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

/-- `i32` analogue of `udivPow2_refinement` (`udivwPow2`). -/
theorem udivwPow2_refinement {x : LLVM.Int 32} (k : BitVec 5) :
    (Data.LLVM.Int.udiv x (LLVM.Int.val ((1#32) <<< k))) ⊒
      (RISCV.Reg.toInt (Data.RISCV.srliw k (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

/-- `i32` analogue of `sdivPow2Exact_pos_refinement` (`sdivwPow2Exact`, positive
    divisor): a genuine positive `i32` divisor `2^k` needs `k < 31`. -/
theorem sdivwPow2Exact_pos_refinement {x : LLVM.Int 32} (k : BitVec 5) (hk : k < 31) :
    (Data.LLVM.Int.sdiv x (LLVM.Int.val ((1#32) <<< k)) true) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sraiw k (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

/-- `i32` analogue of `sdivPow2Exact_neg_refinement` (`sdivwPow2Exact`, negative
    divisor): `-2^31` (`k = 31`) is itself a valid `i32` divisor, so no upper bound
    on `k` is needed. -/
theorem sdivwPow2Exact_neg_refinement {x : LLVM.Int 32} (k : BitVec 5) :
    (Data.LLVM.Int.sdiv x (LLVM.Int.val (-((1#32) <<< k))) true) ⊒
      (RISCV.Reg.toInt (Data.RISCV.negw (Data.RISCV.sraiw k (LLVM.Int.toReg x))) 32) := by
  veir_bv_decide

/-- `i32` analogue of `sdivPow2_pos_refinement` (`sdivwPow2`, positive divisor). -/
theorem sdivwPow2_pos_refinement {x : LLVM.Int 32} (k : BitVec 5) (hk0 : 0 < k) (hk31 : k < 31) :
    (Data.LLVM.Int.sdiv x (LLVM.Int.val ((1#32) <<< k)) false) ⊒
      (RISCV.Reg.toInt
        (let sign := Data.RISCV.sraiw 31 (LLVM.Int.toReg x)
         let corr := Data.RISCV.srliw (32 - k) sign
         let biased := Data.RISCV.addw corr (LLVM.Int.toReg x)
         Data.RISCV.sraiw k biased) 32) := by
  veir_bv_decide

/-- `i32` analogue of `sdivPow2_neg_refinement` (`sdivwPow2`, negative divisor). -/
theorem sdivwPow2_neg_refinement {x : LLVM.Int 32} (k : BitVec 5) (hk0 : 0 < k) :
    (Data.LLVM.Int.sdiv x (LLVM.Int.val (-((1#32) <<< k))) false) ⊒
      (RISCV.Reg.toInt
        (let sign := Data.RISCV.sraiw 31 (LLVM.Int.toReg x)
         let corr := Data.RISCV.srliw (32 - k) sign
         let biased := Data.RISCV.addw corr (LLVM.Int.toReg x)
         Data.RISCV.negw (Data.RISCV.sraiw k biased)) 32) := by
  veir_bv_decide

theorem srem_refinement_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.srem x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.remw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

theorem urem_refinement_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.urem x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.remuw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

theorem ctlz_refinement_32 {x : LLVM.Int 32} {is_zero_poison : Bool} :
    (Data.LLVM.Int.ctlz x is_zero_poison) ⊒
      (RISCV.Reg.toInt (Data.RISCV.clzw (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

theorem cttz_refinement_32 {x : LLVM.Int 32} {is_zero_poison : Bool} :
    (Data.LLVM.Int.cttz x is_zero_poison) ⊒
      (RISCV.Reg.toInt (Data.RISCV.ctzw (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

theorem ctpop_refinement_32 {x : LLVM.Int 32} :
    (Data.LLVM.Int.ctpop x) ⊒
      (RISCV.Reg.toInt (Data.RISCV.cpopw (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

theorem bswap_refinement_32 {x : LLVM.Int 32} :
    (Data.LLVM.Int.bswap x) ⊒
      (RISCV.Reg.toInt (Data.RISCV.srli 32#6 (Data.RISCV.rev8 (LLVM.Int.toReg x))) 32) := by
  veir_bv_decide

theorem bitreverse_refinement_32 {x : LLVM.Int 32} :
    (Data.LLVM.Int.bitreverse x) ⊒
      (RISCV.Reg.toInt (Data.RISCV.srli 32#6 (Data.RISCV.rev8 (Data.RISCV.brev8 (LLVM.Int.toReg x)))) 32) := by
  veir_bv_decide

theorem bswap_refinement_16 {x : LLVM.Int 16} :
    (Data.LLVM.Int.bswap x) ⊒
      (RISCV.Reg.toInt (Data.RISCV.srli 48#6 (Data.RISCV.rev8 (LLVM.Int.toReg x))) 16) := by
  veir_bv_decide

theorem bitreverse_refinement_16 {x : LLVM.Int 16} :
    (Data.LLVM.Int.bitreverse x) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.srli 48#6 (Data.RISCV.rev8 (Data.RISCV.brev8 (LLVM.Int.toReg x)))) 16) := by
  veir_bv_decide

theorem bitreverse_refinement_8 {x : LLVM.Int 8} :
    (Data.LLVM.Int.bitreverse x) ⊒
      (RISCV.Reg.toInt (Data.RISCV.brev8 (LLVM.Int.toReg x)) 8) := by
  veir_bv_decide

theorem bswap_bitreverse_refinement_16 {x : LLVM.Int 16} :
    (Data.LLVM.Int.bswap (Data.LLVM.Int.bitreverse x)) ⊒
      (RISCV.Reg.toInt (Data.RISCV.brev8 (LLVM.Int.toReg x)) 16) := by
  veir_bv_decide

theorem bitreverse_bswap_refinement_16 {x : LLVM.Int 16} :
    (Data.LLVM.Int.bitreverse (Data.LLVM.Int.bswap x)) ⊒
      (RISCV.Reg.toInt (Data.RISCV.brev8 (LLVM.Int.toReg x)) 16) := by
  veir_bv_decide

theorem bswap_bitreverse_refinement_32 {x : LLVM.Int 32} :
    (Data.LLVM.Int.bswap (Data.LLVM.Int.bitreverse x)) ⊒
      (RISCV.Reg.toInt (Data.RISCV.brev8 (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

theorem bitreverse_bswap_refinement_32 {x : LLVM.Int 32} :
    (Data.LLVM.Int.bitreverse (Data.LLVM.Int.bswap x)) ⊒
      (RISCV.Reg.toInt (Data.RISCV.brev8 (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

theorem bswap_bitreverse_refinement_64 {x : LLVM.Int 64} :
    (Data.LLVM.Int.bswap (Data.LLVM.Int.bitreverse x)) ⊒
      (RISCV.Reg.toInt (Data.RISCV.brev8 (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

theorem bitreverse_bswap_refinement_64 {x : LLVM.Int 64} :
    (Data.LLVM.Int.bitreverse (Data.LLVM.Int.bswap x)) ⊒
      (RISCV.Reg.toInt (Data.RISCV.brev8 (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

theorem icmp_refinement_eq_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.eq) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltiu 1#12
        (Data.RISCV.xor
          (Data.RISCV.sextw (LLVM.Int.toReg y))
          (Data.RISCV.sextw (LLVM.Int.toReg x)))) 1) := by
  veir_bv_decide

theorem icmp_refinement_ne_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ne) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltu
        (Data.RISCV.xor
          (Data.RISCV.sextw (LLVM.Int.toReg y))
          (Data.RISCV.sextw (LLVM.Int.toReg x)))
        (Data.RISCV.li 0#64)) 1) := by
  veir_bv_decide

theorem icmp_refinement_slt_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.slt) ⊒
      (RISCV.Reg.toInt (Data.RISCV.slt
        (Data.RISCV.sextw (LLVM.Int.toReg y))
        (Data.RISCV.sextw (LLVM.Int.toReg x))) 1) := by
  veir_bv_decide

theorem icmp_refinement_sle_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.sle) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.slt
          (Data.RISCV.sextw (LLVM.Int.toReg x))
          (Data.RISCV.sextw (LLVM.Int.toReg y)))) 1) := by
  veir_bv_decide

theorem icmp_refinement_sgt_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.sgt) ⊒
      (RISCV.Reg.toInt (Data.RISCV.slt
        (Data.RISCV.sextw (LLVM.Int.toReg x))
        (Data.RISCV.sextw (LLVM.Int.toReg y))) 1) := by
  veir_bv_decide

theorem icmp_refinement_sge_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.sge) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.slt
          (Data.RISCV.sextw (LLVM.Int.toReg y))
          (Data.RISCV.sextw (LLVM.Int.toReg x)))) 1) := by
  veir_bv_decide

theorem icmp_refinement_ult_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ult) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltu
        (Data.RISCV.sextw (LLVM.Int.toReg y))
        (Data.RISCV.sextw (LLVM.Int.toReg x))) 1) := by
  veir_bv_decide

theorem icmp_refinement_ule_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ule) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.sltu
          (Data.RISCV.sextw (LLVM.Int.toReg x))
          (Data.RISCV.sextw (LLVM.Int.toReg y)))) 1) := by
  veir_bv_decide

theorem icmp_refinement_ugt_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ugt) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltu
        (Data.RISCV.sextw (LLVM.Int.toReg x))
        (Data.RISCV.sextw (LLVM.Int.toReg y))) 1) := by
  veir_bv_decide

theorem icmp_refinement_uge_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.uge) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.sltu
          (Data.RISCV.sextw (LLVM.Int.toReg y))
          (Data.RISCV.sextw (LLVM.Int.toReg x)))) 1) := by
  veir_bv_decide

theorem icmp_refinement_eq_8 {x y : LLVM.Int 8} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.eq) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltiu 1#12
        (Data.RISCV.xor
          (Data.RISCV.sextb (LLVM.Int.toReg y))
          (Data.RISCV.sextb (LLVM.Int.toReg x)))) 1) := by
  veir_bv_decide

theorem icmp_refinement_ne_8 {x y : LLVM.Int 8} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ne) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltu
        (Data.RISCV.xor
          (Data.RISCV.sextb (LLVM.Int.toReg y))
          (Data.RISCV.sextb (LLVM.Int.toReg x)))
        (Data.RISCV.li 0#64)) 1) := by
  veir_bv_decide

theorem icmp_refinement_slt_8 {x y : LLVM.Int 8} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.slt) ⊒
      (RISCV.Reg.toInt (Data.RISCV.slt
        (Data.RISCV.sextb (LLVM.Int.toReg y))
        (Data.RISCV.sextb (LLVM.Int.toReg x))) 1) := by
  veir_bv_decide

theorem icmp_refinement_sle_8 {x y : LLVM.Int 8} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.sle) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.slt
          (Data.RISCV.sextb (LLVM.Int.toReg x))
          (Data.RISCV.sextb (LLVM.Int.toReg y)))) 1) := by
  veir_bv_decide

theorem icmp_refinement_sgt_8 {x y : LLVM.Int 8} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.sgt) ⊒
      (RISCV.Reg.toInt (Data.RISCV.slt
        (Data.RISCV.sextb (LLVM.Int.toReg x))
        (Data.RISCV.sextb (LLVM.Int.toReg y))) 1) := by
  veir_bv_decide

theorem icmp_refinement_sge_8 {x y : LLVM.Int 8} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.sge) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.slt
          (Data.RISCV.sextb (LLVM.Int.toReg y))
          (Data.RISCV.sextb (LLVM.Int.toReg x)))) 1) := by
  veir_bv_decide

theorem icmp_refinement_ult_8 {x y : LLVM.Int 8} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ult) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltu
        (Data.RISCV.sextb (LLVM.Int.toReg y))
        (Data.RISCV.sextb (LLVM.Int.toReg x))) 1) := by
  veir_bv_decide

theorem icmp_refinement_ule_8 {x y : LLVM.Int 8} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ule) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.sltu
          (Data.RISCV.sextb (LLVM.Int.toReg x))
          (Data.RISCV.sextb (LLVM.Int.toReg y)))) 1) := by
  veir_bv_decide

theorem icmp_refinement_ugt_8 {x y : LLVM.Int 8} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ugt) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltu
        (Data.RISCV.sextb (LLVM.Int.toReg x))
        (Data.RISCV.sextb (LLVM.Int.toReg y))) 1) := by
  veir_bv_decide

theorem icmp_refinement_uge_8 {x y : LLVM.Int 8} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.uge) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.sltu
          (Data.RISCV.sextb (LLVM.Int.toReg y))
          (Data.RISCV.sextb (LLVM.Int.toReg x)))) 1) := by
  veir_bv_decide

theorem smax_refinement_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.smax x y) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.max
          (Data.RISCV.sextw (LLVM.Int.toReg y))
          (Data.RISCV.sextw (LLVM.Int.toReg x))) 32) := by
  veir_bv_decide

theorem smin_refinement_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.smin x y) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.min
          (Data.RISCV.sextw (LLVM.Int.toReg y))
          (Data.RISCV.sextw (LLVM.Int.toReg x))) 32) := by
  veir_bv_decide

theorem umax_refinement_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.umax x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.maxu (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

theorem umin_refinement_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.umin x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.minu (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

theorem fshl_rol_refinement_32 {a c : LLVM.Int 32} :
    (Data.LLVM.Int.fshl a a c) ⊒
      (RISCV.Reg.toInt (Data.RISCV.rolw (LLVM.Int.toReg c) (LLVM.Int.toReg a)) 32) := by
  veir_bv_decide

theorem fshr_ror_refinement_32 {a c : LLVM.Int 32} :
    (Data.LLVM.Int.fshr a a c) ⊒
      (RISCV.Reg.toInt (Data.RISCV.rorw (LLVM.Int.toReg c) (LLVM.Int.toReg a)) 32) := by
  veir_bv_decide

theorem freeze_refinement_32 {a : LLVM.Int 32} :
    (Data.LLVM.Int.freeze a) ⊒
      (RISCV.Reg.toInt (LLVM.Int.toReg a) 32) := by
  veir_bv_decide
