import Veir.Data.RISCV.Reg.Basic
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Data.LLVM.Int.Basic
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.LLVM.Int.Bitblast
import Veir.Data.Casting
import Veir.Data.Refinement
import Std.Tactic.BVDecide
import Veir.ForLean

/-!
  In this file we prove the correctness of the lowering patterns used in the
  instruction selection rewrites.
-/

namespace Veir.Data.RISCV

/--
  Prove the correctness of the `constant` lowering pattern.

  We do not need to consider the poison case, as the semantics of `llvm_constant`
  are always concrete in the interpreter.
-/
theorem constant_refinement {v : Int}:
    (LLVM.Int.constant 64 v) ⊒ (RISCV.Reg.toInt (Data.RISCV.li (BitVec.ofInt 64 v)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `poisonConst` lowering pattern.
-/
theorem poisonConst_refinement :
    (LLVM.Int.poison (w := _)) ⊒ (RISCV.Reg.toInt (Data.RISCV.li (BitVec.ofInt 64 0)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `constant` lowering pattern at i32 (similar to the `i64` case above), however currently using the grind tactic.
-/
theorem constant_refinement_32 {v : Int} :
    (LLVM.Int.constant 32 v) ⊒ (RISCV.Reg.toInt (Data.RISCV.li (BitVec.ofInt 64 v)) 32) := by
  veir_bv_decide

theorem constant_refinement_8 {v : Int} :
    (LLVM.Int.constant 8 v) ⊒ (RISCV.Reg.toInt (Data.RISCV.li (BitVec.ofInt 64 v)) 8) := by
  veir_bv_decide

theorem constant_refinement_1 {v : Int} :
    (LLVM.Int.constant 1 v) ⊒ (RISCV.Reg.toInt (Data.RISCV.li (BitVec.ofInt 64 v)) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the `add` lowering pattern.
-/
theorem add_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.add x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.add (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `add` lowering pattern at i32, which selects the
  32-bit `addw`.
-/
theorem addw_refinement {x y : LLVM.Int 32} :
    (Data.LLVM.Int.add x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.addw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

/--
  Prove the correctness of the `and` lowering pattern.
-/
theorem and_refinement{x y : LLVM.Int 64} :
    (Data.LLVM.Int.and x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.and (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

theorem and_refinement_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.and x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.and (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

theorem and_refinement_8 {x y : LLVM.Int 8} :
    (Data.LLVM.Int.and x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.and (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 8) := by
  veir_bv_decide

theorem and_refinement_1 {x y : LLVM.Int 1} :
    (Data.LLVM.Int.and x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.and (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 1) := by
  veir_bv_decide


/--
  Prove the correctness of the `ctlz` intrinsic lowering pattern.
-/
theorem ctlz_refinement {x : LLVM.Int 64} {is_zero_poison : Bool} :
    (Data.LLVM.Int.ctlz x is_zero_poison) ⊒
      (RISCV.Reg.toInt (Data.RISCV.clz (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `cttz` intrinsic lowering pattern.
-/
theorem cttz_refinement {x : LLVM.Int 64} {is_zero_poison : Bool} :
    (Data.LLVM.Int.cttz x is_zero_poison) ⊒
      (RISCV.Reg.toInt (Data.RISCV.ctz (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `ctpop` intrinsic lowering pattern.
-/
theorem ctpop_refinement {x : LLVM.Int 64} :
    (Data.LLVM.Int.ctpop x) ⊒
      (RISCV.Reg.toInt (Data.RISCV.cpop (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `bswap` intrinsic lowering pattern.
-/
theorem bswap_refinement {x : LLVM.Int 64} :
    (Data.LLVM.Int.bswap x) ⊒
      (RISCV.Reg.toInt (Data.RISCV.rev8 (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `bitreverse` intrinsic lowering pattern.
-/
theorem bitreverse_refinement {x : LLVM.Int 64} :
    (Data.LLVM.Int.bitreverse x) ⊒
      (RISCV.Reg.toInt
        (let x0 := LLVM.Int.toReg x
         let m1 := Data.RISCV.li 0x5555555555555555#64
         let x1 := Data.RISCV.or
           (Data.RISCV.slli 1#6 (Data.RISCV.and m1 x0))
           (Data.RISCV.and m1 (Data.RISCV.srli 1#6 x0))
         let m2 := Data.RISCV.li 0x3333333333333333#64
         let x2 := Data.RISCV.or
           (Data.RISCV.slli 2#6 (Data.RISCV.and m2 x1))
           (Data.RISCV.and m2 (Data.RISCV.srli 2#6 x1))
         let m4 := Data.RISCV.li 0x0f0f0f0f0f0f0f0f#64
         let x3 := Data.RISCV.or
           (Data.RISCV.slli 4#6 (Data.RISCV.and m4 x2))
           (Data.RISCV.and m4 (Data.RISCV.srli 4#6 x2))
         Data.RISCV.rev8 x3) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `ashr` lowering pattern.
-/
theorem ashr_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.ashr x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.sra (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

theorem ashr_refinement_1 {x y : LLVM.Int 1} :
    (Data.LLVM.Int.ashr x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.sra (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `eq`.
-/
theorem icmp_refinement_eq {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.eq) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltiu 1#12 (Data.RISCV.xor (LLVM.Int.toReg y) (LLVM.Int.toReg x))) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `ne`.
-/
theorem icmp_refinement_ne {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ne) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltu (Data.RISCV.xor (LLVM.Int.toReg y) (LLVM.Int.toReg x)) (Data.RISCV.li 0#64)) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the constant-zero `icmp eq` peephole, with the zero on
  the right (`x == 0`). The lowering drops the `xor` and emits `sltiu x 1` (seqz)
  directly on the non-zero operand.
-/
theorem icmp_refinement_eq_zero_rhs {x : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x (LLVM.Int.constant 64 0) LLVM.IntPred.eq) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltiu 1#12 (LLVM.Int.toReg x)) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the constant-zero `icmp ne` peephole, with the zero on
  the right (`x != 0`). The lowering drops the `xor` and emits `sltu 0 x` (snez)
  directly on the non-zero operand.
-/
theorem icmp_refinement_ne_zero_rhs {x : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x (LLVM.Int.constant 64 0) LLVM.IntPred.ne) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltu (LLVM.Int.toReg x) (Data.RISCV.li 0#64)) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the `riscv-combine` `li 0 -> x0` rewrite: materializing
  the constant `0` with `li` produces exactly the value of the hard-wired zero
  register `x0` (which the interpreter models as the register holding `0#64`).
  Since every consumer is a pure function of its source registers' values,
  substituting `x0` for the `li 0` result preserves semantics.
-/
theorem li_zero_eq_x0 :
    Data.RISCV.li 0#64 = RISCV.Reg.mk 0#64 := by
  veir_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `slt`.
-/
theorem icmp_refinement_slt {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.slt) ⊒
      (RISCV.Reg.toInt (Data.RISCV.slt (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `sle`.
-/
theorem icmp_refinement_sle {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.sle) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.slt (LLVM.Int.toReg x) (LLVM.Int.toReg y))) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `sgt`.
-/
theorem icmp_refinement_sgt {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.sgt) ⊒
      (RISCV.Reg.toInt (Data.RISCV.slt (LLVM.Int.toReg x) (LLVM.Int.toReg y)) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `sge`.
-/
theorem icmp_refinement_sge {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.sge) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.slt (LLVM.Int.toReg y) (LLVM.Int.toReg x))) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `ult`.
-/
theorem icmp_refinement_ult {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ult) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltu (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `ule`.
-/
theorem icmp_refinement_ule {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ule) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.sltu (LLVM.Int.toReg x) (LLVM.Int.toReg y))) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `ugt`.
-/
theorem icmp_refinement_ugt {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ugt) ⊒
      (RISCV.Reg.toInt ((Data.RISCV.sltu (LLVM.Int.toReg x) (LLVM.Int.toReg y))) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `uge`.
-/
theorem icmp_refinement_uge {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.uge) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.sltu (LLVM.Int.toReg y) (LLVM.Int.toReg x))) 1) := by
  veir_bv_decide

/-! ### Immediate-constant refinements for ordered comparisons

  Each theorem justifies one arm of the `slti` immediate-form selection in
  `isel-sdag-riscv64`, comparing `x` against a constant that equals the
  sign-extension of the 12-bit immediate `imm` actually encoded in the emitted
  instruction. For the `≤` predicates the constant is `sext(imm) - 1`, capturing
  the `x ≤ C == x < C+1` rewrite (the code stores `C+1` as the immediate). The
  unsigned off-by-one form carries the `imm ≠ 0` hypothesis that the code
  enforces by rejecting `C = -1` (else `C+1` wraps past `UINT_MAX`). -/

/-- `icmp sge x C` with `C = sext(imm)` -> `xori (slti x imm) 1`. -/
theorem icmp_refinement_sge_imm {x : LLVM.Int 64} (imm : BitVec 12) :
    (Data.LLVM.Int.icmp x (LLVM.Int.val (imm.signExtend 64)) LLVM.IntPred.sge) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.slti imm (LLVM.Int.toReg x))) 1) := by
  veir_bv_decide

/-- `icmp uge x C` with `C = sext(imm)` -> `xori (sltiu x imm) 1`. -/
theorem icmp_refinement_uge_imm {x : LLVM.Int 64} (imm : BitVec 12) :
    (Data.LLVM.Int.icmp x (LLVM.Int.val (imm.signExtend 64)) LLVM.IntPred.uge) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.sltiu imm (LLVM.Int.toReg x))) 1) := by
  veir_bv_decide

/-- `icmp sle x C` with `C = sext(imm) - 1` -> `slti x imm` (i.e. `x < C+1`). -/
theorem icmp_refinement_sle_imm {x : LLVM.Int 64} (imm : BitVec 12) :
    (Data.LLVM.Int.icmp x (LLVM.Int.val (imm.signExtend 64 - 1)) LLVM.IntPred.sle) ⊒
      (RISCV.Reg.toInt (Data.RISCV.slti imm (LLVM.Int.toReg x)) 1) := by
  veir_bv_decide

/-- `icmp ule x C` with `C = sext(imm) - 1` -> `sltiu x imm`; needs `imm ≠ 0`
    (else `C = UINT_MAX` and `C+1` wraps to `0`). -/
theorem icmp_refinement_ule_imm {x : LLVM.Int 64} (imm : BitVec 12) (h : imm ≠ 0) :
    (Data.LLVM.Int.icmp x (LLVM.Int.val (imm.signExtend 64 - 1)) LLVM.IntPred.ule) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltiu imm (LLVM.Int.toReg x)) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the `or` lowering pattern.
-/
theorem or_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.or x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.or (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `or` lowering pattern at i32 (plain `or`, no `W` variant).
-/
theorem or_refinement_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.or x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.or (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

theorem or_refinement_8 {x y : LLVM.Int 8} :
    (Data.LLVM.Int.or x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.or (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 8) := by
  veir_bv_decide

theorem or_refinement_1 {x y : LLVM.Int 1} :
    (Data.LLVM.Int.or x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.or (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 1) := by
  veir_bv_decide

/--
  Prove the correctness of the `xor` lowering pattern.
-/
theorem xor_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.xor x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.xor (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `xor` lowering pattern at i32.
-/
theorem xor_refinement_32 {x y : LLVM.Int 32} :
    (Data.LLVM.Int.xor x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.xor (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

/--
  Prove the correctness of the `mul` lowering pattern.
-/
theorem mul_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.mul x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.mul (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `sdiv` lowering pattern.
-/
theorem sdiv_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.sdiv x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.div (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `udiv` lowering pattern.
-/
theorem udiv_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.udiv x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.divu (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/-! ### `sdiv`/`udiv` by a constant power of two -/

/--
  `udiv x, 2^k` -> `riscv.srli x, k` (`udivPow2`). Mirrors `DAGCombiner::visitUDIVLike`'s
  `fold (udiv x, (1 << c)) -> x >>u c` (via `BuildLogBase2`).
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L5430-L5440
-/
theorem udivPow2_refinement {x : LLVM.Int 64} (k : BitVec 6) :
    (Data.LLVM.Int.udiv x (LLVM.Int.val ((1#64) <<< k))) ⊒
      (RISCV.Reg.toInt (Data.RISCV.srli k (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  `sdiv exact x, 2^k` -> `riscv.srai x, k` (`sdivPow2Exact`, positive divisor).
  Since `exact` makes the source poison whenever `x` isn't a multiple of `2^k`, this
  only has to hold when the arithmetic right shift and the truncating division
  agree, i.e. when there is no fractional part to round differently.
-/
theorem sdivPow2Exact_pos_refinement {x : LLVM.Int 64} (k : BitVec 6) (hk : k < 63) :
    (Data.LLVM.Int.sdiv x (LLVM.Int.val ((1#64) <<< k)) true) ⊒
      (RISCV.Reg.toInt (Data.RISCV.srai k (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  `sdiv exact x, -2^k` -> `riscv.sub 0, (riscv.srai x, k)` (`sdivPow2Exact`, negative
  divisor). No upper bound on `k` is needed here: `-2^63` (`k = 63`) is itself a
  valid `i64` divisor.
-/
theorem sdivPow2Exact_neg_refinement {x : LLVM.Int 64} (k : BitVec 6) :
    (Data.LLVM.Int.sdiv x (LLVM.Int.val (-((1#64) <<< k))) true) ⊒
      (RISCV.Reg.toInt (Data.RISCV.neg (Data.RISCV.srai k (LLVM.Int.toReg x))) 64) := by
  veir_bv_decide

/--
  General (non-`exact`) `sdiv x, 2^k` -> the Hacker's-Delight bias/shift sequence
  (`sdivPow2`, positive divisor): bias a negative dividend by `2^k - 1` before the
  arithmetic shift, so truncation rounds toward zero. `k = 0` is excluded because the
  correction shift `64 - k` would then need a full 64-bit shift, which has no legal
  RISC-V immediate encoding (`sdiv x, ±1` never reaches instruction selection as
  such: it is always simplified away first).
-/
theorem sdivPow2_pos_refinement {x : LLVM.Int 64} (k : BitVec 6) (hk0 : 0 < k) (hk63 : k < 63) :
    (Data.LLVM.Int.sdiv x (LLVM.Int.val ((1#64) <<< k)) false) ⊒
      (RISCV.Reg.toInt
        (let sign := Data.RISCV.srai 63 (LLVM.Int.toReg x)
         let corr := Data.RISCV.srli (64 - k) sign
         let biased := Data.RISCV.add corr (LLVM.Int.toReg x)
         Data.RISCV.srai k biased) 64) := by
  veir_bv_decide

/--
  Negative-divisor case of `sdivPow2_pos_refinement`: negate the biased-shift result.
-/
theorem sdivPow2_neg_refinement {x : LLVM.Int 64} (k : BitVec 6) (hk0 : 0 < k) :
    (Data.LLVM.Int.sdiv x (LLVM.Int.val (-((1#64) <<< k))) false) ⊒
      (RISCV.Reg.toInt
        (let sign := Data.RISCV.srai 63 (LLVM.Int.toReg x)
         let corr := Data.RISCV.srli (64 - k) sign
         let biased := Data.RISCV.add corr (LLVM.Int.toReg x)
         Data.RISCV.neg (Data.RISCV.srai k biased)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `udiv` lowering pattern.
-/
theorem srem_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.srem x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.rem (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `udiv` lowering pattern.
-/
theorem urem_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.urem x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.remu (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `udiv` lowering pattern.
-/
theorem sub_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.sub x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.sub (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `sub` lowering pattern at i32.
-/
theorem subw_refinement {x y : LLVM.Int 32} :
    (Data.LLVM.Int.sub x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.subw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

/--
  Prove the correctness of the `shl` lowering pattern.
-/
theorem sllw_refinement {x y : LLVM.Int 32} :
    (Data.LLVM.Int.shl x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.sllw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

/--
  Prove the correctness of the `lshr` lowering pattern.
-/
theorem srlw_refinement {x y : LLVM.Int 32} :
    (Data.LLVM.Int.lshr x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.srlw (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

/--
  Prove the correctness of the `andn` lowering pattern.
-/
theorem andn_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.and x (Data.LLVM.Int.xor y (LLVM.Int.constant 64 (-1)))) ⊒
      (RISCV.Reg.toInt (Data.RISCV.andn (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `orn` lowering pattern.
-/
theorem orn_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.or x (Data.LLVM.Int.xor y (LLVM.Int.constant 64 (-1)))) ⊒
      (RISCV.Reg.toInt (Data.RISCV.orn (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `xnor` lowering pattern.
-/
theorem xnor_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.xor x (Data.LLVM.Int.xor y (LLVM.Int.constant 64 (-1)))) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xnor (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `select c t 0` -> `czero.eqz t c` lowering pattern.
-/
theorem select_czeroeqz_refinement {c : LLVM.Int 1} {t : LLVM.Int 64} :
    (Data.LLVM.Int.select c t (LLVM.Int.constant 64 0)) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.czeroeqz (LLVM.Int.toReg c) (LLVM.Int.toReg t)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `select c 0 f` -> `czero.nez f c` lowering pattern.
-/
theorem select_czeronez_refinement {c : LLVM.Int 1} {f : LLVM.Int 64} :
    (Data.LLVM.Int.select c (LLVM.Int.constant 64 0) f) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.czeronez (LLVM.Int.toReg c) (LLVM.Int.toReg f)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the general `select c t f` ->
  `or (czero.eqz t c) (czero.nez f c)` lowering pattern.
-/
theorem select_refinement {c : LLVM.Int 1} {t f : LLVM.Int 64} :
    (Data.LLVM.Int.select c t f) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.or
          (Data.RISCV.czeronez (LLVM.Int.toReg c) (LLVM.Int.toReg f))
          (Data.RISCV.czeroeqz (LLVM.Int.toReg c) (LLVM.Int.toReg t))) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `orcb` lowering pattern (the `Y = 0` case).

  The `and` with the per-byte bit-0 mask `0x0101_0101_0101_0101` is what makes the
  rewrite sound: it ensures each byte of the masked value `M` has only bit 0
  possibly set, so `(M << 8) - M` equals `orc.b M`.
-/
theorem orcb_refinement_y0 {z : LLVM.Int 64} :
    (Data.LLVM.Int.sub
        (Data.LLVM.Int.shl
          (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0101010101010101))
          (LLVM.Int.constant 64 8))
        (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0101010101010101)))
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.orcb (LLVM.Int.toReg
            (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0101010101010101)))) 64 := by
  veir_bv_decide

/--
  Prove the correctness of the `orcb` lowering pattern for `1 ≤ Y < 8`.

  For each `Y`, masking with `0x0101_0101_0101_0101 <<< Y` ensures each byte of
  `M` has only bit `Y` possibly set, so `(M << (8 - Y)) - (M >> Y)` equals
  `orc.b M`.
-/
theorem orcb_refinement_y1 {z : LLVM.Int 64} :
    (Data.LLVM.Int.sub
        (Data.LLVM.Int.shl (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0202020202020202))
          (LLVM.Int.constant 64 7))
        (Data.LLVM.Int.lshr (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0202020202020202))
          (LLVM.Int.constant 64 1)))
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.orcb (LLVM.Int.toReg
            (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0202020202020202)))) 64 := by
  veir_bv_decide

theorem orcb_refinement_y2 {z : LLVM.Int 64} :
    (Data.LLVM.Int.sub
        (Data.LLVM.Int.shl (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0404040404040404))
          (LLVM.Int.constant 64 6))
        (Data.LLVM.Int.lshr (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0404040404040404))
          (LLVM.Int.constant 64 2)))
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.orcb (LLVM.Int.toReg
            (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0404040404040404)))) 64 := by
  veir_bv_decide

theorem orcb_refinement_y3 {z : LLVM.Int 64} :
    (Data.LLVM.Int.sub
        (Data.LLVM.Int.shl (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0808080808080808))
          (LLVM.Int.constant 64 5))
        (Data.LLVM.Int.lshr (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0808080808080808))
          (LLVM.Int.constant 64 3)))
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.orcb (LLVM.Int.toReg
            (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0808080808080808)))) 64 := by
  veir_bv_decide

theorem orcb_refinement_y4 {z : LLVM.Int 64} :
    (Data.LLVM.Int.sub
        (Data.LLVM.Int.shl (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x1010101010101010))
          (LLVM.Int.constant 64 4))
        (Data.LLVM.Int.lshr (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x1010101010101010))
          (LLVM.Int.constant 64 4)))
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.orcb (LLVM.Int.toReg
            (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x1010101010101010)))) 64 := by
  veir_bv_decide

theorem orcb_refinement_y5 {z : LLVM.Int 64} :
    (Data.LLVM.Int.sub
        (Data.LLVM.Int.shl (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x2020202020202020))
          (LLVM.Int.constant 64 3))
        (Data.LLVM.Int.lshr (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x2020202020202020))
          (LLVM.Int.constant 64 5)))
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.orcb (LLVM.Int.toReg
            (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x2020202020202020)))) 64 := by
  veir_bv_decide

theorem orcb_refinement_y6 {z : LLVM.Int 64} :
    (Data.LLVM.Int.sub
        (Data.LLVM.Int.shl (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x4040404040404040))
          (LLVM.Int.constant 64 2))
        (Data.LLVM.Int.lshr (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x4040404040404040))
          (LLVM.Int.constant 64 6)))
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.orcb (LLVM.Int.toReg
            (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x4040404040404040)))) 64 := by
  veir_bv_decide

theorem orcb_refinement_y7 {z : LLVM.Int 64} :
    (Data.LLVM.Int.sub
        (Data.LLVM.Int.shl (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x8080808080808080))
          (LLVM.Int.constant 64 1))
        (Data.LLVM.Int.lshr (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x8080808080808080))
          (LLVM.Int.constant 64 7)))
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.orcb (LLVM.Int.toReg
            (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x8080808080808080)))) 64 := by
  veir_bv_decide

/--
  Prove the correctness of the `zext` lowering pattern `i8` -> `i16`
-/
theorem zext_refinement_8_16 {x : LLVM.Int 8} :
    (Data.LLVM.Int.zext x 16 b h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.zextb (LLVM.Int.toReg x)) 16) := by
  veir_bv_decide

/--
  Prove the correctness of the `zext` lowering pattern `i8` -> `i32`
-/
theorem zext_refinement_8_32 {x : LLVM.Int 8} :
    (Data.LLVM.Int.zext x 32 b h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.zextb (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

/--
  Prove the correctness of the `zext` lowering pattern `i8` -> `i64`
-/
theorem zext_refinement_8_64 {x : LLVM.Int 8} :
    (Data.LLVM.Int.zext x 64 b h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.zextb (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `zext` lowering pattern `i16` -> `i32`
-/
theorem zext_refinement_16_32 {x : LLVM.Int 16} :
    (Data.LLVM.Int.zext x 32 b h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.zexth (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

/--
  Prove the correctness of the `zext` lowering pattern `i16` -> `i64`
-/
theorem zext_refinement_16_64 {x : LLVM.Int 16} :
    (Data.LLVM.Int.zext x 64 b h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.zexth (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `zext` lowering pattern `i32` -> `i64`
-/
theorem zext_refinement_32_64 {x : LLVM.Int 32} :
    (Data.LLVM.Int.zext x 64 b h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.zextw (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `zext` lowering pattern `i1` -> `i64`
-/
theorem zext_refinement_1_64 {x : LLVM.Int 1} :
    (Data.LLVM.Int.zext x 64 b h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.andi 1#12 (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `sext` lowering pattern `i8` -> `i16`
-/
theorem sext_refinement_8_16 {x : LLVM.Int 8} :
    (Data.LLVM.Int.sext x 16 h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sextb (LLVM.Int.toReg x)) 16) := by
  veir_bv_decide

/--
  Prove the correctness of the `sext` lowering pattern `i8` -> `i32`
-/
theorem sext_refinement_8_32 {x : LLVM.Int 8} :
    (Data.LLVM.Int.sext x 32 h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sextb (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

/--
  Prove the correctness of the `sext` lowering pattern `i8` -> `i64`
-/
theorem sext_refinement_8_64 {x : LLVM.Int 8} :
    (Data.LLVM.Int.sext x 64 h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sextb (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `sext` lowering pattern `i16` -> `i32`
-/
theorem sext_refinement_16_32 {x : LLVM.Int 16} :
    (Data.LLVM.Int.sext x 32 h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sexth (LLVM.Int.toReg x)) 32) := by
  veir_bv_decide

/--
  Prove the correctness of the `sext` lowering pattern `i16` -> `i64`
-/
theorem sext_refinement_16_64 {x : LLVM.Int 16} :
    (Data.LLVM.Int.sext x 64 h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sexth (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `sext` lowering pattern `i32` -> `i64`
-/
theorem sext_refinement_32_64 {x : LLVM.Int 32} :
    (Data.LLVM.Int.sext x 64 h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sextw (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `sext` lowering pattern `i1` -> `i64`
-/
theorem sext_refinement_1_64 {x : LLVM.Int 1} :
    (Data.LLVM.Int.sext x 64 h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.srai 63#6 (Data.RISCV.slli 63#6 (LLVM.Int.toReg x))) 64) := by
  veir_bv_decide

theorem sext_refinement_1_32 {x : LLVM.Int 1} :
    (Data.LLVM.Int.sext x 32 h) ⊒
      (RISCV.Reg.toInt (Data.RISCV.srai 63#6 (Data.RISCV.slli 63#6 (LLVM.Int.toReg x))) 32) := by
  veir_bv_decide

/--
  Prove the correctness of the `trunc` lowering pattern `i64` -> `i32`
-/
theorem trunc_refinement_64_32 {x : LLVM.Int 64} :
    (Data.LLVM.Int.trunc x 32 nsw nuw h) ⊒
      (RISCV.Reg.toInt (LLVM.Int.toReg x) 32) := by
  veir_bv_decide

/--
  Prove the correctness of the `trunc` lowering pattern `i64` -> `i16`
-/
theorem trunc_refinement_64_16 {x : LLVM.Int 64} :
    (Data.LLVM.Int.trunc x 16 nsw nuw h) ⊒
      (RISCV.Reg.toInt (LLVM.Int.toReg x) 16) := by
  veir_bv_decide

/--
  Prove the correctness of the `trunc` lowering pattern `i64` -> `i8`
-/
theorem trunc_refinement_64_8 {x : LLVM.Int 64} :
    (Data.LLVM.Int.trunc x 8 nsw nuw h) ⊒
      (RISCV.Reg.toInt (LLVM.Int.toReg x) 8) := by
  veir_bv_decide

/--
  Prove the correctness of the `trunc` lowering pattern `i32` -> `i16`
-/
theorem trunc_refinement_32_16 {x : LLVM.Int 32} :
    (Data.LLVM.Int.trunc x 16 nsw nuw h) ⊒
      (RISCV.Reg.toInt (LLVM.Int.toReg x) 16) := by
  veir_bv_decide

/--
  Prove the correctness of the `trunc` lowering pattern `i32` -> `i8`
-/
theorem trunc_refinement_32_8 {x : LLVM.Int 32} :
    (Data.LLVM.Int.trunc x 8 nsw nuw h) ⊒
      (RISCV.Reg.toInt (LLVM.Int.toReg x) 8) := by
  veir_bv_decide

/--
  Prove the correctness of the `trunc` lowering pattern `i16` -> `i8`
-/
theorem trunc_refinement_16_8 {x : LLVM.Int 16} :
    (Data.LLVM.Int.trunc x 8 nsw nuw h) ⊒
      (RISCV.Reg.toInt (LLVM.Int.toReg x) 8) := by
  veir_bv_decide

/--
  Prove the correctness of the `smax` lowering pattern (`llvm.intr.smax` -> `max`).
-/
theorem smax_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.smax x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.max (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `smin` lowering pattern (`llvm.intr.smin` -> `min`).
-/
theorem smin_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.smin x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.min (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `umax` lowering pattern (`llvm.intr.umax` -> `maxu`).
-/
theorem umax_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.umax x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.maxu (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `umin` lowering pattern (`llvm.intr.umin` -> `minu`).
-/
theorem umin_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.umin x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.minu (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/-! ### Saturating integer intrinsic lowerings

  Each theorem below matches the RV64+Zbb+Zicond sequence emitted by the
  corresponding pattern in `Veir/Passes/InstructionSelection/RISCV64.lean`,
  which in turn mirrors LLVM's generic expansions
  (`llvm/lib/CodeGen/SelectionDAG/TargetLowering.cpp`). Operand order follows
  the `riscv.OP #[a, b]` ↦ `Data.RISCV.OP b a` convention (second operand is
  `rs2`). For the shift variants, a shift amount ≥ 64 makes the LLVM operation
  poison, which refines any register value, so the RV64 low-6-bit masking is
  sound.
-/

/--
  Prove the correctness of the `sadd.sat` lowering (`llvm.intr.sadd.sat` ->
  signed saturating-add with Zicond select).
-/
theorem saddSat_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.saddSat x y) ⊒
      (RISCV.Reg.toInt
        (let x0 := LLVM.Int.toReg x
         let y0 := LLVM.Int.toReg y
         let m1 := Data.RISCV.li (BitVec.ofInt 64 (-1))
         let sum := Data.RISCV.add y0 x0
         let rhsSign := Data.RISCV.srli 63#6 y0
         let carryLike := Data.RISCV.slt x0 sum
         let sumSign := Data.RISCV.srai 63#6 sum
         let intMin := Data.RISCV.slli 63#6 m1
         let overflow := Data.RISCV.xor carryLike rhsSign
         let sat := Data.RISCV.xor intMin sumSign
         Data.RISCV.or
           (Data.RISCV.czeronez overflow sum)
           (Data.RISCV.czeroeqz overflow sat)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `ssub.sat` lowering (`llvm.intr.ssub.sat` ->
  signed saturating-sub with Zicond select).
-/
theorem ssubSat_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.ssubSat x y) ⊒
      (RISCV.Reg.toInt
        (let x0 := LLVM.Int.toReg x
         let y0 := LLVM.Int.toReg y
         let m1 := Data.RISCV.li (BitVec.ofInt 64 (-1))
         let diff := Data.RISCV.sub y0 x0
         let cmp := Data.RISCV.slt y0 x0
         let diffSignBit := Data.RISCV.srli 63#6 diff
         let diffSign := Data.RISCV.srai 63#6 diff
         let intMin := Data.RISCV.slli 63#6 m1
         let overflow := Data.RISCV.xor diffSignBit cmp
         let sat := Data.RISCV.xor intMin diffSign
         Data.RISCV.or
           (Data.RISCV.czeronez overflow diff)
           (Data.RISCV.czeroeqz overflow sat)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `uadd.sat` lowering
  (`llvm.intr.uadd.sat` -> `umin(a, ~b) + b`).
-/
theorem uaddSat_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.uaddSat x y) ⊒
      (RISCV.Reg.toInt
        (let x0 := LLVM.Int.toReg x
         let y0 := LLVM.Int.toReg y
         let notRhs := Data.RISCV.xori (BitVec.ofInt 12 (-1)) y0
         Data.RISCV.add y0 (Data.RISCV.minu notRhs x0)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `usub.sat` lowering
  (`llvm.intr.usub.sat` -> `umax(a, b) - b`).
-/
theorem usubSat_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.usubSat x y) ⊒
      (RISCV.Reg.toInt
        (let x0 := LLVM.Int.toReg x
         let y0 := LLVM.Int.toReg y
         Data.RISCV.sub y0 (Data.RISCV.maxu y0 x0)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `sshl.sat` lowering (`llvm.intr.sshl.sat` ->
  signed saturating-shl with Zicond select).
-/
theorem sshlSat_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.sshlSat x y) ⊒
      (RISCV.Reg.toInt
        (let x0 := LLVM.Int.toReg x
         let y0 := LLVM.Int.toReg y
         let m1 := Data.RISCV.li (BitVec.ofInt 64 (-1))
         let shifted := Data.RISCV.sll y0 x0
         let unshifted := Data.RISCV.sra y0 shifted
         let sign := Data.RISCV.srai 63#6 x0
         let intMax := Data.RISCV.srli 1#6 m1
         let overflow := Data.RISCV.xor unshifted x0
         let sat := Data.RISCV.xor intMax sign
         Data.RISCV.or
           (Data.RISCV.czeronez overflow shifted)
           (Data.RISCV.czeroeqz overflow sat)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `ushl.sat` lowering (`llvm.intr.ushl.sat` ->
  unsigned saturating-shl with the `sltiu`/`addi`/`or` mask idiom).
-/
theorem ushlSat_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.ushlSat x y) ⊒
      (RISCV.Reg.toInt
        (let x0 := LLVM.Int.toReg x
         let y0 := LLVM.Int.toReg y
         let shifted := Data.RISCV.sll y0 x0
         let unshifted := Data.RISCV.srl y0 shifted
         let lostBits := Data.RISCV.xor unshifted x0
         let noOverflow := Data.RISCV.sltiu 1#12 lostBits
         let overflowMask := Data.RISCV.addi (BitVec.ofInt 12 (-1)) noOverflow
         Data.RISCV.or shifted overflowMask) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `abs` lowering (`llvm.intr.abs` -> `max(x, -x)`
  via Zbb `neg`/`max`). The lowering is independent of `is_int_min_poison`: when
  it is set, `abs intMin` is poison (which refines the `intMin` the `neg`/`max`
  sequence produces); when it is clear, both sides yield `intMin`.
-/
theorem abs_refinement {x : LLVM.Int 64} {is_int_min_poison : Bool} :
    (Data.LLVM.Int.abs x is_int_min_poison) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.max (Data.RISCV.neg (LLVM.Int.toReg x)) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/-!
  ## Funnel-shift lowerings

  These cover both the rotate special cases (identical data operands, selecting
  `rol`/`ror`/`rori`/`roriw`) and the general distinct-operand funnel shifts
  (selecting LLVM's `expandFunnelShift` shift/or sequence).

  `veir_bv_decide` closes all of them directly. Its `veir_bv_normalize` phase
  rewrites the funnel-shift semantics (via `getValue_fshl`/`getValue_fshr`) into a
  BitVec shift by the `BitVec` amount `c.getValue % w` on the `2*w`-bit
  concatenation `a ++ b`, which `bv_decide` bit-blasts as a barrel shifter and
  proves equal to the RISC-V register expression. No manual reduction is needed.
-/

/--
  Prove the correctness of the `fshl` rotate lowering: a funnel shift with
  identical data operands is a rotate-left, lowered to `rol`.
-/
theorem fshl_rol_refinement {a c : LLVM.Int 64} :
    (Data.LLVM.Int.fshl a a c) ⊒
      (RISCV.Reg.toInt (Data.RISCV.rol (LLVM.Int.toReg c) (LLVM.Int.toReg a)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `fshr` rotate lowering: a funnel shift with
  identical data operands is a rotate-right, lowered to `ror`.
-/
theorem fshr_ror_refinement {a c : LLVM.Int 64} :
    (Data.LLVM.Int.fshr a a c) ⊒
      (RISCV.Reg.toInt (Data.RISCV.ror (LLVM.Int.toReg c) (LLVM.Int.toReg a)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the constant-amount `fshr` lowering: a rotate-right is
  lowered to `rori a, (c mod 64)`. The immediate `c mod 64` is the low six bits of
  the (constant) shift amount.
-/
theorem fshr_rori_refinement {a c : LLVM.Int 64} :
    (Data.LLVM.Int.fshr a a c) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.rori (BitVec.extractLsb 5 0 (LLVM.Int.toReg c).val) (LLVM.Int.toReg a)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the constant-amount `fshl` lowering: a rotate-left by
  `c` is a rotate-right by `64 - c`, lowered to `rori a, (-(c mod 64))` (there is no
  `roli`, so the immediate is negated mod 64).
-/
theorem fshl_rori_refinement {a c : LLVM.Int 64} :
    (Data.LLVM.Int.fshl a a c) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.rori (-(BitVec.extractLsb 5 0 (LLVM.Int.toReg c).val)) (LLVM.Int.toReg a)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the constant-amount i32 `fshr` lowering (`roriw` selection):
  a 32-bit rotate-right is lowered to `roriw a, (c mod 32)`. The immediate is the low
  five bits of the (constant) shift amount.
-/
theorem fshr_roriw_refinement {a c : LLVM.Int 32} :
    (Data.LLVM.Int.fshr a a c) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.roriw (BitVec.extractLsb 4 0 (LLVM.Int.toReg c).val) (LLVM.Int.toReg a)) 32) := by
  veir_bv_decide

/--
  Prove the correctness of the constant-amount i32 `fshl` lowering (`roliw` selection):
  a 32-bit rotate-left by `c` is a rotate-right by `32 - c`, lowered to
  `roriw a, (-(c mod 32))` (there is no `roliw`, so the immediate is negated mod 32).
-/
theorem fshl_roriw_refinement {a c : LLVM.Int 32} :
    (Data.LLVM.Int.fshl a a c) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.roriw (-(BitVec.extractLsb 4 0 (LLVM.Int.toReg c).val)) (LLVM.Int.toReg a)) 32) := by
  veir_bv_decide

/--
  Prove the correctness of the general (distinct-operand) i64 `fshl` lowering,
  mirroring LLVM's generic `expandFunnelShift`:

    fshl a b c = (a << c) | ((b >> 1) >> ~c)

  The RISC-V shifts mask their amount modulo 64, so `c` stands for `c % 64` and
  `~c` (the `xori a, -1`) stands for `(63 - c % 64)`; the `>> 1` pre-shift keeps
  the `c % 64 = 0` case (where `shy` shifts fully out to zero) correct.
-/
theorem fshlGeneral_refinement {a b c : LLVM.Int 64} :
    (Data.LLVM.Int.fshl a b c) ⊒
      (RISCV.Reg.toInt
        (let x0 := LLVM.Int.toReg a
         let y0 := LLVM.Int.toReg b
         let z0 := LLVM.Int.toReg c
         let notz := Data.RISCV.xori (BitVec.ofInt 12 (-1)) z0
         let shx := Data.RISCV.sll z0 x0
         let y1 := Data.RISCV.srli 1#6 y0
         let shy := Data.RISCV.srl notz y1
         Data.RISCV.or shx shy) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the general (distinct-operand) i64 `fshr` lowering,
  mirroring LLVM's generic `expandFunnelShift`:

    fshr a b c = ((a << 1) << ~c) | (b >> c)

  The RISC-V shifts mask their amount modulo 64, so `c` stands for `c % 64` and
  `~c` (the `xori a, -1`) stands for `(63 - c % 64)`; the `<< 1` pre-shift keeps
  the `c % 64 = 0` case (where `shx` shifts fully out to zero) correct.
-/
theorem fshrGeneral_refinement {a b c : LLVM.Int 64} :
    (Data.LLVM.Int.fshr a b c) ⊒
      (RISCV.Reg.toInt
        (let x0 := LLVM.Int.toReg a
         let y0 := LLVM.Int.toReg b
         let z0 := LLVM.Int.toReg c
         let notz := Data.RISCV.xori (BitVec.ofInt 12 (-1)) z0
         let x1 := Data.RISCV.slli 1#6 x0
         let shx := Data.RISCV.sll notz x1
         let shy := Data.RISCV.srl z0 y0
         Data.RISCV.or shx shy) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the general (distinct-operand) i32 `fshl` lowering: the
  i64 expansion using the `w`-suffixed shifts (`sllw`/`srliw`/`srlw`), which mask
  their amount modulo 32. Only the low 32 bits of the `or` are observed (`toInt …
  32`), so the sign-extension the `w` shifts produce is harmless.
-/
theorem fshlGeneralw_refinement {a b c : LLVM.Int 32} :
    (Data.LLVM.Int.fshl a b c) ⊒
      (RISCV.Reg.toInt
        (let x0 := LLVM.Int.toReg a
         let y0 := LLVM.Int.toReg b
         let z0 := LLVM.Int.toReg c
         let notz := Data.RISCV.xori (BitVec.ofInt 12 (-1)) z0
         let shx := Data.RISCV.sllw z0 x0
         let y1 := Data.RISCV.srliw 1#5 y0
         let shy := Data.RISCV.srlw notz y1
         Data.RISCV.or shx shy) 32) := by
  veir_bv_decide

/--
  Prove the correctness of the general (distinct-operand) i32 `fshr` lowering: the
  i64 expansion using the `w`-suffixed shifts (`slliw`/`sllw`/`srlw`), which mask
  their amount modulo 32. Only the low 32 bits of the `or` are observed (`toInt …
  32`), so the sign-extension the `w` shifts produce is harmless.
-/
theorem fshrGeneralw_refinement {a b c : LLVM.Int 32} :
    (Data.LLVM.Int.fshr a b c) ⊒
      (RISCV.Reg.toInt
        (let x0 := LLVM.Int.toReg a
         let y0 := LLVM.Int.toReg b
         let z0 := LLVM.Int.toReg c
         let notz := Data.RISCV.xori (BitVec.ofInt 12 (-1)) z0
         let x1 := Data.RISCV.slliw 1#5 x0
         let shx := Data.RISCV.sllw notz x1
         let shy := Data.RISCV.srlw z0 y0
         Data.RISCV.or shx shy) 32) := by
  veir_bv_decide

/--
  Soundness of the `slti` selection (`PatGprSimm12<setlt, SLTI>`):
  `riscv.slt rs1 (riscv.li imm)` -> `riscv.slti rs1 imm`, valid when the `li` value is
  the 64-bit sign extension of the 12-bit immediate used by `slti`.
-/
theorem fold_slt_li_to_slti_sound (rs1 : Reg) (imm : BitVec 12) :
    slt (li (imm.signExtend 64)) rs1 = slti imm rs1 := by
  rw [val_inj]
  simp only [val_slt, val_slti, val_li]

/--
  Soundness of the `sltiu` selection (`PatGprSimm12<setult, SLTIU>`):
  `riscv.sltu rs1 (riscv.li imm)` -> `riscv.sltiu rs1 imm`. As in the ISA semantics for
  `sltiu`, the immediate is sign-extended before the unsigned comparison.
-/
theorem fold_sltu_li_to_sltiu_sound (rs1 : Reg) (imm : BitVec 12) :
    sltu (li (imm.signExtend 64)) rs1 = sltiu imm rs1 := by
  veir_bv_decide

/-! ### Immediate-selection folds

  Each lemma below states that the immediate-form RISC-V instruction selected by
  `isel-sdag-riscv64` computes the same value as materializing the constant with
  `li` and using the reg-reg form. Composed with the reg-reg lowering refinements
  above (and `constant_refinement`), this is the soundness obligation for selecting
  the immediate form directly from the LLVM op, mirroring LLVM's `PatGprImm` family.
-/

/-- imm12 binops: `OP (li imm.sext) rs1 = OPi imm rs1` (sign-extended immediate). -/
theorem fold_add_li_to_addi_sound (rs1 : Reg) (imm : BitVec 12) :
    add (li (imm.signExtend 64)) rs1 = addi imm rs1 := by
  veir_bv_decide

theorem fold_or_li_to_ori_sound (rs1 : Reg) (imm : BitVec 12) :
    or (li (imm.signExtend 64)) rs1 = ori imm rs1 := by
  veir_bv_decide

theorem fold_and_li_to_andi_sound (rs1 : Reg) (imm : BitVec 12) :
    and (li (imm.signExtend 64)) rs1 = andi imm rs1 := by
  veir_bv_decide

theorem fold_xor_li_to_xori_sound (rs1 : Reg) (imm : BitVec 12) :
    xor (li (imm.signExtend 64)) rs1 = xori imm rs1 := by
  veir_bv_decide

/-- uimm6 shifts: `SH (li shamt) rs1 = SHi shamt rs1` (reg-reg form uses the low 6 bits). -/
theorem fold_sll_li_to_slli_sound (rs1 : Reg) (shamt : BitVec 6) :
    sll (li (shamt.setWidth 64)) rs1 = slli shamt rs1 := by
  veir_bv_decide

theorem fold_srl_li_to_srli_sound (rs1 : Reg) (shamt : BitVec 6) :
    srl (li (shamt.setWidth 64)) rs1 = srli shamt rs1 := by
  veir_bv_decide

theorem fold_sra_li_to_srai_sound (rs1 : Reg) (shamt : BitVec 6) :
    sra (li (shamt.setWidth 64)) rs1 = srai shamt rs1 := by
  veir_bv_decide

/-- Word `*w` forms: `OPw (li imm) rs1 = OPiw imm rs1`. -/
theorem fold_addw_li_to_addiw_sound (rs1 : Reg) (imm : BitVec 12) :
    addw (li (imm.signExtend 64)) rs1 = addiw imm rs1 := by
  veir_bv_decide

theorem fold_sllw_li_to_slliw_sound (rs1 : Reg) (shamt : BitVec 5) :
    sllw (li (shamt.setWidth 64)) rs1 = slliw shamt rs1 := by
  veir_bv_decide

theorem fold_srlw_li_to_srliw_sound (rs1 : Reg) (shamt : BitVec 5) :
    srlw (li (shamt.setWidth 64)) rs1 = srliw shamt rs1 := by
  veir_bv_decide

theorem fold_sraw_li_to_sraiw_sound (rs1 : Reg) (shamt : BitVec 5) :
    sraw (li (shamt.setWidth 64)) rs1 = sraiw shamt rs1 := by
  veir_bv_decide

theorem fold_rorw_li_to_roriw_sound (rs1 : Reg) (shamt : BitVec 5) :
    rorw (li (shamt.setWidth 64)) rs1 = roriw shamt rs1 := by
  veir_bv_decide

/-- Zbs single-bit forms. The bit `shamt` is set/cleared/inverted/extracted; the
    materialized constant is the single-bit mask `1 <<< shamt` (or its complement). -/
theorem fold_or_singlebit_to_bseti_sound (rs1 : Reg) (shamt : BitVec 6) :
    or (li (((1#1).zeroExtend 64) <<< shamt)) rs1 = bseti shamt rs1 := by
  veir_bv_decide

theorem fold_xor_singlebit_to_binvi_sound (rs1 : Reg) (shamt : BitVec 6) :
    xor (li (((1#1).zeroExtend 64) <<< shamt)) rs1 = binvi shamt rs1 := by
  veir_bv_decide

theorem fold_and_clearbit_to_bclri_sound (rs1 : Reg) (shamt : BitVec 6) :
    and (li (~~~(((1#1).setWidth 64) <<< shamt))) rs1 = bclri shamt rs1 := by
  veir_bv_decide

/-- `andi 1 (srli shamt rs1) = bexti shamt rs1`: `(x >> shamt) & 1` extracts bit `shamt`. -/
theorem fold_bexti_sound (rs1 : Reg) (shamt : BitVec 6) :
    andi 1 (srli shamt rs1) = bexti shamt rs1 := by
  veir_bv_decide

/-- Zba: `sll (li shamt) (zextw rs1) = slliuw shamt rs1` (shift of a 32-bit zero-extend). -/
theorem fold_slliuw_sound (rs1 : Reg) (shamt : BitVec 6) :
    sll (li (shamt.setWidth 64)) (zextw rs1) = slliuw shamt rs1 := by
  veir_bv_decide

theorem freeze_refinement {a : LLVM.Int 64} :
    (Data.LLVM.Int.freeze a) ⊒
      (RISCV.Reg.toInt (LLVM.Int.toReg a) 64) := by
  veir_bv_decide

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
      (RISCV.Reg.toInt
        (let x0 := LLVM.Int.toReg x
         let m1 := Data.RISCV.li 0x55555555#64
         let x1 := Data.RISCV.or
           (Data.RISCV.slli 1#6 (Data.RISCV.and m1 x0))
           (Data.RISCV.and m1 (Data.RISCV.srli 1#6 x0))
         let m2 := Data.RISCV.li 0x33333333#64
         let x2 := Data.RISCV.or
           (Data.RISCV.slli 2#6 (Data.RISCV.and m2 x1))
           (Data.RISCV.and m2 (Data.RISCV.srli 2#6 x1))
         let m4 := Data.RISCV.li 0x0f0f0f0f#64
         let x3 := Data.RISCV.or
           (Data.RISCV.slli 4#6 (Data.RISCV.and m4 x2))
           (Data.RISCV.and m4 (Data.RISCV.srli 4#6 x2))
         Data.RISCV.srli 32#6 (Data.RISCV.rev8 x3)) 32) := by
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

theorem select_czeroeqz_refinement_32 {c : LLVM.Int 1} {t : LLVM.Int 32} :
    (Data.LLVM.Int.select c t (LLVM.Int.constant 32 0)) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.czeroeqz (LLVM.Int.toReg c) (LLVM.Int.toReg t)) 32) := by
  veir_bv_decide

theorem select_czeronez_refinement_32 {c : LLVM.Int 1} {f : LLVM.Int 32} :
    (Data.LLVM.Int.select c (LLVM.Int.constant 32 0) f) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.czeronez (LLVM.Int.toReg c) (LLVM.Int.toReg f)) 32) := by
  veir_bv_decide

theorem select_refinement_32 {c : LLVM.Int 1} {t f : LLVM.Int 32} :
    (Data.LLVM.Int.select c t f) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.or
          (Data.RISCV.czeronez (LLVM.Int.toReg c) (LLVM.Int.toReg f))
          (Data.RISCV.czeroeqz (LLVM.Int.toReg c) (LLVM.Int.toReg t))) 32) := by
  veir_bv_decide

theorem select_refinement_1 {c : LLVM.Int 1} {t f : LLVM.Int 1} :
    (Data.LLVM.Int.select c t f) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.or
          (Data.RISCV.czeronez (LLVM.Int.toReg c) (LLVM.Int.toReg f))
          (Data.RISCV.czeroeqz (LLVM.Int.toReg c) (LLVM.Int.toReg t))) 1) := by
  veir_bv_decide

theorem freeze_refinement_32 {a : LLVM.Int 32} :
    (Data.LLVM.Int.freeze a) ⊒
      (RISCV.Reg.toInt (LLVM.Int.toReg a) 32) := by
  veir_bv_decide
