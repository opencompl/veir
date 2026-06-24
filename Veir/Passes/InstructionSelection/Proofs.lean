import Veir.Data.RISCV.Reg.Basic
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Data.LLVM.Int.Basic
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.LLVM.Int.Bitblast
import Veir.Data.Casting
import Veir.Data.Refinement
import Std.Tactic.BVDecide

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
  Prove the correctness of the `add` lowering pattern.
-/
theorem add_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.add x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.add (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `and` lowering pattern.
-/
theorem and_refinement{x y : LLVM.Int 64} :
    (Data.LLVM.Int.and x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.and (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
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

/--
  Prove the correctness of the `or` lowering pattern.
-/
theorem or_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.or x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.or (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  veir_bv_decide

/--
  Prove the correctness of the `xor` lowering pattern.
-/
theorem xor_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.xor x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.xor (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
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
  rcases c with cv | _ <;> rcases t with tv | _ <;> rcases f with fv | _ <;>
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

/-!
  The funnel-shift rotate lowerings cannot use `veir_bv_decide` directly: its
  simp normalization rewrites the BitVec shift in the funnel-shift semantics into
  a *symbolic* `Nat` shift (`c.toNat % w`) on the `2*w`-bit concatenation, which
  `bv_decide` cannot bit-blast. Instead we reduce the refinement to a pure-BitVec
  goal by hand (discharging the poison cases from the non-poison hypothesis on the
  result, and keeping the shift amounts as `BitVec`s) and finish with bare
  `bv_decide`.
-/

/--
  Prove the correctness of the `fshl` rotate lowering: a funnel shift with
  identical data operands is a rotate-left, lowered to `rol`.
-/
theorem fshl_rol_refinement {a c : LLVM.Int 64} :
    (Data.LLVM.Int.fshl a a c) ⊒
      (RISCV.Reg.toInt (Data.RISCV.rol (LLVM.Int.toReg c) (LLVM.Int.toReg a)) 64) := by
  rw [Data.LLVM.Int.isRefinedBy_iff]
  refine ⟨fun _ => toInt_isPoison, fun h1 _ => ?_⟩
  have hp := Data.LLVM.Int.isPoison_fshl a a c
  rw [h1] at hp
  have ha : a.isPoison = false := by grind
  have hc : c.isPoison = false := by grind
  rw [Data.LLVM.Int.getValue_fshl a a c h1, toInt_getValue]
  cases a with
  | poison => simp [Data.LLVM.Int.isPoison] at ha
  | val av =>
  cases c with
  | poison => simp [Data.LLVM.Int.isPoison] at hc
  | val cv =>
    simp only [Data.LLVM.Int.getValue, Data.RISCV.rol, LLVM.Int.toReg,
      BitVec.truncate_eq_setWidth]
    bv_decide

/--
  Prove the correctness of the `fshr` rotate lowering: a funnel shift with
  identical data operands is a rotate-right, lowered to `ror`.
-/
theorem fshr_ror_refinement {a c : LLVM.Int 64} :
    (Data.LLVM.Int.fshr a a c) ⊒
      (RISCV.Reg.toInt (Data.RISCV.ror (LLVM.Int.toReg c) (LLVM.Int.toReg a)) 64) := by
  rw [Data.LLVM.Int.isRefinedBy_iff]
  refine ⟨fun _ => toInt_isPoison, fun h1 _ => ?_⟩
  have hp := Data.LLVM.Int.isPoison_fshr a a c
  rw [h1] at hp
  have ha : a.isPoison = false := by grind
  have hc : c.isPoison = false := by grind
  rw [Data.LLVM.Int.getValue_fshr a a c h1, toInt_getValue]
  cases a with
  | poison => simp [Data.LLVM.Int.isPoison] at ha
  | val av =>
  cases c with
  | poison => simp [Data.LLVM.Int.isPoison] at hc
  | val cv =>
    simp only [Data.LLVM.Int.getValue, Data.RISCV.ror, LLVM.Int.toReg,
      BitVec.truncate_eq_setWidth]
    bv_decide

/--
  Prove the correctness of the constant-amount `fshr` lowering: a rotate-right is
  lowered to `rori a, (c mod 64)`. The immediate `c mod 64` is the low six bits of
  the (constant) shift amount.
-/
theorem fshr_rori_refinement {a c : LLVM.Int 64} :
    (Data.LLVM.Int.fshr a a c) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.rori (BitVec.extractLsb 5 0 (LLVM.Int.toReg c).val) (LLVM.Int.toReg a)) 64) := by
  rw [Data.LLVM.Int.isRefinedBy_iff]
  refine ⟨fun _ => toInt_isPoison, fun h1 _ => ?_⟩
  have hp := Data.LLVM.Int.isPoison_fshr a a c
  rw [h1] at hp
  have ha : a.isPoison = false := by grind
  have hc : c.isPoison = false := by grind
  rw [Data.LLVM.Int.getValue_fshr a a c h1, toInt_getValue]
  cases a with
  | poison => simp [Data.LLVM.Int.isPoison] at ha
  | val av =>
  cases c with
  | poison => simp [Data.LLVM.Int.isPoison] at hc
  | val cv =>
    simp only [Data.LLVM.Int.getValue, Data.RISCV.rori, LLVM.Int.toReg,
      BitVec.truncate_eq_setWidth]
    bv_decide

/--
  Prove the correctness of the constant-amount `fshl` lowering: a rotate-left by
  `c` is a rotate-right by `64 - c`, lowered to `rori a, (-(c mod 64))` (there is no
  `roli`, so the immediate is negated mod 64).
-/
theorem fshl_rori_refinement {a c : LLVM.Int 64} :
    (Data.LLVM.Int.fshl a a c) ⊒
      (RISCV.Reg.toInt
        (Data.RISCV.rori (-(BitVec.extractLsb 5 0 (LLVM.Int.toReg c).val)) (LLVM.Int.toReg a)) 64) := by
  rw [Data.LLVM.Int.isRefinedBy_iff]
  refine ⟨fun _ => toInt_isPoison, fun h1 _ => ?_⟩
  have hp := Data.LLVM.Int.isPoison_fshl a a c
  rw [h1] at hp
  have ha : a.isPoison = false := by grind
  have hc : c.isPoison = false := by grind
  rw [Data.LLVM.Int.getValue_fshl a a c h1, toInt_getValue]
  cases a with
  | poison => simp [Data.LLVM.Int.isPoison] at ha
  | val av =>
  cases c with
  | poison => simp [Data.LLVM.Int.isPoison] at hc
  | val cv =>
    simp only [Data.LLVM.Int.getValue, Data.RISCV.rori, LLVM.Int.toReg,
      BitVec.truncate_eq_setWidth]
    bv_decide
