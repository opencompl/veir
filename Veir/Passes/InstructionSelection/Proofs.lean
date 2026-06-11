import Veir.Data.RISCV.Reg.Basic
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Data.LLVM.Int.Basic
import Veir.Data.LLVM.Int.Simp
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
  A tactic to unfold the semantics of operations on `LLVM.Int` and on `RISCV.Reg` to
  bitvectors, such that `bv_decide` can prove the correctness of the refinement relation
  over instruction selection patterns.
-/
macro "refine_bv_decide" : tactic =>
  `(tactic| ((try simp only [llvm_toBitVec, reg_toBitVec]; try simp [LLVM.Int.getValue_eq_getValueD, -BitVec.extractLsb_toNat]; try bv_decide)))


/--
  Prove the correctness of the `constant` lowering pattern.

  We do not need to consider the poison case, as the semantics of `llvm_constant`
  are always concrete in the interpreter.
-/
theorem constant_refinement {v : Int}:
    (LLVM.Int.constant 64 v) ⊒ (RISCV.Reg.toInt (Data.RISCV.li (BitVec.ofInt 64 v)) 64) := by
  refine_bv_decide

/--
  Prove the correctness of the `add` lowering pattern.
-/
theorem add_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.add x y) ⊒
      (RISCV.Reg.toInt (Data.RISCV.add (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  refine_bv_decide

/--
  Prove the correctness of the `and` lowering pattern.
-/
theorem and_refinement{x y : LLVM.Int 64} :
    (Data.LLVM.Int.and x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.and (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  refine_bv_decide

/--
  Prove the correctness of the `ashr` lowering pattern.
-/
theorem ashr_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.ashr x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.sra (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  refine_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `eq`.
-/
theorem icmp_refinement_eq {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.eq) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltiu 1#12 (Data.RISCV.xor (LLVM.Int.toReg y) (LLVM.Int.toReg x))) 1) := by
  refine_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `ne`.
-/
theorem icmp_refinement_ne {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ne) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltu (Data.RISCV.xor (LLVM.Int.toReg y) (LLVM.Int.toReg x)) (Data.RISCV.li 0#64)) 1) := by
  refine_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `slt`.
-/
theorem icmp_refinement_slt {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.slt) ⊒
      (RISCV.Reg.toInt (Data.RISCV.slt (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 1) := by
  refine_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `sle`.
-/
theorem icmp_refinement_sle {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.sle) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.slt (LLVM.Int.toReg x) (LLVM.Int.toReg y))) 1) := by
  refine_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `sgt`.
-/
theorem icmp_refinement_sgt {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.sgt) ⊒
      (RISCV.Reg.toInt (Data.RISCV.slt (LLVM.Int.toReg x) (LLVM.Int.toReg y)) 1) := by
  refine_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `sge`.
-/
theorem icmp_refinement_sge {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.sge) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.slt (LLVM.Int.toReg y) (LLVM.Int.toReg x))) 1) := by
  refine_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `ult`.
-/
theorem icmp_refinement_ult {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ult) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltu (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 1) := by
  refine_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `ule`.
-/
theorem icmp_refinement_ule {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ule) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.sltu (LLVM.Int.toReg x) (LLVM.Int.toReg y))) 1) := by
  refine_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `ugt`.
-/
theorem icmp_refinement_ugt {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.ugt) ⊒
      (RISCV.Reg.toInt ((Data.RISCV.sltu (LLVM.Int.toReg x) (LLVM.Int.toReg y))) 1) := by
  refine_bv_decide

/--
  Prove the correctness of the `icmp` lowering pattern with `uge`.
-/
theorem icmp_refinement_uge {x y : LLVM.Int 64} :
    (Data.LLVM.Int.icmp x y LLVM.IntPred.uge) ⊒
      (RISCV.Reg.toInt (Data.RISCV.xori 1#12 (Data.RISCV.sltu (LLVM.Int.toReg y) (LLVM.Int.toReg x))) 1) := by
  refine_bv_decide

/--
  Prove the correctness of the `or` lowering pattern.
-/
theorem or_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.or x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.or (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  refine_bv_decide

/--
  Prove the correctness of the `xor` lowering pattern.
-/
theorem xor_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.xor x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.xor (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  refine_bv_decide

/--
  Prove the correctness of the `mul` lowering pattern.
-/
theorem mul_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.mul x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.mul (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  refine_bv_decide

/--
  Prove the correctness of the `sdiv` lowering pattern.
-/
theorem sdiv_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.sdiv x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.div (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  refine_bv_decide

/--
  Prove the correctness of the `udiv` lowering pattern.
-/
theorem udiv_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.udiv x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.divu (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  refine_bv_decide

/--
  Prove the correctness of the `udiv` lowering pattern.
-/
theorem srem_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.srem x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.rem (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  refine_bv_decide

/--
  Prove the correctness of the `udiv` lowering pattern.
-/
theorem urem_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.urem x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.remu (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  refine_bv_decide

/--
  Prove the correctness of the `udiv` lowering pattern.
-/
theorem sub_refinement {x y : LLVM.Int 64} :
    (Data.LLVM.Int.sub x y) ⊒ (RISCV.Reg.toInt (Data.RISCV.sub (LLVM.Int.toReg y) (LLVM.Int.toReg x)) 64) := by
  refine_bv_decide

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
  simp only [llvm_toBitVec, reg_toBitVec, Data.RISCV.orcByte]
  simp [LLVM.Int.getValue_eq_getValueD, -BitVec.extractLsb_toNat]
  bv_decide

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
  simp only [llvm_toBitVec, reg_toBitVec, Data.RISCV.orcByte]
  simp [LLVM.Int.getValue_eq_getValueD, -BitVec.extractLsb_toNat]
  bv_decide

theorem orcb_refinement_y2 {z : LLVM.Int 64} :
    (Data.LLVM.Int.sub
        (Data.LLVM.Int.shl (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0404040404040404))
          (LLVM.Int.constant 64 6))
        (Data.LLVM.Int.lshr (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0404040404040404))
          (LLVM.Int.constant 64 2)))
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.orcb (LLVM.Int.toReg
            (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0404040404040404)))) 64 := by
  simp only [llvm_toBitVec, reg_toBitVec, Data.RISCV.orcByte]
  simp [LLVM.Int.getValue_eq_getValueD, -BitVec.extractLsb_toNat]
  bv_decide

theorem orcb_refinement_y3 {z : LLVM.Int 64} :
    (Data.LLVM.Int.sub
        (Data.LLVM.Int.shl (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0808080808080808))
          (LLVM.Int.constant 64 5))
        (Data.LLVM.Int.lshr (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0808080808080808))
          (LLVM.Int.constant 64 3)))
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.orcb (LLVM.Int.toReg
            (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x0808080808080808)))) 64 := by
  simp only [llvm_toBitVec, reg_toBitVec, Data.RISCV.orcByte]
  simp [LLVM.Int.getValue_eq_getValueD, -BitVec.extractLsb_toNat]
  bv_decide

theorem orcb_refinement_y4 {z : LLVM.Int 64} :
    (Data.LLVM.Int.sub
        (Data.LLVM.Int.shl (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x1010101010101010))
          (LLVM.Int.constant 64 4))
        (Data.LLVM.Int.lshr (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x1010101010101010))
          (LLVM.Int.constant 64 4)))
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.orcb (LLVM.Int.toReg
            (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x1010101010101010)))) 64 := by
  simp only [llvm_toBitVec, reg_toBitVec, Data.RISCV.orcByte]
  simp [LLVM.Int.getValue_eq_getValueD, -BitVec.extractLsb_toNat]
  bv_decide

theorem orcb_refinement_y5 {z : LLVM.Int 64} :
    (Data.LLVM.Int.sub
        (Data.LLVM.Int.shl (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x2020202020202020))
          (LLVM.Int.constant 64 3))
        (Data.LLVM.Int.lshr (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x2020202020202020))
          (LLVM.Int.constant 64 5)))
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.orcb (LLVM.Int.toReg
            (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x2020202020202020)))) 64 := by
  simp only [llvm_toBitVec, reg_toBitVec, Data.RISCV.orcByte]
  simp [LLVM.Int.getValue_eq_getValueD, -BitVec.extractLsb_toNat]
  bv_decide

theorem orcb_refinement_y6 {z : LLVM.Int 64} :
    (Data.LLVM.Int.sub
        (Data.LLVM.Int.shl (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x4040404040404040))
          (LLVM.Int.constant 64 2))
        (Data.LLVM.Int.lshr (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x4040404040404040))
          (LLVM.Int.constant 64 6)))
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.orcb (LLVM.Int.toReg
            (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x4040404040404040)))) 64 := by
  simp only [llvm_toBitVec, reg_toBitVec, Data.RISCV.orcByte]
  simp [LLVM.Int.getValue_eq_getValueD, -BitVec.extractLsb_toNat]
  bv_decide

theorem orcb_refinement_y7 {z : LLVM.Int 64} :
    (Data.LLVM.Int.sub
        (Data.LLVM.Int.shl (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x8080808080808080))
          (LLVM.Int.constant 64 1))
        (Data.LLVM.Int.lshr (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x8080808080808080))
          (LLVM.Int.constant 64 7)))
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.orcb (LLVM.Int.toReg
            (Data.LLVM.Int.and z (LLVM.Int.constant 64 0x8080808080808080)))) 64 := by
  simp only [llvm_toBitVec, reg_toBitVec, Data.RISCV.orcByte]
  simp [LLVM.Int.getValue_eq_getValueD, -BitVec.extractLsb_toNat]
  bv_decide
