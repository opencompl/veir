import Veir.Data.LLVM.Int.Bitblast
import Veir.Data.LLVM.Int.Basic

/-!
  This file contains some of the `InstCombine` tests retrieved from Lean-MLIR,
  instantiated for integers with width `64`:
  https://github.com/opencompl/lean-mlir/blob/main/SSA/Projects/InstCombine/AliveStatements.lean

  We exclude the tests comprising unsupported operations, such as `neg` and `not`.
-/

open Veir.Data.LLVM
namespace Veir.Data.Int

theorem bv_AddSub_1152 :
    ∀ (e e_1 : Int 1), LLVM.Int.add e_1 e = LLVM.Int.xor e_1 e := by
  simp [llvm_toBitVec]
  bv_decide

theorem bv_AddSub_1156 :
    ∀ (e : Int 64), LLVM.Int.add e e =
      LLVM.Int.shl e (LLVM.Int.constant (w := 64) 1) := by
    simp [llvm_toBitVec]
    bv_decide

-- theorem bv_AddSub_1164 :
--     ∀ (e e_1 : Int 64), LLVM.Int.LLVM.Int.add (LLVM.Int.LLVM.Int.add (LLVM.Int.constant (w := 64) (v := 0)) e) e_1 =
--       LLVM.Int.LLVM.Int.add e_1 e := by
--     simp [llvm_toBitVec]
--     bv_decide

theorem bv_AddSub_1165 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.add (LLVM.Int.add (LLVM.Int.constant (w := 64) 0) e) (LLVM.Int.add (LLVM.Int.constant (w := 64) 0) e_1) = LLVM.Int.add (LLVM.Int.constant (w := 64) 0) (LLVM.Int.add e e_1) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AddSub_1176 :
    ∀ (e e_1 : Int 64), LLVM.Int.add e (LLVM.Int.add (LLVM.Int.constant (w := 64) 0) e_1) = LLVM.Int.add e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AddSub_1202 :
    ∀ (e e_1 : Int 64), LLVM.Int.add (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_1 = LLVM.Int.add (LLVM.Int.add e_1 (LLVM.Int.constant (w := 64) 1)) e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AddSub_1295 :
    ∀ (e e_1 : Int 64), LLVM.Int.add (LLVM.Int.and e e_1) (LLVM.Int.xor e e_1) = LLVM.Int.or e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AddSub_1309 :
    ∀ (e e_1 : Int 64), LLVM.Int.add (LLVM.Int.and e e_1) (LLVM.Int.or e e_1) = LLVM.Int.add e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AddSub_1539 :
    ∀ (e e_1 : Int 64), LLVM.Int.add e_1 (LLVM.Int.add (LLVM.Int.constant (w := 64) 0) e) = LLVM.Int.add e_1 e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AddSub_1556 :
    ∀ (e e_1 : Int 1), LLVM.Int.add e_1 e = LLVM.Int.xor e_1 e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AddSub_1560 :
    ∀ (e : Int 64), LLVM.Int.add (LLVM.Int.constant (w := 64) (v := -1)) e = LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1)) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AddSub_1564 :
    ∀ (e e_1 : Int 64), LLVM.Int.add e_1 (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) = LLVM.Int.add e (LLVM.Int.add e_1 (LLVM.Int.constant (w := 64) 1)) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AddSub_1574 :
    ∀ (e e_1 e_2 : Int 64), LLVM.Int.add e_1 (LLVM.Int.add e e_2) = LLVM.Int.add (LLVM.Int.add e_1 e_2) e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AddSub_1614 :
    ∀ (e e_1 : Int 64), LLVM.Int.add e_1 (LLVM.Int.add e_1 e) = LLVM.Int.add (LLVM.Int.constant (w := 64) 0) e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AddSub_1619 :
    ∀ (e e_1 : Int 64), LLVM.Int.add (LLVM.Int.add e_1 e) e_1 = LLVM.Int.add (LLVM.Int.constant (w := 64) 0) e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AddSub_1624 :
    ∀ (e e_1 : Int 64), LLVM.Int.add (LLVM.Int.or e e_1) (LLVM.Int.xor e e_1) = LLVM.Int.and e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_135 :
    ∀ (e e_1 e_2 : Int 64), LLVM.Int.and (LLVM.Int.xor e e_1) e_2 = LLVM.Int.xor (LLVM.Int.and e e_2) (LLVM.Int.and e_1 e_2) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_144 :
    ∀ (e e_1 e_2 : Int 64), LLVM.Int.and (LLVM.Int.or e e_1) e_2 = LLVM.Int.and (LLVM.Int.or e (LLVM.Int.and e_1 e_2)) e_2 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_698 :
    ∀ (e e_1 e_2 : Int 64),
      LLVM.Int.and (LLVM.Int.icmp (LLVM.Int.and e e_1) (LLVM.Int.constant (w := 64) 0) IntPred.eq)
          (LLVM.Int.icmp (LLVM.Int.and e e_2) (LLVM.Int.constant (w := 64) 0) IntPred.eq) =
        LLVM.Int.icmp (LLVM.Int.and e (LLVM.Int.or e_1 e_2)) (LLVM.Int.constant (w := 64) 0) IntPred.eq := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_709 :
    ∀ (e e_1 e_2 : Int 64),
      LLVM.Int.and (LLVM.Int.icmp (LLVM.Int.and e e_1) e_1 IntPred.eq)
        (LLVM.Int.icmp (LLVM.Int.and e e_2) e_2 IntPred.eq) =
        LLVM.Int.icmp (LLVM.Int.and e (LLVM.Int.or e_1 e_2)) (LLVM.Int.or e_1 e_2) IntPred.eq := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_716 :
    ∀ (e e_1 e_2 : Int 64),
      LLVM.Int.and (LLVM.Int.icmp (LLVM.Int.and e e_1) e IntPred.eq)
        (LLVM.Int.icmp (LLVM.Int.and e e_2) e IntPred.eq) =
        LLVM.Int.icmp (LLVM.Int.and e (LLVM.Int.and e_1 e_2)) e IntPred.eq := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_794 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.and (LLVM.Int.icmp e e_1 IntPred.sgt)
        (LLVM.Int.icmp e e_1 IntPred.ne) = LLVM.Int.icmp e e_1 IntPred.sgt := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_827 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.and (LLVM.Int.icmp  e (LLVM.Int.constant (w := 64) 0) IntPred.eq) (LLVM.Int.icmp e_1 (LLVM.Int.constant (w := 64) 0) IntPred.eq) =
        LLVM.Int.icmp (LLVM.Int.or e e_1) (LLVM.Int.constant (w := 64) 0) IntPred.eq := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_887_2 :
    ∀ (e e_1 : Int 64), LLVM.Int.and (LLVM.Int.icmp  e e_1 IntPred.eq)
      (LLVM.Int.icmp  e e_1 IntPred.ne) = LLVM.Int.constant (w := 1) (v := 1) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_1230__A__B___A__B :
    ∀ (e e_1 : Int 64),
      LLVM.Int.and (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1))) =
        LLVM.Int.xor (LLVM.Int.or e e_1) (LLVM.Int.constant (w := 64) (v := -1)) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_1241_AB__AB__AB :
    ∀ (e e_1 : Int 64), LLVM.Int.and (LLVM.Int.or e e_1) (LLVM.Int.xor (LLVM.Int.and e e_1) (LLVM.Int.constant (w := 64) (v := -1))) = LLVM.Int.xor e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_1247_AB__AB__AB :
    ∀ (e e_1 : Int 64), LLVM.Int.and (LLVM.Int.xor (LLVM.Int.and e e_1) (LLVM.Int.constant (w := 64) (v := -1))) (LLVM.Int.or e e_1) = LLVM.Int.xor e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_1253_A__AB___A__B :
    ∀ (e e_1 : Int 64), LLVM.Int.and (LLVM.Int.xor e e_1) e = LLVM.Int.and e (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1))) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_1280_ABA___AB :
    ∀ (e e_1 : Int 64), LLVM.Int.and (LLVM.Int.or (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_1) e = LLVM.Int.and e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_1288_A__B__B__C__A___A__B__C :
    ∀ (e e_1 e_2 : Int 64),
      LLVM.Int.and (LLVM.Int.xor e e_2) (LLVM.Int.xor (LLVM.Int.xor e_2 e_1) e) =
        LLVM.Int.and (LLVM.Int.xor e e_2) (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1))) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_1294_A__B__A__B___A__B :
    ∀ (e e_1 : Int 64), LLVM.Int.and (LLVM.Int.or e e_1) (LLVM.Int.xor (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_1) = LLVM.Int.and e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_1683_1 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.or (LLVM.Int.icmp  e e_1 IntPred.ugt) (LLVM.Int.icmp e e_1 IntPred.eq) =
        LLVM.Int.icmp  e e_1 IntPred.uge := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_1683_2 :
    ∀ (e e_1 : Int 64), LLVM.Int.or (LLVM.Int.icmp e e_1 IntPred.uge) (LLVM.Int.icmp  e e_1 IntPred.ne) =
      LLVM.Int.constant (w := 1) 1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_1704 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.or (LLVM.Int.icmp  e_1 (LLVM.Int.constant (w := 64) 0) IntPred.eq)
        (LLVM.Int.icmp  e e_1 IntPred.ult) =
        LLVM.Int.icmp  (LLVM.Int.add e_1 (LLVM.Int.constant (w := 64) (v := -1))) e IntPred.uge := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_1705 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.or (LLVM.Int.icmp  e_1 (LLVM.Int.constant (w := 64) 0) IntPred.eq)
        (LLVM.Int.icmp  e_1 e IntPred.ugt) =
        LLVM.Int.icmp (LLVM.Int.add e_1 (LLVM.Int.constant (w := 64) (v := -1))) e IntPred.uge := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_1733 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.or (LLVM.Int.icmp  e (LLVM.Int.constant (w := 64) 0) IntPred.ne)
      (LLVM.Int.icmp  e_1 (LLVM.Int.constant (w := 64) 0) IntPred.ne) =
        LLVM.Int.icmp  (LLVM.Int.or e e_1) (LLVM.Int.constant (w := 64) 0) IntPred.ne := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2063__X__C1__C2____X__C2__C1__C2 :
    ∀ (e e_1 e_2 : Int 64), LLVM.Int.or (LLVM.Int.xor e e_1) e_2 = LLVM.Int.xor (LLVM.Int.or e e_2) (LLVM.Int.and e_1 (not e_2)) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2113___A__B__A___A__B :
    ∀ (e e_1 : Int 64), LLVM.Int.or (LLVM.Int.and (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_1) e = LLVM.Int.or e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2118___A__B__A___A__B :
    ∀ (e e_1 : Int 64),
      LLVM.Int.or (LLVM.Int.and e e_1) (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) = LLVM.Int.or (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2123___A__B__A__B___A__B :
    ∀ (e e_1 : Int 64), LLVM.Int.or (LLVM.Int.and e (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1)))) (LLVM.Int.xor e e_1) = LLVM.Int.xor e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2188 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.or (LLVM.Int.and e (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1)))) (LLVM.Int.and (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_1) =
        LLVM.Int.xor e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2231__A__B__B__C__A___A__B__C :
    ∀ (e e_1 e_2 : Int 64), LLVM.Int.or (LLVM.Int.xor e e_2) (LLVM.Int.xor (LLVM.Int.xor e_2 e_1) e) = LLVM.Int.or (LLVM.Int.xor e e_2) e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2243__B__C__A__B___B__A__C :
    ∀ (e e_1 e_2 : Int 64), LLVM.Int.or (LLVM.Int.and (LLVM.Int.or e_2 e_1) e) e_2 = LLVM.Int.or e_2 (LLVM.Int.and e e_1) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2247__A__B__A__B :
    ∀ (e e_1 : Int 64),
      LLVM.Int.or (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1))) =
        LLVM.Int.xor (LLVM.Int.and e e_1) (LLVM.Int.constant (w := 64) (v := -1)) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2263 :
    ∀ (e e_1 : Int 64), LLVM.Int.or e_1 (LLVM.Int.xor e_1 e) = LLVM.Int.or e_1 e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2264 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.or e (LLVM.Int.xor (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_1) = LLVM.Int.or e (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1))) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2265 :
    ∀ (e e_1 : Int 64), LLVM.Int.or (LLVM.Int.and e e_1) (LLVM.Int.xor e e_1) = LLVM.Int.or e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2284 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.or e (LLVM.Int.xor (LLVM.Int.or e e_1) (LLVM.Int.constant (w := 64) (v := -1))) = LLVM.Int.or e (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1))) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2285 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.or e (LLVM.Int.xor (LLVM.Int.xor e e_1) (LLVM.Int.constant (w := 64) (v := -1))) = LLVM.Int.or e (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1))) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2297 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.or (LLVM.Int.and e e_1) (LLVM.Int.xor (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_1) =
        LLVM.Int.xor (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2367 :
    ∀ (e e_1 e_2 : Int 64), LLVM.Int.or (LLVM.Int.or e e_1) e_2 = LLVM.Int.or (LLVM.Int.or e e_2) e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2416 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.xor (LLVM.Int.and (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_1) (LLVM.Int.constant (w := 64) (v := -1)) =
        LLVM.Int.or e (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1))) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2417 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.xor (LLVM.Int.or (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_1) (LLVM.Int.constant (w := 64) (v := -1)) =
        LLVM.Int.and e (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1))) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2429 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.xor (LLVM.Int.and e_1 e) (LLVM.Int.constant (w := 64) (v := -1)) =
        LLVM.Int.or (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1))) (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2430 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.xor (LLVM.Int.or e_1 e) (LLVM.Int.constant (w := 64) (v := -1)) =
        LLVM.Int.and (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1))) (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2443 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.xor (LLVM.Int.ashr (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1))) e) (LLVM.Int.constant (w := 64) (v := -1)) = LLVM.Int.ashr e_1 e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2453 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.xor (LLVM.Int.icmp  e_1 e IntPred.slt) (LLVM.Int.constant (w := 1) (v := -1)) =
        LLVM.Int.icmp  e_1 e IntPred.sge := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2475 :
    ∀ (e e_1 : Int 64), LLVM.Int.xor (LLVM.Int.add e_1 e) (LLVM.Int.constant (w := 64) (v := -1)) = LLVM.Int.add e (LLVM.Int.add (LLVM.Int.constant (w := 64) (v := -1)) e_1) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2486 :
    ∀ (e e_1 : Int 64), LLVM.Int.xor (LLVM.Int.add e e_1) (LLVM.Int.constant (w := 64) (v := -1)) = LLVM.Int.add (LLVM.Int.add (LLVM.Int.constant (w := 64) (v := -1)) e_1) e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2581__BAB___A__B :
    ∀ (e e_1 : Int 64), LLVM.Int.xor (LLVM.Int.or e e_1) e_1 = LLVM.Int.and e (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1))) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2587__BAA___B__A :
    ∀ (e e_1 : Int 64), LLVM.Int.xor (LLVM.Int.and e e_1) e_1 = LLVM.Int.and (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2595 :
    ∀ (e e_1 : Int 64), LLVM.Int.xor (LLVM.Int.and e e_1) (LLVM.Int.or e e_1) = LLVM.Int.xor e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2607 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.xor (LLVM.Int.or e (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1)))) (LLVM.Int.or (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_1) =
        LLVM.Int.xor e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2617 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.xor (LLVM.Int.and e (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1)))) (LLVM.Int.and (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_1) =
        LLVM.Int.xor e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2627 :
    ∀ (e e_1 e_2 : Int 64),
      LLVM.Int.xor (LLVM.Int.xor e e_1) (LLVM.Int.or e e_2) = LLVM.Int.xor (LLVM.Int.and (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) e_2) e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2647 :
    ∀ (e e_1 : Int 64), LLVM.Int.xor (LLVM.Int.and e e_1) (LLVM.Int.xor e e_1) = LLVM.Int.or e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2658 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.xor (LLVM.Int.and e (LLVM.Int.xor e_1 (LLVM.Int.constant (w := 64) (v := -1)))) (LLVM.Int.xor e (LLVM.Int.constant (w := 64) (v := -1))) =
        LLVM.Int.xor (LLVM.Int.and e e_1) (LLVM.Int.constant (w := 64) (v := -1)) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_AndOrXor_2663 :
    ∀ (e e_1 : Int 64),
      LLVM.Int.xor (LLVM.Int.icmp  e e_1 IntPred.ule) (LLVM.Int.icmp  e e_1 IntPred.ne) =
        LLVM.Int.icmp  e e_1 IntPred.uge := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_152 :
    ∀ (e : Int 64), LLVM.Int.mul e (LLVM.Int.constant (w := 64) (v := -1)) = LLVM.Int.add (LLVM.Int.constant (w := 64) 0) e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_229 :
    ∀ (e e_1 e_2 : Int 64), LLVM.Int.mul (LLVM.Int.add e e_1) e_2 = LLVM.Int.add (LLVM.Int.mul e e_2) (LLVM.Int.mul e_1 e_2) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_239 :
    ∀ (e e_1 : Int 64), LLVM.Int.mul (LLVM.Int.add (LLVM.Int.constant (w := 64) 0) e_1) (LLVM.Int.add (LLVM.Int.constant (w := 64) 0) e) = LLVM.Int.mul e_1 e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_275 :
    ∀ (e e_1 : Int 5), LLVM.Int.mul (LLVM.Int.udiv e_1 e) e = LLVM.Int.add e_1 (LLVM.Int.urem e_1 e) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_275_2 :
    ∀ (e e_1 : Int 5), LLVM.Int.mul (LLVM.Int.sdiv e_1 e) e = LLVM.Int.add e_1 (LLVM.Int.srem e_1 e) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_276 :
    ∀ (e e_1 : Int 5), LLVM.Int.mul (LLVM.Int.sdiv e_1 e) (LLVM.Int.add (LLVM.Int.constant (w := 5) 0) e) =
      LLVM.Int.add (LLVM.Int.srem e_1 e) e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_276_2 :
    ∀ (e e_1 : Int 5), LLVM.Int.mul (LLVM.Int.udiv e_1 e) (LLVM.Int.add
      (LLVM.Int.constant (w := 5) 0) e) = LLVM.Int.add (LLVM.Int.urem e_1 e) e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_283 :
    ∀ (e e_1 : Int 1), LLVM.Int.mul e_1 e = LLVM.Int.and e_1 e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_290__292 :
    ∀ (e e_1 : Int 64), LLVM.Int.mul (LLVM.Int.shl (LLVM.Int.constant (w := 64) 1) e) e_1 = LLVM.Int.shl e_1 e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_820 :
    ∀ (e e_1 : Int 9), LLVM.Int.sdiv (LLVM.Int.add e (LLVM.Int.srem e e_1)) e_1 = LLVM.Int.sdiv e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_820' :
    ∀ (e e_1 : Int 9), LLVM.Int.udiv (LLVM.Int.add e (LLVM.Int.urem e e_1)) e_1 = LLVM.Int.udiv e e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_1030 :
    ∀ (e : Int 64), LLVM.Int.sdiv e (LLVM.Int.constant (w := 64) (v := -1)) = LLVM.Int.add (LLVM.Int.constant (w := 64) 0) e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_Select_858 :
    ∀ (e e_1 : Int 1),
      LLVM.Int.select e (LLVM.Int.xor e (LLVM.Int.constant (w := 1) (v := -1))) e_1 =
          LLVM.Int.and (LLVM.Int.xor e (LLVM.Int.constant (w := 1) (v := -1))) e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_Select_859' :
    ∀ (e e_1 : Int 1),
      LLVM.Int.select e e_1 (LLVM.Int.xor e (LLVM.Int.constant (w := 1) (v := -1))) =
        LLVM.Int.or (LLVM.Int.xor e (LLVM.Int.constant (w := 1) (v := -1))) e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_select_1100 :
    ∀ (e e_1 : Int 64), LLVM.Int.select (LLVM.Int.constant (w := 1) (v := 1)) e_1 e = e_1 := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_Select_1105 :
    ∀ (e e_1 : Int 64), LLVM.Int.select (LLVM.Int.constant (w := 1) (v := 0)) e_1 e = e := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_InstCombineShift__239 :
    ∀ (e e_1 : Int 64), LLVM.Int.lshr (LLVM.Int.shl e e_1) e_1 = LLVM.Int.and e (LLVM.Int.lshr (LLVM.Int.constant (w := 64) (v := -1)) e_1) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_InstCombineShift__279 :
    ∀ (e e_1 : Int 64), LLVM.Int.shl (LLVM.Int.lshr e e_1) e_1 =
        LLVM.Int.and e (LLVM.Int.shl (LLVM.Int.constant (w := 64) (v := -1)) e_1) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_InstCombineShift__440 :
    ∀ (e e_1 e_2 e_3 : Int 64),
      LLVM.Int.shl (LLVM.Int.xor e (LLVM.Int.and (LLVM.Int.lshr e_1 e_2) e_3)) e_2 =
        LLVM.Int.xor (LLVM.Int.and e_1 (LLVM.Int.shl e_3 e_2)) (LLVM.Int.shl e e_2) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_InstCombineShift__476 :
    ∀ (e e_1 e_2 e_3 : Int 64),
      LLVM.Int.shl (LLVM.Int.or (LLVM.Int.and (LLVM.Int.lshr e_1 e_2) e_3) e) e_2 =
        LLVM.Int.or (LLVM.Int.and e_1 (LLVM.Int.shl e_3 e_2)) (LLVM.Int.shl e e_2) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_InstCombineShift__497 :
    ∀ (e e_1 e_2 : Int 64), LLVM.Int.lshr (LLVM.Int.xor e e_2) e_1 = LLVM.Int.xor (LLVM.Int.lshr e e_1) (LLVM.Int.lshr e_2 e_1) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_InstCombineShift__497''' :
    ∀ (e e_1 e_2 : Int 64), LLVM.Int.shl (LLVM.Int.add e e_2) e_1 = LLVM.Int.add (LLVM.Int.shl e e_1) (LLVM.Int.shl e_2 e_1) := by
    simp [llvm_toBitVec]
    bv_decide

theorem bv_InstCombineShift__582 :
    ∀ (e e_1 : Int 64), LLVM.Int.lshr (LLVM.Int.shl e e_1) e_1 = LLVM.Int.and e (LLVM.Int.lshr (LLVM.Int.constant (w := 64) (v := -1)) e_1) := by
    simp [llvm_toBitVec]
    bv_decide
