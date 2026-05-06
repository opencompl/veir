import Veir.Data.LLVM.Int.Basic
import Veir.Data.LLVM.Int.Simp
import Veir.Data.Refinement

/-!
  This file contains some of the `InstCombine` tests retrieved from Lean-MLIR,
  instantiated for integers with width `64`:
  https://github.com/opencompl/lean-mlir/blob/main/SSA/Projects/InstCombine/AliveStatements.lean

  We exclude the tests comprising unsupported operations, such as `neg` and `not`.
-/

/-- We introduce a tactic to automatically prove all the lemmas. -/
macro "llvm_bv_decide" : tactic =>
  `(tactic| ((try simp [llvm_toBitVec]; try bv_decide); all_goals sorry))


/-
  `LLVM.not` is not supported in

  theorem bv_AddSub_1043 :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.add (Veir.Data.LLVM.Int.add (Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and e_1 e) e) (Veir.Data.LLVM.Int.constant 64 1)) e_2 ⊑ Veir.Data.LLVM.Int.sub e_2 (Veir.Data.LLVM.Int.or e_1 (Veir.Data.LLVM.Int.not e)) := by
-/

theorem bv_AddSub_1152 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 1), Veir.Data.LLVM.Int.add e_1 e ⊑ Veir.Data.LLVM.Int.xor e_1 e := by
  llvm_bv_decide

theorem bv_AddSub_1156 :
    ∀ (e : Veir.Data.LLVM.Int 64), (Veir.Data.LLVM.Int.add e e) ⊑
        (Veir.Data.LLVM.Int.shl e (Veir.Data.LLVM.Int.constant 64 1)) := by
  llvm_bv_decide

theorem bv_AddSub_1164 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.add (Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 0) e) e_1 ⊑ Veir.Data.LLVM.Int.sub e_1 e := by
  llvm_bv_decide

theorem bv_AddSub_1165 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.add (Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 0) e) (Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 0) e_1) ⊑ Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 0) (Veir.Data.LLVM.Int.add e e_1) := by
  llvm_bv_decide

theorem bv_AddSub_1176 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.add e (Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 0) e_1) ⊑ Veir.Data.LLVM.Int.sub e e_1 := by
  llvm_bv_decide

theorem bv_AddSub_1202 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.add (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_1 ⊑ Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.sub e_1 (Veir.Data.LLVM.Int.constant 64 1)) e := by
  llvm_bv_decide

theorem bv_AddSub_1295 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.add (Veir.Data.LLVM.Int.and e e_1) (Veir.Data.LLVM.Int.xor e e_1) ⊑ Veir.Data.LLVM.Int.or e e_1 := by
  llvm_bv_decide

theorem bv_AddSub_1309 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.add (Veir.Data.LLVM.Int.and e e_1) (Veir.Data.LLVM.Int.or e e_1) ⊑ Veir.Data.LLVM.Int.add e e_1 := by
  llvm_bv_decide

theorem bv_AddSub_1539 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.sub e_1 (Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 0) e) ⊑ Veir.Data.LLVM.Int.add e_1 e := by
  llvm_bv_decide

/-
  `LLVM.neg` is not supported in

  theorem bv_AddSub_1539_2 :
      ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.sub e e_1 ⊑ Veir.Data.LLVM.Int.add e (Veir.Data.LLVM.Int.neg e_1) := by
-/

theorem bv_AddSub_1556 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 1), Veir.Data.LLVM.Int.sub e_1 e ⊑ Veir.Data.LLVM.Int.xor e_1 e := by
  llvm_bv_decide

theorem bv_AddSub_1560 :
    ∀ (e : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 (-1)) e ⊑ Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1)) := by
  llvm_bv_decide

theorem bv_AddSub_1564 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.sub e_1 (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) ⊑ Veir.Data.LLVM.Int.add e (Veir.Data.LLVM.Int.add e_1 (Veir.Data.LLVM.Int.constant 64 1)) := by
  llvm_bv_decide

theorem bv_AddSub_1574 :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.sub e_1 (Veir.Data.LLVM.Int.add e e_2) ⊑ Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.sub e_1 e_2) e := by
  llvm_bv_decide

theorem bv_AddSub_1614 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.sub e_1 (Veir.Data.LLVM.Int.add e_1 e) ⊑
      Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 0) e := by
  llvm_bv_decide

theorem bv_AddSub_1619 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.sub e_1 e) e_1 ⊑ Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 0) e := by
  llvm_bv_decide

theorem bv_AddSub_1624 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.or e e_1) (Veir.Data.LLVM.Int.xor e e_1) ⊑ Veir.Data.LLVM.Int.and e e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_135 :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.xor e e_1) e_2 ⊑ Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and e e_2) (Veir.Data.LLVM.Int.and e_1 e_2) := by
  llvm_bv_decide

theorem bv_AndOrXor_144 :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.or e e_1) e_2 ⊑ Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.or e (Veir.Data.LLVM.Int.and e_1 e_2)) e_2 := by
  llvm_bv_decide

theorem bv_AndOrXor_698 :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.icmp
            (Veir.Data.LLVM.Int.and e e_1) (Veir.Data.LLVM.Int.constant 64 0) Veir.Data.LLVM.IntPred.eq)
          (Veir.Data.LLVM.Int.icmp (Veir.Data.LLVM.Int.and e e_2) (Veir.Data.LLVM.Int.constant 64 0) Veir.Data.LLVM.IntPred.eq) ⊑
        Veir.Data.LLVM.Int.icmp  (Veir.Data.LLVM.Int.and e (Veir.Data.LLVM.Int.or e_1 e_2)) (Veir.Data.LLVM.Int.constant 64 0) Veir.Data.LLVM.IntPred.eq := by
  llvm_bv_decide

theorem bv_AndOrXor_709 :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.icmp  (Veir.Data.LLVM.Int.and e e_1) e_1 Veir.Data.LLVM.IntPred.eq) (Veir.Data.LLVM.Int.icmp (Veir.Data.LLVM.Int.and e e_2) e_2 Veir.Data.LLVM.IntPred.eq) ⊑
        Veir.Data.LLVM.Int.icmp (Veir.Data.LLVM.Int.and e (Veir.Data.LLVM.Int.or e_1 e_2)) (Veir.Data.LLVM.Int.or e_1 e_2) Veir.Data.LLVM.IntPred.eq := by
  llvm_bv_decide

theorem bv_AndOrXor_716 :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.icmp (Veir.Data.LLVM.Int.and e e_1) e Veir.Data.LLVM.IntPred.eq) (Veir.Data.LLVM.Int.icmp  (Veir.Data.LLVM.Int.and e e_2) e Veir.Data.LLVM.IntPred.eq) ⊑
        Veir.Data.LLVM.Int.icmp (Veir.Data.LLVM.Int.and e (Veir.Data.LLVM.Int.and e_1 e_2)) e Veir.Data.LLVM.IntPred.eq := by
  llvm_bv_decide

theorem bv_AndOrXor_794 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.icmp e e_1 Veir.Data.LLVM.IntPred.sgt)
        (Veir.Data.LLVM.Int.icmp e e_1 Veir.Data.LLVM.IntPred.ne) ⊑ Veir.Data.LLVM.Int.icmp e e_1 Veir.Data.LLVM.IntPred.sgt := by
  llvm_bv_decide

theorem bv_AndOrXor_827 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.icmp  e (Veir.Data.LLVM.Int.constant 64 0) Veir.Data.LLVM.IntPred.eq)
            (Veir.Data.LLVM.Int.icmp e_1 (Veir.Data.LLVM.Int.constant 64 0) Veir.Data.LLVM.IntPred.eq) ⊑
        Veir.Data.LLVM.Int.icmp (Veir.Data.LLVM.Int.or e e_1) (Veir.Data.LLVM.Int.constant 64 0) Veir.Data.LLVM.IntPred.eq := by
  llvm_bv_decide

theorem bv_AndOrXor_887_2 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.icmp e e_1 Veir.Data.LLVM.IntPred.eq) (Veir.Data.LLVM.Int.icmp e e_1 Veir.Data.LLVM.IntPred.ne) ⊑ Veir.Data.LLVM.Int.constant 1 0 := by
  llvm_bv_decide

theorem bv_AndOrXor_1230__A__B___A__B :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) ⊑
        Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.or e e_1) (Veir.Data.LLVM.Int.constant 64 (-1)) := by
  llvm_bv_decide

theorem bv_AndOrXor_1241_AB__AB__AB :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.or e e_1) (Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and e e_1) (Veir.Data.LLVM.Int.constant 64 (-1))) ⊑ Veir.Data.LLVM.Int.xor e e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_1247_AB__AB__AB :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and e e_1) (Veir.Data.LLVM.Int.constant 64 (-1))) (Veir.Data.LLVM.Int.or e e_1) ⊑ Veir.Data.LLVM.Int.xor e e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_1253_A__AB___A__B :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.xor e e_1) e ⊑ Veir.Data.LLVM.Int.and e (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) := by
  llvm_bv_decide

theorem bv_AndOrXor_1280_ABA___AB :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_1) e ⊑ Veir.Data.LLVM.Int.and e e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_1288_A__B__B__C__A___A__B__C :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.xor e e_2) (Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.xor e_2 e_1) e) ⊑
        Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.xor e e_2) (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) := by
  llvm_bv_decide

theorem bv_AndOrXor_1294_A__B__A__B___A__B :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.or e e_1) (Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_1) ⊑ Veir.Data.LLVM.Int.and e e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_1683_1 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.icmp e e_1 Veir.Data.LLVM.IntPred.ugt ) (Veir.Data.LLVM.Int.icmp e e_1 Veir.Data.LLVM.IntPred.eq ) ⊑ Veir.Data.LLVM.Int.icmp e e_1 Veir.Data.LLVM.IntPred.uge := by
  llvm_bv_decide

theorem bv_AndOrXor_1683_2 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.icmp e e_1 Veir.Data.LLVM.IntPred.uge)
    (Veir.Data.LLVM.Int.icmp e e_1 Veir.Data.LLVM.IntPred.ne ) ⊑ Veir.Data.LLVM.Int.constant 1 1 := by
  llvm_bv_decide

theorem bv_AndOrXor_1704 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.icmp  e_1 (Veir.Data.LLVM.Int.constant 64 0) Veir.Data.LLVM.IntPred.eq)
        (Veir.Data.LLVM.Int.icmp  e e_1 Veir.Data.LLVM.IntPred.ult) ⊑
        Veir.Data.LLVM.Int.icmp  (Veir.Data.LLVM.Int.add e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) e Veir.Data.LLVM.IntPred.uge := by
  llvm_bv_decide

theorem bv_AndOrXor_1705 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.icmp  e_1 (Veir.Data.LLVM.Int.constant 64 0) Veir.Data.LLVM.IntPred.eq)
      (Veir.Data.LLVM.Int.icmp  e_1 e Veir.Data.LLVM.IntPred.ugt) ⊑
        Veir.Data.LLVM.Int.icmp  (Veir.Data.LLVM.Int.add e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) e Veir.Data.LLVM.IntPred.uge := by
  llvm_bv_decide

theorem bv_AndOrXor_1733 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.icmp  e (Veir.Data.LLVM.Int.constant 64 0) Veir.Data.LLVM.IntPred.ne)
        (Veir.Data.LLVM.Int.icmp  e_1 (Veir.Data.LLVM.Int.constant 64 0) Veir.Data.LLVM.IntPred.ne) ⊑
        Veir.Data.LLVM.Int.icmp  (Veir.Data.LLVM.Int.or e e_1) (Veir.Data.LLVM.Int.constant 64 0) Veir.Data.LLVM.IntPred.ne := by
  llvm_bv_decide

/-
  `LLVM.not` is not supported in

  theorem bv_AndOrXor_2063__X__C1__C2____X__C2__C1__C2 :
      ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.xor e e_1) e_2 ⊑
      Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.or e e_2) (Veir.Data.LLVM.Int.and e_1 (Veir.Data.LLVM.Int.not e_2)) := by
-/

theorem bv_AndOrXor_2113___A__B__A___A__B :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_1) e ⊑ Veir.Data.LLVM.Int.or e e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_2118___A__B__A___A__B :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.and e e_1) (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) ⊑ Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_2123___A__B__A__B___A__B :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.and e (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1)))) (Veir.Data.LLVM.Int.xor e e_1) ⊑ Veir.Data.LLVM.Int.xor e e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_2188 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.and e (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1)))) (Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_1) ⊑
        Veir.Data.LLVM.Int.xor e e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_2231__A__B__B__C__A___A__B__C :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.xor e e_2) (Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.xor e_2 e_1) e) ⊑ Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.xor e e_2) e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_2243__B__C__A__B___B__A__C :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.or e_2 e_1) e) e_2 ⊑ Veir.Data.LLVM.Int.or e_2 (Veir.Data.LLVM.Int.and e e_1) := by
  llvm_bv_decide

theorem bv_AndOrXor_2247__A__B__A__B :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) ⊑
        Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and e e_1) (Veir.Data.LLVM.Int.constant 64 (-1)) := by
  llvm_bv_decide

theorem bv_AndOrXor_2263 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.or e_1 (Veir.Data.LLVM.Int.xor e_1 e) ⊑ Veir.Data.LLVM.Int.or e_1 e := by
  llvm_bv_decide

theorem bv_AndOrXor_2264 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.or e (Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_1) ⊑ Veir.Data.LLVM.Int.or e (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) := by
  llvm_bv_decide

theorem bv_AndOrXor_2265 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.and e e_1) (Veir.Data.LLVM.Int.xor e e_1) ⊑ Veir.Data.LLVM.Int.or e e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_2284 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.or e (Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.or e e_1) (Veir.Data.LLVM.Int.constant 64 (-1))) ⊑ Veir.Data.LLVM.Int.or e (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) := by
  llvm_bv_decide

theorem bv_AndOrXor_2285 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.or e (Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.xor e e_1) (Veir.Data.LLVM.Int.constant 64 (-1))) ⊑ Veir.Data.LLVM.Int.or e (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) := by
  llvm_bv_decide

theorem bv_AndOrXor_2297 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.and e e_1) (Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_1) ⊑
        Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_2367 :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.or e e_1) e_2 ⊑ Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.or e e_2) e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_2416 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_1) (Veir.Data.LLVM.Int.constant 64 (-1)) ⊑
        Veir.Data.LLVM.Int.or e (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) := by
  llvm_bv_decide

theorem bv_AndOrXor_2417 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_1) (Veir.Data.LLVM.Int.constant 64 (-1)) ⊑
        Veir.Data.LLVM.Int.and e (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) := by
  llvm_bv_decide

theorem bv_AndOrXor_2429 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and e_1 e) (Veir.Data.LLVM.Int.constant 64 (-1)) ⊑
        Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) := by
  llvm_bv_decide

theorem bv_AndOrXor_2430 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.or e_1 e) (Veir.Data.LLVM.Int.constant 64 (-1)) ⊑
        Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) := by
  llvm_bv_decide

theorem bv_AndOrXor_2443 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.ashr (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) e) (Veir.Data.LLVM.Int.constant 64 (-1)) ⊑ Veir.Data.LLVM.Int.ashr e_1 e := by
  llvm_bv_decide

theorem bv_AndOrXor_2453 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.icmp  e_1 e Veir.Data.LLVM.IntPred.slt) (Veir.Data.LLVM.Int.constant 1 (-1)) ⊑ Veir.Data.LLVM.Int.icmp  e_1 e Veir.Data.LLVM.IntPred.sge := by
  llvm_bv_decide

theorem bv_AndOrXor_2475 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.sub e_1 e) (Veir.Data.LLVM.Int.constant 64 (-1)) ⊑ Veir.Data.LLVM.Int.add e (Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 (-1)) e_1) := by
  llvm_bv_decide

theorem bv_AndOrXor_2486 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.add e e_1) (Veir.Data.LLVM.Int.constant 64 (-1)) ⊑ Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 (-1)) e_1) e := by
  llvm_bv_decide

theorem bv_AndOrXor_2581__BAB___A__B :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.or e e_1) e_1 ⊑ Veir.Data.LLVM.Int.and e (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1))) := by
  llvm_bv_decide

theorem bv_AndOrXor_2587__BAA___B__A :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and e e_1) e_1 ⊑ Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_2595 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and e e_1) (Veir.Data.LLVM.Int.or e e_1) ⊑ Veir.Data.LLVM.Int.xor e e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_2607 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.or e (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1)))) (Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_1) ⊑
        Veir.Data.LLVM.Int.xor e e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_2617 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and e (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1)))) (Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_1) ⊑
        Veir.Data.LLVM.Int.xor e e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_2627 :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.xor e e_1) (Veir.Data.LLVM.Int.or e e_2) ⊑ Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) e_2) e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_2647 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and e e_1) (Veir.Data.LLVM.Int.xor e e_1) ⊑ Veir.Data.LLVM.Int.or e e_1 := by
  llvm_bv_decide

theorem bv_AndOrXor_2658 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and e (Veir.Data.LLVM.Int.xor e_1 (Veir.Data.LLVM.Int.constant 64 (-1)))) (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 64 (-1))) ⊑
        Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and e e_1) (Veir.Data.LLVM.Int.constant 64 (-1)) := by
  llvm_bv_decide

theorem bv_AndOrXor_2663 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.icmp  e e_1 Veir.Data.LLVM.IntPred.ule) (Veir.Data.LLVM.Int.icmp  e e_1 Veir.Data.LLVM.IntPred.ne) ⊑ Veir.Data.LLVM.Int.icmp  e e_1 Veir.Data.LLVM.IntPred.uge:= by
  llvm_bv_decide

theorem bv_152 :
    ∀ (e : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.mul e (Veir.Data.LLVM.Int.constant 64 (-1)) ⊑ Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 0) e := by
  llvm_bv_decide

/--
  expected error: The SAT solver timed out while solving the problem.

  theorem bv_229 :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.mul (Veir.Data.LLVM.Int.add e e_1) e_2 ⊑ Veir.Data.LLVM.Int.add (Veir.Data.LLVM.Int.mul e e_2) (Veir.Data.LLVM.Int.mul e_1 e_2) := by
  llvm_bv_decide
-/


theorem bv_239 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.mul (Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 0) e_1) (Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 0) e) ⊑ Veir.Data.LLVM.Int.mul e_1 e := by
  llvm_bv_decide

theorem bv_275 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 5), Veir.Data.LLVM.Int.mul (Veir.Data.LLVM.Int.udiv e_1 e) e ⊑ Veir.Data.LLVM.Int.sub e_1 (Veir.Data.LLVM.Int.urem e_1 e) := by
  llvm_bv_decide

theorem bv_275_2 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 5), Veir.Data.LLVM.Int.mul (Veir.Data.LLVM.Int.sdiv e_1 e) e ⊑ Veir.Data.LLVM.Int.sub e_1 (Veir.Data.LLVM.Int.srem e_1 e) := by
  llvm_bv_decide

theorem bv_276 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 5), Veir.Data.LLVM.Int.mul (Veir.Data.LLVM.Int.sdiv e_1 e) (Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 5 0) e) ⊑ Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.srem e_1 e) e_1 := by
  llvm_bv_decide

theorem bv_276_2 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 5), Veir.Data.LLVM.Int.mul (Veir.Data.LLVM.Int.udiv e_1 e) (Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 5 0) e) ⊑ Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.urem e_1 e) e_1 := by
  llvm_bv_decide

theorem bv_283 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 1), Veir.Data.LLVM.Int.mul e_1 e ⊑ Veir.Data.LLVM.Int.and e_1 e := by
  llvm_bv_decide

theorem bv_290__292 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.mul (Veir.Data.LLVM.Int.shl (Veir.Data.LLVM.Int.constant 64 1) e) e_1 ⊑ Veir.Data.LLVM.Int.shl e_1 e := by
  llvm_bv_decide

theorem bv_820 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 9), Veir.Data.LLVM.Int.sdiv (Veir.Data.LLVM.Int.sub e (Veir.Data.LLVM.Int.srem e e_1)) e_1 ⊑ Veir.Data.LLVM.Int.sdiv e e_1 := by
  llvm_bv_decide

theorem bv_820' :
    ∀ (e e_1 : Veir.Data.LLVM.Int 9), Veir.Data.LLVM.Int.udiv (Veir.Data.LLVM.Int.sub e (Veir.Data.LLVM.Int.urem e e_1)) e_1 ⊑ Veir.Data.LLVM.Int.udiv e e_1 := by
  llvm_bv_decide

theorem bv_1030 :
    ∀ (e : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.sdiv e (Veir.Data.LLVM.Int.constant 64 (-1)) ⊑ Veir.Data.LLVM.Int.sub (Veir.Data.LLVM.Int.constant 64 0) e := by
  llvm_bv_decide

theorem bv_Select_858 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 1),
      Veir.Data.LLVM.Int.select e (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 1 (-1))) e_1 ⊑ Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 1 (-1))) e_1 := by
  llvm_bv_decide

theorem bv_Select_859' :
    ∀ (e e_1 : Veir.Data.LLVM.Int 1),
      Veir.Data.LLVM.Int.select e e_1 (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 1 (-1))) ⊑ Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.constant 1 (-1))) e_1 := by
  llvm_bv_decide

theorem bv_select_1100 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.select (Veir.Data.LLVM.Int.constant 1 1) e_1 e ⊑ e_1 := by
  llvm_bv_decide

theorem bv_Select_1105 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.select (Veir.Data.LLVM.Int.constant 1 0) e_1 e ⊑ e := by
  llvm_bv_decide

theorem bv_InstCombineShift__239 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.lshr (Veir.Data.LLVM.Int.shl e e_1) e_1 ⊑ Veir.Data.LLVM.Int.and e (Veir.Data.LLVM.Int.lshr (Veir.Data.LLVM.Int.constant 64 (-1)) e_1) := by
  llvm_bv_decide

theorem bv_InstCombineShift__279 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.shl (Veir.Data.LLVM.Int.lshr e e_1) e_1 ⊑ Veir.Data.LLVM.Int.and e (Veir.Data.LLVM.Int.shl (Veir.Data.LLVM.Int.constant 64 (-1)) e_1) := by
  llvm_bv_decide

theorem bv_InstCombineShift__440 :
    ∀ (e e_1 e_2 e_3 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.shl (Veir.Data.LLVM.Int.xor e (Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.lshr e_1 e_2) e_3)) e_2 ⊑
        Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.and e_1 (Veir.Data.LLVM.Int.shl e_3 e_2)) (Veir.Data.LLVM.Int.shl e e_2) := by
  llvm_bv_decide

theorem bv_InstCombineShift__476 :
    ∀ (e e_1 e_2 e_3 : Veir.Data.LLVM.Int 64),
      Veir.Data.LLVM.Int.shl (Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.and (Veir.Data.LLVM.Int.lshr e_1 e_2) e_3) e) e_2 ⊑
        Veir.Data.LLVM.Int.or (Veir.Data.LLVM.Int.and e_1 (Veir.Data.LLVM.Int.shl e_3 e_2)) (Veir.Data.LLVM.Int.shl e e_2) := by
  llvm_bv_decide

theorem bv_InstCombineShift__497 :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.lshr (Veir.Data.LLVM.Int.xor e e_2) e_1 ⊑ Veir.Data.LLVM.Int.xor (Veir.Data.LLVM.Int.lshr e e_1) (Veir.Data.LLVM.Int.lshr e_2 e_1) := by
  llvm_bv_decide

theorem bv_InstCombineShift__497''' :
    ∀ (e e_1 e_2 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.shl (Veir.Data.LLVM.Int.add e e_2) e_1 ⊑ Veir.Data.LLVM.Int.add (Veir.Data.LLVM.Int.shl e e_1) (Veir.Data.LLVM.Int.shl e_2 e_1) := by
  llvm_bv_decide

theorem bv_InstCombineShift__582 :
    ∀ (e e_1 : Veir.Data.LLVM.Int 64), Veir.Data.LLVM.Int.lshr (Veir.Data.LLVM.Int.shl e e_1) e_1 ⊑ Veir.Data.LLVM.Int.and e (Veir.Data.LLVM.Int.lshr (Veir.Data.LLVM.Int.constant 64 (-1)) e_1) := by
  llvm_bv_decide
