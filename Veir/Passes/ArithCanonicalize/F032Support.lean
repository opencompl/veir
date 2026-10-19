import Veir.Dialects.Arith.Puddle

namespace Veir.ArithCanonicalize

open Veir Veir.Data
theorem signed_mul_div_cancel (w : Nat) (a b : BitVec w)
    (hmul : ¬BitVec.smulOverflow a b)
    (hb : b ≠ 0#w)
    (hUB : a * b ≠ BitVec.intMin w ∨ b ≠ -1#w) :
    (a * b).sdiv b = a := by
  have hbInt : b.toInt ≠ 0 := by
    intro hz
    apply hb
    apply BitVec.eq_of_toInt_eq
    simpa using hz
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv_of_ne_or_ne _ _ hUB,
    BitVec.toInt_mul_of_not_smulOverflow hmul,
    Int.mul_tdiv_cancel _ hbInt]
theorem signed_mul_div_refines (w : Nat) (a b : LLVM.Int w)
    (nuw exact : Bool)
    (hUB : LLVM.Int.isSignedDivisionUB (LLVM.Int.mul a b true nuw) b = false) :
    RuntimeValue.int w (LLVM.Int.sdiv (LLVM.Int.mul a b true nuw) b exact) ⊒
      .int w a := by
  cases a with
  | poison =>
    simp [RuntimeValue.isRefinedBy, isRefinedBy,
      LLVM.Int.mul, LLVM.Int.sdiv, Id.run]
  | val x =>
    cases b with
    | poison =>
      simp [RuntimeValue.isRefinedBy, isRefinedBy,
        LLVM.Int.mul, LLVM.Int.sdiv, Id.run]
    | val y =>
      by_cases hs : x.smulOverflow y = true
      · simp [RuntimeValue.isRefinedBy, isRefinedBy,
          LLVM.Int.mul, LLVM.Int.sdiv, Id.run, hs]
      · by_cases hu : nuw = true ∧ x.umulOverflow y = true
        · simp [RuntimeValue.isRefinedBy, isRefinedBy,
            LLVM.Int.mul, LLVM.Int.sdiv, Id.run, hs, hu]
        · have hm : LLVM.Int.mul (.val x) (.val y) true nuw = .val (x * y) := by
            simp [LLVM.Int.mul, Id.run, hs, hu]
          rw [hm] at hUB ⊢
          simp [LLVM.Int.isSignedDivisionUB] at hUB
          have hy : y ≠ 0#w := hUB.1
          have hov : ¬(x * y = BitVec.intMin w ∧ y = -1#w) := by
            exact fun ⟨h0,h1⟩ => hUB.2 h1 h0
          have hsafe : x * y ≠ BitVec.intMin w ∨ y ≠ -1#w := by
            by_cases h0 : x * y = BitVec.intMin w
            · exact Or.inr (fun h1 => hov ⟨h0,h1⟩)
            · exact Or.inl h0
          have hcancel : (x * y).sdiv y = x :=
            signed_mul_div_cancel w x y (by simpa using hs) hy hsafe
          by_cases he : exact = true ∧ ¬(x * y).smod y = 0#w
          · simp [RuntimeValue.isRefinedBy, isRefinedBy,
              LLVM.Int.sdiv, Id.run, pure, hy, hov, he]
          · simp [RuntimeValue.isRefinedBy, isRefinedBy,
              LLVM.Int.sdiv, Id.run, hy, hov, he, hcancel]

theorem signed_mul_div_comm_refines (w : Nat) (a b : LLVM.Int w)
    (nuw exact : Bool)
    (hUB : LLVM.Int.isSignedDivisionUB (LLVM.Int.mul b a true nuw) b = false) :
    RuntimeValue.int w (LLVM.Int.sdiv (LLVM.Int.mul b a true nuw) b exact) ⊒
      .int w a := by
  rw [LLVM.Int.mul_comm b a] at hUB ⊢
  exact signed_mul_div_refines w a b nuw exact hUB

end Veir.ArithCanonicalize
