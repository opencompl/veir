import Veir.Dialects.Arith.Puddle
import Veir.Data.LLVM.Int.Lemmas

/-! Flag-aware refinement for the Arith canonicalization `x + y * -1`. -/

namespace Veir.ArithCanonicalize

open Veir
open Veir.Data

/-- A flagged add of a flagged multiplication by minus one refines plain subtraction. -/
theorem add_mul_neg_one_refines (w : Nat) (x y : LLVM.Int w)
    (mulNsw mulNuw addNsw addNuw : Bool) :
    RuntimeValue.int w
      (LLVM.Int.add x (LLVM.Int.mul y (.val (BitVec.ofInt w (-1))) mulNsw mulNuw)
        addNsw addNuw) ⊒
      .int w (LLVM.Int.sub x y) := by
  have hbits (a b : BitVec w) : a + b * BitVec.ofInt w (-1) = a - b := by
    have hneg : BitVec.ofInt w (-1) = -1#w := by simp [BitVec.ofInt_neg]
    rw [hneg, BitVec.mul_comm, ← BitVec.neg_eq_neg_one_mul]
    exact BitVec.add_neg_eq_sub
  cases x <;> cases y <;>
    simp [RuntimeValue.isRefinedBy, LLVM.Int.add, LLVM.Int.mul, LLVM.Int.sub,
      isRefinedBy, Id.run, pure]
  grind

/-- The commuted outer add has the same refinement. -/
private theorem add_comm_flags (w : Nat) (x y : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.add x y nsw nuw = LLVM.Int.add y x nsw nuw := by
  cases x <;> cases y <;>
    simp [LLVM.Int.add, BitVec.add_comm, BitVec.saddOverflow_comm,
      BitVec.uaddOverflow_comm]

theorem add_mul_neg_one_comm_refines (w : Nat) (x y : LLVM.Int w)
    (mulNsw mulNuw addNsw addNuw : Bool) :
    RuntimeValue.int w
      (LLVM.Int.add (LLVM.Int.mul y (.val (BitVec.ofInt w (-1))) mulNsw mulNuw)
        x addNsw addNuw) ⊒
      .int w (LLVM.Int.sub x y) := by
  rw [add_comm_flags]
  exact add_mul_neg_one_refines _ _ _ _ _ _ _

end Veir.ArithCanonicalize
