module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Refinement
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import Veir.ForLean

open Veir.Data.LLVM

/-!
  Lemmas about `LLVM.Int` used by the fold-table correctness proofs.
-/

public section

namespace Veir.Data.LLVM.Int

@[simp]
theorem add_zero {w : Nat} (x : Int w) (nsw nuw : Bool) :
    add x (.val (0#w)) nsw nuw = x := by
  cases x <;> simp [add, Id.run, BitVec.saddOverflow_eq, BitVec.uaddOverflow, BitVec.isLt]

/-- Adding zero never overflows, so the carry may be refined to concrete false. -/
@[simp]
theorem uaddOverflowFlag_zero {w : Nat} (x : Int w) :
    uaddOverflowFlag x (.val (0#w)) ⊒ .val (0#1) := by
  cases x <;> simp [uaddOverflowFlag, Id.run, BitVec.uaddOverflow_eq, isRefinedBy,
    BitVec.msb_eq_getLsbD_last]

end Veir.Data.LLVM.Int

end
