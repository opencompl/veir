import Veir.Dialects.Arith.Puddle

namespace Veir.ArithCanonicalize.IntegerSupport

open Veir Veir.Data

/-- Normalizing an integer attribute never changes its modular bits. -/
theorem normalize_bits (ty : IntegerType) (v : Int) :
    BitVec.ofInt ty.bitwidth (IntegerAttr.ofInt v ty).value = BitVec.ofInt ty.bitwidth v := by
  simp only [IntegerAttr.ofInt, IntegerAttr.normalizeValue]
  by_cases h : ty.signedness = IntegerType.Signedness.unsigned ∨ ty = IntegerType.signless 1
  · rw [ite_eq_left h, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
    simp
  · rw [ite_eq_right h]
    exact BitVec.ofInt_toInt

/-- A subtraction after a potentially overflowing addition refines the modular
    addition by the folded difference. -/
theorem sub_add_refines (w : Nat) (x : LLVM.Int w) (a b : BitVec w)
    (an au sn su : Bool) :
    RuntimeValue.int w (LLVM.Int.sub (LLVM.Int.add x (.val a) an au) (.val b) sn su) ⊒
      .int w (LLVM.Int.add x (.val (a - b))) := by
  have bv_id (x a b : BitVec w) : x + a - b = x + (a - b) := by
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  cases x with
  | poison => simp [RuntimeValue.isRefinedBy, LLVM.Int.sub, LLVM.Int.add, isRefinedBy,
      Id.run]
  | val xv =>
    cases an <;> cases au <;> cases sn <;> cases su <;>
      simp [RuntimeValue.isRefinedBy, LLVM.Int.sub, LLVM.Int.add, isRefinedBy,
        Id.run, pure, bv_id] <;> grind

end Veir.ArithCanonicalize.IntegerSupport
