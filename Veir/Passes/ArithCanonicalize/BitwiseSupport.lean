import Veir.Dialects.Arith.Puddle
namespace Veir.ArithCanonicalize.BitwiseSupport

open Veir Veir.Data

theorem folded_bits (ty : IntegerType) (v : BitVec ty.bitwidth) :
    BitVec.ofInt ty.bitwidth (IntegerAttr.ofInt (Int.ofNat v.toNat) ty).value = v := by
  simp only [IntegerAttr.ofInt, IntegerAttr.normalizeValue]
  by_cases h : ty.signedness = IntegerType.Signedness.unsigned ∨ ty = IntegerType.signless 1
  · simp [h, BitVec.ofNat_toNat]
  · simp [h, BitVec.ofInt_toInt, BitVec.ofNat_toNat]

theorem xor_assoc_refines (w : Nat) (x : LLVM.Int w) (a b : BitVec w) :
    RuntimeValue.int w (LLVM.Int.xor (LLVM.Int.xor x (.val a)) (.val b)) ⊒
      .int w (LLVM.Int.xor x (.val (a ^^^ b))) := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.xor, isRefinedBy,
    Id.run, BitVec.xor_assoc]

theorem and_assoc_refines (w : Nat) (x : LLVM.Int w) (a b : BitVec w) :
    RuntimeValue.int w (LLVM.Int.and (LLVM.Int.and x (.val a)) (.val b)) ⊒
      .int w (LLVM.Int.and x (.val (a &&& b))) := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.and, isRefinedBy,
    Id.run, BitVec.and_assoc]

theorem or_assoc_refines (w : Nat) (x : LLVM.Int w) (a b : BitVec w)
    (d0 d1 : Bool) :
    RuntimeValue.int w (LLVM.Int.or (LLVM.Int.or x (.val a) d0) (.val b) d1) ⊒
      .int w (LLVM.Int.or x (.val (a ||| b)) false) := by
  cases x with
  | poison =>
    simp [RuntimeValue.isRefinedBy, LLVM.Int.or, isRefinedBy, Id.run]
  | val xv =>
    cases d0 <;> cases d1 <;>
      (by_cases h0 : xv &&& a = 0#w <;>
       by_cases h1 : (xv ||| a) &&& b = 0#w <;>
       simp [RuntimeValue.isRefinedBy, LLVM.Int.or, isRefinedBy,
         Id.run, pure, h0, h1, BitVec.or_assoc])

end Veir.ArithCanonicalize.BitwiseSupport
