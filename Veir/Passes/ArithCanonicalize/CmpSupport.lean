import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Integer comparison predicate transforms from pinned Arith canonicalizations. -/
namespace Veir.ArithCanonicalize.CmpSupport
open Veir Veir.Data

def invert : LLVM.IntPred → LLVM.IntPred
 | .eq => .ne | .ne => .eq
 | .slt => .sge | .sle => .sgt | .sgt => .sle | .sge => .slt
 | .ult => .uge | .ule => .ugt | .ugt => .ule | .uge => .ult

theorem eval_invert (p : LLVM.IntPred) (x y : BitVec w) :
    LLVM.IntPred.eval (invert p) x y = !(LLVM.IntPred.eval p x y) := by
  cases p <;> simp [invert, LLVM.IntPred.eval, BitVec.slt, BitVec.sle, BitVec.ult, BitVec.ule]
  case eq => rfl
  case ne => simp [bne]
  case ugt => by_cases h : y.toNat < x.toNat <;> simp [h] <;> omega
  case uge => by_cases h : y.toNat ≤ x.toNat <;> simp [h] <;> omega
  case ult => by_cases h : x.toNat < y.toNat <;> simp [h] <;> omega
  case ule => by_cases h : x.toNat ≤ y.toNat <;> simp [h] <;> omega
  case sgt => by_cases h : y.toInt < x.toInt <;> simp [h] <;> omega
  case sge => by_cases h : y.toInt ≤ x.toInt <;> simp [h] <;> omega
  case slt => by_cases h : x.toInt < y.toInt <;> simp [h] <;> omega
  case sle => by_cases h : x.toInt ≤ y.toInt <;> simp [h] <;> omega

theorem xor_icmp_invert (p : LLVM.IntPred) (x y : LLVM.Int w) :
    LLVM.Int.xor (LLVM.Int.icmp x y p) (.val (1#1)) =
      LLVM.Int.icmp x y (invert p) := by
  cases x with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run]
  | val a =>
    cases y with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.xor, Id.run]
    | val b =>
      simp only [LLVM.Int.icmp, Id.run]
      rw [show LLVM.IntPred.eval (invert p) a b =
        !(LLVM.IntPred.eval p a b) from eval_invert p a b]
      cases h : LLVM.IntPred.eval p a b <;>
        simp [LLVM.Int.icmp, LLVM.Int.xor, h, Id.run]

end Veir.ArithCanonicalize.CmpSupport
