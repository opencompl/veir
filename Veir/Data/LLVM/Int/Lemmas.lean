module

public import Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Int.Basic
import Veir.ForLean

open Veir.Data.LLVM

public section

namespace Veir.Data.LLVM.Int

/- # add -/

@[simp, grind =]
theorem poison_add {w : Nat} (x : Int w) : add poison x = poison := by
  simp only [add, Id.run]

@[simp, grind =]
theorem add_poison {w : Nat} (x : Int w) : add x poison = poison := by
  simp only [add, Id.run]
  grind

@[grind =]
theorem add_assoc {w : Nat} (x y z : Int w) :
    add (add x y) z = add x (add y z) := by
  simp only [add, Id.run]
  cases x <;> cases y <;> cases z <;> simp [BitVec.add_assoc]

@[grind =]
theorem add_comm {w : Nat} (x y : Int w) : add x y = add y x := by
  simp only [add]
  cases x <;> cases y <;> simp [BitVec.add_comm]

/- # mul -/

@[simp, grind =]
theorem poison_mul {w : Nat} (x : Int w) : mul poison x = poison := by
  simp only [mul, Id.run]

@[simp, grind =]
theorem mul_poison {w : Nat} (x : Int w) : mul x poison = poison := by
  simp only [mul, Id.run]
  grind

@[grind =]
theorem mul_assoc {w : Nat} (x y z : Int w) :
    mul x (mul y z) = mul (mul x y) z := by
  simp only [HMul.hMul, Mul.mul, mul, Id.run]
  cases x <;> cases y <;> cases z <;> simp [BitVec.mul_assoc]

@[grind =]
theorem mul_comm {w : Nat} {nsw nuw : Bool} (x y : Int w) :
    mul x y nsw nuw = mul y x nsw nuw := by
  simp only [Id.run, Veir.Data.LLVM.Int.mul]
  cases x <;> cases y <;>
  simp [BitVec.mul_comm, BitVec.smulOverflow_comm, BitVec.umulOverflow_comm]

/- # IntPred.eval -/

@[simp, grind =]
theorem _root_.Veir.Data.LLVM.IntPred.eval_eq {w : Nat} (x y : BitVec w) :
    IntPred.eq.eval x y = (x == y) := by
  simp only [IntPred.eval]

@[simp, grind =]
theorem _root_.Veir.Data.LLVM.IntPred.eval_ne {w : Nat} (x y : BitVec w) :
    IntPred.ne.eval x y = (x != y) := by
  simp only [IntPred.eval]

@[simp, grind =]
theorem _root_.Veir.Data.LLVM.IntPred.eval_ugt {w : Nat} (x y : BitVec w) :
    IntPred.ugt.eval x y = (y.ult x) := by
  simp only [IntPred.eval]

@[simp, grind =]
theorem _root_.Veir.Data.LLVM.IntPred.eval_uge {w : Nat} (x y : BitVec w) :
    IntPred.uge.eval x y = (y.ule x) := by
  simp only [IntPred.eval]

@[simp, grind =]
theorem _root_.Veir.Data.LLVM.IntPred.eval_ult {w : Nat} (x y : BitVec w) :
    IntPred.ult.eval x y = (x.ult y) := by
  simp only [IntPred.eval]

@[simp, grind =]
theorem _root_.Veir.Data.LLVM.IntPred.eval_ule {w : Nat} (x y : BitVec w) :
    IntPred.ule.eval x y = (x.ule y) := by
  simp only [IntPred.eval]

@[simp, grind =]
theorem _root_.Veir.Data.LLVM.IntPred.eval_sgt {w : Nat} (x y : BitVec w) :
    IntPred.sgt.eval x y = (y.slt x) := by
  simp only [IntPred.eval]

@[simp, grind =]
theorem _root_.Veir.Data.LLVM.IntPred.eval_sge {w : Nat} (x y : BitVec w) :
    IntPred.sge.eval x y = (y.sle x) := by
  simp only [IntPred.eval]

@[simp, grind =]
theorem _root_.Veir.Data.LLVM.IntPred.eval_slt {w : Nat} (x y : BitVec w) :
    IntPred.slt.eval x y = (x.slt y) := by
  simp only [IntPred.eval]

@[simp, grind =]
theorem _root_.Veir.Data.LLVM.IntPred.eval_sle {w : Nat} (x y : BitVec w) :
    IntPred.sle.eval x y = (x.sle y) := by
  simp only [IntPred.eval]

/- # icmp -/

@[simp, grind =]
theorem icmp_val {w : Nat} (x y : BitVec w) (p : IntPred) :
    icmp (val x) (val y) p = val (BitVec.ofBool (p.eval x y)) := by
  simp only [icmp, Id.run]

@[simp, grind =]
theorem poison_icmp {w : Nat} (y : Int w) (p : IntPred) : icmp poison y p = poison := by
  simp only [icmp, Id.run]

@[simp, grind =]
theorem icmp_poison {w : Nat} (x : Int w) (p : IntPred) : icmp x poison p = poison := by
  cases x <;> simp only [icmp, Id.run]

/- # zext -/

@[simp, grind =]
theorem zext_val {w₁ w₂ : Nat} (v : BitVec w₁) (h : w₁ < w₂) :
    zext (val v) w₂ false h = val (v.zeroExtend w₂) := by
  simp only [zext, Id.run]
  simp

@[simp, grind =]
theorem poison_zext {w₁ w₂ : Nat} {nneg : Bool} (h : w₁ < w₂) :
    zext (poison : Int w₁) w₂ nneg h = poison := by
  simp only [zext, Id.run]

end Int
