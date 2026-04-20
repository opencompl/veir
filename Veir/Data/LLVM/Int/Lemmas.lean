module

import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Int.Tactic
import Veir.ForLean

open Veir.Data.LLVM

namespace Veir.Data.LLVM.Int

/- # BitVec -/

@[simp_int]
def ofInt (x : Int w) : BitVec w :=
  match x with
  | .val v => v
  | .poison => 0#w

@[simp_int]
theorem inj_val (x y : Int w)
    (hx : x = Int.val v) (hy : y = Int.val v') :
    x = y ↔ v = v' := by
  simp [hx, hy]

@[simp_int]
theorem ofInt_inj_val (x y : Int w)
    (hx : x = Int.val v) (hy : y = Int.val v) :
    ofInt x = ofInt y ↔ x = y := by
  simp [hx, hy]

@[simp_int]
theorem ofInt_inj_poison (x y : Int w)
    (hx : x = .poison) (hy : y = .poison) :
    ofInt x = ofInt y ↔ x = y := by
  simp [hx, hy]

@[simp_int]
theorem val_injEq {w : Nat} (v v' : BitVec w) :
    (Int.val v = Int.val v') = (v = v') := by
  simp

@[simp_int]
def casesOn'.{u}  {motive : Int w → Sort u}
    (poison : motive Int.poison)
    (value : (v : BitVec w) → motive (Int.val v))
    : motive v? :=
  match v? with
  | .val a => value a
  | .poison => poison


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

end Int
