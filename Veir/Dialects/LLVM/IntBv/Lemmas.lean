module

import all Veir.Dialects.LLVM.IntBv.Basic

open Veir.Dialects.LLVM.IntBv

namespace Veir.Dialects.LLVM.IntBv

@[bv_normalize]
theorem mkVal_eq {w : Nat} (x : BitVec w) :
    (IntBv.mkVal x) = ⟨x, false, by simp⟩ := rfl

@[bv_normalize]
theorem mkPoison_eq {w : Nat} :
    IntBv.mkPoison = ⟨0#w, true, by simp⟩ := rfl

@[simp, bv_normalize]
theorem poison_mkVal {w : Nat} (x : BitVec w) : (IntBv.mkVal x).poison = false := by
  simp only [IntBv.mkVal]

@[simp, bv_normalize]
theorem val_mkVal {w : Nat} (x : BitVec w) :
    (IntBv.mkVal x).val = x := by
  simp only [IntBv.mkVal]

@[simp, bv_normalize]
theorem val_mkPoison {w : Nat} : IntBv.mkPoison.val = 0#w := by
  simp [IntBv.mkPoison]

@[simp, bv_normalize]
theorem poison_mkPoison {w : Nat} : (IntBv.mkPoison (w := w)).poison = true := by
  simp only [IntBv.mkPoison]

@[bv_normalize]
theorem ext_iff {w : Nat} (x y : IntBv w) :
    x = y ↔ (x.val = y.val ∧ x.poison = y.poison) := by
  rw [@IntBv.mk.injEq]

/- # add -/

@[bv_normalize]
theorem add_eq {w : Nat} (x y : IntBv w) :
    x + y = if x.poison || y.poison then
              IntBv.mkPoison
            else
              IntBv.mkVal (x.val + y.val) := by
  simp only [HAdd.hAdd, Add.add, add]

theorem add_assoc {w : Nat} (x y z : IntBv w) : x + y + z = x + (y + z) := by
  simp only [HAdd.hAdd, Add.add, add]
  cases x.poison <;> cases y.poison <;> cases z.poison <;> simp [BitVec.add_assoc]

@[simp, bv_normalize]
theorem poison_add {w : Nat} (x : IntBv w) : IntBv.mkPoison + x = IntBv.mkPoison := by
  simp [HAdd.hAdd, Add.add, add]

@[simp, bv_normalize]
theorem add_poison {w : Nat} (x : IntBv w) : x + IntBv.mkPoison = IntBv.mkPoison := by
  simp [HAdd.hAdd, Add.add, add]

@[grind =]
theorem add_comm {w : Nat} (x y : IntBv w) : x + y = y + x := by
  simp only [HAdd.hAdd, Add.add, add]
  cases x.poison <;> cases y.poison <;> simp [BitVec.add_comm]

/- # mul -/

@[simp, bv_normalize]
theorem poison_mul {w : Nat} (x : IntBv w) : IntBv.mkPoison * x = IntBv.mkPoison := by
  simp [HMul.hMul, Mul.mul, mul]

@[simp, bv_normalize]
theorem mul_poison {w : Nat} (x : IntBv w) : x * IntBv.mkPoison = IntBv.mkPoison := by
  simp [HMul.hMul, Mul.mul, mul]

theorem mul_assoc {w : Nat} (x y z : IntBv w) : x * y * z = x * (y * z) := by
  simp only [HMul.hMul, Mul.mul, mul]
  cases x.poison <;> cases y.poison <;> cases z.poison <;> simp [BitVec.mul_assoc]

theorem mul_comm {w : Nat} (x y : IntBv w) : x * y = y * x := by
  simp only [HMul.hMul, Mul.mul, mul]
  cases x.poison <;> cases y.poison <;> simp [BitVec.mul_comm]
