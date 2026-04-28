module

public meta import Std.Tactic.BVDecide.Reflect
import all Veir.Data.LLVM.Int.Basic
import Veir.ForLean
import Veir.Data.LLVM.Int.Simp

open Veir.Data.LLVM

namespace Veir.Data.LLVM.Int

/--
  We define a bitblastable structure `IntBv`, where the `toBitVec` fields contains a bitvector,
  the `poison` field indicates whether the value is poison,
  and `inv` preserves a proof that if the value is poison its corresponding bitvector
  value is `0#w`.
-/
@[ext]
structure IntBv (w : Nat) where
  toBitVec : BitVec w
  poison : Bool
  inv : poison → (toBitVec = 0#w) := by simp
deriving DecidableEq

/-- An `LLVM.Int w` is converted into a structure `IntBv`, where
  the `poison` field indicates whether the `Int` is poison. -/
def toIntBv {w : Nat} (x : Int w) : IntBv w :=
  match h : x with
  | .val v => {toBitVec := v, poison := false}
  | .poison => {toBitVec := 0#w, poison := true}

/-- Return a boolean if the LLVM.int `x` is poison. -/
def isPoison {w : Nat} (x : Int w) : Bool :=
  match x with
  | .val _ => false
  | .poison => true

/-- Return a concrete bitvector value given an LLVM.Int. -/
def getValue {w : Nat} (x : Int w) : BitVec w := x.toIntBv.toBitVec

/--
  We prove the injectivity of `toIntBv`.
-/
theorem toIntBv.inj {w : Nat} {x y : Int w} (h : x.toIntBv = y.toIntBv) : x = y :=
  match x, y with
  | .val v,  .val v' => by
    simp only [toIntBv, IntBv.mk.injEq, and_true] at h
    simp [h]
  | .poison, .poison => rfl
  | .val v,  .poison => by
    simp [toIntBv] at h
  | .poison, .val v => by
    simp [toIntBv] at h

@[llvm_toBitVec]
theorem int_inj {w : Nat} (i1 i2 : Int w) :
    i1 = i2 ↔ i1.toIntBv = i2.toIntBv := ⟨(· ▸ rfl), by apply toIntBv.inj⟩

@[llvm_toBitVec]
theorem toIntBv_poison {w : Nat} :
    poison.toIntBv = ⟨0#w, true, by simp⟩ := by
  simp [toIntBv]

@[llvm_toBitVec]
theorem toIntBv_val {w : Nat} {v : BitVec w} :
    (val v).toIntBv = ⟨v, false, by simp⟩ := by
  simp [toIntBv]

@[llvm_toBitVec]
theorem ite_toIntBv_eq {w : Nat} (x : Int w) :
    (if x.toIntBv.poison = true then {toBitVec := 0#w, poison := true}
    else { toBitVec := x.toIntBv.toBitVec, poison := false}) = x.toIntBv := by
  rcases x <;> simp [llvm_toBitVec]

@[llvm_toBitVec]
theorem toIntBv_ite_eq {w : Nat} (x y : Int w) (c1 c2 : Bool) :
    (if c1 ∧ c2 then x else y).toIntBv = if c1 ∧ c2 then x.toIntBv else y.toIntBv := by
  rcases x <;> rcases y <;> simp [llvm_toBitVec]
  · split <;> simp [toIntBv]
  · split <;> simp [toIntBv]
  · split <;> simp [toIntBv]

@[bv_normalize]
theorem toBitVec_zero_of_poison (x : IntBv w) :
    x.poison = true → x.toBitVec = 0#w := by
  obtain ⟨bv, poison, h⟩ := x
  exact h

@[bv_normalize]
theorem eq_iff {w : Nat} {x y : IntBv w} :
    x = y ↔ x.toBitVec = y.toBitVec ∧ x.poison = y.poison :=
  IntBv.ext_iff

@[bv_normalize]
theorem toBitVec_ite {w : Nat} (b : Prop) [Decidable b] (x y : IntBv w) :
    (if b then x else y).toBitVec = if b then x.toBitVec else y.toBitVec := by
  split <;> rfl

@[bv_normalize]
theorem poison_ite {w : Nat} (b : Prop) [Decidable b] (x y : IntBv w) :
    (if b then x else y).poison = if b then x.poison else y.poison := by
  split <;> rfl

@[bv_normalize]
theorem poison_toBitVec_constraint {w : Nat} (x : IntBv w) :
    x.poison = true → x.toBitVec = 0#w := x.inv

@[bv_normalize]
theorem toBitVec_bif {w : Nat} (b : Bool) (x y : IntBv w) :
    (bif b then x else y).toBitVec = bif b then x.toBitVec else y.toBitVec := by
  cases b <;> rfl

@[bv_normalize]
theorem poison_bif {w : Nat} (b : Bool) (x y : IntBv w) :
    (bif b then x else y).poison = bif b then x.poison else y.poison := by
  cases b <;> rfl

@[llvm_toBitVec]
theorem isPoison_of_poison {w : Nat} : poison.isPoison (w := w) = true := by
  simp [isPoison]

@[llvm_toBitVec]
theorem isPoison_of_val {w : Nat} {v : BitVec w}: (val v).isPoison (w := w) = false := by
  simp [isPoison]

@[llvm_toBitVec]
theorem getValue_of_poison {w : Nat} : (poison).getValue = 0#w := by
  simp [getValue, llvm_toBitVec]

@[llvm_toBitVec]
theorem getValue_of_val {w : Nat} {v : BitVec w} : (val v).getValue = v := by
  simp [getValue, llvm_toBitVec]

@[llvm_toBitVec]
theorem getValue_eq_toBitVec_of_not_poison {w : Nat} {x : Int w} (hx : ¬ x.isPoison) :
    x.getValue = x.toIntBv.toBitVec := by
  cases x
  · simp [toIntBv, getValue]
  · simp [isPoison] at hx

/-! # LLVM IR operations unfolding to `toIntBv` -/

@[llvm_toBitVec]
theorem toIntBv_constant {w : Nat} (v : _root_.Int) :
    (constant w v).toIntBv = ⟨BitVec.ofInt w v, false, by simp⟩ := by
  simp [constant, toIntBv]

@[llvm_toBitVec]
theorem toIntBv_add {w : Nat} (x y : Int w) :
    (add x y nsw nuw).toIntBv =
      if (x.toIntBv.poison ∨ y.toIntBv.poison) = true then {toBitVec := 0#w, poison := true}
        else if (nsw ∧ BitVec.saddOverflow x.toIntBv.toBitVec y.toIntBv.toBitVec)
          then {toBitVec := 0#w, poison := true}
            else if (nuw ∧ BitVec.uaddOverflow x.toIntBv.toBitVec y.toIntBv.toBitVec)
              then {toBitVec := 0#w, poison := true}
                else {toBitVec := x.toIntBv.toBitVec + y.toIntBv.toBitVec, poison := false} := by
  simp [add, llvm_toBitVec, Id.run]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem toIntBv_sub {w : Nat} (x y : Int w) :
    (sub x y nsw nuw).toIntBv =
      if (x.toIntBv.poison ∨ y.toIntBv.poison) = true then {toBitVec := 0#w, poison := true}
        else if (nsw ∧ BitVec.ssubOverflow x.toIntBv.toBitVec y.toIntBv.toBitVec)
          then {toBitVec := 0#w, poison := true}
            else if (nuw ∧ BitVec.usubOverflow x.toIntBv.toBitVec y.toIntBv.toBitVec)
              then {toBitVec := 0#w, poison := true}
                else {toBitVec := x.toIntBv.toBitVec - y.toIntBv.toBitVec, poison := false} := by
  simp [sub, llvm_toBitVec, Id.run]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem toIntBv_mul {w : Nat} (x y : Int w) :
    (mul x y nsw nuw).toIntBv =
      if (x.toIntBv.poison ∨ y.toIntBv.poison) = true then {toBitVec := 0#w, poison := true}
        else if (nsw ∧ BitVec.smulOverflow x.toIntBv.toBitVec y.toIntBv.toBitVec)
          then {toBitVec := 0#w, poison := true}
            else if (nuw ∧ BitVec.umulOverflow x.toIntBv.toBitVec y.toIntBv.toBitVec)
              then {toBitVec := 0#w, poison := true}
                else {toBitVec := x.toIntBv.toBitVec * y.toIntBv.toBitVec, poison := false} := by
  simp [mul, llvm_toBitVec, Id.run]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]



example (x y : Int 64) :
    (x.add y) = (y.add x) := by
  simp [llvm_toBitVec]
  bv_decide

example (x : Int 64) :
    x.add (val 0#64) = x := by
  simp [llvm_toBitVec]

example (x y : Int 64) :
    (x.add y) = (y.add x) := by
  simp [llvm_toBitVec]
  bv_decide

end Int
