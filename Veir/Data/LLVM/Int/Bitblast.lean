module

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
theorem getValue_of_val {w : Nat} {v : BitVec w} :
    (val v).getValue = v := by
  rfl

@[llvm_toBitVec]
theorem toIntBv_isPoison_iff (x : Int w) :
    x.isPoison = x.toIntBv.poison := by
  cases x <;> simp [isPoison, llvm_toBitVec]

@[llvm_toBitVec]
theorem ite_eq_toIntBv {w : Nat} (x : Int w) :
   (if x.isPoison then {toBitVec := 0#w, poison := true} else
      {toBitVec := x.getValue, poison := false}) = x.toIntBv := by
  rcases x <;> simp [llvm_toBitVec, isPoison]
  <;> split <;> simp [toIntBv]

@[llvm_toBitVec]
theorem poison_ite_eq {w : Nat} (x y : Int w) (z : BitVec w):
  (if x.isPoison = true ∨ y.isPoison = true then
      ({ toBitVec := 0#w, poison := true, inv := by simp} : IntBv w) else
      ({ toBitVec := z, poison := false, inv := by simp} : IntBv w)).poison =
      (x.isPoison ∨ y.isPoison) := by
  split
  · case _ h =>  simp [h]
  · case _ h => simpa using h

@[llvm_toBitVec]
theorem toIntBv_ite_eq {w : Nat} (x y : Int w) (c1 : Prop) [Decidable c1] :
    (if c1 then x else y).toIntBv = if c1 then x.toIntBv else y.toIntBv:= by
  rcases x <;> rcases y <;> simp [llvm_toBitVec]
  <;> split <;> simp [toIntBv]

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
theorem toIntBv_add {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (add x y nsw nuw).toIntBv =
      if x.isPoison ∨ y.isPoison then {toBitVec := 0#w, poison := true}
        else if (nsw ∧ BitVec.saddOverflow x.getValue y.getValue)
          then {toBitVec := 0#w, poison := true}
            else if (nuw ∧ BitVec.uaddOverflow x.getValue y.getValue)
              then {toBitVec := 0#w, poison := true}
                else {toBitVec := x.getValue + y.getValue, poison := false} := by
  simp only [add, Id.run, pure_bind]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem poison_toIntBv_add {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (add x y nsw nuw).toIntBv.poison =
        (x.isPoison ∨ y.isPoison ∨
        (nsw ∧ BitVec.saddOverflow x.getValue y.getValue) ∨
        (nuw ∧ BitVec.uaddOverflow x.getValue y.getValue)) := by
  simp only [toIntBv_add, eq_iff_iff]
  split
  · case _ h => rcases h with h|h <;> simp [h]
  · split
    · simp_all
    · split <;> simp_all

@[llvm_toBitVec]
theorem isPoison_add {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (add x y nsw nuw).isPoison =
        (x.isPoison ∨ y.isPoison ∨
        (nsw ∧ BitVec.saddOverflow x.getValue y.getValue) ∨
        (nuw ∧ BitVec.uaddOverflow x.getValue y.getValue)) := by
  simp [toIntBv_isPoison_iff, poison_toIntBv_add]

@[llvm_toBitVec]
theorem toIntBv_sub {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (sub x y nsw nuw).toIntBv =
      if x.isPoison ∨ y.isPoison then {toBitVec := 0#w, poison := true}
        else if (nsw ∧ BitVec.ssubOverflow x.getValue y.getValue)
          then {toBitVec := 0#w, poison := true}
            else if (nuw ∧ BitVec.usubOverflow x.getValue y.getValue)
              then {toBitVec := 0#w, poison := true}
                else {toBitVec := x.getValue - y.getValue, poison := false} := by
  simp only [sub, Id.run, pure_bind]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem toIntBv_mul {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (mul x y nsw nuw).toIntBv =
      if x.isPoison ∨ y.isPoison then {toBitVec := 0#w, poison := true}
        else if (nsw ∧ BitVec.smulOverflow x.getValue y.getValue)
          then {toBitVec := 0#w, poison := true}
            else if (nuw ∧ BitVec.umulOverflow x.getValue y.getValue)
              then {toBitVec := 0#w, poison := true}
                else {toBitVec := x.getValue * y.getValue, poison := false} := by
  simp only [mul, Id.run, pure_bind]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem toIntBv_udiv {w : Nat} (x y : Int w) {exact : Bool}:
    (udiv x y exact).toIntBv =
      if x.isPoison ∨ y.isPoison then {toBitVec := 0#w, poison := true}
        else if (exact ∧ BitVec.umod x.getValue y.getValue ≠ 0)
          then {toBitVec := 0#w, poison := true}
            else if (y.getValue = 0)
              then {toBitVec := 0#w, poison := true}
                else {toBitVec := x.getValue.udiv y.getValue, poison := false} := by
  simp only [udiv, Id.run, BitVec.umod_eq, BitVec.ofNat_eq_ofNat, ne_eq, pure_bind, BitVec.udiv_eq]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem toIntBv_sdiv {w : Nat} (x y : Int w) {exact : Bool}:
    (sdiv x y exact).toIntBv =
      if x.isPoison ∨ y.isPoison then {toBitVec := 0#w, poison := true}
        else if (y.getValue == 0 ||
            (w != 1 && x.getValue == (BitVec.intMin w) && y.getValue == -1))
          then {toBitVec := 0#w, poison := true}
            else if (exact ∧ BitVec.smod x.getValue y.getValue ≠ 0)
              then {toBitVec := 0#w, poison := true}
                else if (y.getValue = 0)
                  then {toBitVec := 0#w, poison := true}
                    else {toBitVec := x.getValue.sdiv y.getValue, poison := false} := by
  simp only [sdiv, Id.run, BitVec.ofNat_eq_ofNat, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    bne_iff_ne, ne_eq, pure_bind]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem toIntBv_urem {w : Nat} (x y : Int w) :
    (urem x y).toIntBv =
      if x.isPoison ∨ y.isPoison then {toBitVec := 0#w, poison := true}
        else if (y.getValue == 0)
          then {toBitVec := 0#w, poison := true}
            else {toBitVec := x.getValue.umod y.getValue, poison := false} := by
  simp only [urem, Id.run, BitVec.ofNat_eq_ofNat, beq_iff_eq, pure_bind,
    BitVec.umod_eq]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem toIntBv_srem {w : Nat} (x y : Int w) :
    (srem x y).toIntBv =
      if x.isPoison ∨ y.isPoison then {toBitVec := 0#w, poison := true}
        else if (y.getValue == 0 ||
            (w != 1 && x.getValue  == (BitVec.intMin w) && y.getValue  == -1))
          then {toBitVec := 0#w, poison := true}
            else {toBitVec := x.getValue.srem y.getValue, poison := false} := by
  simp only [srem, Id.run, BitVec.ofNat_eq_ofNat, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    bne_iff_ne, ne_eq, pure_bind]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem toIntBv_shl {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (shl x y nsw nuw).toIntBv =
      if x.isPoison ∨ y.isPoison then {toBitVec := 0#w, poison := true}
        else if (nsw ∧
            (x.getValue <<< y.getValue).sshiftRight' y.getValue ≠ x.getValue)
          then {toBitVec := 0#w, poison := true}
            else if (nuw ∧
                (x.getValue <<< y.getValue) >>> y.getValue ≠ x.getValue)
              then {toBitVec := 0#w, poison := true}
                else if (y.getValue ≥ w)
                  then {toBitVec := 0#w, poison := true}
                else {toBitVec := x.getValue <<< y.getValue, poison := false} := by
  simp only [shl, Id.run, BitVec.shiftLeft_eq', BitVec.sshiftRight_eq', ne_eq,
    BitVec.ushiftRight_eq', BitVec.natCast_eq_ofNat, ge_iff_le, pure_bind]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem toIntBv_lshr {w : Nat} (x y : Int w) {exact : Bool} :
    (lshr x y exact).toIntBv =
      if x.isPoison ∨ y.isPoison then {toBitVec := 0#w, poison := true}
        else if (y.getValue ≥ w)
          then {toBitVec := 0#w, poison := true}
            else if exact ∧ (x.getValue >>> y.getValue) <<< y.getValue ≠ x.getValue
              then {toBitVec := 0#w, poison := true}
                else {toBitVec := x.getValue >>> y.getValue, poison := false} := by
  simp only [lshr, Id.run, BitVec.natCast_eq_ofNat, ge_iff_le, BitVec.ushiftRight_eq',
    BitVec.shiftLeft_eq', ne_eq, pure_bind]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem toIntBv_ashr {w : Nat} (x y : Int w) {exact : Bool} :
    (ashr x y exact).toIntBv =
      if x.isPoison ∨ y.isPoison then {toBitVec := 0#w, poison := true}
        else if (y.getValue ≥ w)
          then {toBitVec := 0#w, poison := true}
            else if exact ∧ (x.getValue >>> y.getValue) <<< y.getValue ≠ x.getValue
              then {toBitVec := 0#w, poison := true}
                else {toBitVec := x.getValue.sshiftRight' y.getValue, poison := false} := by
  simp only [ashr, Id.run, BitVec.natCast_eq_ofNat, ge_iff_le, BitVec.ushiftRight_eq',
    BitVec.shiftLeft_eq', ne_eq, BitVec.sshiftRight_eq', pure_bind]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem toIntBv_cast {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ = w₂) :
    (cast x h).toIntBv =
      if x.isPoison then {toBitVec := 0#w₂, poison := true}
        else {toBitVec := (x.getValue.cast h), poison := false } := by
  simp only [cast]
  rcases x
  <;> simp [llvm_toBitVec]

@[llvm_toBitVec]
theorem toIntBv_and {w : Nat} (x y : Int w) :
    (and x y).toIntBv =
      if x.isPoison ∨ y.isPoison then {toBitVec := 0#w, poison := true}
        else {toBitVec := x.getValue &&& y.getValue, poison := false} := by
  simp only [and, Id.run]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec]

@[llvm_toBitVec]
theorem toIntBv_or {w : Nat} (x y : Int w) {disjoint : Bool} :
    (or x y disjoint).toIntBv =
      if x.isPoison ∨ y.isPoison then {toBitVec := 0#w, poison := true}
        else if disjoint ∧ (x.getValue &&& y.getValue) ≠ 0 then {toBitVec := 0#w, poison := true}
          else {toBitVec := x.getValue ||| y.getValue, poison := false} := by
  simp only [or, Id.run, ne_eq, pure_bind]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem toIntBv_xor {w : Nat} (x y : Int w) :
    (xor x y).toIntBv =
      if x.isPoison ∨ y.isPoison then {toBitVec := 0#w, poison := true}
        else {toBitVec := x.getValue ^^^ y.getValue, poison := false} := by
  simp only [xor, Id.run]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec]

@[llvm_toBitVec]
theorem toIntBv_trunc {w₁ w₂ : Nat} (x : Int w₁) (nsw : Bool := false) (nuw : Bool := false)
  (h : w₁ > w₂):
    (trunc x w₂ nsw nuw h).toIntBv =
      if x.isPoison then {toBitVec := 0#w₂, poison := true}
        else if nsw ∧ (x.getValue.truncate w₂).signExtend w₁ ≠ x.getValue
          then {toBitVec := 0#w₂, poison := true}
            else if nuw ∧ (x.getValue.truncate w₂).zeroExtend w₁ ≠ x.getValue
              then {toBitVec := 0#w₂, poison := true}
                else {toBitVec := x.getValue.truncate w₂, poison := false} := by
  simp only [trunc, Id.run, BitVec.truncate_eq_setWidth, ne_eq, decide_not, Bool.and_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, pure_bind]
  rcases x
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem toIntBv_zext {w₁ w₂ : Nat} (x : Int w₁) (nneg : Bool := false) (h : w₁ < w₂):
    (zext x w₂ nneg h).toIntBv =
      if x.isPoison then {toBitVec := 0#w₂, poison := true}
        else if nneg ∧ x.getValue.msb then {toBitVec := 0#w₂, poison := true}
          else {toBitVec := x.getValue.zeroExtend w₂, poison := false} := by
  simp only [zext, Id.run, Bool.and_eq_true, BitVec.truncate_eq_setWidth, pure_bind]
  rcases x
  <;> simp [llvm_toBitVec, pure, Id]

@[llvm_toBitVec]
theorem toIntBv_sext {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ < w₂):
    (sext x w₂ h).toIntBv =
      if x.isPoison then {toBitVec := 0#w₂, poison := true}
        else {toBitVec := x.getValue.signExtend w₂, poison := false} := by
  simp only [sext, Id.run]
  rcases x
  <;> simp [llvm_toBitVec]

@[llvm_toBitVec]
theorem toIntBv_icmp {w : Nat} (x y : Int w) (p : IntPred):
    (icmp x y p).toIntBv =
      if x.isPoison ∨ y.isPoison then {toBitVec := 0#1, poison := true}
        else {toBitVec := BitVec.ofBool (IntPred.eval p x.getValue y.getValue), poison := false} := by
  simp only [icmp, Id.run]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec]

@[llvm_toBitVec]
theorem toIntBv_select {w : Nat} (x y : Int w) (c : Int 1):
    (select c x y).toIntBv =
      if x.isPoison ∨ y.isPoison ∨ c.isPoison then {toBitVec := 0#w, poison := true}
        else
          {toBitVec := if c.getValue == 1#1 then x.getValue else y.getValue,
            poison := false} := by
  simp only [select, Id.run, beq_iff_eq]
  rcases x <;> rcases y <;> rcases c
  <;> simp [llvm_toBitVec]



theorem bv_AddSub_1165 :
    ∀ (e e_1 : Int 64),
      add (add (constant (w := 64) 0) e) (add (constant (w := 64) 0) e_1) =
      add (constant (w := 64) 0) (add e e_1) := by
  intros x y
  simp [llvm_toBitVec]
  bv_decide




end Int
