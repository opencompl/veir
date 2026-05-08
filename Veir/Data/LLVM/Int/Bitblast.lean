module

import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
public import Veir.Data.LLVM.Int.Basic
public meta import Std.Tactic.BVDecide.Reflect
import Veir.ForLean
import Veir.Data.LLVM.Int.Simp

open Veir.Data.LLVM

namespace Veir.Data.LLVM.Int

/-- Return true if the LLVM.Int `x` is poison. -/
def isPoison {w : Nat} (x : Int w) : Bool :=
  match x with
  | .poison => true
  | .val _ => false

/-- Return the value in the LLVM.Int `x` or 0 if `x` is poison. -/
def getValue {w : Nat} (x : Int w) : BitVec w :=
  match x with
  | .poison => 0#w
  | .val v => v

@[llvm_toBitVec]
theorem eq_iff {w : Nat} (a b : Int w) :
  a = b ↔
    a.isPoison = b.isPoison ∧
    (a.isPoison = false → b.isPoison = false → a.getValue = b.getValue) := by
  unfold isPoison getValue
  grind

@[llvm_toBitVec]
theorem isRefinedBy_iff {w : Nat} (a b : Int w) :
  a ⊑ b ↔
    a.isPoison = true ∨
    (b.isPoison = false ∧
      (a.isPoison = false → b.isPoison = false → a.getValue = b.getValue)) := by
  unfold isRefinedBy isPoison getValue
  grind

@[llvm_toBitVec]
theorem getValue_of_val {w : Nat} {v : BitVec w} :
    (val v).getValue = v := rfl

@[llvm_toBitVec]
theorem getValue_of_poison {w : Nat} :
    poison.getValue = 0#w := rfl

@[llvm_toBitVec]
theorem isPoison_of_val {w : Nat} {v : BitVec w} :
    (val v).isPoison = false := rfl

@[llvm_toBitVec]
theorem isPoison_of_poison {w : Nat} :
    poison.isPoison (w := w) = true := rfl

/-! # LLVM IR operations unfolding to `toIntBv` -/

@[llvm_toBitVec]
theorem getValue_constant {w : Nat} (v : _root_.Int) :
    (constant w v).getValue = BitVec.ofInt w v := rfl

@[llvm_toBitVec]
theorem isPoison_constant {w : Nat} (v : _root_.Int) :
    (constant w v).isPoison = false := rfl

@[llvm_toBitVec]
theorem isPoison_add {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (add x y nsw nuw).isPoison =
      decide
        (x.isPoison = true ∨ y.isPoison = true ∨
        (x.isPoison = false → y.isPoison = false →
          (nsw ∧ BitVec.saddOverflow x.getValue y.getValue) ∨
          (nuw ∧ BitVec.uaddOverflow x.getValue y.getValue))) := by
  simp only [isPoison, add, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]
  <;> grind

@[llvm_toBitVec]
theorem getValue_add {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (add x y nsw nuw).isPoison = false) :
    (add x y nsw nuw).getValue = x.getValue + y.getValue := by
  simp only [add, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id] at *
  <;> grind

@[llvm_toBitVec]
theorem isPoison_sub {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (sub x y nsw nuw).isPoison =
      decide
        (x.isPoison = true ∨ y.isPoison = true ∨
        (x.isPoison = false → y.isPoison = false →
          (nsw ∧ BitVec.ssubOverflow x.getValue y.getValue) ∨
          (nuw ∧ BitVec.usubOverflow x.getValue y.getValue))) := by
  simp only [isPoison, sub, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]
  <;> grind

@[llvm_toBitVec]
theorem getValue_sub {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (sub x y nsw nuw).isPoison = false) :
    (sub x y nsw nuw).getValue = x.getValue - y.getValue := by
  simp only [sub, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id] at *
  <;> grind

@[llvm_toBitVec]
theorem isPoison_mul {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (mul x y nsw nuw).isPoison =
      decide
        (x.isPoison = true ∨ y.isPoison = true ∨
        (x.isPoison = false → y.isPoison = false →
          (nsw ∧ BitVec.smulOverflow x.getValue y.getValue) ∨
          (nuw ∧ BitVec.umulOverflow x.getValue y.getValue))) := by
  simp only [isPoison, mul, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]
  <;> grind

@[llvm_toBitVec]
theorem getValue_mul {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (mul x y nsw nuw).isPoison = false) :
    (mul x y nsw nuw).getValue = x.getValue * y.getValue := by
  simp only [mul, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id] at *
  <;> grind

@[llvm_toBitVec]
theorem isPoison_udiv {w : Nat} (x y : Int w) {exact : Bool} :
    (udiv x y exact).isPoison =
      decide
        (x.isPoison ∨ y.isPoison ∨
        (x.isPoison = false → y.isPoison = false →
          (exact ∧ BitVec.umod x.getValue y.getValue ≠ 0) ∨
          (y.getValue = 0))) := by
  simp only [isPoison, udiv, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]
  <;> grind

@[llvm_toBitVec]
theorem getValue_udiv {w : Nat} (x y : Int w) {exact : Bool} (h : (udiv x y exact).isPoison = false) :
    (udiv x y exact).getValue = x.getValue.udiv y.getValue := by
  simp only [udiv, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id] at *
  <;> grind

@[llvm_toBitVec]
theorem isPoison_sdiv {w : Nat} (x y : Int w) {exact : Bool} :
    (sdiv x y exact).isPoison =
      decide
        (x.isPoison ∨ y.isPoison ∨
        (x.isPoison = false → y.isPoison = false →
          (y.getValue == 0 ||
              (w != 1 && x.getValue == (BitVec.intMin w) && y.getValue == -1)) ∨
          (exact ∧ BitVec.smod x.getValue y.getValue ≠ 0) ∨
          (y.getValue = 0))) := by
  simp only [isPoison, sdiv, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]
  <;> grind

@[llvm_toBitVec]
theorem getValue_sdiv {w : Nat} (x y : Int w) {exact : Bool} (h : (sdiv x y exact).isPoison = false) :
    (sdiv x y exact).getValue = x.getValue.sdiv y.getValue := by
  simp only [sdiv, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id] at *
  <;> grind

@[llvm_toBitVec]
theorem isPoison_urem {w : Nat} (x y : Int w) :
    (urem x y).isPoison =
      decide
        (x.isPoison ∨ y.isPoison ∨
        (y.isPoison = false → y.getValue = 0)) := by
  simp only [isPoison, urem, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]
  <;> grind

@[llvm_toBitVec]
theorem getValue_urem {w : Nat} (x y : Int w) (h : (urem x y).isPoison = false) :
    (urem x y).getValue = x.getValue.umod y.getValue := by
  simp only [urem, Id.run, pure_bind, getValue] at *
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id, isPoison] at *
  <;> grind

@[llvm_toBitVec]
theorem isPoison_srem {w : Nat} (x y : Int w) :
    (srem x y).isPoison =
      decide
        (x.isPoison ∨ y.isPoison ∨
        (x.isPoison = false → y.isPoison = false →
        (y.getValue == 0 ||
            (w != 1 && x.getValue  == (BitVec.intMin w) && y.getValue == -1)))) := by
  simp only [isPoison, srem, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]
  <;> grind

@[llvm_toBitVec]
theorem getValue_srem {w : Nat} (x y : Int w) (h : (srem x y).isPoison = false) :
    (srem x y).getValue = x.getValue.srem y.getValue := by
  simp only [srem, Id.run, pure_bind, getValue] at *
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id, isPoison] at *
  <;> grind

@[llvm_toBitVec]
theorem isPoison_shl {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (shl x y nsw nuw).isPoison =
      decide
        (x.isPoison ∨ y.isPoison ∨
        (x.isPoison = false → y.isPoison = false →
          (nsw ∧
              (x.getValue <<< y.getValue).sshiftRight' y.getValue ≠ x.getValue) ∨
          (nuw ∧
                  (x.getValue <<< y.getValue) >>> y.getValue ≠ x.getValue) ∨
          (y.getValue ≥ w))) := by
  simp only [isPoison, shl, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]
  <;> grind

@[llvm_toBitVec]
theorem getValue_shl {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (shl x y nsw nuw).isPoison = false) :
    (shl x y nsw nuw).getValue = x.getValue <<< y.getValue := by
  simp only [shl, Id.run, pure_bind, getValue] at *
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id, isPoison] at *
  <;> grind

@[llvm_toBitVec]
theorem isPoison_lshr {w : Nat} (x y : Int w) {exact : Bool} :
    (lshr x y exact).isPoison =
      decide
        (x.isPoison ∨ y.isPoison ∨
        (x.isPoison = false → y.isPoison = false →
          y.getValue ≥ w ∨
          (exact ∧ (x.getValue >>> y.getValue) <<< y.getValue ≠ x.getValue))) := by
  simp only [isPoison, lshr, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]
  <;> grind

@[llvm_toBitVec]
theorem getValue_lshr {w : Nat} (x y : Int w) {exact : Bool} (h : (lshr x y exact).isPoison = false) :
    (lshr x y exact).getValue = x.getValue >>> y.getValue := by
  simp only [lshr, Id.run, pure_bind, getValue] at *
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id, isPoison] at *
  <;> grind

@[llvm_toBitVec]
theorem isPoison_ashr {w : Nat} (x y : Int w) {exact : Bool} :
    (ashr x y exact).isPoison =
      decide
        (x.isPoison ∨ y.isPoison ∨
        (x.isPoison = false → y.isPoison = false →
          y.getValue ≥ w ∨
          (exact ∧ (x.getValue >>> y.getValue) <<< y.getValue ≠ x.getValue))) := by
  simp only [isPoison, ashr, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]
  <;> grind

@[llvm_toBitVec]
theorem getValue_ashr {w : Nat} (x y : Int w) {exact : Bool} (h : (ashr x y exact).isPoison = false) :
    (ashr x y exact).getValue = x.getValue.sshiftRight' y.getValue := by
  simp only [ashr, Id.run, pure_bind, getValue] at *
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id, isPoison] at *
  <;> grind

@[llvm_toBitVec]
theorem isPoison_cast {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ = w₂) :
    (cast x h).isPoison =
        x.isPoison := by
  unfold cast isPoison
  grind

@[llvm_toBitVec]
theorem getValue_cast {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ = w₂) :
    (cast x h).getValue = x.getValue.cast h := by
  unfold cast getValue
  grind

@[llvm_toBitVec]
theorem isPoison_and {w : Nat} (x y : Int w) :
    (and x y).isPoison =
      decide
        (x.isPoison ∨ y.isPoison) := by
  simp only [and, isPoison, Id.run]
  grind

@[llvm_toBitVec]
theorem getValue_and {w : Nat} (x y : Int w) :
    (and x y).getValue = x.getValue &&& y.getValue := by
  simp only [and, getValue, Id.run] at *
  grind

@[llvm_toBitVec]
theorem isPoison_or {w : Nat} (x y : Int w) {disjoint : Bool} :
    (or x y disjoint).isPoison =
      decide
        (x.isPoison ∨ y.isPoison ∨
        (x.isPoison = false → y.isPoison = false →
          disjoint ∧ (x.getValue &&& y.getValue) ≠ 0)) := by
  simp only [isPoison, or, Id.run, pure_bind, getValue]
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id]
  <;> grind

@[llvm_toBitVec]
theorem getValue_or {w : Nat} (x y : Int w) {disjoint : Bool} (h : (or x y disjoint).isPoison = false) :
    (or x y disjoint).getValue = x.getValue ||| y.getValue := by
  simp only [or, Id.run, pure_bind, getValue] at *
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, pure, Id, isPoison] at *
  <;> grind

@[llvm_toBitVec]
theorem isPoison_xor {w : Nat} (x y : Int w) :
    (xor x y).isPoison =
      decide
        (x.isPoison ∨ y.isPoison) := by
  simp only [xor, isPoison, Id.run] at *
  grind

@[llvm_toBitVec]
theorem getValue_xor {w : Nat} (x y : Int w) (h : (xor x y).isPoison = false) :
    (xor x y).getValue = x.getValue ^^^ y.getValue := by
  simp only [xor, Id.run, getValue] at *
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, isPoison] at *
  <;> grind

@[llvm_toBitVec]
theorem isPoison_trunc {w₁ w₂: Nat} (x : Int w₁) {nsw nuw : Bool} (h : w₁ > w₂) :
    (trunc x w₂ nsw nuw h).isPoison =
      decide
        (x.isPoison ∨
        (x.isPoison = false →
          (nsw ∧ (x.getValue.truncate w₂).signExtend w₁ ≠ x.getValue) ∨
          (nuw ∧ (x.getValue.truncate w₂).zeroExtend w₁ ≠ x.getValue))) := by
  simp only [isPoison, trunc, Id.run, pure_bind, getValue]
  rcases x
  <;> simp [llvm_toBitVec, pure, Id]
  <;> grind

@[llvm_toBitVec]
theorem getValue_trunc {w₁ w₂: Nat} (x : Int w₁) {nsw nuw : Bool} (h : w₁ > w₂) (hpoison : (trunc x w₂ nsw nuw h).isPoison = false) :
    (trunc x w₂ nsw nuw h).getValue = x.getValue.truncate w₂ := by
  simp only [trunc, Id.run, pure_bind, getValue] at *
  rcases x
  <;> simp [llvm_toBitVec, pure, Id, isPoison] at *
  <;> grind

@[llvm_toBitVec]
theorem isPoison_zext {w₁ w₂: Nat} (x : Int w₁) {nneg : Bool} (h : w₁ < w₂) :
    (zext x w₂ nneg h).isPoison =
      decide
        (x.isPoison ∨
          (x.isPoison = false → nneg ∧ x.getValue.msb)) := by
  simp only [isPoison, zext, Id.run, pure_bind, getValue]
  rcases x
  <;> simp [llvm_toBitVec, pure, Id]
  <;> grind

@[llvm_toBitVec]
theorem getValue_zext (x : Int w₁) {nneg : Bool} (h : w₁ < w₂) (hpoison : (zext x w₂ nneg h).isPoison = false) :
    (zext x w₂ nneg h).getValue = x.getValue.zeroExtend w₂ := by
  simp only [zext, Id.run, pure_bind, getValue] at *
  rcases x
  <;> simp [llvm_toBitVec, pure, Id, isPoison] at *
  <;> grind

@[llvm_toBitVec]
theorem isPoison_sext {w₁ w₂: Nat} (x : Int w₁) (h : w₁ < w₂) :
    (sext x w₂ h).isPoison = x.isPoison := by
  simp only [sext, isPoison, Id.run]
  grind

@[llvm_toBitVec]
theorem getValue_sext (x : Int w₁) (h : w₁ < w₂) :
    (sext x w₂ h).getValue = x.getValue.signExtend w₂ := by
  simp only [sext, getValue, Id.run]
  grind

@[llvm_toBitVec]
theorem isPoison_icmp {w : Nat} (x y : Int w) (p : IntPred) :
    (icmp x y p).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp only [icmp, isPoison, Id.run]
  grind

@[llvm_toBitVec]
theorem getValue_icmp {w : Nat} (x y : Int w) (p : IntPred) (h : (icmp x y p).isPoison = false) :
    (icmp x y p).getValue = BitVec.ofBool (IntPred.eval p x.getValue y.getValue) := by
  simp only [icmp, Id.run, getValue] at *
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, isPoison] at *
  <;> grind

attribute [llvm_toBitVec] IntPred.eval

@[llvm_toBitVec]
theorem isPoison_select {w : Nat} (x y : Int w) (c : Int 1) :
    (select c x y).isPoison = decide (x.isPoison ∨ y.isPoison ∨ c.isPoison) := by
  simp only [select, isPoison, Id.run]
  grind

@[llvm_toBitVec]
theorem getValue_select {w : Nat} (x y : Int w) (c : Int 1) (h : (select c x y).isPoison = false) :
    (select c x y).getValue = if c.getValue == 1#1 then x.getValue else y.getValue := by
  simp only [select, Id.run, getValue] at *
  rcases x <;> rcases y
  <;> simp [llvm_toBitVec, isPoison] at *
  <;> grind


/-! # Examples
  The following section includes examples we are using to compare across all the different implementations.
-/

/-- We can prove some basic properties about LLVM operations. -/
example (x y : Int 64) : (add x y) ⊑ (add y x) := by
  simp (contextual := true) [llvm_toBitVec]
  bv_decide

example (x y : Int 64)  :
    sub x (sub (constant 64 0) y) ⊑ add x y := by
  simp (contextual := true) [llvm_toBitVec]
  bv_normalize

end Int
