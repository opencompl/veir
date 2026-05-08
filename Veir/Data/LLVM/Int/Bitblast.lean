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
def getValue {w : Nat} (x : Int w) (h : x.isPoison = false := by grind) : BitVec w :=
  match x, h with
  | .val v, _ => v

def getValueD {w : Nat} (x : Int w) : BitVec w :=
  match x with
  | .poison => 0#w
  | .val v => v

/--
  Low priority rule to convert getValue to getValueD once no more simplification can be done.
  This is needed because `bv_decide` cannot see different instantiations of `x.getValue proof`
  as the same and abstracts them to separate values.
-/
@[llvm_toBitVec 1]
theorem getValue_eq_getValueD {w : Nat} (x : Int w) (h : x.isPoison = false := by grind) :
    x.getValue h = x.getValueD := by
  unfold getValue getValueD
  grind

@[llvm_toBitVec]
theorem eq_iff {w : Nat} (a b : Int w) :
  a = b ↔
    a.isPoison = b.isPoison ∧
    ((_ : a.isPoison = false) → (_ : b.isPoison = false) → a.getValue = b.getValue) := by
  unfold isPoison getValue
  grind

@[llvm_toBitVec, grind =]
theorem isRefinedBy_iff {w : Nat} (a b : Int w) :
  a ⊑ b ↔
    (a.isPoison = false → b.isPoison = false) ∧
    ((_ : a.isPoison = false) → (_ : b.isPoison = false) → a.getValue = b.getValue) := by
  unfold isRefinedBy isPoison getValue
  grind

@[llvm_toBitVec, grind =]
theorem getValue_of_val {w : Nat} {v : BitVec w} :
    (val v).getValue (by grind [isPoison]) = v := rfl

@[llvm_toBitVec, grind =]
theorem isPoison_of_val {w : Nat} {v : BitVec w} :
    (val v).isPoison = false := rfl

@[llvm_toBitVec, grind =]
theorem isPoison_of_poison {w : Nat} :
    poison.isPoison (w := w) = true := rfl

/-! # LLVM IR operations unfolding to `toIntBv` -/

@[llvm_toBitVec, grind =]
theorem getValue_constant {w : Nat} (v : _root_.Int) :
    (constant w v).getValue (by grind [constant]) = BitVec.ofInt w v := rfl

@[llvm_toBitVec, grind =]
theorem isPoison_constant {w : Nat} (v : _root_.Int) :
    (constant w v).isPoison = false := rfl

@[llvm_toBitVec, grind =]
theorem isPoison_add {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (add x y nsw nuw).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then
        true
      else
        (nsw ∧ BitVec.saddOverflow x.getValue y.getValue) ∨
        (nuw ∧ BitVec.uaddOverflow x.getValue y.getValue) := by
  simp only [add, isPoison, getValue, Id.run, pure_bind]
  simp only [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_add {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (add x y nsw nuw).isPoison = false) :
    (add x y nsw nuw).getValue h = x.getValue + y.getValue := by
  unfold add
  grind [Id.run]

@[llvm_toBitVec, grind =]
theorem isPoison_sub {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (sub x y nsw nuw).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then
        true
      else
        (nsw ∧ BitVec.ssubOverflow x.getValue y.getValue) ∨
        (nuw ∧ BitVec.usubOverflow x.getValue y.getValue) := by
  simp only [sub, isPoison, getValue, Id.run, pure_bind]
  simp only [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_sub {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (sub x y nsw nuw).isPoison = false) :
    (sub x y nsw nuw).getValue h = x.getValue - y.getValue := by
  unfold sub
  grind [Id.run]

@[llvm_toBitVec, grind =]
theorem isPoison_mul {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (mul x y nsw nuw).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then
        true
      else
        (nsw ∧ BitVec.smulOverflow x.getValue y.getValue) ∨
        (nuw ∧ BitVec.umulOverflow x.getValue y.getValue) := by
  simp only [mul, isPoison, getValue, Id.run, pure_bind]
  simp only [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_mul {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (mul x y nsw nuw).isPoison = false) :
    (mul x y nsw nuw).getValue h = x.getValue * y.getValue := by
  unfold mul
  grind [Id.run]

@[llvm_toBitVec, grind =]
theorem isPoison_udiv {w : Nat} (x y : Int w) {exact : Bool} :
    (udiv x y exact).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then
        true
      else
        (exact ∧ BitVec.umod x.getValue y.getValue ≠ 0) ∨
        (y.getValue = 0) := by
  simp only [udiv, isPoison, getValue, Id.run, pure_bind]
  simp only [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_udiv {w : Nat} (x y : Int w) {exact : Bool} (h : (udiv x y exact).isPoison = false) :
    (udiv x y exact).getValue h = x.getValue.udiv y.getValue := by
  unfold udiv
  grind [Id.run]

@[llvm_toBitVec, grind =]
theorem isPoison_sdiv {w : Nat} (x y : Int w) {exact : Bool} :
    (sdiv x y exact).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then
        true
      else
        (y.getValue == 0 || (w != 1 && x.getValue == (BitVec.intMin w) && y.getValue == -1)) ∨
        (exact ∧ BitVec.smod x.getValue y.getValue ≠ 0) ∨
        (y.getValue = 0) := by
  simp only [sdiv, isPoison, getValue, Id.run, pure_bind]
  simp only [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_sdiv {w : Nat} (x y : Int w) {exact : Bool} (h : (sdiv x y exact).isPoison = false) :
    (sdiv x y exact).getValue h = x.getValue.sdiv y.getValue := by
  unfold sdiv
  grind [Id.run]

@[llvm_toBitVec, grind =]
theorem isPoison_urem {w : Nat} (x y : Int w) :
    (urem x y).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then
        true
      else
        y.getValue = 0 := by
  simp only [urem, isPoison, getValue, Id.run, pure_bind]
  simp only [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_urem {w : Nat} (x y : Int w) (h : (urem x y).isPoison = false) :
    (urem x y).getValue h = x.getValue.umod y.getValue := by
  unfold urem
  grind [Id.run]

@[llvm_toBitVec, grind =]
theorem isPoison_srem {w : Nat} (x y : Int w) :
    (srem x y).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then
        true
      else
        (y.getValue == 0 || (w != 1 && x.getValue  == (BitVec.intMin w) && y.getValue == -1)) := by
  simp only [srem, isPoison, getValue, Id.run, pure_bind]
  simp only [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_srem {w : Nat} (x y : Int w) (h : (srem x y).isPoison = false) :
    (srem x y).getValue h = x.getValue.srem y.getValue := by
  unfold srem
  grind [Id.run]

@[llvm_toBitVec, grind =]
theorem isPoison_shl {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (shl x y nsw nuw).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then
        true
      else
        (nsw ∧ (x.getValue <<< y.getValue).sshiftRight' y.getValue ≠ x.getValue) ∨
        (nuw ∧ (x.getValue <<< y.getValue) >>> y.getValue ≠ x.getValue) ∨
        (y.getValue ≥ w) := by
  simp only [shl, isPoison, getValue, Id.run, pure_bind]
  simp only [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_shl {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (shl x y nsw nuw).isPoison = false) :
    (shl x y nsw nuw).getValue h = x.getValue <<< y.getValue := by
  unfold shl
  grind [Id.run]

@[llvm_toBitVec, grind =]
theorem isPoison_lshr {w : Nat} (x y : Int w) {exact : Bool} :
    (lshr x y exact).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then
        true
      else
        y.getValue ≥ w ∨
        (exact ∧ (x.getValue >>> y.getValue) <<< y.getValue ≠ x.getValue) := by
  simp only [lshr, isPoison, getValue, Id.run, pure_bind]
  simp only [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_lshr {w : Nat} (x y : Int w) {exact : Bool} (h : (lshr x y exact).isPoison = false) :
    (lshr x y exact).getValue h = x.getValue >>> y.getValue := by
  unfold lshr
  grind [Id.run]

@[llvm_toBitVec, grind =]
theorem isPoison_ashr {w : Nat} (x y : Int w) {exact : Bool} :
    (ashr x y exact).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then
        true
      else
        y.getValue ≥ w ∨
        (exact ∧ (x.getValue >>> y.getValue) <<< y.getValue ≠ x.getValue) := by
  simp only [ashr, isPoison, getValue, Id.run, pure_bind]
  simp only [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_ashr {w : Nat} (x y : Int w) {exact : Bool} (h : (ashr x y exact).isPoison = false) :
    (ashr x y exact).getValue h = x.getValue.sshiftRight' y.getValue := by
  unfold ashr
  grind [Id.run]

@[llvm_toBitVec, grind =]
theorem isPoison_cast {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ = w₂) :
    (cast x h).isPoison = x.isPoison := by
  unfold cast isPoison
  grind

@[llvm_toBitVec, grind =]
theorem getValue_cast {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ = w₂) (hpoison : (cast x h).isPoison = false) :
    (cast x h).getValue hpoison = x.getValue.cast h := by
  unfold cast getValue
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_and {w : Nat} (x y : Int w) :
    (and x y).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp only [and, isPoison, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_and {w : Nat} (x y : Int w) (h : (and x y).isPoison = false) :
    (and x y).getValue h = x.getValue &&& y.getValue := by
  simp only [and, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_or {w : Nat} (x y : Int w) {disjoint : Bool} :
    (or x y disjoint).isPoison =
      if h : x.isPoison ∨ y.isPoison then
        true
      else
        disjoint ∧ ((x.getValue &&& y.getValue) ≠ 0) := by
  simp only [or, isPoison, getValue, Id.run, pure_bind]
  simp only [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_or {w : Nat} (x y : Int w) {disjoint : Bool} (h : (or x y disjoint).isPoison = false) :
    (or x y disjoint).getValue h = x.getValue ||| y.getValue := by
  unfold or
  grind [Id.run]

@[llvm_toBitVec, grind =]
theorem isPoison_xor {w : Nat} (x y : Int w) :
    (xor x y).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp only [xor, isPoison, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_xor {w : Nat} (x y : Int w) (h : (xor x y).isPoison = false) :
    (xor x y).getValue h = x.getValue ^^^ y.getValue := by
  simp only [xor, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_trunc {w₁ w₂: Nat} (x : Int w₁) {nsw nuw : Bool} (h : w₁ > w₂) :
    (trunc x w₂ nsw nuw h).isPoison =
      if h : x.isPoison then
        true
      else
        (nsw ∧ (x.getValue.truncate w₂).signExtend w₁ ≠ x.getValue) ∨
        (nuw ∧ (x.getValue.truncate w₂).zeroExtend w₁ ≠ x.getValue) := by
  simp only [trunc, isPoison, getValue, Id.run, pure_bind]
  simp only [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_trunc {w₁ w₂: Nat} (x : Int w₁) {nsw nuw : Bool} (h : w₁ > w₂) (hpoison : (trunc x w₂ nsw nuw h).isPoison = false) :
    (trunc x w₂ nsw nuw h).getValue hpoison = x.getValue.truncate w₂ := by
  unfold trunc
  grind [Id.run]

@[llvm_toBitVec, grind =]
theorem isPoison_zext {w₁ w₂: Nat} (x : Int w₁) {nneg : Bool} (h : w₁ < w₂) :
    (zext x w₂ nneg h).isPoison =
      if h : x.isPoison then
        true
      else
        nneg ∧ x.getValue.msb := by
  simp only [zext, isPoison, getValue, Id.run, pure_bind]
  simp only [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_zext (x : Int w₁) {nneg : Bool} (h : w₁ < w₂) (hpoison : (zext x w₂ nneg h).isPoison = false) :
    (zext x w₂ nneg h).getValue hpoison = x.getValue.zeroExtend w₂ := by
  unfold zext
  grind [Id.run]

@[llvm_toBitVec, grind =]
theorem isPoison_sext {w₁ w₂: Nat} (x : Int w₁) (h : w₁ < w₂) :
    (sext x w₂ h).isPoison = x.isPoison := by
  simp only [sext, isPoison, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_sext (x : Int w₁) (h : w₁ < w₂) (hpoison : (sext x w₂ h).isPoison = false) :
    (sext x w₂ h).getValue hpoison = x.getValue.signExtend w₂ := by
  simp only [sext, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_icmp {w : Nat} (x y : Int w) (p : IntPred) :
    (icmp x y p).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp only [icmp, isPoison, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_icmp {w : Nat} (x y : Int w) (p : IntPred) (h : (icmp x y p).isPoison = false) :
    (icmp x y p).getValue h = BitVec.ofBool (IntPred.eval p x.getValue y.getValue) := by
  simp only [icmp, Id.run]
  grind

attribute [llvm_toBitVec, grind =] IntPred.eval

@[llvm_toBitVec, grind =]
theorem isPoison_select {w : Nat} (x y : Int w) (c : Int 1) :
    (select c x y).isPoison = decide (x.isPoison ∨ y.isPoison ∨ c.isPoison) := by
  simp only [select, isPoison, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_select {w : Nat} (x y : Int w) (c : Int 1) (h : (select c x y).isPoison = false) :
    (select c x y).getValue = if c.getValue == 1#1 then x.getValue else y.getValue := by
  simp only [select, Id.run]
  grind


/-! # Examples
  The following section includes examples we are using to compare across all the different implementations.
-/

/-- We can prove some basic properties about LLVM operations. -/
example (x y : Int 64) : (add x y (nsw := true)) ⊑ (add y x) := by
  simp [llvm_toBitVec]
  bv_decide

example (x y : Int 64)  :
    sub x (sub (constant 64 0) y) ⊑ add x y := by
  simp [llvm_toBitVec]

end Int
