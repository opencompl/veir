module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Refinement
public import Veir.Data.LLVM.Int.Simp
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement

open Veir.Data.LLVM

namespace Veir.Data.LLVM.Int

public section

/-- Return true if the LLVM.Int `x` is poison. -/
def isPoison {w : Nat} : (x : Int w) -> Bool
  | .poison => true
  | .val _ => false

/-- Return the bitvector value of a non-poison `LLVM.Int`. -/
def getValue {w : Nat} (x : Int w) (h : x.isPoison = false := by grind) : BitVec w :=
  match x, h with
  | .val v, _ => v

/-- Return the bitvector value `v` of an `LLVM.Int` if it is not poison,
  or a zero bitvector `0#w` otherwise. -/
def getValueD {w : Nat} (x : Int w) : BitVec w :=
  match x with
  | .poison => 0#w
  | .val v => v

/-- The bitvector value of a non-poison `LLVM.Int` via `getValue` is equal to the default one,
  obtained by `getValueD`.
  This lemma should be applied when no more simplifications are available, such that `bv_decide` can
  reason about different instantiations of `getValue` without abstracting them separately.
-/
theorem getValue_eq_getValueD {w : Nat} (x : Int w) (h : x.isPoison = false) :
    x.getValue h = x.getValueD := by
  simp [getValue, getValueD]
  cases x <;> grind

/-- Two elements `a b : LLVM.Int` are equal if and only if they return the same `isPoison` and,
  the same `getValue` in case they are *not* poison. -/
@[llvm_toBitVec]
theorem eq_iff {w : Nat} (a b : Int w) :
  a = b ↔
    (a.isPoison = b.isPoison) ∧
    ((_ : a.isPoison = false) → (_ : b.isPoison = false) → a.getValue = b.getValue) := by
  simp [isPoison, getValue, llvm_toBitVec]
  grind

@[ext, grind ext]
theorem eq_ext {w : Nat} {a b : Int w} (hp : a.isPoison = b.isPoison) (hv : (a.getValueD = b.getValueD)) :
    a = b := by
  cases a <;> cases b
  · simpa using hv
  · simp [isPoison] at hp
  · simp [isPoison] at hp
  · simp

/-- The value `getValue` of a `val v` is `v`. -/
@[llvm_toBitVec, grind =]
theorem getValue_of_val {w : Nat} {v : BitVec w} :
    (val v).getValue (by grind [isPoison]) = v := by rfl

/-- An element `val v` is not poison. -/
@[llvm_toBitVec, grind =]
theorem isPoison_of_val {w : Nat} {v : BitVec w} :
    (val v).isPoison = false := by rfl

/-- A `poison` element is poison. -/
@[llvm_toBitVec, grind =]
theorem isPoison_of_poison {w : Nat} :
    poison.isPoison (w := w) = true := by rfl

/-- An element `b : LLVM.Int` refines an element `a : LLVM.Int` if either `a` is a poison value
  (in which case, any concrete or poison value refines it) or if `a` is not a poison value,
  `b` is not a poison value, and their concrete bitvector values are the same. -/
@[llvm_toBitVec, grind =]
theorem isRefinedBy_iff {w : Nat} (a b : Int w) :
  a ⊑ b ↔
    (a.isPoison = false → b.isPoison = false) ∧
    ((_ : a.isPoison = false) → (_ : b.isPoison = false) → a.getValue = b.getValue) := by
  simp [llvm_toBitVec, isPoison, getValue]
  grind [isRefinedBy]

/-! # LLVM IR operations unfolding to `toIntBv` -/

@[llvm_toBitVec, grind =]
theorem getValue_constant {w : Nat} (v : _root_.Int) :
    (constant w v).getValue (by grind [constant]) = BitVec.ofInt w v := by rfl

@[llvm_toBitVec, grind =]
theorem isPoison_constant {w : Nat} (v : _root_.Int) :
    (constant w v).isPoison = false := by rfl

@[llvm_toBitVec, grind =]
theorem isPoison_add {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (add x y nsw nuw).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        (nsw ∧ BitVec.saddOverflow x.getValue y.getValue) ∨
        (nuw ∧ BitVec.uaddOverflow x.getValue y.getValue) := by
  simp only [isPoison, add, Id.run, pure_bind, getValue, Bool.decide_or, Bool.decide_and,
    Bool.decide_eq_true]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_add {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (add x y nsw nuw).isPoison = false) :
    (add x y nsw nuw).getValue h = x.getValue + y.getValue := by
  simp [add, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_sub {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (sub x y nsw nuw).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        (nsw ∧ BitVec.ssubOverflow x.getValue y.getValue) ∨
        (nuw ∧ BitVec.usubOverflow x.getValue y.getValue) := by
  simp only [isPoison, sub, Id.run, pure_bind, getValue, Bool.decide_or, Bool.decide_and,
    Bool.decide_eq_true]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_sub {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (sub x y nsw nuw).isPoison = false) :
    (sub x y nsw nuw).getValue h = x.getValue - y.getValue := by
  simp [sub, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_mul {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (mul x y nsw nuw).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        (nsw ∧ BitVec.smulOverflow x.getValue y.getValue) ∨
        (nuw ∧ BitVec.umulOverflow x.getValue y.getValue) := by
  simp only [mul, isPoison, getValue, Id.run, pure_bind]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_mul {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (mul x y nsw nuw).isPoison = false) :
    (mul x y nsw nuw).getValue h = x.getValue * y.getValue := by
  simp [mul, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_udiv {w : Nat} (x y : Int w) {exact : Bool} :
    (udiv x y exact).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        (exact ∧ BitVec.umod x.getValue y.getValue ≠ 0) ∨
        (y.getValue = 0) := by
  simp only [udiv, isPoison, getValue, Id.run, pure_bind]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_udiv {w : Nat} (x y : Int w) {exact : Bool} (h : (udiv x y exact).isPoison = false) :
    (udiv x y exact).getValue h = x.getValue.udiv y.getValue := by
  simp [udiv, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_sdiv {w : Nat} (x y : Int w) {exact : Bool} :
    (sdiv x y exact).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        (y.getValue = 0 ∨ (w ≠ 1 ∧ x.getValue = (BitVec.intMin w) ∧ y.getValue = -1)) ∨
        (exact ∧ BitVec.smod x.getValue y.getValue ≠ 0) ∨
        (y.getValue = 0) := by
  simp only [sdiv, isPoison, getValue, Id.run, pure_bind]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_sdiv {w : Nat} (x y : Int w) {exact : Bool} (h : (sdiv x y exact).isPoison = false) :
    (sdiv x y exact).getValue h = x.getValue.sdiv y.getValue := by
  simp [sdiv, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_urem {w : Nat} (x y : Int w) :
    (urem x y).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        y.getValue = 0 := by
  simp only [urem, isPoison, getValue, Id.run, pure_bind]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_urem {w : Nat} (x y : Int w) (h : (urem x y).isPoison = false) :
    (urem x y).getValue h = x.getValue.umod y.getValue := by
  simp [urem, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_srem {w : Nat} (x y : Int w) :
    (srem x y).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        (y.getValue = 0 ∨ (w ≠ 1 ∧ x.getValue = (BitVec.intMin w) ∧ y.getValue = -1)) := by
  simp only [srem, isPoison, getValue, Id.run, pure_bind]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_srem {w : Nat} (x y : Int w) (h : (srem x y).isPoison = false) :
    (srem x y).getValue h = x.getValue.srem y.getValue := by
  simp [srem, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_shl {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (shl x y nsw nuw).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        (nsw ∧ (x.getValue <<< y.getValue).sshiftRight' y.getValue ≠ x.getValue) ∨
        (nuw ∧ (x.getValue <<< y.getValue) >>> y.getValue ≠ x.getValue) ∨
        (y.getValue ≥ w) := by
  simp only [shl, isPoison, getValue, Id.run, pure_bind]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_shl {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (shl x y nsw nuw).isPoison = false) :
    (shl x y nsw nuw).getValue h = x.getValue <<< y.getValue := by
  simp only [shl, Id.run, BitVec.shiftLeft_eq', BitVec.sshiftRight_eq', ne_eq,
    BitVec.ushiftRight_eq', BitVec.natCast_eq_ofNat, ge_iff_le, pure_bind]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_lshr {w : Nat} (x y : Int w) {exact : Bool} :
    (lshr x y exact).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        y.getValue ≥ w ∨
        (exact ∧ (x.getValue >>> y.getValue) <<< y.getValue ≠ x.getValue) := by
  simp only [lshr, isPoison, getValue, Id.run, pure_bind]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_lshr {w : Nat} (x y : Int w) {exact : Bool} (h : (lshr x y exact).isPoison = false) :
    (lshr x y exact).getValue h = x.getValue >>> y.getValue := by
  simp only [lshr, Id.run, BitVec.natCast_eq_ofNat, ge_iff_le, BitVec.ushiftRight_eq',
    BitVec.shiftLeft_eq', ne_eq, pure_bind]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_ashr {w : Nat} (x y : Int w) {exact : Bool} :
    (ashr x y exact).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        y.getValue ≥ w ∨
        (exact ∧ (x.getValue >>> y.getValue) <<< y.getValue ≠ x.getValue) := by
  simp only [ashr, isPoison, getValue, Id.run, pure_bind]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_ashr {w : Nat} (x y : Int w) {exact : Bool} (h : (ashr x y exact).isPoison = false) :
    (ashr x y exact).getValue h = x.getValue.sshiftRight' y.getValue := by
  simp only [ashr, Id.run, BitVec.natCast_eq_ofNat, ge_iff_le, BitVec.ushiftRight_eq',
    BitVec.shiftLeft_eq', ne_eq, BitVec.sshiftRight_eq', pure_bind]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_cast {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ = w₂) :
    (cast x h).isPoison = x.isPoison := by
  simp [cast, isPoison]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_cast {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ = w₂) (hpoison : (cast x h).isPoison = false) :
    (cast x h).getValue hpoison = x.getValue.cast h := by
  simp [cast, getValue]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_and {w : Nat} (x y : Int w) :
    (and x y).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp [and, isPoison, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_and {w : Nat} (x y : Int w) (h : (and x y).isPoison = false) :
    (and x y).getValue h = x.getValue &&& y.getValue := by
  simp [and, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_or {w : Nat} (x y : Int w) {disjoint : Bool} :
    (or x y disjoint).isPoison =
      if h : x.isPoison ∨ y.isPoison then true
      else
        disjoint ∧ ((x.getValue &&& y.getValue) ≠ 0) := by
  simp only [or, isPoison, getValue, Id.run, pure_bind]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_or {w : Nat} (x y : Int w) {disjoint : Bool} (h : (or x y disjoint).isPoison = false) :
    (or x y disjoint).getValue h = x.getValue ||| y.getValue := by
  simp [or, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_xor {w : Nat} (x y : Int w) :
    (xor x y).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp [xor, isPoison, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_xor {w : Nat} (x y : Int w) (h : (xor x y).isPoison = false) :
    (xor x y).getValue h = x.getValue ^^^ y.getValue := by
  simp [xor, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_trunc {w₁ w₂: Nat} (x : Int w₁) {nsw nuw : Bool} (h : w₁ > w₂) :
    (trunc x w₂ nsw nuw h).isPoison =
      if h : x.isPoison then true
      else
        (nsw ∧ (x.getValue.truncate w₂).signExtend w₁ ≠ x.getValue) ∨
        (nuw ∧ (x.getValue.truncate w₂).zeroExtend w₁ ≠ x.getValue) := by
  simp only [trunc, isPoison, getValue, Id.run, pure_bind]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_trunc {w₁ w₂: Nat} (x : Int w₁) {nsw nuw : Bool} (h : w₁ > w₂) (hpoison : (trunc x w₂ nsw nuw h).isPoison = false) :
    (trunc x w₂ nsw nuw h).getValue hpoison = x.getValue.truncate w₂ := by
  simp [trunc, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_zext {w₁ w₂: Nat} (x : Int w₁) {nneg : Bool} (h : w₁ < w₂) :
    (zext x w₂ nneg h).isPoison =
      if h : x.isPoison then true
      else
        nneg ∧ x.getValue.msb := by
  simp only [zext, isPoison, getValue, Id.run, pure_bind]
  simp [pure]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_zext (x : Int w₁) {nneg : Bool} (h : w₁ < w₂) (hpoison : (zext x w₂ nneg h).isPoison = false) :
    (zext x w₂ nneg h).getValue hpoison = x.getValue.zeroExtend w₂ := by
  simp [zext, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_sext {w₁ w₂: Nat} (x : Int w₁) (h : w₁ < w₂) :
    (sext x w₂ h).isPoison = x.isPoison := by
  simp [sext, isPoison, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_sext {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ < w₂) (hpoison : (sext x w₂ h).isPoison = false) :
    (sext x w₂ h).getValue hpoison = x.getValue.signExtend w₂ := by
  simp [sext, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem isPoison_icmp {w : Nat} (x y : Int w) (p : IntPred) :
    (icmp x y p).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp [icmp, isPoison, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_icmp {w : Nat} (x y : Int w) (p : IntPred) (h : (icmp x y p).isPoison = false) :
    (icmp x y p).getValue h = BitVec.ofBool (IntPred.eval p x.getValue y.getValue) := by
  simp [icmp, Id.run]
  grind

attribute [llvm_toBitVec, grind =] IntPred.eval

@[llvm_toBitVec, grind =]
theorem isPoison_select {w : Nat} (x y : Int w) (c : Int 1) :
    (select c x y).isPoison = decide (x.isPoison ∨ y.isPoison ∨ c.isPoison) := by
  simp [select, isPoison, Id.run]
  grind

@[llvm_toBitVec, grind =]
theorem getValue_select {w : Nat} (x y : Int w) (c : Int 1) (h : (select c x y).isPoison = false) :
    (select c x y).getValue h = if c.getValue = 1#1 then x.getValue else y.getValue := by
  simp [select, Id.run]
  grind
