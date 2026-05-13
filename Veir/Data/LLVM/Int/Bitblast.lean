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
