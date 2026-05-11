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

  We set the priority of the lemma to `1` (low priority), such that it is only applied when no
  more simplifications are available. This ultimately allows `bv_decide` to reason about different
  instantiations of `getValue` without abstracting them separately.
-/
@[llvm_toBitVec 1]
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

/-- The value `getValue` of a `val v` is `v`. -/
@[llvm_toBitVec, grind =]
theorem getValue_of_val {w : Nat} {v : BitVec w} :
    (val v).getValue (by grind [isPoison]) = v := rfl

/-- An element `val v` is not poison. -/
@[llvm_toBitVec, grind =]
theorem isPoison_of_val {w : Nat} {v : BitVec w} :
    (val v).isPoison = false := rfl

/-- A `poison` element is poison. -/
@[llvm_toBitVec, grind =]
theorem isPoison_of_poison {w : Nat} :
    poison.isPoison (w := w) = true := rfl

/-- An element `b : LLVM.Int` refines an element `a : LLVM.Int` if either `a` is a poison value
  (in which case, any concrete or poison value refines it) or if `a` is not a poison value,
  `b` is not a poison value, and their concrete bitvector values are the same. -/
@[llvm_toBitVec, grind =]
theorem isRefinedBy_iff {w : Nat} (a b : Int w) :
  a ⊑ b ↔
    (a.isPoison = false → b.isPoison = false) ∧
    ((_ : a.isPoison = false) → (_ : b.isPoison = false) → a.getValue = b.getValue) := by
  simp [isRefinedBy, llvm_toBitVec, isPoison, getValue]
  grind

end Int
