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
  as the same and abstracts them to separate terms.
-/
@[llvm_toBitVec 1]
theorem getValue_eq_getValueD {w : Nat} (x : Int w) (h : x.isPoison = false) :
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
