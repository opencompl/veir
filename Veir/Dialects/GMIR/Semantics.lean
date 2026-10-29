module

public meta import Veir.Meta.Tactic.BVDecide
public import Veir.Data.LLVM.Int.Bitblast
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Int.Bitblast

open Veir.Data.LLVM

namespace Veir.GMIR

public section

/--
 Like `LLVM.Int.select`, for a condition of any width, which is true when it is nonzero. This is the
 meaning gMIR's `G_SELECT` has on a target whose booleans are zero or one, such as RISC-V: LLVM
 leaves the meaning of a condition wider than `i1` to the target. For an `i1` condition, it is
 `select` (see `selectNonzero_one`).
-/
def selectNonzero {wc w : Nat} (c : Int wc) (x y : Int w) : Int w := Id.run do
  let .val c' := c | .poison
  if c' != 0#wc then x else y

@[veir_bv_normalize, grind =]
theorem isPoison_selectNonzero {wc w : Nat} (x y : Int w) (c : Int wc) :
    (selectNonzero c x y).isPoison =
      if h : c.isPoison = true then true
      else if c.getValue ≠ 0#wc then x.isPoison else y.isPoison := by
  cases c with
  | poison => simp [selectNonzero, Id.run, Int.isPoison]
  | val c' => by_cases hc : c' = 0#wc <;> simp [selectNonzero, Id.run, hc, Int.isPoison]

@[veir_bv_normalize, grind =]
theorem getValue_selectNonzero {wc w : Nat} (x y : Int w) (c : Int wc)
    (h : (selectNonzero c x y).isPoison = false) :
    (selectNonzero c x y).getValue h =
      if _ : c.getValue ≠ 0#wc then x.getValue else y.getValue := by
  cases c with
  | poison => simp [selectNonzero, Id.run, Int.isPoison] at h
  | val c' => by_cases hc : c' = 0#wc <;> simp [selectNonzero, Id.run, hc]

/-- For an `i1` condition, `selectNonzero` is `select`. -/
theorem selectNonzero_one {w : Nat} (c : Int 1) (x y : Int w) :
    selectNonzero c x y = Int.select c x y := by
  cases c with
  | poison => simp [selectNonzero, Int.select, Id.run]
  | val c' =>
    rcases BitVec.eq_zero_or_eq_one c' with rfl | rfl <;>
      simp [selectNonzero, Int.select, Id.run]

end

end Veir.GMIR
