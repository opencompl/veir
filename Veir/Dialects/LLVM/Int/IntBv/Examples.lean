module

import Veir.Dialects.LLVM.Int.IntBv.Basic
import Std.Tactic.BVDecide

open Veir.Dialects.LLVM.Int.IntBv

theorem IntBv.ext (l r : IntBv w) (h : l.val = r.val ∧ l.poison = r.poison) : l = r := sorry

open Veir.Dialects.LLVM.Int.IntBv

@[bv_normalize]
theorem ext_iff {w : Nat} (x y : IntBv w) :
    x = y ↔ (x.val = y.val ∧ x.poison = y.poison) := by
  constructor
  <;> rw [IntBv.mk.injEq]
  <;> simp

@[bv_normalize]
theorem add_eq {w : Nat} (x y : IntBv w) :
    x + y = if x.poison || y.poison then mk_poison else mk_val (x.val + y.val) := by
  rfl

example (x y : IntBv 8) : x + y = y + x := by
  rw [add_eq]

  bv_normalize
  bv_decide
