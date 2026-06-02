module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.RISCV.Reg.Basic

public section

/-!
  This file defines the refinement relation from the `LLVM.Int` to `RISCV.Reg` type.
-/

/--
  `LLVM.Int` is refined by `LLVM.Int`.
  `i'` refines `i` if its behaviour are a subset of the behaviours allowed by `i`.
  In particular, any concrete `i'` refines a poison `i`, but a poison `i'` does *not* refine
  any `i`.
-/
def isRefinedBy {w : Nat} (i i' : Veir.Data.LLVM.Int w) : Prop :=
  match i, i' with
  | .val v, .val v' => v = v'
  | .val _, .poison => False
  | .poison, _ => True

@[inherit_doc] infix:50 " ⊑ "  => isRefinedBy

theorem isRefinedBy_eq {w : Nat} (i i' : Veir.Data.LLVM.Int w) :
  i ⊑ i' ↔ (match i, i' with
            | .val v, .val v' => v = v'
            | .val _, .poison => False
            | .poison, _ => True) := by rfl
