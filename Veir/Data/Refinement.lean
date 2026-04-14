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
def isRefinedBy (i i' : Veir.Data.LLVM.Int 64) : Prop :=
  match i with
  | .val v =>
    match i' with
    | .val v' => v = v'
    | .poison => true
  | .poison => true
