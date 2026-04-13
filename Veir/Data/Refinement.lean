module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.RISCV.Reg.Basic

public section

/-!
  This file defines the refinement relation from the `LLVM.Int` to `RISCV.Reg` type.
-/


/--
  `LLVM.Int` is refined by `RISCV.Reg`.
-/
def IntIsRefinedByReg [DecidableEq Prop] (i : Veir.Data.LLVM.Int 64) (r : Veir.Data.RISCV.Reg) : Prop :=
  match i with
  | .val v => r.val = v
  | .poison => true
