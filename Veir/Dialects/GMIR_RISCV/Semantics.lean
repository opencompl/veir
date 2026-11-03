module

public import Veir.Data.LLVM.Int.Basic

open Veir.Data.LLVM

namespace Veir.GMIR_RISCV

public section

/--
 `f` on the low 32 bits of `x` and `y`, sign-extended to 64 bits, as a word operation computes it.
-/
def word (f : Int 32 → Int 32 → Int 32) (x y : Int 64) : Int 64 :=
  Int.sext (f (x.trunc 32 false false (by decide)) (y.trunc 32 false false (by decide))) 64
    (by decide)

/--
 `f` on the low 32 bits of `x`, sign-extended to 64 bits, as a unary word operation computes it.
-/
def wordUnary (f : Int 32 → Int 32) (x : Int 64) : Int 64 :=
  Int.sext (f (x.trunc 32 false false (by decide))) 64 (by decide)

/-- The amount of a word shift, which reads only the low 5 bits of `y`. -/
def wordShiftAmount (y : Int 32) : Int 32 :=
  Int.and y (.val 31#32)

end

end Veir.GMIR_RISCV
