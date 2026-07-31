module

public import Veir.Dialects.LLVM.Fold.Basic
public import Veir.Data.LLVM.Byte.Basic

import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Byte.Basic

public section

/-!
  Correctness proofs specific to the `llvm` fold table. The integer rows it
  shares with `arith` are proved in `Veir.Fold.Lemmas`.
-/

namespace Veir.Fold.Proofs

open Veir.Data

namespace Byte

/-- The LLVM shift tables also accept a byte-valued left operand. -/
theorem shl_zero (x : LLVM.Byte 8) (nuw : Bool) :
    LLVM.Byte.shl x (LLVM.Int.constant 8 0) nuw = x := by
  cases x
  cases nuw <;> simp [LLVM.Byte.shl, LLVM.Int.constant] <;> congr

theorem lshr_zero (x : LLVM.Byte 8) (exact : Bool) :
    LLVM.Byte.lshr x (LLVM.Int.constant 8 0) exact = x := by
  cases exact <;> simp [LLVM.Byte.lshr, LLVM.Int.constant]

end Byte

end Veir.Fold.Proofs
