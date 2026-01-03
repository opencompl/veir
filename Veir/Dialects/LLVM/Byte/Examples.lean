module

import Std.Tactic.BVDecide
public import Veir.Dialects.LLVM.Int.Basic
import all Veir.Dialects.LLVM.Byte.Basic
import all Veir.Dialects.LLVM.Byte.Lemmas

namespace Veir.Dialects.LLVM.Byte

example (w : Nat) (x y : Byte w) : x ||| y = y ||| x := by
  simp only [or_eq]
  simp [BitVec.or_comm (x.poison) (y.poison), BitVec.or_comm (x.val) (y.val)]

example (x y : Byte 8) : x ||| y = y ||| x := by
  rw [ext_iff]
  simp [or_eq]
  bv_decide

end Veir.Dialects.LLVM.Byte
