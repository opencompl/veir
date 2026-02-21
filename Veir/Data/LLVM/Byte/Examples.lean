module

import Std.Tactic.BVDecide
import Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Byte.Lemmas


namespace Veir.Data.LLVM.Byte

example (w : Nat) (x y : Byte w) : x ||| y = y ||| x := by
  simp only [or_eq]
  simp [BitVec.or_comm (x.poison) (y.poison), BitVec.or_comm (x.val) (y.val)]

example (x y : Byte 8) : x ||| y = y ||| x := by
  bv_decide

end Veir.Data.LLVM.Byte
