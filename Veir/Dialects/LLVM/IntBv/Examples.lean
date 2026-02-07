module

import Std.Tactic.BVDecide
import Veir.Dialects.LLVM.IntBv.Basic
import all Veir.Dialects.LLVM.IntBv.Lemmas

namespace Veir.Dialects.LLVM.IntBv

example (w : Nat) (x y : IntBv w) : x + y = y + x := by
  grind

example (x y : IntBv 8) : x + y = y + x := by
  bv_normalize
  bv_normalize -- We need to call bv_normalize twice for bv_decide to work.
  bv_decide

end Veir.Dialects.LLVM.IntBv
