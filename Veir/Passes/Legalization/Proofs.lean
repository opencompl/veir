module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
meta import Veir.Meta.PBVDecide

import Veir.ForLean

public section

namespace Veir.Data.LLVM

/--
  Prove the correctness of `llvm.add` widening with anyext.
  Currently bounded to 16 bits for performance.
-/
theorem add_widening (w t : Nat) (i i' : LLVM.Int w)
    (ext ext' : BitVec (t - w)) (nuw nsw : Bool)
    (hIsWiden : w < t) (h : t < 16) :
    LLVM.Int.add i i' nuw nsw ⊒
      LLVM.Int.trunc
        (LLVM.Int.add (LLVM.Int.ext i t ext hIsWiden)
          (LLVM.Int.ext i' t ext' hIsWiden) false false)
        w false false hIsWiden := by
  veir_bv_normalize
  constructor
  · simp
  · intros
    pbv_decide 16
    · bv_decide

end Veir.Data.LLVM

end
