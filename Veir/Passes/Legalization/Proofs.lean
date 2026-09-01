module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting
public import Veir.Meta.PBVDecide

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

import Veir.ForLean

public section

namespace Veir.Data.LLVM

/--
Prove the correctness of `llvm.add` widening with anyext.
-/
theorem add_widening_32_64 (i i' : LLVM.Int 32) (ext ext' : BitVec 32) (nuw nsw : Bool) :
    LLVM.Int.add i i' nuw nsw ⊒
      LLVM.Int.trunc (LLVM.Int.add
        (LLVM.Int.ext i 64 ext (by grind))
        (LLVM.Int.ext i' 64 ext' (by grind))
        false false
      ) 32 false false (by grind) := by
  veir_bv_decide

theorem add_widening_generic (w t : Nat) (i i' : LLVM.Int w) (ext ext' : BitVec (t - w)) (nuw nsw : Bool)
  (hIsWiden : w < t) :
    LLVM.Int.add i i' nuw nsw ⊒
      LLVM.Int.trunc (LLVM.Int.add
        (LLVM.Int.ext i t ext (by grind))
        (LLVM.Int.ext i' t ext' (by grind))
        false false
      ) w false false (by grind) := by
  veir_bv_normalize
  . pbv_decide 64

end Veir.Data.LLVM

end
