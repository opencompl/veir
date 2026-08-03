module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting
public import Veir.Data.Refinement

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

import Veir.ForLean

public section

namespace Veir.Data.LLVM

/--
Prove the correctness of `llvm.add` widening with anyext.
-/
theorem add_widening (i i' : Veir.Data.LLVM.Int 32) (ext ext' : BitVec 32) (nuw nsw : Bool) :
    LLVM.Int.add i i' nuw nsw ⊒
      Veir.Data.LLVM.Int.trunc (Veir.Data.LLVM.Int.add
        (Veir.Data.LLVM.Int.ext i 64 ext (by grind))
        (Veir.Data.LLVM.Int.ext i' 64 ext' (by grind))
        false false
      ) 32 false false (by grind) := by
  veir_bv_decide

end Veir.Data.LLVM

end
