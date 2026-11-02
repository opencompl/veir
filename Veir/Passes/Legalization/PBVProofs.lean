module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting
public import Veir.Dialects.GMIR.Semantics

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

import Veir.ForLean
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.GMIR.Semantics

import Veir.Meta.Tactic.PBVDecide

public section

namespace Veir.Data.LLVM

/--
Prove the correctness of `llvm.add` widening with anyext.
-/
theorem add_widening {w v : Nat} (i i' : LLVM.Int w) (ext ext' : BitVec v) (nuw nsw : Bool) (h : w + v ≤ 64) (hv : v > 0):
    LLVM.Int.add i i' nuw nsw ⊒
      LLVM.Int.trunc (LLVM.Int.add
        (LLVM.Int.ext i (w + v) (ext.cast (by grind)) (by grind))
        (LLVM.Int.ext i' (w + v) (ext'.cast (by grind)) (by grind))
        false false
      ) w false false (by grind) := by
  veir_bv_normalize
  -- generalize i.isPoison = i_poison
  -- generalize i'.isPoison = i'_poison
  -- generalize i.getValueD = bv_i
  -- generalize i'.getValueD = bv_i'
  -- clear i i'
  pbv_decide 64 -bv_decide

theorem add_widening_32_64 (i i' : LLVM.Int 32) (ext ext' : BitVec 32) (nuw nsw : Bool) :
    LLVM.Int.add i i' nuw nsw ⊒
      LLVM.Int.trunc (LLVM.Int.add
        (LLVM.Int.ext i 64 ext (by grind))
        (LLVM.Int.ext i' 64 ext' (by grind))
        false false
      ) 32 false false (by grind) := by
  veir_bv_normalize
  bv_decide

end Veir.Data.LLVM

end
