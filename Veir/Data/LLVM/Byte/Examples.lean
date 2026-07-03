module

meta import Veir.Meta.BVDecide

import Std.Tactic.BVDecide
import Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Byte.Lemmas


namespace Veir.Data.LLVM.Byte

example (w : Nat) (x y : Byte w) : x ||| y = y ||| x := by
  veir_bv_normalize; grind

example (x y : Byte 8) : x ||| y = y ||| x := by
  veir_bv_decide

example (x : Int 8) :
    (Byte.fromInt x).toInt = x := by
  veir_bv_decide

example (x : Byte 8) :
    (x.poison = 0 ∨ x.poison = .allOnes _) →
    (Byte.fromInt x.toInt) = x := by
  veir_bv_decide

example (x y : Byte 8) : (x ||| y).trunc 4 = x.trunc 4 ||| y.trunc 4 := by
  veir_bv_decide

example (x : Byte 8) : x.lshr .poison = allPoison := by
  veir_bv_decide

example (x : Byte 8) : x.lshr (.val 0#8) = x := by
  veir_bv_decide

example (x : Byte 8) : x.lshr (.val 8#8) = allPoison := by
  veir_bv_decide

end Veir.Data.LLVM.Byte
