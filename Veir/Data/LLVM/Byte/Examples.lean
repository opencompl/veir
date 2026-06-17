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

end Veir.Data.LLVM.Byte
