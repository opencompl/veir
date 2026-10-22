module

meta import Veir.Meta.Tactic.BVDecide

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

-- The `nsw` and `nuw` flags of `trunc` and `shl` either keep the result or make all of it poison.
example (x : Byte 8) (nsw nuw : Bool) :
    x.trunc 4 nsw nuw = x.trunc 4 ∨ x.trunc 4 nsw nuw = allPoison := by
  veir_bv_decide

example (x : Byte 8) (y : Int 8) (nsw nuw : Bool) :
    x.shl y nsw nuw = x.shl y ∨ x.shl y nsw nuw = allPoison := by
  veir_bv_decide

-- `trunc nuw` keeps the poison of the remaining bits, but a poison bit it drops makes all of it
-- poison.
example (x : Byte 8) :
    x.val >>> 4 = 0 → x.poison >>> 4 = 0 → x.trunc 4 (nuw := true) = x.trunc 4 := by
  veir_bv_decide

example (x : Byte 8) : x.poison >>> 4 ≠ 0 → x.trunc 4 (nuw := true) = allPoison := by
  veir_bv_decide

example (x : Byte 8) : x.lshr .poison = allPoison := by
  veir_bv_decide

example (x : Byte 8) : x.lshr (.val 0#8) = x := by
  veir_bv_decide

example (x : Byte 8) : x.lshr (.val 8#8) = allPoison := by
  veir_bv_decide

end Veir.Data.LLVM.Byte
