module

import all Veir.Data.LLVM.Byte.Basic

namespace Veir.Data.LLVM.Byte

open Veir.Data.LLVM.Int
attribute [local grind cases] Int

theorem toInt_fromInt {w : Nat} (x : Int w) (h : 0 < w) : (Byte.fromInt x).toInt = x := by
  simp only [Byte.toInt, fromInt, BitVec.toNat_eq];
  grind

@[veir_bv_normalize]
theorem ext_iff {w : Nat} (x y : Byte w) :
    x = y ↔ (x.val = y.val ∧ x.poison = y.poison) := by
  rw [Byte.mk.injEq]

/- # {to,from}Int -/
section ToFromInt
attribute [local grind] Byte.toInt Byte.fromInt

@[veir_bv_normalize] theorem val_fromInt (x : Int w) : (fromInt x).val = x.getValueD := by grind
@[veir_bv_normalize] theorem poison_fromInt (x : Int w) :
    (fromInt x).poison = if x.isPoison then .allOnes _ else 0 := by
  grind

@[veir_bv_normalize] theorem getValue_toInt (x : Byte w) (h : x.toInt.isPoison = false) :
    x.toInt.getValue h = x.val := by
  grind

@[veir_bv_normalize] theorem isPoison_toInt (x : Byte w) :
    x.toInt.isPoison = (x.poison != 0) := by
  grind

end ToFromInt

/- # and -/

@[veir_bv_normalize]
theorem and_eq {w : Nat} (x y : Byte w) :
    (x &&& y) =
    let poison := x.poison ||| y.poison
    ⟨(x.val &&& y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩ := by
  rfl

theorem and_comm {w : Nat} (x y : Byte w) :
    x &&& y = y &&& x := by
  simp only [and_eq, BitVec.and_comm, BitVec.or_comm]

theorem val_and {w : Nat} (x y : Byte w) :
    (x&&& y).val = (x.val &&& y.val) &&& ~~~(x.poison ||| y.poison) := by
  simp [and_eq]

/- # or -/

@[veir_bv_normalize]
theorem or_eq {w : Nat} (x y : Byte w) :
    (x ||| y) =
    let poison := x.poison ||| y.poison
    ⟨(x.val ||| y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩ := by
  rfl

theorem or_comm {w : Nat} (x y : Byte w) :
    x ||| y = y ||| x := by
  simp only [or_eq, BitVec.or_comm]

theorem val_or {w : Nat} (x y : Byte w) :
    (x ||| y).val = (x.val ||| y.val) &&& ~~~(x.poison ||| y.poison) := by
  simp [or_eq]

/- # xor -/

@[veir_bv_normalize]
theorem xor_eq {w : Nat} (x y : Byte w) :
    (x ^^^ y) =
    let poison := x.poison ||| y.poison
    ⟨(x.val ^^^ y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩ := by
  rfl

theorem xor_comm {w : Nat} (x y : Byte w) :
    x ^^^ y = y ^^^ x := by
  simp only [xor_eq, BitVec.xor_comm, BitVec.or_comm]

theorem val_xor {w : Nat} (x y : Byte w) :
    (x ^^^ y).val = (x.val ^^^ y.val) &&& ~~~(x.poison ||| y.poison) := by
  simp [xor_eq]

end Veir.Data.LLVM.Byte
