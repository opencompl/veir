module

public import Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.LLVM.Int.Bitblast
import all Veir.Data.LLVM.Byte.Basic

namespace Veir.Data.LLVM.Ptr

public section

/- # isRefinedBy -/

@[simp, grind .]
theorem isRefinedBy_refl (p : Ptr) : p ⊒ p := by
  cases p <;> simp

@[grind .]
theorem isRefinedBy_trans {p₁ p₂ p₃ : Ptr}
    (h12 : p₁ ⊒ p₂) (h23 : p₂ ⊒ p₃) : p₁ ⊒ p₃ := by
  cases p₁ <;> cases p₂ <;> cases p₃ <;> simp_all

/-- Only the same pointer refines a pointer that is not poison. -/
@[grind .]
theorem eq_of_val_isRefinedBy {p : UInt64} {q : Ptr}
    (h : Ptr.val p ⊒ q) : q = .val p := by
  cases q <;> simp_all

/- # {to,of}Int -/

@[simp, grind =]
theorem ofInt_toInt (p : Ptr) : ofInt p.toInt = p := by
  cases p <;> simp

@[simp, grind =]
theorem toInt_ofInt (i : Int 64) : (ofInt i).toInt = i := by
  cases i <;> simp

/- # {to,of}Byte -/

@[simp, grind =]
theorem ofByte_toByte (p : Ptr) : ofByte p.toByte = p := by
  cases p <;> simp [ofByte, toByte, Byte.toInt, Byte.fromInt, Int.isPoison, Int.getValue]

end

end Veir.Data.LLVM.Ptr
