module

public import Veir.Data.LLVM.Byte.Basic

import all Veir.Data.LLVM.Int.Bitblast
import all Veir.Data.LLVM.Byte.Basic

namespace Veir.Data.LLVM

public section

/--
  A pointer-typed value: an address, or poison.

  We currently model a 64-bit system.
-/
inductive Ptr where
  /-- An address. -/
  | val (p : UInt64)
  /-- A poison value indicating deferred undefined behavior. -/
  | poison
deriving Inhabited, Repr, DecidableEq

namespace Ptr

def null : Ptr := .val 0

@[expose, simp, grind .]
def isRefinedBy : Ptr → Ptr → Prop
  | .poison, _ => True
  | .val p, .val p' => p = p'
  | .val _, .poison => False

@[inherit_doc] infix:50 " ⊒ " => LLVM.Ptr.isRefinedBy

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

@[simp, grind =]
def toInt (p : Ptr) : Int 64 :=
  match p with
  | .val p => .val p.toBitVec
  | .poison => .poison

@[simp, grind =]
def ofInt (i : Int 64) : Ptr :=
  match i with
  | .val v => .val (UInt64.ofBitVec v)
  | .poison => .poison

@[simp, grind =]
theorem ofInt_toInt (p : Ptr) : ofInt p.toInt = p := by
  cases p <;> simp

@[simp, grind =]
theorem toInt_ofInt (i : Int 64) : (ofInt i).toInt = i := by
  cases i <;> simp

/-- The pointer whose bits are `b`, poison if any bit is poison. -/
def ofByte (b : Byte 64) : Ptr := ofInt b.toInt

/-- The bits of a pointer: all poison for a poison pointer. -/
def toByte (p : Ptr) : Byte 64 := Byte.fromInt p.toInt

@[simp, grind =]
theorem ofByte_toByte (p : Ptr) : ofByte p.toByte = p := by
  cases p <;> simp [ofByte, toByte, Byte.toInt, Byte.fromInt, Int.isPoison, Int.getValue]

/-- Prints as `ptr(0x…)`, so a pointer is told apart from an integer in program output. -/
instance : ToString Ptr where
  toString
    | .val p =>
      let digits := String.ofList (Nat.toDigits 16 p.toNat)
      s!"ptr(0x{"".pushn '0' (16 - digits.length) ++ digits})"
    | .poison => "poison"

end Ptr

end

end Veir.Data.LLVM
