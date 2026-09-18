module

public import Veir.Data.LLVM.Byte.Basic

namespace Veir.Data.LLVM

public section

/--
  A pointer into interpreter memory. In the flat memory model this is the
  address itself.

  We currently model a 64-bit system.
-/
abbrev Pointer := UInt64

namespace Pointer

/-- The null pointer. -/
def null : Pointer := 0

end Pointer

/--
  A pointer-typed value: a pointer, or poison.
-/
inductive Ptr where
  /-- A pointer. -/
  | val (p : Pointer)
  /-- A poison value indicating deferred undefined behavior. -/
  | poison
deriving Inhabited, Repr, DecidableEq

namespace Ptr

def null : Ptr := .val Pointer.null

@[expose, simp, grind .]
def isRefinedBy : Ptr → Ptr → Prop
  | .poison, _ => True
  | .val p, .val p' => p = p'
  | .val _, .poison => False

@[inherit_doc] infix:50 " ⊒ " => LLVM.Ptr.isRefinedBy

/-- The address as a 64-bit integer; poison for a poison pointer. -/
@[simp, grind =]
def toInt (p : Ptr) : Int 64 :=
  match p with
  | .val p => .val p.toBitVec
  | .poison => .poison

/-- The pointer at address `i`; poison for poison. -/
@[simp, grind =]
def ofInt (i : Int 64) : Ptr :=
  match i with
  | .val v => .val (UInt64.ofBitVec v)
  | .poison => .poison

/-- The pointer whose bits are `b`, poison if any bit is poison. -/
def ofByte (b : Byte 64) : Ptr := ofInt b.toInt

/-- The bits of a pointer: all poison for a poison pointer. -/
def toByte (p : Ptr) : Byte 64 := Byte.fromInt p.toInt

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
