module

public import Veir.Data.Pointer.Basic
public import Veir.Data.LLVM.Byte.Basic

namespace Veir.Data.LLVM

public section

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

instance : ToString Ptr where
  toString
    | .val p => ToString.toString p
    | .poison => "poison"

/--
  The wild pointer at an address: the integer says nothing about the object,
  so the access through the pointer finds it.
-/
def ofInt : Int 64 → Ptr
  | .val v => .val (Pointer.ofAddress (UInt64.ofBitVec v))
  | .poison => .poison

/-- The pointer whose bits are `b`. -/
def ofByte (b : Byte 64) : Ptr :=
  if b.poison = 0 then .val (Pointer.ofAddress b.toUInt64) else .poison

/-- The address of a pointer as a 64-bit integer. -/
def toInt : Ptr → Int 64
  | .val p => .val p.address.toBitVec
  | .poison => .poison

/-- The bits of a pointer, its address. -/
def toByte : Ptr → Byte 64
  | .val p => Byte.fromUInt64 p.address
  | .poison => Byte.allPoison

end Ptr

end

end Veir.Data.LLVM
