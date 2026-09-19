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

/-- The address as a 64-bit integer, the offset in the flat model; poison for a poison pointer. -/
@[simp, grind =]
def toInt (p : Ptr) : Int 64 :=
  match p with
  | .val p => .val p.offset.toBitVec
  | .poison => .poison

/-- The pointer at address `i`, an offset into object 0 in the flat model; poison for poison. -/
@[simp, grind =]
def ofInt (i : Int 64) : Ptr :=
  match i with
  | .val v => .val ⟨0, UInt64.ofBitVec v⟩
  | .poison => .poison

/-- The pointer whose bits are `b`, poison if any bit is poison. -/
def ofByte (b : Byte 64) : Ptr := ofInt b.toInt

/-- The bits of a pointer: all poison for a poison pointer. -/
def toByte (p : Ptr) : Byte 64 := Byte.fromInt p.toInt

instance : ToString Ptr where
  toString
    | .val p => ToString.toString p
    | .poison => "poison"

end Ptr

end

end Veir.Data.LLVM
