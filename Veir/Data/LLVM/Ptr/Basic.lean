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
  | .val p, .val p' => p ⊒ p'
  | .val _, .poison => False

@[inherit_doc] infix:50 " ⊒ " => LLVM.Ptr.isRefinedBy

/--
The greatest lower bound of two pointer values under refinement: the least defined value both
refine to, or `none` if no value refines both (both are defined and differ).
-/
def glb? : Ptr → Ptr → Option Ptr
  | .poison, q => some q
  | p, .poison => some p
  | .val a, .val b => if a = b then some (.val a) else none

instance : ToString Ptr where
  toString
    | .val p => ToString.toString p
    | .poison => "poison"

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
