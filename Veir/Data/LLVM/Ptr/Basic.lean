module

namespace Veir.Data.LLVM

public section

/--
  A pointer into interpreter memory: the object it may access and a byte
  offset into it. Pointers derived from different objects never alias, and an
  access outside the object is undefined behaviour. Every object has a
  physical address, so a pointer converts to an integer with
  `MemoryState.address` and an integer converts back with `MemoryState.decode`.
-/
structure Pointer where
  object : Nat
  offset : UInt64
deriving Inhabited, Repr, DecidableEq, Hashable

namespace Pointer

/-- The null pointer. Object 0 holds no bytes, so every access through it is UB. -/
def null : Pointer := ⟨0, 0⟩

def isNull (p : Pointer) : Bool := p == null

instance : ToString Pointer where
  toString p := s!"ptr({p.object}, {p.offset})"

end Pointer

/--
  A pointer-typed value: a pointer, or poison.
-/
inductive Ptr where
  /-- A pointer to an object. -/
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

end Ptr

end

end Veir.Data.LLVM
