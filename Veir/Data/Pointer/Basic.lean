module

namespace Veir.Data

public section

/--
  A pointer into interpreter memory: the object it may access and its
  address. Its offset into the object is the address less the object's base.
-/
structure Pointer where
  object : Nat
  address : UInt64
deriving Inhabited, Repr, DecidableEq, Hashable

namespace Pointer

/-- The null pointer. -/
def null : Pointer := ⟨0, 0⟩

/-- The pointer `i` bytes past `p`. -/
def addBytes (p : Pointer) (i : Nat) : Pointer :=
  ⟨p.object, p.address + i.toUInt64⟩

instance : ToString Pointer where
  toString p := s!"ptr({p.object}, {p.address})"

end Pointer

end

end Veir.Data
