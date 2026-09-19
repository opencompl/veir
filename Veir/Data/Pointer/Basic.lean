module

namespace Veir.Data

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

end

end Veir.Data
