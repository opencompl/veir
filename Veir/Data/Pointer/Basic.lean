module

namespace Veir.Data

public section

/--
  A pointer into interpreter memory: the object it may access and a byte
  offset into it. The flat memory model has a single object, 0, whose
  offsets are the addresses themselves.
-/
structure Pointer where
  object : Nat
  offset : UInt64
deriving Inhabited, Repr, DecidableEq, Hashable

namespace Pointer

/-- The null pointer. -/
def null : Pointer := ⟨0, 0⟩

def isNull (p : Pointer) : Bool := p == null

instance : ToString Pointer where
  toString p := s!"ptr({p.object}, {p.offset})"

end Pointer

end

end Veir.Data
