module

namespace Veir.Data

public section

/--
  A pointer into interpreter memory: the object it may access and a byte
  offset into it.

  A pointer may also be *wild*: its object is unknown and `offset` is a raw
  address. A wild pointer names the null object, whose address is 0, so its
  address is `offset`, and an access through it finds the object that address
  lies in at the time of the access. Casting an integer to a pointer gives a
  wild pointer, since the integer carries no object.
-/
structure Pointer where
  object : Nat
  offset : UInt64
  wild : Bool := false
deriving Inhabited, Repr, DecidableEq, Hashable

namespace Pointer

/-- The null pointer. -/
def null : Pointer := ⟨0, 0, false⟩

/-- The wild pointer with the address `addr`. -/
def ofAddress (addr : UInt64) : Pointer := ⟨0, addr, true⟩

/-
TODO: we should eventually add an interface that lets us check if the
address of any pointer happens to be null: addr(p) == 0.
-/

instance : ToString Pointer where
  toString p := if p.wild then s!"ptr({p.offset})" else s!"ptr({p.object}, {p.offset})"

end Pointer

end

end Veir.Data
