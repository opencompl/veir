module

namespace Veir.Data

public section

/--
  A pointer into interpreter memory: the object it may access and its
  address, which are its bits. Its offset into the object is the address less
  the object's base.

  A pointer may also be *wild*: it carries an address and no object. Its
  `object` is ignored, and an access through it finds the object the address
  lies in at that moment. A pointer cast from an integer is wild, since the
  integer carries no object.
-/
structure Pointer where
  object : Nat
  address : UInt64
  wild : Bool
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

/-- The pointer `i` bytes past `p`. -/
def addBytes (p : Pointer) (i : Nat) : Pointer :=
  { p with address := p.address + i.toUInt64 }

instance : ToString Pointer where
  toString p := if p.wild then s!"ptr({p.address})" else s!"ptr({p.object}, {p.address})"

end Pointer

end

end Veir.Data
