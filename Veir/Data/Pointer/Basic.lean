module

namespace Veir.Data

public section

/--
  A pointer into interpreter memory: the object it may access and a byte
  offset into it.

  A pointer may also be *wild*: it carries an address and no object. Its
  `offset` is that address and its `object` is 0, the null object at address
  0, so its address is still `offset`; an access through it finds the object
  the address lies in at that moment. A pointer cast from an integer is wild,
  since the integer carries no object.
-/
structure Pointer where
  object : Nat
  offset : UInt64
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

instance : ToString Pointer where
  toString p := if p.wild then s!"ptr({p.offset})" else s!"ptr({p.object}, {p.offset})"

end Pointer

end

end Veir.Data
