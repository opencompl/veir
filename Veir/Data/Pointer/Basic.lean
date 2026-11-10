module

namespace Veir.Data

public section

/--
  A pointer into interpreter memory: the object it may access and its
  address. Its offset into the object is the address less the object's base.
  A pointer without an object (`none`) may access any object that holds the bytes.
-/
structure Pointer where
  object : Option Nat
  address : UInt64
deriving Inhabited, Repr, DecidableEq, Hashable

namespace Pointer

/-- The null pointer. -/
def null : Pointer := ⟨some 0, 0⟩

/-- The pointer `i` bytes past `p`. -/
def addBytes (p : Pointer) (i : Nat) : Pointer :=
  ⟨p.object, p.address + i.toUInt64⟩

/-- The pointer at `p`'s address that has no provenance. -/
def wildcard (p : Pointer) : Pointer := ⟨none, p.address⟩

@[simp]
theorem wildcard_wildcard (p : Pointer) : p.wildcard.wildcard = p.wildcard := by
  simp [wildcard]

@[simp]
theorem wildcard_address (p : Pointer) : p.wildcard.address = p.address := by
  simp [wildcard]

@[simp]
theorem wildcard_object (p : Pointer) : p.wildcard.object = none := by
  simp [wildcard]

theorem mk_none_eq_wildcard (o : Option Nat) (a : UInt64) :
    (⟨none, a⟩ : Pointer) = (⟨o, a⟩ : Pointer).wildcard := by
  simp [wildcard]

theorem wildcard_eq_iff {p q : Pointer} :
    p.wildcard = q ↔ q.object = none ∧ q.address = p.address := by
  rcases q with ⟨o, a⟩
  simp [wildcard, eq_comm]

/-- A pointer without provenance is not null. -/
@[simp]
theorem wildcard_ne_null (p : Pointer) : p.wildcard ≠ null := by
  simp [wildcard, null]

instance : ToString Pointer where
  toString p := match p.object with
    | some object => s!"ptr({object}, {p.address})"
    | none => s!"ptr(*, {p.address})"

end Pointer

end

end Veir.Data
