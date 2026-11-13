module

namespace Veir.Data

public section

/--
  A pointer into interpreter memory: its address. We do not model provenance, so a pointer may
  access any object that holds the bytes.
-/
structure Pointer where
  address : UInt64
deriving Inhabited, Repr, DecidableEq, Hashable

namespace Pointer

/-- The null pointer. -/
def null : Pointer := ⟨0⟩

/-- The pointer `i` bytes past `p`. -/
def addBytes (p : Pointer) (i : Nat) : Pointer :=
  ⟨p.address + i.toUInt64⟩

/-- `p'` refines `p` if it is `p`. -/
def isRefinedBy (p p' : Pointer) : Prop := p' = p

@[inherit_doc] infix:50 " ⊒ " => Pointer.isRefinedBy

@[simp, grind =]
theorem isRefinedBy_iff {p p' : Pointer} : p ⊒ p' ↔ p' = p := Iff.rfl

instance : ToString Pointer where
  toString p := s!"ptr({p.address})"

end Pointer

end

end Veir.Data
