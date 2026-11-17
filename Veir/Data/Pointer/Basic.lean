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

/-- Adding `a` and then `b` bytes adds `a + b` bytes, as the address wraps around. -/
theorem addBytes_addBytes (p : Pointer) (a b : BitVec 64) :
    (p.addBytes a.toNat).addBytes b.toNat = p.addBytes (a + b).toNat := by
  simp only [addBytes, Pointer.mk.injEq, ← UInt64.toNat_inj, UInt64.toNat_add, Nat.toUInt64_eq,
    UInt64.toNat_ofNat', BitVec.toNat_add]
  omega

/-- `p'` refines `p` if it is `p`. -/
def isRefinedBy (p p' : Pointer) : Prop := p' = p

@[inherit_doc] infix:50 " ⊒ " => Pointer.isRefinedBy

@[simp, grind =]
theorem isRefinedBy_iff {p p' : Pointer} : p ⊒ p' ↔ p' = p := Iff.rfl

/-- A refinement of a pointer has the same address as the pointer. -/
theorem isRefinedBy.address_eq {p p' : Pointer} (h : p ⊒ p') : p'.address = p.address := by
  rw [h]

instance : ToString Pointer where
  toString p := s!"ptr({p.address})"

end Pointer

end

end Veir.Data
