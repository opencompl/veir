module

/-
  # Source locations in the parser.

  A `Location` is a typed wrapper around a byte offset into the parser input.
  Using a dedicated type instead of `Nat` prevents accidentally mixing
  positions with sizes, counts, indices, or other numeric quantities.
-/

namespace Veir.Parser

public section

/-- A location into the parser input. -/
structure Location where
  /-- The byte offset in the parser input. -/
  byteOffset : Nat
deriving Inhabited, DecidableEq, Repr

namespace Location

instance : LT Location := ⟨fun a b => a.byteOffset < b.byteOffset⟩
instance : LE Location := ⟨fun a b => a.byteOffset ≤ b.byteOffset⟩

/-- Advance a location forward by `n` bytes. -/
@[grind, expose]
def advance (loc : Location) (n : Nat) : Location :=
  { byteOffset := loc.byteOffset + n }

/-- `loc + n` advances `loc` forward by `n` bytes. -/
instance : HAdd Location Nat Location := ⟨Location.advance⟩

@[grind =]
theorem HAdd_eq_advance (loc : Location) (n : Nat) : loc + n = Location.advance loc n := rfl

end Location

end -- public section

end Veir.Parser
