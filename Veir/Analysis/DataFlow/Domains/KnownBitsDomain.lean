module

public import Veir.Analysis.DataFlow.Domains.AbstractDomain

public section

namespace Veir

/-!
# Known-bits domain

This file defines the abstract value used by known-bits analysis. As in LLVM, a
known-bits value stores two masks: `zero` marks bits known to be zero and `one`
marks bits known to be one. Bits absent from both masks are unknown.
-/

/-- Two masks describing the known zero and known one bits of a fixed-width integer. -/
structure KnownBits where
  bitwidth : Nat
  zero : BitVec bitwidth
  one : BitVec bitwidth
deriving DecidableEq, Repr

namespace KnownBits

/-- No bits are known for an integer of the given width. -/
def unknown (bitwidth : Nat) : KnownBits :=
  { bitwidth, zero := 0, one := 0 }

/-- Every bit of a concrete integer is known. -/
def constant (bitwidth : Nat) (value : Int) : KnownBits :=
  let bits := BitVec.ofInt bitwidth value
  { bitwidth, zero := ~~~bits, one := bits }

/-- The zero and one masks do not make contradictory claims. -/
def isValid (bits : KnownBits) : Bool :=
  bits.zero &&& bits.one == 0

/-- Keep only facts known on both incoming control-flow paths. -/
def join? (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsZero := h ▸ rhs.zero
    let rhsOne := h ▸ rhs.one
    some
      { bitwidth := lhs.bitwidth
        zero := lhs.zero &&& rhsZero
        one := lhs.one &&& rhsOne }
  else
    none

/-- Known bits produced by bitwise AND. -/
def bitwiseAnd? (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsZero := h ▸ rhs.zero
    let rhsOne := h ▸ rhs.one
    some
      { bitwidth := lhs.bitwidth
        zero := lhs.zero ||| rhsZero
        one := lhs.one &&& rhsOne }
  else
    none

/-- Known bits produced by bitwise OR. -/
def bitwiseOr? (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsZero := h ▸ rhs.zero
    let rhsOne := h ▸ rhs.one
    some
      { bitwidth := lhs.bitwidth
        zero := lhs.zero &&& rhsZero
        one := lhs.one ||| rhsOne }
  else
    none

/-- Known bits produced by bitwise XOR. -/
def bitwiseXor? (lhs rhs : KnownBits) : Option KnownBits :=
  if h : lhs.bitwidth = rhs.bitwidth then
    let rhsZero := h ▸ rhs.zero
    let rhsOne := h ▸ rhs.one
    some
      { bitwidth := lhs.bitwidth
        zero := (lhs.zero &&& rhsZero) ||| (lhs.one &&& rhsOne)
        one := (lhs.zero &&& rhsOne) ||| (lhs.one &&& rhsZero) }
  else
    none

end KnownBits

/--
Sparse lattice for known bits. `bottom` is an uninitialized sparse value, `known`
contains width-aware masks, and `top` is used when even the integer width is unavailable.
-/
inductive KnownBitsLattice where
  | bottom
  | known (bits : KnownBits)
  | top
deriving DecidableEq, Repr

namespace KnownBitsLattice

instance : Bot KnownBitsLattice where
  bot := .bottom

instance : Top KnownBitsLattice where
  top := .top

/-- No bit facts are known, but the integer width is known. -/
def unknown (bitwidth : Nat) : KnownBitsLattice :=
  .known (KnownBits.unknown bitwidth)

/-- An exact fixed-width integer value. -/
def constant (bitwidth : Nat) (value : Int) : KnownBitsLattice :=
  .known (KnownBits.constant bitwidth value)

/-- Join facts arriving along different control-flow paths. -/
def join : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice
  | .bottom, rhs => rhs
  | lhs, .bottom => lhs
  | .top, _ => .top
  | _, .top => .top
  | .known lhs, .known rhs =>
      match lhs.join? rhs with
      | some bits => .known bits
      | none => .top

instance : Join KnownBitsLattice where
  join := join

/-- Transfer known bits through bitwise AND. -/
def bitwiseAnd : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice
  | .bottom, _ | _, .bottom => .bottom
  | .top, .top => .top
  | .known lhs, .top | .top, .known lhs =>
      .known { lhs with one := 0 }
  | .known lhs, .known rhs =>
      match lhs.bitwiseAnd? rhs with
      | some bits => .known bits
      | none => .top

/-- Transfer known bits through bitwise OR. -/
def bitwiseOr : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice
  | .bottom, _ | _, .bottom => .bottom
  | .top, .top => .top
  | .known lhs, .top | .top, .known lhs =>
      .known { lhs with zero := 0 }
  | .known lhs, .known rhs =>
      match lhs.bitwiseOr? rhs with
      | some bits => .known bits
      | none => .top

/-- Transfer known bits through bitwise XOR. -/
def bitwiseXor : KnownBitsLattice → KnownBitsLattice → KnownBitsLattice
  | .bottom, _ | _, .bottom => .bottom
  | .top, .top => .top
  | .known lhs, .top | .top, .known lhs => .unknown lhs.bitwidth
  | .known lhs, .known rhs =>
      match lhs.bitwiseXor? rhs with
      | some bits => .known bits
      | none => .top

end KnownBitsLattice

end Veir
