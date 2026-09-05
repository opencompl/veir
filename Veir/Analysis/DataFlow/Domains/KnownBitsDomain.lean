module

public import Veir.Analysis.DataFlow.Domains.AbstractDomain
public import Veir.RuntimeValue
import Veir.Meta.BVDecide

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

/-- The concrete runtime values represented by a known-bits lattice element. -/
@[expose] def γ : KnownBitsLattice → Set RuntimeValue
  | .bottom => ⊥
  | .top => ⊤
  | .known bits => fun concrete =>
      match concrete with
      | .int bitwidth (.val value) =>
        ∃ h : bitwidth = bits.bitwidth,
          let value := value.cast h
          value &&& bits.zero = 0 ∧ value &&& bits.one = bits.one
      | _ => False

@[simp] theorem not_mem_γ_bottom (value : RuntimeValue) : value ∉ γ .bottom := fun h => h.elim

@[simp] theorem mem_γ_top (value : RuntimeValue) : value ∈ γ .top := trivial

/-- Normalize membership in a known-bits value to masks at the concrete value's width. -/
theorem mem_γ_known_masks_iff
    {bits : KnownBits}
    {bitwidth : Nat}
    {value : BitVec bitwidth} :
    RuntimeValue.int bitwidth (.val value) ∈ γ (.known bits) ↔
      ∃ zero one : BitVec bitwidth,
        bits = ⟨bitwidth, zero, one⟩ ∧
        value &&& zero = 0 ∧ value &&& one = one := by
  constructor
  · rcases bits with ⟨bitsWidth, zero, one⟩
    rintro ⟨hwidth, hzero, hone⟩
    change bitwidth = bitsWidth at hwidth
    subst bitsWidth
    simp at hzero hone
    exact ⟨zero, one, rfl, hzero, hone⟩
  · rintro ⟨zero, one, rfl, hzero, hone⟩
    exact ⟨rfl, hzero, hone⟩

/-- Characterize known-bits membership as facts about each concrete bit. -/
theorem mem_γ_known_iff
    {bits : KnownBits}
    {bitwidth : Nat}
    {value : BitVec bitwidth} :
    RuntimeValue.int bitwidth (.val value) ∈ γ (.known bits) ↔
      ∃ zero one : BitVec bitwidth,
        bits = ⟨bitwidth, zero, one⟩ ∧
        (∀ i (hi : i < bitwidth), zero[i] = true → value[i] = false) ∧
        (∀ i (hi : i < bitwidth), one[i] = true → value[i] = true) := by
  rw [mem_γ_known_masks_iff]
  constructor
  · rintro ⟨zero, one, hbits, hzero, hone⟩
    refine ⟨zero, one, hbits, ?_, ?_⟩
    · intro i hi hzeroTrue
      have hzeroBit := congrArg (fun value => value[i]) hzero
      simp at hzeroBit
      veir_bv_decide
    · intro i hi honeTrue
      have honeBit := congrArg (fun value => value[i]) hone
      simp at honeBit
      veir_bv_decide
  · rintro ⟨zero, one, hbits, hzero, hone⟩
    refine ⟨zero, one, hbits, ?_, ?_⟩
    · ext i hi
      have hzeroBit := hzero i hi
      simp at hzeroBit ⊢
      veir_bv_decide
    · ext i hi
      have honeBit := hone i hi
      simp at honeBit ⊢
      veir_bv_decide

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

end KnownBitsLattice

end Veir
