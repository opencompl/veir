module

public import Veir.Analysis.DataFlow.Domains.AbstractDomain
public import Veir.Interpreter.Evaluate

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

/--
Known-bits AND soundly over-approximates every result produced by the LLVM
interpreter from concrete values represented by its abstract operands.
-/
theorem bitwiseAnd_sound
    (lhs rhs : KnownBitsLattice)
    (bitwidth : Nat)
    (lhsValue rhsValue resultValue : BitVec bitwidth)
    (hlhs : RuntimeValue.int bitwidth (.val lhsValue) ∈ γ lhs)
    (hrhs : RuntimeValue.int bitwidth (.val rhsValue) ∈ γ rhs)
    (heval :
      foldEvaluate (.llvm .and) () #[IntegerType.mk bitwidth]
          #[.int bitwidth (.val lhsValue), .int bitwidth (.val rhsValue)] =
        .ok #[.int bitwidth (.val resultValue)]) :
    RuntimeValue.int bitwidth (.val resultValue) ∈ γ (bitwiseAnd lhs rhs) := by
  have hresult : resultValue = lhsValue &&& rhsValue := by
    rw [foldEvaluate_llvm_and] at heval
    simpa using heval.symm
  subst resultValue
  cases lhs with
  | bottom => exact hlhs.elim
  | top =>
    cases rhs with
    | bottom => exact hrhs.elim
    | top => trivial
    | known rhsBits =>
      rcases hrhs with ⟨hwidth, hzero, _⟩
      subst bitwidth
      refine ⟨rfl, ?_, by simp⟩
      ext i hi
      have hzeroBit := congrArg (fun value => value[i]) hzero
      simp at hzeroBit ⊢
      intro _ hrhsValue
      exact hzeroBit hrhsValue
  | known lhsBits =>
    cases rhs with
    | bottom => exact hrhs.elim
    | top =>
      rcases hlhs with ⟨hwidth, hzero, _⟩
      subst bitwidth
      refine ⟨rfl, ?_, by simp⟩
      ext i hi
      have hzeroBit := congrArg (fun value => value[i]) hzero
      simp at hzeroBit ⊢
      intro hlhsValue _
      exact hzeroBit hlhsValue
    | known rhsBits =>
      rcases lhsBits with ⟨lhsWidth, lhsZero, lhsOne⟩
      rcases rhsBits with ⟨rhsWidth, rhsZero, rhsOne⟩
      rcases hlhs with ⟨hlwidth, hlzero, hlone⟩
      subst bitwidth
      rcases hrhs with ⟨hrwidth, hrzero, hrone⟩
      simp at hlzero hlone hrwidth
      subst rhsWidth
      simp at hrzero hrone
      simp only [bitwiseAnd, KnownBits.bitwiseAnd?, γ]
      refine ⟨rfl, ?_, ?_⟩
      · ext i hi
        have hlzeroBit := congrArg (fun value => value[i]) hlzero
        have hrzeroBit := congrArg (fun value => value[i]) hrzero
        simp at hlzeroBit hrzeroBit ⊢
        intro hlhsValue hrhsValue
        exact ⟨hlzeroBit hlhsValue, hrzeroBit hrhsValue⟩
      · ext i hi
        have hloneBit := congrArg (fun value => value[i]) hlone
        have hroneBit := congrArg (fun value => value[i]) hrone
        simp at hloneBit hroneBit ⊢
        intro lhsOne rhsOne
        exact ⟨hloneBit lhsOne, hroneBit rhsOne⟩

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
