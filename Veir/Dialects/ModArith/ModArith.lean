import Veir.Interpreter

namespace Veir.Dialects.ModArith

/--
  Barrett reduction requires that the input value is less than `m^2` and that `m > 0`.
-/
def BarretPrecondition (m x : Nat) : Prop :=
  0 < m ∧ x < m * m

/--
  Barrett-reducing a value in [0, m^2) should yield a value in [0, 2m)
   that is either `x mod m` or `x mod m + m`.
-/
def BarrettReduceSpec (m x r : Nat) : Prop :=
    BarretPrecondition m x →
    (r = x % m ∨ r = x % m + m)

/--
  If a value is Barrett-reduced,
  the result is less than twice the modulus.
-/
theorem BarretReduceSpecImpliesLt2q (m x r : Nat) :
  (BarretPrecondition m x ∧
  BarrettReduceSpec m x r ) →
    r < 2 * m := by
    rintro ⟨hBounds, hSpec⟩
    have hOr := hSpec hBounds
    have hlt := Nat.mod_lt x hBounds.left
    grind

theorem barrettReduceStepNatCorrect (m x : Nat) :
  ∀ output, barrettReduceStepNat m x = output  →
    BarrettReduceSpec m x output := by
    intro output hOutput
    simp [BarrettReduceSpec, BarretPrecondition]
    intro h0 hmm
    unfold barrettReduceStepNat at hOutput
    sorry
