import Veir.Interpreter

namespace Veir.Dialects.ModArith

/--
  Barrett reduction requires that the input value is less than `m^2` and that `m > 0`.
-/
def BarretPrecondition (m x : Nat) : Prop :=
  0 < m ∧ x < m * m

/--
  Barrett-reducing a value in [0, q^2) should yield a value in [0, 2q)
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

/--
  The Barret Reduction Step algorithm satisfies the specification.
-/
theorem barrettReduceStepNatCorrect (m x : Nat) :
  ∀ output, barrettReduceStepNat? x m = some output  →
    BarrettReduceSpec m x output := by
    rintro output hStep
    unfold BarrettReduceSpec
    intro hPre
    unfold BarretPrecondition at hPre
    simp [barrettReduceStepNat?] at hStep
    rcases hPre with ⟨hmPos, hRange⟩
    rcases hStep with ⟨hmGt1, hBitNe0, hOut⟩
    let l := Veir.natBitLength (m - 1)
    let s := 2 * l
    let basePow := (2 : Nat) ^ s
    let ratioNat := basePow / m
    let qHat := (x * ratioNat) / basePow
    by_cases hExactMod : qHat = x / m
    ·

      subst output




    sorry
