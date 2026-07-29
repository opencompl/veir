module

public import Veir.Data.ModArith.Basic

import Veir.ForLean

public section

namespace Veir.Data.ModArith

/-!
Correctness proofs for the `mod_arith` patterns in `Canonicalize.lean`.
-/

/--
Replacing the value of `mod_arith.constant` from `value` to `value % modulus`
preserves its value in `ℤ/modulusℤ`.
-/
@[simp, grind =]
theorem canonicalizeModArithConstant_correct (value modulus : Int) :
    constant modulus (value % modulus) = constant modulus value := by
  simp [constant]

/--
For the positive moduli guaranteed by the verifier, the rewritten constant is
in the canonical interval `[0, modulus)`.
-/
theorem canonicalizeModArithConstant_in_range (value modulus : Int)
    (hmodulus : 0 < modulus) :
    0 ≤ value % modulus ∧ value % modulus < modulus := by
  exact ⟨Int.emod_nonneg value (by omega), Int.emod_lt_of_pos value hmodulus⟩

end Veir.Data.ModArith
