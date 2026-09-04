module

public import Veir.Data.PBV.Lemmas
public import Veir.Data.PBV.Mask

/-! # Replacing `Nat` widths and parametric-width variables.

`width_elim` names the mask of a width, and `var_elim` replaces a variable of
parametric width `w` by one of the blast width `o` that is invariant under masking.
See `Veir.Data.PBV` for the pipeline these steps belong to.
-/

namespace Veir.Data.PBV

public section

/-! ## Introducing masks -/

/-- Given some Prop `Q`, it can be generalised to hold given any `m : BitVec o`
which represents a mask of width `w`. This is to be used "backwards", to
introduce a new bitvector variable into the context of an existing goal `Q`. -/
theorem width_elim (o w : Nat) (Q : Prop)
    (h : ∀ (m : BitVec o), m = maskOfWidth o w → Q) : Q :=
  h _ rfl

/-! ## Eliminating parametric-width variables -/

/-- This theorem states that if some Prop `Q` holds for a bitvector variable `x`
of width `o` that is masked to "behave" as if it had width `w` (where `w ≤ o`)
then it also holds for a bitvector `x` of width `w`. -/
theorem var_elim {o w : Nat} (hwo : w ≤ o) (Q : BitVec w → Prop)
    (h : ∀ (x : BitVec o), x &&& maskOfWidth o w = x → Q (x.setWidth w)) :
    ∀ (x : BitVec w), Q x := by
  intro x
  have hinv : (x.setWidth o) &&& maskOfWidth o w = x.setWidth o := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_and_maskOfWidth hwo, BitVec.toNat_setWidth_of_le hwo,
      Nat.mod_eq_of_lt x.isLt]
  have hx := h (x.setWidth o) hinv
  simpa [hwo] using hx
