module

public import Veir.Data.PBV.Lemmas
public import Veir.Data.PBV.Mask

/-! # Steps 3 and 4: replacing `Nat` widths and parametric-width variables.

`width_elim` names the mask of a width, and `var_elim` replaces a variable of parametric width `w`
by one of the blast width `o` that is invariant under masking. See `Veir.Data.PBV` for the pipeline
these steps belong to.
-/

namespace Veir.Data.PBV

public section

/-! ## Introducing masks -/

/-- Name the mask of a width; the content is in what the tactic keeps after clearing `hm`. -/
theorem width_elim (o w : Nat) (Q : Prop)
    (h : ∀ (m : BitVec o), m = maskOfWidth o w → Q) : Q :=
  h _ rfl

/-! ## Eliminating parametric-width variables -/

/-- Every `x : BitVec w` is the truncation of a `BitVec o` invariant under masking by `w`'s mask. -/
theorem var_elim (o w : Nat) (hwo : w ≤ o) (Q : BitVec w → Prop)
    (h : ∀ (x : BitVec o), x &&& maskOfWidth o w = x → Q (x.setWidth w)) :
    ∀ (x : BitVec w), Q x := by
  intro x
  have hinv : (x.setWidth o) &&& maskOfWidth o w = x.setWidth o := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_and_maskOfWidth hwo, BitVec.toNat_setWidth_of_le hwo,
      Nat.mod_eq_of_lt x.isLt]
  have hx := h (x.setWidth o) hinv
  rwa [BitVec.setWidth_setWidth_eq_self_of_le hwo] at hx
