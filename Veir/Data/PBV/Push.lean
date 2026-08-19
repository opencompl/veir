module

public import Veir.Data.PBV.Lemmas
public import Veir.Data.PBV.Mask

/-! # Rewriting a parametric expression into a concrete, single-width one.

`eq_iff` introduces a `setWidth o` at the root of the goal, and the remaining
lemmas push it down towards the leaves, masking the result of every
width-sensitive operation. See `Veir.Data.PBV` for more details.
-/

namespace Veir.Data.PBV

public section

/-! ## Introducing `setWidth o` at the root -/

theorem eq_iff {w o : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w), (a = b) = (a.setWidth o = b.setWidth o) := by
  intro a b
  apply propext
  exact ⟨fun hab => hab ▸ rfl, fun hab => BitVec.setWidth_inj h hab⟩

/-! ## Pushing `setWidth o` towards the leaves — leaves and width changes -/

theorem setWidth_setWidth {w o : Nat} (h : w ≤ o) :
    ∀ {u : Nat} (a : BitVec u),
      (a.setWidth w).setWidth o = a.setWidth o &&& maskOfWidth o w := by
  intro u a
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_mod_pow_of_le h]

/-! ## Width-sensitive arithmetic: mask the result -/

theorem setWidth_add {w o : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w),
      (a + b).setWidth o = (a.setWidth o + b.setWidth o) &&& maskOfWidth o w := by
  intro a b
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_add, BitVec.toNat_setWidth_of_le h, BitVec.toNat_setWidth_of_le h,
    Nat.mod_mod_pow_of_le h, BitVec.toNat_add]
