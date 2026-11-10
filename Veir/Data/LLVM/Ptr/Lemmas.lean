module

public import Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.LLVM.Ptr.Basic

namespace Veir.Data.LLVM.Ptr

public section

/- # isRefinedBy -/

@[simp, grind .]
theorem isRefinedBy_refl (p : Ptr) : p ⊒ p := by
  cases p <;> simp

@[grind .]
theorem isRefinedBy_trans {p₁ p₂ p₃ : Ptr}
    (h12 : p₁ ⊒ p₂) (h23 : p₂ ⊒ p₃) : p₁ ⊒ p₃ := by
  cases p₁ <;> cases p₂ <;> cases p₃ <;> simp_all
  rcases h12 with rfl | rfl <;> rcases h23 with rfl | rfl <;> simp

theorem isRefinedBy_antisymm {p q : Ptr} (h₁ : p ⊒ q) (h₂ : q ⊒ p) : p = q := by
  cases p <;> cases q <;> simp_all
  rename_i a b
  rcases h₁ with rfl | rfl
  · rfl
  · rcases h₂ with h | h
    · exact h
    · rw [h]; simp

/--
A common refinement of two pointers: they are the same, or they are at the same address and the
refinement is the pointer there without provenance.
-/
theorem common_refinement {a b c : Pointer} (hc : a ⊒ c) (hd : b ⊒ c) :
    (a = b ∧ a ⊒ c) ∨ (a ≠ b ∧ a.address = b.address ∧ c = a.wildcard) := by
  rw [Pointer.isRefinedBy_iff] at hc hd ⊢
  have ha : c.address = a.address := by rcases hc with rfl | rfl <;> simp
  have hb : c.address = b.address := by rcases hd with rfl | rfl <;> simp
  by_cases hab : a = b
  · exact .inl ⟨hab, hc⟩
  · refine .inr ⟨hab, ha.symm.trans hb, ?_⟩
    rcases hc with rfl | rfl
    · rcases hd with h | h
      · exact absurd h hab
      · rw [h]; simp
    · rfl

theorem val_isRefinedBy_iff {p : Pointer} {q : Ptr} :
    Ptr.val p ⊒ q ↔ q = .val p ∨ q = .val p.wildcard := by
  cases q <;> simp

end

end Veir.Data.LLVM.Ptr
