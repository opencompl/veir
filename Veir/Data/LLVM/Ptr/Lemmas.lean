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

theorem isRefinedBy_antisymm {p q : Ptr} (h₁ : p ⊒ q) (h₂ : q ⊒ p) : p = q := by
  cases p <;> cases q <;> simp_all

/-- A common refinement of two pointers: they are the same, and it is that pointer. -/
theorem common_refinement {a b c : Pointer} (hc : a ⊒ c) (hd : b ⊒ c) : a = b ∧ a ⊒ c :=
  ⟨(Pointer.isRefinedBy_iff.mp hc).symm.trans (Pointer.isRefinedBy_iff.mp hd), hc⟩

theorem val_isRefinedBy_iff {p : Pointer} {q : Ptr} : Ptr.val p ⊒ q ↔ q = .val p := by
  cases q <;> simp

/- # glb? -/

/-- `glb?` is a lower bound: what it returns refines both pointer values. -/
theorem glb?_isRefinedBy {p q m : Ptr} (h : p.glb? q = some m) : p ⊒ m ∧ q ⊒ m := by
  grind [glb?, cases Ptr]

/--
`glb?` is the greatest lower bound: every pointer value that refines both refines what `glb?`
returns.
-/
theorem glb?_greatest {p q e : Ptr} (hp : p ⊒ e) (hq : q ⊒ e) :
    ∃ m, p.glb? q = some m ∧ m ⊒ e := by
  grind [glb?, cases Ptr]

end

end Veir.Data.LLVM.Ptr
