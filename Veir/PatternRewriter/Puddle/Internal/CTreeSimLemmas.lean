module

public import CTree.Sim

public section

namespace CTree
open Coinductive Lean.Order Tower

variable {EIn FIn CIn C'In DIn X Y X' Y' : Type u}
  {E : EIn → Type u} {F : FIn → Type u} {C : CIn → Type u} {C' : C'In → Type u} {D : DIn → Type u}
  {R R' : Type u} (RR : R → R' → Prop)

namespace Sim

variable [UB : HasUB EIn] [HasUB FIn]

/-- A simulation remains valid when its relation on return values is weakened. -/
theorem mono {RR RS : R → R' → Prop} {t : CTree E C R} {u : CTree E C' R'}
    (h : Sim RR t u) (hrel : ∀ x y, RR x y → RS x y) : Sim RS t u := by
  have hbind := bind t u CTree.ret CTree.ret h
    (fun x y hxy => (ret RS x y).mpr (hrel x y hxy))
  change Sim RS (t >>= Pure.pure) (u >>= Pure.pure) at hbind
  simpa only [_root_.bind_pure] using hbind

/-- Compose simulations when the two return relations imply the desired relation. -/
theorem trans {R₁ R₂ R₃ : Type u} {RS : R₁ → R₂ → Prop} {RT : R₂ → R₃ → Prop}
    {RU : R₁ → R₃ → Prop} {t : CTree E C R₁} {u : CTree E C' R₂} {v : CTree E D R₃}
    (htu : Sim RS t u) (huv : Sim RT u v)
    (hrel : ∀ x y z, RS x y → RT y z → RU x z) : Sim RU t v := by
  apply (trans_rel htu huv).mono
  rintro x z ⟨y, hxy, hyz⟩
  exact hrel x y z hxy hyz

end Sim

end CTree
