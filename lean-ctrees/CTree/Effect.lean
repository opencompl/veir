-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

module

/-!
# Effects

Vendored (and adapted) from the `ITree` library for `EffectSSA`
(https://github.com/ISTA-PLV/coinductive, `ITree/Effect.lean`,
upstream rev `d1aeffe87ec7bd4bd13ed92fdc00ef6c5d58f800`).

Unlike upstream, we do *not* bundle the index type `ι` together with the family
`ε : ι → Type u` — the index type is inferred from the family instead, so no
`Effect` typeclass is required.
-/

@[expose] public section

namespace CTree

/--
Sum of two effect families: on the sum of the index types, dispatches to the
corresponding component family.
-/
@[implicit_reducible]
def SumE {ι₁ ι₂ : Type u} (ε₁ : ι₁ → Type u) (ε₂ : ι₂ → Type u) : (ι₁ ⊕ ι₂) → Type u
  | .inl i => ε₁ i
  | .inr i => ε₂ i

@[inherit_doc] infixr:30 " ⊕ₑ " => SumE

@[simp, grind =] theorem SumE.eq_inl {ι₁ ι₂}
    {ε₁ : ι₁ → Type u} {ε₂ : ι₂ → Type u} (i : ι₁) :
    (ε₁ ⊕ₑ ε₂) (.inl i) = ε₁ i := rfl
@[simp, grind =] theorem SumE.eq_inr {ι₁ ι₂}
    {ε₁ : ι₁ → Type u} {ε₂ : ι₂ → Type u} (i : ι₂) :
    (ε₁ ⊕ₑ ε₂) (.inr i) = ε₂ i := rfl

class Subeffect {ι₁ ι₂} (ε₁ : ι₁ → Type u) (ε₂ : ι₂ → Type v) where
  map : (i₁ : ι₁) → ((i₂ : ι₂) × (ε₂ i₂ → ε₁ i₁))
  map_surj : ∀ i₁, Function.Surjective (map i₁).snd := by
    grind [Function.Surjective]

infix:20 " -< " => Subeffect
attribute [grind! .] Subeffect.map_surj

/-! ## Subeffect Definitions -/
namespace Subeffect

/-- `mapEff` is an abbreviation of the first component of `map`. -/
@[simp, grind]
abbrev mapEff {ι₁ ι₂} (ε₁ : ι₁ → Type u) (ε₂ : ι₂ → Type v)
    [s : ε₁ -< ε₂] (i₁ : ι₁) : ι₂ :=
  (s.map i₁).1

/-- `mapCont` is an abbreviation of the second component of `map`. -/
@[simp, grind]
abbrev mapCont {ι₁ ι₂} (ε₁ : ι₁ → Type u) (ε₂ : ι₂ → Type v) [s : ε₁ -< ε₂]
    (i₁ : ι₁) : ε₂ (s.mapEff _ _ i₁) → ε₁ i₁ :=
  (s.map i₁).2

/-! ## Instances -/

/-! ### Identity / Reflexivity -/
section Refl
variable {ι : Type u} {ε : ι → Type u}

/-- Every effect is a sub-effect of itself. -/
instance : ε -< ε where
  map i := ⟨i, λ x => x⟩

@[simp, grind =] theorem map_eq_self (i : ι) :
    (map (ε₁ := ε) (ε₂ := ε) i) = ⟨i, id⟩ := rfl
@[simp, grind =] theorem mapEff_eq_self (i : ι) :
    (mapEff ε ε i) = i := rfl

end Refl

/-! ### Sum Effects -/
section Sum
variable {ι ι' ι₁ ι₂ : Type u}
         {ε : ι → Type u} {ε' : ι' → Type u}
         {ε₁ : ι₁ → Type u} {ε₂ : ι₂ → Type u}

/-!
If both `ε₁` and `ε₂` are sub-effects of `ε'`,
then `ε₁ ⊕ₑ ε₂` is a sub-effect of `ε'`,
via a straightforward case-analysis.
-/
instance [subl : ε₁ -< ε'] [subr : ε₂ -< ε'] : (ε₁ ⊕ₑ ε₂) -< ε' where
  map
  | .inl x => subl.map x
  | .inr x => subr.map x
  map_surj i₁ := by cases i₁ <;> apply Subeffect.map_surj

@[simp] theorem map_inl [ε₁ -< ε'] [ε₂ -< ε'] {e : ι₁} :
    (map (ε₁ := ε₁ ⊕ₑ ε₂) (ε₂:=ε') <| .inl e) = map e := rfl
@[simp] theorem mapEff_inl [ε₁ -< ε'] [ε₂ -< ε'] {e : ι₁} :
    (mapEff (ε₁ ⊕ₑ ε₂) ε' <| .inl e) = mapEff ε₁ ε' e := rfl
@[simp] theorem map_inr [ε₁ -< ε'] [ε₂ -< ε'] {e : ι₂} :
    (map (ε₁ := ε₁ ⊕ₑ ε₂) (ε₂:=ε') <| .inr e) = map e := rfl
@[simp] theorem mapEff_inr [ε₁ -< ε'] [ε₂ -< ε'] {e : ι₂} :
    (mapEff (ε₁ ⊕ₑ ε₂) ε' <| .inr e) = mapEff ε₂ ε' e := rfl

/-- `ε₁` is a sub-effect of `ε₁ ⊕ₑ ε₂`. -/
instance (priority := mid) instSubSumL [sub : ε₁ -< ε₂] : ε₁ -< (ε₂ ⊕ₑ ε') where
  map t := let ⟨i, f⟩ := (sub.map t); ⟨.inl i, f⟩

/-- The `ε' -< (ε₁ ⊕ₑ ε₂)` instance derived from `ε' -< ε₁` maps to `Sum.inl`. -/
@[simp] theorem map_eq_inl [ε' -< ε₁] (e : ι') :
    map (ε₁ := ε') (ε₂ := ε₁ ⊕ₑ ε₂) e = ⟨.inl (map e).fst, (map e).snd⟩ := rfl
@[simp] theorem mapEff_eq_inl [ε' -< ε₁] (e : ι') :
    mapEff ε' (ε₁ ⊕ₑ ε₂) e = .inl (mapEff ε' ε₁ e) := rfl

/-- `ε₂` is a sub-effect of `ε₁ ⊕ₑ ε₂`. -/
instance (priority := low) instSubSumR {ι₁ ι₂ ι'}
    {ε₁ : ι₁ → Type u} {ε₂ : ι₂ → Type u} {ε' : ι' → Type u}
    [sub : ε₁ -< ε₂] : ε₁ -< ε' ⊕ₑ ε₂ where
  map t := let ⟨i, f⟩ := (sub.map t); ⟨.inr i, f⟩
  map_surj := sub.map_surj

/-- The `ε' -< (ε₁ ⊕ₑ ε₂)` instance derived from `ε' -< ε₂` maps to `Sum.inr`. -/
@[simp] theorem map_eq_inr [ε' -< ε₂] (e : ι') :
    map (ε₁ := ε') (ε₂ := ε₁ ⊕ₑ ε₂) e = ⟨.inr (map e).fst, (map e).snd⟩ := rfl
@[simp] theorem mapEff_eq_inr [ε' -< ε₂] (e : ι') :
    mapEff ε' (ε₁ ⊕ₑ ε₂) e = .inr (mapEff ε' ε₂ e) := rfl

end Sum

end Subeffect

end CTree
