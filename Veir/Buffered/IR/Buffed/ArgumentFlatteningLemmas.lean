module

public import Init.Internal.Order.Basic
import all Init.Internal.Order.Basic

/-! Checked least-fixed-point fusion for argument reindexing and raw-result
projection. Optional result projection preserves bottom and admissibility, including
for logically nonterminating source functions. -/

public section
namespace Veir.Buffered.Buffed
open Lean.Order Lean.Order.PartialOrder
open scoped Lean.Order

theorem admissible_upper {α : Sort u} [CCPO α] (b : α) :
    admissible (fun a => a ⊑ b) := by
  intro c hc h
  exact csup_le hc h

theorem admissible_option_project {α : Type u} {β : Type v}
    (project : Option α → Option β) (h : project none = none) (bound : Option β) :
    admissible (fun value => project value ⊑ bound) := by
  apply admissible_flatOrder
  change project none ⊑ bound
  rw [h]
  exact FlatOrder.rel.bot

theorem admissible_eval {α : Sort u} {β : α → Sort v} [∀ x, CCPO (β x)]
    (x : α) (P : β x → Prop) (hP : admissible P) :
    admissible (fun f : ∀ x, β x => P (f x)) := by
  intro c hc h
  rw [← fun_csup_eq]
  apply hP _ (chain_apply hc x)
  rintro _ ⟨f, hf, rfl⟩
  exact h f hf

theorem fix_le {α : Sort u} [CCPO α] {F : α → α} (hF : monotone F)
    (b : α) (hb : F b ⊑ b) : fix F hF ⊑ b := by
  apply fix_induct hF (fun a => a ⊑ b) (admissible_upper b)
  intro a ha
  exact rel_trans (hF _ _ ha) hb

theorem reindex_fix {α : Sort u} {β : Sort v} [CCPO α] [CCPO β]
    (F : α → α) (G : β → β) (hF : monotone F) (hG : monotone G)
    (reindex : α → β)
    (hadm : ∀ b, admissible (fun a => reindex a ⊑ b))
    (commute : ∀ a, reindex (F a) = G (reindex a)) :
    reindex (fix F hF) = fix G hG := by
  apply rel_antisymm
  · apply fix_induct hF (fun a => reindex a ⊑ fix G hG) (hadm _)
    intro a ha
    rw [commute]
    have h := hG _ _ ha
    rwa [← fix_eq hG] at h
  · apply fix_le hG
    rw [← commute, ← fix_eq hF]
    exact rel_refl

end Veir.Buffered.Buffed
