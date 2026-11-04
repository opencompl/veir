module

public import Veir.Prelude

public section
namespace Veir.Buffed

/-- A raw result representation with reconstruction from the exact, erased source
result. The source reference is never inspected by executable code. -/
structure ResultView (α : Type u) (β : Type v) where
  project : α → β
  restore : (ref : Erased α) → (raw : β) → raw = project ref.out → α
  restore_eq : ∀ ref raw h, restore ref raw h = ref.out

namespace ResultView

/-- `Subtype` erases its certificate and has the runtime representation of `β`.
In particular, this is not a structure containing an `Erased` payload field. -/
abbrev Checked (view : ResultView α β) (ref : Erased α) :=
  { raw : β // raw = view.project ref.out }

@[expose, inline] def unpack (view : ResultView α β) (ref : Erased α) (raw : view.Checked ref) : α :=
  view.restore ref raw.val raw.property

@[simp] theorem unpack_eq (view : ResultView α β) (ref : Erased α) (raw : view.Checked ref) :
    view.unpack ref raw = ref.out := view.restore_eq _ _ _

theorem project_unpack (view : ResultView α β) (ref : Erased α) (raw : view.Checked ref) :
    view.project (view.unpack ref raw) = raw.val := by
  rw [unpack_eq, raw.property]

@[expose, inline] def identity (α : Type u) : ResultView α α where
  project := id
  restore _ raw _ := raw
  restore_eq _ _ h := h

@[expose, inline] def prod (a : ResultView α α') (b : ResultView β β') :
    ResultView (α × β) (α' × β') where
  project x := (a.project x.1, b.project x.2)
  restore ref raw h :=
    (a.restore (.mk ref.out.1) raw.1 (by simpa only [Erased.out_mk] using congrArg Prod.fst h),
     b.restore (.mk ref.out.2) raw.2 (by simpa only [Erased.out_mk] using congrArg Prod.snd h))
  restore_eq ref raw h := by simp only [a.restore_eq, b.restore_eq, Erased.out_mk]

@[expose, inline] def optionRestore (view : ResultView α β) (ref : Erased (Option α))
    (raw : Option β) (h : raw = ref.out.map view.project) : Option α :=
  match hr : raw with
  | none => none
  | some value =>
    have hs : ref.out.isSome := by
      cases hh : ref.out <;> simp_all
    let innerRef := Erased.mk (ref.out.get hs)
    have hp : value = view.project innerRef.out := by
      simp only [innerRef, Erased.out_mk]
      have hh := h
      rw [← Option.some_get hs] at hh
      exact Option.some.inj hh
    some (view.restore innerRef value hp)

@[expose, inline] def option (view : ResultView α β) : ResultView (Option α) (Option β) where
  project := Option.map view.project
  restore := optionRestore view
  restore_eq ref raw h := by
    unfold optionRestore
    split <;> (try dsimp only)
    · symm
      apply Option.map_eq_none_iff.mp
      symm
      assumption
    · simp only [view.restore_eq, Erased.out_mk, Option.some_get]

theorem map_ite (f : α → β) (c : Prop) [Decidable c] (x y : Option α) :
    (if c then x else y).map f = if c then x.map f else y.map f := by
  split <;> rfl

theorem map_dite (f : α → β) (c : Prop) [Decidable c]
    (x : c → Option α) (y : ¬c → Option α) :
    (if h : c then x h else y h).map f = if h : c then (x h).map f else (y h).map f := by
  split <;> rfl

@[expose, inline] def subtype (view : ResultView α β) (predicate : α → Prop) :
    ResultView (Subtype predicate) β where
  project x := view.project x.val
  restore ref raw h :=
    ⟨view.restore (.mk ref.out.val) raw (by simpa only [Erased.out_mk] using h), by
      rw [view.restore_eq, Erased.out_mk]
      exact ref.out.property⟩
  restore_eq ref raw h := by
    apply Subtype.ext
    exact (view.restore_eq _ _ _).trans (Erased.out_mk _)

end ResultView
end Veir.Buffed
