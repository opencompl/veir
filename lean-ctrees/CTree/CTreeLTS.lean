module

public import CTree.Tower
public import CTree.LTS.Defs
public import CTree.LTS.Sim
public import CTree.Defs
public import CTree.UB
public import CTree.Iter
public import CTree.Interp

public section

namespace CTree
open Coinductive LTS Lean.Order

variable {EIn FIn CIn C'In DIn : Type u}
  {E : EIn → Type u} {F : FIn → Type u} {C : CIn → Type u} {C' : C'In → Type u} {D : DIn → Type u}
  {α β : Type u} (RR : α → β → Prop)

inductive CTree.Obs : Type u where
| eff i (e : E i)
| effEmpty (i : EIn)
| val (r : α)

inductive CTree.Trans : label (@CTree.Obs _ E α) → CTree E C α → CTree E C α → Prop where
| tau : Trans .tau (.tauG i k) (k x)
| vis : Trans (.obs (.eff i x)) (.vis i k) (k x)
| visEmpty i k : (E i → False) → Trans (.obs (.effEmpty i)) (.vis i k) .empty
| ret : Trans (.obs (.val r)) (.ret r) .empty

@[expose, reducible]
def CTree.lts (EIn CIn : Type u) (E : EIn → Type u) (C : CIn → Type u) (α : Type u) : LTS :=
  ⟨@CTree.Obs _ E _, CTree E C α, CTree.Trans⟩

inductive CTree.Robs (RE : ∀ {i i'}, E i → E i' → Prop) (RR : α → β → Prop) : @Obs EIn E α → @Obs EIn E β → Prop where
| eff i i' (x : E i) (y : E i') (hRE : RE x x') : Robs RE RR (Obs.eff i x) (Obs.eff i' y)
| effEmpty i : Robs RE RR (.effEmpty i) (.effEmpty i)
| val (r : α) (r' : β) : RR r r' → Robs RE RR (.val r) (.val r')

@[refl]
theorem CTree.Robs.refl RE (RR : α → α → Prop) [h : ∀ i, Std.Refl (@RE i i)] [h' : Std.Refl RR] :
    ∀ a, Robs (E := E) RE RR a a := by
  intros a
  cases a
  case eff i x =>
    constructor
    apply (@h i).refl
  case val =>
    constructor
    apply h'.refl
  case effEmpty i =>
    constructor

instance (α : Type u) RE (RR : α → α → Prop)
  [h : ∀ i, Std.Refl (@RE i i)] [h' : Std.Refl RR] :
    Std.Refl (CTree.Robs (E := E) RE RR) where
  refl := CTree.Robs.refl RE RR

@[expose]
def CTree.as_state (t : CTree E C α) : (CTree.lts EIn CIn E C α).state := t

@[expose]
def CTree.UB [UB : HasUB EIn] (t : CTree E C α) : Prop :=
  match t.unfold with
  | .vis e _ => UB.isUB e
  | _ => False

@[grind .]
theorem trans_empty : CTree.Trans l CTree.empty t' → False := by
  intros h
  generalize ht : CTree.empty = t at h
  cases h
  case tau i k x =>
    have ht := tauG_eq_tauG _ _ _ _ ht
    subst ht
    cases x
  case vis =>
    grind
  case ret =>
    grind
  case visEmpty =>
    grind

@[grind .]
theorem trans_ret : CTree.Trans l (CTree.ret r) t' → l = .obs (.val r) := by
  intros h
  generalize ht : CTree.ret r = t at h
  cases h <;> grind

@[grind .]
theorem trans_ret' : CTree.Trans l (CTree.ret r) t' → t' = CTree.empty := by
  intros h
  generalize ht : CTree.ret r = t at h
  cases h <;> grind

@[grind .]
theorem trans_tau : CTree.Trans l (CTree.tauG i k) t' → l = .tau := by
  intros h
  generalize ht : CTree.tauG i k = t at h
  cases h <;> grind

@[grind .]
theorem trans_tau' : CTree.Trans .tau (CTree.tauG i k) t' → exists o, t' = k o := by
  intros h
  generalize ht : CTree.tauG i k = t at h
  cases h
  case tau i k x =>
    have ht' := tauG_eq_tauG _ _ _ _ ht
    subst ht'
    have ht' := tauG_eq_tauG' _ _ _ ht
    rw [ht']
    exists x

--@[grind .]
--theorem trans_vis : CTree.Trans l (CTree.vis i k) t' → (l = .obs (.effEmpty i) ∧ t' = .empty) ∨ exists o, l = .obs (.eff i o) := by

@[grind .]
theorem trans_vis i (k : E i → CTree E C α) l t' [inh : Inhabited (E i)] : CTree.Trans l (CTree.vis i k) t' → exists o, l = .obs (.eff i o) := by
  intros h
  generalize ht : CTree.vis i k = t at h
  cases h
  case tau =>
    grind
  case vis i x k =>
    have ht := vis_eq_vis _ _ _ _ ht
    rw [ht]
    exists x
  case ret =>
    grind
  case visEmpty i k h =>
    have ht := vis_eq_vis _ _ _ _ ht
    subst ht
    have h := h inh.default
    contradiction

@[grind .]
theorem trans_vis' : CTree.Trans (.obs (.eff i o)) (CTree.vis i k) t' → t' = k o := by
  intros h
  generalize ht : CTree.vis i k = t at h
  cases h
  case vis i x k =>
    have ht'' := vis_eq_vis' _ _ _ ht
    subst ht''
    rfl

end CTree

