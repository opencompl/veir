import Veir.Meta.Tactic.PBVDecide.Basic
import Veir.Data.PBV

namespace Veir.Meta.Tactic.PBVDecide

open Veir.Data.PBV

structure Env where
  atom : Nat -> Nat

abbrev TmKind.Sem : TmKind → Type
  | .width => Nat
  | .prop  => Prop

def Tm.denote (self : Tm k) (ρ : Env) : k.Sem :=
  match self with
  | .widthLit val => val
  | .widthAtom id | .widthFVar id _ => ρ.atom id
  | .widthAdd a b => (a.denote ρ) + (b.denote ρ)
  | .widthSub a b => (a.denote ρ) - (b.denote ρ)
  | .widthLt  v w => (v.denote ρ) < (w.denote ρ)
  | .widthLe  v w => (v.denote ρ) ≤ (w.denote ρ)
  | .widthEq  v w => (v.denote ρ) = (w.denote ρ)
  | .and      v w => (v.denote ρ) ∧ (w.denote ρ)

theorem Tm.width_induction {motive : WidthTm → Prop}
    (lit  : ∀ n, motive (.widthLit n))
    (atom : ∀ i, motive (.widthAtom i))
    (fvar : ∀ i f, motive (.widthFVar i f))
    (add  : ∀ a b, motive a → motive b → motive (.widthAdd a b))
    (sub  : ∀ a b, motive a → motive b → motive (.widthSub a b)) :
    ∀ t, motive t
  | .widthLit n     => lit n
  | .widthAtom i    => atom i
  | .widthFVar i f  => fvar i f
  | .widthAdd a b   => add a b (width_induction lit atom fvar add sub a) (width_induction lit atom fvar add sub b)
  | .widthSub a b   => sub a b (width_induction lit atom fvar add sub a) (width_induction lit atom fvar add sub b)

theorem upperBound_correct (bound : Nat) (ρ : Env) (tm : WidthTm) (hρ : ∀ i, ρ.atom i ≤ bound) :
  tm.denote ρ ≤ tm.getUpperBound bound := by
  induction tm using Tm.width_induction with
  | lit val =>
    unfold Tm.denote Tm.getUpperBound
    simp
  | atom id
  | fvar id _ =>
    apply hρ
  | add v w vih wih =>
    apply Nat.add_le_add
    exact vih
    exact wih
  | sub v w vih wih =>
    unfold Tm.denote Tm.getUpperBound
    grind

def Tm.toMask (maskMap : Nat → BitVec o) : WidthTm → BitVec o
  | .widthLit val => maskOfWidth o val
  | .widthAtom id | .widthFVar id _ => maskMap id
  | .widthAdd v w => (1#o <<< (BitVec.cpop (v.toMask maskMap) + BitVec.cpop (w.toMask maskMap))) - 1#o
  | .widthSub v w => (v.toMask maskMap) >>> BitVec.cpop (w.toMask maskMap)

theorem maskCorrect {o bound : Nat} {ρ : Env} {m : Nat → BitVec o} (tm : WidthTm)
  (hρ : ∀ i, ρ.atom i ≤ bound)
  (hm : ∀ i, m i = maskOfWidth o (ρ.atom i))
  (ho : tm.getUpperBound bound ≤ o) :
    maskOfWidth o (tm.denote ρ) = tm.toMask m := by
  induction tm using Tm.width_induction with
  | lit val =>
    unfold Tm.denote Tm.toMask
    rfl
  | atom id
  | fvar id _ =>
    unfold Tm.denote Tm.toMask
    simp only [hm id]
  | add v w ihv ihw =>
    unfold Tm.denote Tm.toMask
    rw [← ihv, ← ihw]
    have vBound := by apply upperBound_correct bound ρ v hρ
    have wBound := by apply upperBound_correct bound ρ w hρ
    apply add_eq_shift_sum_of_maskOfWidth (w₁ := v.denote ρ) (w₂ := w.denote ρ)
      (hm₁ := rfl) (hm₂ := rfl) (hm₃ := rfl)
    all_goals
      unfold Tm.getUpperBound at ho
      grind
  | sub v w ihv ihw =>
    unfold Tm.denote Tm.toMask
    rw [← ihv, ← ihw]
    have vBound := by apply upperBound_correct bound ρ v hρ
    have wBound := by apply upperBound_correct bound ρ w hρ
    apply sub_eq_shift_sum_of_maskOfWidth (w₁ := v.denote ρ) (w₂ := w.denote ρ)
      (hm₁ := rfl) (hm₂ := rfl) (hm₃ := rfl)
    all_goals
      unfold Tm.getUpperBound at ho
      grind
