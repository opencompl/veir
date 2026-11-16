module

public import Veir.Data.LLVM.Byte.Bitblast
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Byte.Bitblast
import Veir.ForLean

namespace Veir.Data.LLVM.Byte

open Veir.Data.LLVM.Int
attribute [local grind cases] Int

theorem toInt_fromInt {w : Nat} (x : Int w) (h : 0 < w) : (Byte.fromInt x).toInt = x := by
  simp only [Byte.toInt, fromInt, BitVec.toNat_eq];
  grind

/- # and -/

theorem and_comm {w : Nat} (x y : Byte w) :
    x &&& y = y &&& x := by
  simp only [and_eq, BitVec.and_comm, BitVec.or_comm]

/- # or -/

theorem or_comm {w : Nat} (x y : Byte w) :
    x ||| y = y ||| x := by
  simp only [or_eq, BitVec.or_comm]

/- # xor -/

theorem xor_comm {w : Nat} (x y : Byte w) :
    x ^^^ y = y ^^^ x := by
  simp only [xor_eq, BitVec.xor_comm, BitVec.or_comm]

/-! # Refinement -/

theorem getLsbD_of_isRefinedBy' {w m : Nat} {b b' : Byte w} (h : b ⊒ b') :
    b.poison.getLsbD m = true ∨
      (b.val.getLsbD m = b'.val.getLsbD m ∧ b'.poison.getLsbD m = false) := by
  have h' := congrArg (·.getLsbD m) h
  by_cases htrue : b.poison.getLsbD m = true
  · simp [htrue]
  · by_cases hlt : m < w
    · simp only [BitVec.getLsbD_or, htrue, BitVec.getLsbD_and, BitVec.getLsbD_xor,
        BitVec.getLsbD_not, hlt, decide_true, Bool.true_and, Bool.bne_not, Bool.false_or,
        BitVec.getLsbD_allOnes, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        bne_eq_false_iff_eq] at h'
      simp [htrue, h']
    · simp_all

theorem isRefinedBy_of_getLsbD {w : Nat} {b b' : Byte w}
    (h : ∀ m < w, b.poison.getLsbD m = true ∨
      (b.val.getLsbD m = b'.val.getLsbD m ∧ b'.poison.getLsbD m = false)) : b ⊒ b' := by
  ext k hk
  specialize h k hk
  simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_not,
    Bool.bne_not, BitVec.getElem_allOnes, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, bne_eq_false_iff_eq]
  simp [← BitVec.getLsbD_eq_getElem, h]

theorem val_false_of_isRefinedBy {w i: Nat} {x x' : Byte w} (h : x ⊒ x')
    (P : Nat → Prop)
    (hv : P i → x.val.getLsbD i = false)
    (hp : P i → x.poison.getLsbD i = false) :
    (P i → x'.val.getLsbD i = false) := by
  have := congrArg (·.getLsbD i) h
  by_cases hp' : P i
  · by_cases hlt : i < w
    · simp only [hp', hlt, BitVec.getLsbD_eq_getElem, forall_const] at hv hp h this
      simp only [BitVec.getElem_or, hp, BitVec.getElem_and, BitVec.getElem_xor, hv,
        BitVec.getElem_not, Bool.bne_not, Bool.false_bne, Bool.false_or, BitVec.getElem_allOnes,
        Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
      simp [hp', hlt, this]
    · simp only [hp', forall_const]
      refine BitVec.getLsbD_of_ge x'.val i (by omega)
  · simp [hp']

theorem poison_false_of_isRefinedBy {w i: Nat} {x x' : Byte w} (h : x ⊒ x')
    (P : Nat → Prop)
    (hv : P i → x.val.getLsbD i = false)
    (hp : P i → x.poison.getLsbD i = false) :
    (P i → x'.poison.getLsbD i = false) := by
  have := congrArg (·.getLsbD i) h
  by_cases hp' : P i
  · by_cases hlt : i < w
    · simp only [hp', hlt, BitVec.getLsbD_eq_getElem, forall_const] at hv hp h this
      simp only [BitVec.getElem_or, hp, BitVec.getElem_and, BitVec.getElem_xor, hv,
        BitVec.getElem_not, Bool.bne_not, Bool.false_bne, Bool.false_or, BitVec.getElem_allOnes,
        Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
      simp [hp', hlt, this]
    · simp only [hp', forall_const]
      refine BitVec.getLsbD_of_ge x'.poison i (by omega)
  · simp [hp']

/-- Truncation is monotone under refinement. -/
theorem trunc_isRefinedBy {w : Nat} {x x' : Byte w} (h : x ⊒ x') (w' : Nat) :
    x.trunc w' ⊒ x'.trunc w' := by
  apply isRefinedBy_of_getLsbD
  intro m hm
  simp only [trunc, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hm, decide_true,
    Bool.true_and]
  exact getLsbD_of_isRefinedBy' h

/-- Left shift is monotone under refinement, also with `nuw`. -/
theorem shl_isRefinedBy_of_isRefinedBy {w : Nat} {x x' : Byte w} {y y' : Int w}
      (hx : x ⊒ x') (hy : y ⊒ y') :
    x.shl y nuw ⊒ x'.shl y' nuw := by
  cases y with
  | poison => exact allPoison_isRefinedBy _
  | val s =>
    simp [Int.isRefinedBy_eq] at hy
    split at hy
    · case _ i i' v v' heq =>
      simp [isRefinedBy] at hx
      simp [isRefinedBy, heq, hy, poison_shl, val_shl]
      subst hy
      by_cases hs : BitVec.ofNat w w ≤ v
      <;> by_cases hv : nuw = true ∧ ¬x.val <<< v.toNat >>> v.toNat = x.val
      <;> by_cases hp : nuw = true ∧ ¬x.poison <<< v.toNat >>> v.toNat = x.poison
      <;> simp only [hs, ↓reduceIte, BitVec.not_zero, BitVec.xor_allOnes, BitVec.not_allOnes,
        BitVec.and_zero, BitVec.or_zero]
      <;> simp only [hv, not_false_eq_true, and_self, ↓reduceIte, true_and, ite_not,
        BitVec.zero_xor, BitVec.allOnes_or]
      <;> simp only [hp, not_false_eq_true, and_self, ↓reduceIte, true_and, ite_not,
        BitVec.zero_xor, BitVec.allOnes_or]
      have hv' : ¬(nuw = true ∧ ¬x'.val <<< v.toNat >>> v.toNat = x'.val) := by
        rintro ⟨hn, hne⟩
        simp only [hn, true_and, Decidable.not_not, BitVec.shiftLeft_ushiftRight_eq_iff] at hv hp hne
        exact hne fun i hi hsi =>
          val_false_of_isRefinedBy hx (fun i => i < w ∧ w ≤ v.toNat + i)
            (fun h => hv i h.1 h.2) (fun h => hp i h.1 h.2) ⟨hi, hsi⟩
      have hp' : ¬(nuw = true ∧ ¬x'.poison <<< v.toNat >>> v.toNat = x'.poison) := by
        rintro ⟨hn, hne⟩
        simp only [hn, true_and, Decidable.not_not, BitVec.shiftLeft_ushiftRight_eq_iff] at hv hp hne
        exact hne fun i hi hsi =>
          poison_false_of_isRefinedBy hx (fun i => i < w ∧ w ≤ v.toNat + i)
            (fun h => hv i h.1 h.2) (fun h => hp i h.1 h.2) ⟨hi, hsi⟩
      simp only [hv', hp', ↓reduceIte]
      ext i hi
      have := congrArg (·.getLsbD (i - v.toNat)) hx
      simp only [show i - v.toNat < w by omega, BitVec.getLsbD_eq_getElem, BitVec.getElem_or,
        BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_not, Bool.bne_not,
        BitVec.getElem_allOnes, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true, bne_eq_false_iff_eq, BitVec.getElem_shiftLeft, Bool.not_and, Bool.not_not,
        decide_eq_false_iff_not, Nat.not_lt, bne_iff_ne, ne_eq, decide_eq_true_eq] at this ⊢
      by_cases hiv : i < v.toNat
      · simp [hiv]
      · simp [hiv, decide_false, Bool.not_false, Bool.true_and, show v.toNat ≤ i by omega, this]
    · simp at hy
    · case _ heq =>
      simp at heq


/-- Logical right shift is monotone under refinement, also with `exact`. -/
theorem lshr_isRefinedBy_of_isRefinedBy {w : Nat} {x x' : Byte w} {y y' : Int w}
      (hx : x ⊒ x') (hy : y ⊒ y') :
    x.lshr y exact ⊒ x'.lshr y' exact := by
  cases y with
  | poison => rw [lshr_poison]; exact allPoison_isRefinedBy _
  | val s =>
    simp [Int.isRefinedBy_eq] at hy
    split at hy
    · case _ i i' v v' heq =>
      simp [isRefinedBy] at hx
      simp [isRefinedBy, heq, hy, poison_lshr, val_lshr]
      subst hy
      by_cases hs : BitVec.ofNat w w ≤ v
      <;> by_cases hv : exact = true ∧ ¬x.val >>> v.toNat <<< v.toNat = x.val
      <;> by_cases hp : exact = true ∧ ¬x.poison >>> v.toNat <<< v.toNat = x.poison
      <;> simp only [hs, ↓reduceIte, BitVec.not_zero, BitVec.xor_allOnes, BitVec.not_allOnes,
        BitVec.and_zero, BitVec.or_zero]
      <;> simp only [hv, not_false_eq_true, and_self, ↓reduceIte, true_and, ite_not,
        BitVec.zero_xor, BitVec.allOnes_or]
      <;> simp only [hp, not_false_eq_true, and_self, ↓reduceIte, true_and, ite_not,
        BitVec.zero_xor, BitVec.allOnes_or]
      have hv' : ¬(exact = true ∧ ¬x'.val >>> v.toNat <<< v.toNat = x'.val) := by
        rintro ⟨hn, hne⟩
        simp only [hn, true_and, Decidable.not_not, BitVec.ushiftRight_shiftLeft_eq_iff] at hv hp hne
        exact hne fun i hi hsi =>
          val_false_of_isRefinedBy hx (fun i => i < w ∧ i < v.toNat)
            (fun h => hv i h.1 h.2) (fun h => hp i h.1 h.2) ⟨hi, hsi⟩
      have hp' : ¬(exact = true ∧ ¬x'.poison >>> v.toNat <<< v.toNat = x'.poison) := by
        rintro ⟨hn, hne⟩
        simp only [hn, true_and, Decidable.not_not, BitVec.ushiftRight_shiftLeft_eq_iff] at hv hp hne
        exact hne fun i hi hsi =>
          poison_false_of_isRefinedBy hx (fun i => i < w ∧ i < v.toNat)
            (fun h => hv i h.1 h.2) (fun h => hp i h.1 h.2) ⟨hi, hsi⟩
      simp only [hv', hp', ↓reduceIte]
      ext i hi
      have := congrArg (·.getLsbD (v.toNat + i)) hx
      simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_not,
        Bool.bne_not, BitVec.getElem_allOnes, BitVec.getElem_ushiftRight, BitVec.getLsbD_or,
        BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_allOnes,
        Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        bne_eq_false_iff_eq] at this ⊢
      by_cases hiv : v.toNat + i < w
      · simpa [hiv] using this
      · simp [BitVec.getLsbD_of_ge _ _ (Nat.not_lt.mp hiv)]
    · simp at hy
    · case _ heq =>
      simp at heq

theorem toInt_isRefinedBy {w : Nat} {x x' : Byte w} (h : x ⊒ x') :
    x.toInt ⊒ x'.toInt := by
  have := isPoison_toInt (w := w) (x := x)
  simp only [toInt, BitVec.ofNat_eq_ofNat]
  by_cases hp : x.toInt.isPoison
  · suffices hsuff : ¬ x.poison = 0#w by simp only [hsuff, ↓reduceIte, poison_isRefinedBy]
    simp only [this, BitVec.ofNat_eq_ofNat, bne_iff_ne, ne_eq] at hp
    exact hp
  · simp only [hp, BitVec.ofNat_eq_ofNat, Bool.false_eq, bne_eq_false_iff_eq] at this
    simp only [isRefinedBy, this, BitVec.zero_or, BitVec.and_eq_allOnes_iff] at h
    have hnp : x'.poison = 0#w := by
      ext k hk
      have ⟨_, h⟩ := h
      have := congrArg (·.getLsbD k) h
      simp [hk] at this
      simp [this]
    simp only [this, ↓reduceIte, hnp, isRefinedBy_eq]
    ext k hk
    have ⟨h, _⟩ := h
    have := congrArg (·.getLsbD k) h
    simp [hk] at this
    simp [this]

theorem fromInt_isRefinedBy {w : Nat} {i i' : Int w} (h : i ⊒ i') :
    fromInt i ⊒ fromInt i' := by
  simp only [fromInt, BitVec.ofNat_eq_ofNat]
  simp only [isRefinedBy_eq] at h
  cases i <;> cases i'
  · simp [h]
  · simp at h
  · simp [isRefinedBy]
  · simp


end Veir.Data.LLVM.Byte
