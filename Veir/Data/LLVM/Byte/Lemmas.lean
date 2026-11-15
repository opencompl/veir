module

import all Veir.Data.LLVM.Byte.Basic
meta import Veir.Meta.Tactic.BVDecide

namespace Veir.Data.LLVM.Byte

open Veir.Data.LLVM.Int
attribute [local grind cases] Int

theorem toInt_fromInt {w : Nat} (x : Int w) (h : 0 < w) : (Byte.fromInt x).toInt = x := by
  simp only [Byte.toInt, fromInt, BitVec.toNat_eq];
  grind

@[veir_bv_normalize]
theorem ext_iff {w : Nat} (x y : Byte w) :
    x = y ↔ (x.val = y.val ∧ x.poison = y.poison) := by
  rw [Byte.mk.injEq]

/- # {to,from}Int -/
section ToFromInt
attribute [local grind] Byte.toInt Byte.fromInt

@[veir_bv_normalize] theorem val_fromInt (x : Int w) : (fromInt x).val = x.getValueD := by grind
@[veir_bv_normalize] theorem poison_fromInt (x : Int w) :
    (fromInt x).poison = if x.isPoison then .allOnes _ else 0 := by
  grind

@[veir_bv_normalize] theorem getValue_toInt (x : Byte w) (h : x.toInt.isPoison = false) :
    x.toInt.getValue h = x.val := by
  grind

@[veir_bv_normalize] theorem isPoison_toInt (x : Byte w) :
    x.toInt.isPoison = (x.poison != 0) := by
  grind

end ToFromInt

/- # and -/

@[veir_bv_normalize]
theorem and_eq {w : Nat} (x y : Byte w) :
    (x &&& y) =
    let poison := x.poison ||| y.poison
    ⟨(x.val &&& y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩ := by
  rfl

theorem and_comm {w : Nat} (x y : Byte w) :
    x &&& y = y &&& x := by
  simp only [and_eq, BitVec.and_comm, BitVec.or_comm]

theorem val_and {w : Nat} (x y : Byte w) :
    (x &&& y).val = (x.val &&& y.val) &&& ~~~(x.poison ||| y.poison) := by
  simp [and_eq]

/- # or -/

@[veir_bv_normalize]
theorem or_eq {w : Nat} (x y : Byte w) :
    (x ||| y) =
    let poison := x.poison ||| y.poison
    ⟨(x.val ||| y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩ := by
  rfl

theorem or_comm {w : Nat} (x y : Byte w) :
    x ||| y = y ||| x := by
  simp only [or_eq, BitVec.or_comm]

theorem val_or {w : Nat} (x y : Byte w) :
    (x ||| y).val = (x.val ||| y.val) &&& ~~~(x.poison ||| y.poison) := by
  simp [or_eq]

/- # xor -/

@[veir_bv_normalize]
theorem xor_eq {w : Nat} (x y : Byte w) :
    (x ^^^ y) =
    let poison := x.poison ||| y.poison
    ⟨(x.val ^^^ y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩ := by
  rfl

theorem xor_comm {w : Nat} (x y : Byte w) :
    x ^^^ y = y ^^^ x := by
  simp only [xor_eq, BitVec.xor_comm, BitVec.or_comm]

theorem val_xor {w : Nat} (x y : Byte w) :
    (x ^^^ y).val = (x.val ^^^ y.val) &&& ~~~(x.poison ||| y.poison) := by
  simp [xor_eq]

/- # shl -/

/-- `Byte.shl` as a conditional chain. Unlike `Byte.lshr`, `Byte.shl` is defined as a `do`-block,
which `bv_decide` cannot see through; this restates it in the same shape as `Byte.lshr` so that the
normalization set can unfold it. -/
@[veir_bv_normalize]
theorem shl_eq {w : Nat} (x : Byte w) (y : Int w) (nuw : Bool) :
    x.shl y nuw =
      if y.isPoison || y.getValueD ≥ w then allPoison
      else if nuw ∧ (x.val <<< y.getValueD) >>> y.getValueD ≠ x.val then allPoison
      else if nuw ∧ (x.poison <<< y.getValueD) >>> y.getValueD ≠ x.poison then allPoison
      else ⟨x.val <<< y.getValueD, x.poison <<< y.getValueD, by
        simp [← BitVec.shiftLeft_and_distrib, x.h]⟩ := by
  cases y with
  | poison => simp [Byte.shl, Id.run, Int.isPoison_of_poison]
  | val y' =>
    simp only [Byte.shl, Id.run, Int.isPoison_of_val, Int.getValueD_val, Bool.false_or,
      decide_eq_true_eq]
    repeat' split
    all_goals first | rfl | simp_all | (exfalso; bv_omega)

/-! # Refinement -/

theorem getLsbD_of_isRefinedBy' {w : Nat} {b b' : Byte w} (h : b ⊒ b') {m : Nat}
    (hm : m < w) :
    b.poison.getLsbD m = true ∨
      (b.val.getLsbD m = b'.val.getLsbD m ∧ b'.poison.getLsbD m = false) := by
  have h' := congrArg (·.getLsbD m) h
  by_cases htrue : b.poison.getLsbD m = true
  · simp [htrue]
  · simp only [BitVec.getLsbD_or, htrue, BitVec.getLsbD_and, BitVec.getLsbD_xor,
      BitVec.getLsbD_not, Bool.false_or, BitVec.getLsbD_allOnes, Bool.false_eq_true, false_or] at ⊢ h'
    simp only [hm, decide_true, Bool.true_and, Bool.bne_not, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq] at h'
    exact h'

/-- Byte refinement from its per-bit form. -/
private theorem isRefinedBy_of_getLsbD {w : Nat} {b b' : Byte w}
    (h : ∀ m < w, b.poison.getLsbD m = true ∨
      (b.val.getLsbD m = b'.val.getLsbD m ∧ b'.poison.getLsbD m = false)) : b ⊒ b' := by
  apply BitVec.eq_of_getLsbD_eq
  intro m hm
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor,
    BitVec.getLsbD_not, BitVec.getLsbD_allOnes, hm, decide_true, Bool.true_and]
  rcases h m hm with h₁ | ⟨h₂, h₃⟩
  · simp [h₁]
  · simp [h₂, h₃]

/-- Shifting left and back right keeps `a` iff its top `s` bits are zero. -/
private theorem shiftLeft_ushiftRight_eq_iff {w : Nat} (a : BitVec w) (s : Nat) :
    (a <<< s) >>> s = a ↔ ∀ i < w, w ≤ s + i → a.getLsbD i = false := by
  constructor
  · intro h i hi hs
    have := congrArg (·.getLsbD i) h
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft] at this
    rw [← this]
    simp [Nat.not_lt.mpr hs]
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    by_cases hs : s + i < w
    · simp [hs, Nat.add_sub_cancel_left]
    · simp [hs, h i hi (Nat.not_lt.mp hs)]

/-- Shifting right and back left keeps `a` iff its low `s` bits are zero. -/
private theorem ushiftRight_shiftLeft_eq_iff {w : Nat} (a : BitVec w) (s : Nat) :
    (a >>> s) <<< s = a ↔ ∀ i < w, i < s → a.getLsbD i = false := by
  constructor
  · intro h i hi hs
    have := congrArg (·.getLsbD i) h
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft] at this
    rw [← this]
    simp [hs]
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    by_cases hs : i < s
    · simp [hs, h i hi hs]
    · simp [hs, hi, Nat.add_sub_cancel' (Nat.not_lt.mp hs)]

/--
If the bits of `x` selected by `P` are neither poison nor set, the same holds in a refinement.
-/
private theorem bits_false_of_isRefinedBy {w : Nat} {x x' : Byte w} (h : x ⊒ x')
    (P : Nat → Prop)
    (hv : ∀ i < w, P i → x.val.getLsbD i = false)
    (hp : ∀ i < w, P i → x.poison.getLsbD i = false) :
    (∀ i < w, P i → x'.val.getLsbD i = false) ∧
      (∀ i < w, P i → x'.poison.getLsbD i = false) := by
  constructor
  all_goals
    intro i hi hP
    rcases getLsbD_of_isRefinedBy' h hi with h₁ | ⟨h₂, h₃⟩
    · simp [hp i hi hP] at h₁
    · first | exact h₃ | rw [← h₂]; exact hv i hi hP

/-- Truncation is monotone under refinement. -/
theorem trunc_isRefinedBy {w : Nat} {x x' : Byte w} (h : x ⊒ x') (w' : Nat) :
    x.trunc w' ⊒ x'.trunc w' := by
  apply isRefinedBy_of_getLsbD
  intro m hm
  simp only [trunc, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hm, decide_true,
    Bool.true_and]
  by_cases hw : m < w
  · exact getLsbD_of_isRefinedBy' h hw
  · simp [BitVec.getLsbD_of_ge _ _ (Nat.not_lt.mp hw)]

/-- Left shift is monotone under refinement, also with `nuw`. -/
theorem shl_isRefinedBy {w : Nat} {x x' : Byte w} {y y' : Int w} (hx : x ⊒ x')
    (hy : _root_.isRefinedBy y y') (nuw : Bool) :
    x.shl y nuw ⊒ x'.shl y' nuw := by
  cases y with
  | poison => exact allPoison_isRefinedBy _
  | val s =>
    cases y' with
    | poison => simp [_root_.isRefinedBy] at hy
    | val s' =>
      simp only [_root_.isRefinedBy] at hy
      subst hy
      simp only [shl, Id.run]
      by_cases hs : s ≥ ↑w
      · rw [ite_eq_left hs]; exact allPoison_isRefinedBy _
      rw [ite_eq_right hs, ite_eq_right hs]
      by_cases hv : nuw = true ∧ (x.val <<< s) >>> s ≠ x.val
      · rw [ite_eq_left hv]; exact allPoison_isRefinedBy _
      rw [ite_eq_right hv]
      by_cases hp : nuw = true ∧ (x.poison <<< s) >>> s ≠ x.poison
      · rw [ite_eq_left hp]; exact allPoison_isRefinedBy _
      rw [ite_eq_right hp]
      have hv' : ¬(nuw = true ∧ (x'.val <<< s) >>> s ≠ x'.val) := by
        rintro ⟨hn, hne⟩
        simp only [hn, true_and, Decidable.not_not, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
          shiftLeft_ushiftRight_eq_iff] at hv hp hne
        exact hne ((shiftLeft_ushiftRight_eq_iff _ _).mpr
          (bits_false_of_isRefinedBy hx _ hv hp).1)
      have hp' : ¬(nuw = true ∧ (x'.poison <<< s) >>> s ≠ x'.poison) := by
        rintro ⟨hn, hne⟩
        simp only [hn, true_and, Decidable.not_not, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
          shiftLeft_ushiftRight_eq_iff] at hv hp hne
        exact hne ((shiftLeft_ushiftRight_eq_iff _ _).mpr
          (bits_false_of_isRefinedBy hx _ hv hp).2)
      rw [ite_eq_right hv', ite_eq_right hp']
      apply isRefinedBy_of_getLsbD
      intro m hm
      simp only [BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft, hm, decide_true, Bool.true_and]
      by_cases hms : m < s.toNat
      · simp [hms]
      · simp only [hms, decide_false, Bool.not_false, Bool.true_and]
        exact getLsbD_of_isRefinedBy' hx (by omega)

/-- `lshr` by a non-poison amount, with the conditions stated on the shift amount itself. -/
private theorem lshr_val {w : Nat} (x : Byte w) (s : BitVec w) (exact : Bool) :
    x.lshr (.val s) exact =
      if s ≥ ↑w then allPoison
      else if exact = true ∧ (x.val >>> s) <<< s ≠ x.val then allPoison
      else if exact = true ∧ (x.poison >>> s) <<< s ≠ x.poison then allPoison
      else ⟨x.val >>> s, x.poison >>> s, by simp [← BitVec.ushiftRight_and_distrib, x.h]⟩ := by
  unfold lshr; simp only [Int.isPoison, Bool.false_or, decide_eq_true_eq]; rfl

/-- Logical right shift is monotone under refinement, also with `exact`. -/
theorem lshr_isRefinedBy {w : Nat} {x x' : Byte w} {y y' : Int w} (hx : x ⊒ x')
    (hy : _root_.isRefinedBy y y') (exact : Bool) :
    x.lshr y exact ⊒ x'.lshr y' exact := by
  cases y with
  | poison =>
    simp only [lshr, Int.isPoison, Bool.true_or, ↓reduceIte]
    exact allPoison_isRefinedBy _
  | val s =>
    cases y' with
    | poison => simp [_root_.isRefinedBy] at hy
    | val s' =>
      simp only [_root_.isRefinedBy] at hy
      subst hy
      rw [lshr_val, lshr_val]
      by_cases hs : s ≥ ↑w
      · rw [ite_eq_left hs]; exact allPoison_isRefinedBy _
      rw [ite_eq_right hs, ite_eq_right hs]
      by_cases hv : exact = true ∧ (x.val >>> s) <<< s ≠ x.val
      · rw [ite_eq_left hv]; exact allPoison_isRefinedBy _
      rw [ite_eq_right hv]
      by_cases hp : exact = true ∧ (x.poison >>> s) <<< s ≠ x.poison
      · rw [ite_eq_left hp]; exact allPoison_isRefinedBy _
      rw [ite_eq_right hp]
      have hv' : ¬(exact = true ∧ (x'.val >>> s) <<< s ≠ x'.val) := by
        rintro ⟨hn, hne⟩
        simp only [hn, true_and, Decidable.not_not, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
          ushiftRight_shiftLeft_eq_iff] at hv hp hne
        exact hne ((ushiftRight_shiftLeft_eq_iff _ _).mpr
          (bits_false_of_isRefinedBy hx _ hv hp).1)
      have hp' : ¬(exact = true ∧ (x'.poison >>> s) <<< s ≠ x'.poison) := by
        rintro ⟨hn, hne⟩
        simp only [hn, true_and, Decidable.not_not, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
          ushiftRight_shiftLeft_eq_iff] at hv hp hne
        exact hne ((ushiftRight_shiftLeft_eq_iff _ _).mpr
          (bits_false_of_isRefinedBy hx _ hv hp).2)
      rw [ite_eq_right hv', ite_eq_right hp']
      apply isRefinedBy_of_getLsbD
      intro m hm
      simp only [BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight]
      by_cases hms : s.toNat + m < w
      · exact getLsbD_of_isRefinedBy' hx hms
      · simp [BitVec.getLsbD_of_ge _ _ (Nat.not_lt.mp hms)]

/-- Converting a byte to an integer is monotone under refinement. -/
theorem toInt_isRefinedBy {w : Nat} {x x' : Byte w} (h : x ⊒ x') :
    _root_.isRefinedBy x.toInt x'.toInt := by
  by_cases hp : x.poison = 0
  · have hp' : x'.poison = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro m hm
      rcases getLsbD_of_isRefinedBy' h hm with h₁ | ⟨_, h₃⟩
      · simp [hp] at h₁
      · simpa using h₃
    have hv : x'.val = x.val := by
      apply BitVec.eq_of_getLsbD_eq
      intro m hm
      rcases getLsbD_of_isRefinedBy' h hm with h₁ | ⟨h₂, _⟩
      · simp [hp] at h₁
      · exact h₂.symm
    simp [toInt, hp, hp', hv, _root_.isRefinedBy]
  · rw [toInt, ite_eq_right hp]; exact _root_.poison_isRefinedBy _

/-- Converting an integer to a byte is monotone under refinement. -/
theorem fromInt_isRefinedBy {w : Nat} {i i' : Int w} (h : _root_.isRefinedBy i i') :
    fromInt i ⊒ fromInt i' := by
  cases i with
  | poison => rw [fromInt_poison]; exact allPoison_isRefinedBy _
  | val v =>
    cases i' with
    | poison => simp [_root_.isRefinedBy] at h
    | val v' =>
      simp only [_root_.isRefinedBy] at h
      subst h
      exact isRefinedBy_refl _

end

end Veir.Data.LLVM.Byte

end Veir.Data.LLVM.Byte
