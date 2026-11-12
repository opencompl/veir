module

public import Veir.Data.LLVM.Byte.Basic
public import Veir.Data.Refinement
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Int.Bitblast

/-!
# Byte operations under refinement

The byte operations used by the interpreter are monotone under refinement: refining the operands
refines the result.
-/

namespace Veir.Data.LLVM.Byte

public section

/-- Per-bit form of byte refinement: a bit is poison, or it is defined and kept. -/
theorem getLsbD_of_isRefinedBy {w : Nat} {b b' : Byte w} (h : b ⊒ b') {m : Nat}
    (hm : m < w) :
    b.poison.getLsbD m = true ∨
      (b.val.getLsbD m = b'.val.getLsbD m ∧ b'.poison.getLsbD m = false) := by
  have h' := congrArg (·.getLsbD m) h
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor,
    BitVec.getLsbD_not, BitVec.getLsbD_allOnes, hm, decide_true, Bool.true_and] at h'
  revert h'
  cases b.poison.getLsbD m <;> cases b'.poison.getLsbD m <;> simp

/-- Byte refinement from its per-bit form. -/
theorem isRefinedBy_of_getLsbD {w : Nat} {b b' : Byte w}
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
    rcases getLsbD_of_isRefinedBy h hi with h₁ | ⟨h₂, h₃⟩
    · simp [hp i hi hP] at h₁
    · first | exact h₃ | rw [← h₂]; exact hv i hi hP

/--
A round-trip guard that a byte passes is passed by its refinements: the bits the round trip
loses are neither set nor poison, and that is inherited.
-/
private theorem guard_of_isRefinedBy {w : Nat} {x x' : Byte w} (h : x ⊒ x') {g : Bool}
    {P : Nat → Prop} {rt : BitVec w → BitVec w}
    (hrt : ∀ a : BitVec w, rt a = a ↔ ∀ i < w, P i → a.getLsbD i = false)
    (hv : ¬(g = true ∧ rt x.val ≠ x.val)) (hp : ¬(g = true ∧ rt x.poison ≠ x.poison)) :
    ¬(g = true ∧ rt x'.val ≠ x'.val) ∧ ¬(g = true ∧ rt x'.poison ≠ x'.poison) := by
  cases g
  · simp
  obtain ⟨hv, hp⟩ : rt x.val = x.val ∧ rt x.poison = x.poison := by simp_all
  obtain ⟨hv', hp'⟩ := bits_false_of_isRefinedBy h P ((hrt _).mp hv) ((hrt _).mp hp)
  simp [(hrt _).mpr hv', (hrt _).mpr hp']

/-- Truncation is monotone under refinement. -/
theorem trunc_isRefinedBy {w : Nat} {x x' : Byte w} (h : x ⊒ x') (w' : Nat) :
    x.trunc w' ⊒ x'.trunc w' := by
  apply isRefinedBy_of_getLsbD
  intro m hm
  simp only [trunc, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hm, decide_true,
    Bool.true_and]
  by_cases hw : m < w
  · exact getLsbD_of_isRefinedBy h hw
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
      simp only [shl, Id.run, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
      by_cases hs : s ≥ ↑w
      · rw [ite_eq_left hs]; exact allPoison_isRefinedBy _
      rw [ite_eq_right hs, ite_eq_right hs]
      by_cases hv : nuw = true ∧ (x.val <<< s.toNat) >>> s.toNat ≠ x.val
      · rw [ite_eq_left hv]; exact allPoison_isRefinedBy _
      rw [ite_eq_right hv]
      by_cases hp : nuw = true ∧ (x.poison <<< s.toNat) >>> s.toNat ≠ x.poison
      · rw [ite_eq_left hp]; exact allPoison_isRefinedBy _
      rw [ite_eq_right hp]
      obtain ⟨hv', hp'⟩ := guard_of_isRefinedBy hx (shiftLeft_ushiftRight_eq_iff · s.toNat) hv hp
      rw [ite_eq_right hv', ite_eq_right hp']
      apply isRefinedBy_of_getLsbD
      intro m hm
      simp only [BitVec.getLsbD_shiftLeft, hm, decide_true, Bool.true_and]
      by_cases hms : m < s.toNat
      · simp [hms]
      · simp only [hms, decide_false, Bool.not_false, Bool.true_and]
        exact getLsbD_of_isRefinedBy hx (by omega)

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
      simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
      by_cases hs : s ≥ ↑w
      · rw [ite_eq_left hs]; exact allPoison_isRefinedBy _
      rw [ite_eq_right hs, ite_eq_right hs]
      by_cases hv : exact = true ∧ (x.val >>> s.toNat) <<< s.toNat ≠ x.val
      · rw [ite_eq_left hv]; exact allPoison_isRefinedBy _
      rw [ite_eq_right hv]
      by_cases hp : exact = true ∧ (x.poison >>> s.toNat) <<< s.toNat ≠ x.poison
      · rw [ite_eq_left hp]; exact allPoison_isRefinedBy _
      rw [ite_eq_right hp]
      obtain ⟨hv', hp'⟩ := guard_of_isRefinedBy hx (ushiftRight_shiftLeft_eq_iff · s.toNat) hv hp
      rw [ite_eq_right hv', ite_eq_right hp']
      apply isRefinedBy_of_getLsbD
      intro m hm
      simp only [BitVec.getLsbD_ushiftRight]
      by_cases hms : s.toNat + m < w
      · exact getLsbD_of_isRefinedBy hx hms
      · simp [BitVec.getLsbD_of_ge _ _ (Nat.not_lt.mp hms)]

/-- A byte without poison is refined only by itself. -/
theorem eq_of_isRefinedBy_of_poison_eq_zero {w : Nat} {b b' : Byte w} (h : b ⊒ b')
    (h₀ : b.poison = 0) : b' = b := by
  have key : ∀ m < w, b'.val.getLsbD m = b.val.getLsbD m ∧ b'.poison.getLsbD m = false := by
    intro m hm
    rcases getLsbD_of_isRefinedBy h hm with h₁ | ⟨h₂, h₃⟩
    · simp [h₀] at h₁
    · exact ⟨h₂.symm, h₃⟩
  obtain ⟨hv, hp⟩ : b'.val = b.val ∧ b'.poison = 0 :=
    ⟨BitVec.eq_of_getLsbD_eq fun m hm => (key m hm).1,
     BitVec.eq_of_getLsbD_eq fun m hm => by simpa using (key m hm).2⟩
  cases b; cases b'; simp_all

/-- Converting a byte to an integer is monotone under refinement. -/
theorem toInt_isRefinedBy {w : Nat} {x x' : Byte w} (h : x ⊒ x') :
    _root_.isRefinedBy x.toInt x'.toInt := by
  by_cases hp : x.poison = 0
  · rw [eq_of_isRefinedBy_of_poison_eq_zero h hp]
    exact _root_.isRefinedBy_refl _
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
