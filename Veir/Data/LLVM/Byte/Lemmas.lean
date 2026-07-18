module

public import Veir.Data.LLVM.Byte.Basic
public import Veir.Data.Refinement
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.Refinement
meta import Veir.Meta.BVDecide

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


public section

/-- A concrete integer is refined only by itself. -/
private theorem int_eq_of_val_isRefinedBy {w : Nat} {v : BitVec w} {x : Int w}
    (h : Int.val v ⊒ x) : x = Int.val v := by
  cases x with
  | poison => exact absurd h (by simp [_root_.isRefinedBy])
  | val u =>
    have : v = u := by simpa [_root_.isRefinedBy] using h
    simp [this]

/-- Bit-wise characterisation of byte refinement: at every bit, either the source bit is poison,
or the value bits agree and the target bit is not poison. -/
theorem isRefinedBy_iff {w : Nat} (x y : Byte w) :
    x ⊒ y ↔ ∀ i, i < w →
      (x.poison.getLsbD i = true ∨
        (x.val.getLsbD i = y.val.getLsbD i ∧ y.poison.getLsbD i = false)) := by
  simp only [isRefinedBy, BitVec.eq_of_getLsbD_eq_iff, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_allOnes]
  constructor
  · intro h i hi
    have hbit := h i hi
    revert hbit
    simp only [hi, decide_true, Bool.true_and]
    cases x.poison.getLsbD i <;> cases x.val.getLsbD i <;> cases y.val.getLsbD i <;>
      cases y.poison.getLsbD i <;> simp
  · intro h i hi
    have hbit := h i hi
    revert hbit
    simp only [hi, decide_true, Bool.true_and]
    cases x.poison.getLsbD i <;> cases x.val.getLsbD i <;> cases y.val.getLsbD i <;>
      cases y.poison.getLsbD i <;> simp

/-- The all-poison byte refines every byte. -/
theorem allPoison_isRefinedBy {w : Nat} (y : Byte w) :
    allPoison ⊒ y := by
  rw [isRefinedBy_iff]
  intro i hi
  simp [allPoison, hi]

/-- Shifting left and back right is the identity exactly when the bits shifted out are zero. -/
private theorem bv_shiftLeft_ushiftRight_eq_self_iff {w : Nat} (v : BitVec w) (n : Nat) :
    (v <<< n) >>> n = v ↔ ∀ i, i < w → w ≤ i + n → v.getLsbD i = false := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, Nat.add_sub_cancel_left]
  constructor
  · intro h i hi hw
    have := h i hi
    simp only [Nat.not_lt.mpr (by omega : w ≤ n + i), decide_false, Bool.false_and] at this
    grind
  · intro h i hi
    by_cases hw : n + i < w
    · simp [hw]
    · simp only [hw, decide_false, Bool.false_and]
      exact (h i hi (by omega)).symm

/-- Shifting right and back left is the identity exactly when the bits shifted out are zero. -/
private theorem bv_ushiftRight_shiftLeft_eq_self_iff {w : Nat} (v : BitVec w) (n : Nat) :
    (v >>> n) <<< n = v ↔ ∀ i, i < n → v.getLsbD i = false := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  constructor
  · intro h i hi
    by_cases hiw : i < w
    · have := h i hiw
      simp only [hiw, decide_true, Bool.true_and, hi, decide_true, Bool.not_true,
        Bool.false_and] at this
      exact this.symm
    · exact BitVec.getLsbD_of_ge v i (by omega)
  · intro h i hi
    by_cases hin : i < n
    · simp only [hi, decide_true, Bool.true_and, hin, decide_true, Bool.not_true, Bool.false_and]
      exact (h i hin).symm
    · simp only [hi, decide_true, Bool.true_and, hin, decide_false, Bool.not_false,
        Bool.true_and]
      congr 1
      omega

/-- Shifting both the value and the poison mask left preserves byte refinement. -/
theorem shiftLeft_isRefinedBy {w : Nat} {x y : Byte w} (h : x ⊒ y)
    (s : BitVec w) (hx : (x.val <<< s) &&& (x.poison <<< s) = 0)
    (hy : (y.val <<< s) &&& (y.poison <<< s) = 0) :
    (⟨x.val <<< s, x.poison <<< s, hx⟩ : Byte w) ⊒
      ⟨y.val <<< s, y.poison <<< s, hy⟩ := by
  rw [isRefinedBy_iff] at h ⊢
  intro i hi
  simp only [BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  by_cases hlt : i < s.toNat
  · simp [hlt]
  · simp only [hlt, decide_false, Bool.not_false, Bool.true_and]
    exact h (i - s.toNat) (by omega)

/-- Shifting both the value and the poison mask right preserves byte refinement. -/
theorem ushiftRight_isRefinedBy {w : Nat} {x y : Byte w} (h : x ⊒ y)
    (s : BitVec w) (hx : (x.val >>> s) &&& (x.poison >>> s) = 0)
    (hy : (y.val >>> s) &&& (y.poison >>> s) = 0) :
    (⟨x.val >>> s, x.poison >>> s, hx⟩ : Byte w) ⊒
      ⟨y.val >>> s, y.poison >>> s, hy⟩ := by
  rw [isRefinedBy_iff] at h ⊢
  intro i hi
  simp only [BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight]
  by_cases hlt : s.toNat + i < w
  · exact h (s.toNat + i) hlt
  · right
    exact ⟨by rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)],
      BitVec.getLsbD_of_ge _ _ (by omega)⟩

/-- If the source byte loses no bit when shifted left (the `nuw` check of `shl`), then
neither does a byte refining it: the bits shifted out are concrete zeros in the source, hence also
in the target. -/
theorem shl_noWrap_of_isRefinedBy {w : Nat} {x y : Byte w} (h : x ⊒ y)
    (s : BitVec w) (hv : (x.val <<< s) >>> s = x.val)
    (hp : (x.poison <<< s) >>> s = x.poison) :
    (y.val <<< s) >>> s = y.val ∧ (y.poison <<< s) >>> s = y.poison := by
  rw [isRefinedBy_iff] at h
  rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq'] at hv hp
  rw [bv_shiftLeft_ushiftRight_eq_self_iff] at hv hp
  constructor <;>
    · rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', bv_shiftLeft_ushiftRight_eq_self_iff]
      intro i hi hw
      rcases h i hi with hpoison | ⟨hval, hypoison⟩
      · simp [hp i hi hw] at hpoison
      · first
          | (rw [← hval]; exact hv i hi hw)
          | exact hypoison

/-- If the source byte loses no bit when shifted right (the `exact` check of `lshr`),
then neither does a byte refining it. -/
theorem lshr_exact_of_isRefinedBy {w : Nat} {x y : Byte w} (h : x ⊒ y)
    (s : BitVec w) (hv : (x.val >>> s) <<< s = x.val)
    (hp : (x.poison >>> s) <<< s = x.poison) :
    (y.val >>> s) <<< s = y.val ∧ (y.poison >>> s) <<< s = y.poison := by
  rw [isRefinedBy_iff] at h
  rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq'] at hv hp
  rw [bv_ushiftRight_shiftLeft_eq_self_iff] at hv hp
  constructor <;>
    · rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', bv_ushiftRight_shiftLeft_eq_self_iff]
      intro i hi
      by_cases hiw : i < w
      · rcases h i hiw with hpoison | ⟨hval, hypoison⟩
        · simp [hp i hi] at hpoison
        · first
            | (rw [← hval]; exact hv i hi)
            | exact hypoison
      · exact BitVec.getLsbD_of_ge _ _ (by omega)

/-- `shl` is monotone in both of its operands. -/
theorem shl_mono {w : Nat} (x y : Byte w) (a b : Int w) (nuw : Bool)
    (hxy : x ⊒ y) (hab : a ⊒ b) :
    shl x a nuw ⊒ shl y b nuw := by
  cases a with
  | poison =>
    rw [shl_eq]
    simp only [Int.isPoison_of_poison, Bool.true_or, if_true]
    exact allPoison_isRefinedBy _
  | val s =>
    rw [int_eq_of_val_isRefinedBy hab, shl_eq, shl_eq]
    simp only [Int.isPoison_of_val, Int.getValueD_val, Bool.false_or]
    split
    · exact allPoison_isRefinedBy _
    · by_cases hnuw : nuw = true
      · subst hnuw
        split
        · exact allPoison_isRefinedBy _
        · next hv =>
          split
          · exact allPoison_isRefinedBy _
          · next hp =>
            have hv' : (x.val <<< s) >>> s = x.val := by simpa using hv
            have hp' : (x.poison <<< s) >>> s = x.poison := by simpa using hp
            obtain ⟨hvy, hpy⟩ := shl_noWrap_of_isRefinedBy hxy s hv' hp'
            rw [if_neg (by simpa using hvy), if_neg (by simpa using hpy)]
            exact shiftLeft_isRefinedBy hxy s _ _
      · simp only [Bool.not_eq_true] at hnuw
        subst hnuw
        simp only [Bool.false_eq_true, false_and, if_false]
        exact shiftLeft_isRefinedBy hxy s _ _

/-- `lshr` is monotone in both of its operands. -/
theorem lshr_mono {w : Nat} (x y : Byte w) (a b : Int w) (exact : Bool)
    (hxy : x ⊒ y) (hab : a ⊒ b) :
    lshr x a exact ⊒ lshr y b exact := by
  cases a with
  | poison =>
    simp only [lshr, Int.isPoison_of_poison, Bool.true_or, if_true]
    exact allPoison_isRefinedBy _
  | val s =>
    rw [int_eq_of_val_isRefinedBy hab]
    simp only [lshr, Int.isPoison_of_val, Int.getValueD_val, Bool.false_or]
    split
    · exact allPoison_isRefinedBy _
    · by_cases hexact : exact = true
      · subst hexact
        split
        · exact allPoison_isRefinedBy _
        · next hv =>
          split
          · exact allPoison_isRefinedBy _
          · next hp =>
            have hv' : (x.val >>> s) <<< s = x.val := by simpa using hv
            have hp' : (x.poison >>> s) <<< s = x.poison := by simpa using hp
            obtain ⟨hvy, hpy⟩ := lshr_exact_of_isRefinedBy hxy s hv' hp'
            rw [if_neg (by simpa using hvy), if_neg (by simpa using hpy)]
            exact ushiftRight_isRefinedBy hxy s _ _
      · simp only [Bool.not_eq_true] at hexact
        subst hexact
        simp only [Bool.false_eq_true, false_and, if_false]
        exact ushiftRight_isRefinedBy hxy s _ _

/-- `trunc` is monotone. -/
theorem trunc_mono {w w' : Nat} (x y : Byte w) (h : x ⊒ y) :
    trunc x w' ⊒ trunc y w' := by
  rw [isRefinedBy_iff] at h ⊢
  intro i hi
  simp only [trunc, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases hiw : i < w
  · exact h i hiw
  · right
    exact ⟨by rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)],
      BitVec.getLsbD_of_ge _ _ (by omega)⟩

end

end Veir.Data.LLVM.Byte
