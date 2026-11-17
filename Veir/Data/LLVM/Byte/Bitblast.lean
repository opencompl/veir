module

public meta import Veir.Meta.Tactic.BVDecide
public import Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Byte.Basic

/-!
# Bitblasting lemmas for `Byte`

Like `Veir.Data.LLVM.Int.Bitblast` for bytes: lemmas that unfold every `Byte`
operation into its `val` and `poison` bitvectors for `veir_bv_normalize` and `bv_decide` to reason about,
plus their bit-level chatecterizations.
-/

open Veir.Data.LLVM

namespace Veir.Data.LLVM.Byte

public section

@[veir_bv_normalize]
theorem ext_iff {w : Nat} (x y : Byte w) :
    x = y ↔ (x.val = y.val ∧ x.poison = y.poison) := by
  rw [Byte.mk.injEq]


/- # {to,from}Int -/

@[veir_bv_normalize]
theorem val_fromInt (x : Int w) :
    (fromInt x).val = x.getValueD := by
  cases x <;> simp [fromInt]

@[veir_bv_normalize]
theorem poison_fromInt (x : Int w) :
    (fromInt x).poison = if x.isPoison then .allOnes _ else 0 := by
  cases x <;> simp [fromInt]

@[veir_bv_normalize]
theorem getValue_toInt (x : Byte w) (h : x.toInt.isPoison = false) :
    x.toInt.getValue h = x.val := by
  simp only [toInt, BitVec.ofNat_eq_ofNat]
  grind

@[veir_bv_normalize]
theorem isPoison_toInt (x : Byte w) :
    x.toInt.isPoison = (x.poison != 0) := by
  simp only [toInt, BitVec.ofNat_eq_ofNat]
  grind


/- # and -/

theorem and_eq {w : Nat} (x y : Byte w) :
    (x &&& y) =
    let poison := x.poison ||| y.poison
    ⟨(x.val &&& y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩ := by
  rfl

@[veir_bv_normalize]
theorem val_and {w : Nat} (x y : Byte w) :
    (x &&& y).val = (x.val &&& y.val) &&& ~~~(x.poison ||| y.poison) := by
  simp [and_eq]

@[veir_bv_normalize]
theorem poison_and {w : Nat} (x y : Byte w) :
    (x &&& y).poison = x.poison ||| y.poison := by
  simp [and_eq]


/- # or -/

theorem or_eq {w : Nat} (x y : Byte w) :
    (x ||| y) =
    let poison := x.poison ||| y.poison
    ⟨(x.val ||| y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩ := by
  rfl

@[veir_bv_normalize]
theorem val_or {w : Nat} (x y : Byte w) :
    (x ||| y).val = (x.val ||| y.val) &&& ~~~(x.poison ||| y.poison) := by
  simp [or_eq]

@[veir_bv_normalize]
theorem poison_or {w : Nat} (x y : Byte w) :
    (x ||| y).poison = x.poison ||| y.poison := by
  simp [or_eq]


/- # xor -/

theorem xor_eq {w : Nat} (x y : Byte w) :
    (x ^^^ y) =
    let poison := x.poison ||| y.poison
    ⟨(x.val ^^^ y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩ := by
  rfl

@[veir_bv_normalize]
theorem val_xor {w : Nat} (x y : Byte w) :
    (x ^^^ y).val = (x.val ^^^ y.val) &&& ~~~(x.poison ||| y.poison) := by
  simp [xor_eq]

@[veir_bv_normalize]
theorem poison_xor {w : Nat} (x y : Byte w) :
    (x ^^^ y).poison = x.poison ||| y.poison := by
  simp [xor_eq]


/- # shl -/

theorem shl_eq {w : Nat} (x : Byte w) (y : Int w) (nuw : Bool) :
    (x.shl y nuw) =
      if y.isPoison || y.getValueD ≥ w then allPoison
      else if nuw ∧ (x.val <<< y.getValueD) >>> y.getValueD ≠ x.val then allPoison
      else if nuw ∧ (x.poison <<< y.getValueD) >>> y.getValueD ≠ x.poison then allPoison
      else ⟨x.val <<< y.getValueD, x.poison <<< y.getValueD, by
        simp [← BitVec.shiftLeft_and_distrib, x.h]⟩ := by
  cases y with
  | poison => simp [Byte.shl, Id.run, Int.isPoison_of_poison]
  | val y' =>
    simp [Byte.shl, Id.run, Int.isPoison_of_val, Int.getValueD_val, Bool.false_or,
      decide_eq_true_eq, pure]

@[veir_bv_normalize]
theorem val_shl {w : Nat} (x : Byte w) (y : Int w) (nuw : Bool) :
    (x.shl y nuw).val =
      if y.isPoison || y.getValueD ≥ w then 0#w
      else if nuw ∧ (x.val <<< y.getValueD) >>> y.getValueD ≠ x.val then 0#w
      else if nuw ∧ (x.poison <<< y.getValueD) >>> y.getValueD ≠ x.poison then 0#w
      else x.val <<< y.getValueD := by
  simp only [shl_eq, BitVec.natCast_eq_ofNat, ge_iff_le, Bool.or_eq_true, decide_eq_true_eq,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', ne_eq]
  rcases y with hy | hy
  · simp only [Int.isPoison_of_val, Bool.false_eq_true, Int.getValueD_val, false_or, allPoison,
    BitVec.ofNat_eq_ofNat]
    split
    · simp
    · split
      · simp
      · split <;> simp
  · simp [allPoison]

@[veir_bv_normalize]
theorem poison_shl {w : Nat} (x : Byte w) (y : Int w) (nuw : Bool) :
    (x.shl y nuw).poison =
      if y.isPoison || y.getValueD ≥ w then .allOnes w
      else if nuw ∧ (x.val <<< y.getValueD) >>> y.getValueD ≠ x.val then .allOnes w
      else if nuw ∧ (x.poison <<< y.getValueD) >>> y.getValueD ≠ x.poison then .allOnes w
      else x.poison <<< y.getValueD := by
  simp only [shl_eq, BitVec.natCast_eq_ofNat, ge_iff_le, Bool.or_eq_true, decide_eq_true_eq,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', ne_eq]
  rcases y with hy | hy
  · simp only [Int.isPoison_of_val, Bool.false_eq_true, Int.getValueD_val, false_or, allPoison,
    BitVec.ofNat_eq_ofNat]
    split
    · simp
    · split
      · simp
      · split <;> simp
  · simp [allPoison]


/- # lshr -/

theorem lshr_eq {w : Nat} (x : Byte w) (y : Int w) (exact : Bool) :
    (x.lshr y exact) =
      if y.isPoison || y.getValueD ≥ w then allPoison
      else if exact ∧ (x.val >>> y.getValueD) <<< y.getValueD ≠ x.val then allPoison
      else if exact ∧ (x.poison >>> y.getValueD) <<< y.getValueD ≠ x.poison then allPoison
      else ⟨x.val >>> y.getValueD, x.poison >>> y.getValueD, by
        simp [← BitVec.ushiftRight_and_distrib, x.h]⟩ := by
  rfl

@[veir_bv_normalize]
theorem val_lshr {w : Nat} (x : Byte w) (y : Int w) (exact : Bool) :
    (x.lshr y exact).val =
      if y.isPoison || y.getValueD ≥ w then 0#w
      else if exact ∧ (x.val >>> y.getValueD) <<< y.getValueD ≠ x.val then 0#w
      else if exact ∧ (x.poison >>> y.getValueD) <<< y.getValueD ≠ x.poison then 0#w
      else x.val >>> y.getValueD := by
  simp only [lshr_eq, BitVec.natCast_eq_ofNat, ge_iff_le, Bool.or_eq_true, decide_eq_true_eq,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', ne_eq]
  rcases y with hy | hy
  · simp only [Int.isPoison_of_val, Bool.false_eq_true, Int.getValueD_val, false_or, allPoison,
    BitVec.ofNat_eq_ofNat]
    split
    · simp
    · split
      · simp
      · split <;> simp
  · simp [allPoison]

@[veir_bv_normalize]
theorem poison_lshr {w : Nat} (x : Byte w) (y : Int w) (exact : Bool) :
    (x.lshr y exact).poison =
      if y.isPoison || y.getValueD ≥ w then .allOnes w
      else if exact ∧ (x.val >>> y.getValueD) <<< y.getValueD ≠ x.val then .allOnes w
      else if exact ∧ (x.poison >>> y.getValueD) <<< y.getValueD ≠ x.poison then .allOnes w
      else x.poison >>> y.getValueD := by
  simp only [lshr_eq, BitVec.natCast_eq_ofNat, ge_iff_le, Bool.or_eq_true, decide_eq_true_eq,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', ne_eq]
  rcases y with hy | hy
  · simp only [Int.isPoison_of_val, Bool.false_eq_true, Int.getValueD_val, false_or, allPoison,
    BitVec.ofNat_eq_ofNat]
    split
    · simp
    · split
      · simp
      · split <;> simp
  · simp [allPoison]

/- # getLsbD -/

@[simp]
theorem getLsbD_val_eq_false_of_poison (x : Byte w) {i : Nat} (h : x.poison.getLsbD i = true) :
    x.val.getLsbD i = false := by
  have := congrArg (·.getLsbD i) x.h
  simp_all

@[simp]
theorem getLsbD_poison_eq_false_of_val (x : Byte w) {i : Nat} (h : x.val.getLsbD i = true) :
    x.poison.getLsbD i = false := by
  have := congrArg (·.getLsbD i) x.h
  simp_all

@[simp]
theorem getLsbD_val_and_getLsbD_poison (x : Byte w) (i : Nat) :
    (x.val.getLsbD i && x.poison.getLsbD i) = false := by
  have := congrArg (·.getLsbD i) x.h
  simp_all

@[simp]
theorem getLsbD_poison_and_getLsbD_val (x : Byte w) (i : Nat) :
    (x.poison.getLsbD i && x.val.getLsbD i) = false := by
  rw [Bool.and_comm]
  exact getLsbD_val_and_getLsbD_poison x i


/-! ## allPoison -/

@[simp]
theorem val_allPoison : (allPoison : Byte w).val = 0#w := by
  simp [Byte.allPoison]

@[simp]
theorem poison_allPoison : (allPoison : Byte w).poison = .allOnes w := by
  simp [Byte.allPoison]

@[simp]
theorem getLsbD_val_allPoison (i : Nat) :
    (allPoison : Byte w).val.getLsbD i = false := by
  veir_bv_normalize
  simp

@[simp]
theorem getLsbD_poison_allPoison (i : Nat) :
    (allPoison : Byte w).poison.getLsbD i = decide (i < w) := by
  simp [poison_allPoison]


/-! ## cast -/

theorem val_cast {w₁ w₂ : Nat} (x : Byte w₁) (h : w₁ = w₂) :
    (x.cast h).val = x.val.cast h := by
  simp [Byte.cast]

theorem poison_cast {w₁ w₂ : Nat} (x : Byte w₁) (h : w₁ = w₂) :
    (x.cast h).poison = x.poison.cast h := by
  simp [Byte.cast]

@[simp]
theorem getLsbD_val_cast {w₁ w₂ : Nat} (x : Byte w₁) (h : w₁ = w₂) (i : Nat) :
    (x.cast h).val.getLsbD i = x.val.getLsbD i := by
  simp [val_cast]

@[simp]
theorem getLsbD_poison_cast {w₁ w₂ : Nat} (x : Byte w₁) (h : w₁ = w₂) (i : Nat) :
    (x.cast h).poison.getLsbD i = x.poison.getLsbD i := by
  simp [poison_cast]


/-! ## and -/

theorem getLsbD_val_and (x y : Byte w) (i : Nat) :
    (x &&& y).val.getLsbD i = (x.val.getLsbD i && y.val.getLsbD i) := by
  have hx := getLsbD_val_and_getLsbD_poison x i
  have hy := getLsbD_val_and_getLsbD_poison y i
  simp only [val_and, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_or, Bool.not_or,
    Bool.and_eq_left_iff_imp, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, and_imp]
  intros hx' hy'
  have hlt := BitVec.lt_of_getLsbD hx'
  simp only [hx', Bool.true_and, hy'] at hx hy
  simp only [hlt, hx, hy, and_self]

theorem getLsbD_poison_and (x y : Byte w) (i : Nat) :
    (x &&& y).poison.getLsbD i = (x.poison.getLsbD i || y.poison.getLsbD i) := by
  simp [poison_and]


/-! ## or -/

theorem getLsbD_val_or (x y : Byte w) (i : Nat) :
    (x ||| y).val.getLsbD i =
      ((x.val.getLsbD i || y.val.getLsbD i) && !x.poison.getLsbD i && !y.poison.getLsbD i) := by
  rw [val_or]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_or]
  by_cases hi : i < w
  · simp only [hi, decide_true]
    generalize x.val.getLsbD i = a; generalize x.poison.getLsbD i = b
    generalize y.val.getLsbD i = c; generalize y.poison.getLsbD i = d
    cases a <;> cases b <;> cases c <;> cases d <;> simp
  · simp [BitVec.getLsbD_of_ge _ _ (Nat.not_lt.mp hi)]

theorem getLsbD_poison_or (x y : Byte w) (i : Nat) :
    (x ||| y).poison.getLsbD i = (x.poison.getLsbD i || y.poison.getLsbD i) := by
  simp [poison_or]


/-! ## xor -/

theorem getLsbD_val_xor (x y : Byte w) (i : Nat) :
    (x ^^^ y).val.getLsbD i =
      ((x.val.getLsbD i ^^ y.val.getLsbD i) && !x.poison.getLsbD i && !y.poison.getLsbD i) := by
  rw [val_xor]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_xor]
  by_cases hi : i < w
  · simp only [hi, decide_true]
    generalize x.val.getLsbD i = a; generalize x.poison.getLsbD i = b
    generalize y.val.getLsbD i = c; generalize y.poison.getLsbD i = d
    cases a <;> cases b <;> cases c <;> cases d <;> simp
  · simp [BitVec.getLsbD_of_ge _ _ (Nat.not_lt.mp hi)]

theorem getLsbD_poison_xor (x y : Byte w) (i : Nat) :
    (x ^^^ y).poison.getLsbD i = (x.poison.getLsbD i || y.poison.getLsbD i) := by
  simp [poison_xor]


/-! ## trunc -/

@[simp]
theorem val_trunc (x : Byte w) (w' : Nat) : (x.trunc w').val = x.val.setWidth w' := by
  simp [Byte.trunc]

@[simp]
theorem poison_trunc (x : Byte w) (w' : Nat) :
    (x.trunc w').poison = x.poison.setWidth w' := by simp [Byte.trunc]

theorem getLsbD_val_trunc (x : Byte w) (w' i : Nat) :
    (x.trunc w').val.getLsbD i = (decide (i < w') && x.val.getLsbD i) := by
  simp

theorem getLsbD_poison_trunc (x : Byte w) (w' i : Nat) :
    (x.trunc w').poison.getLsbD i = (decide (i < w') && x.poison.getLsbD i) := by
  simp


/-! ## freeze -/

@[simp]
theorem val_freeze (x : Byte w) : x.freeze.val = x.val := by
  simp [Byte.freeze]

@[simp]
theorem poison_freeze (x : Byte w) : x.freeze.poison = 0#w := by
  simp [Byte.freeze]

@[simp]
theorem getLsbD_val_freeze (x : Byte w) (i : Nat) :
    x.freeze.val.getLsbD i = x.val.getLsbD i := by
  simp

@[simp]
theorem getLsbD_poison_freeze (x : Byte w) (i : Nat) :
    x.freeze.poison.getLsbD i = false := by
  simp


/-! ## fillPoison -/

@[veir_bv_normalize]
theorem fillPoison_eq (x : Byte w) (chosen : BitVec w) :
    x.fillPoison chosen = x.val ||| (x.poison &&& chosen) := by
  simp [Byte.fillPoison]

@[simp]
theorem getLsbD_fillPoison (x : Byte w) (chosen : BitVec w) (i : Nat) :
    (x.fillPoison chosen).getLsbD i =
      (x.val.getLsbD i || (x.poison.getLsbD i && chosen.getLsbD i)) := by
  simp [fillPoison_eq]


/-! ## fromInt, fromBitVec, fromUInt64 -/

@[simp]
theorem getLsbD_val_fromInt (y : Int w) (i : Nat) :
    (fromInt y).val.getLsbD i = y.getValueD.getLsbD i := by
  simp [val_fromInt]

@[simp]
theorem getLsbD_poison_fromInt (y : Int w) (i : Nat) :
    (fromInt y).poison.getLsbD i = (y.isPoison && decide (i < w)) := by
  rw [poison_fromInt]; split <;> simp_all

@[simp]
theorem getLsbD_val_fromBitVec (v : BitVec w) (i : Nat) :
    (fromBitVec v).val.getLsbD i = v.getLsbD i := by simp

@[simp]
theorem getLsbD_poison_fromBitVec (v : BitVec w) (i : Nat) :
    (fromBitVec v).poison.getLsbD i = false := by simp

/-! ## merge -/

@[simp]
theorem val_merge (x y : Byte w) : (merge x y).val = x.val ||| y.val := rfl

@[simp]
theorem poison_merge (x y : Byte w) : (merge x y).poison = x.poison &&& y.poison := rfl

theorem getLsbD_val_merge (x y : Byte w) (i : Nat) :
    (merge x y).val.getLsbD i = (x.val.getLsbD i || y.val.getLsbD i) := by
  simp

theorem getLsbD_poison_merge (x y : Byte w) (i : Nat) :
    (merge x y).poison.getLsbD i = (x.poison.getLsbD i && y.poison.getLsbD i) := by
  simp

/-- Two bytes are compatible iff on every bit, one of them is poison or they agree. -/
theorem compatible_iff_getLsbD (x y : Byte w) :
    Compatible x y ↔ ∀ i, x.poison.getLsbD i = true ∨ y.poison.getLsbD i = true ∨
      x.val.getLsbD i = y.val.getLsbD i := by
  simp only [Compatible]
  constructor
  · intro h i
    have := congrArg (·.getLsbD i) h
    by_cases hlt : i < w
    · by_cases hxp : x.poison.getLsbD i = true
      · simp [hxp]
      · by_cases hbit : y.poison.getLsbD i = true
        · simp [hbit, hxp]
        · simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, hlt,
            decide_true, hbit, Bool.not_false, Bool.and_true, hxp,
            BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, bne_eq_false_iff_eq] at this
          simp [this]
    · simp [BitVec.getLsbD_of_ge x.val i (by omega), BitVec.getLsbD_of_ge y.val i (by omega)]
  · intro h
    ext k hk
    specialize h k
    rcases h with h | h | h
    <;> simp [← BitVec.getLsbD_eq_getElem, h]


/-! ## shl -/

@[simp]
theorem shl_poison (x : Byte w) (nuw : Bool) : x.shl .poison nuw = allPoison := by
  simp [shl_eq]

theorem shl_val_of_le (x : Byte w) {s : BitVec w} (h : w ≤ s.toNat) (nuw : Bool) :
    x.shl (.val s) nuw = allPoison := by
  have hs : (w : BitVec w) ≤ s := by
    simp [BitVec.le_def, Nat.mod_eq_of_lt Nat.lt_two_pow_self, h]
  rw [shl_eq]
  simp only [Int.isPoison_of_val, Int.getValueD_val, Bool.false_or, hs, decide_true, ↓reduceIte]

theorem shl_val_of_nuw_val (x : Byte w) {s : BitVec w} (h : (x.val <<< s) >>> s ≠ x.val) :
    x.shl (.val s) true = allPoison := by
  rw [shl_eq]
  simp only [Int.isPoison_of_val, Int.getValueD_val, Bool.false_or, h, ne_eq, not_false_eq_true,
    and_self, ↓reduceIte, decide_eq_true_eq]
  split <;> rfl

theorem shl_val_of_nuw_poison (x : Byte w) {s : BitVec w}
    (h : (x.poison <<< s) >>> s ≠ x.poison) : x.shl (.val s) true = allPoison := by
  rw [shl_eq]
  simp only [Int.isPoison_of_val, Int.getValueD_val, Bool.false_or, h, ne_eq, not_false_eq_true,
    and_self, ↓reduceIte, decide_eq_true_eq]
  split <;> (try split) <;> rfl

theorem shl_val_of_lt (x : Byte w) {s : BitVec w} (h : s.toNat < w) {nuw : Bool}
    (hnuw : nuw = true → (x.val <<< s) >>> s = x.val ∧ (x.poison <<< s) >>> s = x.poison) :
    x.shl (.val s) nuw =
      ⟨x.val <<< s, x.poison <<< s, by simp [← BitVec.shiftLeft_and_distrib, x.h]⟩ := by
  rw [shl_eq]
  have h' : ¬ ((w : BitVec w) ≤ s) := by
    simp [BitVec.le_def, Nat.mod_eq_of_lt Nat.lt_two_pow_self, h]
  simp only [Int.isPoison_of_val, Int.getValueD_val, Bool.false_or, h', decide_false,
    Bool.false_eq_true, ↓reduceIte, ne_eq]
  cases nuw with
  | false => simp
  | true =>
    obtain ⟨h1, h2⟩ := hnuw rfl
    simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq'] at h1 h2 ⊢
    simp [h1, h2]

theorem getLsbD_val_shl (x : Byte w) {s : BitVec w} (h : s.toNat < w) {nuw : Bool}
    (hnuw : nuw = true → (x.val <<< s) >>> s = x.val ∧ (x.poison <<< s) >>> s = x.poison)
    (i : Nat) :
    (x.shl (.val s) nuw).val.getLsbD i =
      (decide (i < w) && !decide (i < s.toNat) && x.val.getLsbD (i - s.toNat)) := by
  rw [shl_val_of_lt x h hnuw]
  simp [BitVec.shiftLeft_eq']

theorem getLsbD_poison_shl (x : Byte w) {s : BitVec w} (h : s.toNat < w) {nuw : Bool}
    (hnuw : nuw = true → (x.val <<< s) >>> s = x.val ∧ (x.poison <<< s) >>> s = x.poison)
    (i : Nat) :
    (x.shl (.val s) nuw).poison.getLsbD i =
      (decide (i < w) && !decide (i < s.toNat) && x.poison.getLsbD (i - s.toNat)) := by
  rw [shl_val_of_lt x h hnuw]
  simp [BitVec.shiftLeft_eq']


/-! ## lshr

Same shape as `shl`, with `exact` in place of `nuw`. -/

@[simp]
theorem lshr_poison (x : Byte w) (exact : Bool) : x.lshr .poison exact = allPoison := by
  simp [lshr]

theorem lshr_val_of_le (x : Byte w) {s : BitVec w} (h : w ≤ s.toNat) (exact : Bool) :
    x.lshr (.val s) exact = allPoison := by
  have hs : (w : BitVec w) ≤ s := by
    simp [BitVec.le_def, Nat.mod_eq_of_lt Nat.lt_two_pow_self, h]
  unfold lshr
  simp only [Int.isPoison_of_val, Int.getValueD_val, Bool.false_or, hs, decide_true, ↓reduceIte]

theorem lshr_val_of_exact_val (x : Byte w) {s : BitVec w} (h : (x.val >>> s) <<< s ≠ x.val) :
    x.lshr (.val s) true = allPoison := by
  unfold lshr
  simp only [Int.isPoison_of_val, Int.getValueD_val, Bool.false_or, h, ne_eq, not_false_eq_true,
    and_self, ↓reduceIte, decide_eq_true_eq]
  split <;> rfl

theorem lshr_val_of_exact_poison (x : Byte w) {s : BitVec w}
    (h : (x.poison >>> s) <<< s ≠ x.poison) : x.lshr (.val s) true = allPoison := by
  unfold lshr
  simp only [Int.isPoison_of_val, Int.getValueD_val, Bool.false_or, h, ne_eq, not_false_eq_true,
    and_self, ↓reduceIte, decide_eq_true_eq]
  split <;> (try split) <;> rfl

theorem lshr_val_of_lt (x : Byte w) {s : BitVec w} (h : s.toNat < w) {exact : Bool}
    (hexact : exact = true → (x.val >>> s) <<< s = x.val ∧ (x.poison >>> s) <<< s = x.poison) :
    x.lshr (.val s) exact =
      ⟨x.val >>> s, x.poison >>> s, by simp [← BitVec.ushiftRight_and_distrib, x.h]⟩ := by
  unfold lshr
  have h' : ¬ ((w : BitVec w) ≤ s) := by
    simp [BitVec.le_def, Nat.mod_eq_of_lt Nat.lt_two_pow_self, h]
  simp only [Int.isPoison_of_val, Int.getValueD_val, Bool.false_or, h', decide_false,
    Bool.false_eq_true, ↓reduceIte, ne_eq]
  cases exact with
  | false => simp
  | true =>
    obtain ⟨h1, h2⟩ := hexact rfl
    simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq'] at h1 h2 ⊢
    simp [h1, h2]

theorem getLsbD_val_lshr (x : Byte w) {s : BitVec w} (h : s.toNat < w) {exact : Bool}
    (hexact : exact = true → (x.val >>> s) <<< s = x.val ∧ (x.poison >>> s) <<< s = x.poison)
    (i : Nat) :
    (x.lshr (.val s) exact).val.getLsbD i = x.val.getLsbD (s.toNat + i) := by
  rw [lshr_val_of_lt x h hexact]
  simp [BitVec.ushiftRight_eq']

theorem getLsbD_poison_lshr (x : Byte w) {s : BitVec w} (h : s.toNat < w) {exact : Bool}
    (hexact : exact = true → (x.val >>> s) <<< s = x.val ∧ (x.poison >>> s) <<< s = x.poison)
    (i : Nat) :
    (x.lshr (.val s) exact).poison.getLsbD i = x.poison.getLsbD (s.toNat + i) := by
  rw [lshr_val_of_lt x h hexact]
  simp [BitVec.ushiftRight_eq']


end

end Veir.Data.LLVM.Byte
