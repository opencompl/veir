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

@[simp]
theorem poison_and {w : Nat} (x y : Byte w) :
    (x &&& y).poison = x.poison ||| y.poison := by
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

@[simp]
theorem poison_or {w : Nat} (x y : Byte w) :
    (x ||| y).poison = x.poison ||| y.poison := by
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

@[simp]
theorem poison_xor {w : Nat} (x y : Byte w) :
    (x ^^^ y).poison = x.poison ||| y.poison := by
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

/-! # Bit-level characterization

For every operation `op` on bytes, `val_getLsbD_op` and `poison_getLsbD_op` describe bit `i` of
the value and of the poison mask of `op`, in terms of the bits of its arguments, in the style of
`BitVec.getLsbD_and` and friends. `val_getElem_op` and `poison_getElem_op` are the `x[i]`
versions, which need `i < w`. -/

section Bits

variable {w : Nat}

/-! ## The invariant, per bit -/

/-- A poisoned bit has value `0`. -/
theorem val_getLsbD_eq_false_of_poison (x : Byte w) {i : Nat} (h : x.poison.getLsbD i = true) :
    x.val.getLsbD i = false := by
  have := congrArg (·.getLsbD i) x.h
  simpa [h] using this

/-- A bit with value `1` is not poisoned. -/
theorem poison_getLsbD_eq_false_of_val (x : Byte w) {i : Nat} (h : x.val.getLsbD i = true) :
    x.poison.getLsbD i = false := by
  have := congrArg (·.getLsbD i) x.h
  simpa [h] using this

@[simp]
theorem val_getLsbD_and_poison_getLsbD (x : Byte w) (i : Nat) :
    (x.val.getLsbD i && x.poison.getLsbD i) = false := by
  have := congrArg (·.getLsbD i) x.h
  simpa using this

@[simp]
theorem poison_getLsbD_and_val_getLsbD (x : Byte w) (i : Nat) :
    (x.poison.getLsbD i && x.val.getLsbD i) = false := by
  rw [Bool.and_comm]; exact val_getLsbD_and_poison_getLsbD x i

theorem val_getElem_eq_false_of_poison (x : Byte w) {i : Nat} (hi : i < w)
    (h : x.poison[i] = true) : x.val[i] = false := by
  simpa [BitVec.getLsbD_eq_getElem hi] using
    val_getLsbD_eq_false_of_poison x (i := i) (by simpa [BitVec.getLsbD_eq_getElem hi] using h)

theorem poison_getElem_eq_false_of_val (x : Byte w) {i : Nat} (hi : i < w)
    (h : x.val[i] = true) : x.poison[i] = false := by
  simpa [BitVec.getLsbD_eq_getElem hi] using
    poison_getLsbD_eq_false_of_val x (i := i) (by simpa [BitVec.getLsbD_eq_getElem hi] using h)

@[simp]
theorem val_getElem_and_poison_getElem (x : Byte w) {i : Nat} (hi : i < w) :
    (x.val[i] && x.poison[i]) = false := by
  simpa [BitVec.getLsbD_eq_getElem hi] using val_getLsbD_and_poison_getLsbD x i

@[simp]
theorem poison_getElem_and_val_getElem (x : Byte w) {i : Nat} (hi : i < w) :
    (x.poison[i] && x.val[i]) = false := by
  simpa [BitVec.getLsbD_eq_getElem hi] using poison_getLsbD_and_val_getLsbD x i

/-! ## allPoison -/

@[simp] theorem val_allPoison : (allPoison : Byte w).val = 0#w := rfl
@[simp] theorem poison_allPoison : (allPoison : Byte w).poison = .allOnes w := rfl

theorem val_getLsbD_allPoison (i : Nat) : (allPoison : Byte w).val.getLsbD i = false := by simp
theorem poison_getLsbD_allPoison (i : Nat) :
    (allPoison : Byte w).poison.getLsbD i = decide (i < w) := by simp
theorem val_getElem_allPoison {i : Nat} (hi : i < w) : (allPoison : Byte w).val[i] = false := by simp
theorem poison_getElem_allPoison {i : Nat} (hi : i < w) :
    (allPoison : Byte w).poison[i] = true := by simp

/-! ## cast -/

@[simp] theorem val_cast {w₁ w₂ : Nat} (x : Byte w₁) (h : w₁ = w₂) :
    (x.cast h).val = x.val.cast h := rfl
@[simp] theorem poison_cast {w₁ w₂ : Nat} (x : Byte w₁) (h : w₁ = w₂) :
    (x.cast h).poison = x.poison.cast h := rfl

theorem val_getLsbD_cast {w₁ w₂ : Nat} (x : Byte w₁) (h : w₁ = w₂) (i : Nat) :
    (x.cast h).val.getLsbD i = x.val.getLsbD i := by simp
theorem poison_getLsbD_cast {w₁ w₂ : Nat} (x : Byte w₁) (h : w₁ = w₂) (i : Nat) :
    (x.cast h).poison.getLsbD i = x.poison.getLsbD i := by simp
theorem val_getElem_cast {w₁ w₂ : Nat} (x : Byte w₁) (h : w₁ = w₂) {i : Nat} (hi : i < w₂) :
    (x.cast h).val[i] = x.val[i] := by simp
theorem poison_getElem_cast {w₁ w₂ : Nat} (x : Byte w₁) (h : w₁ = w₂) {i : Nat} (hi : i < w₂) :
    (x.cast h).poison[i] = x.poison[i] := by simp

/-! ## and -/

/-- Since a bit with value `1` is never poisoned, the poison mask of `x &&& y` does not show up. -/
@[simp]
theorem val_getLsbD_and (x y : Byte w) (i : Nat) :
    (x &&& y).val.getLsbD i = (x.val.getLsbD i && y.val.getLsbD i) := by
  have hx := val_getLsbD_and_poison_getLsbD x i
  have hy := val_getLsbD_and_poison_getLsbD y i
  rw [val_and]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_or]
  by_cases hi : i < w
  · simp only [hi, decide_true]
    revert hx hy
    generalize x.val.getLsbD i = a; generalize x.poison.getLsbD i = b
    generalize y.val.getLsbD i = c; generalize y.poison.getLsbD i = d
    cases a <;> cases b <;> cases c <;> cases d <;> simp
  · simp [BitVec.getLsbD_of_ge _ _ (Nat.not_lt.mp hi)]

@[simp]
theorem poison_getLsbD_and (x y : Byte w) (i : Nat) :
    (x &&& y).poison.getLsbD i = (x.poison.getLsbD i || y.poison.getLsbD i) := by
  simp

@[simp]
theorem val_getElem_and (x y : Byte w) {i : Nat} (hi : i < w) :
    (x &&& y).val[i] = (x.val[i] && y.val[i]) := by
  simpa [BitVec.getLsbD_eq_getElem hi] using val_getLsbD_and x y i

@[simp]
theorem poison_getElem_and (x y : Byte w) {i : Nat} (hi : i < w) :
    (x &&& y).poison[i] = (x.poison[i] || y.poison[i]) := by
  simp

/-! ## or -/

@[simp]
theorem val_getLsbD_or (x y : Byte w) (i : Nat) :
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

@[simp]
theorem poison_getLsbD_or (x y : Byte w) (i : Nat) :
    (x ||| y).poison.getLsbD i = (x.poison.getLsbD i || y.poison.getLsbD i) := by
  simp

@[simp]
theorem val_getElem_or (x y : Byte w) {i : Nat} (hi : i < w) :
    (x ||| y).val[i] = ((x.val[i] || y.val[i]) && !x.poison[i] && !y.poison[i]) := by
  simpa [BitVec.getLsbD_eq_getElem hi] using val_getLsbD_or x y i

@[simp]
theorem poison_getElem_or (x y : Byte w) {i : Nat} (hi : i < w) :
    (x ||| y).poison[i] = (x.poison[i] || y.poison[i]) := by
  simp

/-! ## xor -/

@[simp]
theorem val_getLsbD_xor (x y : Byte w) (i : Nat) :
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

@[simp]
theorem poison_getLsbD_xor (x y : Byte w) (i : Nat) :
    (x ^^^ y).poison.getLsbD i = (x.poison.getLsbD i || y.poison.getLsbD i) := by
  simp

@[simp]
theorem val_getElem_xor (x y : Byte w) {i : Nat} (hi : i < w) :
    (x ^^^ y).val[i] = ((x.val[i] ^^ y.val[i]) && !x.poison[i] && !y.poison[i]) := by
  simpa [BitVec.getLsbD_eq_getElem hi] using val_getLsbD_xor x y i

@[simp]
theorem poison_getElem_xor (x y : Byte w) {i : Nat} (hi : i < w) :
    (x ^^^ y).poison[i] = (x.poison[i] || y.poison[i]) := by
  simp

/-! ## trunc -/

@[simp] theorem val_trunc (x : Byte w) (w' : Nat) : (x.trunc w').val = x.val.setWidth w' := rfl
@[simp] theorem poison_trunc (x : Byte w) (w' : Nat) :
    (x.trunc w').poison = x.poison.setWidth w' := rfl

theorem val_getLsbD_trunc (x : Byte w) (w' i : Nat) :
    (x.trunc w').val.getLsbD i = (decide (i < w') && x.val.getLsbD i) := by simp
theorem poison_getLsbD_trunc (x : Byte w) (w' i : Nat) :
    (x.trunc w').poison.getLsbD i = (decide (i < w') && x.poison.getLsbD i) := by simp
theorem val_getElem_trunc (x : Byte w) {w' i : Nat} (hi : i < w') :
    (x.trunc w').val[i] = x.val.getLsbD i := by simp
theorem poison_getElem_trunc (x : Byte w) {w' i : Nat} (hi : i < w') :
    (x.trunc w').poison[i] = x.poison.getLsbD i := by simp

/-! ## freeze -/

@[simp] theorem val_freeze (x : Byte w) : x.freeze.val = x.val := rfl
@[simp] theorem poison_freeze (x : Byte w) : x.freeze.poison = 0#w := rfl

theorem val_getLsbD_freeze (x : Byte w) (i : Nat) : x.freeze.val.getLsbD i = x.val.getLsbD i := by
  simp
theorem poison_getLsbD_freeze (x : Byte w) (i : Nat) : x.freeze.poison.getLsbD i = false := by
  simp
theorem val_getElem_freeze (x : Byte w) {i : Nat} (hi : i < w) : x.freeze.val[i] = x.val[i] := by
  simp
theorem poison_getElem_freeze (x : Byte w) {i : Nat} (hi : i < w) :
    x.freeze.poison[i] = false := by
  simp

/-! ## fromInt, fromBitVec, fromUInt64 -/

@[simp]
theorem val_getLsbD_fromInt (y : Int w) (i : Nat) :
    (fromInt y).val.getLsbD i = y.getValueD.getLsbD i := by
  simp [val_fromInt]

@[simp]
theorem poison_getLsbD_fromInt (y : Int w) (i : Nat) :
    (fromInt y).poison.getLsbD i = (y.isPoison && decide (i < w)) := by
  rw [poison_fromInt]; split <;> simp_all

@[simp]
theorem val_getElem_fromInt (y : Int w) {i : Nat} (hi : i < w) :
    (fromInt y).val[i] = y.getValueD[i] := by
  simpa [BitVec.getLsbD_eq_getElem hi] using val_getLsbD_fromInt y i

@[simp]
theorem poison_getElem_fromInt (y : Int w) {i : Nat} (hi : i < w) :
    (fromInt y).poison[i] = y.isPoison := by
  simpa [BitVec.getLsbD_eq_getElem hi, hi] using poison_getLsbD_fromInt y i

theorem val_getLsbD_fromBitVec (v : BitVec w) (i : Nat) :
    (fromBitVec v).val.getLsbD i = v.getLsbD i := by simp
theorem poison_getLsbD_fromBitVec (v : BitVec w) (i : Nat) :
    (fromBitVec v).poison.getLsbD i = false := by simp
theorem val_getElem_fromBitVec (v : BitVec w) {i : Nat} (hi : i < w) :
    (fromBitVec v).val[i] = v[i] := by simp
theorem poison_getElem_fromBitVec (v : BitVec w) {i : Nat} (hi : i < w) :
    (fromBitVec v).poison[i] = false := by simp

theorem val_getLsbD_fromUInt64 (u : UInt64) (i : Nat) :
    (fromUInt64 u).val.getLsbD i = u.toBitVec.getLsbD i := by simp
theorem poison_getLsbD_fromUInt64 (u : UInt64) (i : Nat) :
    (fromUInt64 u).poison.getLsbD i = false := by simp
theorem val_getElem_fromUInt64 (u : UInt64) {i : Nat} (hi : i < 64) :
    (fromUInt64 u).val[i] = u.toBitVec[i] := by simp
theorem poison_getElem_fromUInt64 (u : UInt64) {i : Nat} (hi : i < 64) :
    (fromUInt64 u).poison[i] = false := by simp

/-! ## merge -/

@[simp] theorem val_merge (x y : Byte w) : (merge x y).val = x.val ||| y.val := rfl
@[simp] theorem poison_merge (x y : Byte w) : (merge x y).poison = x.poison &&& y.poison := rfl

theorem val_getLsbD_merge (x y : Byte w) (i : Nat) :
    (merge x y).val.getLsbD i = (x.val.getLsbD i || y.val.getLsbD i) := by simp
theorem poison_getLsbD_merge (x y : Byte w) (i : Nat) :
    (merge x y).poison.getLsbD i = (x.poison.getLsbD i && y.poison.getLsbD i) := by simp
theorem val_getElem_merge (x y : Byte w) {i : Nat} (hi : i < w) :
    (merge x y).val[i] = (x.val[i] || y.val[i]) := by simp
theorem poison_getElem_merge (x y : Byte w) {i : Nat} (hi : i < w) :
    (merge x y).poison[i] = (x.poison[i] && y.poison[i]) := by simp

/-- Two bytes are compatible iff on every bit, one of them is poison or they agree. -/
theorem compatible_iff_getLsbD (x y : Byte w) :
    Compatible x y ↔ ∀ i < w, x.poison.getLsbD i = true ∨ y.poison.getLsbD i = true ∨
      x.val.getLsbD i = y.val.getLsbD i := by
  simp only [Compatible]
  constructor
  · intro h i hi
    have := congrArg (·.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, hi, decide_true] at this
    revert this
    generalize x.val.getLsbD i = a; generalize x.poison.getLsbD i = b
    generalize y.val.getLsbD i = c; generalize y.poison.getLsbD i = d
    cases a <;> cases b <;> cases c <;> cases d <;> simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := h i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, hi, decide_true]
    revert this
    generalize x.val.getLsbD i = a; generalize x.poison.getLsbD i = b
    generalize y.val.getLsbD i = c; generalize y.poison.getLsbD i = d
    cases a <;> cases b <;> cases c <;> cases d <;> simp

/-! ## shl

`shl` is all-poison when the amount is poison, out of range, or (with `nuw`) shifts out a set
value or poison bit; otherwise it shifts value and poison mask together. The bit lemmas are stated
for the last case, with the `nuw` side condition as a hypothesis that is vacuous for `nuw = false`.
-/

/-- The comparison `s ≥ w` used by `shl` and `lshr`, on `Nat`. -/
private theorem ge_natCast_iff (s : BitVec w) : s ≥ (w : BitVec w) ↔ w ≤ s.toNat := by
  simp [GE.ge, BitVec.le_def, Nat.mod_eq_of_lt Nat.lt_two_pow_self]

@[simp]
theorem shl_poison (x : Byte w) (nuw : Bool) : x.shl .poison nuw = allPoison := by
  simp [shl_eq]

theorem shl_val_of_le (x : Byte w) {s : BitVec w} (h : w ≤ s.toNat) (nuw : Bool) :
    x.shl (.val s) nuw = allPoison := by
  have hs : s ≥ (w : BitVec w) := (ge_natCast_iff s).mpr h
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
  have h' : ¬ (s ≥ (w : BitVec w)) := by rw [ge_natCast_iff]; omega
  simp only [Int.isPoison_of_val, Int.getValueD_val, Bool.false_or, h', decide_false,
    Bool.false_eq_true, ↓reduceIte, ne_eq]
  cases nuw with
  | false => simp
  | true =>
    obtain ⟨h1, h2⟩ := hnuw rfl
    simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq'] at h1 h2 ⊢
    simp [h1, h2]

theorem val_getLsbD_shl (x : Byte w) {s : BitVec w} (h : s.toNat < w) {nuw : Bool}
    (hnuw : nuw = true → (x.val <<< s) >>> s = x.val ∧ (x.poison <<< s) >>> s = x.poison)
    (i : Nat) :
    (x.shl (.val s) nuw).val.getLsbD i =
      (decide (i < w) && !decide (i < s.toNat) && x.val.getLsbD (i - s.toNat)) := by
  rw [shl_val_of_lt x h hnuw]
  simp [BitVec.shiftLeft_eq']

theorem poison_getLsbD_shl (x : Byte w) {s : BitVec w} (h : s.toNat < w) {nuw : Bool}
    (hnuw : nuw = true → (x.val <<< s) >>> s = x.val ∧ (x.poison <<< s) >>> s = x.poison)
    (i : Nat) :
    (x.shl (.val s) nuw).poison.getLsbD i =
      (decide (i < w) && !decide (i < s.toNat) && x.poison.getLsbD (i - s.toNat)) := by
  rw [shl_val_of_lt x h hnuw]
  simp [BitVec.shiftLeft_eq']

theorem val_getElem_shl (x : Byte w) {s : BitVec w} (h : s.toNat < w) {nuw : Bool}
    (hnuw : nuw = true → (x.val <<< s) >>> s = x.val ∧ (x.poison <<< s) >>> s = x.poison)
    {i : Nat} (hi : i < w) :
    (x.shl (.val s) nuw).val[i] = (!decide (i < s.toNat) && x.val[i - s.toNat]) := by
  rw [shl_val_of_lt x h hnuw]
  simp [BitVec.shiftLeft_eq']

theorem poison_getElem_shl (x : Byte w) {s : BitVec w} (h : s.toNat < w) {nuw : Bool}
    (hnuw : nuw = true → (x.val <<< s) >>> s = x.val ∧ (x.poison <<< s) >>> s = x.poison)
    {i : Nat} (hi : i < w) :
    (x.shl (.val s) nuw).poison[i] = (!decide (i < s.toNat) && x.poison[i - s.toNat]) := by
  rw [shl_val_of_lt x h hnuw]
  simp [BitVec.shiftLeft_eq']

/-! ## lshr

Same shape as `shl`, with `exact` in place of `nuw`. -/

@[simp]
theorem lshr_poison (x : Byte w) (exact : Bool) : x.lshr .poison exact = allPoison := by
  simp [lshr]

theorem lshr_val_of_le (x : Byte w) {s : BitVec w} (h : w ≤ s.toNat) (exact : Bool) :
    x.lshr (.val s) exact = allPoison := by
  have hs : s ≥ (w : BitVec w) := (ge_natCast_iff s).mpr h
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
  have h' : ¬ (s ≥ (w : BitVec w)) := by rw [ge_natCast_iff]; omega
  simp only [Int.isPoison_of_val, Int.getValueD_val, Bool.false_or, h', decide_false,
    Bool.false_eq_true, ↓reduceIte, ne_eq]
  cases exact with
  | false => simp
  | true =>
    obtain ⟨h1, h2⟩ := hexact rfl
    simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq'] at h1 h2 ⊢
    simp [h1, h2]

theorem val_getLsbD_lshr (x : Byte w) {s : BitVec w} (h : s.toNat < w) {exact : Bool}
    (hexact : exact = true → (x.val >>> s) <<< s = x.val ∧ (x.poison >>> s) <<< s = x.poison)
    (i : Nat) :
    (x.lshr (.val s) exact).val.getLsbD i = x.val.getLsbD (s.toNat + i) := by
  rw [lshr_val_of_lt x h hexact]
  simp [BitVec.ushiftRight_eq']

theorem poison_getLsbD_lshr (x : Byte w) {s : BitVec w} (h : s.toNat < w) {exact : Bool}
    (hexact : exact = true → (x.val >>> s) <<< s = x.val ∧ (x.poison >>> s) <<< s = x.poison)
    (i : Nat) :
    (x.lshr (.val s) exact).poison.getLsbD i = x.poison.getLsbD (s.toNat + i) := by
  rw [lshr_val_of_lt x h hexact]
  simp [BitVec.ushiftRight_eq']

theorem val_getElem_lshr (x : Byte w) {s : BitVec w} (h : s.toNat < w) {exact : Bool}
    (hexact : exact = true → (x.val >>> s) <<< s = x.val ∧ (x.poison >>> s) <<< s = x.poison)
    {i : Nat} (hi : i < w) :
    (x.lshr (.val s) exact).val[i] = x.val.getLsbD (s.toNat + i) := by
  rw [lshr_val_of_lt x h hexact]
  simp [BitVec.ushiftRight_eq']

theorem poison_getElem_lshr (x : Byte w) {s : BitVec w} (h : s.toNat < w) {exact : Bool}
    (hexact : exact = true → (x.val >>> s) <<< s = x.val ∧ (x.poison >>> s) <<< s = x.poison)
    {i : Nat} (hi : i < w) :
    (x.lshr (.val s) exact).poison[i] = x.poison.getLsbD (s.toNat + i) := by
  rw [lshr_val_of_lt x h hexact]
  simp [BitVec.ushiftRight_eq']

end Bits

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

/-- Shifting left and back right keeps `a` iff its top `s` bits are zero. -/
theorem shiftLeft_ushiftRight_eq_iff {w : Nat} (a : BitVec w) (s : Nat) :
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
theorem ushiftRight_shiftLeft_eq_iff {w : Nat} (a : BitVec w) (s : Nat) :
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
theorem shl_isRefinedBy_of_isRefinedBy {w : Nat} {x x' : Byte w} {y y' : Int w} (hx : x ⊒ x')
      (hy : y ⊒ y') :
    x.shl y nuw ⊒ x'.shl y' nuw := by
  cases y with
  | poison => exact allPoison_isRefinedBy _
  | val s =>
    simp [isRefinedBy] at ⊢ hx hy
    ext k hk
    simp
    have hxbit := congrArg (·.getLsbD k) hx
    simp [hk] at hxbit
    rcases hxbit with h1 | h2
    · unfold shl
      simp
      split
      · simp [allPoison]
      · split
        · simp [allPoison]
        · split
          · simp [allPoison]

          · simp [Id.run]
            by_cases hlt : k < s.toNat
            · simp [hlt, show ¬ s.toNat ≤ k by omega]
              split
              · split
                · simp [allPoison, pure]



                  sorry
                · sorry
              ·
                sorry
              sorry
            sorry
        sorry
    · sorry


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
